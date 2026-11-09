(** * Charged incremental join maintenance

    Updates charge the entire supplied atom inventory and the inserted row occurrences.
    For example, an empty batch still pays every reset and row callback in the plan.
    Builds on: DatalogJoinProof, DatalogCost and public Map cost equations. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire DatalogCost
  DatalogJoin DatalogJoinProof DatalogJoinCost.
Import List.ListNotations Cost.Notations Join JoinProof JoinCost.
Local Open Scope N_scope.

Module JoinUpdateCost.

(** Position selection charges at most one tick per mask position and the final arity test. *)
Theorem select_cost {A} mask (row : list A) :
  Cost.ticks (select_c mask row) <= 1 + N.of_nat (length mask).
Proof.
  revert row; induction mask as [|keep mask IH]; intros [|x row];
    cbn [select_c length]; autorewrite with galois_cost; try lia.
  specialize (IH row); rewrite Nat2N.inj_succ; lia.
Qed.

(** Inserting one row retains both key encodings, both trie paths and its complete selection. *)
Theorem index_add_cost mask row idx e w :
  (forall key, select mask row = Some key ->
    Cost.ticks (encode_c tuple_encoding key) <= e /\ key_bits tuple_encoding key <= w) ->
  Cost.ticks (index_add_c mask row idx) <= 3 + N.of_nat (length mask) + 2 * (e + w).
Proof.
  intro Hkeys; unfold index_add_c; rewrite Cost.ticks_bind.
  pose proof (select_cost mask row) as Hselect.
  fold (@select positive mask row); destruct (select mask row) as [key |] eqn:Hkey.
  - rewrite Cost.ticks_bind, index_get_cost, Map.set_cost.
    fold (key_bits tuple_encoding key); destruct (Hkeys key eq_refl) as [Henc Hbits].
    lia.
  - rewrite Cost.ticks_ret; lia.
Qed.

(** Extending an index charges every supplied row occurrence without scanning existing buckets. *)
Theorem extend_index_cost mask rows idx e w :
  (forall row key, In row rows -> select mask row = Some key ->
    Cost.ticks (encode_c tuple_encoding key) <= e /\ key_bits tuple_encoding key <= w) ->
  Cost.ticks (extend_index_c mask rows idx) <=
    N.of_nat (length rows) * (4 + N.of_nat (length mask) + 2 * (e + w)).
Proof.
  intro Hkeys; unfold extend_index_c.
  eapply N.le_trans; [apply (fold_right_bound_on _ (3 + N.of_nat (length mask) +
    2 * (e + w))) |].
  - intros row acc Hrow; apply index_add_cost; intros key Hkey.
    exact (Hkeys row key Hrow Hkey).
  - nia.
Qed.

(** Maintenance duties mention callbacks, supplied row counts and selected-key encoding only. *)
Definition insert_primitives {P} (plan : plan_state P)
    (reset : P -> Cost.t bool) (rows : P -> Cost.t (list tuple)) a r z c e w : Prop :=
  forall n, In n plan ->
    (length (mask n) <= a)%nat /\
    Cost.ticks (reset (pred (source n))) <= z /\
    Cost.ticks (rows (pred (source n))) <= c /\
    N.of_nat (length (Cost.value (rows (pred (source n))))) <= r /\
    forall row key, In row (Cost.value (rows (pred (source n)))) ->
      select (mask n) row = Some key ->
      Cost.ticks (encode_c tuple_encoding key) <= e /\ key_bits tuple_encoding key <= w.

(** The coefficient retains reset callbacks, batch callbacks and per-row selection and insertion. *)
Definition insert_unit_cost a r z c e w := 3 + z + c + r * (4 + N.of_nat a + 2 * (e + w)).

(** Incremental maintenance is linear in the full supplied inventory and inserted row occurrences. *)
Theorem join_insert_cost {P} (plan : plan_state P) reset rows a r z c e w :
  insert_primitives plan reset rows a r z c e w ->
  Cost.ticks (insert_rows_c reset rows plan) <=
    N.of_nat (length plan) * insert_unit_cost a r z c e w.
Proof.
  intro Hprimitives; unfold insert_rows_c; rewrite ticks_map_c.
  replace (insert_unit_cost a r z c e w) with
    ((2 + z + c + r * (4 + N.of_nat a + 2 * (e + w))) + 1)
    by (unfold insert_unit_cost; lia).
  apply traversal_bound_on; intros n Hn.
  destruct (Hprimitives n Hn) as [Hmask [Hreset [Hrows [Hcount Hkeys]]]].
  repeat rewrite Cost.ticks_bind; rewrite !Cost.ticks_step, Cost.ticks_ret.
  pose proof (extend_index_cost (mask n) (Cost.value (rows (pred (source n))))
    (if Cost.value (reset (pred (source n))) then Map.empty else table n)
    e w Hkeys) as Hextend.
  pose proof (nat_N_le _ _ Hmask) as HmaskN.
  assert (Hscaled : N.of_nat (length (Cost.value (rows (pred (source n))))) *
    (4 + N.of_nat (length (mask n)) + 2 * (e + w)) <=
      r * (4 + N.of_nat a + 2 * (e + w))).
  { apply N.mul_le_mono; [exact Hcount | lia]. }
  eapply N.le_trans with
    (m := 1 + (z + (1 + (c + (r * (4 + N.of_nat a + 2 * (e + w)) + 0))))).
  - apply N.add_le_mono; [reflexivity |].
    apply N.add_le_mono; [exact Hreset |].
    apply N.add_le_mono; [reflexivity |].
    apply N.add_le_mono; [exact Hrows |].
    apply N.add_le_mono; [eapply N.le_trans; [exact Hextend | exact Hscaled] | reflexivity].
  - lia.
Qed.

(** Family bounds retain atom scans even when every supplied batch is empty. *)
Theorem join_insert_bigO {X P} (plan : X -> plan_state P)
    (reset : X -> P -> Cost.t bool) (rows : X -> P -> Cost.t (list tuple))
    (a : X -> nat) (r z c e w : X -> N) :
  (forall x, insert_primitives (plan x) (reset x) (rows x)
    (a x) (r x) (z x) (c x) (e x) (w x)) ->
  bigO (fun x => N.of_nat (length (plan x)) *
    insert_unit_cost (a x) (r x) (z x) (c x) (e x) (w x))
    (fun x => Cost.ticks (insert_rows_c (reset x) (rows x) (plan x))).
Proof.
  intro Hprimitives; exists 1; intro x.
  pose proof (join_insert_cost _ _ _ _ _ _ _ _ _ (Hprimitives x)); nia.
Qed.

End JoinUpdateCost.
Import JoinUpdateCost.
