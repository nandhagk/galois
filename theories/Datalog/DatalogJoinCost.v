(** * Primitive-relative indexed join bounds

    Join work counts probes and bucket rows, and primitive budgets retain binding and key costs.
    For example, a long tuple can cost more than one tick even when its bucket has one row.
    Builds on: DatalogJoinProof, DatalogCost and BaseMap cost equations. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire DatalogCost
  DatalogJoin DatalogJoinProof.
Import List.ListNotations Cost.Notations Join JoinProof.
Local Open Scope N_scope.

Module JoinCost.

Lemma callback_sum_cost i enc bits matched copied count ia e w q k :
  i <= ia -> enc <= e -> bits <= w ->
  matched <= count * (q + 1) -> copied <= count ->
  2 + ia + e + w <= k -> q + 2 <= k ->
  1 + (i + (1 + enc + bits) + (matched + copied)) <= (1 + count) * k.
Proof.
  intros Hi Henc Hbits Hmatched Hcopied Hbase Hrow.
  pose proof (N.mul_le_mono_l _ _ count Hrow) as Hscaled.
  rewrite N.mul_add_distr_l, N.mul_1_r in Hmatched.
  rewrite N.mul_add_distr_l in Hscaled.
  rewrite N.mul_add_distr_r, N.mul_1_l; lia.
Qed.

Lemma bind_term_length b t c b' :
  bind_term b t c = Some b' -> (length b' <= S (length b))%nat.
Proof.
  apply DatalogCost.bind_term_length.
Qed.

(** Matching one term charges a binding lookup or positive comparison, including the call tick. *)
Theorem bind_term_cost b t c v :
  N.pos (Pos.size c) <= v ->
  Cost.ticks (bind_term_c b t c) <= 1 + N.of_nat (length b) + v.
Proof.
  apply DatalogCost.bind_term_cost.
Qed.

(** Matching a row has a numeric bound from term count, binding length and row-component widths. *)
Theorem bind_terms_cost ts row b h v :
  (length b + length ts <= h)%nat ->
  (forall c, In c row -> N.pos (Pos.size c) <= v) ->
  Cost.ticks (bind_terms_c ts row b) <=
    (N.of_nat (length ts) + 1) * (2 + N.of_nat h + v).
Proof.
  apply DatalogCost.bind_terms_cost.
Qed.

(** Instantiation retains the list traversal and the cost of each partial-valuation lookup. *)
Theorem instantiate_cost b ts :
  Cost.ticks (instantiate_c b ts) <=
    N.of_nat (length ts) * (1 + N.of_nat (length b)).
Proof.
  apply DatalogCost.instantiate_cost.
Qed.

(** A bucket probe has the public map lookup's encoding and key-width charges. *)
Theorem index_get_cost idx key :
  Cost.ticks (index_get_c idx key) =
    1 + Cost.ticks (encode_c tuple_encoding key) + key_bits tuple_encoding key.
Proof.
  unfold index_get_c; rewrite Map.find_or_cost, Map.get_cost; reflexivity.
Qed.

Definition probe_work {P} (n : node P) bs :=
  fold_right (fun b total =>
    1 + N.of_nat (length (index_get (table n)
      (map (inst (binding_value b)) (key_terms n)))) + total) 0 bs.

(** Primitive budgets concern lengths, actual probe keys and enumerated row components.
    They contain no premise about the cost or result of a join operation. *)
Definition probe_primitives {P} (n : node P) bs (a h : nat) (v e w : N) :=
  (length (args (source n)) <= a)%nat /\
  (length (key_terms n) <= a)%nat /\
  forall b, In b bs ->
    (length b <= h)%nat /\
    let key := map (inst (binding_value b)) (key_terms n) in
    Cost.ticks (encode_c tuple_encoding key) <= e /\
    key_bits tuple_encoding key <= w /\
    forall row c, In row (index_get (table n) key) -> In c row ->
      N.pos (Pos.size c) <= v.

(** The per-work-item coefficient includes term matching, lookup and tuple-key encoding. *)
Definition join_unit_cost (a h : nat) (v e w : N) :=
  5 + N.of_nat a * (1 + N.of_nat h) + e + w +
    (N.of_nat a + 1) * (2 + N.of_nat (h + a) + v).

Lemma join_unit_positive a h v e w : 1 <= join_unit_cost a h v e w.
Proof.
  unfold join_unit_cost; nia.
Qed.

Lemma probe_callback_cost {P} (n : node P) b acc a h v e w :
  probe_primitives n [b] a h v e w ->
  1 + Cost.ticks (probe_one_c n b acc) <=
    (1 + N.of_nat (length (index_get (table n)
      (map (inst (binding_value b)) (key_terms n))))) * join_unit_cost a h v e w.
Proof.
  intros [Hargs [Hkeys Hbudget]].
  destruct (Hbudget b (or_introl eq_refl)) as [Hbinding [Henc [Hwidth Hrows]]].
  unfold probe_one_c.
  repeat rewrite Cost.ticks_bind; rewrite instantiate_equation, index_get_cost.
  fold (index_get (table n) (map (inst (binding_value b)) (key_terms n))).
  set (rows := index_get (table n) (map (inst (binding_value b)) (key_terms n))).
  set (q := (N.of_nat a + 1) * (2 + N.of_nat (h + a) + v)).
  assert (Hmatch : forall row, In row rows ->
    Cost.ticks (bind_terms_c (args (source n)) row b) <= q).
  { intros row Hrow; eapply N.le_trans; [apply (bind_terms_cost _ _ _ (h + a) v) |].
    - lia.
    - intros c Hc; apply (Hrows row c Hrow Hc).
    - unfold q; pose proof (nat_N_le _ _ Hargs); nia. }
  pose proof (traversal_bound_on
    (fun row => Cost.ticks (bind_terms_c (args (source n)) row b)) q rows Hmatch) as Hfilter.
  pose proof (instantiate_cost b (key_terms n)) as Hinst.
  pose proof (nat_N_le _ _ Hkeys) as HkeysN.
  pose proof (nat_N_le _ _ Hbinding) as HbindingN.
  assert (Hinstbound : Cost.ticks (instantiate_c b (key_terms n)) <=
    N.of_nat a * (1 + N.of_nat h)).
  { eapply N.le_trans; [exact Hinst |].
    apply N.mul_le_mono; [exact HkeysN | lia]. }
  rewrite ticks_filter_map_c, ticks_app_c, value_filter_map_c.
  pose proof (nat_N_le _ _ (filter_map_length
    (fun row => bind_terms (args (source n)) row b) rows)) as Hlength.
  change (1 + (Cost.ticks (instantiate_c b (key_terms n)) +
    ((1 + Cost.ticks (encode_c tuple_encoding
      (map (inst (binding_value b)) (key_terms n))) +
      key_bits tuple_encoding (map (inst (binding_value b)) (key_terms n))) +
    (fold_right (fun row total =>
      1 + Cost.ticks (bind_terms_c (args (source n)) row b) + total) 0 rows +
    N.of_nat (length (filter_map
      (fun row => bind_terms (args (source n)) row b) rows))))) <=
    (1 + N.of_nat (length rows)) * join_unit_cost a h v e w).
  cbv beta in Hfilter.
  pose proof (callback_sum_cost
    (Cost.ticks (instantiate_c b (key_terms n)))
    (Cost.ticks (encode_c tuple_encoding (map (inst (binding_value b)) (key_terms n))))
    (key_bits tuple_encoding (map (inst (binding_value b)) (key_terms n)))
    (fold_right (fun row total =>
      1 + Cost.ticks (bind_terms_c (args (source n)) row b) + total) 0 rows)
    (N.of_nat (length (filter_map (fun row => bind_terms (args (source n)) row b) rows)))
    (N.of_nat (length rows)) (N.of_nat a * (1 + N.of_nat h)) e w q
    (join_unit_cost a h v e w) Hinstbound Henc Hwidth Hfilter Hlength
    ltac:(unfold join_unit_cost; lia) ltac:(unfold q, join_unit_cost; lia)) as Htotal.
  rewrite !N.add_assoc in Htotal |- *.
  exact Htotal.
Qed.

Lemma probe_cost {P} (n : node P) bs a h v e w :
  probe_primitives n bs a h v e w ->
  Cost.ticks (probe_c n bs) <= probe_work n bs * join_unit_cost a h v e w.
Proof.
  intros [Hargs [Hkeys Hbudget]]; unfold probe_c.
  induction bs as [|b bs IH]; [change (0 <= 0); lia |].
  rewrite ticks_fold_right_c_cons.
  assert (Htail : forall x, In x bs ->
    (length x <= h)%nat /\
    let key := map (inst (binding_value x)) (key_terms n) in
    Cost.ticks (encode_c tuple_encoding key) <= e /\
    key_bits tuple_encoding key <= w /\
    forall row c, In row (index_get (table n) key) -> In c row ->
      N.pos (Pos.size c) <= v).
  { intros x Hx; apply Hbudget; now right. }
  specialize (IH Htail).
  assert (Hsingle : probe_primitives n [b] a h v e w).
  { split; [exact Hargs | split; [exact Hkeys |]].
    intros x Hx; destruct Hx as [Heq | Hbad]; [subst x | contradiction].
    apply Hbudget; now left. }
  pose proof (probe_callback_cost n b
    (probe n bs) a h v e w
    Hsingle) as Hhead.
  pose proof (join_unit_positive a h v e w) as Hpositive.
  change (1 + Cost.ticks (probe_one_c n b
    (Cost.value (fold_right_c (probe_one_c n) [] bs))) <=
    (1 + N.of_nat (length (index_get (table n)
      (map (inst (binding_value b)) (key_terms n))))) * join_unit_cost a h v e w) in Hhead.
  change (1 + Cost.ticks (fold_right_c (probe_one_c n) [] bs) +
    Cost.ticks (probe_one_c n b (Cost.value (fold_right_c (probe_one_c n) [] bs))) <=
    ((1 + N.of_nat (length (index_get (table n)
      (map (inst (binding_value b)) (key_terms n))))) + probe_work n bs) *
      join_unit_cost a h v e w).
  rewrite N.mul_add_distr_r; lia.
Qed.

(** Every reached atom carries primitive budgets for its actual input binding list. *)
Fixpoint run_primitives {P} (plan : plan_state P) bs a h v e w : Prop :=
  match plan with
  | [] => True
  | n :: rest =>
    probe_primitives n bs a h v e w /\
    run_primitives rest (probe n bs) a h v e w
  end.

Lemma run_from_cost {P} (plan : plan_state P) bs a h v e w :
  run_primitives plan bs a h v e w ->
  Cost.ticks (run_from_c plan bs) <= work_from plan bs * join_unit_cost a h v e w.
Proof.
  revert bs; induction plan as [|n plan IH]; intros bs Hprimitives.
  - change (0 <= 0); lia.
  - destruct Hprimitives as [Hprobe Hrest].
    cbn [run_from_c]; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step.
    fold (@probe P n bs).
    pose proof (probe_cost n bs a h v e w Hprobe).
    pose proof (IH (probe n bs) Hrest).
    pose proof (join_unit_positive a h v e w).
    change (1 + (Cost.ticks (probe_c n bs) + Cost.ticks (run_from_c plan (probe n bs))) <=
      (1 + probe_work n bs + work_from plan (probe n bs)) * join_unit_cost a h v e w).
    nia.
Qed.

(** Indexed join ticks are linear in probe-and-bucket work at the explicit primitive coefficient. *)
Theorem join_run_cost {P} (plan : plan_state P) a h v e w :
  run_primitives plan [[]] a h v e w ->
  Cost.ticks (run_c plan) <= (work plan + 1) * join_unit_cost a h v e w.
Proof.
  intro Hprimitives; pose proof (run_from_cost plan [[]] a h v e w Hprimitives).
  unfold run_c, work; nia.
Qed.

(** Varying plans retain a big-O bound in both join work and primitive key and binding costs. *)
Theorem join_run_bigO {X P} (plan : X -> plan_state P)
    (a h : X -> nat) (v e w : X -> N) :
  (forall x, run_primitives (plan x) [[]] (a x) (h x) (v x) (e x) (w x)) ->
  bigO (fun x => (work (plan x) + 1) * join_unit_cost (a x) (h x) (v x) (e x) (w x))
    (fun x => Cost.ticks (run_c (plan x))).
Proof.
  intro Hprimitives; exists 1; intro x.
  pose proof (join_run_cost _ _ _ _ _ _ (Hprimitives x)); nia.
Qed.

End JoinCost.
Import JoinCost.
