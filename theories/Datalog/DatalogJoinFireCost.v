(** * Complete indexed firing costs

    Firing charges probes, negative membership tests, head projections and canonical output storage.
    For example, two pivots may emit the same head and both emissions incur construction work.
    Builds on: DatalogJoinCost and the public FinSet numerical construction contract. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire DatalogCost
  DatalogJoin DatalogJoinProof DatalogJoinCost.
Import List.ListNotations Cost.Notations Join JoinProof JoinCost.
Local Open Scope N_scope.

Module JoinFireCost.

Lemma forallb_bound_on {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (forallb_c f xs) <= N.of_nat (length xs) * (k + 1).
Proof.
  apply DatalogCost.forallb_bound_on.
Qed.

(** One binding's negative tests retain the full body inventory and actual instantiated-key widths. *)
Theorem negative_cost {P} (r : rule P) env b a h c e w :
  (length b <= h)%nat ->
  (forall atom, In (LNeg atom) (body r) ->
    (length (args atom) <= a)%nat /\
    Cost.ticks (env (pred atom)) <= c /\
    Cost.ticks (encode_c tuple_encoding
      (map (inst (binding_value b)) (args atom))) <= e /\
    key_bits tuple_encoding (map (inst (binding_value b)) (args atom)) <= w) ->
  Cost.ticks (negative_ok_c r env b) <=
    N.of_nat (length (body r)) * (3 + N.of_nat a * (1 + N.of_nat h) + c + e + w).
Proof.
  apply DatalogCost.negative_cost.
Qed.

(** Attaching the erased validity certificate leaves the primitive set-construction cost unchanged. *)
Theorem relation_build_cost rows e w :
  (forall row, In row rows ->
    Cost.ticks (encode_c tuple_encoding row) <= e /\ key_bits tuple_encoding row <= w) ->
  Cost.ticks (set_of_list_c tuple_encoding rows) <=
    N.of_nat (length rows) * (3 + e + w).
Proof.
  exact (FinSet.of_list_numeric_cost Map.cost_laws_hold tuple_encoding rows e w).
Qed.

Lemma probe_length {P} (n : node P) bs :
  N.of_nat (length (probe n bs)) <= probe_work n bs.
Proof.
  rewrite probe_equation; induction bs as [|b bs IH].
  - change (0 <= 0); lia.
  - cbn [flat_map probe_work fold_right]; rewrite length_app, Nat2N.inj_add.
    pose proof (nat_N_le _ _ (filter_map_length
      (fun row => bind_terms (args (source n)) row b)
      (index_get (table n) (map (inst (binding_value b)) (key_terms n))))) as Hlength.
    eapply N.le_trans; [apply N.add_le_mono; [exact Hlength | exact IH] |].
    change (N.of_nat (length (index_get (table n)
      (map (inst (binding_value b)) (key_terms n)))) + probe_work n bs <=
      1 + N.of_nat (length (index_get (table n)
      (map (inst (binding_value b)) (key_terms n)))) + probe_work n bs).
    lia.
Qed.

Lemma run_from_length {P} (plan : plan_state P) bs :
  N.of_nat (length (run_from plan bs)) <= N.of_nat (length bs) + work_from plan bs.
Proof.
  revert bs; induction plan as [|n plan IH]; intro bs; rewrite run_from_equation.
  - cbn [work_from]; lia.
  - specialize (IH (probe n bs)); pose proof (probe_length n bs).
    change (N.of_nat (length (run_from plan (probe n bs))) <=
      N.of_nat (length bs) + (1 + probe_work n bs + work_from plan (probe n bs))).
    lia.
Qed.

(** Probe-and-bucket work bounds every emitted binding occurrence, including duplicates. *)
Theorem join_run_length {P} (plan : plan_state P) :
  N.of_nat (length (run plan)) <= 1 + work plan.
Proof.
  exact (run_from_length plan [[]]).
Qed.

(** Firing duties bound source lengths, reached binding lengths and actual negative and head keys. *)
Definition fire_primitives {P} (r : rule P) (env : P -> Cost.t relation) (plan : plan_state P)
    (a h : nat) (v c e w : N) :=
  run_primitives plan [[]] a h v e w /\
  (length (args (head r)) <= a)%nat /\
  forall b, In b (run plan) ->
    (length b <= h)%nat /\
    (forall atom, In (LNeg atom) (body r) ->
      (length (args atom) <= a)%nat /\
      Cost.ticks (env (pred atom)) <= c /\
      Cost.ticks (encode_c tuple_encoding
        (map (inst (binding_value b)) (args atom))) <= e /\
      key_bits tuple_encoding (map (inst (binding_value b)) (args atom)) <= w) /\
    Cost.ticks (encode_c tuple_encoding
      (map (inst (binding_value b)) (args (head r)))) <= e /\
    key_bits tuple_encoding (map (inst (binding_value b)) (args (head r))) <= w.

(** The coefficient keeps literal tests, binding scans, callbacks and head storage explicitly. *)
Definition fire_unit_cost (l a h : nat) v c e w :=
  join_unit_cost a h v e w +
    N.of_nat l * (3 + N.of_nat a * (1 + N.of_nat h) + c + e + w) +
    N.of_nat a * (1 + N.of_nat h) + 5 + e + w.

Lemma fire_pipeline_cost {P} (r : rule P) env plan n i e w :
  (forall b, In b (run plan) -> Cost.ticks (negative_ok_c r env b) <= n) ->
  (forall b, In b (run plan) -> Cost.ticks (instantiate_c b (args (head r))) <= i) ->
  (forall b, In b (run plan) ->
    Cost.ticks (encode_c tuple_encoding
      (map (inst (binding_value b)) (args (head r)))) <= e /\
    key_bits tuple_encoding (map (inst (binding_value b)) (args (head r))) <= w) ->
  Cost.ticks (fire_c r env plan) <= Cost.ticks (run_c plan) +
    N.of_nat (length (run plan)) * (n + i + 5 + e + w).
Proof.
  intros Hnegative Hinstantiate Hkeys.
  set (bs := run plan).
  set (selected := filter (negative_ok r env) bs).
  set (heads := map (fun b => map (inst (binding_value b)) (args (head r))) selected).
  assert (Hfilter : Cost.ticks (filter_c (negative_ok_c r env) bs) <=
    N.of_nat (length bs) * (n + 1)).
  { rewrite ticks_filter_c; apply traversal_bound_on, Hnegative. }
  assert (Hmap : Cost.ticks (map_c (fun b => instantiate_c b (args (head r))) selected) <=
    N.of_nat (length selected) * (i + 1)).
  { rewrite ticks_map_c; apply traversal_bound_on; intros b Hb.
    apply Hinstantiate; apply filter_In in Hb; exact (proj1 Hb). }
  assert (Hbuild : Cost.ticks (set_of_list_c tuple_encoding heads) <=
    N.of_nat (length heads) * (3 + e + w)).
  { apply relation_build_cost; intros row Hrow; apply in_map_iff in Hrow
      as [b [<- Hb]]; apply Hkeys; apply filter_In in Hb; exact (proj1 Hb). }
  assert (Hlength : N.of_nat (length selected) <= N.of_nat (length bs)).
  { apply nat_N_le, filter_length_bound. }
  unfold fire_c; repeat rewrite Cost.ticks_bind.
  fold (@run P plan).
  rewrite value_filter_c, value_map_c.
  change (Cost.ticks (run_c plan) +
    (Cost.ticks (filter_c (negative_ok_c r env) bs) +
    (Cost.ticks (map_c (fun b => instantiate_c b (args (head r))) selected) +
    Cost.ticks (set_of_list_c tuple_encoding
      (map (fun b => Cost.value (instantiate_c b (args (head r)))) selected)))) <=
    Cost.ticks (run_c plan) + N.of_nat (length bs) * (n + i + 5 + e + w)).
  assert (Hheads : map (fun b => Cost.value (instantiate_c b (args (head r))))
    selected = heads).
  { unfold heads; apply map_ext; intro b; apply instantiate_equation. }
  rewrite Hheads.
  assert (Hheadcount : length heads = length selected) by (apply length_map).
  rewrite Hheadcount in Hbuild.
  pose proof (N.mul_le_mono_r _ _ (i + 1) Hlength) as Hmapscale.
  pose proof (N.mul_le_mono_r _ _ (3 + e + w) Hlength) as Hbuildscale.
  lia.
Qed.

(** Complete firing is linear in actual indexed work at the full primitive-relative coefficient. *)
Theorem join_fire_cost {P} (r : rule P) env (plan : plan_state P) a h v c e w :
  fire_primitives r env plan a h v c e w ->
  Cost.ticks (fire_c r env plan) <=
    (work plan + 1) * fire_unit_cost (length (body r)) a h v c e w.
Proof.
  intros [Hrun [Hhead Hbindings]].
  set (n := N.of_nat (length (body r)) *
    (3 + N.of_nat a * (1 + N.of_nat h) + c + e + w)).
  set (i := N.of_nat a * (1 + N.of_nat h)).
  assert (Hnegative : forall b, In b (run plan) -> Cost.ticks (negative_ok_c r env b) <= n).
  { intros b Hb; destruct (Hbindings b Hb) as [Hlen [Hneg _]].
    apply (negative_cost r env b a h c e w Hlen Hneg). }
  assert (Hinstantiate : forall b, In b (run plan) ->
    Cost.ticks (instantiate_c b (args (head r))) <= i).
  { intros b Hb; destruct (Hbindings b Hb) as [Hlen _].
    eapply N.le_trans; [apply instantiate_cost |].
    unfold i; apply N.mul_le_mono; [apply nat_N_le, Hhead |].
    pose proof (nat_N_le _ _ Hlen); lia. }
  pose proof (fire_pipeline_cost r env plan n i e w Hnegative Hinstantiate
    (fun b Hb => proj2 (proj2 (Hbindings b Hb)))) as Hpipeline.
  pose proof (join_run_cost plan a h v e w Hrun) as Hjoin.
  pose proof (join_run_length plan) as Hcount.
  pose proof (N.mul_le_mono_r _ _ (n + i + 5 + e + w) Hcount) as Hscale.
  unfold fire_unit_cost; fold n; fold i; nia.
Qed.

(** The firing family bound permits source widths, callbacks and all key budgets to vary. *)
Theorem join_fire_bigO {X P} (r : X -> rule P) (env : X -> P -> Cost.t relation)
    (plan : X -> plan_state P) (a h : X -> nat) (v c e w : X -> N) :
  (forall x, fire_primitives (r x) (env x) (plan x)
    (a x) (h x) (v x) (c x) (e x) (w x)) ->
  bigO (fun x => (work (plan x) + 1) *
    fire_unit_cost (length (body (r x))) (a x) (h x) (v x) (c x) (e x) (w x))
    (fun x => Cost.ticks (fire_c (r x) (env x) (plan x))).
Proof.
  intro Hprimitives; exists 1; intro x.
  pose proof (join_fire_cost _ _ _ _ _ _ _ _ _ (Hprimitives x)); nia.
Qed.

End JoinFireCost.
Import JoinFireCost.
