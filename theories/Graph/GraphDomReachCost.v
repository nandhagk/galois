(** * Scope-sensitive bounds for the shared closure

    Scoped bounds compose the public reachability equations without another closure implementation.
    For example, a blocked-node query pays its singleton membership at each admitted candidate.
    Builds on: GraphFrontierSweep, GraphWalk and the public scope and list cost contracts. *)

From Stdlib Require Import List Bool PArith NArith Nnat Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphReach
  GraphDomSpec GraphWalk GraphFrontierSweep.
Import List.ListNotations Cost.Notations.

Module DomReachCost.
Local Open Scope N_scope.

Definition successor_bound n m w q hs := q + m * (hs + 2 + n * (w + 1)).

(** The scoped closure budget retains setup, supplied roots, credit, unary conversion and the driver. *)
Definition reach_bound n m l w a q hs :=
  let next := successor_bound n m w q hs in
  FrontierSweep.universe_work n w a + n * (1 + hs + l * (w + 1)) +
    n * (2 + next + m) + n +
    (n * (m + 2) + 1) * (12 + next + m + 2 * n * (w + 1) + w).

Local Lemma comparisons {V E} (p : Prepared.t V E) t n m l b w a q h s
    (Hr : FrontierSweep.resources p t n m l b w a q h s) v :
  Prepared.valid_id p v -> forall x, Cost.ticks (Map.code_compare_c v x) <= w.
Proof.
  intros Hv x. eapply N.le_trans; [apply Map.code_compare_cost|].
  exact (FrontierSweep.width_bound Hr v Hv).
Qed.

(** Scoped successor costs use the actual supplied admission budget on valid IDs. *)
Theorem successors_cost {V E} (p : Prepared.t V E) scope t n m l b w a q h s hs i :
  Prepared.ready p -> FrontierSweep.resources p t n m l b w a q h s ->
  (forall v, Prepared.valid_id p v -> Cost.ticks (Scope.admits_c scope v) <= hs) ->
  Prepared.valid_id p i ->
  Cost.ticks (FrontierSweep.successors_c p scope (Reach.universe p) i) <=
    successor_bound (N.of_nat n) (N.of_nat m) w q hs /\
  Forall (Prepared.valid_id p)
    (Cost.value (FrontierSweep.successors_c p scope (Reach.universe p) i)) /\
  (length (Cost.value (FrontierSweep.successors_c p scope (Reach.universe p) i)) <= m)%nat.
Proof.
  intros Hready Hr Hscope_cost Hi.
  assert (Htargets : Forall (Prepared.valid_id p) (map snd (Prepared.succ_edges p i))).
  { apply Forall_forall. intros v Hv. apply in_map_iff in Hv.
    destruct Hv as [[e j] [Heq Hin]]. cbn [snd] in Heq. subst j.
    exact (proj1 (Forall_forall _ _)
      (FrontierSweep.successor_support p i Hready) (e, v) Hin). }
  pose proof (FrontierSweep.successor_length_bound Hr i Hi) as Hlength.
  assert (Hmap : Cost.ticks (map_c (fun edge => Cost.ret (snd edge))
    (Prepared.succ_edges p i)) <= N.of_nat m).
  { pose proof (ticks_map_c_le (fun edge : E * positive => Cost.ret (snd edge))
      0 (Prepared.succ_edges p i) ltac:(intros; reflexivity)). nia. }
  assert (Hfilter : Cost.ticks (filter_c (fun v =>
    let* admitted := Scope.admits_c scope v in
    let* valid := FrontierSweep.member_c v (Reach.universe p) in
    Cost.ret (admitted && valid)) (map snd (Prepared.succ_edges p i))) <=
      N.of_nat m * (hs + N.of_nat n * (w + 1) + 1)).
  { rewrite ticks_filter_c. eapply N.le_trans.
    - apply (FrontierSweep.sum_bound_on _ (hs + N.of_nat n * (w + 1))).
      intros v Hv.
      pose proof (proj1 (Forall_forall _ _) Htargets v Hv) as Hvalid.
      pose proof (Hscope_cost v Hvalid).
      pose proof (FrontierSweep.member_cost v (Reach.universe p) w
        (comparisons p t n m l b w a q h s Hr v Hvalid)).
      pose proof (FrontierSweep.universe_bound Hr).
      rewrite !Cost.ticks_bind. autorewrite with galois_cost. nia.
    - rewrite length_map. apply N.mul_le_mono; [lia|reflexivity]. }
  split.
  - rewrite FrontierSweep.successors_equation.
    rewrite !Cost.ticks_bind, value_map_c.
    fold (Prepared.succ_edges p i).
    pose proof (FrontierSweep.successor_lookup_bound Hr i Hi).
    unfold successor_bound.
    replace (map (fun x : E * positive => Cost.value (Cost.ret (snd x)))
      (Prepared.succ_edges p i)) with (map snd (Prepared.succ_edges p i)) by reflexivity.
    nia.
  - rewrite FrontierSweep.successors_equation.
    autorewrite with galois_cost. fold (Prepared.succ_edges p i).
    split.
    + apply Forall_forall. intros v Hv. apply filter_In in Hv.
      exact (proj1 (Forall_forall _ _) Htargets v (proj1 Hv)).
    + eapply Nat.le_trans; [apply List.filter_length_le|].
      rewrite length_map. exact Hlength.
Qed.

(** Scoped root filtering retains every supplied-root membership comparison. *)
Theorem roots_cost {V E} (p : Prepared.t V E) scope t n m l b w a q h s hs :
  FrontierSweep.resources p t n m l b w a q h s ->
  (forall v, Prepared.valid_id p v -> Cost.ticks (Scope.admits_c scope v) <= hs) ->
  Cost.ticks (FrontierSweep.roots_c scope (Reach.universe p) (Prepared.entry_ids p)) <=
    N.of_nat n * (1 + hs + N.of_nat l * (w + 1)) /\
  Forall (Prepared.valid_id p)
    (Cost.value (FrontierSweep.roots_c scope (Reach.universe p) (Prepared.entry_ids p))) /\
  (length (Cost.value
    (FrontierSweep.roots_c scope (Reach.universe p) (Prepared.entry_ids p))) <= n)%nat.
Proof.
  intros Hr Hscope_cost. rewrite FrontierSweep.roots_equation. split.
  - rewrite ticks_filter_c. eapply N.le_trans.
    + apply (FrontierSweep.sum_bound_on _ (hs + N.of_nat l * (w + 1))).
      intros v Hv. pose proof (proj1 (Reach.universe_spec p v) Hv) as Hvalid.
      pose proof (Hscope_cost v Hvalid).
      pose proof (FrontierSweep.member_cost v (Prepared.entry_ids p) w
        (comparisons p t n m l b w a q h s Hr v Hvalid)).
      pose proof (FrontierSweep.entries_bound Hr).
      rewrite !Cost.ticks_bind. autorewrite with galois_cost. nia.
    + apply N.mul_le_mono; [pose proof (FrontierSweep.universe_bound Hr); lia|nia].
  - rewrite value_filter_c. split.
    + apply Forall_forall. intros v Hv. apply filter_In in Hv.
      apply Reach.universe_spec. exact (proj1 Hv).
    + eapply Nat.le_trans; [apply List.filter_length_le|].
      exact (FrontierSweep.universe_bound Hr).
Qed.

Local Lemma fuel_N n : N.pos (Pos.of_succ_nat n) = N.of_nat (S n).
Proof.
  rewrite <- (N2Nat.id (N.pos (Pos.of_succ_nat n))).
  cbn [N.to_nat]. now rewrite SuccNat2Pos.id_succ.
Qed.

Local Lemma materialize_cost {V E} (p : Prepared.t V E) t n m l b w a q h s
    (Hr : FrontierSweep.resources p t n m l b w a q h s) xs :
  Forall (Prepared.valid_id p) xs ->
  Cost.ticks (FinSet.of_list_c positive_encoding xs) <= N.of_nat (length xs) * (w + 4).
Proof.
  intro Hsupport. eapply N.le_trans.
  - apply (FinSet.of_list_numeric_cost Map.cost_laws_hold positive_encoding xs 1 w).
    intros i Hi. split; [rewrite positive_encoding_cost; reflexivity|].
    exact (FrontierSweep.width_bound Hr i
      (proj1 (Forall_forall _ _) Hsupport i Hi)).
  - apply N.mul_le_mono; [reflexivity|nia].
Qed.

(** Scoped reachability has a closed public-callee polynomial bound without another runtime loop. *)
Theorem reach_cost {V E} (p : Prepared.t V E) scope t n m l b w a q h s hs :
  Prepared.ready p -> FrontierSweep.resources p t n m l b w a q h s ->
  (forall v, Prepared.valid_id p v -> Cost.ticks (Scope.admits_c scope v) <= hs) ->
  Cost.ticks (FrontierSweep.reach_c p scope (Prepared.entry_ids p)) <=
    reach_bound (N.of_nat n) (N.of_nat m) (N.of_nat l) w a q hs.
Proof.
  intros Hready Hr Hscope_cost.
  set (P := Prepared.valid_id p).
  set (all := Reach.universe p).
  set (next := FrontierSweep.successors_c p scope all).
  set (initial := Cost.value (FrontierSweep.roots_c scope all (Prepared.entry_ids p))).
  set (credit := Cost.value (FrontierSweep.credit_c next all)).
  set (fuel := Pos.of_succ_nat (credit + length initial)).
  set (kn := successor_bound (N.of_nat n) (N.of_nat m) w q hs).
  assert (Hnext : forall v, P v -> Forall P (Cost.value (next v)) /\
    (length (Cost.value (next v)) <= m)%nat /\ Cost.ticks (next v) <= kn).
  { intros v Hv.
    destruct (successors_cost p scope t n m l b w a q h s hs v Hready Hr Hscope_cost Hv)
      as [Hcost [Hsupport Hlength]].
    exact (conj Hsupport (conj Hlength Hcost)). }
  pose proof (FrontierSweep.universe_cost p t n m l b w a q h s Hready Hr
    (comparisons p t n m l b w a q h s Hr)) as Huniverse.
  destruct (roots_cost p scope t n m l b w a q h s hs Hr Hscope_cost)
    as [Hroots [Hinitial Hinitial_length]].
  fold all in Hroots, Hinitial, Hinitial_length.
  fold initial in Hinitial, Hinitial_length.
  destruct (FrontierSweep.credit_cost next P all n m kn (FrontierSweep.universe_support p)
    (FrontierSweep.universe_bound Hr)
    ltac:(intros v Hv; exact (proj2 (Hnext v Hv)))) as [Hcredit Hcredit_length].
  fold credit in Hcredit_length.
  assert (Hfuel : N.pos fuel <= N.of_nat n * (N.of_nat m + 2) + 1).
  { unfold fuel. rewrite fuel_N, Nat2N.inj_succ, Nat2N.inj_add.
    assert (Hc : N.of_nat credit <= N.of_nat n * (N.of_nat m + 1)).
    { replace (N.of_nat n * (N.of_nat m + 1)) with (N.of_nat (n * (m + 1)%nat))
        by (rewrite Nat2N.inj_mul, Nat2N.inj_add; reflexivity).
      lia. }
    nia. }
  assert (Hlists : forall v xs, P v -> (length xs <= n)%nat ->
    Cost.ticks (FrontierSweep.member_c v xs) <= N.of_nat n * (w + 1) /\
    Cost.ticks (FrontierSweep.remove_c v xs) <= N.of_nat n * (w + 1) /\
    (length (Cost.value (FrontierSweep.remove_c v xs)) <= length xs)%nat).
  { intros v xs Hv Hlength.
    pose proof (comparisons p t n m l b w a q h s Hr v Hv) as Hcompare.
    pose proof (FrontierSweep.member_cost v xs w Hcompare) as Hmember.
    destruct (FrontierSweep.remove_cost v xs w Hcompare) as [Hremove Hshort].
    assert (Hscale : N.of_nat (length xs) * (w + 1) <= N.of_nat n * (w + 1)).
    { apply N.mul_le_mono; [lia|reflexivity]. }
    split; [eapply N.le_trans; eassumption|].
    split; [eapply N.le_trans; eassumption|exact Hshort]. }
  pose proof (Walk.closure_cost next FrontierSweep.member_c FrontierSweep.remove_c P n m kn
    (N.of_nat n * (w + 1)) (N.of_nat n * (w + 1))
    fuel initial all Hinitial (FrontierSweep.universe_bound Hr) Hnext Hlists) as Hloop.
  destruct (Walk.closure_seen next FrontierSweep.member_c FrontierSweep.remove_c P fuel
    initial all Hinitial ltac:(intros v Hv; exact (proj1 (Hnext v Hv))))
    as [Hseen Hseen_length].
  pose proof (materialize_cost p t n m l b w a q h s Hr _ Hseen) as Hset.
  assert (HseenN : N.of_nat (length (snd (Cost.value
    (Walk.closure_c next FrontierSweep.member_c FrontierSweep.remove_c fuel initial all [])))) <=
    N.pos fuel).
  { rewrite <- (N2Nat.id (N.pos fuel)). cbn [N.to_nat]. lia. }
  assert (Hset' : Cost.ticks (FinSet.of_list_c positive_encoding (snd (Cost.value
    (Walk.closure_c next FrontierSweep.member_c FrontierSweep.remove_c fuel initial all [])))) <=
    (N.of_nat n * (N.of_nat m + 2) + 1) * (w + 4)).
  { eapply N.le_trans; [exact Hset|].
    apply N.mul_le_mono; [lia|reflexivity]. }
  rewrite FrontierSweep.reach_equation.
  rewrite Cost.ticks_bind, FrontierSweep.universe_value. fold all next.
  rewrite !Cost.ticks_bind, value_length_c, Prepared.budget_cost, Prepared.budget_value.
  fold initial credit fuel. rewrite ticks_length_c.
  assert (Hconversion : N.of_nat (credit + length initial) <=
    N.of_nat n * (N.of_nat m + 2) + 1).
  { unfold fuel in Hfuel. rewrite fuel_N in Hfuel. lia. }
  assert (Hloop' : Cost.ticks
    (Walk.closure_c next FrontierSweep.member_c FrontierSweep.remove_c fuel initial all []) <=
    (6 + kn + 2 * N.of_nat n * (w + 1) + N.of_nat m) *
      (N.of_nat n * (N.of_nat m + 2) + 1)).
  { eapply N.le_trans; [exact Hloop|].
    apply N.mul_le_mono; [nia|exact Hfuel]. }
  assert (HinitialN : N.of_nat (length initial) <= N.of_nat n) by lia.
  unfold reach_bound. fold kn.
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Huniverse|].
    apply N.add_le_mono; [exact Hroots|].
    apply N.add_le_mono; [exact Hcredit|].
    apply N.add_le_mono; [exact HinitialN|].
    apply N.add_le_mono; [exact Hconversion|].
    apply N.add_le_mono; [exact Hloop'|exact Hset'].
  - clear -n m l w a q hs kn. nia.
Qed.

(** A blocked scope has no region query and pays the complete positive-ID membership width. *)
Theorem blocked_admission_cost d v w :
  N.pos (Pos.size v) <= w -> Cost.ticks (Scope.admits_c (Reach.blocked d) v) <= 3 + w.
Proof.
  intro Hwidth. rewrite Scope.admits_cost_equation, Reach.blocked_equation.
  cbn [Scope.blocked Scope.within].
  pose proof (FrontierSweep.positive_mem_cost
    (FinSet.add positive_encoding d FinSet.empty) v w Hwidth).
  destruct (FinSet.mem positive_encoding v
    (FinSet.add positive_encoding d FinSet.empty)); lia.
Qed.

End DomReachCost.
