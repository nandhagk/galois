(** * Complete certified-boundary cost composition

    One fast checker selects charged canonical numbering or the actual selected producer.
    For example, rejection includes the producer's entire virtual-root preparation and output pass.
    Builds on: GraphDomFastCheckCost, GraphDomGlobalCost and GraphDomNumberCost. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Ring.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphPrepared GraphReach GraphDomSpec GraphCheckDom
  GraphSearchCost GraphDomBackend GraphDomFiniteView GraphDomFiniteReach GraphDomFiniteCost
  GraphDomFiniteQueryCost GraphDomFastCheck GraphDomFastCheckCost GraphDomNumberCost
  GraphDomGlobalCost GraphDomCheckBound GraphDomCostBasis.

Module DomCheckedCost.
Local Open Scope N_scope.

(** Canonicalization pays normalization, materialized search, enumeration and annotation. *)
Definition accepted_bound (n m r : nat) w :=
  DomFiniteCost.prepare_bound n m r w w w +
  DomFastCheckCost.query_bound n m r w w +
  (TrieCost.trie_k * (1 + N.of_nat n * w) + N.of_nat n) +
  DomNumberCost.number_bound n w.

(** The whole bound retains both branch budgets and every raw candidate-storage price. *)
Definition wrapper_bound (n m r b : nat) w wc s :=
  DomFastCheckCost.checker_bound n m r b w w w wc w s +
  accepted_bound n m r w + DomGlobalCost.lt_k * DomGlobalCost.work n m r w.

Section Candidate.
Context {V E : Type} (p : Prepared.t V E) (parents : Map.t positive positive).
Local Abbreviation seen := (Reach.set p Reach.unrestricted (Prepared.entry_ids p)).
Local Abbreviation live := (FinSet.elements seen).

Local Lemma accepted_number_bounds n m r w :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r w w w ->
  Map.wf positive_encoding parents -> DomCheck.check p parents = true ->
  DomNumberCost.bounds live parents n w.
Proof.
  intros Hb Hparents Hcheck. constructor.
  - apply (FinSet.elements_nodup positive_encoding). apply Reach.set_wf.
  - exact Hparents.
  - intros v u Hget.
    rewrite DomCheck.check_equation in Hcheck. cbn zeta in Hcheck.
    apply andb_true_iff in Hcheck. destruct Hcheck as [Hcheck _].
    apply andb_true_iff in Hcheck. destruct Hcheck as [Hdomains _].
    apply forallb_forall with (x := (v, u)) in Hdomains.
    + change (FinSet.mem positive_encoding v seen &&
        FinSet.mem positive_encoding u seen = true) in Hdomains.
      apply andb_true_iff in Hdomains. destruct Hdomains as [Hv Hu].
      split; apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
        [apply Reach.set_wf|exact Hv|apply Reach.set_wf|exact Hu].
    + exact (proj2 (Map.elements_spec positive_encoding positive_encoding_laws
        v u parents Hparents) Hget).
  - exact (DomFastCheckCost.live_length p (Prepared.entry_ids p) n m r w w w Hb).
  - intros v Hv. apply (DomFiniteCost.universe_width Hb v).
    apply (DomFastCheckCost.live_support p (Prepared.entry_ids p) v).
    exact (proj1 (FinSet.elements_spec positive_encoding positive_encoding_laws v seen
      (Reach.set_wf p _ _)) Hv).
Qed.

(** Acceptance derives numbering's finite domain from the actual Boolean binding check. *)
Theorem accepted_cost n m r w :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r w w w ->
  N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= w ->
  Map.wf positive_encoding parents -> DomCheck.check p parents = true ->
  Cost.ticks (DomBackend.checked_candidate_c p parents) <= accepted_bound n m r w.
Proof.
  intros Hb Hfuel Hparents Hcheck.
  pose proof (accepted_number_bounds n m r w Hb Hparents Hcheck) as Hnumber.
  pose proof (DomFiniteCost.prepare_cost p (Prepared.entry_ids p) n m r w w w Hb) as Hsetup.
  pose proof (DomFiniteQueryCost.reach_cost p (Prepared.entry_ids p)
    n m r w w w w (3 + 4 * w) Reach.unrestricted Hb Hfuel
    ltac:(intros v Hv; eapply N.le_trans; [apply SearchCost.admits_cost;
      exact (DomFiniteCost.universe_width Hb v Hv)|unfold SearchCost.id_cost; lia])) as Hreach.
  pose proof (DomCostBasis.elements_cost seen n w (Reach.set_wf p _ _)
    ltac:(rewrite FinSet.size_elements; exact (DomNumberCost.live_length Hnumber))
    ltac:(intros v Hv; apply (DomNumberCost.live_width Hnumber v);
      exact (proj2 (FinSet.elements_spec positive_encoding positive_encoding_laws v seen
        (Reach.set_wf p _ _)) Hv))) as Henumerate.
  pose proof (DomNumberCost.number_cost live parents n w Hnumber) as Hannotation.
  rewrite DomBackend.checked_candidate_cost_equation.
  unfold accepted_bound, DomFastCheckCost.query_bound.
  apply N.add_le_mono; [|exact Hannotation].
  apply N.add_le_mono; [|exact Henumerate].
  now apply N.add_le_mono.
Qed.

End Candidate.

Section Whole.
Context {V E : Type} (p : Prepared.t V E) (candidate : Dom.tree).
Context (n m r b : nat) (w wc s : N).
Hypothesis Hready : Prepared.ready p.
Hypothesis Hglobal : DomGlobalCost.bounds p n m r w.
Hypothesis Hfinite : DomFiniteCost.bounds p (Prepared.entry_ids p) n m r w w w.
Hypothesis Hfuel : N.pos (Pos.size (Prepared.fuel
  (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= w.
Hypothesis Hparents : Map.wf positive_encoding (Dom.idom candidate).
Hypothesis Hcard : (Map.size (Dom.idom candidate) <= b)%nat.
Hypothesis Hskeleton : MapCost.skeleton_nodes (Dom.idom candidate) <= s.
Hypothesis Hstored : DomCheckBound.stored_width (Dom.idom candidate) wc.

Local Lemma branch_cost backend :
  Cost.ticks (DomBackend.compute_c backend p) <=
    DomGlobalCost.lt_k * DomGlobalCost.work n m r w ->
  Cost.ticks (DomBackend.compute_checked_c backend p candidate) <=
    wrapper_bound n m r b w wc s.
Proof.
  intro Hfallback.
  pose proof (DomFastCheckCost.check_cost p (Dom.idom candidate)
    n m r b w w w wc w s Hfinite Hfuel Hparents Hcard Hskeleton Hstored) as Hchecker.
  rewrite DomBackend.compute_checked_cost_equation.
  destruct (DomCheck.check p (Dom.idom candidate)) eqn:Hcheck.
  - pose proof (accepted_cost p (Dom.idom candidate) n m r w
      Hfinite Hfuel Hparents Hcheck) as Haccepted.
    unfold wrapper_bound. lia.
  - unfold wrapper_bound. lia.
Qed.

(** Whole LT checked costs need finite input duties and derive the selected branch internally. *)
Theorem lt_cost :
  Cost.ticks (DomBackend.compute_checked_c DomBackend.lt p candidate) <=
    wrapper_bound n m r b w wc s.
Proof.
  apply branch_cost. exact (DomGlobalCost.lt_cost p n m r w Hready Hglobal).
Qed.

(** Whole NCA checked costs include the actual producer whenever the raw candidate is rejected. *)
Theorem semi_nca_cost :
  Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca p candidate) <=
    wrapper_bound n m r b w wc s.
Proof.
  apply branch_cost. exact (DomGlobalCost.semi_nca_cost p n m r w Hready Hglobal).
Qed.

(** LT proof refinement keeps the same complete checker and selected-branch budget. *)
Theorem certified_lt_cost Hlaws :
  Cost.ticks (DomBackend.compute_checked DomBackend.lt p candidate Hlaws Hready Hparents) <=
    wrapper_bound n m r b w wc s.
Proof.
  unfold DomBackend.compute_checked. rewrite Cost.ticks_refine. exact lt_cost.
Qed.

(** NCA proof refinement keeps every normalization, annotation and real fallback charge. *)
Theorem certified_semi_nca_cost Hlaws :
  Cost.ticks (DomBackend.compute_checked DomBackend.semi_nca p candidate Hlaws Hready Hparents) <=
    wrapper_bound n m r b w wc s.
Proof.
  unfold DomBackend.compute_checked. rewrite Cost.ticks_refine. exact semi_nca_cost.
Qed.

End Whole.

Section Family.
Context {X V E : Type} (p : X -> Prepared.t V E) (candidate : X -> Dom.tree).
Context (n m r b : X -> nat) (w wc s : X -> N).
Hypothesis Hready : forall x, Prepared.ready (p x).
Hypothesis Hglobal : forall x, DomGlobalCost.bounds (p x) (n x) (m x) (r x) (w x).
Hypothesis Hfinite : forall x, DomFiniteCost.bounds (p x) (Prepared.entry_ids (p x))
  (n x) (m x) (r x) (w x) (w x) (w x).
Hypothesis Hfuel : forall x, N.pos (Pos.size (Prepared.fuel
  (DomFiniteView.prepared (p x) (Prepared.entry_ids (p x))))) <= w x.
Hypothesis Hparents : forall x, Map.wf positive_encoding (Dom.idom (candidate x)).
Hypothesis Hcard : forall x, (Map.size (Dom.idom (candidate x)) <= b x)%nat.
Hypothesis Hskeleton : forall x, MapCost.skeleton_nodes (Dom.idom (candidate x)) <= s x.
Hypothesis Hstored : forall x, DomCheckBound.stored_width (Dom.idom (candidate x)) (wc x).

(** Complete LT checked bounds lift to families without an acceptance or desired-output premise. *)
Theorem lt_bigO :
  bigO (fun x => wrapper_bound (n x) (m x) (r x) (b x) (w x) (wc x) (s x))
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.lt (p x) (candidate x))).
Proof.
  exists 1. intro x.
  pose proof (lt_cost (p x) (candidate x) (n x) (m x) (r x) (b x) (w x) (wc x) (s x)
    (Hready x) (Hglobal x) (Hfinite x) (Hfuel x) (Hparents x)
    (Hcard x) (Hskeleton x) (Hstored x)). lia.
Qed.

(** Complete NCA checked families include charged canonicalization and the same actual fallback. *)
Theorem semi_nca_bigO :
  bigO (fun x => wrapper_bound (n x) (m x) (r x) (b x) (w x) (wc x) (s x))
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca (p x) (candidate x))).
Proof.
  exists 1. intro x.
  pose proof (semi_nca_cost (p x) (candidate x) (n x) (m x) (r x) (b x) (w x) (wc x) (s x)
    (Hready x) (Hglobal x) (Hfinite x) (Hfuel x) (Hparents x)
    (Hcard x) (Hskeleton x) (Hstored x)). lia.
Qed.

End Family.

(** The restricted wrapper coefficient retains checker, producer and annotation coefficients. *)
Definition table_k :=
  DomFastCheckCost.table_k + DomFastCheckCost.checker_k +
  DomNumberCost.number_k + DomGlobalCost.lt_k.

Local Lemma accepted_shape n m r w :
  (r <= n)%nat -> DomNumberCost.rank_width n <= w -> DomNumberCost.fuel_width n <= w ->
  accepted_bound n m r w <=
    (DomFastCheckCost.checker_k + DomNumberCost.number_k) *
      (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  intros Hr Hrank Hfuel.
  assert (Hsetup : accepted_bound n m r w <=
    DomFastCheckCost.checker_bound n m r 0 w w w 0 w 0 +
      DomNumberCost.number_bound n w).
  { unfold accepted_bound, DomFastCheckCost.checker_bound.
    cbn [N.of_nat]. lia. }
  pose proof (DomFastCheckCost.core_budget n m r w w w w Hr
    (N.le_refl _) (N.le_refl _) (N.le_refl _)) as Hcore.
  pose proof (DomNumberCost.number_shape n w w (N.le_refl _) Hrank Hfuel) as Hnumber.
  assert (Hnumber_shape : DomNumberCost.number_bound n w <=
    DomNumberCost.number_k *
      (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w)).
  { eapply N.le_trans; [exact Hnumber|].
    apply N.mul_le_mono; [apply N.mul_le_mono; lia|reflexivity]. }
  eapply N.le_trans; [exact Hsetup|].
  replace ((DomFastCheckCost.checker_k + DomNumberCost.number_k) *
    (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w)) with
    (DomFastCheckCost.checker_k *
       (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w) +
     DomNumberCost.number_k *
       (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w)) by ring.
  now apply N.add_le_mono.
Qed.

Local Lemma producer_shape n m r w :
  (r <= n)%nat ->
  DomGlobalCost.work n m r w <=
    (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  intro Hr. unfold DomGlobalCost.work. apply N.mul_le_mono; [|reflexivity].
  replace ((1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m)) with
    (N.of_nat n * N.of_nat m + N.of_nat n +
      (1 + N.of_nat n + N.of_nat n * N.of_nat n + N.of_nat m)) by ring.
  lia.
Qed.

Section Table.
Context {V E : Type} (p : Prepared.t V E) (candidate : Dom.tree) (n m r : nat) (w : N).
Hypothesis Hready : Prepared.ready p.
Hypothesis Hglobal : DomGlobalCost.bounds p n m r w.
Hypothesis Hfinite : DomFiniteCost.bounds p (Prepared.entry_ids p) n m r w w w.
Hypothesis Hfuel : N.pos (Pos.size (Prepared.fuel
  (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= w.
Hypothesis Hparents : Map.wf positive_encoding (Dom.idom candidate).
Hypothesis Hcard : (Map.size (Dom.idom candidate) <= n)%nat.
Hypothesis Hstored : DomCheckBound.stored_width (Dom.idom candidate) w.
Hypothesis Hroots : (r <= n)%nat.

Local Lemma table_branch_cost backend :
  Cost.ticks (DomBackend.compute_c backend p) <=
    DomGlobalCost.lt_k * DomGlobalCost.work n m r w ->
  Cost.ticks (DomBackend.compute_checked_c backend p candidate) <=
    table_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  intro Hfallback.
  pose proof (DomFastCheckCost.check_table_cost p (Dom.idom candidate) n m r w w w
    Hfinite Hfuel Hparents Hcard Hstored Hroots (N.le_refl _) (N.le_refl _)) as Hchecker.
  set (target := (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w)).
  assert (Hfallback_shape : Cost.ticks (DomBackend.compute_c backend p) <=
    DomGlobalCost.lt_k * target).
  { eapply N.le_trans; [exact Hfallback|].
    apply N.mul_le_mono; [reflexivity|exact (producer_shape n m r w Hroots)]. }
  pose proof (accepted_shape n m r w Hroots
    (DomGlobalCost.allocation_width Hglobal) (DomGlobalCost.output_fuel_width Hglobal))
    as Haccepted_shape.
  replace (table_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w)) with
    (table_k * target) by (unfold target; ring).
  rewrite DomBackend.compute_checked_cost_equation.
  destruct (DomCheck.check p (Dom.idom candidate)) eqn:Hcheck.
  - pose proof (accepted_cost p (Dom.idom candidate) n m r w
      Hfinite Hfuel Hparents Hcheck) as Haccepted.
    change (Cost.ticks (DomFastCheck.check_c p (Dom.idom candidate)) +
      Cost.ticks (DomBackend.checked_candidate_c p (Dom.idom candidate)) <= table_k * target).
    replace (DomFastCheckCost.table_k * (1 + N.of_nat n) *
      (1 + N.of_nat n + N.of_nat m) * (1 + w)) with
      (DomFastCheckCost.table_k * target) in Hchecker by (unfold target; ring).
    replace ((DomFastCheckCost.checker_k + DomNumberCost.number_k) *
      (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w)) with
      ((DomFastCheckCost.checker_k + DomNumberCost.number_k) * target)
      in Haccepted_shape by (unfold target; ring).
    unfold table_k. nia.
  - unfold table_k, target in *. nia.
Qed.

(** The whole LT checked boundary has the table upper bound on its explicit bounded-input domain. *)
Theorem lt_table_cost :
  Cost.ticks (DomBackend.compute_checked_c DomBackend.lt p candidate) <=
    table_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  apply table_branch_cost. exact (DomGlobalCost.lt_cost p n m r w Hready Hglobal).
Qed.

(** The same upper bound includes NCA's complete actual fallback and accepted canonicalization. *)
Theorem semi_nca_table_cost :
  Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca p candidate) <=
    table_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w).
Proof.
  apply table_branch_cost. exact (DomGlobalCost.semi_nca_cost p n m r w Hready Hglobal).
Qed.

End Table.

Section TableFamily.
Context {X V E : Type} (p : X -> Prepared.t V E) (candidate : X -> Dom.tree).
Context (n m r : X -> nat) (w : X -> N).
Hypothesis Hready : forall x, Prepared.ready (p x).
Hypothesis Hglobal : forall x, DomGlobalCost.bounds (p x) (n x) (m x) (r x) (w x).
Hypothesis Hfinite : forall x, DomFiniteCost.bounds (p x) (Prepared.entry_ids (p x))
  (n x) (m x) (r x) (w x) (w x) (w x).
Hypothesis Hfuel : forall x, N.pos (Pos.size (Prepared.fuel
  (DomFiniteView.prepared (p x) (Prepared.entry_ids (p x))))) <= w x.
Hypothesis Hparents : forall x, Map.wf positive_encoding (Dom.idom (candidate x)).
Hypothesis Hcard : forall x, (Map.size (Dom.idom (candidate x)) <= n x)%nat.
Hypothesis Hstored : forall x, DomCheckBound.stored_width (Dom.idom (candidate x)) (w x).
Hypothesis Hroots : forall x, (r x <= n x)%nat.

(** Bounded LT checked families retain all actual checker, normalization and fallback work. *)
Theorem lt_table_bigO :
  bigO (fun x => (1 + N.of_nat (n x)) *
      (1 + N.of_nat (n x) + N.of_nat (m x)) * (1 + w x))
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.lt (p x) (candidate x))).
Proof.
  exists table_k. intro x.
  eapply N.le_trans.
  - exact (lt_table_cost (p x) (candidate x) (n x) (m x) (r x) (w x)
      (Hready x) (Hglobal x) (Hfinite x) (Hfuel x)
      (Hparents x) (Hcard x) (Hstored x) (Hroots x)).
  - rewrite <- !N.mul_assoc. apply N.mul_le_mono; [reflexivity|lia].
Qed.

(** Bounded NCA checked families retain every actual accepted or rejected branch charge. *)
Theorem semi_nca_table_bigO :
  bigO (fun x => (1 + N.of_nat (n x)) *
      (1 + N.of_nat (n x) + N.of_nat (m x)) * (1 + w x))
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca (p x) (candidate x))).
Proof.
  exists table_k. intro x.
  eapply N.le_trans.
  - exact (semi_nca_table_cost (p x) (candidate x) (n x) (m x) (r x) (w x)
      (Hready x) (Hglobal x) (Hfinite x) (Hfuel x)
      (Hparents x) (Hcard x) (Hstored x) (Hroots x)).
  - rewrite <- !N.mul_assoc. apply N.mul_le_mono; [reflexivity|lia].
Qed.

End TableFamily.
End DomCheckedCost.
