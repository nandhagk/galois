(** * Numeric domains of hierarchy calls

    Actual SCC members, counters and header-deleted scopes satisfy the primitive hierarchy budgets.
    For example, all child roots are distinct valid global IDs and retain the global fuel width.
    Builds on: GraphTarjanExact, GraphHierProducer and GraphHierWork. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchInvariant GraphSearchCost GraphSearchScopedCost GraphSccSpec GraphHierSpec GraphHier
  GraphHierFacts GraphHierProducer GraphHierWork GraphHierLocalCost GraphTarjan GraphTarjanExact
  GraphTarjanCost GraphTarjanState GraphTarjanPartition.
Import List.ListNotations.
Local Open Scope N_scope.

Module HierCostData.

(** Ready interner storage contains exactly the listed graph nodes. *)
Theorem interner_node_count {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
    Intern.size (Prepared.names p) = length (Graph.nodes (Prepared.graph p)).
Proof.
  intros [Hgraph [Hout Hp]].
  pose proof (Intern.wf_maps (Prepared.node_enc p) (Prepared.names p)
    (Prepared.names_wf p Hp)) as [Htable Hinverse].
  assert (Hperm : Permutation (Graph.nodes (Prepared.graph p))
    (map fst (Map.elements (Intern.table (Prepared.names p))))).
  { apply NoDup_Permutation;
      [exact (nodes_nodup Hgraph)|exact (Map.elements_nodup (Prepared.node_enc p) _ Htable)|].
    intro v. rewrite (Prepared.ids_domain p Hp v), in_map_iff. split.
    - intros [i Hi]. exists (v, i). split; [reflexivity|].
      apply (Map.elements_spec (Prepared.node_enc p) (Prepared.encoding_valid p Hp) v i
        _ Htable). rewrite <- Intern.find_equation, <- Prepared.id_of_equation. exact Hi.
    - intros [[u i] [Heq Hin]]. cbn [fst] in Heq. subst u.
      exists i. rewrite Prepared.id_of_equation, Intern.find_equation.
      apply (Map.elements_spec (Prepared.node_enc p) (Prepared.encoding_valid p Hp)
        v i _ Htable), Hin. }
  pose proof (Permutation_length Hperm) as Hlength.
  rewrite length_map, <- Map.size_elements, <- Intern.size_equation in Hlength.
  symmetry. exact Hlength.
Qed.

(** Every positive component position up to the node count is itself a valid dense global ID. *)
Theorem counter_valid {V E} (p : Prepared.t V E) i :
  Prepared.ready p -> (Pos.to_nat i <= length (Graph.nodes (Prepared.graph p)))%nat ->
    Prepared.valid_id p i.
Proof.
  intros Hready Hindex. pose proof (proj2 (proj2 Hready)) as Hp.
  rewrite <- (interner_node_count p Hready) in Hindex.
  destruct (proj1 (Intern.ids_size (Prepared.node_enc p) (Prepared.encoding_valid p Hp) i
    (Prepared.names p) (Prepared.names_wf p Hp)) Hindex) as [v Hi].
  exists v. assert (Hid : Prepared.id_of p v = Some i).
  { rewrite Prepared.id_of_equation. exact Hi. }
  split; [apply (Prepared.ids_domain p Hp); now exists i|exact Hid].
Qed.

(** Readiness and the public valid-ID width budget discharge finite component-counter widths. *)
Theorem counter_width {V E} (p : Prepared.t V E) roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w -> HierLocalCost.counter_width p w.
Proof.
  intros Hready Hwidth i Hi. apply Hwidth. left. exact (counter_valid p i Hready Hi).
Qed.

(** Every actual owner index lies within the global source-node count. *)
Theorem owners_width {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> HierLocalCost.counter_width p w ->
    HierLocalCost.owner_width (Tarjan.compute p scope roots) w.
Proof.
  intros Hready Hwidth v i Howner. apply Hwidth.
  apply (TarjanExact.owners_exact p scope roots v i Hready) in Howner.
  destruct Howner as [c [Hnth Hv]].
  assert (Hindex :
    (Nat.pred (Pos.to_nat i) < length (Scc.components (Tarjan.compute p scope roots)))%nat).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  destruct (TarjanExact.component_count_bounds p scope roots Hready) as [Hcomponents [_ Hnodes]].
  pose proof (Pos2Nat.is_pos i). lia.
Qed.

(** Exact component member lists are duplicate-free valid IDs. *)
Theorem component_domain {V E} (p : Prepared.t V E) scope roots c :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) ->
    NoDup c /\ forall v, In v c -> Prepared.valid_id p v.
Proof.
  intros Hready Hc.
  pose proof (TarjanExact.block_exact p scope roots c Hready Hc) as Hblock.
  split; [exact (proj1 (proj2 Hblock))|]. intros v Hv.
  destruct (proj1 (proj2 (proj2 Hblock)) v Hv) as [root [es [_ Hpath]]].
  exact (proj1 (HierFacts.path_target p scope root es v Hpath)).
Qed.

(** Actual component flattening has no duplicates and contains valid IDs only. *)
Theorem partition_domain {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  NoDup (concat (Scc.components (Tarjan.compute p scope roots))) /\
  forall v, In v (concat (Scc.components (Tarjan.compute p scope roots))) -> Prepared.valid_id p v.
Proof.
  intro Hready. split; [apply TarjanExact.partition_unique, Hready|].
  intros v Hv. apply (TarjanExact.partition_complete p scope roots v Hready) in Hv.
  destruct Hv as [root [es [_ Hpath]]].
  exact (proj1 (HierFacts.path_target p scope root es v Hpath)).
Qed.

(** Selected child lists are duplicate-free, valid and admitted in their actual child scope. *)
Theorem child_domain {V E} (p : Prepared.t V E) scope roots c preferred h body :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) ->
  HierRun.select preferred c = Some (h, body) ->
  NoDup body /\ forall v, In v body ->
    Prepared.valid_id p v /\ Scope.admits (HierRun.child_scope scope h body) v = true.
Proof.
  intros Hready Hc Hselected.
  destruct (component_domain p scope roots c Hready Hc) as [Hnodup Hvalid].
  pose proof (HierRun.select_permutation preferred c h body Hselected) as Hperm.
  pose proof (Permutation_NoDup Hperm Hnodup) as Hselected_nodup.
  inversion Hselected_nodup as [|head tail Hfresh Htail]; subst.
  split; [exact Htail|]. intros v Hv. split.
  - apply Hvalid. exact (Permutation_in v (Permutation_sym Hperm) (or_intror Hv)).
  - pose proof (TarjanExact.block_exact p scope roots c Hready Hc) as Hblock.
    destruct (proj1 (proj2 (proj2 Hblock)) v
      (Permutation_in v (Permutation_sym Hperm) (or_intror Hv))) as [root [es [_ Hpath]]].
    pose proof (proj2 (HierFacts.path_target p scope root es v Hpath)) as Hallowed.
    rewrite Scope.admits_equation in Hallowed. apply andb_true_iff in Hallowed.
    destruct Hallowed as [Hblocked Hwithin]. apply negb_true_iff in Hblocked.
    rewrite Scope.admits_equation, HierRun.child_scope_equation.
    cbn [Scope.blocked Scope.within]. rewrite FinSet.mem_add_raw.
    assert (Hne : eqb positive_encoding v h = false).
    { apply Bool.not_true_is_false. intro Heq.
      apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq.
      subst v. contradiction. }
    rewrite Hne, Hblocked. cbn [orb negb andb].
    rewrite FinSet.mem_of_list. apply TarjanStateFacts.member_test, Hv.
Qed.

(** A valid admitted selected body is exactly its child scope's valid source support. *)
Theorem child_support {V E} (p : Prepared.t V E) scope h body :
  Prepared.ready p -> NoDup body ->
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  Permutation body (ScopedSearchCost.vertices p (HierRun.child_scope scope h body)).
Proof.
  intros Hready Hnodup Hdomain. apply HierWork.scoped_support; [exact Hready|exact Hnodup|].
  intro v. split; [apply Hdomain|].
  intros [_ Ha]. rewrite Scope.admits_equation, HierRun.child_scope_equation in Ha.
  apply andb_true_iff in Ha. cbn [Scope.within] in Ha.
  rewrite FinSet.mem_of_list in Ha. apply TarjanStateFacts.member_test. exact (proj2 Ha).
Qed.

(** Root and scoped source counts give the child SCC call its component-sensitive budget. *)
Theorem child_scc_cost {V E} (p : Prepared.t V E) scope h body w :
  Prepared.ready p -> SearchCost.width_bound p [] w -> NoDup body ->
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  Cost.ticks (Tarjan.compute_c p (HierRun.child_scope scope h body) (rev body)) <=
    2 * TarjanCost.scc_k * HierWork.mass p w body.
Proof.
  intros Hready Hwidth Hnodup Hdomain.
  assert (Hroots : SearchCost.width_bound p (rev body) w).
  { intros v [Hv|Hv].
    - apply Hwidth. now left.
    - apply Hwidth. left. exact (proj1 (Hdomain v (proj2 (in_rev body v) Hv))). }
  pose proof (TarjanCost.scc_scoped_cost p (HierRun.child_scope scope h body) (rev body) w
    Hready Hroots) as Hcost.
  pose proof (child_support p scope h body Hready Hnodup Hdomain) as Hsupport.
  assert (Hmass : HierWork.mass p w body =
    HierWork.mass p w (ScopedSearchCost.vertices p (HierRun.child_scope scope h body))).
  { apply HierWork.sum_permutation, Hsupport. }
  rewrite HierWork.scoped_mass in Hmass.
  pose proof (Permutation_length Hsupport) as Hlength.
  assert (Hsize : TarjanCost.scc_scoped_size p (HierRun.child_scope scope h body) (rev body) w <=
    2 * HierWork.mass p w body).
  { unfold TarjanCost.scc_scoped_size. rewrite length_rev.
    unfold ScopedSearchCost.node_count in *. unfold HierWork.fuel_width in Hmass.
    nia. }
  eapply N.le_trans; [exact Hcost|].
  pose proof (N.mul_le_mono_l _ _ TarjanCost.scc_k Hsize). nia.
Qed.

(** Global member work is bounded by sources, all outgoing occurrences and actual fuel width. *)
Theorem global_mass {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p ->
  HierWork.mass p w (concat (Scc.components (Tarjan.compute p scope roots))) <=
    (N.of_nat (length (Graph.nodes (Prepared.graph p))) +
      N.of_nat (GraphModel.edge_count (Prepared.graph p))) * (1 + w) +
      N.of_nat (length (Graph.nodes (Prepared.graph p))) * HierWork.fuel_width p.
Proof.
  intro Hready. set (xs := concat (Scc.components (Tarjan.compute p scope roots))).
  destruct (partition_domain p scope roots Hready) as [Hnodup Hvalid].
  assert (Hsub : incl xs (SearchInvariant.vertices p)).
  { intros v Hv. apply SearchInvariant.vertices_spec, Hvalid, Hv. }
  pose proof (HierWork.sum_incl
    (fun v => 1 + N.of_nat (length (Prepared.succ_edges p v))) xs
    (SearchInvariant.vertices p) Hnodup Hsub) as Hwork.
  assert (Hsum : HierWork.sum (fun v => 1 + N.of_nat (length (Prepared.succ_edges p v)))
    (SearchInvariant.vertices p) = N.of_nat (SearchInvariant.capacity p)).
  { clear Hsub Hwork. unfold SearchInvariant.capacity, SearchInvariant.vertex_work, HierWork.sum.
    induction (SearchInvariant.vertices p) as [|v rest IH]; cbn [fold_right].
    - reflexivity.
    - rewrite Nat2N.inj_add, Nat2N.inj_succ, IH. lia. }
  rewrite Hsum, SearchInvariant.capacity_equation in Hwork by exact Hready.
  rewrite Nat2N.inj_add in Hwork.
  assert (Hxs : HierWork.sum (fun v => 1 + N.of_nat (length (Prepared.succ_edges p v))) xs =
    N.of_nat (length xs) + HierWork.outgoing p xs).
  { apply HierWork.source_work. }
  rewrite Hxs in Hwork.
  destruct (TarjanExact.component_count_bounds p scope roots Hready) as [_ [_ Hlength]].
  assert (Hlength' : N.of_nat
    (length (concat (Scc.components (Tarjan.compute p scope roots)))) <=
      N.of_nat (length (Graph.nodes (Prepared.graph p)))) by lia.
  unfold HierWork.mass at 1. fold (HierWork.mass p w xs). rewrite HierWork.mass_equation.
  fold xs in Hlength'. nia.
Qed.

(** Actual child SCCs partition exactly the selected body, preserving its occurrence work. *)
Theorem child_partition {V E} (p : Prepared.t V E) scope h body :
  Prepared.ready p -> NoDup body ->
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  Permutation body (concat (Scc.components
    (Tarjan.compute p (HierRun.child_scope scope h body) (rev body)))).
Proof.
  intros Hready Hnodup Hdomain.
  apply NoDup_Permutation; [exact Hnodup|apply TarjanExact.partition_unique, Hready|].
  intro v. rewrite TarjanExact.partition_complete by exact Hready. split.
  - intro Hv. exists v, []. split.
    + exact (proj1 (in_rev body v) Hv).
    + destruct (Hdomain v Hv). now apply Search.scoped_nil.
  - intros [root [es [_ Hpath]]].
    pose proof (proj2 (HierFacts.path_target p _ root es v Hpath)) as Ha.
    rewrite Scope.admits_equation, HierRun.child_scope_equation in Ha.
    apply andb_true_iff in Ha. cbn [Scope.within] in Ha.
    rewrite FinSet.mem_of_list in Ha. apply TarjanStateFacts.member_test. exact (proj2 Ha).
Qed.

(** Child component reversal keeps body work and bounds component count by body count. *)
Theorem child_partition_work {V E} (p : Prepared.t V E) scope h body w :
  Prepared.ready p -> NoDup body ->
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  let r := Tarjan.compute p (HierRun.child_scope scope h body) (rev body) in
  HierWork.mass p w (concat (rev (Scc.components r))) = HierWork.mass p w body /\
  (length (Scc.components r) <= length body)%nat.
Proof.
  intros Hready Hnodup Hdomain r.
  pose proof (child_partition p scope h body Hready Hnodup Hdomain) as Hpartition.
  fold r in Hpartition. split.
  - apply HierWork.sum_permutation.
    eapply Permutation_trans.
    + apply Permutation_sym, TarjanPartition.concat_rev_permutation.
    + apply Permutation_sym, Hpartition.
  - destruct (TarjanExact.component_count_bounds p
      (HierRun.child_scope scope h body) (rev body) Hready) as [Hcount _].
    fold r in Hcount. pose proof (Permutation_length Hpartition). lia.
Qed.

(** The actual setup budget separates supplied roots from all reached source and outgoing work. *)
Theorem entries_actual_cost {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w -> HierLocalCost.counter_width p w ->
  Cost.ticks (HierRun.entries_c p roots (Tarjan.compute p scope roots)) <=
    128 * (N.of_nat (length roots) * (1 + w) +
      HierWork.mass p w (concat (Scc.components (Tarjan.compute p scope roots)))).
Proof.
  intros Hready Hwidth Hcounter.
  pose proof (HierLocalCost.entries_cost p w (Tarjan.compute p scope roots) roots
    Hready Hwidth (owners_width p scope roots w Hready Hcounter)
    (proj2 (partition_domain p scope roots Hready))) as Hcost.
  destruct (TarjanExact.component_count_bounds p scope roots Hready) as [Hcount _].
  assert (Hcount' : N.of_nat (length (Scc.components (Tarjan.compute p scope roots))) <=
    N.of_nat (length (concat (Scc.components (Tarjan.compute p scope roots))))) by lia.
  rewrite HierWork.mass_equation. nia.
Qed.

(** Child setup retains its distinct-root construction and every scoped outgoing occurrence. *)
Theorem child_entries_cost {V E} (p : Prepared.t V E) scope h body w :
  Prepared.ready p -> SearchCost.width_bound p [] w -> HierLocalCost.counter_width p w ->
  NoDup body ->
  (forall v, In v body -> Prepared.valid_id p v /\
    Scope.admits (HierRun.child_scope scope h body) v = true) ->
  Cost.ticks (HierRun.entries_c p (rev body)
    (Tarjan.compute p (HierRun.child_scope scope h body) (rev body))) <=
      256 * HierWork.mass p w body.
Proof.
  intros Hready Hwidth Hcounter Hnodup Hdomain.
  assert (Hroots : SearchCost.width_bound p (rev body) w).
  { intros v [Hv|Hv]; apply Hwidth; left; [exact Hv|].
    exact (proj1 (Hdomain v (proj2 (in_rev body v) Hv))). }
  pose proof (entries_actual_cost p (HierRun.child_scope scope h body) (rev body) w
    Hready Hroots Hcounter) as Hcost.
  pose proof (HierWork.sum_permutation (HierWork.weight p w) _ _
    (child_partition p scope h body Hready Hnodup Hdomain)) as Hmass.
  fold (HierWork.mass p w body) in Hmass.
  fold (HierWork.mass p w (concat (Scc.components
    (Tarjan.compute p (HierRun.child_scope scope h body) (rev body))))) in Hmass.
  rewrite <- Hmass, length_rev in Hcost.
  rewrite HierWork.mass_equation in *. nia.
Qed.

(** Scoped member work counts admitted valid sources and all their outgoing occurrences. *)
Theorem scoped_mass {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p ->
  HierWork.mass p w (concat (Scc.components (Tarjan.compute p scope roots))) <=
    (N.of_nat (ScopedSearchCost.node_count p scope) +
      N.of_nat (ScopedSearchCost.edge_count p scope)) * (1 + w) +
      N.of_nat (ScopedSearchCost.node_count p scope) * HierWork.fuel_width p.
Proof.
  intro Hready. rewrite <- HierWork.scoped_mass.
  apply HierWork.sum_incl; [apply TarjanExact.partition_unique, Hready|].
  intros v Hv. apply ScopedSearchCost.vertices_spec.
  apply (TarjanExact.partition_complete p scope roots v Hready) in Hv.
  destruct Hv as [root [es [_ Hpath]]].
  exact (HierFacts.path_target p scope root es v Hpath).
Qed.

End HierCostData.
