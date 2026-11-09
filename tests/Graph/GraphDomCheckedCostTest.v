(** * Importing complete checked-boundary controls

    Accepted and rejected parents share input-domain proofs for complete numeric and family bounds.
    For example, an arbitrary encoder charge is retained on both selected branches.
    Builds on: GraphDomCheckedCost and existing nonempty fixture and callback clients. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseMapCost.
From Galois.Graph Require Import GraphPrepared GraphFixtures GraphDomSpec GraphCheckDom
  GraphDomBackend GraphDomFiniteView GraphDomFiniteReach GraphDomFiniteCost GraphDomGlobalCost
  GraphDomCheckedCost GraphDomFastCheck GraphDomNumber GraphDomCheckBound GraphReach.
From Galois.Tests.Graph Require Import GraphDomBackendTest GraphDomFastCheckCostTest
  GraphDomGlobalCostTest.
Import Cost.Notations.

Example checked_line_finite_bounds extra :
  DomFiniteCost.bounds (charged_line extra) (Prepared.entry_ids (charged_line extra))
    5 5 1 (extra + 8)%N (extra + 8)%N (extra + 8)%N.
Proof.
  pose proof (charged_line_bounds extra) as Hb. constructor.
  - pose proof (DomFiniteCost.input_nodes Hb). lia.
  - exact (DomFiniteCost.input_roots Hb).
  - intros v Hv. destruct (DomFiniteCost.input_keys Hb v Hv) as [Hprice Hwidth]. split; lia.
  - intros v Hv. pose proof (DomFiniteCost.universe_width Hb v Hv). lia.
  - intros v Hv. pose proof (DomFiniteCost.root_width Hb v Hv). lia.
  - intros u ev Hu Hev. pose proof (DomFiniteCost.row_width Hb u ev Hu Hev). lia.
  - intros u Hu. pose proof (DomFiniteCost.row_length Hb u Hu). lia.
  - pose proof (DomFiniteCost.graph_edges Hb). lia.
  - pose proof (DomFiniteCost.dense_width Hb). lia.
Qed.

Definition selected_candidate (accepted : bool) :=
  if accepted then Fixtures.Line.tree else bad_line.

Example selected_storage accepted :
  Map.wf positive_encoding (Dom.idom (selected_candidate accepted)).
Proof.
  destruct accepted; [exact Fixtures.Line.parents_wf|exact bad_line_wf].
Qed.

Example selected_size accepted : (Map.size (Dom.idom (selected_candidate accepted)) <= 3)%nat.
Proof.
  destruct accepted; vm_compute; lia.
Qed.

Example selected_skeleton accepted :
  (MapCost.skeleton_nodes (Dom.idom (selected_candidate accepted)) <= 4)%N.
Proof.
  destruct accepted; vm_compute; intuition discriminate.
Qed.

Example selected_width accepted :
  DomCheckBound.stored_width (Dom.idom (selected_candidate accepted)) 3%N.
Proof.
  destruct accepted; [exact line_stored_width|].
  intros vu Hvu. vm_compute in Hvu.
  destruct Hvu as [<-|[<-|[<-|Hfalse]]]; [| | |contradiction];
    vm_compute; intuition discriminate.
Qed.

Example checked_line_ready extra : Prepared.ready (charged_line extra).
Proof.
  exact (weighted_line_ready extra).
Qed.

Example checked_line_global_bounds extra :
  DomGlobalCost.bounds (charged_line extra) 5 5 1 (extra + 8)%N.
Proof.
  exact (weighted_bounds extra).
Qed.

Example checked_line_fuel extra :
  (N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared (charged_line extra) (Prepared.entry_ids (charged_line extra))))) <=
    extra + 8)%N.
Proof.
  pose proof (charged_line_fuel_width extra). lia.
Qed.

Example complete_checked_lt_bound accepted extra :
  (Cost.ticks (DomBackend.compute_checked_c DomBackend.lt
    (charged_line extra) (selected_candidate accepted)) <=
    DomCheckedCost.wrapper_bound 5 5 1 3 (extra + 8) 3 4)%N.
Proof.
  apply DomCheckedCost.lt_cost.
  - exact (checked_line_ready extra).
  - exact (checked_line_global_bounds extra).
  - exact (checked_line_finite_bounds extra).
  - exact (checked_line_fuel extra).
  - exact (selected_storage accepted).
  - exact (selected_size accepted).
  - exact (selected_skeleton accepted).
  - exact (selected_width accepted).
Qed.

Example complete_certified_nca_bound accepted extra :
  (Cost.ticks (DomBackend.compute_checked DomBackend.semi_nca
    (charged_line extra) (selected_candidate accepted) DomBackend.semi_nca_laws
    (checked_line_ready extra) (selected_storage accepted)) <=
    DomCheckedCost.wrapper_bound 5 5 1 3 (extra + 8) 3 4)%N.
Proof.
  apply DomCheckedCost.certified_semi_nca_cost.
  - exact (checked_line_global_bounds extra).
  - exact (checked_line_finite_bounds extra).
  - exact (checked_line_fuel extra).
  - exact (selected_size accepted).
  - exact (selected_skeleton accepted).
  - exact (selected_width accepted).
Qed.

Example both_branches_nonempty_lt_family :
  bigO (fun x : bool * N => DomCheckedCost.wrapper_bound 5 5 1 3 (snd x + 8) 3 4)
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.lt
      (charged_line (snd x)) (selected_candidate (fst x)))).
Proof.
  apply DomCheckedCost.lt_bigO.
  - intro x. exact (checked_line_ready (snd x)).
  - intro x. exact (checked_line_global_bounds (snd x)).
  - intro x. exact (checked_line_finite_bounds (snd x)).
  - intro x. exact (checked_line_fuel (snd x)).
  - intro x. exact (selected_storage (fst x)).
  - intro x. exact (selected_size (fst x)).
  - intro x. exact (selected_skeleton (fst x)).
  - intro x. exact (selected_width (fst x)).
Qed.

Example both_branches_nonempty_nca_family :
  bigO (fun x : bool * N => DomCheckedCost.wrapper_bound 5 5 1 3 (snd x + 8) 3 4)
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca
      (charged_line (snd x)) (selected_candidate (fst x)))).
Proof.
  apply DomCheckedCost.semi_nca_bigO.
  - intro x. exact (checked_line_ready (snd x)).
  - intro x. exact (checked_line_global_bounds (snd x)).
  - intro x. exact (checked_line_finite_bounds (snd x)).
  - intro x. exact (checked_line_fuel (snd x)).
  - intro x. exact (selected_storage (fst x)).
  - intro x. exact (selected_size (fst x)).
  - intro x. exact (selected_skeleton (fst x)).
  - intro x. exact (selected_width (fst x)).
Qed.

Example whole_checked_table_lt accepted extra :
  (Cost.ticks (DomBackend.compute_checked_c DomBackend.lt
    (charged_line extra) (selected_candidate accepted)) <=
    DomCheckedCost.table_k * (1 + N.of_nat 5) *
      (1 + N.of_nat 5 + N.of_nat 5) * (1 + (extra + 8)))%N.
Proof.
  apply DomCheckedCost.lt_table_cost with (r := 1%nat).
  - exact (checked_line_ready extra).
  - exact (checked_line_global_bounds extra).
  - exact (checked_line_finite_bounds extra).
  - exact (checked_line_fuel extra).
  - exact (selected_storage accepted).
  - pose proof (selected_size accepted). lia.
  - intros vu Hvu. destruct (selected_width accepted vu Hvu). split; lia.
  - lia.
Qed.

Example whole_checked_table_nca_family :
  bigO (fun x : bool * N =>
    ((1 + N.of_nat 5) * (1 + N.of_nat 5 + N.of_nat 5) * (1 + (snd x + 8)))%N)
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca
      (charged_line (snd x)) (selected_candidate (fst x)))).
Proof.
  apply DomCheckedCost.semi_nca_table_bigO with (r := fun _ => 1%nat).
  - intro x. exact (checked_line_ready (snd x)).
  - intro x. exact (checked_line_global_bounds (snd x)).
  - intro x. exact (checked_line_finite_bounds (snd x)).
  - intro x. exact (checked_line_fuel (snd x)).
  - intro x. exact (selected_storage (fst x)).
  - intro x. pose proof (selected_size (fst x)). lia.
  - intros x vu Hvu. destruct (selected_width (fst x) vu Hvu). split; lia.
  - intros _. lia.
Qed.

Example accepted_full_numbering_order {V E} (p : Prepared.t V E) parents :
  Cost.value (DomBackend.checked_candidate_c p parents) =
    DomNumber.of_parents
      (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) parents.
Proof.
  apply DomBackend.checked_candidate_value.
Qed.

Example accepted_all_selected_ticks :
  Cost.ticks certified_diamond =
    (Cost.ticks (DomFastCheck.check_c Fixtures.Diamond.prepared Fixtures.Diamond.parents) +
      (Cost.ticks (DomFiniteView.prepare_c
        Fixtures.Diamond.prepared (Prepared.entry_ids Fixtures.Diamond.prepared)) +
       Cost.ticks (DomFiniteReach.reach_c
         (DomFiniteView.prepared Fixtures.Diamond.prepared
           (Prepared.entry_ids Fixtures.Diamond.prepared)) Reach.unrestricted) +
       Cost.ticks (FinSet.elements_c (Reach.set Fixtures.Diamond.prepared Reach.unrestricted
         (Prepared.entry_ids Fixtures.Diamond.prepared))) +
       Cost.ticks (DomNumber.of_parents_c
         (FinSet.elements (Reach.set Fixtures.Diamond.prepared Reach.unrestricted
           (Prepared.entry_ids Fixtures.Diamond.prepared))) Fixtures.Diamond.parents)))%N.
Proof.
  unfold certified_diamond. rewrite DomBackend.compute_checked_ticks.
  change (Dom.idom unnumbered_diamond) with Fixtures.Diamond.parents.
  assert (Haccept : DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true).
  { vm_compute. reflexivity. }
  rewrite Haccept, DomBackend.checked_candidate_cost_equation. reflexivity.
Qed.

Example rejected_same_actual_fallback :
  DomBackend.compute_checked_c DomBackend.semi_nca Fixtures.Line.prepared bad_line =
    (DomFastCheck.check_c Fixtures.Line.prepared (Dom.idom bad_line) ;;
      DomBackend.compute_c DomBackend.semi_nca Fixtures.Line.prepared).
Proof.
  exact rejected_checked_branch_client.
Qed.
