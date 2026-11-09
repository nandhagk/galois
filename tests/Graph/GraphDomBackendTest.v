(** * Certification-boundary clients

    External candidates supply their own storage evidence and untrusted interval maps.
    For example, a wrong line parent is rejected by the actual certificate constructor.
    Builds on: GraphDomBackend and hand-written GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFixtures
  GraphCheckDom GraphDomBackend GraphDomNumber.
Import List.ListNotations Cost.Notations.
Open Scope positive_scope.

Definition bad_line :=
  Dom.Tree (Map.of_list positive_encoding [(2, 1); (3, 1); (4, 1)]) Map.empty Map.empty.

Example bad_line_wf : Map.wf positive_encoding (Dom.idom bad_line).
Proof.
  apply Map.wf_of_list.
Qed.

Example rejected_external_line :
  DomBackend.accept Fixtures.Line.prepared bad_line Fixtures.Line.fixture_ready bad_line_wf =
    None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition unnumbered_diamond :=
  Dom.Tree Fixtures.Diamond.parents Map.empty Map.empty.

Example accepted_external_diamond :
  exists result,
    DomBackend.accept Fixtures.Diamond.prepared unnumbered_diamond
      Fixtures.Diamond.fixture_ready Fixtures.Diamond.parents_wf = Some result.
Proof.
  apply DomBackend.accept_some_iff. vm_compute. reflexivity.
Qed.

Example accepted_parents_client result :
  DomBackend.accept Fixtures.Diamond.prepared unnumbered_diamond
    Fixtures.Diamond.fixture_ready Fixtures.Diamond.parents_wf = Some result ->
  Dom.idom (proj1_sig result) = Fixtures.Diamond.parents.
Proof.
  apply DomBackend.accept_parents.
Qed.

Example accepted_exact_client result :
  DomBackend.accept Fixtures.Diamond.prepared unnumbered_diamond
    Fixtures.Diamond.fixture_ready Fixtures.Diamond.parents_wf = Some result ->
  Dom.exact Fixtures.Diamond.prepared (proj1_sig result).
Proof.
  intros _. exact (proj2_sig result).
Qed.

Definition malformed_line :=
  Map.set_code 2 3 1
    (Map.set_code 3 2 2 (Map.set positive_encoding 4 3 Map.empty)).

Example graph_check_does_not_validate_storage :
  DomCheck.check Fixtures.Line.prepared malformed_line = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example malformed_line_has_no_storage_certificate :
  ~ Map.wf positive_encoding malformed_line.
Proof.
  intro Hmap.
  assert (Hin : In (3, 1) (Map.elements malformed_line)).
  { vm_compute. tauto. }
  pose proof (proj1 (Map.elements_spec positive_encoding positive_encoding_laws
    3 1 malformed_line Hmap) Hin) as Hget.
  vm_compute in Hget. discriminate.
Qed.

Definition observations {V E} (p : Prepared.t V E) :=
  (DomBackend.parents DomBackend.lt p, DomBackend.parents DomBackend.semi_nca p).

Example line_backends :
  observations Fixtures.Line.prepared = (Fixtures.Line.parents, Fixtures.Line.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_backends :
  observations Fixtures.Diamond.prepared = (Fixtures.Diamond.parents, Fixtures.Diamond.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_backends :
  observations Fixtures.JoinLoop.prepared =
    (Fixtures.JoinLoop.parents, Fixtures.JoinLoop.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example multiple_entry_backends :
  observations Fixtures.TwoEntry.prepared =
    (Fixtures.TwoEntry.parents, Fixtures.TwoEntry.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_backends :
  observations Fixtures.Empty.prepared = (Map.empty, Map.empty).
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_backends :
  observations Fixtures.Singleton.prepared = (Map.empty, Map.empty).
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_backends :
  observations Fixtures.Unreachable.prepared =
    (Fixtures.Unreachable.parents, Fixtures.Unreachable.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_backends :
  observations Fixtures.Irreducible.prepared =
    (Fixtures.Irreducible.parents, Fixtures.Irreducible.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_loop_backends :
  observations Fixtures.NestedLoop.prepared =
    (Fixtures.NestedLoop.parents, Fixtures.NestedLoop.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example every_fixture_candidate_is_checked :
  forallb (fun p =>
    DomCheck.check p (DomBackend.parents DomBackend.lt p) &&
    DomCheck.check p (DomBackend.parents DomBackend.semi_nca p))
    [Fixtures.Line.prepared; Fixtures.Diamond.prepared; Fixtures.JoinLoop.prepared;
     Fixtures.NestedLoop.prepared; Fixtures.Irreducible.prepared; Fixtures.TwoEntry.prepared;
     Fixtures.Empty.prepared; Fixtures.Singleton.prepared; Fixtures.Unreachable.prepared] =
    true.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_parent_pipeline_ticks :
  (Cost.ticks (DomBackend.parents_c DomBackend.lt Fixtures.Line.prepared),
   Cost.ticks (DomBackend.parents_c DomBackend.semi_nca Fixtures.Line.prepared)) =
    (3106, 2799)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_parent_pipeline_ticks :
  (Cost.ticks (DomBackend.parents_c DomBackend.lt Fixtures.Diamond.prepared),
   Cost.ticks (DomBackend.parents_c DomBackend.semi_nca Fixtures.Diamond.prepared)) =
    (3398, 3073)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example numbered_backend_agreement :
  (DomBackend.compute DomBackend.lt Fixtures.Line.prepared,
   DomBackend.compute DomBackend.lt Fixtures.Diamond.prepared) =
  (DomBackend.compute DomBackend.semi_nca Fixtures.Line.prepared,
   DomBackend.compute DomBackend.semi_nca Fixtures.Diamond.prepared).
Proof.
  vm_compute. reflexivity.
Qed.

Example line_numbering :
  let t := DomBackend.compute DomBackend.lt Fixtures.Line.prepared in
  (map (fun v => Map.get positive_encoding v (Dom.tin t)) [1; 2; 3; 4],
   map (fun v => Map.get positive_encoding v (Dom.tout t)) [1; 2; 3; 4]) =
    ([Some 1; Some 2; Some 3; Some 4], [Some 4; Some 3; Some 2; Some 1]).
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_tree_queries_match_hand_written_certificates :
  forallb (fun p =>
    let produced := DomBackend.compute DomBackend.lt (fst p) in
    forallb (fun d => forallb (fun n =>
      Bool.eqb (DomCheck.dominates_b produced d n)
        (DomCheck.dominates_b (snd p) d n)) [1; 2; 3; 4; 5; 9])
      [1; 2; 3; 4; 5; 9])
    [(Fixtures.Line.prepared, Fixtures.Line.tree);
     (Fixtures.Diamond.prepared, Fixtures.Diamond.tree);
     (Fixtures.JoinLoop.prepared, Fixtures.JoinLoop.tree);
     (Fixtures.TwoEntry.prepared, Fixtures.TwoEntry.tree);
     (Fixtures.Empty.prepared, Fixtures.Empty.tree);
     (Fixtures.Singleton.prepared, Fixtures.Singleton.tree);
     (Fixtures.Unreachable.prepared, Fixtures.Unreachable.tree)] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_compute_ticks :
  (Cost.ticks (DomBackend.compute_c DomBackend.lt Fixtures.Line.prepared),
   Cost.ticks (DomBackend.compute_c DomBackend.semi_nca Fixtures.Line.prepared)) =
    (3857, 3550)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_compute_ticks :
  (Cost.ticks (DomBackend.compute_c DomBackend.lt Fixtures.Diamond.prepared),
   Cost.ticks (DomBackend.compute_c DomBackend.semi_nca Fixtures.Diamond.prepared)) =
    (4139, 3814)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition repeated_reachable_entry :=
  Fixtures.prepare [1; 3; 1; 3]%nat [1; 2; 3; 4]%nat
    [(1, 2); (1, 3); (2, 4); (3, 4)]%nat.

Example a_later_entry_still_has_no_parent :
  observations repeated_reachable_entry =
    (Fixtures.parents [(2, 1)], Fixtures.parents [(2, 1)]).
Proof.
  vm_compute. reflexivity.
Qed.

Definition weighted_graph :=
  let g := Prepared.graph Fixtures.Line.prepared in
  Graph.Make (Graph.entries g) (Graph.nodes g)
    (fun v => Cost.tick 7 ;; Graph.out_c g v)
    (fun e => Cost.tick 11 ;; Graph.source_c g e)
    (fun e => Cost.tick 13 ;; Graph.target_c g e).

Definition weighted_encoding :=
  Encoding (fun n : nat => Cost.tick 17 ;; encode_c nat_encoding n).

Definition weighted_prepared := Prepared.prepare weighted_encoding weighted_graph.

Example weighted_callbacks_keep_actual_parents :
  observations weighted_prepared = (Fixtures.Line.parents, Fixtures.Line.parents).
Proof.
  vm_compute. reflexivity.
Qed.

Example arbitrary_client_callback_work_is_retained :
  (N.ltb (Cost.ticks (DomBackend.compute_c DomBackend.lt Fixtures.Line.prepared))
     (Cost.ticks (DomBackend.compute_c DomBackend.lt weighted_prepared)),
   N.ltb (Cost.ticks (DomBackend.compute_c DomBackend.semi_nca Fixtures.Line.prepared))
     (Cost.ticks (DomBackend.compute_c DomBackend.semi_nca weighted_prepared))) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_forest_numbering_contract_client live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  forall d n, In d live -> In n live ->
  exists a b c e,
    Map.get positive_encoding d (Dom.tin (DomNumber.of_parents live parents)) = Some a /\
    Map.get positive_encoding n (Dom.tin (DomNumber.of_parents live parents)) = Some b /\
    Map.get positive_encoding n (Dom.tout (DomNumber.of_parents live parents)) = Some c /\
    Map.get positive_encoding d (Dom.tout (DomNumber.of_parents live parents)) = Some e /\
    ((a <= b /\ c <= e)%positive <-> idom_ancestor parents d n).
Proof.
  apply DomNumber.of_parents_numbering.
Qed.
