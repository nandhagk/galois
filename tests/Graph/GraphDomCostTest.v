(** * Primitive checker-bound clients

    Resource witnesses instantiate the coarse bound without an assumed checker result.
    For example, the line's raw candidate storage is counted independently of graph node count.
    Builds on: GraphDomCost, GraphDomCheckBound and GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFixtures
  GraphDomCost GraphDomCheckBound GraphCheckDom GraphCheckDomCost GraphFrontierSweep GraphDomNca
  GraphDomNcaCost GraphDomSemi GraphDomFastCheck GraphDomAncestorIndex GraphDomFiniteView
  GraphDomFiniteSearch GraphDomFiniteReach GraphDomFiniteTransport GraphReach.
Import List.ListNotations.
Open Scope positive_scope.

Local Lemma line_ids i :
  Prepared.valid_id Fixtures.Line.prepared i -> i = 1 \/ i = 2 \/ i = 3 \/ i = 4.
Proof.
  intros [v [Hnodes Hid]]. vm_compute in Hnodes.
  destruct Hnodes as [Hv|[Hv|[Hv|[Hv|Hfalse]]]]; [| | | |contradiction];
    subst v; vm_compute in Hid; injection Hid as <-; auto.
Qed.

(** Reduce a valid fixture ID to its finite cases and close the resulting literal cost bounds. *)
Local Ltac finite_id :=
  intros i Hi;
  destruct (line_ids i Hi) as [Hcase|[Hcase|[Hcase|Hcase]]];
  subst i;
  vm_compute; try lia; intuition discriminate.

Example line_resources :
  FrontierSweep.resources Fixtures.Line.prepared
    (Dom.Tree Fixtures.Line.parents Map.empty Map.empty)
    4 1 1 3 3%N 5%N 5%N 6%N 4%N.
Proof.
  constructor.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. intuition discriminate.
  - finite_id.
  - intros v Hv. vm_compute in Hv.
    destruct Hv as [Hv|[Hv|[Hv|[Hv|Hfalse]]]]; [| | | |contradiction];
      subst v; vm_compute; intuition discriminate.
  - finite_id.
  - finite_id.
  - finite_id.
  - finite_id.
  - finite_id.
Qed.

Example line_parent_width : DomCheckCost.parent_width Fixtures.Line.parents 3%N.
Proof.
  intros v u Hget.
  apply (Map.elements_spec positive_encoding positive_encoding_laws v u _
    Fixtures.Line.parents_wf) in Hget.
  vm_compute in Hget.
  destruct Hget as [Heq|[Heq|[Heq|Hfalse]]]; [| | |contradiction];
    injection Heq as <- <-; vm_compute; intuition discriminate.
Qed.

Example line_stored_width : DomCheckBound.stored_width Fixtures.Line.parents 3%N.
Proof.
  intros vu Hin. vm_compute in Hin.
  destruct Hin as [Heq|[Heq|[Heq|Hfalse]]]; [| | |contradiction];
    subst vu; vm_compute; intuition discriminate.
Qed.

Example actual_line_closed_bound :
  (Cost.ticks (DomCost.check_c Fixtures.Line.prepared Fixtures.Line.parents) <=
    DomCheckBound.checker_bound 4 1 1 3 3%N 5%N 5%N 6%N 4%N)%N.
Proof.
  apply DomCost.check_cost.
  - exact Fixtures.Line.fixture_ready.
  - exact line_resources.
  - exact line_parent_width.
  - exact line_stored_width.
Qed.

Example empty_bound_has_nonzero_driver_overhead :
  N.ltb 0 (DomCheckBound.checker_bound 0 0 0 0 1%N 1%N 3%N 4%N 0%N) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_cost_contract_client {V E} (p : Prepared.t V E) candidate n m l b w a q h s :
  Prepared.ready p ->
  FrontierSweep.resources p (Dom.Tree candidate Map.empty Map.empty) n m l b w a q h s ->
  DomCheckCost.parent_width candidate w -> DomCheckBound.stored_width candidate w ->
  (Cost.ticks (DomCost.check_c p candidate) <=
    DomCheckBound.checker_bound n m l b w a q h s)%N.
Proof.
  apply DomCost.check_cost.
Qed.

Example actual_line_nca_finish_bound :
  (Cost.ticks (DomNca.finish_c (DomSemi.compute Fixtures.Line.prepared)) <=
    16 * DomNcaCost.actual_work Fixtures.Line.prepared)%N.
Proof.
  apply DomNcaCost.actual_finish_numeric_cost. exact Fixtures.Line.fixture_ready.
Qed.

Example actual_two_entry_nca_finish_bound :
  (Cost.ticks (DomNca.finish_c (DomSemi.compute Fixtures.TwoEntry.prepared)) <=
    16 * DomNcaCost.actual_work Fixtures.TwoEntry.prepared)%N.
Proof.
  apply DomNcaCost.actual_finish_numeric_cost. exact Fixtures.TwoEntry.fixture_ready.
Qed.

Example empty_graph_still_has_a_virtual_rank :
  N.ltb 0 (DomNcaCost.actual_work Fixtures.Empty.prepared) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example arbitrary_cyclic_walk_is_bounded :
  let cyclic := Map.of_list positive_encoding [(2, 3); (3, 2)] in
  (Cost.ticks (DomNca.walk_c 1 cyclic 3) <=
    3 * (DomNcaCost.walk_k * (1 + DomNcaCost.width 3)))%N.
Proof.
  apply DomNcaCost.walk_cost.
Qed.

Example normalized_line_is_ready :
  Prepared.ready (DomFiniteView.prepared Fixtures.Line.prepared [1]).
Proof.
  apply DomFiniteView.prepared_ready.
Qed.

Definition corrupt_adjacency :=
  let p := Fixtures.Line.prepared in
  Prepared.Make (Prepared.graph p) (Prepared.node_enc p) (Prepared.names p)
    (Map.of_list positive_encoding
      [(1, [((90, 91)%nat, 2); ((90, 91)%nat, 99)]);
       (2, [((92, 93)%nat, 4)])])
    Map.empty [1; 1; 99] 1.

Example malformed_original_still_normalizes_to_ready :
  Prepared.ready (DomFiniteView.prepared corrupt_adjacency (Prepared.entry_ids corrupt_adjacency)).
Proof.
  apply DomFiniteView.prepared_ready.
Qed.

Example normalized_raw_adjacency_and_fuel_control :
  let q := DomFiniteView.prepared corrupt_adjacency (Prepared.entry_ids corrupt_adjacency) in
  FinSet.elements (Cost.value (DomFiniteReach.reach_c q Reach.unrestricted)) = [4; 2; 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example normalized_raw_scope_translation_control :
  let q := DomFiniteView.prepared corrupt_adjacency (Prepared.entry_ids corrupt_adjacency) in
  FinSet.elements (Cost.value (DomFiniteReach.reach_c q (Reach.blocked 2))) = [1].
Proof.
  vm_compute. reflexivity.
Qed.

Definition raw_cache_corruption :=
  Map.set_code 2 3 1
    (Map.set_code 3 2 2 (Map.set positive_encoding 4 3 Map.empty)).

Example cached_ancestry_retains_malformed_storage_and_cycles :
  forallb (fun parents =>
    let index := DomAncestorIndex.build parents [1; 2; 3; 4] in
    forallb (fun d => forallb (fun n =>
      Bool.eqb (Cost.value (DomAncestorIndex.contains_c index d n))
        (DomCheck.ancestor_b parents d n)) [1; 2; 3; 4]) [1; 2; 3; 4; 99])
    [Fixtures.Line.parents; raw_cache_corruption;
     Map.of_list positive_encoding [(2, 3); (3, 2)]] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example fast_checker_raw_domain_controls :
  let parents := Map.of_list positive_encoding [(2, 1); (4, 2)] in
  (Cost.value (DomFastCheck.check_c corrupt_adjacency parents),
   DomCheck.check corrupt_adjacency parents) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example fast_checker_accepts_fixture_candidates :
  forallb (fun pair => Cost.value (DomFastCheck.check_c (fst pair) (snd pair)))
    [(Fixtures.Line.prepared, Fixtures.Line.parents);
     (Fixtures.Diamond.prepared, Fixtures.Diamond.parents);
     (Fixtures.JoinLoop.prepared, Fixtures.JoinLoop.parents);
     (Fixtures.TwoEntry.prepared, Fixtures.TwoEntry.parents);
     (Fixtures.Empty.prepared, Fixtures.Empty.parents);
     (Fixtures.Singleton.prepared, Fixtures.Singleton.parents);
     (Fixtures.Unreachable.prepared, Fixtures.Unreachable.parents)] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example fast_checker_rejects_bad_domains_and_cycles :
  (Cost.value (DomFastCheck.check_c Fixtures.Line.prepared
     (Map.of_list positive_encoding [(99, 1)])),
   Cost.value (DomFastCheck.check_c Fixtures.Line.prepared
     (Map.of_list positive_encoding [(2, 3); (3, 2)]))) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example early_domain_cardinality_client :
  (Map.size Fixtures.Line.parents <=
    length (FinSet.elements
      (Reach.set Fixtures.Line.prepared Reach.unrestricted [1%positive])))%nat.
Proof.
  apply DomFastCheck.domains_cardinality.
  - apply Reach.set_wf.
  - exact Fixtures.Line.parents_wf.
  - vm_compute. reflexivity.
Qed.

Example unconditional_fast_checker_client {V E} (p : Prepared.t V E) parents :
  Cost.value (DomFastCheck.check_c p parents) = DomCheck.check p parents.
Proof.
  apply DomFastCheck.check_c_value.
Qed.

Example malformed_view_transport_client scope v :
  let q := DomFiniteView.prepared corrupt_adjacency (Prepared.entry_ids corrupt_adjacency) in
  Cost.value (DomFiniteSearch.member_c q (DomFiniteSearch.run q scope) v) =
    FinSet.mem positive_encoding v
      (Reach.set corrupt_adjacency scope (Prepared.entry_ids corrupt_adjacency)).
Proof.
  apply DomFiniteTransport.member_value.
Qed.

Example indexed_line_construction_bound :
  let nodes := [1; 2; 3; 4] in
  (Cost.ticks (DomAncestorIndex.build_c Fixtures.Line.parents nodes) <=
    TrieCost.trie_k * (1 + MapCost.skeleton_nodes Fixtures.Line.parents) +
    N.of_nat (length nodes) *
      (2 + DomCheckCost.id_get_budget 3 +
        N.of_nat (S (Map.size Fixtures.Line.parents)) *
          (5 + DomCheckCost.id_get_budget 3 + 3)))%N.
Proof.
  cbn zeta. apply DomAncestorIndex.build_cost.
  - exact line_parent_width.
  - intros n [<-|[<-|[<-|[<-|Hfalse]]]]; [| | | |contradiction];
      vm_compute; intuition discriminate.
Qed.

Example fast_checker_keeps_raw_storage_semantics :
  (Cost.value (DomFastCheck.check_c Fixtures.Line.prepared raw_cache_corruption),
    DomCheck.check Fixtures.Line.prepared raw_cache_corruption) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.
