(** * Shared ranked-prologue observations

    Hand-written fixtures check discovery-rank transport and reverse settlement.
    For example, a diamond's two incoming join occurrences retain their separate labels.
    Builds on: GraphDomSemi and GraphFixtures. *)

From Stdlib Require Import List PArith NArith.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphDomSemi
  GraphDomRank GraphSearchSpec GraphReach GraphDomTransport GraphDomErase GraphDomLt GraphDomNca
  GraphDomLink GraphDomLinkProof GraphDomPath GraphDomDfs GraphDomDfsPath GraphDomSemiEval
  GraphDomSemiExact GraphDomCut GraphDomCutPath GraphDomCutTransport GraphDomNcaProof
  GraphDomSpec.
Import List.ListNotations Cost.Notations.
Open Scope positive_scope.

Definition line_shared := DomSemi.compute Fixtures.Line.prepared.
Definition diamond_shared := DomSemi.compute Fixtures.Diamond.prepared.

Example line_semidominators :
  DomSemi.semis (DomSemi.settled line_shared) =
    Map.of_list positive_encoding [(2, 1); (3, 2); (4, 3); (5, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_semidominators :
  DomSemi.semis (DomSemi.settled diamond_shared) =
    Map.of_list positive_encoding [(2, 1); (3, 2); (4, 2); (5, 2)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_labels_and_ranked_sources :
  Index.find positive_encoding 4 (DomSemi.predecessors (DomSemi.ranked diamond_shared)) =
    [(inl (2, 4)%nat, 3); (inl (3, 4)%nat, 5)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_inverse_order :
  Map.elements (DomSemi.real_ids (DomSemi.ranked diamond_shared)) =
    [(4, 4); (2, 1); (5, 3); (3, 2)].
Proof.
  vm_compute. reflexivity.
Qed.

Example ranks_compare_numerically :
  (Cost.value (DomRank.compare_c 2 3), Cost.value (DomRank.compare_c 4 3)) = (Lt, Gt).
Proof.
  vm_compute. reflexivity.
Qed.

Definition unreachable_predecessor :=
  Fixtures.prepare [1]%nat [1; 2; 3]%nat [(1, 2); (3, 2)]%nat.

Example unreachable_incoming_source_has_no_rank :
  let shared := DomSemi.compute unreachable_predecessor in
  Index.find positive_encoding 3 (DomSemi.predecessors (DomSemi.ranked shared)) =
    [(inl (1, 2)%nat, 2)].
Proof.
  vm_compute. reflexivity.
Qed.

Example exact_search_client {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Search.exact (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted
    (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p)))
    (DomSemi.search (DomSemi.compute p)).
Proof.
  apply DomSemi.search_exact.
Qed.

Example missing_rank_contract_client {V E} (p : Prepared.t V E) n u :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some u ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = None ->
  ~ reachable (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) n.
Proof.
  apply DomSemi.missing_rank_unreachable.
Qed.

Example canonical_inverse_contract_client {V E} (p : Prepared.t V E) :
  Map.wf positive_encoding (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))).
Proof.
  apply DomTransport.inverse_wf.
Qed.

Example injective_inverse_contract_client {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  DomErase.injective
    (fun rank => Map.get positive_encoding rank
      (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p)))).
Proof.
  apply DomTransport.inverse_injective.
Qed.

Example complete_inverse_contract_client {V E} (p : Prepared.t V E) v rank original :
  Prepared.ready p -> In v (Search.preorder (DomSemi.search (DomSemi.compute p))) ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank ->
  DomErase.real_id p (DomSemi.prepared (DomSemi.compute p)) v = Some original ->
  Map.get positive_encoding rank (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) =
    Some original.
Proof.
  apply DomTransport.inverse_complete.
Qed.

Example canonical_intermediate_maps_client {V E} (p : Prepared.t V E) :
  Map.wf positive_encoding (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) /\
    Map.wf positive_encoding (DomLt.finish (DomSemi.compute p)) /\
    Map.wf positive_encoding (DomNca.finish (DomSemi.compute p)).
Proof.
  split; [apply DomSemi.semidominators_wf|].
  split; [apply DomLt.finish_wf|apply DomNca.finish_wf].
Qed.

Definition linked :=
  Cost.value (DomLink.link_c (Cost.value (DomLink.link_c DomLink.empty 3 2)) 2 1).

Definition scored (rank : positive) := Cost.tick 7 ;; Cost.ret rank.

Example actual_linked_state_valid :
  DomLinkProof.valid (fun x => Cost.value (scored x)) linked.
Proof.
  apply DomLinkProof.link_valid.
  - apply DomLinkProof.link_valid.
    + apply DomLinkProof.empty_valid.
    + vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Example actual_original_links_decrease :
  forall v a, Map.get positive_encoding v (DomLink.original linked) = Some a -> (a < v)%positive.
Proof.
  intros v a Hget.
  apply (Map.elements_spec positive_encoding positive_encoding_laws v a _
    (DomLinkProof.original_wf _ _ actual_linked_state_valid)) in Hget.
  vm_compute in Hget.
  destruct Hget as [Heq|[Heq|Hfalse]]; [| |contradiction];
    injection Heq as <- <-; vm_compute; reflexivity.
Qed.

Example actual_compression_contract :
  DomLinkProof.query_valid (fun x => Cost.value (scored x)) linked 3
    (Cost.value (DomLink.compress_c scored linked 3)).
Proof.
  apply DomLinkProof.compress_correct.
  - exact actual_linked_state_valid.
  - exact actual_original_links_decrease.
Qed.

Example compression_excludes_the_root_score :
  snd (Cost.value (DomLink.compress_c scored linked 3)) = (1, Some 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example compression_really_updates_the_shortcut :
  Map.get positive_encoding 3
    (DomLink.shortcut (fst (Cost.value (DomLink.compress_c scored linked 3)))) = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example compression_retains_nonunit_score_calls :
  Cost.ticks (DomLink.compress_c scored linked 3) =
    (Cost.ticks (DomLink.compress_c (fun rank => Cost.ret rank) linked 3) + 14)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example ranked_arc_contract_client {V E} (p : Prepared.t V E) target rank e source_rank :
  Prepared.ready p ->
  Map.get positive_encoding target
    (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  (DomSemi.ranked_arc (DomSemi.compute p) source_rank e rank <->
    exists source, Prepared.arc (DomSemi.prepared (DomSemi.compute p)) source e target /\
      Map.get positive_encoding source
        (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some source_rank).
Proof.
  apply DomTransport.ranked_arc_spec.
Qed.

Example labelled_path_lift_client {V E} (p : Prepared.t V E) u es v source_rank target_rank :
  Prepared.ready p ->
  Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted u es v ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some source_rank ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some target_rank ->
  DomPath.path (DomSemi.compute p) source_rank es target_rank.
Proof.
  apply DomPath.lift.
Qed.

Example labelled_path_lower_client {V E} (p : Prepared.t V E) source_rank es target_rank :
  Prepared.ready p -> DomPath.path (DomSemi.compute p) source_rank es target_rank ->
  forall u v,
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some source_rank ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some target_rank ->
  Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted u es v.
Proof.
  apply DomPath.lower.
Qed.

Example root_reflexive_ranked_path : DomPath.path line_shared 1 [] 1.
Proof.
  constructor. exists 5. vm_compute. reflexivity.
Qed.

Example unknown_rank_is_not_a_vertex : ~ DomPath.vertex line_shared 9.
Proof.
  intros [v Hget].
  pose proof (DomSemi.search_exact Fixtures.Line.prepared Fixtures.Line.fixture_ready)
    as Hsearch.
  pose proof (proj1 (proj2 (Search.result_wf _ _ _ _ Hsearch))) as Hmap.
  apply (Map.elements_spec positive_encoding positive_encoding_laws v 9 _ Hmap) in Hget.
  vm_compute in Hget. intuition discriminate.
Qed.

Example dfs_parent_contract_client {V E} (p : Prepared.t V E) n parent :
  Prepared.ready p ->
  Map.get positive_encoding n (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent -> (parent < n)%positive.
Proof.
  apply DomDfs.parent_decreases.
Qed.

Example actual_reverse_order_is_strict {V E} (p : Prepared.t V E) u v :
  Prepared.ready p ->
  before (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) u v -> (v < u)%positive.
Proof.
  apply DomDfs.settlement_decreases.
Qed.

Example semidominator_producer_contract_client {V E} (p : Prepared.t V E) n u :
  Prepared.ready p ->
  (Map.get positive_encoding n (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) = Some u <->
    DomPath.vertex (DomSemi.compute p) n /\ n <> 1 /\ DomSemiExact.semidominator p u n).
Proof.
  apply DomSemiExact.semidominators_exact.
Qed.

Example actual_line_semidominator_is_minimal :
  DomSemiExact.semidominator Fixtures.Line.prepared 3 4.
Proof.
  apply (proj2 (proj2 (proj1 (DomSemiExact.semidominators_exact
    Fixtures.Line.prepared 4 3 Fixtures.Line.fixture_ready) ltac:(vm_compute; reflexivity)))).
Qed.

Example actual_diamond_join_semidominator_is_minimal :
  DomSemiExact.semidominator Fixtures.Diamond.prepared 2 4.
Proof.
  apply (proj2 (proj2 (proj1 (DomSemiExact.semidominators_exact
    Fixtures.Diamond.prepared 4 2 Fixtures.Diamond.fixture_ready) ltac:(vm_compute; reflexivity)))).
Qed.

Example diamond_arm_does_not_minimize_join_candidates :
  ~ DomSemiExact.semidominator Fixtures.Diamond.prepared 3 4.
Proof.
  intro Hsemi.
  pose proof (DomSemiExact.semidominator_unique Fixtures.Diamond.prepared 2 3 4
    actual_diamond_join_semidominator_is_minimal Hsemi) as Hfalse.
  discriminate.
Qed.

Example actual_virtual_root_has_no_settled_entry {V E} (p : Prepared.t V E) u :
  Prepared.ready p ->
  Map.get positive_encoding 1 (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) <> Some u.
Proof.
  intros Hready Hget.
  apply (proj1 (DomSemiExact.semidominators_exact p 1 u Hready)) in Hget.
  exact (proj1 (proj2 Hget) eq_refl).
Qed.

Example label_preserving_semidominator_path_client {V E} (p : Prepared.t V E)
    raw_source raw_target source target :
  Prepared.ready p ->
  Map.get positive_encoding raw_source (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some source ->
  Map.get positive_encoding raw_target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some target ->
  DomSemiExact.semidom_path p source target ->
  exists es, es <> [] /\
    Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted
      raw_source es raw_target.
Proof.
  apply DomSemiExact.candidate_original_path.
Qed.

Example semidominator_value_contract_client {V E} (p : Prepared.t V E) n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n -> n <> 1 ->
  DomSemiExact.semidominator p (DomCut.score p n) n /\
    (DomCut.score p n < n)%positive /\ DomDfs.ancestor p (DomCut.score p n) n.
Proof.
  apply DomCut.score_exact.
Qed.

Example nca_parent_domain_contract_client {V E} (p : Prepared.t V E) n :
  Prepared.ready p ->
  ((exists a, Map.get positive_encoding n (DomNca.finish (DomSemi.compute p)) = Some a) <->
    DomPath.vertex (DomSemi.compute p) n /\ n <> 1).
Proof.
  apply DomNcaProof.finish_domain.
Qed.

Example nca_well_founded_contract_client {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  well_founded (fun a n => Map.get positive_encoding n
    (DomNca.finish (DomSemi.compute p)) = Some a).
Proof.
  apply DomNcaProof.finish_well_founded.
Qed.

Example nca_actual_cut_contract_client {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n ->
  (idom_ancestor (DomNca.finish (DomSemi.compute p)) d n <-> DomCut.cut p d n).
Proof.
  apply DomNcaProof.finish_cuts.
Qed.

Example cut_avoiding_path_contract_client {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n ->
  (DomCut.cut p d n <-> DomCutPath.no_avoiding p d n).
Proof.
  apply DomCutPath.cut_exact.
Qed.

Example nca_semantic_immediate_contract_client {V E} (p : Prepared.t V E)
    d n deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) d = Some deleted ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some target ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  (Map.get positive_encoding rank_target (DomNca.finish (DomSemi.compute p)) = Some rank_deleted <->
    immediately_dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n).
Proof.
  apply DomNcaProof.finish_immediate.
Qed.

Example diamond_branch_is_a_closed_join_cut :
  DomCut.cut Fixtures.Diamond.prepared 2 4.
Proof.
  apply (proj1 (DomNcaProof.finish_cuts Fixtures.Diamond.prepared 2 4
    Fixtures.Diamond.fixture_ready ltac:(exists 4; vm_compute; reflexivity))).
  apply rt_step. vm_compute. reflexivity.
Qed.

Example diamond_arm_is_not_a_closed_join_cut :
  ~ DomCut.cut Fixtures.Diamond.prepared 3 4.
Proof.
  intro Hcut.
  pose proof (DomCut.cut_bound Fixtures.Diamond.prepared 3 4
    Fixtures.Diamond.fixture_ready Hcut ltac:(discriminate)) as Hbound.
  vm_compute in Hbound. exact (Hbound eq_refl).
Qed.

Example actual_diamond_nca_join_parent_is_semantically_immediate :
  immediately_dominates (Prepared.graph (DomSemi.prepared diamond_shared))
    (Some 1%nat) (Some 4%nat).
Proof.
  apply (proj1 (DomNcaProof.finish_immediate Fixtures.Diamond.prepared
    (Some 1%nat) (Some 4%nat) 1 4 2 4 Fixtures.Diamond.fixture_ready
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))).
  vm_compute. reflexivity.
Qed.
