(** * Input-derived discovery and edge inventories

    Exact search supplies one actual incoming edge for every discovered nonroot.
    For example, a single-root search discovers at most one more vertex than its graph has edges.
    Builds on: public search specifications and prepared virtual-root readiness. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchCost GraphDomVirtual GraphDomSemi GraphReach.
Import List.ListNotations.

Module DomSize.

(** Materialized edge occurrences have the same cardinality as the public graph edge inventory. *)
Theorem all_edges_length {V E} (g : Graph.t V E) :
  length (Prepared.all_edges g) = edge_count g.
Proof.
  unfold Prepared.all_edges, edge_count.
  induction (Graph.nodes g) as [|v rest IH]; cbn [flat_map fold_right];
    [reflexivity|now rewrite length_app, IH].
Qed.

Local Lemma parents_edge_bound {V E} (p : Prepared.t V E) scope roots (result : Search.result E) :
  Search.exact p scope roots result ->
  (Map.size (Search.parent_edge result) <= edge_count (Prepared.graph p))%nat.
Proof.
  intro Hsearch.
  set (targets := Prepared.present
    (fun e => Prepared.id_of p (Graph.target (Prepared.graph p) e))
    (Prepared.all_edges (Prepared.graph p))).
  eapply Nat.le_trans with (m := length targets).
  - apply (Map.size_support_bound positive_encoding positive_encoding_laws).
    + exact (proj1 (Search.result_wf _ _ _ _ Hsearch)).
    + intros v [e u] Hget.
      pose proof (proj1 (Search.parent_edge_valid _ _ _ _ Hsearch v e u Hget)) as Harc.
      destruct Harc as [a [b [Ha [Hu [Hv [Hsource [Htarget Hedge]]]]]]].
      unfold targets. apply Prepared.present_spec. exists e. split.
      * unfold Prepared.all_edges. apply in_flat_map. now exists a.
      * now rewrite Htarget.
  - eapply Nat.le_trans; [apply Prepared.present_length|].
    rewrite all_edges_length. reflexivity.
Qed.

(** Exact search is bounded by supplied roots plus actual edge occurrences. *)
Theorem preorder_edges {V E} (p : Prepared.t V E) scope roots (result : Search.result E) :
  Search.exact p scope roots result ->
  (length (Search.preorder result) <= length roots + edge_count (Prepared.graph p))%nat.
Proof.
  intro Hsearch.
  eapply Nat.le_trans with
    (m := length (roots ++ map fst (Map.elements (Search.parent_edge result)))).
  - apply NoDup_incl_length; [exact (Search.pre_nodup _ _ _ _ Hsearch)|].
    intros v Hv. apply in_or_app.
    destruct (Map.get positive_encoding v (Search.parent_edge result)) as [[e u]|] eqn:Hget.
    + right. apply in_map_iff. exists (v, (e, u)). split; [reflexivity|].
      apply (Map.elements_spec positive_encoding positive_encoding_laws);
        [exact (proj1 (Search.result_wf _ _ _ _ Hsearch))|exact Hget].
    + left. exact (Search.parent_roots _ _ _ _ Hsearch v Hv Hget).
  - rewrite length_app, length_map, <- Map.size_elements.
    pose proof (parents_edge_bound p scope roots result Hsearch). lia.
Qed.

(** The prepared virtual graph has its successfully converted fresh root as its only entry. *)
Theorem virtual_entries {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Prepared.entry_ids (DomVirtual.virtual p) =
    [Pos.of_succ_nat (length (Graph.nodes (Prepared.graph p)))].
Proof.
  intro Hready.
  pose proof (DomVirtual.virtual_ready p Hready) as Hvirtual.
  rewrite (Prepared.entries_agree _ (proj2 (proj2 Hvirtual))).
  unfold Prepared.ids.
  rewrite DomVirtual.prepared_graph, DomVirtual.graph_equation.
  cbn [Graph.entries Prepared.present].
  change (match Prepared.id_of (DomVirtual.virtual p) None with
    | Some i => [i]
    | None => []
    end = [Pos.of_succ_nat (length (Graph.nodes (Prepared.graph p)))]).
  rewrite DomVirtual.root_id by exact Hready. reflexivity.
Qed.

(** Single-root actual discovery is bounded by the actual virtual edge inventory. *)
Theorem actual_preorder_edges {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  (length (Search.preorder (DomSemi.search (DomSemi.compute p))) <=
    1 + edge_count (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)))%nat.
Proof.
  intro Hready.
  pose proof (preorder_edges (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted
    (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p))) (DomSemi.search (DomSemi.compute p))
    (DomSemi.search_exact p Hready)) as Hsize.
  rewrite DomSemi.prepared_equation, virtual_entries in Hsize by exact Hready.
  rewrite DomVirtual.prepared_graph in Hsize. exact Hsize.
Qed.

(** Actual discovery is also bounded by the original listed nodes and the single fresh root. *)
Theorem actual_preorder_nodes {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  (length (Search.preorder (DomSemi.search (DomSemi.compute p))) <=
    length (Graph.nodes (Prepared.graph p)) + 1)%nat.
Proof.
  intro Hready. rewrite DomSemi.search_equation.
  change (length (Search.preorder
    (SearchRun.dfs (DomVirtual.virtual p) Reach.unrestricted
      (Prepared.entry_ids (DomVirtual.virtual p)))) <=
    length (Graph.nodes (Prepared.graph p)) + 1)%nat.
  eapply Nat.le_trans; [apply SearchCost.preorder_length; now apply DomVirtual.virtual_ready|].
  rewrite DomVirtual.prepared_graph, DomVirtual.graph_equation.
  cbn [Graph.nodes]. rewrite length_app, length_map. cbn [length]. lia.
Qed.

End DomSize.
