(** * Adequacy of full legacy slice execution

    Matching callbacks connect both counted DFS traversals to the original slice.
    For example, the reverse traversal begins at the actual load.
    Builds on: AnalysesAuditMemoryLegacySliceFull, slice and graph DFS adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditDfs
  GraphAuditDfsAdequacy.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacySlice
  AnalysesAuditMemoryLegacySliceAdequacy AnalysesAuditMemoryLegacySliceFull.
Import List.ListNotations.

(** * DFS callback agreement *)

(** The adapter returns the actual graph target and the supplied matching node code. *)
Lemma audit_legacy_dfs_callbacks_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (g : Graph.t N E) :
    (forall n, fst (node_enc n) = encode EN n) ->
    audit_dfs_callbacks_erase EN g (audit_legacy_dfs_callbacks node_enc g).
Proof.
  intro Hnode; split.
  - intro edge; reflexivity.
  - intro node; unfold audit_legacy_dfs_callbacks; cbn.
    specialize (Hnode node).
    destruct (node_enc node); exact Hnode.
Qed.

(** The two DFS traces and the node scan fit their stated source-work budgets. *)
Theorem audit_legacy_slice_full_trace_bound : audit_legacy_slice_full_trace_bound_statement.
Proof.
  intros N E T CN CT W EN ET node_enc site_enc g p writes read roots load node_work site_work
    writes_work Hnode.
  pose proof (audit_dfs_source_correct N E (list CN) EN g p
    (audit_legacy_dfs_callbacks node_enc g) node_work FinSet.empty roots
    (audit_legacy_dfs_callbacks_erases N E CN EN node_enc g Hnode)) as Hforward.
  pose proof (audit_dfs_source_correct N E (list CN) EN (reverse_graph p [load])
    (prepared_reverse p [load]) (audit_legacy_dfs_callbacks node_enc (reverse_graph p [load]))
    node_work FinSet.empty [load]
    (audit_legacy_dfs_callbacks_erases N E CN EN node_enc (reverse_graph p [load]) Hnode))
    as Hbackward.
  unfold audit_legacy_slice_full, audit_legacy_reached_counted.
  destruct (audit_dfs_source_counted p (audit_legacy_dfs_callbacks node_enc g) FinSet.empty roots)
    as [fresult fevents].
  destruct (audit_dfs_source_counted (prepared_reverse p [load])
    (audit_legacy_dfs_callbacks node_enc (reverse_graph p [load])) FinSet.empty [load])
    as [bresult bevents].
  cbn [fst snd] in Hforward, Hbackward.
  destruct Hforward as [Hfresult [_ [_ Hfwork]]].
  destruct Hbackward as [Hbresult [_ [_ Hbwork]]].
  pose proof (audit_legacy_slice_nodes_source_bound N T CN CT W node_enc site_enc writes node_work
    site_work writes_work read (visited fresult) (visited bresult) (Graph.nodes g)) as Hscan.
  destruct (audit_legacy_slice_nodes node_enc site_enc writes read (visited fresult)
    (visited bresult) (Graph.nodes g)) as [answer events]; cbn [snd] in Hscan |- *.
  unfold audit_legacy_slice_full_source_work; cbn [audit_legacy_slice_forward_dfs
    audit_legacy_slice_reverse_dfs audit_legacy_slice_node_checks].
  rewrite <- Hfresult, <- Hbresult; lia.
Qed.

(** The counted traversal returns the source DFS visited set. *)
Lemma audit_legacy_reached_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (g : Graph.t N E) (p : prepared EN g) roots :
    (forall n, fst (node_enc n) = encode EN n) ->
    fst (audit_legacy_reached_counted EN node_enc g p roots) =
      visited (dfs p FinSet.empty roots).
Proof.
  intro Hnode.
  pose proof (audit_dfs_source_result_and_count p (audit_legacy_dfs_callbacks node_enc g)
    FinSet.empty roots (audit_legacy_dfs_callbacks_erases N E CN EN node_enc g Hnode)) as [Hdfs _].
  unfold audit_legacy_reached_counted.
  destruct (audit_dfs_source_counted p (audit_legacy_dfs_callbacks node_enc g) FinSet.empty roots)
    as [result events]; cbn in *.
  rewrite Hdfs; reflexivity.
Qed.

(** Both counted walks feed the same visited sets into the original slice scan. *)
Theorem audit_legacy_slice_full_erases : audit_legacy_slice_full_erases_statement.
Proof.
  intros N E T CN CT W EN ET node_enc site_enc g p writes read roots load Hnode Hsite.
  unfold audit_legacy_slice_full, legacy_slice, legacy_reached.
  pose proof (audit_legacy_reached_erases N E CN EN node_enc g p roots Hnode) as Hforward.
  pose proof (audit_legacy_reached_erases N E CN EN node_enc (reverse_graph p [load])
    (prepared_reverse p [load]) [load] Hnode) as Hbackward.
  destruct (audit_legacy_reached_counted EN node_enc g p roots) as [forward fe].
  destruct (audit_legacy_reached_counted EN node_enc (reverse_graph p [load])
    (prepared_reverse p [load]) [load]) as [backward be]; cbn in *.
  pose proof (audit_legacy_slice_nodes_erases N T CN CT W EN ET node_enc site_enc writes read
    forward backward (Graph.nodes g) Hnode Hsite) as Hscan.
  destruct (audit_legacy_slice_nodes node_enc site_enc writes read forward backward (Graph.nodes g))
    as [answer events]; cbn in *.
  rewrite Hscan, Hforward, Hbackward; reflexivity.
Qed.
