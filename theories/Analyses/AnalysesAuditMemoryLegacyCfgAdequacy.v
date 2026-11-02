(** * Adequacy of legacy adjacency construction

    The observer preserves the original target order and distinctness when building indexed rows.
    For example, repeated targets are indexed only at their first occurrence.
    Builds on: AnalysesAuditMemoryLegacyCfg and memory index adequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesMemoryFrontier
  AnalysesAuditMemoryLegacyCfg AnalysesAuditMemoryDistinct AnalysesAuditMemoryIndex
  AnalysesAuditMemoryDistinctAdequacy
  AnalysesAuditMemoryIndexAdequacy.

(** * Row and graph agreement *)

(** The observer preserves the order of returned target nodes. *)
Lemma audit_legacy_cfg_targets_erases N E CN OE TE (target : E -> N * list TE) node edges :
    fst (@audit_legacy_cfg_targets N E CN OE TE target node edges) =
      map (fun edge => fst (target edge)) edges.
Proof.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_legacy_cfg_targets map].
    destruct (target edge) as [result calls].
    destruct (audit_legacy_cfg_targets target node rest) as [tail events]; cbn in *.
    rewrite IH; reflexivity.
Qed.

(** Pair construction preserves every target occurrence in order. *)
Lemma audit_legacy_cfg_pairs_erases N E CN OE TE node targets :
    fst (@audit_legacy_cfg_pairs N E CN OE TE node targets) =
      map (fun target => (node, target)) targets.
Proof.
  induction targets as [|target rest IH].
  - reflexivity.
  - cbn [audit_legacy_cfg_pairs map].
    destruct (audit_legacy_cfg_pairs node rest) as [tail events]; cbn in *.
    rewrite IH; reflexivity.
Qed.

(** A counted row agrees with the original adjacency row under callback agreement. *)
Lemma audit_legacy_cfg_row_erases N E CN OE TE (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) (g : Graph.t N E) node :
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    fst (audit_legacy_cfg_row EN node_enc out target node) =
      map (fun target => (node, target))
        (memory_distinct EN (map (Graph.target g) (Graph.out g node))).
Proof.
  intros Hnode Hout Htarget.
  unfold audit_legacy_cfg_row.
  pose proof (audit_legacy_cfg_targets_erases N E CN OE TE target node (fst (out node)))
    as Htargets.
  destruct (out node) as [edges out_calls] eqn:Hout_call; cbn in *.
  destruct (audit_legacy_cfg_targets target node edges) as [targets target_events]; cbn in *.
  pose proof (audit_memory_distinct_erases N CN node_enc EN targets
    (fun n _ => Hnode n)) as Hdistinct.
  destruct (audit_memory_distinct node_enc targets) as [distinct distinct_events]; cbn in *.
  pose proof (audit_legacy_cfg_pairs_erases N E CN OE TE node distinct) as Hpairs.
  destruct (audit_legacy_cfg_pairs node distinct) as [pairs pair_events]; cbn in *.
  specialize (Hout node); rewrite Hout_call in Hout; cbn in Hout.
  rewrite Hpairs, Hdistinct, Htargets, Hout.
  f_equal; f_equal; apply map_ext; exact Htarget.
Qed.

(** Matching callbacks recover the complete indexed legacy graph. *)
Theorem audit_legacy_cfg_erases : audit_legacy_cfg_erases_statement.
Proof.
  intros N E CN OE TE EN node_enc out target g Hnode Hout Htarget.
  pose proof (audit_memory_result_index_erases N (list (N * N)) CN
    (audit_legacy_cfg_event N E CN OE TE) node_enc EN (audit_legacy_cfg_row EN node_enc out target)
    (fun node => map (fun target => (node, target))
      (memory_distinct EN (map (Graph.target g) (Graph.out g node)))) (Graph.nodes g)
    (fun n _ => Hnode n)
    (fun n _ => audit_legacy_cfg_row_erases N E CN OE TE EN node_enc out target g n
      Hnode Hout Htarget)) as Hrows.
  unfold audit_legacy_cfg_counted, audit_legacy_cfg_rows, legacy_cfg, legacy_cfg_rows.
  destruct (audit_memory_result_index node_enc (audit_legacy_cfg_row EN node_enc out target)
    (Graph.nodes g)) as [rows events]; cbn in *.
  rewrite Hrows; reflexivity.
Qed.

(** Result-index work bounds the graph construction's recorded work. *)
Theorem audit_legacy_cfg_source_bound : audit_legacy_cfg_source_bound_statement.
Proof.
  intros N E CN OE TE EN node_enc out target g node_work out_work target_work.
  unfold audit_legacy_cfg_source_work, audit_legacy_cfg_counted, audit_legacy_cfg_rows.
  pose proof (audit_memory_result_index_work_bound N (list (N * N)) CN
    (audit_legacy_cfg_event N E CN OE TE) node_enc (audit_legacy_cfg_row EN node_enc out target)
    node_work (audit_legacy_cfg_row_work node_work out_work target_work) (Graph.nodes g)) as Hbound.
  destruct (audit_memory_result_index node_enc (audit_legacy_cfg_row EN node_enc out target)
    (Graph.nodes g)); exact Hbound.
Qed.
