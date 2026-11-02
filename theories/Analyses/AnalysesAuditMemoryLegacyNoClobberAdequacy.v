(** * Adequacy of the complete legacy checker

    The recorded setup and node checks recover the original no-clobber Boolean.
    For example, duplicate graph nodes retain the original indexed row.
    Builds on: legacy CFG, successor, full slice and checker adequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase
  GraphAuditBaseAdequacy GraphAuditDfs GraphAuditDfsAdequacy.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacyCfg
  AnalysesAuditMemoryLegacyCfgAdequacy AnalysesAuditMemoryLegacyChecker
  AnalysesAuditMemoryLegacyCheckerAdequacy
  AnalysesAuditMemoryLegacySuccessor AnalysesAuditMemoryLegacySuccessorAdequacy
  AnalysesAuditMemoryLegacySliceFull AnalysesAuditMemoryLegacySliceFullAdequacy
  AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryWalkIndex
  AnalysesAuditMemoryWalkIndexAdequacy AnalysesAuditMemoryLegacyNoClobber.
Import List.ListNotations.

(** * Preparation and checker agreement *)

(** Normalized graph callbacks return the actual indexed row and pair target. *)
Lemma audit_legacy_prepare_callbacks_erases N CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (rows : Map.t N (list (N * N))) entries nodes :
    (forall n, fst (node_enc n) = encode EN n) ->
    audit_prepare_callbacks_erase EN (Graph.Make entries nodes (index_edges EN rows) fst snd)
      (audit_legacy_prepare_callbacks node_enc rows).
Proof.
  intro Hnode; unfold audit_legacy_prepare_callbacks.
  apply audit_walk_callbacks_erases.
  - exact Hnode.
  - intro n; apply audit_walk_predecessors_erases; apply Hnode.
  - intro edge; reflexivity.
Qed.

(** Matching graph and client callbacks recover the original no-clobber decision. *)
Theorem audit_legacy_no_clobber_erases : audit_legacy_no_clobber_erases_statement.
Proof.
  intros F N E T CN CF CT OE TE CR CW CD EN EF ET node_enc function_enc site_enc out target
    reads writes f g ms definitions Hnode Hfunction Hsite Hout Htarget Hdefinitions.
  pose proof (audit_legacy_cfg_erases N E CN OE TE EN node_enc out target g Hnode Hout Htarget)
    as Hcfg.
  unfold audit_legacy_no_clobber_counted, no_clobber_check.
  destruct (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) as [rows cfg_events]
    eqn:Hrows.
  unfold audit_legacy_cfg_counted in Hcfg; rewrite Hrows in Hcfg; cbn in Hcfg.
  set (cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd) in *.
  pose proof (audit_legacy_prepare_callbacks_erases N CN EN node_enc rows (Graph.entries g)
    (Graph.nodes g) Hnode) as Hcallbacks.
  change (audit_prepare_callbacks_erase EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    in Hcallbacks.
  pose proof (audit_prepare_source_correct N (N * N)%type _ EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) (fun _ => 0) Hcallbacks) as Hprepare.
  destruct (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    as [prep prep_events] eqn:Hprepare_call; cbn in Hprepare.
  destruct Hprepare as [Hprep _].
  subst prep.
  pose proof (audit_legacy_reached_erases N (N * N)%type CN EN node_enc cfg (prepare EN cfg)
    (Graph.entries cfg) Hnode) as Hreached.
  unfold audit_legacy_reached_counted in Hreached.
  destruct (audit_dfs_source_counted (prepare EN cfg) (audit_legacy_dfs_callbacks node_enc cfg)
    FinSet.empty (Graph.entries cfg)) as [result reached_events] eqn:Hdfs; cbn in Hreached.
  pose proof (audit_legacy_check_nodes_erases F N (N * N)%type T CN CF CT
    (audit_legacy_successor_event N (N * N) CN) CR CW CD EN EF ET node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc cfg (prepare EN cfg)) reads writes definitions
    (fun n => fst (reads n)) (fun n => fst (writes n)) (def_of_load ms) cfg (prepare EN cfg)
    (visited result) f (Graph.nodes g) Hnode Hfunction Hsite
    (fun n => audit_legacy_successors_erases N (N * N)%type CN EN node_enc cfg
      (prepare EN cfg) n Hnode)
    (fun _ => eq_refl) (fun _ => eq_refl) Hdefinitions) as Hcheck.
  destruct (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc cfg (prepare EN cfg)) reads writes cfg
    (prepare EN cfg) (visited result) definitions f (Graph.nodes g)) as [answer check_events].
  cbn in Hcheck |- *.
  rewrite Hcheck, Hreached.
  unfold legacy_reached; rewrite <- Hcfg; reflexivity.
Qed.
