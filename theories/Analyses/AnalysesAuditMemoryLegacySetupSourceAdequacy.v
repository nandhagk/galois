(** * Adequacy of shared legacy projection setup

    Normalized adjacency, reachability and original effect indexes preserve their plain values.
    For example, duplicate listed edges are still charged when constructing the edge set.
    Builds on: legacy CFG, graph preparation, DFS and shared table adequacy. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditFinSetAdequacy CollectionsAuditMap.
From Galois.Views Require Import ViewsGraph.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase
  GraphAuditBaseAdequacy GraphAuditDfs.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryLegacy AnalysesMemoryWalk
  AnalysesAuditMemoryLegacySetupSource AnalysesAuditMemoryLegacyCfg
  AnalysesAuditMemoryLegacyCfgAdequacy AnalysesAuditMemoryLegacySliceFull
  AnalysesAuditMemoryLegacySliceFullAdequacy AnalysesAuditMemoryLegacyNoClobber
  AnalysesAuditMemoryLegacyNoClobberAdequacy AnalysesAuditMemoryLegacyInputBudget
  AnalysesAuditMemoryLegacyInputBudgetAdequacy AnalysesAuditMemoryIndex
  AnalysesAuditMemoryTable AnalysesAuditMemoryTableAdequacy AnalysesAuditMemorySharedBudget
  AnalysesAuditMemorySharedBudgetAdequacy AnalysesAuditMemoryGraphCallbacks
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryWalkIndexAdequacy.
Import List.ListNotations.

(** Every setup observation is the corresponding plain normalized graph or original index. *)
Theorem audit_legacy_projection_setup_erases : audit_legacy_projection_setup_erases_statement.
Proof.
  intros N E T CN CE OE TE FE EN EE node_enc edge_enc out target effects g Hnode Hedge Hout Htarget.
  pose proof (audit_legacy_cfg_erases N E CN OE TE EN node_enc out target g Hnode Hout Htarget)
    as Hcfg.
  pose proof (audit_memory_effect_table_erases N E T CE OE FE EE g edge_enc out effects
    (fun e => fst (effects e)) Hedge Hout (fun _ => eq_refl)) as Htable.
  assert (Hedges : fst (audit_memory_edges out (Graph.nodes g)) = edges_of g).
  { rewrite audit_memory_edges_erases; unfold edges_of.
    apply flat_map_ext; exact Hout. }
  unfold audit_legacy_projection_setup.
  destruct (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) as [rows cfg_events]
    eqn:Hrows.
  unfold audit_legacy_cfg_counted in Hcfg; rewrite Hrows in Hcfg; cbn [fst] in Hcfg.
  set (cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd) in *.
  pose proof (audit_prepare_source_correct N (N * N)%type _ EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) (fun _ => 0)
    (audit_legacy_prepare_callbacks_erases N CN EN node_enc rows (Graph.entries g)
      (Graph.nodes g) Hnode)) as Hprepare.
  destruct (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    as [prep prepare_events]; cbn [fst] in Hprepare.
  destruct Hprepare as [Hprep _]; subst prep.
  pose proof (audit_legacy_reached_erases N (N * N)%type CN EN node_enc cfg (prepare EN cfg)
    (Graph.entries cfg) Hnode) as Hreached.
  destruct (audit_legacy_reached_counted EN node_enc cfg (prepare EN cfg) (Graph.entries cfg))
    as [reached reached_events]; cbn [fst] in Hreached.
  destruct (audit_memory_edges out (Graph.nodes g)) as [edges edge_events]; cbn [fst] in Hedges.
  pose proof (audit_finset_of_list_erases E CE edge_enc EE edges (fun e _ => Hedge e)) as Hlisted.
  destruct (audit_finset_of_list edge_enc edges) as [listed listed_events]; cbn [fst] in Hlisted.
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) as [table table_events];
    cbn [fst] in Htable.
  cbn [audit_legacy_setup_cfg audit_legacy_setup_reached audit_legacy_setup_listed
    audit_legacy_setup_table audit_legacy_setup_prepared].
  rewrite Hreached, Hlisted, Htable, Hedges.
  unfold legacy_reached.
  rewrite Hcfg; repeat split; reflexivity.
Qed.

(** Per-edge encoder bounds lift to the duplicate-preserving edge-set construction budget. *)
Lemma audit_legacy_listed_work_input E CE (edge_enc : E -> positive * list CE)
    edge_work edge_budget edges :
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  audit_finset_source_work edge_work (snd (audit_finset_of_list edge_enc edges)) <=
    audit_legacy_listed_input_budget edge_enc edge_budget edges.
Proof.
  intro Hedge.
  pose proof (audit_finset_of_list_source_bound E CE edge_enc edge_work edges) as Hset.
  eapply Nat.le_trans; [exact Hset|].
  clear Hset.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_finset_of_list_budget audit_legacy_listed_input_budget].
    pose proof (Hedge edge); lia.
Qed.

(** The setup bound derives every internal phase from the original inputs and foreign budgets. *)
Theorem audit_legacy_setup_whole_input_bound : audit_legacy_setup_whole_input_bound_statement.
Proof.
  intros N E T CN CE OE TE FE EN node_enc edge_enc out target effects node_work edge_work
    out_work target_work effect_work node_budget edge_budget out_budget target_budget effect_budget
    g Hnode Hnw Hew How Htw Hfw.
  pose proof (audit_legacy_cfg_whole_input_bound N E CN OE TE EN node_enc out target node_work
    out_work target_work node_budget out_budget target_budget g Hnw How Htw) as Hcfg.
  pose proof (audit_memory_table_whole_input_bound N E T CE OE FE edge_enc out effects edge_work
    out_work effect_work edge_budget out_budget effect_budget (Graph.nodes g) Hew How Hfw)
    as Htable.
  pose proof (audit_memory_edges_work_exact N E OE out out_work (Graph.nodes g)) as Hedges.
  pose proof (audit_memory_edges_budget_input N E OE out out_work out_budget (Graph.nodes g) How)
    as Hedgesbudget.
  unfold audit_legacy_projection_setup, audit_legacy_setup_input_budget.
  destruct (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) as [rows cfg_events]
    eqn:Hrows.
  unfold audit_legacy_cfg_counted in Hcfg; rewrite Hrows in Hcfg; cbn [snd] in Hcfg.
  set (cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd).
  pose proof (audit_legacy_prepare_input_bound N CN EN node_enc node_work node_budget rows
    (Graph.entries g) (Graph.nodes g) Hnode Hnw) as Hpreparework.
  cbn zeta in Hpreparework; fold cfg in Hpreparework.
  pose proof (audit_prepare_source_correct N (N * N)%type _ EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) (fun _ => 0)
    (audit_legacy_prepare_callbacks_erases N CN EN node_enc rows (Graph.entries g)
      (Graph.nodes g) Hnode)) as Hprepare.
  destruct (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    as [prep prepare_events]; cbn [fst snd] in Hpreparework, Hprepare.
  destruct Hprepare as [Hprep _]; subst prep.
  pose proof (audit_legacy_dfs_input_bound N (N * N)%type CN EN cfg (prepare EN cfg) node_enc
    node_work node_budget (Graph.entries cfg) Hnode Hnw) as Hdfs.
  unfold audit_legacy_reached_counted.
  destruct (audit_dfs_source_counted (prepare EN cfg) (audit_legacy_dfs_callbacks node_enc cfg)
    FinSet.empty (Graph.entries cfg)) as [reached reached_events]; cbn [snd] in Hdfs.
  destruct (audit_memory_edges out (Graph.nodes g)) as [edges edge_events]; cbn [fst snd] in Hedges.
  pose proof (audit_legacy_listed_work_input E CE edge_enc edge_work edge_budget edges Hew) as Hset.
  destruct (audit_finset_of_list edge_enc edges) as [listed listed_events]; cbn [snd] in Hset.
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) as [table table_events];
    cbn [snd] in Htable.
  unfold audit_legacy_setup_source_work; cbn [audit_legacy_setup_cfg_events
    audit_legacy_setup_prepare_events audit_legacy_setup_reached_events
    audit_legacy_setup_edges_events audit_legacy_setup_listed_events
      audit_legacy_setup_table_events].
  cbn [fst]; fold cfg; lia.
Qed.
