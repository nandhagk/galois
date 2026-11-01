(** * Complete snapshot source adequacy

    The refresh mirror retains its actual callbacks and rebuilds the saved indexes on a miss.
    For example, a matching epoch preserves a nonempty memo without invoking preparation.
    Builds on: complete refresh, graph preparation and memory table adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditBaseAdequacy.
From Galois.Analyses Require Import AnalysesAuditMemoryState AnalysesAuditMemoryMemoSnapshot
  AnalysesAuditMemoryMemoSnapshotSource AnalysesAuditMemoryMemoExecute
  AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryTable
  AnalysesAuditMemoryTableAdequacy AnalysesAuditMemorySharedBudgetAdequacy
  AnalysesAuditMemoryWalkIndexAdequacy.

(** * Complete refresh source *)

(** A source refresh hit returns the entire original saved cache. *)
Theorem audit_snapshot_refresh_source_hit : audit_snapshot_refresh_source_hit_statement.
Proof.
  intros N E T Epoch CE CN OE FE TE EN epoch_enc node_enc edge_enc out target effects old current.
  unfold audit_snapshot_refresh_source.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  pose proof (audit_positive_eqb_erases old_code current_code) as Heq.
  destruct (audit_positive_eqb old_code current_code) as [same calls]; cbn in Heq |- *.
  rewrite <- Heq; intros ->; reflexivity.
Qed.

(** A source refresh miss rebuilds both indexes from the current snapshot observations. *)
Theorem audit_snapshot_refresh_source_miss : audit_snapshot_refresh_source_miss_statement.
Proof.
  intros N E T Epoch CE CN OE FE TE EN EE epoch_enc node_enc edge_enc out target effects old
    current Hmiss Hnode Hedge Hout Htarget Heffects.
  unfold audit_snapshot_refresh_source.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  pose proof (audit_positive_eqb_erases old_code current_code) as Heq.
  destruct (audit_positive_eqb old_code current_code) as [same calls]; cbn in Heq, Hmiss |- *.
  rewrite <- Heq in Hmiss; subst same.
  pose proof (audit_walk_callbacks_erases N E CN OE TE EN (snapshot_graph current)
    node_enc out target Hnode Hout Htarget) as Hcallbacks.
  pose proof (audit_prepare_source_correct N E _ EN (snapshot_graph current)
    (audit_snapshot_graph_callbacks node_enc out target)
    (fun _ => 0) Hcallbacks) as Hprepare.
  pose proof (audit_memory_effect_table_erases N E T CE OE FE EE (snapshot_graph current)
    edge_enc out effects (snapshot_effects current) Hedge Hout Heffects) as Htable.
  destruct (audit_prepare_source_counted EN (snapshot_graph current)
    (audit_snapshot_graph_callbacks node_enc out target))
    as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes (snapshot_graph current)))
    as [table rows].
  cbn in Hprepare, Htable |- *; rewrite (proj1 Hprepare), Htable; reflexivity.
Qed.

(** Complete refresh work is bounded by its epoch calls, concrete preparation and table inputs. *)
Theorem audit_snapshot_refresh_whole_input_bound :
  audit_snapshot_refresh_whole_input_bound_statement.
Proof.
  intros N E T Epoch CE CN OE FE TE EN epoch_enc node_enc edge_enc out target effects
    epoch_work node_work edge_work out_work effect_work target_work
    epoch_budget node_budget edge_budget out_budget effect_budget target_budget old current
    Hnode Hout Htarget Hepoch Hnodework Hedgework Houtwork Heffectwork Htargetwork.
  pose proof (audit_walk_prepare_source_bound N E CN OE TE EN (snapshot_graph current)
    node_enc out target node_work out_work target_work node_budget out_budget target_budget
    Hnode Hout Htarget Hnodework Houtwork Htargetwork) as Hprepare.
  pose proof (audit_memory_table_whole_input_bound N E T CE OE FE edge_enc out effects
    edge_work out_work effect_work edge_budget out_budget effect_budget
    (Graph.nodes (snapshot_graph current)) Hedgework Houtwork Heffectwork) as Htable.
  unfold audit_snapshot_refresh_source, audit_snapshot_refresh_input_budget.
  pose proof (Hepoch (snapshot_epoch (audit_cache_snapshot old))) as Hold.
  pose proof (Hepoch (snapshot_epoch current)) as Hcurrent.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  pose proof (audit_positive_eqb_erases old_code current_code) as Heq.
  pose proof (audit_positive_eqb_source_bound old_code current_code) as Hcompare.
  destruct (audit_positive_eqb old_code current_code) as [same calls].
  cbn [fst snd] in Heq, Hcompare, Hold, Hcurrent |- *; rewrite <- Heq.
  destruct same; cbn [snd audit_snapshot_refresh_full_source_work]; [lia|].
  destruct (audit_prepare_source_counted EN (snapshot_graph current)
    (audit_snapshot_graph_callbacks node_enc out target))
    as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes (snapshot_graph current)))
    as [table rows].
  cbn [snd audit_snapshot_refresh_full_source_work] in Hprepare, Htable |- *; lia.
Qed.

(** Querying threads memo entries while preserving the exact saved snapshot and both indexes. *)
Theorem audit_snapshot_query_saved_values : audit_snapshot_query_saved_values_statement.
Proof.
  intros N E T Epoch EN EE ET cache q start fuel.
  unfold audit_snapshot_query.
  destruct (audit_memory_memo_query EN EE ET
    (snapshot_graph (audit_cache_snapshot cache))
    (snapshot_effects (audit_cache_snapshot cache))
    (snapshot_memory (audit_cache_snapshot cache))
    (@MemoState N E T EN (snapshot_graph (audit_cache_snapshot cache))
      (snapshot_effects (audit_cache_snapshot cache)) (snapshot_memory (audit_cache_snapshot cache))
      (audit_cache_prepared cache) (audit_cache_effect_index cache)
      (audit_cache_entries cache)) q start fuel) as [result final].
  cbn; repeat split; reflexivity.
Qed.
