(** * Snapshot refresh adequacy

    Refresh preserves the complete saved cache on an epoch hit and rebuilds indexes on a miss.
    For example, a hit retains completed memo entries and their original graph.
    Builds on: snapshot refresh, primitive equality and memory table adequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditPrimitive
  CollectionsAuditPrimitiveAdequacy.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Analyses Require Import AnalysesAuditMemoryState AnalysesAuditMemoryMemoSnapshot
  AnalysesAuditMemoryTable AnalysesAuditMemoryTableAdequacy.
Import List.ListNotations.

(** * Exact refresh branches *)

(** Equal epoch codes retain every saved cache field and produce two refresh events. *)
Theorem audit_snapshot_refresh_match : audit_snapshot_refresh_match_statement.
Proof.
  intros N E T Epoch CE CN OE FE EN EE epoch_enc node_enc edge_enc out effects old current.
  unfold audit_snapshot_refresh.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  pose proof (audit_positive_eqb_erases old_code current_code) as Heq.
  destruct (audit_positive_eqb old_code current_code) as [same calls]; cbn in Heq |- *.
  rewrite <- Heq; destruct same; cbn.
  - intro Hsame; repeat split; reflexivity.
  - destruct (audit_graph_prepare_nested_counted EN (snapshot_graph current)
      (audit_snapshot_prepare_callbacks node_enc (snapshot_graph current))) as [prep preparation].
    destruct (audit_memory_effect_table edge_enc out effects
      (Graph.nodes (snapshot_graph current))) as [table rows].
    cbn; discriminate.
Qed.

(** A refresh hit records the exact encoded epochs and comparison body that selected it. *)
Theorem audit_snapshot_refresh_match_execution : audit_snapshot_refresh_match_execution_statement.
Proof.
  intros N E T Epoch CE CN OE FE EN EE epoch_enc node_enc edge_enc out effects old current.
  unfold audit_snapshot_refresh.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  destruct (audit_positive_eqb old_code current_code) as [same calls].
  destruct same; cbn.
  - intro Hsame; split; reflexivity.
  - destruct (audit_graph_prepare_nested_counted EN (snapshot_graph current)
      (audit_snapshot_prepare_callbacks node_enc (snapshot_graph current))) as [prep preparation].
    destruct (audit_memory_effect_table edge_enc out effects
      (Graph.nodes (snapshot_graph current))) as [table rows].
    cbn; discriminate.
Qed.

(** A miss stores the current snapshot, an empty memo and its exact rebuilt effect table. *)
Theorem audit_snapshot_refresh_miss : audit_snapshot_refresh_miss_statement.
Proof.
  intros N E T Epoch CE CN OE FE EN EE epoch_enc node_enc edge_enc out effects old current.
  unfold audit_snapshot_refresh.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  pose proof (audit_positive_eqb_erases old_code current_code) as Heq.
  destruct (audit_positive_eqb old_code current_code) as [same calls]; cbn in Heq |- *.
  rewrite <- Heq; destruct same; cbn; [discriminate|].
  destruct (audit_graph_prepare_nested_counted EN (snapshot_graph current)
    (audit_snapshot_prepare_callbacks node_enc (snapshot_graph current))) as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes (snapshot_graph current)))
    as [table rows] eqn:Htablecall.
  cbn; intros Hsame Hedge Hnode Hout Heffects.
  pose proof (audit_memory_effect_table_erases N E T CE OE FE EE (snapshot_graph current)
    edge_enc out effects (snapshot_effects current) Hedge Hout Heffects) as Htable.
  rewrite Htablecall in Htable.
  cbn in Htable |- *; repeat split; try reflexivity; exact Htable.
Qed.

(** A miss retains both complete preparation and table traces from its actual calls. *)
Theorem audit_snapshot_refresh_miss_execution : audit_snapshot_refresh_miss_execution_statement.
Proof.
  intros N E T Epoch CE CN OE FE EN EE epoch_enc node_enc edge_enc out effects old current.
  unfold audit_snapshot_refresh.
  destruct (epoch_enc (snapshot_epoch (audit_cache_snapshot old))) as [old_code old_body].
  destruct (epoch_enc (snapshot_epoch current)) as [current_code current_body].
  destruct (audit_positive_eqb old_code current_code) as [same calls].
  destruct same; cbn; [discriminate|].
  destruct (audit_graph_prepare_nested_counted EN (snapshot_graph current)
    (audit_snapshot_prepare_callbacks node_enc (snapshot_graph current))) as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes (snapshot_graph current)))
    as [table rows]; cbn; intro Hsame; reflexivity.
Qed.

(** * Epoch observations *)

(** The snapshot-domain law transports graph, effects and memory observations at equal epochs. *)
Theorem audit_snapshot_refresh_observation_context :
  audit_snapshot_refresh_observation_context_statement.
Proof.
  intros N E T Epoch EN EE ET EEpoch domain epoch_identity laws old current
    Hold Hcurrent Hmatch.
  pose proof (epoch_identity old current Hmatch) as Hepoch.
  split; [exact Hepoch|].
  exact (epoch_equal_observations domain laws old current Hold Hcurrent Hepoch).
Qed.

(** Correct epoch encoders select the same comparison as the public epoch predicate. *)
Theorem audit_snapshot_refresh_epoch_compare_erases :
  audit_snapshot_refresh_epoch_compare_erases_statement.
Proof.
  intros Epoch CE EEpoch epoch_enc old current Hencode.
  rewrite (Hencode old), (Hencode current); reflexivity.
Qed.
