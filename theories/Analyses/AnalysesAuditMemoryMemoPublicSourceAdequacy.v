(** * Public memo source adequacy

    Public queries use the saved incoming trie and return the concrete persistent memo cache.
    For example, a snapshot query reads its saved graph after an epoch hit.
    Builds on: query erasure, complete graph preparation and concrete table bounds. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditBaseAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryState
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteBound
  AnalysesAuditMemoryMemoExecuteBoundAdequacy AnalysesAuditMemoryMemoPublicSource
  AnalysesAuditMemoryMemoSnapshot AnalysesAuditMemoryMemoSnapshotSource
  AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryTable AnalysesAuditMemoryTableAdequacy
  AnalysesAuditMemorySharedBudgetAdequacy AnalysesAuditMemoryWalkIndex
  AnalysesAuditMemoryWalkIndexAdequacy.

(** * Saved memo queries *)

(** Public counted queries erase through the actual saved predecessor-map reads. *)
Theorem audit_memory_memo_public_source_erases : audit_memory_memo_public_source_erases_statement.
Proof.
  intros N E T CN CE SE OE BE EN EE ET node_enc edge_enc site_enc g effects mg state
    operand before scope start fuel Hnode Hedge Hsite Hoperand Hbefore.
  unfold audit_memory_memo_public_source_counted.
  apply audit_memory_memo_query_counted_erases; try assumption.
  intro node; apply audit_walk_predecessors_erases; apply Hnode.
Qed.

(** Public work pays the concrete saved predecessor trie and all query control. *)
Theorem audit_memory_memo_public_whole_input_bound :
  audit_memory_memo_public_whole_input_bound_statement.
Proof.
  intros N E T CN CE SE OE BE EN node_enc edge_enc site_enc g effects mg state operand before
    node_work edge_work site_work operand_work before_work
    node_budget edge_budget site_budget operand_budget before_budget scope start fuel
    Hnode Hedge Hsite Hoperand Hbefore.
  pose proof (audit_memory_memo_query_whole_input_bound N E T CN CE SE _ OE BE EN node_enc edge_enc
    site_enc g effects mg state
    (audit_walk_predecessors node_enc (in_index (@memo_adjacency N E T EN g effects mg state)))
    operand before node_work edge_work site_work
    (audit_map_source_work node_work) operand_work before_work
    node_budget edge_budget site_budget (audit_walk_predecessor_input_budget node_enc node_budget)
    operand_budget before_budget scope start fuel Hnode Hedge Hsite
    (fun node => audit_walk_predecessors_work_bound N E CN node_enc node_work node_budget
      (in_index (@memo_adjacency N E T EN g effects mg state)) node (Hnode node)) Hoperand Hbefore)
    as Hbound.
  unfold audit_memory_memo_public_source_counted.
  destruct (audit_memory_memo_query_counted node_enc edge_enc site_enc EN g effects mg state
    (audit_walk_predecessors node_enc (in_index (@memo_adjacency N E T EN g effects mg state)))
    operand before scope start fuel) as [encoded_scope run].
  destruct Hbound as [budget [Hbudget Hwork]]; exists budget; split; [exact Hbudget|lia].
Qed.

(** Snapshot query erasure uses the saved memory's actual operand and before callbacks. *)
Theorem audit_snapshot_query_source_erases : audit_snapshot_query_source_erases_statement.
Proof.
  intros N E T Epoch CN CE SE OE BE EN EE ET node_enc edge_enc site_enc cache operand before
    scope start fuel Hnode Hedge Hsite Hoperand Hbefore.
  pose proof (audit_memory_memo_public_source_erases N E T CN CE SE OE BE EN EE ET node_enc edge_enc
    site_enc (snapshot_graph (audit_cache_snapshot cache))
    (snapshot_effects (audit_cache_snapshot cache)) (snapshot_memory (audit_cache_snapshot cache))
    (@MemoState N E T EN _ _ _ (audit_cache_prepared cache) (audit_cache_effect_index cache)
      (audit_cache_entries cache)) operand before scope start fuel
    Hnode Hedge Hsite Hoperand Hbefore) as Herase.
  unfold audit_snapshot_query_source_counted, audit_snapshot_query.
  destruct (audit_memory_memo_query EN EE ET (snapshot_graph (audit_cache_snapshot cache))
    (snapshot_effects (audit_cache_snapshot cache)) (snapshot_memory (audit_cache_snapshot cache))
    (@MemoState N E T EN _ _ _ (audit_cache_prepared cache) (audit_cache_effect_index cache)
      (audit_cache_entries cache)) scope start fuel) as [result final].
  exact Herase.
Qed.

(** * Initialization and snapshot wrappers *)

(** Initial source preparation returns the exact public initial memo state. *)
Theorem audit_memory_memo_initial_source_erases : audit_memory_memo_initial_source_erases_statement.
Proof.
  intros N E T CN CE OE TE FE EN EE node_enc edge_enc out target effects g mg
    Hnode Hedge Hout Htarget.
  pose proof (audit_prepare_source_correct N E _ EN g
    (audit_snapshot_graph_callbacks node_enc out target) (fun _ => 0)
    (audit_walk_callbacks_erases N E CN OE TE EN g node_enc out target Hnode Hout Htarget))
    as Hprepare.
  pose proof (audit_memory_effect_table_erases N E T CE OE FE EE g edge_enc out effects
    (fun e => fst (effects e)) Hedge Hout (fun _ => eq_refl)) as Htable.
  unfold audit_memory_memo_initial_source_counted.
  destruct (audit_prepare_source_counted EN g (audit_snapshot_graph_callbacks node_enc out target))
    as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) as [table rows].
  cbn in Hprepare, Htable |- *; rewrite (proj1 Hprepare), Htable; reflexivity.
Qed.

(** Initial source work includes both complete graph preparation and concrete effect-table setup. *)
Theorem audit_memory_memo_initial_whole_input_bound :
  audit_memory_memo_initial_whole_input_bound_statement.
Proof.
  intros N E T CN CE OE TE FE EN node_enc edge_enc out target effects
    node_work edge_work out_work target_work effect_work node_budget edge_budget out_budget
    target_budget effect_budget g mg Hnode Hout Htarget Hnodework Hedgework Houtwork Htargetwork
    Heffectwork.
  pose proof (audit_walk_prepare_source_bound N E CN OE TE EN g node_enc out target
    node_work out_work target_work node_budget out_budget target_budget
    Hnode Hout Htarget Hnodework Houtwork Htargetwork) as Hprepare.
  pose proof (audit_memory_table_whole_input_bound N E T CE OE FE edge_enc out effects
    edge_work out_work effect_work edge_budget out_budget effect_budget (Graph.nodes g)
    Hedgework Houtwork Heffectwork) as Htable.
  unfold audit_memory_memo_initial_source_counted.
  destruct (audit_prepare_source_counted EN g (audit_snapshot_graph_callbacks node_enc out target))
    as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) as [table rows].
  cbn [snd] in Hprepare, Htable |- *; lia.
Qed.

(** Snapshot work uses the same saved-state recurrence and pays its cache reconstruction. *)
Theorem audit_snapshot_query_whole_input_bound : audit_snapshot_query_whole_input_bound_statement.
Proof.
  intros N E T Epoch CN CE SE OE BE EN node_enc edge_enc site_enc cache operand before
    node_work edge_work site_work operand_work before_work
    node_budget edge_budget site_budget operand_budget before_budget scope start fuel
    Hnode Hedge Hsite Hoperand Hbefore.
  pose proof (audit_memory_memo_public_whole_input_bound N E T CN CE SE OE BE EN node_enc edge_enc
    site_enc (snapshot_graph (audit_cache_snapshot cache))
    (snapshot_effects (audit_cache_snapshot cache)) (snapshot_memory (audit_cache_snapshot cache))
    (@MemoState N E T EN _ _ _ (audit_cache_prepared cache) (audit_cache_effect_index cache)
      (audit_cache_entries cache)) operand before node_work edge_work site_work operand_work
        before_work
    node_budget edge_budget site_budget operand_budget before_budget scope start fuel
    Hnode Hedge Hsite Hoperand Hbefore) as Hbound.
  unfold audit_snapshot_query_source_counted.
  destruct (audit_memory_memo_public_source_counted node_enc edge_enc site_enc EN
    (snapshot_graph (audit_cache_snapshot cache)) (snapshot_effects (audit_cache_snapshot cache))
    (snapshot_memory (audit_cache_snapshot cache))
    (@MemoState N E T EN _ _ _ (audit_cache_prepared cache) (audit_cache_effect_index cache)
      (audit_cache_entries cache)) operand before scope start fuel) as [encoded_scope run].
  destruct Hbound as [budget [Hbudget Hwork]]; exists budget; split; [exact Hbudget|lia].
Qed.
