(** * Snapshot refresh with complete graph callbacks

    Refresh captures outgoing, target and encoder bodies in the actual full prepare execution.
    For example, a matching epoch preserves the saved graph, effect table and completed memo.
    Builds on: snapshot-valued caches, full graph preparation and the fixed memo query. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditPrimitive.
From Galois.Analyses Require Import AnalysesAuditMemoryMemoSnapshot AnalysesAuditMemoryTable
  AnalysesAuditMemorySharedBudget AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryGraphCallbacks.
Import List.ListNotations.

Inductive audit_snapshot_refresh_source_event (N E T Epoch CE CN OE FE TE : Type) : Type :=
  | AuditSnapshotSourceEpoch (old current : Epoch) (old_body current_body : list CE)
      (comparison : list audit_positive_eqb_event)
  | AuditSnapshotSourceHit
  | AuditSnapshotSourceMiss
      (preparation : list (audit_prepare_source_event N E (audit_snapshot_graph_body CN OE TE)))
      (table : list (audit_memory_table_event N E T CE OE FE)).
Arguments AuditSnapshotSourceEpoch {N E T Epoch CE CN OE FE TE} _ _ _ _ _.
Arguments AuditSnapshotSourceHit {N E T Epoch CE CN OE FE TE}.
Arguments AuditSnapshotSourceMiss {N E T Epoch CE CN OE FE TE} _ _.

Definition audit_snapshot_refresh_source {N E T Epoch CE CN OE FE TE}
    (EN : encoding N) (epoch_enc : Epoch -> positive * list CE)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (old : audit_snapshot_memo_cache N E T Epoch EN) (current : memo_snapshot N E T Epoch) :
    audit_snapshot_memo_cache N E T Epoch EN *
      list (audit_snapshot_refresh_source_event N E T Epoch CE CN OE FE TE) :=
  let old_epoch := snapshot_epoch (audit_cache_snapshot old) in
  let current_epoch := snapshot_epoch current in
  let '(old_code, old_body) := epoch_enc old_epoch in
  let '(current_code, current_body) := epoch_enc current_epoch in
  let '(same, comparison) := audit_positive_eqb old_code current_code in
  let prefix := AuditSnapshotSourceEpoch old_epoch current_epoch old_body current_body comparison in
  if same then (old, [prefix; AuditSnapshotSourceHit])
  else
    let '(prepared, preparation) := audit_prepare_source_counted EN (snapshot_graph current)
      (audit_snapshot_graph_callbacks node_enc out target) in
    let '(table, rows) := audit_memory_effect_table edge_enc out effects
      (Graph.nodes (snapshot_graph current)) in
    (AuditSnapshotMemoCache current prepared table Map.empty,
      [prefix; AuditSnapshotSourceMiss preparation rows]).

Fixpoint audit_snapshot_refresh_full_source_work {N E T Epoch CE CN OE FE TE}
    (epoch_work : list CE -> nat) (node_work : list CN -> nat) (edge_work : list CE -> nat)
    (out_work : list OE -> nat) (effect_work : list FE -> nat) (target_work : list TE -> nat)
    (events : list (audit_snapshot_refresh_source_event N E T Epoch CE CN OE FE TE)) : nat :=
  match events with
  | [] => 0
  | AuditSnapshotSourceEpoch _ _ old_body current_body comparison :: rest =>
      2 + epoch_work old_body + epoch_work current_body +
      audit_positive_eqb_source_work comparison +
      audit_snapshot_refresh_full_source_work epoch_work node_work edge_work out_work
        effect_work target_work rest
  | AuditSnapshotSourceHit :: rest => 2 +
      audit_snapshot_refresh_full_source_work epoch_work node_work edge_work out_work
        effect_work target_work rest
  | AuditSnapshotSourceMiss preparation table :: rest =>
      6 + audit_prepare_source_work (audit_snapshot_graph_body_work node_work out_work target_work)
        preparation + audit_memory_table_work edge_work out_work effect_work table +
      audit_snapshot_refresh_full_source_work epoch_work node_work edge_work out_work
        effect_work target_work rest
  end.

Definition audit_snapshot_refresh_input_budget {N E T Epoch CE CN OE FE TE}
    (EN : encoding N) (epoch_enc : Epoch -> positive * list CE)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (epoch_budget : Epoch -> nat) (node_budget out_budget : N -> nat)
    (edge_budget effect_budget target_budget : E -> nat)
    (old : audit_snapshot_memo_cache N E T Epoch EN) (current : memo_snapshot N E T Epoch) : nat :=
  let old_epoch := snapshot_epoch (audit_cache_snapshot old) in
  let current_epoch := snapshot_epoch current in
  let old_code := fst (epoch_enc old_epoch) in
  let current_code := fst (epoch_enc current_epoch) in
  4 + epoch_budget old_epoch + epoch_budget current_epoch +
  2 * Nat.min (Pos.size_nat old_code) (Pos.size_nat current_code) +
  if Pos.eqb old_code current_code then 0 else
    let g := snapshot_graph current in
    6 + audit_prepare_source_budget EN g +
      audit_graph_prepare_full_event_bound g *
        audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
          (Graph.nodes g) +
      audit_memory_table_input_budget edge_enc out effects edge_budget out_budget effect_budget
        (Graph.nodes g).

(** A hit preserves the complete saved snapshot and all dependent cache values exactly. *)
Definition audit_snapshot_refresh_source_hit_statement : Prop :=
  forall N E T Epoch CE CN OE FE TE (EN : encoding N)
      (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      old current,
    Pos.eqb (fst (epoch_enc (snapshot_epoch (audit_cache_snapshot old))))
      (fst (epoch_enc (snapshot_epoch current))) = true ->
    fst (audit_snapshot_refresh_source EN epoch_enc node_enc edge_enc out target effects old
      current) =
      old.

(** On an epoch-code miss, matching encoders and graph and effect callbacks rebuild the saved
    snapshot indexes and clear entries. *)
Definition audit_snapshot_refresh_source_miss_statement : Prop :=
  forall N E T Epoch CE CN OE FE TE (EN : encoding N) (EE : encoding E)
      (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      old current,
    Pos.eqb (fst (epoch_enc (snapshot_epoch (audit_cache_snapshot old))))
      (fst (epoch_enc (snapshot_epoch current))) = false ->
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out (snapshot_graph current) n) ->
    (forall e, fst (target e) = Graph.target (snapshot_graph current) e) ->
    (forall e, fst (effects e) = snapshot_effects current e) ->
    let result := fst (audit_snapshot_refresh_source EN epoch_enc node_enc edge_enc out target
      effects
      old current) in
    result = AuditSnapshotMemoCache current (prepare EN (snapshot_graph current))
      (memory_walk_effect_table EE (snapshot_graph current) (snapshot_effects current)) Map.empty.

(** Matching node, outgoing and target callbacks and callback budgets bound the full refresh
    source work. *)
Definition audit_snapshot_refresh_whole_input_bound_statement : Prop :=
  forall N E T Epoch CE CN OE FE TE (EN : encoding N)
      (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      epoch_work node_work edge_work out_work effect_work target_work
      epoch_budget node_budget edge_budget out_budget effect_budget target_budget old current,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out (snapshot_graph current) n) ->
    (forall e, fst (target e) = Graph.target (snapshot_graph current) e) ->
    (forall epoch, epoch_work (snd (epoch_enc epoch)) <= epoch_budget epoch) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    audit_snapshot_refresh_full_source_work epoch_work node_work edge_work out_work effect_work
      target_work (snd (audit_snapshot_refresh_source EN epoch_enc node_enc edge_enc out target
        effects old current)) <=
    audit_snapshot_refresh_input_budget EN epoch_enc node_enc edge_enc out target effects
      epoch_budget node_budget out_budget edge_budget effect_budget target_budget old current.

(** Query executes the stored snapshot values, including after cross-snapshot epoch reuse. *)
Definition audit_snapshot_query {N E T Epoch} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (cache : audit_snapshot_memo_cache N E T Epoch EN) (q : memory_scope T)
    (start : memory_version N E) (fuel : positive) :
    memory_clobber_result N E * audit_snapshot_memo_cache N E T Epoch EN :=
  let saved := audit_cache_snapshot cache in
  let state := @MemoState N E T EN (snapshot_graph saved) (snapshot_effects saved)
    (snapshot_memory saved) (audit_cache_prepared cache) (audit_cache_effect_index cache)
    (audit_cache_entries cache) in
  let '(result, final) := audit_memory_memo_query EN EE ET (snapshot_graph saved)
    (snapshot_effects saved) (snapshot_memory saved) state q start fuel in
  (result, AuditSnapshotMemoCache saved (audit_cache_prepared cache) (audit_cache_effect_index
    cache)
    (@memo_entries N E T EN (snapshot_graph saved) (snapshot_effects saved) (snapshot_memory saved)
      final)).

(** Querying preserves the saved snapshot, predecessor lookups and effect index while threading
    entries. *)
Definition audit_snapshot_query_saved_values_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T) cache q start fuel,
    let final := snd (@audit_snapshot_query N E T Epoch EN EE ET cache q start fuel) in
    audit_cache_snapshot final = audit_cache_snapshot cache /\
    (forall n, pred_edges (audit_cache_prepared final) n =
      pred_edges (audit_cache_prepared cache) n) /\
    audit_cache_effect_index final = audit_cache_effect_index cache.
