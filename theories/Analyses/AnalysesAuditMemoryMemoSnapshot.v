(** * Snapshot-valued memo state and exact epoch refresh

    The prepared graph and effect index are dependent values inside one stored snapshot.
    A matching epoch returns the complete cache unchanged. A miss prepares and indexes
    the new snapshot and starts with an empty memo table. This avoids transporting a
    dependent cache across merely pointwise observation equality.
    For example, a matching epoch preserves existing memo entries.
    Builds on: memo state, graph preparation and effect indexing. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Analyses Require Import AnalysesAuditMemoryState AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryMemo AnalysesAuditMemoryTable.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
From Galois.Collections Require Import CollectionsAuditPrimitive.
Import List.ListNotations.

Record audit_snapshot_memo_cache (N E T Epoch : Type) (EN : encoding N) : Type :=
  AuditSnapshotMemoCache {
    audit_cache_snapshot : memo_snapshot N E T Epoch;
    audit_cache_prepared : prepared EN (snapshot_graph audit_cache_snapshot);
    audit_cache_effect_index : Map.t E (Map.t nat (memory_effect T));
    audit_cache_entries : Map.t (positive * memory_version N E) (memo_entry N E)
  }.
Arguments AuditSnapshotMemoCache {N E T Epoch EN}.
Arguments audit_cache_snapshot {N E T Epoch EN} _.
Arguments audit_cache_prepared {N E T Epoch EN} _.
Arguments audit_cache_effect_index {N E T Epoch EN} _.
Arguments audit_cache_entries {N E T Epoch EN} _.

Inductive audit_snapshot_refresh_event (N E T Epoch CE CN OE FE : Type) : Type :=
  | AuditSnapshotEpochCompare (old current : Epoch) (old_code current_code : positive)
      (old_body current_body : list CE) (result : bool) (calls : list audit_positive_eqb_event)
  | AuditSnapshotRefreshHit
  | AuditSnapshotRefreshMiss (prepare_events : list (audit_prepare_nested_event N E (list CN)))
      (table_events : list (audit_memory_table_event N E T CE OE FE)).
Arguments AuditSnapshotEpochCompare {N E T Epoch CE CN OE FE} _ _ _ _ _ _ _ _.
Arguments AuditSnapshotRefreshHit {N E T Epoch CE CN OE FE}.
Arguments AuditSnapshotRefreshMiss {N E T Epoch CE CN OE FE} _ _.

Definition audit_snapshot_prepare_callbacks {N E CN}
    (node_enc : N -> positive * list CN) (g : Graph.t N E) :
    audit_prepare_callback_model N E (list CN) :=
  @AuditPrepareCallbackModel N E (list CN)
    (fun n => (Graph.out g n, [])) (fun e => (Graph.target g e, []))
    (fun n => let '(code, trace) := node_enc n in (code, [trace])).

Definition audit_snapshot_out_adapter {N E OE} (g : Graph.t N E)
    : N -> list E * list OE := fun n => (Graph.out g n, []).

Definition audit_snapshot_effect_adapter {E T FE}
    (effects : E -> list (memory_effect T)) : E -> list (memory_effect T) * list FE :=
  fun e => (effects e, []).

Definition audit_snapshot_refresh {N E T Epoch CE CN OE FE}
    (EN : encoding N) (EE : encoding E) (epoch_enc : Epoch -> positive * list CE)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OE) (effects : E -> list (memory_effect T) * list FE)
    (old : audit_snapshot_memo_cache N E T Epoch EN)
    (current : memo_snapshot N E T Epoch)
    : audit_snapshot_memo_cache N E T Epoch EN *
      list (audit_snapshot_refresh_event N E T Epoch CE CN OE FE) :=
  let old_snapshot := audit_cache_snapshot old in
  let '(old_code, old_trace) := epoch_enc (snapshot_epoch old_snapshot) in
  let '(current_code, current_trace) := epoch_enc (snapshot_epoch current) in
  let '(same, compare_events) := audit_positive_eqb old_code current_code in
  if same then
    (old, [AuditSnapshotEpochCompare (snapshot_epoch old_snapshot) (snapshot_epoch current)
      old_code current_code old_trace current_trace same compare_events; AuditSnapshotRefreshHit])
  else
    let '(prepared_index, prepare_events) := audit_graph_prepare_nested_counted EN
      (snapshot_graph current) (audit_snapshot_prepare_callbacks node_enc (snapshot_graph
        current)) in
    let '(table, table_events) := audit_memory_effect_table edge_enc out effects
      (Graph.nodes (snapshot_graph current)) in
    (AuditSnapshotMemoCache current prepared_index table Map.empty,
      [AuditSnapshotEpochCompare (snapshot_epoch old_snapshot) (snapshot_epoch current)
        old_code current_code old_trace current_trace same compare_events;
       AuditSnapshotRefreshMiss prepare_events table_events]).

(** Matching epoch codes preserve the complete cache and emit two events. *)
Definition audit_snapshot_refresh_match_statement : Prop :=
  forall N E (T Epoch CE CN OE FE : Type) (EN : encoding N) (EE : encoding E)
    (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE)
    (old : audit_snapshot_memo_cache N E T Epoch EN) (current : memo_snapshot N E T Epoch),
    let '(result, events) := audit_snapshot_refresh EN EE epoch_enc node_enc edge_enc out effects
      old current in
    Pos.eqb (fst (epoch_enc (snapshot_epoch (audit_cache_snapshot old))))
      (fst (epoch_enc (snapshot_epoch current))) = true ->
    result = old /\ audit_cache_snapshot result = audit_cache_snapshot old /\
    audit_cache_effect_index result = audit_cache_effect_index old /\
    audit_cache_entries result = audit_cache_entries old /\
    length events = 2.

(** Matching epoch codes record the comparison and refresh-hit events exactly and return the old
    cache. *)
Definition audit_snapshot_refresh_match_execution_statement : Prop :=
  forall N E (T Epoch CE CN OE FE : Type) (EN : encoding N) (EE : encoding E)
    (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE)
    (old : audit_snapshot_memo_cache N E T Epoch EN) (current : memo_snapshot N E T Epoch),
    let '(result, events) := audit_snapshot_refresh EN EE epoch_enc node_enc edge_enc out effects
      old current in
    let old_snapshot := audit_cache_snapshot old in
    let '(old_code, old_body) := epoch_enc (snapshot_epoch old_snapshot) in
    let '(current_code, current_body) := epoch_enc (snapshot_epoch current) in
    let '(same, compare_events) := audit_positive_eqb old_code current_code in
    same = true ->
    result = old /\ events =
      [AuditSnapshotEpochCompare (snapshot_epoch old_snapshot) (snapshot_epoch current)
        old_code current_code old_body current_body same compare_events; AuditSnapshotRefreshHit].

(** With matching node and edge encoders, outgoing edges and effects, an epoch mismatch saves
    the current snapshot, rebuilds its effect index and clears entries. *)
Definition audit_snapshot_refresh_miss_statement : Prop :=
  forall N E (T Epoch CE CN OE FE : Type) (EN : encoding N) (EE : encoding E)
    (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE)
    (old : audit_snapshot_memo_cache N E T Epoch EN) (current : memo_snapshot N E T Epoch),
    let '(result, events) := audit_snapshot_refresh EN EE epoch_enc node_enc edge_enc out effects
      old current in
    Pos.eqb (fst (epoch_enc (snapshot_epoch (audit_cache_snapshot old))))
      (fst (epoch_enc (snapshot_epoch current))) = false ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out (snapshot_graph current) n) ->
    (forall e, fst (effects e) = snapshot_effects current e) ->
    audit_cache_snapshot result = current /\ audit_cache_entries result = Map.empty /\
    audit_cache_effect_index result = memory_walk_effect_table EE (snapshot_graph current)
      (snapshot_effects current) /\ length events = 2.

(** Mismatching epoch codes record the exact comparison, preparation and table traces. *)
Definition audit_snapshot_refresh_miss_execution_statement : Prop :=
  forall N E (T Epoch CE CN OE FE : Type) (EN : encoding N) (EE : encoding E)
    (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE)
    (old : audit_snapshot_memo_cache N E T Epoch EN) (current : memo_snapshot N E T Epoch),
    let '(result, events) := audit_snapshot_refresh EN EE epoch_enc node_enc edge_enc out effects
      old current in
    let old_snapshot := audit_cache_snapshot old in
    let '(old_code, old_body) := epoch_enc (snapshot_epoch old_snapshot) in
    let '(current_code, current_body) := epoch_enc (snapshot_epoch current) in
    let '(same, compare_events) := audit_positive_eqb old_code current_code in
    same = false ->
    events =
      [AuditSnapshotEpochCompare (snapshot_epoch old_snapshot) (snapshot_epoch current)
        old_code current_code old_body current_body same compare_events;
       AuditSnapshotRefreshMiss
         (snd (audit_graph_prepare_nested_counted EN (snapshot_graph current)
           (audit_snapshot_prepare_callbacks node_enc (snapshot_graph current))))
         (snd (audit_memory_effect_table edge_enc out effects (Graph.nodes (snapshot_graph
           current))))].

(** The saved snapshot has matching prepared and effect indexes, a well-formed memo map and no
    busy entries. *)
Definition audit_snapshot_cache_valid {N E T Epoch} (EN : encoding N) (EE : encoding E)
    (cache : audit_snapshot_memo_cache N E T Epoch EN) : Prop :=
  audit_cache_prepared cache = prepare EN (snapshot_graph (audit_cache_snapshot cache)) /\
  audit_cache_effect_index cache = memory_walk_effect_table EE
    (snapshot_graph (audit_cache_snapshot cache)) (snapshot_effects (audit_cache_snapshot cache)) /\
  Map.wf (memo_key EN EE) (audit_cache_entries cache) /\
  (forall k, Map.get (memo_key EN EE) k (audit_cache_entries cache) <> Some MemoBusy).

(** When both snapshots satisfy the domain laws and matching codes identify epochs, matching
    epoch codes imply equal epoch, graph, effect and memory observations. *)
Definition audit_snapshot_refresh_observation_context_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (EEpoch : encoding Epoch)
    (domain : memo_snapshot N E T Epoch -> Prop)
    (epoch_identity : forall (old current : memo_snapshot N E T Epoch),
      Pos.eqb (encode EEpoch (snapshot_epoch old)) (encode EEpoch (snapshot_epoch current)) = true
        ->
      snapshot_epoch old = snapshot_epoch current)
    (laws : memo_epoch_laws domain) (old current : memo_snapshot N E T Epoch),
    domain old -> domain current ->
    Pos.eqb (encode EEpoch (snapshot_epoch old)) (encode EEpoch (snapshot_epoch current)) = true ->
    snapshot_epoch old = snapshot_epoch current /\
    graph_observations_equal (snapshot_graph old) (snapshot_graph current) /\
    (forall e, snapshot_effects old e = snapshot_effects current e) /\
    memory_observations_equal (snapshot_memory old) (snapshot_memory current).

(** Matching epoch encoders make the observed code comparison agree with epoch matching. *)
Definition audit_snapshot_refresh_epoch_compare_erases_statement : Prop :=
  forall Epoch CE (EEpoch : encoding Epoch) (epoch_enc : Epoch -> positive * list CE) old current,
    (forall epoch, fst (epoch_enc epoch) = encode EEpoch epoch) ->
    Pos.eqb (fst (epoch_enc old)) (fst (epoch_enc current)) =
      epoch_matches EEpoch old current.

Fixpoint audit_snapshot_refresh_source_work {N E T Epoch CE CN OE FE}
    (epoch_work : list CE -> nat) (node_work : list CN -> nat)
    (edge_work : list CE -> nat) (out_work : list OE -> nat) (effect_work : list FE -> nat)
    (events : list (audit_snapshot_refresh_event N E T Epoch CE CN OE FE)) : nat :=
  match events with
  | [] => 0
  | AuditSnapshotEpochCompare _ _ _ _ old_body current_body _ eq_events :: rest =>
      2 + epoch_work old_body + epoch_work current_body + audit_positive_eqb_source_work eq_events +
        audit_snapshot_refresh_source_work epoch_work node_work edge_work out_work effect_work rest
  | AuditSnapshotRefreshHit :: rest => 2 +
      audit_snapshot_refresh_source_work epoch_work node_work edge_work out_work effect_work rest
  | AuditSnapshotRefreshMiss prepare_events table_events :: rest =>
      audit_graph_prepare_nested_total_work node_work prepare_events +
      audit_memory_table_work edge_work out_work effect_work table_events +
      audit_snapshot_refresh_source_work epoch_work node_work edge_work out_work effect_work rest
  end.
