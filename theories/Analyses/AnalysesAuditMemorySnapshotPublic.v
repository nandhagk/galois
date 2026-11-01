(** * Plain snapshot refresh and full saved-cache validity

    Public refresh stores complete snapshot values and executes no counted observer or ghost trace.
    For example, an epoch hit returns the exact old cache and a miss prepares the new snapshot.
    Builds on: saved snapshots, the plain memo query and full source refresh models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryMemoSnapshot
  AnalysesAuditMemoryMemoSnapshotSource AnalysesAuditMemoryMemoPublicSource.
Import List.ListNotations.

Definition audit_snapshot_refresh_compute {N E T Epoch} (EN : encoding N) (EE : encoding E)
    (EEpoch : encoding Epoch) (old : audit_snapshot_memo_cache N E T Epoch EN)
    (current : memo_snapshot N E T Epoch) : audit_snapshot_memo_cache N E T Epoch EN :=
  if epoch_matches EEpoch (snapshot_epoch (audit_cache_snapshot old)) (snapshot_epoch current)
  then old
  else AuditSnapshotMemoCache current (prepare EN (snapshot_graph current))
    (memory_walk_effect_table EE (snapshot_graph current) (snapshot_effects current)) Map.empty.

Definition audit_snapshot_saved_state {N E T Epoch} (EN : encoding N)
    (cache : audit_snapshot_memo_cache N E T Epoch EN) :=
  let saved := audit_cache_snapshot cache in
  @MemoState N E T EN (snapshot_graph saved) (snapshot_effects saved) (snapshot_memory saved)
    (audit_cache_prepared cache) (audit_cache_effect_index cache) (audit_cache_entries cache).

(** Saved-state validity requires matching indexes, well-formed nonbusy entries and exact
    duplicate-free terminal roots and traces for completed entries with valid starts. *)
Definition audit_snapshot_semantic_valid {N E T Epoch} (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (cache : audit_snapshot_memo_cache N E T Epoch EN) : Prop :=
  let saved := audit_cache_snapshot cache in
  memo_valid EN EE ET (snapshot_graph saved) (snapshot_effects saved) (snapshot_memory saved)
    (audit_snapshot_saved_state EN cache).

(** Matching epoch, node and edge encoders and graph and effect callbacks make counted refresh
    agree with the plain refresh. *)
Definition audit_snapshot_refresh_plain_erases_statement : Prop :=
  forall N E T Epoch CE CN OE FE TE (EN : encoding N) (EE : encoding E) (EEpoch : encoding Epoch)
      (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE) old current,
    (forall epoch, fst (epoch_enc epoch) = encode EEpoch epoch) ->
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out (snapshot_graph current) n) ->
    (forall e, fst (target e) = Graph.target (snapshot_graph current) e) ->
    (forall e, fst (effects e) = snapshot_effects current e) ->
    fst (audit_snapshot_refresh_source EN epoch_enc node_enc edge_enc out target effects old
      current) =
      audit_snapshot_refresh_compute EN EE EEpoch old current.

(** Refreshing a semantically valid saved cache preserves validity on both epoch hit and rebuilt
    miss. *)
Definition audit_snapshot_refresh_semantic_valid_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (EEpoch : encoding Epoch) (old : audit_snapshot_memo_cache N E T Epoch EN) current,
    audit_snapshot_semantic_valid EN EE ET old ->
    audit_snapshot_semantic_valid EN EE ET
      (audit_snapshot_refresh_compute EN EE EEpoch old current).

(** For a valid saved cache, well-formed saved graph and valid start, querying preserves cache
    validity, snapshot and indexes. *)
Definition audit_snapshot_query_semantic_valid_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (cache : audit_snapshot_memo_cache N E T Epoch EN) scope start fuel,
    let saved := audit_cache_snapshot cache in
    audit_snapshot_semantic_valid EN EE ET cache ->
    memory_graph_wf (snapshot_graph saved) (snapshot_effects saved) (snapshot_memory saved) ->
    memory_valid_version (snapshot_graph saved) (snapshot_effects saved) (snapshot_memory saved)
      start ->
    let next := snd (audit_snapshot_query EN EE ET cache scope start fuel) in
    audit_snapshot_semantic_valid EN EE ET next /\
    audit_cache_snapshot next = audit_cache_snapshot cache /\
    audit_cache_prepared next = audit_cache_prepared cache /\
    audit_cache_effect_index next = audit_cache_effect_index cache.

(** For a valid saved cache and start in its well-formed graph, each terminal or
    repeated-version walk trace intersects the query roots. *)
Definition audit_snapshot_query_coverage_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (cache : audit_snapshot_memo_cache N E T Epoch EN) scope start fuel,
    let saved := audit_cache_snapshot cache in
    let graph := snapshot_graph saved in
    let effects := snapshot_effects saved in
    let memory := snapshot_memory saved in
    audit_snapshot_semantic_valid EN EE ET cache -> memory_graph_wf graph effects memory ->
    memory_valid_version graph effects memory start ->
    forall trace last, memory_walk_trace ET effects memory scope start trace ->
      memory_trace_last trace = Some last ->
      (memory_walk_terminal ET effects memory scope last \/ ~ NoDup trace) ->
      exists hit, In hit trace /\
        In hit (clobber_roots (fst (audit_snapshot_query EN EE ET cache scope start fuel))).

(** For a valid saved cache and start in its well-formed graph, complete query roots are exactly
    its reachable terminals. *)
Definition audit_snapshot_query_complete_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (cache : audit_snapshot_memo_cache N E T Epoch EN) scope start fuel,
    let saved := audit_cache_snapshot cache in
    let graph := snapshot_graph saved in
    let effects := snapshot_effects saved in
    let memory := snapshot_memory saved in
    audit_snapshot_semantic_valid EN EE ET cache -> memory_graph_wf graph effects memory ->
    memory_valid_version graph effects memory start ->
    let result := fst (audit_snapshot_query EN EE ET cache scope start fuel) in
    clobber_complete result = true ->
    forall version, In version (clobber_roots result) <->
      memory_walk_terminal ET effects memory scope version /\
      exists trace, memory_walk_trace ET effects memory scope start trace /\
        memory_trace_last trace = Some version.

(** Under the epoch-domain laws, matching epochs, valid cache and valid current graph and start,
    each terminal or repeated-version current trace intersects the saved-query roots. *)
Definition audit_snapshot_query_current_coverage_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (EEpoch : encoding Epoch) (domain : memo_snapshot N E T Epoch -> Prop)
      (cache : audit_snapshot_memo_cache N E T Epoch EN) current scope start fuel,
    memo_epoch_laws domain -> domain (audit_cache_snapshot cache) -> domain current ->
    epoch_matches EEpoch (snapshot_epoch (audit_cache_snapshot cache)) (snapshot_epoch current)
      = true ->
    audit_snapshot_semantic_valid EN EE ET cache ->
    memory_graph_wf (snapshot_graph current) (snapshot_effects current) (snapshot_memory current) ->
    memory_valid_version (snapshot_graph current) (snapshot_effects current) (snapshot_memory
      current)
      start ->
    forall trace last,
      memory_walk_trace ET (snapshot_effects current) (snapshot_memory current) scope start trace ->
      memory_trace_last trace = Some last ->
      (memory_walk_terminal ET (snapshot_effects current) (snapshot_memory current) scope last \/
        ~ NoDup trace) ->
      exists hit, In hit trace /\
        In hit (clobber_roots (fst (audit_snapshot_query EN EE ET cache scope start fuel))).

(** Under the epoch-domain laws, matching epochs, valid cache and valid current graph and start,
    complete saved-query roots are exactly current reachable terminals. *)
Definition audit_snapshot_query_current_complete_statement : Prop :=
  forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (EEpoch : encoding Epoch) (domain : memo_snapshot N E T Epoch -> Prop)
      (cache : audit_snapshot_memo_cache N E T Epoch EN) current scope start fuel,
    memo_epoch_laws domain -> domain (audit_cache_snapshot cache) -> domain current ->
    epoch_matches EEpoch (snapshot_epoch (audit_cache_snapshot cache)) (snapshot_epoch current)
      = true ->
    audit_snapshot_semantic_valid EN EE ET cache ->
    memory_graph_wf (snapshot_graph current) (snapshot_effects current) (snapshot_memory current) ->
    memory_valid_version (snapshot_graph current) (snapshot_effects current) (snapshot_memory
      current)
      start ->
    let result := fst (audit_snapshot_query EN EE ET cache scope start fuel) in
    clobber_complete result = true ->
    forall version, In version (clobber_roots result) <->
      memory_walk_terminal ET (snapshot_effects current) (snapshot_memory current) scope version /\
      exists trace,
        memory_walk_trace ET (snapshot_effects current) (snapshot_memory current) scope start
          trace /\
        memory_trace_last trace = Some version.
