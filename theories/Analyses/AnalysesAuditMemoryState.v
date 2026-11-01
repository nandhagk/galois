(** * G4 memory walk semantics

    This declaration-only pilot isolates G4 semantic contracts.
    For example, it keeps the historical observation in its original statement.
    Builds on: Galois.Analyses. *)

From Stdlib Require Import List Bool NArith PArith ZArith Permutation.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsDenseSet CollectionsUnionFind.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesMemoryWalk AnalysesMemoryLegacy AnalysesMemoryFrontier AnalysesMemorySealed.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding.
Import List.ListNotations.

(** Declarations from the MemoProbe candidate. *)

(** Equal encoded memory scopes denote equal scopes. *)
Definition scope_code_injective_statement : Prop := forall T (ET : encoding T) a b,
  scope_code ET a = scope_code ET b -> a = b.

Inductive memo_entry (N E : Type) : Type :=
  | MemoBusy
  | MemoDone (roots : list (memory_version N E)).

Arguments MemoBusy {N E}.
Arguments MemoDone {N E}.

Record memo_state {N E T} (EN : encoding N) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) : Type := MemoState {
  memo_adjacency : prepared EN g;
  memo_effect_index : Map.t E (Map.t nat (memory_effect T));
  memo_entries : Map.t (positive * memory_version N E) (memo_entry N E)
}.

(** Indexes match the graph and effects, entries are well formed and not busy, and each completed
    entry has a valid start, duplicate-free roots and traces, and exactly the reachable
    terminals. *)
Definition memo_valid {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (s : memo_state EN g effects mg) : Prop :=
  @memo_adjacency N E T EN g effects mg s = prepare EN g /\
  @memo_effect_index N E T EN g effects mg s = memory_walk_effect_table EE g effects /\
  Map.wf (memo_key EN EE) (@memo_entries N E T EN g effects mg s) /\
  (forall k, Map.get (memo_key EN EE) k (@memo_entries N E T EN g effects mg s) <> Some MemoBusy) /\
  forall q start roots,
    Map.get (memo_key EN EE) (scope_code ET q, start) (@memo_entries N E T EN g effects mg s) =
      Some (MemoDone roots) ->
    NoDup roots /\ memory_valid_version g effects mg start /\
    (forall trace, memory_walk_trace ET effects mg q start trace -> NoDup trace) /\
    forall v, In v roots <-> memory_walk_terminal ET effects mg q v /\
      exists trace, memory_walk_trace ET effects mg q start trace /\ memory_trace_last trace =
        Some v.

Definition memo_initial {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    memo_state EN g effects mg :=
  @MemoState N E T EN g effects mg (prepare EN g) (memory_walk_effect_table EE g effects) Map.empty.

Section Query.
  Variable query : forall {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    memo_state EN g effects mg -> memory_scope T -> memory_version N E -> positive ->
    memory_clobber_result N E * memo_state EN g effects mg.

  (** The freshly prepared state with an empty memo satisfies the memo validity invariant. *)
  Definition memo_initial_statement : Prop := forall N E T (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg,
    memo_valid EN EE ET g effects mg (memo_initial EN EE g effects mg).

  (** A query from a valid memo and valid start in a well-formed graph returns a valid memo. *)
  Definition memo_preserved_statement : Prop := forall N E T (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q start fuel,
    memo_valid EN EE ET g effects mg s ->
    memory_graph_wf g effects mg -> memory_valid_version g effects mg start ->
    memo_valid EN EE ET g effects mg (snd (query EN EE ET g effects mg s q start fuel)).

  (** For a valid memo and start in a well-formed graph, every terminal or cyclic walk trace
    intersects the query roots. *)
  Definition memo_coverage_statement : Prop := forall N E T (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q start fuel,
    memo_valid EN EE ET g effects mg s -> memory_graph_wf g effects mg ->
    memory_valid_version g effects mg start ->
    forall trace last, memory_walk_trace ET effects mg q start trace ->
      memory_trace_last trace = Some last ->
      (memory_walk_terminal ET effects mg q last \/ ~ NoDup trace) ->
      exists hit, In hit trace /\
        In hit (clobber_roots (fst (query EN EE ET g effects mg s q start fuel))).

  (** For a valid memo and start in a well-formed graph, a complete result contains exactly the
    reachable terminal versions. *)
  Definition memo_complete_statement : Prop := forall N E T (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q start fuel,
    memo_valid EN EE ET g effects mg s -> memory_graph_wf g effects mg ->
    memory_valid_version g effects mg start ->
    clobber_complete (fst (query EN EE ET g effects mg s q start fuel)) = true ->
    forall v, In v (clobber_roots (fst (query EN EE ET g effects mg s q start fuel))) <->
      memory_walk_terminal ET effects mg q v /\
      exists trace, memory_walk_trace ET effects mg q start trace /\ memory_trace_last trace =
        Some v.

  (** In a well-formed graph with a valid memo, each entry-rooted path to an actual occurrence
    has provenance and an occurrence history identifying its input, plus a walk from that input
    intersecting the query roots and ending at the last possible clobber, or live entry, over the
    path and the effects preceding that occurrence. *)
  Definition memo_execution_statement : Prop := forall N E T (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q fuel,
    memo_valid EN EE ET g effects mg s -> memory_graph_wf g effects mg ->
    forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
      memory_occurrence g effects e i a -> exists input origin trace hit,
      memory_provenance g effects mg root es (Graph.source g e)
        (memory_in mg (Graph.source g e)) (memory_last_path effects es) /\
      memory_occurrence_history g effects mg es e i input origin /\
      memory_walk_trace ET effects mg q input trace /\
      memory_trace_last trace = Some
        (memory_last_clobbers ET q e 0 (firstn i (effects e))
          (memory_path_last_clobber ET q effects es)) /\
      In hit trace /\ In hit (clobber_roots (fst (query EN EE ET g effects mg s q input fuel))).

  (** In a valid memo, a completed entry returns its roots as complete without changing the
    state. *)
  Definition memo_hit_statement : Prop := forall N E T (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q start
    fuel roots,
    memo_valid EN EE ET g effects mg s ->
    Map.get (memo_key EN EE) (scope_code ET q, start) (@memo_entries N E T EN g effects mg s) =
      Some (MemoDone roots) ->
    query EN EE ET g effects mg s q start fuel = (MemoryClobberResult roots true, s).

  (** A complete query from a valid memo and start in a well-formed graph stores its roots. *)
  Definition memo_store_complete_statement : Prop :=
    forall N E T (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q start fuel,
      memo_valid EN EE ET g effects mg s -> memory_graph_wf g effects mg ->
      memory_valid_version g effects mg start ->
      let '(result, next) := query EN EE ET g effects mg s q start fuel in
      clobber_complete result = true ->
      Map.get (memo_key EN EE) (scope_code ET q, start)
        (@memo_entries N E T EN g effects mg next) = Some (MemoDone (clobber_roots result)).

  (** After a complete query from a valid memo and start in a well-formed graph, any second fuel
    returns the same result and state. *)
  Definition memo_second_query_statement : Prop :=
    forall N E T (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) mg s q start first_fuel second_fuel,
      memo_valid EN EE ET g effects mg s -> memory_graph_wf g effects mg ->
      memory_valid_version g effects mg start ->
      let '(first, next) := query EN EE ET g effects mg s q start first_fuel in
      clobber_complete first = true ->
      query EN EE ET g effects mg next q start second_fuel = (first, next).
End Query.

Definition busy_cut {N E} (v : memory_version N E) : memory_clobber_result N E :=
  MemoryClobberResult [v] false.

(** A busy cut is incomplete and covers its version when the trace contains it. *)
Definition busy_cut_coverage_statement : Prop := forall N E (v : memory_version N E) trace,
  In v trace -> clobber_complete (busy_cut v) = false /\
  exists hit, In hit trace /\ In hit (clobber_roots (busy_cut v)).

(** A busy cut is incomplete and intersects any corresponding memory-walk trace. *)
Definition busy_cut_trace_statement : Prop :=
  forall N E T (ET : encoding T) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) q v trace,
    memory_walk_trace ET effects mg q v trace ->
    clobber_complete (busy_cut v) = false /\
    exists hit, In hit trace /\ In hit (clobber_roots (busy_cut v)).

(** Graph observations include ordered entries, nodes, edges and endpoints. *)
Definition graph_observations_equal {N E} (g h : Graph.t N E) : Prop :=
  Graph.entries g = Graph.entries h /\ Graph.nodes g = Graph.nodes h /\
  (forall n, Graph.out g n = Graph.out h n) /\
  (forall e, Graph.source g e = Graph.source h e /\ Graph.target g e = Graph.target h e).

(** Memory observations include versions and every exposed operand and edge lookup. *)
Definition memory_observations_equal {N E} (a b : memory_graph N E) : Prop :=
  memory_phis a = memory_phis b /\ memory_versions a = memory_versions b /\
  (forall n, memory_in a n = memory_in b n) /\
  (forall e i, memory_before a e i = memory_before b e i) /\
  (forall e, memory_out a e = memory_out b e) /\
  (forall n key, memory_operand a n key = memory_operand b n key).

Record memo_snapshot (N E T Epoch : Type) : Type := MemoSnapshot {
  snapshot_epoch : Epoch;
  snapshot_graph : Graph.t N E;
  snapshot_effects : E -> list (memory_effect T);
  snapshot_memory : memory_graph N E
}.

Arguments snapshot_epoch {N E T Epoch}.
Arguments snapshot_graph {N E T Epoch}.
Arguments snapshot_effects {N E T Epoch}.
Arguments snapshot_memory {N E T Epoch}.

(** In the snapshot domain, equal epochs imply equal graph, effect and memory observations. *)
Record memo_epoch_laws {N E T Epoch} (domain : memo_snapshot N E T Epoch -> Prop) : Prop := {
  (** Equal epochs in the domain identify graph, effect and memory observations. *)
  epoch_equal_observations : forall old current,
    domain old -> domain current -> snapshot_epoch old = snapshot_epoch current ->
    graph_observations_equal (snapshot_graph old) (snapshot_graph current) /\
    (forall e, snapshot_effects old e = snapshot_effects current e) /\
    memory_observations_equal (snapshot_memory old) (snapshot_memory current)
}.

Definition epoch_matches {Epoch} (E : encoding Epoch) (old current : Epoch) : bool :=
  Pos.eqb (encode E old) (encode E current).

Section Refresh.
  Variable refresh : forall {N E T Epoch} (EN : encoding N) (EE : encoding E)
    (EEpoch : encoding Epoch) (old current : memo_snapshot N E T Epoch),
    memo_state EN (snapshot_graph old) (snapshot_effects old) (snapshot_memory old) ->
    memo_state EN (snapshot_graph current) (snapshot_effects current) (snapshot_memory current).

  (** Within an epoch-law domain, refreshing a valid old state produces a valid state for the
    current snapshot. *)
  Definition refresh_valid_statement : Prop :=
    forall N E T Epoch (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (EEpoch : encoding Epoch) (domain : memo_snapshot N E T Epoch -> Prop),
      memo_epoch_laws domain -> forall old current,
      domain old -> domain current -> forall s,
      memo_valid EN EE ET (snapshot_graph old) (snapshot_effects old) (snapshot_memory old) s ->
      memo_valid EN EE ET (snapshot_graph current) (snapshot_effects current)
        (snapshot_memory current) (refresh EN EE EEpoch old current s).

  (** An epoch mismatch clears the refreshed memo entries. *)
  Definition refresh_mismatch_statement : Prop :=
    forall N E T Epoch (EN : encoding N) (EE : encoding E) (EEpoch : encoding Epoch)
      (old current : memo_snapshot N E T Epoch) s,
      epoch_matches EEpoch (snapshot_epoch old) (snapshot_epoch current) = false ->
      @memo_entries N E T EN (snapshot_graph current) (snapshot_effects current)
        (snapshot_memory current) (refresh EN EE EEpoch old current s) = Map.empty.

  (** An epoch match preserves the old memo entries in the refreshed state. *)
  Definition refresh_match_statement : Prop :=
    forall N E T Epoch (EN : encoding N) (EE : encoding E) (EEpoch : encoding Epoch)
      (old current : memo_snapshot N E T Epoch) s,
      epoch_matches EEpoch (snapshot_epoch old) (snapshot_epoch current) = true ->
      @memo_entries N E T EN (snapshot_graph current) (snapshot_effects current)
        (snapshot_memory current) (refresh EN EE EEpoch old current s) =
      @memo_entries N E T EN (snapshot_graph old) (snapshot_effects old) (snapshot_memory old) s.
End Refresh.

Section LegacyConsumer.
  Variable project : forall {F N E T} (EN : encoding N) (EE : encoding E) (EF : encoding F)
    (ET : encoding T) (f : F) (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (writes reads : N -> list (footprint T)) (mg : memory_graph N E),
    memo_state EN g effects mg -> (N -> option (E * nat)) -> positive ->
    memory_ssa F N * memo_state EN g effects mg.

  (** A legacy projection from a valid memo and well-formed graph passes the checker and returns
    a valid memo. *)
  Definition memo_legacy_checked_statement : Prop :=
    forall F N E T (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T)
      (f : F) (g : Graph.t N E) (effects : E -> list (memory_effect T))
      (writes reads : N -> list (footprint T)) mg s loads fuel,
      memo_valid EN EE ET g effects mg s -> memory_graph_wf g effects mg ->
      let '(ms, next) := project EN EE EF ET f g effects writes reads mg s loads fuel in
      no_clobber_check EN EF ET f g writes reads ms = true /\
      memo_valid EN EE ET g effects mg next.

  (** Under byte laws, a valid memo and a well-formed graph, the projection preserves a covered
    read byte along a reachable run from just after an edge, or from entry, when its selected
    definition matches that edge's source, or live entry respectively, and the byte identity has
    that site at the corresponding starting state. *)
  Definition memo_legacy_bytes_statement : Prop :=
    forall S O N E T F L (m : semantics S O) (bv : bytes_view S O N E T L)
      (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T) (f : F)
      (effects : E -> list (memory_effect T)) (reads : N -> list (footprint T)) mg s loads fuel,
      bytes_laws m bv ->
      memo_valid EN EE ET (cfg (bgv bv)) effects mg s ->
      memory_graph_wf (cfg (bgv bv)) effects mg ->
      let ms := fst (project EN EE EF ET f (cfg (bgv bv)) effects (writes_at bv) reads
        mg s loads fuel) in
      (forall before after first e es n,
        reachable_state m before -> run_edges m (bgv bv) before [e] first ->
        run_edges m (bgv bv) first es after -> point (bgv bv) after = n ->
        def_of_load ms n = Some (MDef f (Graph.source (cfg (bgv bv)) e)) ->
        forall l site offset, covered (reads n) site offset 1 -> bsite bv first l = Some site ->
          byte bv after l offset = byte bv first l offset) /\
      (forall before es after n, reachable_state m before ->
        In (point (bgv bv) before) (Graph.entries (cfg (bgv bv))) ->
        run_edges m (bgv bv) before es after -> point (bgv bv) after = n ->
        def_of_load ms n = Some (MLive f) ->
        forall l site offset, covered (reads n) site offset 1 -> bsite bv before l = Some site ->
          byte bv after l offset = byte bv before l offset).
End LegacyConsumer.
