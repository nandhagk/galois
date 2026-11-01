(** * End-to-end counted legacy no-clobber checker

    The original edge graph is normalized, prepared and searched for entry reachability;
    each candidate then runs the exact strict pair check with full forward/reverse slices.
    The returned result is the existing [no_clobber_check] boolean.
    For example, a rejected candidate contributes its pair-check events.
    Builds on: legacy preparation, reachability and pair checking. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemoryIndex AnalysesAuditMemoryLegacyCfg
  AnalysesAuditMemoryLegacyChecker AnalysesAuditMemoryLegacySuccessor
  AnalysesAuditMemoryLegacySliceFull AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryWalkIndex.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
Import List.ListNotations.

(** Normalized graph callbacks close the internal indexed out lookup and pair projection. *)
Definition audit_legacy_prepare_callbacks {N CN} (node_enc : N -> positive * list CN)
    (rows : Map.t N (list (N * N))) :=
  audit_snapshot_graph_callbacks node_enc (audit_walk_predecessors node_enc rows)
    (fun edge : N * N => (snd edge, @nil unit)).

Record audit_legacy_no_clobber_events (F N E T CN CF CT OE TE CR CW CD : Type) : Type :=
  AuditLegacyNoClobberEvents {
    audit_legacy_check_cfg_events :
      list (audit_memory_index_event N (list (N * N)) CN (audit_legacy_cfg_event N E CN OE TE));
    audit_legacy_check_prepare_events : list (audit_prepare_source_event N (N * N)
        (audit_snapshot_graph_body CN (audit_map_event N (list (N * N)) CN) unit));
    audit_legacy_check_reached_events : list (audit_dfs_nested_event N (N * N)
        (audit_graph_callback_capture N (N * N) (list CN)));
    audit_legacy_check_nodes_events :
      list (audit_legacy_checker_event F N (N * N) T CN CF CT
        (audit_legacy_successor_event N (N * N) CN) CR CW CD)
  }.
Arguments AuditLegacyNoClobberEvents {F N E T CN CF CT OE TE CR CW CD} _ _ _ _.
Arguments audit_legacy_check_cfg_events {F N E T CN CF CT OE TE CR CW CD} _.
Arguments audit_legacy_check_prepare_events {F N E T CN CF CT OE TE CR CW CD} _.
Arguments audit_legacy_check_reached_events {F N E T CN CF CT OE TE CR CW CD} _.
Arguments audit_legacy_check_nodes_events {F N E T CN CF CT OE TE CR CW CD} _.

Definition audit_legacy_no_clobber_counted {F N E T CN CF CT OE TE CR CW CD}
    (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (reads : N -> list (footprint T) * list CR) (writes : N -> list (footprint T) * list CW)
    (function : F) (g : Graph.t N E)
    (definitions : N -> option (mem_node F N) * list CD)
    : bool * audit_legacy_no_clobber_events F N E T CN CF CT OE TE CR CW CD :=
  let '(rows, cfg_events) := audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g) in
  let cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd in
  let '(p, prepare_events) := audit_prepare_source_counted EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) in
  let '(reached_result, reached_events) := audit_dfs_source_counted p
    (audit_legacy_dfs_callbacks node_enc cfg) FinSet.empty (Graph.entries cfg) in
  let reached := visited reached_result in
  let successors := fun node => audit_legacy_successors_counted EN node_enc cfg p node in
  let '(answer, check_events) := audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc
    successors reads writes cfg p reached definitions function (Graph.nodes g) in
  (answer, AuditLegacyNoClobberEvents cfg_events prepare_events reached_events check_events).

Definition audit_legacy_no_clobber_source_work {F N E T CN CF CT OE TE CR CW CD}
    (EN : encoding N) (node_work : list CN -> nat) (function_work : list CF -> nat)
    (site_work : list CT -> nat) (out_work : list OE -> nat) (target_work : list TE -> nat)
    (read_work : list CR -> nat) (write_work : list CW -> nat) (definition_work : list CD -> nat)
    (events : audit_legacy_no_clobber_events F N E T CN CF CT OE TE CR CW CD) : nat :=
  audit_legacy_cfg_source_work node_work out_work target_work (audit_legacy_check_cfg_events
    events) +
  audit_prepare_source_work
    (audit_snapshot_graph_body_work node_work (audit_map_source_work node_work) (@length unit))
      (audit_legacy_check_prepare_events events) +
  audit_dfs_source_work node_work (audit_legacy_check_reached_events events) +
  audit_legacy_checker_source_work EN node_work function_work site_work
    (audit_legacy_successor_source_work node_work) read_work write_work definition_work
    (audit_legacy_check_nodes_events events).

(** Matching encoders, graph callbacks and load definitions recover the original no-clobber
    boolean using the supplied read and write results. *)
Definition audit_legacy_no_clobber_erases_statement : Prop :=
  forall F N E T CN CF CT OE TE CR CW CD (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT) (out : N -> list E * list OE)
    (target : E -> N * list TE) (reads : N -> list (footprint T) * list CR)
    (writes : N -> list (footprint T) * list CW) f (g : Graph.t N E)
    (ms : memory_ssa F N) (definitions : N -> option (mem_node F N) * list CD),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall x, fst (function_enc x) = encode EF x) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n, fst (definitions n) = def_of_load ms n) ->
    fst (audit_legacy_no_clobber_counted EN EF ET node_enc function_enc site_enc out target reads
      writes f g definitions) =
      no_clobber_check EN EF ET f g (fun n => fst (writes n)) (fun n => fst (reads n)) ms.
