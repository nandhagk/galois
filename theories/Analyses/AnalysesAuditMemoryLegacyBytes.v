(** * Historical bytes for the fixed legacy producer

    Byte preservation observes the same allocation identity after the selected definition or entry.
    For example, a retained live-on-entry pair compares its load byte with that entry's byte.
    Builds on: the original byte-view laws and the fixed all-walk checked projection. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryGraph AnalysesMemoryLegacy.
Import List.ListNotations.

(** Under byte laws and a well-formed graph, the projection preserves a covered read byte along
    a reachable run from just after an edge, or from entry, when its selected definition matches
    that edge's source, or live entry respectively, and the byte identity has that site at the
    corresponding starting state. *)
Definition audit_legacy_projection_historical_bytes_statement : Prop :=
  forall S O N E T F L (m : semantics S O) (bv : bytes_view S O N E T L)
      (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T)
      (function : F) (effects : E -> list (memory_effect T))
      (reads : N -> list (footprint T)) (mg : memory_graph N E)
      (load_occurrence : N -> option (E * nat)) (fuel : positive),
    bytes_laws m bv ->
    memory_graph_wf (cfg (bgv bv)) effects mg ->
    let ms := project_memory_legacy EN EE EF ET function (cfg (bgv bv)) effects (writes_at bv)
      reads mg load_occurrence fuel in
    (forall s after t edge rest node,
      reachable_state m s -> run_edges m (bgv bv) s [edge] after ->
      run_edges m (bgv bv) after rest t -> point (bgv bv) t = node ->
      def_of_load ms node = Some (MDef function (Graph.source (cfg (bgv bv)) edge)) ->
      forall identity site offset,
        covered (reads node) site offset 1 -> bsite bv after identity = Some site ->
        byte bv t identity offset = byte bv after identity offset) /\
    (forall s edges t node,
      reachable_state m s -> In (point (bgv bv) s) (Graph.entries (cfg (bgv bv))) ->
      run_edges m (bgv bv) s edges t -> point (bgv bv) t = node ->
      def_of_load ms node = Some (MLive function) ->
      forall identity site offset,
        covered (reads node) site offset 1 -> bsite bv s identity = Some site ->
        byte bv t identity offset = byte bv s identity offset).
