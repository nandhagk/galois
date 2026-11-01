(** * Plain memo-threaded legacy projection

    This producer evaluates each listed load once, threads its memo and indexes retained pairs.
    For example, a later load at the same scope and version reuses a completed earlier memo query.
    Builds on: the plain memo query and the original independent all-walk retain decision. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects ViewsGraph.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryMemoExecute.
Import List.ListNotations.
Open Scope bool_scope.

Definition audit_memo_legacy_request {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (mg : memory_graph N E) (reached : FinSet.t N) (listed : FinSet.t E)
    (table : Map.t E (Map.t nat (memory_effect T)))
    (reads : N -> list (footprint T)) (loads : N -> option (E * nat)) (node : N) :=
  match loads node with
  | None => None
  | Some (edge, index) =>
      if Pos.eqb (encode EN (Graph.source g edge)) (encode EN node) &&
        FinSet.mem EN (Graph.source g edge) reached && FinSet.mem EE edge listed then
        match memory_walk_effect_get EE table edge index, memory_before mg edge index with
        | Some effect, Some start =>
            if memory_effect_has_read effect then Some (MemoryRegions (reads node), start) else None
        | _, _ => None
        end
      else None
  end.

Definition audit_memo_legacy_one {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (function : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (state : memo_state EN g effects mg) (cfg : Graph.t N (N * N)) (prep : prepared EN cfg)
    (reached : FinSet.t N) (listed : FinSet.t E)
    (writes reads : N -> list (footprint T)) (loads : N -> option (E * nat)) fuel node :=
  match audit_memo_legacy_request EN EE g mg reached listed
    (@memo_effect_index N E T EN g effects mg state) reads loads node with
  | None => (None, state)
  | Some (scope, start) =>
      let '(result, next) := audit_memory_memo_query EN EE ET g effects mg state scope start fuel in
      (legacy_retain EN EF ET function cfg prep reached writes reads node
        (legacy_clobber_proposal function g result), next)
  end.

Fixpoint audit_memo_legacy_nodes {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (function : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (cfg : Graph.t N (N * N)) (prep : prepared EN cfg)
    (reached : FinSet.t N) (listed : FinSet.t E)
    (writes reads : N -> list (footprint T)) (loads : N -> option (E * nat)) (fuel : positive)
    (nodes : list N) (state : memo_state EN g effects mg)
    (pairs : Map.t N (option (mem_node F N))) :=
  match nodes with
  | [] => (pairs, state)
  | node :: rest =>
      let '(candidate, next) := audit_memo_legacy_one EN EE EF ET function g effects mg state cfg
        prep reached listed writes reads loads fuel node in
      audit_memo_legacy_nodes EN EE EF ET function g effects mg cfg prep reached listed writes reads
        loads fuel rest next (Map.set EN node candidate pairs)
  end.

Definition audit_memory_memo_legacy_project {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (function : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (writes reads : N -> list (footprint T))
    (mg : memory_graph N E) (state : memo_state EN g effects mg)
    (loads : N -> option (E * nat)) (fuel : positive) :
    memory_ssa F N * memo_state EN g effects mg :=
  let cfg := legacy_cfg EN g in
  let prep := prepare EN cfg in
  let reached := legacy_reached prep (Graph.entries cfg) in
  let listed := FinSet.of_list EE (edges_of g) in
  let '(pairs, next) := audit_memo_legacy_nodes EN EE EF ET function g effects mg cfg prep reached
    listed writes reads loads fuel (Graph.nodes g) state Map.empty in
  (MemorySSA (fun node =>
    match Map.get EN node pairs with
    | Some result => result
    | None => None
    end),
    next).

(** The fixed memo-threaded producer satisfies the legacy checker and conditional
    byte-preservation contracts. *)
Definition audit_memory_memo_legacy_semantics_statement : Prop :=
  memo_legacy_checked_statement (@audit_memory_memo_legacy_project) /\
  memo_legacy_bytes_statement (@audit_memory_memo_legacy_project).
