(** * Independent complete legacy checker budgets

    These recurrences inspect original rows, footprints and actual intermediate reached sets.
    For example, a false owner still pays both DFS slices and the selected branch's callbacks.
    Builds on: full legacy preparation, strict pair checking and source DFS. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase GraphAuditDfs.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesMemoryFrontier.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditMap.
From Galois.Analyses Require Import AnalysesAuditMemoryInputBudget AnalysesAuditMemorySharedBudget
  AnalysesAuditMemoryIndex AnalysesAuditMemoryLegacyCfg AnalysesAuditMemoryLegacyOverlap
  AnalysesAuditMemoryLegacySlice AnalysesAuditMemoryLegacySliceFull
  AnalysesAuditMemoryLegacyChecker AnalysesAuditMemoryLegacySuccessor
  AnalysesAuditMemoryLegacyNoClobber AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryWalkIndex.
Import List.ListNotations.

Fixpoint audit_legacy_targets_input_budget {N E TE} (target : E -> N * list TE)
    (target_budget : E -> nat) (edges : list E) : nat :=
  match edges with
  | [] => 0
  | edge :: rest => 2 + target_budget edge +
      audit_legacy_targets_input_budget target target_budget rest
  end.

Definition audit_legacy_cfg_row_input_budget {N E CN OE TE}
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) (node_budget out_budget : N -> nat)
    (target_budget : E -> nat) (node : N) : nat :=
  let edges := fst (out node) in
  let targets := map (fun e => fst (target e)) edges in
  8 + length edges + out_budget node +
  audit_legacy_targets_input_budget target target_budget edges +
  audit_memory_distinct_input_budget node_enc node_budget targets + 4 * length targets.

Definition audit_legacy_cfg_input_budget {N E CN OE TE}
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) (node_budget out_budget : N -> nat)
    (target_budget : E -> nat) (nodes : list N) : nat :=
  audit_memory_index_input_budget node_enc node_budget
    (audit_legacy_cfg_row_input_budget node_enc out target node_budget out_budget target_budget)
      nodes.

Fixpoint audit_legacy_overlap_row_input_budget {T CT} (site_enc : T -> positive * list CT)
    (site_budget : T -> nat) (left : footprint T) (right : list (footprint T)) : nat :=
  match right with
  | [] => 1
  | item :: rest =>
      8 + site_budget (fp_site left) + site_budget (fp_site item) +
      2 * Nat.min (Pos.size_nat (fst (site_enc (fp_site left))))
        (Pos.size_nat (fst (site_enc (fp_site item)))) +
      audit_binary_weight (fp_lo left) (fp_hi left) +
      audit_binary_weight (fp_lo item) (fp_hi item) +
      audit_binary_weight (fp_lo left) (fp_hi item) +
      audit_binary_weight (fp_lo item) (fp_hi left) +
      audit_legacy_overlap_row_input_budget site_enc site_budget left rest
  end.

Fixpoint audit_legacy_overlap_input_budget {T CT} (site_enc : T -> positive * list CT)
    (site_budget : T -> nat) (left right : list (footprint T)) : nat :=
  match left with
  | [] => 1
  | item :: rest => 1 + audit_legacy_overlap_row_input_budget site_enc site_budget item right +
      audit_legacy_overlap_input_budget site_enc site_budget rest right
  end.

Fixpoint audit_legacy_slice_nodes_input_budget {N T CN CT W}
    (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
    (writes : N -> list (footprint T) * list W) (node_budget : N -> nat)
    (site_budget : T -> nat) (writes_budget : N -> nat)
    (read : list (footprint T)) (forward backward : FinSet.t N) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | node :: rest => 6 + 2 * audit_walk_predecessor_input_budget node_enc node_budget node +
      (if andb (
        match fst (audit_map_get node_enc node forward) with
        | Some _ => true
        | None => false
        end)
          (
            match fst (audit_map_get node_enc node backward) with
            | Some _ => true
            | None => false
            end)
       then 2 + writes_budget node +
         audit_legacy_overlap_input_budget site_enc site_budget (fst (writes node)) read
       else 0) + audit_legacy_slice_nodes_input_budget node_enc site_enc writes node_budget
         site_budget writes_budget read forward backward rest
  end.

Fixpoint audit_legacy_sum_vertex_budget {N} (node_budget : N -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | node :: rest => node_budget node + audit_legacy_sum_vertex_budget node_budget rest
  end.

(** DFS can discover only roots and actual targets from rows stored in its prepared out map. *)
Definition audit_legacy_dfs_vertices {N E} (g : Graph.t N E) (rows : Map.t N (list E))
    (roots : list N) : list N :=
  roots ++ map fst (Map.elements rows) ++
  map (Graph.target g) (flat_map snd (Map.elements rows)).

Definition audit_legacy_dfs_input_budget {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (node_budget : N -> nat) (roots : list N) : nat :=
  audit_dfs_source_budget EN g p roots + audit_dfs_full_input_event_bound p roots *
    (1 + audit_legacy_sum_vertex_budget node_budget
      (audit_legacy_dfs_vertices g (out_index p) roots)).

Definition audit_legacy_slice_full_input_budget {N E T CN CT W}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (site_enc : T -> positive * list CT) (g : Graph.t N E) (p : prepared EN g)
    (writes : N -> list (footprint T) * list W) (node_budget : N -> nat)
    (site_budget : T -> nat) (writes_budget : N -> nat) read roots load : nat :=
  let forward := visited (dfs p FinSet.empty roots) in
  let backward := visited (dfs (prepared_reverse p [load]) FinSet.empty [load]) in
  audit_legacy_dfs_input_budget EN g p node_budget roots +
  audit_legacy_dfs_input_budget EN (reverse_graph p [load]) (prepared_reverse p [load])
    node_budget [load] + audit_legacy_slice_nodes_input_budget node_enc site_enc writes node_budget
    site_budget writes_budget read forward backward (Graph.nodes g).

Definition audit_legacy_pair_input_budget {F N E T CN CF CT CS CR CW}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (function_enc : F -> positive * list CF) (site_enc : T -> positive * list CT)
    (successors : N -> list N * list CS) (reads : N -> list (footprint T) * list CR)
    (writes : N -> list (footprint T) * list CW) (node_budget : N -> nat)
    (function_budget : F -> nat) (site_budget : T -> nat)
    (successor_budget read_budget write_budget : N -> nat)
    (g : Graph.t N E) (p : prepared EN g) load (definition : mem_node F N) function : nat :=
  let owner :=
    match definition with
    | MDef owner _ | MLive owner => owner
    end in
  let roots :=
    match definition with
    | MDef _ node => fst (successors node)
    | MLive _ => Graph.entries g
    end in
  14 + audit_walk_predecessor_input_budget node_enc node_budget load +
  function_budget owner + function_budget function +
  2 * Nat.min (Pos.size_nat (fst (function_enc owner)))
    (Pos.size_nat (fst (function_enc function))) + read_budget load +
  (
    match definition with
    | MDef _ node => audit_walk_predecessor_input_budget node_enc node_budget node +
        successor_budget node
    | MLive _ => 0
    end) + audit_legacy_slice_full_input_budget EN node_enc site_enc g p writes node_budget
      site_budget write_budget (fst (reads load)) roots load.

Definition audit_legacy_successors_input_budget {N E CN} (node_enc : N -> positive * list CN)
    (node_budget : N -> nat) (rows : Map.t N (list E)) (node : N) : nat :=
  2 + audit_walk_predecessor_input_budget node_enc node_budget node +
  4 * length (
    match fst (audit_map_get node_enc node rows) with
    | Some edges => edges
    | None => []
    end).

Fixpoint audit_legacy_check_nodes_input_budget {F N E T CN CF CT CS CR CW CD}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (function_enc : F -> positive * list CF) (site_enc : T -> positive * list CT)
    (successors : N -> list N * list CS) (reads : N -> list (footprint T) * list CR)
    (writes : N -> list (footprint T) * list CW)
    (definitions : N -> option (mem_node F N) * list CD) (node_budget : N -> nat)
    (function_budget : F -> nat) (site_budget : T -> nat)
    (successor_budget read_budget write_budget definition_budget : N -> nat)
    (g : Graph.t N E) (p : prepared EN g) (function : F) (nodes : list N) : nat :=
  match nodes with
  | [] => 2
  | node :: rest => 4 + definition_budget node +
      (
        match fst (definitions node) with
        | None => 0
        | Some definition => audit_legacy_pair_input_budget EN node_enc function_enc site_enc
            successors reads writes node_budget function_budget site_budget successor_budget
              read_budget
            write_budget g p node definition function
        end) + audit_legacy_check_nodes_input_budget EN node_enc function_enc site_enc successors
        reads
        writes definitions node_budget function_budget site_budget successor_budget read_budget
        write_budget definition_budget g p function rest
  end.

Definition audit_legacy_no_clobber_input_budget {F N E T CN CF CT OE TE CR CW CD}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (function_enc : F -> positive * list CF) (site_enc : T -> positive * list CT)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (reads : N -> list (footprint T) * list CR) (writes : N -> list (footprint T) * list CW)
    (definitions : N -> option (mem_node F N) * list CD)
    (node_budget out_budget read_budget write_budget definition_budget : N -> nat)
    (function_budget : F -> nat) (site_budget : T -> nat) (target_budget : E -> nat)
    (g : Graph.t N E) (function : F) : nat :=
  let rows := fst (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) in
  let cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd in
  let prep := prepare EN cfg in
  let row_read_budget := audit_walk_predecessor_input_budget node_enc node_budget in
  audit_legacy_cfg_input_budget node_enc out target node_budget out_budget target_budget
    (Graph.nodes g) + audit_prepare_source_budget EN cfg +
  audit_graph_prepare_full_event_bound cfg *
    audit_snapshot_graph_input_budget (audit_walk_predecessors node_enc rows)
      (fun edge : N * N => (snd edge, @nil unit)) node_budget row_read_budget (fun _ => 1)
      (Graph.nodes cfg) +
  audit_legacy_dfs_input_budget EN cfg prep node_budget (Graph.entries cfg) +
  audit_legacy_check_nodes_input_budget EN node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc cfg prep) reads writes definitions
    node_budget function_budget site_budget
    (audit_legacy_successors_input_budget node_enc node_budget (out_index prep))
    read_budget write_budget definition_budget cfg prep function (Graph.nodes g).

(** Matching node codes and callback budgets bound the complete checker, including both DFS
    bodies and pair projections. *)
Definition audit_legacy_no_clobber_whole_input_bound_statement : Prop :=
  forall F N E T CN CF CT OE TE CR CW CD (EN : encoding N) (EF : encoding F) (ET : encoding T)
      (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
      (site_enc : T -> positive * list CT) (out : N -> list E * list OE)
      (target : E -> N * list TE) (reads : N -> list (footprint T) * list CR)
      (writes : N -> list (footprint T) * list CW)
      (definitions : N -> option (mem_node F N) * list CD)
      node_work function_work site_work out_work target_work read_work write_work definition_work
      node_budget function_budget site_budget out_budget target_budget read_budget write_budget
      definition_budget (g : Graph.t N E) function,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall f, function_work (snd (function_enc f)) <= function_budget f) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    (forall n, read_work (snd (reads n)) <= read_budget n) ->
    (forall n, write_work (snd (writes n)) <= write_budget n) ->
    (forall n, definition_work (snd (definitions n)) <= definition_budget n) ->
    audit_legacy_no_clobber_source_work EN node_work function_work site_work out_work target_work
      read_work write_work definition_work (snd (audit_legacy_no_clobber_counted EN EF ET node_enc
        function_enc site_enc out target reads writes function g definitions)) <=
    audit_legacy_no_clobber_input_budget EN node_enc function_enc site_enc out target reads writes
      definitions node_budget out_budget read_budget write_budget definition_budget function_budget
      site_budget target_budget g function.

(** Node, outgoing and target budgets bound construction of the legacy adjacency graph. *)
Definition audit_legacy_cfg_whole_input_bound_statement : Prop :=
  forall N E CN OE TE (EN : encoding N) (node_enc : N -> positive * list CN)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      node_work out_work target_work node_budget out_budget target_budget (g : Graph.t N E),
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    audit_legacy_cfg_source_work node_work out_work target_work
      (snd (audit_legacy_cfg_counted EN node_enc out target g)) <=
    audit_legacy_cfg_input_budget node_enc out target node_budget out_budget target_budget
      (Graph.nodes g).
