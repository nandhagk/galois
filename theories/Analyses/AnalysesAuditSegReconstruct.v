(** * SEG reconstruction source

    Reconstruction captures the generated graph, solver map and transfer bodies.
    For example, an interior forward query folds the stored prefix from its source cut.
    Builds on: collection audit operations and SEG builder callbacks. *)
From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder.
Import List.ListNotations.

(** * SEG reconstruction source *)

Inductive audit_seg_reconstruct_event (N E U B : Type) : Type :=
  | ReconCase : nat -> audit_seg_reconstruct_event N E U B
  | ReconSet : audit_set_event N B -> audit_seg_reconstruct_event N E U B
  | ReconInterior : audit_map_event N (E * nat) B -> audit_seg_reconstruct_event N E U B
  | ReconPath : audit_map_event E (list E) B -> audit_seg_reconstruct_event N E U B
  | ReconAssignment : audit_map_event N bool B -> audit_seg_reconstruct_event N E U B
  | ReconGraph : audit_seg_graph_body N E B -> audit_seg_reconstruct_event N E U B
  | ReconTransfer : audit_seg_transfer_source_event E U B -> audit_seg_reconstruct_event N E U B.

Arguments ReconCase {N E U B} _.

Arguments ReconSet {N E U B} _.

Arguments ReconInterior {N E U B} _.

Arguments ReconPath {N E U B} _.

Arguments ReconAssignment {N E U B} _.

Arguments ReconGraph {N E U B} _.

Arguments ReconTransfer {N E U B} _.

(** This is the solver's actual lookup closure, including its Boolean bottom. *)
Definition audit_seg_reconstruct_cut {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (solution : Map.t N bool) (n : N) : bool * list (audit_seg_reconstruct_event N E U B) :=
  let '(found, events) := audit_map_get (seg_build_node_encode cb) n solution in
  (match found with
  Some value => value
  | None => true
  end, map ReconAssignment events).

Fixpoint audit_seg_reconstruct_first {N E U B} (k : nat) (edges : list E)
    : list E * list (audit_seg_reconstruct_event N E U B) :=
  match k, edges with
  | O, _ => ([], [ReconCase 0])
  | S _, [] => ([], [ReconCase 1])
  | S k', e :: rest => let '(out, calls) := audit_seg_reconstruct_first k' rest in
    (e :: out, ReconCase 2 :: calls)
  end.

Fixpoint audit_seg_reconstruct_skip {N E U B} (k : nat) (edges : list E)
    : list E * list (audit_seg_reconstruct_event N E U B) :=
  match k, edges with
  | O, _ => (edges, [ReconCase 3])
  | S _, [] => ([], [ReconCase 4])
  | S k', _ :: rest => let '(out, calls) := audit_seg_reconstruct_skip k' rest in
    (out, ReconCase 5 :: calls)
  end.

Fixpoint audit_seg_reconstruct_forward {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (u : U) (edges : list E) (value : bool) : bool * list (audit_seg_reconstruct_event N E U B) :=
  match edges with
  | [] => (value, [ReconCase 6])
  | e :: rest =>
    let '(next, here) := audit_seg_transfer_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e value in
    let '(result, later) := audit_seg_reconstruct_forward cb u rest next in
    (result, ReconCase 7 :: map ReconTransfer here ++ later)
  end.

Fixpoint audit_seg_reconstruct_backward {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (u : U) (edges : list E) (value : bool) : bool * list (audit_seg_reconstruct_event N E U B) :=
  match edges with
  | [] => (value, [ReconCase 8])
  | e :: rest =>
    let '(next, later) := audit_seg_reconstruct_backward cb u rest value in
    let '(result, here) := audit_seg_transfer_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e next in
    (result, ReconCase 9 :: later ++ map ReconTransfer here)
  end.

(** A probe reuses the constructed cut set and captured solver assignment. *)
Definition audit_seg_reconstruct_probe {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (work : seg_work N E) (idx : seg_index N E) (solution : Map.t N bool)
    (direction : audit_seg_direction) (u : U) (n : N) (cuts : FinSet.t N)
    : bool * list (audit_seg_reconstruct_event N E U B) :=
  let '(is_cut, test) := audit_finset_mem (seg_build_node_encode cb) n cuts in
  let prefix := map ReconSet test in
  if is_cut then let '(value, calls) := audit_seg_reconstruct_cut cb solution n in
    (value, prefix ++ calls)
  else let '(interior, reads) := audit_map_get (seg_build_node_encode cb) n (seg_interiors idx) in
    match interior with
    | None => (false, prefix ++ map ReconInterior reads ++ [ReconCase 10])
    | Some (a, k) =>
      match direction with
      | AuditAvailable =>
        let '(found, path_calls) := audit_map_get (seg_build_edge_encode cb) a (seg_paths idx) in
        let path := match found with
        Some es => es
        | None => []
        end in
        let '(selected, slice) := audit_seg_reconstruct_first (N := N) (U := U) (B := B) (S k)
          path in
        let '(node, graph_calls) := audit_seg_graph_source (seg_build_source cb) a in
        let '(initial, cut_calls) := audit_seg_reconstruct_cut cb solution node in
        let '(value, transfer_calls) := audit_seg_reconstruct_forward cb u selected initial in
        (value, prefix ++ map ReconInterior reads ++ map ReconPath path_calls ++ slice ++
          map ReconGraph graph_calls ++ cut_calls ++ transfer_calls)
      | AuditBusy =>
        let '(node, graph_calls) := audit_seg_graph_target (seg_build_edge_encode cb)
          (seg_build_target cb) work a in
        let '(initial, cut_calls) := audit_seg_reconstruct_cut cb solution node in
        let '(found, path_calls) := audit_map_get (seg_build_edge_encode cb) a (seg_paths idx) in
        let path := match found with
        Some es => es
        | None => []
        end in
        let '(selected, slice) := audit_seg_reconstruct_skip (N := N) (U := U) (B := B) (S k)
          path in
        let '(value, transfer_calls) := audit_seg_reconstruct_backward cb u selected initial in
        (value, prefix ++ map ReconInterior reads ++ map ReconGraph graph_calls ++ cut_calls ++
          map ReconPath path_calls ++ slice ++ transfer_calls)
      end
    end.

(** The setup receipt can be shared across later probes. *)
Definition audit_seg_reconstruct_setup {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (idx : seg_index N E) : FinSet.t N * list (audit_seg_reconstruct_event N E U B) :=
  let '(cuts, events) := audit_finset_of_list (seg_build_node_encode cb)
    (Graph.nodes (seg_graph idx)) in
  (cuts, map ReconSet events).

(** The one-shot operation includes exactly one setup and one probe. *)
Definition audit_seg_reconstruct_counted {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (work : seg_work N E) (idx : seg_index N E) (solution : Map.t N bool)
    (direction : audit_seg_direction) (u : U) (n : N)
    : bool * list (audit_seg_reconstruct_event N E U B) :=
  let '(cuts, setup) := audit_seg_reconstruct_setup cb idx in
  let '(value, events) := audit_seg_reconstruct_probe cb work idx solution direction u n cuts in
  (value, setup ++ events).

(** Work follows the events of this invocation, including supplied callback bodies. *)
Definition audit_seg_reconstruct_event_work {N E U B} (weight : B -> nat)
    (event : audit_seg_reconstruct_event N E U B) : nat :=
  let body := fun xs => fold_right (fun x total => weight x + total) 0 xs in
  64 + match event with
  | ReconCase _ => 0
  | ReconSet call => audit_finset_source_work body [call]
  | ReconInterior call => audit_map_source_work body [call]
  | ReconPath call => audit_map_source_work body [call]
  | ReconAssignment call => audit_map_source_work body [call]
  | ReconGraph call => audit_seg_graph_body_work weight call
  | ReconTransfer call => audit_seg_transfer_source_event_work weight call
  end.

Definition audit_seg_reconstruct_work {N E U B} (weight : B -> nat)
    (events : list (audit_seg_reconstruct_event N E U B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event total => audit_seg_reconstruct_event_work weight event + total) 0 events.

(** This allowance uses each callback's captured input from the same invocation. *)
Definition audit_seg_reconstruct_event_budget {N E U B} (node_budget : N -> nat)
    (edge_budget target_budget source_budget gen_budget : E -> nat) (expr_budget : U -> nat)
    (kill_budget : E * U -> nat) (event : audit_seg_reconstruct_event N E U B) : nat :=
  match event with
  | ReconSet (AuditSetMem n _ _ _ _ _) | ReconSet (AuditSetAdd n _ _ _ _ _) |
    ReconSet (AuditSetRemove n _ _ _ _ _) | ReconInterior (AuditMapGet n _ _ _ _ _) |
    ReconInterior (AuditMapSet n _ _ _ _ _ _) | ReconInterior (AuditMapRemove n _ _ _ _ _) |
    ReconAssignment (AuditMapGet n _ _ _ _ _) | ReconAssignment (AuditMapSet n _ _ _ _ _ _) |
    ReconAssignment (AuditMapRemove n _ _ _ _ _) => node_budget n
  | ReconPath (AuditMapGet e _ _ _ _ _) | ReconPath (AuditMapSet e _ _ _ _ _ _) |
    ReconPath (AuditMapRemove e _ _ _ _ _) => edge_budget e
  | ReconGraph call => audit_seg_graph_body_budget node_budget edge_budget target_budget
    source_budget call
  | ReconTransfer call => audit_seg_transfer_source_event_budget expr_budget gen_budget
    kill_budget call
  | _ => 0
  end.

(** The independent operand scale uses the requested path and its actual endpoints. *)
Definition audit_seg_reconstruct_input_scale {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (idx : seg_index N E) (u : U) (n : N) : nat :=
  let chosen := match Map.get EN n (seg_interiors idx) with
  Some (a, _) => Some a
  | None => None
  end in
  let paths := match chosen with
  Some a => seg_path EE idx a
  | None => []
  end in
  let endpoints := match chosen with
  | Some a => [Graph.source (seg_graph idx) a; Graph.target (seg_graph idx) a]
  | None => []
  end in
  let edges := match chosen with
  Some a => a :: paths
  | None => paths
  end in
  let nodes := n :: Graph.nodes (seg_graph idx) ++ endpoints in
  let expressions := u :: flat_map (gen gk) paths in
  length nodes + length edges + length expressions +
    fold_right (fun x total => Pos.size_nat (encode EN x) + total) 0 nodes +
    fold_right (fun x total => Pos.size_nat (encode EE x) + total) 0 edges +
    fold_right (fun x total => Pos.size_nat (encode EU x) + total) 0 expressions.

Definition audit_seg_reconstruct_input_budget {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (idx : seg_index N E) (u : U) (n : N) : nat :=
  (N.to_nat 65536%N) * Nat.pow (Nat.succ (audit_seg_reconstruct_input_scale EN EE EU gk idx u n)) 8.

(** Under callback and graph-closure laws, reconstruction returns the source answer within its
    bound. *)
Definition audit_seg_reconstruct_adapted_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (work : seg_work N E) (idx : seg_index N E) (solution : Map.t N bool)
    direction u n (weight : B -> nat)
    node_source edge_source expr_source target_source source_source gen_source kill_source
    node_budget edge_budget expr_budget target_budget source_budget gen_budget kill_budget,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    (forall e, fst (audit_seg_graph_source (seg_build_source cb) e) =
      Graph.source (seg_graph idx) e) ->
    (forall e, fst (audit_seg_graph_target (seg_build_edge_encode cb) (seg_build_target cb) work
      e) =
      Graph.target (seg_graph idx) e) ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      edge_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      source_budget ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source gen_budget ->
    audit_graph_external_callback_adapter (seg_build_kill cb) weight kill_source kill_budget ->
    let '(value, events) := audit_seg_reconstruct_counted cb work idx solution direction u n in
    let cut := lookup EN seg_must_lattice solution in
    let expected := match direction with
    | AuditAvailable => seg_reconstruct_available EN EE idx (seg_bit_transfer EU gk u) cut n
    | AuditBusy => seg_reconstruct_busy EN EE idx (seg_bit_transfer EU gk u) cut n
    end in
    let external := fold_right (fun event total => audit_seg_reconstruct_event_budget
      node_budget edge_budget target_budget source_budget gen_budget expr_budget kill_budget
      event + total) 0 events in
    value = expected /\ audit_seg_reconstruct_work weight events <=
      audit_seg_reconstruct_input_budget EN EE EU gk idx u n + external.
