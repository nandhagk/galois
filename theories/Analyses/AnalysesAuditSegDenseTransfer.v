(** * Dense expression transfer and clamp

    Each transfer captures the current facts, kill and generation calls and fresh universe build.
    For example, a killed expression is removed before generation is unioned and clamped.
    Builds on: AnalysesAuditSegDenseUniverse and the collection set models. *)
From Stdlib Require Import List Bool PArith Arith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion.
From Galois.Order Require Import OrderPowerset.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse
  AnalysesAuditSegDenseUniverse.
Import List.ListNotations.

(** * Dense expression transfer and clamp *)

Inductive audit_dense_transfer_event (N E U B : Type) : Type :=
  | DenseTransferUniverse (events : list (audit_seg_universe_event N E U B))
  | DenseTransferElements (events : list (audit_elements_event (U * unit)))
  | DenseTransferSet (events : list (audit_set_event U B))
  | DenseTransferUnion (events : list (audit_union_event U))
  | DenseTransferGen (edge : E) (out : list U) (body : list B)
  | DenseTransferKill (edge : E) (item : U) (out : bool) (body : list B)
  | DenseTransferCase (site : nat).

Arguments DenseTransferUniverse {N E U B} _.

Arguments DenseTransferElements {N E U B} _.

Arguments DenseTransferSet {N E U B} _.

Arguments DenseTransferUnion {N E U B} _.

Arguments DenseTransferGen {N E U B} _ _ _.

Arguments DenseTransferKill {N E U B} _ _ _ _.

Arguments DenseTransferCase {N E U B} _.

(** Filter retains every actual kill callback, including duplicates and later elements. *)
Fixpoint audit_dense_survivors {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (edge : E) (items : list U) : list U * list (audit_dense_transfer_event N E U B) :=
  match items with
  | [] => ([], [DenseTransferCase 0])
  | u :: rest =>
    let '(killed, body) := seg_build_kill cb (edge, u) in
    let '(later, events) := audit_dense_survivors cb edge rest in
    (if killed then later else u :: later, DenseTransferKill edge u killed body :: events)
  end.

(** Clamp's membership filter evaluates the entire supplied universe. *)
Fixpoint audit_dense_clamp_filter {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (set : FinSet.t U) (universe : list U) : list U * list (audit_dense_transfer_event N E U B) :=
  match universe with
  | [] => ([], [DenseTransferCase 1])
  | u :: rest =>
    let '(present, calls) := audit_finset_mem (seg_build_expr_encode cb) u set in
    let '(later, events) := audit_dense_clamp_filter cb set rest in
    (if present then u :: later else later, DenseTransferSet calls :: events)
  end.

(** Clamp rebuilds a finite set using the same filtered sequence. *)
Definition audit_dense_clamp {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (universe : list U) (set : FinSet.t U) :
    FinSet.t U * list (audit_dense_transfer_event N E U B) :=
  let '(selected, filter_events) := audit_dense_clamp_filter cb set universe in
  let '(out, set_events) := audit_finset_of_list (seg_build_expr_encode cb) selected in
  (out, filter_events ++ [DenseTransferSet set_events]).

(** One transfer uses its actual input set and captures a fresh expression-universe build. *)
Definition audit_dense_transfer {N E U B} (g : Graph.t N E)
    (cb : audit_seg_build_callbacks N E U B) (edge : E) (input : FinSet.t U) :
    FinSet.t U * list (audit_dense_transfer_event N E U B) :=
  let '(universe, universe_events) := audit_dense_universe g cb in
  let '(rows, elements) := audit_map_elements input in
  let '(survivors, kills) := audit_dense_survivors cb edge (map fst rows) in
  let '(kept, kept_events) := audit_finset_of_list (seg_build_expr_encode cb) survivors in
  let '(generated, gen_body) := seg_build_gen cb edge in
  let '(gen_set, gen_events) := audit_finset_of_list (seg_build_expr_encode cb) generated in
  let '(merged, union_events) := audit_finset_union kept gen_set in
  let '(out, clamp_events) := audit_dense_clamp cb universe merged in
  (out, [DenseTransferUniverse universe_events; DenseTransferElements elements;
    DenseTransferCase (length rows)] ++ kills ++
    [DenseTransferSet kept_events; DenseTransferGen edge generated gen_body;
     DenseTransferSet gen_events; DenseTransferUnion union_events] ++ clamp_events).

(** Each retained frame and genuine client callback contributes its actual body work. *)
Definition audit_dense_transfer_event_work {N E U B} (weight : B -> nat)
    (event : audit_dense_transfer_event N E U B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | DenseTransferUniverse events => audit_seg_universe_work weight events
  | DenseTransferElements events => fold_right (fun e n => audit_elements_frame_work e + n) 0 events
  | DenseTransferSet events => audit_finset_source_work body events
  | DenseTransferUnion events => audit_finset_union_source_work events
  | DenseTransferGen _ _ events | DenseTransferKill _ _ _ events => body events
  | DenseTransferCase site => site
  end.

(** Work is folded over the same transfer's captured event list. *)
Definition audit_dense_transfer_work {N E U B} (weight : B -> nat)
    (events : list (audit_dense_transfer_event N E U B)) : nat :=
  fold_right (fun event n => audit_dense_transfer_event_work weight event + n) 0 events.

(** Source bounds inspect original graph, edge, input-set nodes and actual generated key widths. *)
Definition audit_dense_transfer_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (edge : E) (input : FinSet.t U) : nat :=
  let universe := expr_universe EU gk in
  let keys := FinSet.elements input ++ gen gk edge ++ universe in
  let bits := fold_right (fun u n => Pos.size_nat (encode EU u) + n) 0 keys in
  (N.to_nat 65536%N) * Nat.pow (Nat.succ (audit_trie_nodes input + length keys + bits)) 8 +
    audit_dense_universe_budget EU gk.

(** External callback budgets follow each actual occurrence and selected set operation. *)
Definition audit_dense_transfer_event_budget {N E U B} (out_budget : N -> nat)
    (gen_budget : E -> nat) (expr_budget : U -> nat) (kill_budget : E * U -> nat)
    (event : audit_dense_transfer_event N E U B) : nat :=
  match event with
  | DenseTransferUniverse events => fold_right (fun e n =>
    audit_seg_universe_event_budget out_budget gen_budget expr_budget e + n) 0 events
  | DenseTransferSet events => fold_right (fun e n => n + match e with
    | AuditSetAdd u _ _ _ _ _ | AuditSetMem u _ _ _ _ _ |
      AuditSetRemove u _ _ _ _ _ => expr_budget u
    | AuditSetFold _ _ => 0
    end) 0 events
  | DenseTransferGen e _ _ => gen_budget e
  | DenseTransferKill e u _ _ => kill_budget (e, u)
  | _ => 0
  end.

(** A transfer witness erases to the actual clamped set and includes all callback body costs. *)
Definition audit_dense_transfer_source_statement : Prop :=
  forall (S O N E U C B : Type) (EU : encoding U) (gk : genkill_view S O N E U C)
    (cb : audit_seg_build_callbacks N E U B) (weight : B -> nat) (edge : E)
    (input : avail_set EU gk) out_source gen_source expr_source kill_source
    out_budget gen_budget expr_budget kill_budget,
    (forall n, fst (seg_build_out cb n) = Graph.out (cfg (gkview gk)) n) ->
    (forall e, fst (seg_build_gen cb e) = gen gk e) ->
    (forall e u, fst (seg_build_kill cb (e, u)) = kill gk e u) ->
    (forall u, fst (seg_build_expr_encode cb u) = encode EU u) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source gen_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    audit_graph_external_callback_adapter (seg_build_kill cb) weight kill_source kill_budget ->
    let '(out, events) := audit_dense_transfer (cfg (gkview gk)) cb edge (proj1_sig input) in
    out = proj1_sig (avail_transfer EU gk edge input) /\
      audit_dense_transfer_work weight events <= audit_dense_transfer_budget EU gk edge
        (proj1_sig input) +
        fold_right (fun event n => audit_dense_transfer_event_budget out_budget gen_budget
          expr_budget kill_budget event + n) 0 events.

(** Clamp charges each original universe occurrence and the input trie shape. *)
Definition audit_dense_clamp_budget {U} (EU : encoding U) (universe : list U)
    (set : FinSet.t U) : nat :=
  let bits := fold_right (fun u n => Pos.size_nat (encode EU u) + n) 0 universe in
  4096 * Nat.pow (S (audit_trie_nodes set + length universe + bits)) 4.

(** Clamp supplies the exact finite-set payload and its same-run source allowance. *)
Definition audit_dense_clamp_source_statement : Prop :=
  forall (N E U B : Type) (EU : encoding U) (cb : audit_seg_build_callbacks N E U B)
    (weight : B -> nat) (universe : list U) (set : FinSet.t U) expr_source expr_budget,
    (forall u, fst (seg_build_expr_encode cb u) = encode EU u) ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    let '(out, events) := audit_dense_clamp cb universe set in
    out = proj1_sig (finite_clamp EU universe set) /\
      audit_dense_transfer_work weight events <= audit_dense_clamp_budget EU universe set +
        fold_right (fun event n => audit_dense_transfer_event_budget (fun _ => 0) (fun _ => 0)
          expr_budget (fun _ => 0) event + n) 0 events.
