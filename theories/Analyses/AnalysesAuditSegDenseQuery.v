(** * Dense SEG result probes

    A retained finite-set assignment answers node-expression queries without another solve.
    For example, a missing assignment uses the finite must-lattice bottom before membership.
    Builds on: AnalysesAuditSegDenseSystem and the shared map and set models. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist.
From Galois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesAuditSegBuilder.
Import List.ListNotations.

(** * Dense SEG result probes *)

Inductive audit_dense_probe_event (N U A B : Type) : Type :=
  | DenseProbeMap (event : audit_map_event N A B)
  | DenseProbeSet (event : audit_set_event U B)
  | DenseProbeCase.

Arguments DenseProbeMap {N U A B} _.

Arguments DenseProbeSet {N U A B} _.

Arguments DenseProbeCase {N U A B}.

(** A probe captures the node lookup and the actual finite-set membership. *)
Definition audit_dense_probe {N E U B} (EU : encoding U) (universe : list U)
    (cb : audit_seg_build_callbacks N E U B) (bottom : finite_set EU universe)
    (values : assignment N (finite_set EU universe)) (n : N) (u : U) :
    bool * list (audit_dense_probe_event N U (finite_set EU universe) B) :=
  let '(found, read_events) := audit_map_get (seg_build_node_encode cb) n values in
  let fact := match found with
  Some value => value
  | None => bottom
  end in
  let '(result, mem_events) := audit_finset_mem (seg_build_expr_encode cb) u (proj1_sig fact) in
  (result, map DenseProbeMap read_events ++ map DenseProbeSet mem_events ++ [DenseProbeCase]).

(** The event fold charges the actual node and expression encoder bodies. *)
Definition audit_dense_probe_work {N U A B} (weight : B -> nat)
    (events : list (audit_dense_probe_event N U A B)) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  fold_right (fun event n => n + 32 + match event with
    | DenseProbeMap e => audit_map_source_work body [e]
    | DenseProbeSet e => audit_finset_source_work body [e]
    | DenseProbeCase => 0
    end) 0 events.

(** Each query frame is bounded by the original node and expression code widths. *)
Definition audit_dense_probe_budget {N U} (EN : encoding N) (EU : encoding U) (n : N) (u : U) :
    nat :=
  256 + 5 * Pos.size_nat (encode EN n) + 5 * Pos.size_nat (encode EU u).

(** Actual encoder budgets are charged only to the corresponding captured call. *)
Definition audit_dense_probe_event_budget {N U A B} (node_budget : N -> nat)
    (expr_budget : U -> nat)
    (event : audit_dense_probe_event N U A B) : nat :=
  match event with
  | DenseProbeMap (AuditMapGet n _ _ _ _ _) | DenseProbeMap (AuditMapSet n _ _ _ _ _ _) |
    DenseProbeMap (AuditMapRemove n _ _ _ _ _) => node_budget n
  | DenseProbeSet (AuditSetAdd u _ _ _ _ _) | DenseProbeSet (AuditSetMem u _ _ _ _ _) |
    DenseProbeSet (AuditSetRemove u _ _ _ _ _) => expr_budget u
  | _ => 0
  end.

(** The captured probe has the source result and a bound using its actual input codes. *)
Definition audit_dense_probe_source_statement : Prop :=
  forall (N E U B : Type) (EN : encoding N) (EU : encoding U) (universe : list U)
    (cb : audit_seg_build_callbacks N E U B) (weight : B -> nat) (bottom : finite_set EU universe)
    (values : assignment N (finite_set EU universe)) (n : N) (u : U)
    node_source expr_source node_budget expr_budget,
    (forall x, fst (seg_build_node_encode cb x) = encode EN x) ->
    (forall x, fst (seg_build_expr_encode cb x) = encode EU x) ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
    node_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
    expr_budget ->
    let '(out, events) := audit_dense_probe EU universe cb bottom values n u in
    out = fmem EU u (match Map.get EN n values with
    Some value => value
    | None => bottom
    end) /\
      audit_dense_probe_work weight events <= audit_dense_probe_budget EN EU n u +
        fold_right (fun event k => audit_dense_probe_event_budget node_budget expr_budget event + k)
          0 events.

(** A batch preserves query order and uses the same captured assignment at every probe. *)
Fixpoint audit_dense_probe_batch {N E U B} (EU : encoding U) (universe : list U)
    (cb : audit_seg_build_callbacks N E U B) (bottom : finite_set EU universe)
    (values : assignment N (finite_set EU universe)) (queries : list (N * U)) :
    list bool * list (audit_dense_probe_event N U (finite_set EU universe) B) :=
  match queries with
  | [] => ([], [DenseProbeCase])
  | (n, u) :: rest =>
    let '(answer, events) := audit_dense_probe EU universe cb bottom values n u in
    let '(later, tail) := audit_dense_probe_batch EU universe cb bottom values rest in
    (answer :: later, DenseProbeCase :: events ++ tail)
  end.

(** The batch source budget sums original per-query operands, not solver reruns. *)
Definition audit_dense_probe_batch_budget {N U} (EN : encoding N) (EU : encoding U)
    (queries : list (N * U)) : nat :=
  32 * S (length queries) +
    fold_right (fun q n => audit_dense_probe_budget EN EU (fst q) (snd q) + n) 0 queries.

(** Batch outputs and callback work preserve all queries and their order. *)
Definition audit_dense_probe_batch_source_statement : Prop :=
  forall (N E U B : Type) (EN : encoding N) (EU : encoding U) (universe : list U)
    (cb : audit_seg_build_callbacks N E U B) (weight : B -> nat) (bottom : finite_set EU universe)
    (values : assignment N (finite_set EU universe)) (queries : list (N * U))
    node_source expr_source node_budget expr_budget,
    (forall x, fst (seg_build_node_encode cb x) = encode EN x) ->
    (forall x, fst (seg_build_expr_encode cb x) = encode EU x) ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
    node_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
    expr_budget ->
    let '(out, events) := audit_dense_probe_batch EU universe cb bottom values queries in
    out = map (fun q => fmem EU (snd q)
      (match Map.get EN (fst q) values with
      Some value => value
      | None => bottom
      end)) queries /\
      audit_dense_probe_work weight events <= audit_dense_probe_batch_budget EN EU queries +
        fold_right (fun event k => audit_dense_probe_event_budget node_budget expr_budget event + k)
          0 events.
