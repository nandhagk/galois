(** * RewriteAuditQueueRebuild

    This module defines receipt-producing queue rebuilds and their prospective contracts.
    For example, with no pairs the prepend contract requires the same queue and receipt work
    at most 4096.
    Builds on: RewriteAuditQueueIndex and
    RewriteAuditQueueKernel. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueCollections RewriteAuditQueueIndex
  RewriteAuditQueueKernel RewriteAuditQueueReference.
Import List.ListNotations.

Local Notation "'rqlet' x ':=' e 'in' c" :=
  (rw_rq_bind 1020 e (fun x => c))
  (at level 10, x ident, e at level 100, c at level 200).

Definition rw_rq_enqueue_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (base : rw_graph K Sort V)
    (baseix : rw_index K) (vars : Map.t rw_id (list rw_id)) (g : rw_graph K Sort V)
    (ix : rw_index K) (a b : rw_id) (queue : rw_pending_queue) :
    rw_rq_source K Sort V rw_pending_queue :=
  rqlet first := rw_rq_parent_source g ix a in
  rqlet second := rw_rq_parent_source g ix b in
  rqlet parents := rw_rq_source_append first second in
  rqlet pairs := rw_rq_source_flat_map (fun id =>
    rqlet partners := rw_rq_partners_source op sort value base baseix vars id in
    rw_rq_source_map (fun other => rw_rq_return 1068 (id, other)) partners) parents in
  rw_rq_prepend_source pairs queue.

Definition rw_rq_step_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (base : rw_graph K Sort V)
    (baseix : rw_index K) (vars : Map.t rw_id (list rw_id)) (state : rw_queue_state K Sort V) :
    rw_rq_source K Sort V (rw_queue_state K Sort V) :=
  let g := rw_queue_graph state in
  let ix := rw_queue_index state in
  rqlet popped := rw_rq_pop_source (rw_queue_pending state) in
  match popped with
  | None => rw_rq_return 1069 state
  | Some ((n, m), rest) =>
    let dropped := RwQueueState g ix rest in
    rqlet first := rw_rq_node_source g n in
    match first with
    | None => rw_rq_return 1070 dropped
    | Some (a, node) =>
      rqlet second := rw_rq_node_source g m in
      match second with
      | None => rw_rq_return 1071 dropped
      | Some (b, other) =>
        rqlet first_root := rw_rq_find_source g a in
        match first_root with
        | None => rw_rq_return 1072 dropped
        | Some ra =>
          rqlet second_root := rw_rq_find_source g b in
          match second_root with
          | None => rw_rq_return 1073 dropped
          | Some rb =>
            rqlet canonical_a := rw_rq_canon_node_source g node in
            rqlet code_a := rw_rq_node_encode op sort value canonical_a in
            rqlet canonical_b := rw_rq_canon_node_source g other in
            rqlet code_b := rw_rq_node_encode op sort value canonical_b in
            rqlet same_code := rw_rq_decision code_a code_b in
            if same_code then
              rqlet same_root := rw_rq_decision ra rb in
              if same_root then rw_rq_return 1074 dropped
              else
                rqlet united := rw_rq_union_source sort g a b in
                match united with
                | None => rw_rq_return 1075 dropped
                | Some next_graph =>
                  rqlet next_index := rw_rq_index_update_source g next_graph ix a b in
                  rqlet next_queue := rw_rq_enqueue_source op sort value base baseix vars
                    g ix a b rest in
                  rw_rq_return 1076 (RwQueueState next_graph next_index next_queue)
                end
            else rw_rq_return 1077 dropped
          end
        end
      end
    end
  end.

Fixpoint rw_rq_repeat_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (base : rw_graph K Sort V)
    (ix : rw_index K) (vars : Map.t rw_id (list rw_id)) (fuel : positive)
    (state : rw_queue_state K Sort V) : rw_rq_source K Sort V (rw_queue_state K Sort V) :=
  match rw_pending_sequence (rw_queue_pending state) with
  | nil => rw_rq_return 1078 state
  | _ :: _ =>
    match fuel with
    | xH => rw_rq_step_source op sort value base ix vars state
    | xO rest =>
      rqlet middle := rw_rq_repeat_source op sort value base ix vars rest state in
      rw_rq_repeat_source op sort value base ix vars rest middle
    | xI rest =>
      rqlet first := rw_rq_step_source op sort value base ix vars state in
      rqlet middle := rw_rq_repeat_source op sort value base ix vars rest first in
      rw_rq_repeat_source op sort value base ix vars rest middle
    end
  end.

Definition rw_rq_fuel_source {K Sort V} (g : rw_graph K Sort V) (count : nat)
    (queue : rw_pending_queue) : rw_rq_source K Sort V positive :=
  let '(fuel, trace) := rw_rebuild_fuel_atomic g count queue in
  RwRqSource fuel [RQSourceFuel g count queue fuel trace].

Definition rw_rq_rebuild_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (g : rw_graph K Sort V) :
    rw_rq_source K Sort V (rw_graph K Sort V) :=
  rqlet prepared := rw_rq_prepare_source op sort value g in
  let '(ix, vars) := prepared in
  rqlet initial_queue := rw_rq_initial_source op sort value g ix vars in
  let '(queue, count) := initial_queue in
  rqlet fuel := rw_rq_fuel_source g count queue in
  rqlet final := rw_rq_repeat_source op sort value g ix vars fuel (RwQueueState g ix queue) in
  rqlet canonical := rw_rq_final_all_source op (rw_nodes_in (rw_queue_graph final))
    (rw_queue_graph final) (rw_queue_index final) in
  rw_rq_return 1079 (fst canonical).

(** A rebuild source run relates a graph to the value and receipts of its source computation. *)
Inductive rw_rq_rebuild_source_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (g : rw_graph K Sort V) : rw_graph K Sort V -> list (rw_rq_receipt K Sort V) -> Prop :=
  | RQRebuildSourceRun : forall output receipts,
      rw_rq_rebuild_source op sort value g = RwRqSource output receipts ->
      rw_rq_rebuild_source_run op sort value g output receipts.

(** When all three encoder adapters agree, a rebuild source run returns both the
    pending rebuild and the original rebuild result. *)
Definition rw_rq_rebuild_source_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_rq_rebuild_source_run op sort value g output receipts ->
    output = rw_pending_rebuild EK ES EV g /\ output = rw_rebuild EK ES EV g.

(** Every receipt in a rebuild source run is valid for its encoder adapters. *)
Definition rw_rq_rebuild_source_valid_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
    rw_rq_rebuild_source_run op sort value g output receipts ->
    Forall (rw_rq_receipt_valid op sort value) receipts.

(** A rebuild source run has receipt work bounded by the sum of receipt budgets. *)
Definition rw_rq_rebuild_source_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
    rw_rq_rebuild_source_run op sort value g output receipts ->
    rw_rq_receipts_work receipts <= rw_rq_receipts_budget receipts.

(** Source prepend erases to pending prepend and has work bounded by the number of
    offered pairs and their encoded bit lengths. *)
Definition rw_rq_prepend_source_linear_statement : Prop :=
  forall K Sort V pairs queue,
    let source := @rw_rq_prepend_source K Sort V pairs queue in
    rw_rq_value source = rw_pending_prepend pairs queue /\
    rw_rq_receipts_work (rw_rq_receipts source) <=
      4096 * S (length pairs) +
        4096 * fold_right (fun p n => rw_pending_pair_key_bits p + n) 0 pairs.
