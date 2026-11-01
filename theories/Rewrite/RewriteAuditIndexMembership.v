(** * RewriteAuditIndexMembership

    This module audits term membership searches using indexed variable and operator buckets.
    For example, a failed first class-root lookup makes the same-class check return false.
    Builds on: RewriteAuditIndexFind and
    RewriteAuditIndexCompare. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexCompare RewriteAuditIndexFind
  RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_encoded_equal {A} (adapter : rw_queue_encoder_adapter A) (a b : A) : bool * nat :=
  let '(p, pw) := rw_queue_encoder_run adapter a in
  let '(q, qw) := rw_queue_encoder_run adapter b in
  let '(answer, trace) := rw_ri_positive_dec_atomic p q in
  (answer, 64 + pw + qw + 64 * audit_work trace).

Definition rw_ri_same_class_atomic {K Sort V} (state : rw_index_state K Sort V) (a b : rw_id) :
    bool * nat :=
  let '(first, ft) := rw_ri_find_atomic state a in
  match first with
  | None => (false, 64 + rw_ri_find_trace_cost ft)
  | Some x =>
    let '(second, st) := rw_ri_find_atomic state b in
    match second with
    | None => (false, 64 + rw_ri_find_trace_cost ft + rw_ri_find_trace_cost st)
    | Some y =>
      let '(answer, trace) := audit_positive_eqb x y in
      (answer, 64 + rw_ri_find_trace_cost ft + rw_ri_find_trace_cost st +
        audit_positive_eqb_source_work trace)
    end
  end.

Definition rw_ri_bucket_ids {A E} (encoder : A -> positive * list E) (encoder_work : list E -> nat)
    (key : A) (table : Map.t A (FinSet.t rw_id)) : list rw_id * nat :=
  let '(found, trace) := audit_map_get encoder key table in
  let bucket :=
    match found with
    | Some b => b
    | None => FinSet.empty
    end in
  let '(ids, et) := audit_finset_elements bucket in
  (ids, 64 + audit_map_source_work encoder_work trace + audit_set_elements_work et).

Fixpoint rw_ri_member_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (term : rw_term K Sort V) (root : rw_id) : bool * nat :=
  match term with
  | RWVar ty v =>
    let '(candidates, bucket_work) := rw_ri_bucket_ids (rw_external_encoding_events value)
      rw_external_events_work v (rw_index_variables state) in
    let fix visit (ids : list rw_id) : bool * nat :=
      match ids with
      | nil => (false, 64)
      | id :: rest =>
        let '(found, node_trace) := audit_map_get audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let '(head, head_work) :=
          match found with
          | Some (owner, RWNVar ty' v') =>
            let '(same_sort, sw) := rw_ri_encoded_equal sort ty ty' in
            if same_sort then
              let '(same_value, vw) := rw_ri_encoded_equal value v v' in
              if same_value then
                let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
                (same_class, 64 + sw + vw + cw)
              else (false, 64 + sw + vw)
            else (false, 64 + sw)
          | _ => (false, 64)
          end in
        let '(tail, tail_work) := visit rest in
        (head || tail, 64 + audit_map_source_work audit_basic_encoding_work node_trace +
          head_work + tail_work)
      end in
    let '(answer, work) := visit candidates in (answer, 64 + bucket_work + work)
  | RWApp ty k children =>
    let '(candidates, bucket_work) := rw_ri_bucket_ids (rw_external_encoding_events op)
      rw_external_events_work k (rw_index_operators state) in
    let fix visit (ids : list rw_id) : bool * nat :=
      match ids with
      | nil => (false, 64)
      | id :: rest =>
        let '(found, node_trace) := audit_map_get audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let '(head, head_work) :=
          match found with
          | Some (owner, RWNApp ty' k' child_ids) =>
            let '(same_sort, sw) := rw_ri_encoded_equal sort ty ty' in
            if same_sort then
              let '(same_op, ow) := rw_ri_encoded_equal op k k' in
              if same_op then
                let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
                let fix pairs (terms : list (rw_term K Sort V)) (classes : list rw_id) :
                    bool * nat :=
                  match terms, classes with
                  | nil, nil => (true, 64)
                  | t :: ts, c :: cs =>
                    let '(head, hw) := rw_ri_member_atomic op sort value state t c in
                    let '(tail, tw) := pairs ts cs in (head && tail, 64 + hw + tw)
                  | _, _ => (false, 64)
                  end in
                let '(same_children, child_work) := pairs children child_ids in
                (same_class && same_children, 64 + sw + ow + cw + child_work)
              else (false, 64 + sw + ow)
            else (false, 64 + sw)
          | _ => (false, 64)
          end in
        let '(tail, tail_work) := visit rest in
        (head || tail, 64 + audit_map_source_work audit_basic_encoding_work node_trace +
          head_work + tail_work)
      end in
    let '(answer, work) := visit candidates in
    (answer, 64 + bucket_work + work)
  end.

(** When the three encoders agree and the index is valid, the membership observer
    returns true exactly for terms represented at the supplied root. *)
Definition rw_ri_member_spec_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (sig : rw_signature K Sort V) state term root,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_index_valid EK ES EV sig state ->
    (fst (rw_ri_member_atomic op sort value state term root) = true <->
      rw_represents (rw_index_graph state) root term).
