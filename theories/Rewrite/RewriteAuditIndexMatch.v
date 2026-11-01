(** * RewriteAuditIndexMatch

    This module audits indexed pattern matching and the collection of distinct assignments.
    For example, matching zero child patterns against zero child identifiers keeps the assignment.
    Builds on: RewriteAuditIndexMatchReference and
    RewriteAuditIndexMembership. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexCompare RewriteAuditIndexFind
  RewriteAuditIndexMatchReference RewriteAuditIndexMembership RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_ri_match_append {A} (xs ys : list A) : list A * nat :=
  match xs with
  | nil => (ys, 64)
  | x :: rest =>
    let '(tail, work) := rw_ri_match_append rest ys in
    (x :: tail, 64 + work)
  end.

Definition rw_ri_bind_atomic {H} (hole : rw_queue_encoder_adapter H) (h : H) (root : rw_id)
    (assignment : rw_assignment H) : list (rw_assignment H) * nat :=
  let '(found, lookup) := audit_map_get (rw_external_encoding_events hole) h assignment in
  match found with
  | Some old =>
    let '(same, trace) := rw_ri_positive_dec_atomic old root in
    ((if same then [assignment] else nil),
      64 + audit_map_source_work rw_external_events_work lookup + 64 * audit_work trace)
  | None =>
    let '(updated, trace) := audit_map_set (rw_external_encoding_events hole) h root assignment in
    ([updated], 64 + audit_map_source_work rw_external_events_work lookup +
      audit_map_source_work rw_external_events_work trace)
  end.

Fixpoint rw_ri_match_flat_map {A B} (body : A -> list B * nat) (xs : list A) : list B * nat :=
  match xs with
  | nil => (nil, 64)
  | x :: rest =>
    let '(head, hw) := body x in
    let '(tail, tw) := rw_ri_match_flat_map body rest in
    let '(out, aw) := rw_ri_match_append head tail in
    (out, 64 + hw + tw + aw)
  end.

Fixpoint rw_ri_match_children_atomic {H} (functions : list (rw_id -> rw_assignment H -> list
    (rw_assignment H) * nat)) (ids : list rw_id) (assignment : rw_assignment H) : list
    (rw_assignment H) * nat :=
  match functions, ids with
  | nil, nil => ([assignment], 64)
  | f :: rest, id :: children =>
    let '(heads, hw) := f id assignment in
    let '(out, tw) := rw_ri_match_flat_map
      (rw_ri_match_children_atomic rest children) heads in
    (out, 64 + hw + tw)
  | _, _ => (nil, 64)
  end.

Definition rw_ri_match_candidates_atomic {K Sort V H} (op : rw_queue_encoder_adapter K) (hole :
    rw_queue_encoder_adapter H) (state : rw_index_state K Sort V) (key : K) (patterns : list
    (rw_pattern K Sort V H)) (assignment : rw_assignment H) : list rw_id * nat :=
  match patterns with
  | RWHole _ h :: _ =>
    let '(found, lookup) := audit_map_get (rw_external_encoding_events hole) h assignment in
    let prefix := 64 + audit_map_source_work rw_external_events_work lookup in
    match found with
    | None =>
      let '(out, work) := rw_ri_bucket_ids (rw_external_encoding_events op)
        rw_external_events_work key (rw_index_operators state) in
      (out, prefix + work)
    | Some id =>
      let '(root, trace) := rw_ri_find_atomic state id in
      match root with
      | None => (nil, prefix + rw_ri_find_trace_cost trace)
      | Some root =>
        let '(out, work) := rw_ri_bucket_ids audit_positive_encode audit_basic_encoding_work
          root (rw_index_parent_buckets state) in
        (out, prefix + rw_ri_find_trace_cost trace + work)
      end
    end
  | _ => rw_ri_bucket_ids (rw_external_encoding_events op)
      rw_external_events_work key (rw_index_operators state)
  end.

Fixpoint rw_ri_match_on_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (state : rw_index_state K Sort V)
    (pattern : rw_pattern K Sort V H)
    (root : rw_id) (assignment : rw_assignment H) {struct pattern} : list (rw_assignment H) * nat :=
  match pattern with
  | RWHole ty h =>
    let '(found, trace) := rw_ri_find_atomic state root in
    match found with
    | None => (nil, 64 + rw_ri_find_trace_cost trace)
    | Some canonical =>
      let '(declared, lookup) := audit_map_get audit_positive_encode root
        (rw_sorts (rw_index_base state)) in
      let prefix := 64 + rw_ri_find_trace_cost trace +
        audit_map_source_work audit_basic_encoding_work lookup in
      match declared with
      | None => (nil, prefix)
      | Some declared =>
        let '(same, work) := rw_ri_encoded_equal sort ty declared in
        if same then
          let '(out, binding_work) := rw_ri_bind_atomic hole h canonical assignment in
          (out, prefix + work + binding_work)
        else (nil, prefix + work)
      end
    end
  | RWPVar ty v =>
    let '(candidates, bucket_work) := rw_ri_bucket_ids (rw_external_encoding_events value)
      rw_external_events_work v (rw_index_variables state) in
    let '(out, work) := rw_ri_match_flat_map (fun id =>
      let '(found, trace) := audit_map_get audit_positive_encode id
        (rw_nodes (rw_index_base state)) in
      let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
      match found with
      | Some (owner, RWNVar declared w) =>
        let '(same_sort, sw) := rw_ri_encoded_equal sort ty declared in
        if same_sort then
          let '(same_value, vw) := rw_ri_encoded_equal value v w in
          if same_value then
            let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
            ((if same_class then [assignment] else nil), prefix + sw + vw + cw)
          else (nil, prefix + sw + vw)
        else (nil, prefix + sw)
      | _ => (nil, prefix)
      end) candidates in
    (out, 64 + bucket_work + work)
  | RWPApp ty key patterns =>
    let '(candidates, bucket_work) :=
      rw_ri_match_candidates_atomic op hole state key patterns assignment in
    let '(out, work) := rw_ri_match_flat_map (fun id =>
      let '(found, trace) := audit_map_get audit_positive_encode id
        (rw_nodes (rw_index_base state)) in
      let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
      match found with
      | Some (owner, RWNApp declared other children) =>
        let '(same_sort, sw) := rw_ri_encoded_equal sort ty declared in
        if same_sort then
          let '(same_op, ow) := rw_ri_encoded_equal op key other in
          if same_op then
            let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
            if same_class then
              let functions := map (rw_ri_match_on_atomic op sort value hole state) patterns in
              let '(out, mw) := rw_ri_match_children_atomic functions children assignment in
              (out, prefix + sw + ow + cw + 64 * S (length patterns) + mw)
            else (nil, prefix + sw + ow + cw)
          else (nil, prefix + sw + ow)
        else (nil, prefix + sw)
      | _ => (nil, prefix)
      end) candidates in
    (out, 64 + bucket_work + work)
  end.

Definition rw_ri_assignment_encode {H} (hole : rw_queue_encoder_adapter H)
    (entries : list (H * rw_id)) :=
  audit_list_encode (audit_pair_encode (rw_external_encoding_events hole) audit_positive_encode)
    entries.

Definition rw_ri_assignment_encode_work {H} (events : list (audit_list_event (H * rw_id)
    (audit_pair_event H rw_id nat (audit_basic_encoding_event positive)))) : nat :=
  audit_list_events_work (audit_pair_events_work rw_external_events_work audit_basic_encoding_work)
    events.

Fixpoint rw_ri_assignment_table_atomic {H} (hole : rw_queue_encoder_adapter H)
    (results : list (rw_assignment H)) : Map.t (list (H * rw_id)) (rw_assignment H) * nat :=
  match results with
  | nil => (Map.empty, 64)
  | assignment :: rest =>
    let '(table, tail_work) := rw_ri_assignment_table_atomic hole rest in
    let '(entries, enumeration) := audit_map_elements assignment in
    let '(out, insertion) := audit_map_set (rw_ri_assignment_encode hole) entries assignment
      table in
    (out, 64 + tail_work + audit_elements_work enumeration +
      audit_map_source_work rw_ri_assignment_encode_work insertion)
  end.

Definition rw_ri_distinct_assignments_atomic {H} (hole : rw_queue_encoder_adapter H)
    (results : list (rw_assignment H)) : list (rw_assignment H) * nat :=
  let '(table, table_work) := rw_ri_assignment_table_atomic hole results in
  let '(entries, enumeration) := audit_map_elements table in
  (map snd entries, 64 + table_work + audit_elements_work enumeration + 64 * S (length entries)).

Definition rw_ri_match_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (state : rw_index_state K Sort V) (root : rw_id)
    (pattern : rw_pattern K Sort V H) : list (rw_assignment H) * nat :=
  let '(raw, match_work) := rw_ri_match_on_atomic op sort value hole state pattern root Map.empty in
  let '(out, distinct_work) := rw_ri_distinct_assignments_atomic hole raw in
  (out, 64 + match_work + distinct_work).

(** When all four encoder adapters agree, erasing matcher work yields matching on
    the index snapshot. *)
Definition rw_ri_match_erases_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H) state root pattern,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    fst (rw_ri_match_atomic op sort value hole state root pattern) = rw_view_match EK ES EV EH
      (rw_snapshot_base (rw_index_view EK ES EV state)) root pattern.
