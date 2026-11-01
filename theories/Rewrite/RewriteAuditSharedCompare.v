(** * RewriteAuditSharedCompare

    Defines memoized comparison of shared nodes and its work relation.
    For example, a memo hit at pair (1, 1) with result Eq returns Eq and leaves the memo unchanged.
    Builds on: RewriteAuditQueueReference and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rd_memo :=
  Map.t (positive * positive) comparison.

Definition rw_rd_pair_encode :=
  audit_pair_encode audit_positive_encode audit_positive_encode.

Definition rw_rd_pair_encoding_work (trace : list (audit_pair_event positive positive
    (audit_basic_encoding_event positive) (audit_basic_encoding_event positive))) : nat :=
  audit_pair_events_work audit_basic_encoding_work audit_basic_encoding_work trace.

Definition rw_rd_memo_get (p q : positive) (memo : rw_rd_memo) : option comparison * nat :=
  let '(answer, trace) := audit_map_get rw_rd_pair_encode (p, q) memo in
  (answer, 64 + audit_map_source_work rw_rd_pair_encoding_work trace).

Definition rw_rd_memo_set (p q : positive) (answer : comparison) (memo : rw_rd_memo) :
    rw_rd_memo * nat :=
  let '(out, trace) := audit_map_set rw_rd_pair_encode (p, q) answer memo in
  (out, 64 + audit_map_source_work rw_rd_pair_encoding_work trace).

Definition rw_rd_node_get {K Sort V} (nodes : Map.t positive (rw_shared_node K Sort V))
    (id : positive) : option (rw_shared_node K Sort V) * nat :=
  let '(out, trace) := audit_map_get audit_positive_encode id nodes in
  (out, 64 + audit_map_source_work audit_basic_encoding_work trace).

Fixpoint rw_rd_positive_compare_cont (otherwise : comparison) (p q : positive) : comparison * nat :=
  match p, q with
  | xH, xH => (otherwise, 64)
  | xH, xO _ => (Lt, 64)
  | xH, xI _ => (Lt, 64)
  | xO _, xH => (Gt, 64)
  | xI _, xH => (Gt, 64)
  | xO a, xO b =>
    let '(answer, work) := rw_rd_positive_compare_cont otherwise a b in
    (answer, 64 + work)
  | xI a, xI b =>
    let '(answer, work) := rw_rd_positive_compare_cont otherwise a b in
    (answer, 64 + work)
  | xO a, xI b =>
    let '(answer, work) := rw_rd_positive_compare_cont Lt a b in
    (answer, 64 + work)
  | xI a, xO b =>
    let '(answer, work) := rw_rd_positive_compare_cont Gt a b in
    (answer, 64 + work)
  end.

Fixpoint rw_rd_headers_compare (xs ys : list positive) : comparison * nat :=
  match xs, ys with
  | nil, nil => (Eq, 64)
  | nil, _ :: _ => (Lt, 64)
  | _ :: _, nil => (Gt, 64)
  | x :: rest, y :: tail =>
    let '(head, head_work) := rw_rd_positive_compare_cont Eq x y in
    match head with
    | Eq =>
      let '(answer, tail_work) := rw_rd_headers_compare rest tail in
      (answer, 64 + head_work + tail_work)
    | _ => (head, 64 + head_work)
    end
  end.

Definition rw_rd_children {K Sort V} (node : rw_shared_node K Sort V) : list positive :=
  match node with
  | RWSharedVar _ _ _ _ _ => nil
  | RWSharedApp _ _ _ _ _ children => children
  end.

Definition rw_rd_header {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node : rw_shared_node K Sort V) : list positive * nat :=
  match node with
  | RWSharedVar _ _ _ ty v =>
    let '(s, sw) := rw_queue_encoder_run sort ty in
    let '(x, xw) := rw_queue_encoder_run value v in
    ([1%positive; s; x; 1%positive], 64 + sw + xw)
  | RWSharedApp _ _ _ ty k children =>
    let '(s, sw) := rw_queue_encoder_run sort ty in
    let '(x, xw) := rw_queue_encoder_run op k in
    let '(arity, length_trace) := rw_fuel_length children in
    let '(code, code_trace) := audit_nat_encode arity in
    ([2%positive; s; x; code],
      64 + sw + xw + audit_work length_trace + audit_nat_events_work code_trace)
  end.

(** Memoized comparison relates two identifiers and an input memo to a comparison,
    output memo, and source work; a memo hit does not require stored root entries. *)
Inductive rw_rd_compare_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (left right : Map.t positive (rw_shared_node K Sort V)) :
    positive -> positive -> rw_rd_memo -> comparison -> rw_rd_memo -> nat -> Prop :=
  | RDRootCached : forall p q memo answer read_work,
      rw_rd_memo_get p q memo = (Some answer, read_work) ->
      rw_rd_compare_run op sort value left right p q memo answer memo (64 + read_work)
  | RDRootDifferent : forall p q memo a b header_a header_b answer read_work left_work right_work
      a_work b_work comparison_work memo' write_work,
      rw_rd_memo_get p q memo = (None, read_work) ->
      rw_rd_node_get left p = (Some a, left_work) ->
      rw_rd_node_get right q = (Some b, right_work) ->
      rw_rd_header op sort value a = (header_a, a_work) ->
      rw_rd_header op sort value b = (header_b, b_work) ->
      rw_rd_headers_compare header_a header_b = (answer, comparison_work) ->
      answer <> Eq ->
      rw_rd_memo_set p q answer memo = (memo', write_work) ->
      rw_rd_compare_run op sort value left right p q memo answer memo'
        (64 + read_work + left_work + right_work + a_work + b_work + comparison_work + write_work)
  | RDRootChildren : forall p q memo a b header_a header_b answer read_work left_work right_work
      a_work b_work comparison_work child_work child_memo memo' write_work,
      rw_rd_memo_get p q memo = (None, read_work) ->
      rw_rd_node_get left p = (Some a, left_work) ->
      rw_rd_node_get right q = (Some b, right_work) ->
      rw_rd_header op sort value a = (header_a, a_work) ->
      rw_rd_header op sort value b = (header_b, b_work) ->
      rw_rd_headers_compare header_a header_b = (Eq, comparison_work) ->
      rw_rd_compare_children_run op sort value left right (rw_rd_children a) (rw_rd_children b)
        memo answer child_memo child_work ->
      rw_rd_memo_set p q answer child_memo = (memo', write_work) ->
      rw_rd_compare_run op sort value left right p q memo answer memo'
        (64 + read_work + left_work + right_work + a_work + b_work + comparison_work + child_work +
          write_work)
(** Child-list comparison relates two lists and an input memo to their comparison,
    output memo, and source work. *)
with rw_rd_compare_children_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (left right : Map.t positive (rw_shared_node K Sort V)) :
    list positive -> list positive -> rw_rd_memo -> comparison -> rw_rd_memo -> nat -> Prop :=
  | RDChildrenEmpty : forall memo,
      rw_rd_compare_children_run op sort value left right nil nil memo Eq memo 64
  | RDChildrenLeftEmpty : forall y ys memo,
      rw_rd_compare_children_run op sort value left right nil (y :: ys) memo Lt memo 64
  | RDChildrenRightEmpty : forall x xs memo,
      rw_rd_compare_children_run op sort value left right (x :: xs) nil memo Gt memo 64
  | RDChildrenDifferent : forall x xs y ys memo answer next child_work,
      rw_rd_compare_run op sort value left right x y memo answer next child_work ->
      answer <> Eq ->
      rw_rd_compare_children_run op sort value left right (x :: xs) (y :: ys) memo answer next
        (64 + child_work)
  | RDChildrenEqual : forall x xs y ys memo middle final answer child_work tail_work,
      rw_rd_compare_run op sort value left right x y memo Eq middle child_work ->
      rw_rd_compare_children_run op sort value left right xs ys middle answer final tail_work ->
      rw_rd_compare_children_run op sort value left right (x :: xs) (y :: ys) memo answer final
        (64 + child_work + tail_work).

(** Shared comparison relates two trees to a boolean comparison or validation failure
    and its source work. *)
Inductive rw_shared_compare_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (left right : rw_shared_tree K Sort V) : option bool -> nat -> Prop :=
  | RDCompareInvalid : forall lvalid rvalid lt rt,
      rw_shared_validate_atomic left = (lvalid, lt) ->
      rw_shared_validate_atomic right = (rvalid, rt) ->
      lvalid && rvalid = false ->
      rw_shared_compare_run op sort value left right None
        (64 + rw_shared_validation_trace_cost lt + rw_shared_validation_trace_cost rt)
  | RDCompareValid : forall lt rt memo answer work,
      rw_shared_validate_atomic left = (true, lt) ->
      rw_shared_validate_atomic right = (true, rt) ->
      rw_rd_compare_run op sort value (rw_shared_nodes K Sort V left)
        (rw_shared_nodes K Sort V right) (rw_shared_root K Sort V left)
        (rw_shared_root K Sort V right) Map.empty answer memo work ->
      rw_shared_compare_run op sort value left right
        (Some (match answer with
        | Gt => false
        | _ => true
        end))
        (64 + rw_shared_validation_trace_cost lt + rw_shared_validation_trace_cost rt + work).

(** Shared comparison has a result and work observation for every pair of inputs. *)
Definition rw_rd_compare_total_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) left right,
    exists answer work, rw_shared_compare_run op sort value left right answer work.

(** Two shared comparison runs on the same inputs have equal results and work. *)
Definition rw_rd_compare_unique_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) left right first second first_work second_work,
    rw_shared_compare_run op sort value left right first first_work ->
    rw_shared_compare_run op sort value left right second second_work ->
    first = second /\ first_work = second_work.
