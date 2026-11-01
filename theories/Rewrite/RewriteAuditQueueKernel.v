(** * RewriteAuditQueueKernel

    Defines receipt-producing queue primitives and their trace validity and cost models.
    For example, looking up key 1 in an empty trie returns None and one lookup receipt.
    Builds on: RewriteAuditQueuePositive and
    RewriteAuditQueueReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueuePositive RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rq_node_event (K Sort V : Type) :=
  audit_sum_event (Sort * V) (Sort * (K * list rw_id)) (audit_pair_event Sort V nat nat)
    (audit_pair_event Sort (K * list rw_id) nat (audit_pair_event K (list rw_id) nat
    (audit_list_event rw_id (audit_basic_encoding_event positive)))).

Inductive rw_rq_receipt (K Sort V : Type) : Type :=
  | RQSourceBlock : nat -> rw_rq_receipt K Sort V
  | RQSourceGet : forall A, positive -> Trie.t A -> option A -> audit_trace (audit_trie_call A) ->
      rw_rq_receipt K Sort V
  | RQSourceUpdate : forall A, positive -> option A -> Trie.t A -> Trie.t A -> audit_trace
      (audit_trie_call A) -> rw_rq_receipt K Sort V
  | RQSourceOperator : K -> positive -> nat -> rw_rq_receipt K Sort V
  | RQSourceSort : Sort -> positive -> nat -> rw_rq_receipt K Sort V
  | RQSourceVariable : V -> positive -> nat -> rw_rq_receipt K Sort V
  | RQSourcePair : rw_pair -> positive -> list (audit_pair_event positive positive
      (audit_basic_encoding_event positive) (audit_basic_encoding_event positive)) -> rw_rq_receipt
      K Sort V
  | RQSourceNode : rw_node K Sort V -> positive -> list (rw_rq_node_event K Sort V) -> rw_rq_receipt
      K Sort V
  | RQSourceDecision : positive -> positive -> bool -> list rw_rq_decision_frame -> rw_rq_receipt K
      Sort V
  | RQSourceCollapse : rw_id -> rw_id -> Map.t rw_id rw_id -> Map.t rw_id rw_id -> list
      (audit_map_transform_event rw_id rw_id rw_id rw_rq_decision_frame) -> rw_rq_receipt K Sort V
  | RQSourceFuel : rw_graph K Sort V -> nat -> rw_pending_queue -> positive -> audit_trace unit ->
      rw_rq_receipt K Sort V.
Arguments RQSourceBlock {K Sort V}.
Arguments RQSourceGet {K Sort V A}.
Arguments RQSourceUpdate {K Sort V A}.
Arguments RQSourceOperator {K Sort V}.
Arguments RQSourceSort {K Sort V}.
Arguments RQSourceVariable {K Sort V}.
Arguments RQSourcePair {K Sort V}.
Arguments RQSourceNode {K Sort V}.
Arguments RQSourceDecision {K Sort V}.
Arguments RQSourceCollapse {K Sort V}.
Arguments RQSourceFuel {K Sort V}.

Definition rw_rq_receipt_work {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceBlock _ => 64
  | RQSourceGet _ _ _ trace => 64 + audit_trie_get_trace_source_work trace
  | RQSourceUpdate _ _ _ _ trace => 64 + audit_trie_update_trace_source_work trace
  | RQSourceOperator _ _ body => 64 + body
  | RQSourceSort _ _ body => 64 + body
  | RQSourceVariable _ _ body => 64 + body
  | RQSourcePair _ _ trace => 64 +
      audit_pair_events_work audit_basic_encoding_work audit_basic_encoding_work trace
  | RQSourceNode _ _ trace => 64 +
      rw_node_encode_trace_cost rw_external_events_work rw_external_events_work
        rw_external_events_work trace
  | RQSourceDecision _ _ _ trace => 64 + 64 * length trace
  | RQSourceCollapse _ _ _ _ trace => 64 +
      audit_map_transform_source_work (fun bits => 64 * length bits) trace
  | RQSourceFuel _ _ _ _ trace => 64 + 64 * audit_work trace
  end.

Definition rw_rq_receipts_work {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : nat :=
  fold_right (fun receipt total => rw_rq_receipt_work receipt + total) 0 receipts.

Record rw_rq_source (K Sort V A : Type) := RwRqSource {
  rw_rq_value : A;
  rw_rq_receipts : list (rw_rq_receipt K Sort V)
}.
Arguments RwRqSource {K Sort V A}.
Arguments rw_rq_value {K Sort V A}.
Arguments rw_rq_receipts {K Sort V A}.

Definition rw_rq_return {K Sort V A} (site : nat) (value : A) : rw_rq_source K Sort V A :=
  RwRqSource value [RQSourceBlock site].

Definition rw_rq_bind {K Sort V A B} (site : nat) (first : rw_rq_source K Sort V A) (next : A ->
    rw_rq_source K Sort V B) : rw_rq_source K Sort V B :=
  let later := next (rw_rq_value first) in
  RwRqSource (rw_rq_value later)
    (rw_rq_receipts first ++ RQSourceBlock site :: rw_rq_receipts later).

Definition rw_rq_code_get {K Sort V A} (code : positive) (before : Trie.t A) : rw_rq_source K Sort V
    (option A) :=
  let '(out, trace) := audit_trie_get code before in
  RwRqSource out [RQSourceGet code before out trace].

Definition rw_rq_map_code_get {K Sort V A B} (code : positive) (before : Map.t A B) : rw_rq_source K
    Sort V (option B) :=
  rw_rq_bind 1000 (rw_rq_code_get code before)
    (fun stored => rw_rq_return 1001 (option_map snd stored)).

Definition rw_rq_code_set {K Sort V A} (code : positive) (value : A) (before : Trie.t A) :
    rw_rq_source K Sort V (Trie.t A) :=
  let '(out, trace) := audit_trie_set code value before in
  RwRqSource out [RQSourceUpdate code (Some value) before out trace].

Definition rw_rq_code_remove {K Sort V A} (code : positive) (before : Trie.t A) : rw_rq_source K
    Sort V (Trie.t A) :=
  let '(out, trace) := audit_trie_remove code before in
  RwRqSource out [RQSourceUpdate code None before out trace].

Definition rw_rq_operator_encode {K Sort V} (adapter : rw_queue_encoder_adapter K) (x : K) :
    rw_rq_source K Sort V positive :=
  let '(code, body) := rw_queue_encoder_run adapter x in
  RwRqSource code [RQSourceOperator x code body].

Definition rw_rq_sort_encode {K Sort V} (adapter : rw_queue_encoder_adapter Sort) (x : Sort) :
    rw_rq_source K Sort V positive :=
  let '(code, body) := rw_queue_encoder_run adapter x in
  RwRqSource code [RQSourceSort x code body].

Definition rw_rq_variable_encode {K Sort V} (adapter : rw_queue_encoder_adapter V) (x : V) :
    rw_rq_source K Sort V positive :=
  let '(code, body) := rw_queue_encoder_run adapter x in
  RwRqSource code [RQSourceVariable x code body].

Definition rw_rq_pair_encode {K Sort V} (pair_value : rw_pair) : rw_rq_source K Sort V positive :=
  let '(code, trace) := audit_pair_encode audit_positive_encode audit_positive_encode pair_value in
  RwRqSource code [RQSourcePair pair_value code trace].

Definition rw_rq_node_encode {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (node : rw_node K Sort V) :
    rw_rq_source K Sort V positive :=
  let '(code, trace) := rw_node_encode_atomic (rw_external_encoding_events op)
    (rw_external_encoding_events sort) (rw_external_encoding_events value) node in
  RwRqSource code [RQSourceNode node code trace].

Definition rw_rq_decision {K Sort V} (a b : positive) : rw_rq_source K Sort V bool :=
  let '(answer, trace) := rw_rq_decision_atomic a b in
  RwRqSource answer [RQSourceDecision a b answer trace].

Definition rw_rq_collapse_source_child (from into root : rw_id) :
    rw_id * list rw_rq_decision_frame :=
  let '(same, trace) := rw_rq_decision_atomic root from in
  ((if same then into else root), trace).

Definition rw_rq_collapse_source {K Sort V} (from into : rw_id) (before : Map.t rw_id rw_id) :
    rw_rq_source K Sort V (Map.t rw_id rw_id) :=
  let '(out, trace) := audit_map_transform (rw_rq_collapse_source_child from into) before in
  RwRqSource out [RQSourceCollapse from into before out trace].

Fixpoint rw_rq_source_append {K Sort V A} (xs ys : list A) : rw_rq_source K Sort V (list A) :=
  match xs with
  | nil => rw_rq_return 1002 ys
  | x :: rest => rw_rq_bind 1003 (rw_rq_source_append rest ys)
      (fun tail => rw_rq_return 1004 (x :: tail))
  end.

Fixpoint rw_rq_source_fold_right {K Sort V A B} (f : A -> B -> rw_rq_source K Sort V B)
    (xs : list A) (initial : B) : rw_rq_source K Sort V B :=
  match xs with
  | nil => rw_rq_return 1005 initial
  | x :: rest => rw_rq_bind 1006 (rw_rq_source_fold_right f rest initial) (f x)
  end.

Fixpoint rw_rq_source_map {K Sort V A B} (f : A -> rw_rq_source K Sort V B) (xs : list A) :
    rw_rq_source K Sort V (list B) :=
  match xs with
  | nil => rw_rq_return 1007 nil
  | x :: rest => rw_rq_bind 1008 (f x) (fun head =>
      rw_rq_bind 1009 (rw_rq_source_map f rest) (fun tail => rw_rq_return 1010 (head :: tail)))
  end.

Fixpoint rw_rq_source_flat_map {K Sort V A B} (f : A -> rw_rq_source K Sort V (list B))
    (xs : list A) : rw_rq_source K Sort V (list B) :=
  match xs with
  | nil => rw_rq_return 1011 nil
  | x :: rest => rw_rq_bind 1012 (f x) (fun head =>
      rw_rq_bind 1013 (rw_rq_source_flat_map f rest) (fun tail => rw_rq_source_append head tail))
  end.

(** A source trie lookup returns the plain lookup and one receipt containing its audit trace. *)
Definition rw_rq_get_receipt_statement : Prop :=
  forall K Sort V A code (before : Trie.t A),
    let run := @rw_rq_code_get K Sort V A code before in
    rw_rq_value run = Trie.get code before /\
    exists trace, rw_rq_receipts run = [RQSourceGet code before (rw_rq_value run) trace] /\
      audit_trie_get code before = (rw_rq_value run, trace).

Fixpoint rw_rq_pair_external {A B EA EB} (first : list EA -> nat) (second : list EB -> nat)
    (trace : list (audit_pair_event A B EA EB)) : nat :=
  match trace with
  | nil => 0
  | AuditPairFirst _ _ child :: rest => first child + rw_rq_pair_external first second rest
  | AuditPairSecond _ _ child :: rest => second child + rw_rq_pair_external first second rest
  | AuditPairFrame _ :: rest => rw_rq_pair_external first second rest
  end.

Definition rw_rq_node_external {K Sort V} (trace : list (rw_rq_node_event K Sort V)) : nat :=
  fold_right (fun event total =>
    match event with
    | AuditSumLeft _ _ child =>
      rw_rq_pair_external rw_external_events_work rw_external_events_work child + total
    | AuditSumRight _ _ child =>
      rw_rq_pair_external rw_external_events_work
        (rw_rq_pair_external rw_external_events_work (fun _ => 0)) child + total
    end) 0 trace.

Definition rw_rq_receipt_budget {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceBlock _ => 128
  | RQSourceGet code _ _ _ => 256 + 512 * Pos.size_nat code
  | RQSourceUpdate code _ _ _ _ => 256 + 512 * Pos.size_nat code
  | RQSourceOperator _ _ body => 256 + body
  | RQSourceSort _ _ body => 256 + body
  | RQSourceVariable _ _ body => 256 + body
  | RQSourcePair pair_value _ _ =>
    1024 + 1024 * (Pos.size_nat (fst pair_value) + Pos.size_nat (snd pair_value))
  | RQSourceNode _ code trace =>
    2048 + 2048 * Pos.size_nat code + rw_rq_node_external trace
  | RQSourceDecision a b _ _ => 1024 + 512 * (Pos.size_nat a + Pos.size_nat b)
  | RQSourceCollapse from _ before _ trace =>
    1024 + 1024 * audit_trie_nodes before +
      fold_right (fun event total =>
        match event with
        | AuditMapTransformCall _ input _ _ =>
          1024 + 512 * (Pos.size_nat input + Pos.size_nat from) + total
        | _ => total
        end) 0 trace
  | RQSourceFuel graph count queue _ _ =>
    256 + 256 * rw_rebuild_fuel_work (length (rw_roots graph)) count
      (length (rw_pending_sequence queue))
  end.

Definition rw_rq_receipts_budget {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : nat :=
  fold_right (fun receipt total => rw_rq_receipt_budget receipt + total) 0 receipts.

(** Every block-site receipt is valid; other receipts are valid when their recorded
    result and trace match the corresponding source primitive or encoder invocation. *)
Inductive rw_rq_receipt_valid {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) :
    rw_rq_receipt K Sort V -> Prop :=
  | RQValidBlock : forall site, rw_rq_receipt_valid op sort value (RQSourceBlock site)
  | RQValidGet : forall A code (before : Trie.t A) out trace,
      audit_trie_get code before = (out, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceGet code before out trace)
  | RQValidUpdate : forall A code item (before after : Trie.t A) trace,
      audit_trie_update code item before = (after, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceUpdate code item before after trace)
  | RQValidOperator : forall input code body, rw_queue_encoder_run op input = (code, body) ->
      rw_rq_receipt_valid op sort value (RQSourceOperator input code body)
  | RQValidSort : forall input code body, rw_queue_encoder_run sort input = (code, body) ->
      rw_rq_receipt_valid op sort value (RQSourceSort input code body)
  | RQValidVariable : forall input code body, rw_queue_encoder_run value input = (code, body) ->
      rw_rq_receipt_valid op sort value (RQSourceVariable input code body)
  | RQValidPair : forall input code trace,
      audit_pair_encode audit_positive_encode audit_positive_encode input = (code, trace) ->
      rw_rq_receipt_valid op sort value (RQSourcePair input code trace)
  | RQValidNode : forall input code trace,
      rw_node_encode_atomic (rw_external_encoding_events op) (rw_external_encoding_events sort)
        (rw_external_encoding_events value) input = (code, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceNode input code trace)
  | RQValidDecision : forall a b answer trace, rw_rq_decision_atomic a b = (answer, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceDecision a b answer trace)
  | RQValidCollapse : forall from into before after trace,
      audit_map_transform (rw_rq_collapse_source_child from into) before = (after, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceCollapse from into before after trace)
  | RQValidFuel : forall graph count queue fuel trace,
      rw_rebuild_fuel_atomic graph count queue = (fuel, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceFuel graph count queue fuel trace).

(** A valid receipt has work at most its own operand-dependent budget. *)
Definition rw_rq_receipt_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) receipt, rw_rq_receipt_valid op sort value receipt ->
    rw_rq_receipt_work receipt <= rw_rq_receipt_budget receipt.

(** A list of valid receipts has work at most the sum of their budgets. *)
Definition rw_rq_receipts_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) receipts,
    Forall (rw_rq_receipt_valid op sort value) receipts ->
    rw_rq_receipts_work receipts <= rw_rq_receipts_budget receipts.
