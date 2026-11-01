(** * RewriteAuditQueueContracts

    Defines external-execution conditions for queue receipts and prospective rebuild bounds.
    For example, block-site receipt 0 imposes no external encoder execution witness.
    Builds on: RewriteAuditQueueKernel and
    RewriteAuditQueueRebuild. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueKernel RewriteAuditQueueRebuild
  RewriteAuditQueueReference.
Import List.ListNotations.

(** An external encoder event contains one body charge and an execution witness for it. *)
Definition rw_rq_external_body {A} (execution : A -> positive -> nat -> Prop) (input : A)
    (code : positive) (events : list nat) : Prop :=
  exists body, events = [body] /\ execution input code body.

(** Each variable-pair sort or value encoding event has its external execution witness. *)
Definition rw_rq_variable_pair_external {Sort V} (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop)
    (trace : list (audit_pair_event Sort V nat nat)) :
    Prop :=
  Forall (fun event =>
    match event with
    | AuditPairFirst input code events => rw_rq_external_body sort_execution input code events
    | AuditPairSecond input code events => rw_rq_external_body value_execution input code events
    | AuditPairFrame _ => True
    end) trace.

(** Each operator encoding event in an operator pair has its external execution witness. *)
Definition rw_rq_operator_pair_external {K} (op_execution : K -> positive -> nat -> Prop)
    (trace : list (audit_pair_event K (list rw_id) nat
      (audit_list_event rw_id (audit_basic_encoding_event positive)))) : Prop :=
  Forall (fun event =>
    match event with
    | AuditPairFirst input code events => rw_rq_external_body op_execution input code events
    | _ => True
    end) trace.

(** Each application-pair sort or nested operator encoding has its external execution witness. *)
Definition rw_rq_application_pair_external {K Sort} (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (trace : list (audit_pair_event Sort (K * list rw_id) nat
      (audit_pair_event K (list rw_id) nat (audit_list_event rw_id
        (audit_basic_encoding_event positive))))) : Prop :=
  Forall (fun event =>
    match event with
    | AuditPairFirst input code events => rw_rq_external_body sort_execution input code events
    | AuditPairSecond _ _ events => rw_rq_operator_pair_external op_execution events
    | AuditPairFrame _ => True
    end) trace.

(** Every variable or application encoding within a node trace has its execution witness. *)
Definition rw_rq_node_external_execution {K Sort V} (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop) (value_execution : V -> positive -> nat ->
    Prop) (trace : list (rw_rq_node_event K Sort V)) : Prop :=
  Forall (fun event =>
    match event with
    | AuditSumLeft _ _ events =>
      rw_rq_variable_pair_external sort_execution value_execution events
    | AuditSumRight _ _ events =>
      rw_rq_application_pair_external op_execution sort_execution events
    end) trace.

(** An external encoding receipt, including nested node encodings, has its execution witness. *)
Definition rw_rq_receipt_external_execution {K Sort V} (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop) (value_execution : V -> positive -> nat ->
    Prop) (receipt : rw_rq_receipt K Sort V) : Prop :=
  match receipt with
  | RQSourceOperator input code body => op_execution input code body
  | RQSourceSort input code body => sort_execution input code body
  | RQSourceVariable input code body => value_execution input code body
  | RQSourceNode _ _ events =>
    rw_rq_node_external_execution op_execution sort_execution value_execution events
  | _ => True
  end.

(** With encoder adapter laws, external-encoding receipts and nested node encodings in a
    rebuild source run retain their corresponding execution witnesses. *)
Definition rw_rq_rebuild_source_external_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop)
    g output receipts,
    rw_queue_encoder_adapter_laws EK op_execution op ->
    rw_queue_encoder_adapter_laws ES sort_execution sort ->
    rw_queue_encoder_adapter_laws EV value_execution value ->
    rw_rq_rebuild_source_run op sort value g output receipts ->
    Forall (rw_rq_receipt_external_execution op_execution sort_execution value_execution) receipts.

(** With encoder adapter laws, the rebuild source satisfies its run relation, erases
    to both rebuilds, has valid receipts and witnesses for applicable external encodings,
    and meets the composed receipt budget. *)
Definition rw_rq_rebuild_source_complete_contract_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop)
    g,
    rw_queue_encoder_adapter_laws EK op_execution op ->
    rw_queue_encoder_adapter_laws ES sort_execution sort ->
    rw_queue_encoder_adapter_laws EV value_execution value ->
    let run := rw_rq_rebuild_source op sort value g in
    rw_rq_rebuild_source_run op sort value g (rw_rq_value run) (rw_rq_receipts run) /\
    rw_rq_value run = rw_pending_rebuild EK ES EV g /\
    rw_rq_value run = rw_rebuild EK ES EV g /\
    Forall (rw_rq_receipt_valid op sort value) (rw_rq_receipts run) /\
    Forall (rw_rq_receipt_external_execution op_execution sort_execution value_execution)
      (rw_rq_receipts run) /\
    rw_rq_receipts_work (rw_rq_receipts run) <= rw_rq_receipts_budget (rw_rq_receipts run).

Definition rw_rq_input_structure {K Sort V} (g : rw_graph K Sort V) : nat :=
  S (length (rw_roots g) + length (rw_nodes_in g) +
    audit_trie_nodes (rw_class_roots g) + audit_trie_nodes (rw_sorts g) +
    audit_trie_nodes (rw_nodes g) +
    fold_right (fun id total =>
      match rw_node_at g id with
      | Some (_, RWNApp _ _ children) => length children + total
      | _ => total
      end) 0 (rw_nodes_in g)).

Definition rw_rq_receipt_foreign_work {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceOperator _ _ body => body
  | RQSourceSort _ _ body => body
  | RQSourceVariable _ _ body => body
  | RQSourceNode _ _ events => rw_rq_node_external events
  | _ => 0
  end.

Definition rw_rq_receipt_dimension {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceGet code before _ _ => S (Pos.size_nat code + audit_trie_nodes before)
  | RQSourceUpdate code _ before after _ =>
    S (Pos.size_nat code + audit_trie_nodes before + audit_trie_nodes after)
  | RQSourceOperator _ code _ => S (Pos.size_nat code)
  | RQSourceSort _ code _ => S (Pos.size_nat code)
  | RQSourceVariable _ code _ => S (Pos.size_nat code)
  | RQSourcePair pair_value code _ =>
    S (Pos.size_nat (fst pair_value) + Pos.size_nat (snd pair_value) + Pos.size_nat code)
  | RQSourceNode _ code _ => S (Pos.size_nat code)
  | RQSourceDecision a b _ _ => S (Pos.size_nat a + Pos.size_nat b)
  | RQSourceCollapse from into before after _ =>
    S (Pos.size_nat from + Pos.size_nat into + audit_trie_nodes before + audit_trie_nodes after +
      fold_right (fun entry largest => Nat.max (Pos.size_nat (snd entry)) largest)
        0 (Map.elements before))
  | RQSourceFuel graph count queue fuel _ =>
    S (length (rw_roots graph) + count + length (rw_pending_sequence queue) + Pos.size_nat fuel)
  | RQSourceBlock _ => 1
  end.

Definition rw_rq_run_dimension {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : nat :=
  fold_right (fun receipt largest => Nat.max (rw_rq_receipt_dimension receipt) largest) 1 receipts.

Definition rw_rq_run_foreign_work {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : N :=
  fold_right (fun receipt total => (N.of_nat (rw_rq_receipt_foreign_work receipt) + total)%N)
    0%N receipts.

Definition rw_rq_whole_input_budget {K Sort V} (g : rw_graph K Sort V) (receipts : list
    (rw_rq_receipt K Sort V)) : N :=
  (rw_rq_run_foreign_work receipts + 65536 * N.pow (N.of_nat (rw_rq_input_structure g)) 14 * N.pow
    (N.of_nat (rw_rq_run_dimension receipts)) 4)%N.

(** A rebuild source run has a receipt count bounded by a polynomial in input structure. *)
Definition rw_rq_source_call_count_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
    rw_rq_rebuild_source_run op sort value g output receipts ->
    (N.of_nat (length receipts) <= 65536 * N.pow (N.of_nat (rw_rq_input_structure g)) 10)%N.

(** A rebuild source run has receipt work at most its whole-input budget. *)
Definition rw_rq_rebuild_input_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
    rw_rq_rebuild_source_run op sort value g output receipts ->
    (N.of_nat (rw_rq_receipts_work receipts) <= rw_rq_whole_input_budget g receipts)%N.
