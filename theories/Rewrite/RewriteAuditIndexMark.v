(** * RewriteAuditIndexMark

    Models dirty-node marking with set-operation traces and a prospective budget.
    For example, an identifier already present in the dirty set is not inserted again.
    Builds on: RewriteEgraph and
    RewriteAuditIndexTickReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexTickReference.
Import List.ListNotations.

Inductive rw_ri_mark_call : Type :=
  | RIMarkMem : rw_id -> bool ->
      list (audit_set_event rw_id (audit_basic_encoding_event positive)) -> rw_ri_mark_call
  | RIMarkAdd : rw_id -> FinSet.t rw_id ->
      list (audit_set_event rw_id (audit_basic_encoding_event positive)) -> rw_ri_mark_call.

Definition rw_ri_mark_event_cost (event : audit_event rw_ri_mark_call) : nat :=
  match event with
  | AuditCall (RIMarkMem _ _ trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | AuditCall (RIMarkAdd _ _ trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | _ => 1
  end.

Definition rw_ri_mark_trace_cost (trace : audit_trace rw_ri_mark_call) : nat :=
  fold_right (fun event total => rw_ri_mark_event_cost event + total) 0 trace.

Fixpoint rw_ri_mark_dirty_atomic (ids : list rw_id) (order : list rw_id) (members : FinSet.t rw_id)
    : (list rw_id * FinSet.t rw_id) * audit_trace rw_ri_mark_call :=
  match ids with
  | nil => ((order, members), [AuditCase 860 []; AuditConstruct 861 []])
  | id :: rest =>
    let '(present, mem_trace) := audit_finset_mem audit_positive_encode id members in
    if present then
      let '(out, trace) := rw_ri_mark_dirty_atomic rest order members in
      (out, [AuditCase 862 []; AuditCall (RIMarkMem id present mem_trace); AuditCase 863 []] ++
        trace)
    else
      let '(updated, add_trace) := audit_finset_add audit_positive_encode id members in
      let '(out, trace) := rw_ri_mark_dirty_atomic rest (id :: order) updated in
      (out, [AuditCase 862 []; AuditCall (RIMarkMem id present mem_trace); AuditCase 864 [];
        AuditCall (RIMarkAdd id updated add_trace); AuditConstruct 865 []] ++ trace)
  end.

Fixpoint rw_ri_mark_budget (ids : list rw_id) : nat :=
  match ids with
  | nil => 2
  | id :: rest => 24 + 24 * Pos.size_nat id + rw_ri_mark_budget rest
  end.

(** Erasing receipts from dirty marking returns the same order and set as the plain operation. *)
Definition rw_ri_mark_erases_contract : Prop :=
  forall ids order members,
    fst (rw_ri_mark_dirty_atomic ids order members) = rw_ri_mark_dirty ids order members.

(** Dirty marking's expanded trace cost is bounded by the budget for the input identifiers. *)
Definition rw_ri_mark_bound_contract : Prop :=
  forall ids order members,
    rw_ri_mark_trace_cost (snd (rw_ri_mark_dirty_atomic ids order members)) <=
      rw_ri_mark_budget ids.
