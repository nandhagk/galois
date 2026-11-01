(** * RewriteAuditIndexFind

    Models index root lookup and node canonicalization with trace costs and bounds.
    For example, a missing base root makes the source lookup return None.
    Builds on: RewriteEgraph and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference.
Import List.ListNotations.

Inductive rw_ri_find_call : Type :=
  | RIFindBase : rw_id -> Map.t rw_id rw_id -> option rw_id ->
      audit_trace (audit_trie_call (rw_id * rw_id)) -> rw_ri_find_call
  | RIFindForest : rw_id -> UnionFind.t rw_id -> (rw_id * UnionFind.t rw_id) ->
      list (audit_uf_event rw_id (audit_basic_encoding_event positive)) -> rw_ri_find_call.

Definition rw_ri_find_event_cost (event : audit_event rw_ri_find_call) : nat :=
  match event with
  | AuditCall (RIFindBase _ _ _ trace) => 2 + audit_trie_get_trace_source_work trace
  | AuditCall (RIFindForest _ _ _ trace) => 1 + audit_uf_source_work audit_basic_encoding_work trace
  | _ => 1
  end.

Definition rw_ri_find_trace_cost (trace : audit_trace rw_ri_find_call) : nat :=
  fold_right (fun event total => rw_ri_find_event_cost event + total) 0 trace.

Definition rw_ri_find_atomic {K Sort V} (state : rw_index_state K Sort V) (id : rw_id) :
    option rw_id * audit_trace rw_ri_find_call :=
  let parents := rw_class_roots (rw_index_base state) in
  let '(base_root, base_trace) := audit_map_code_get id parents in
  match base_root with
  | None => (None, [AuditCase 820 []; AuditCall (RIFindBase id parents None base_trace);
      AuditCase 821 []; AuditConstruct 822 []])
  | Some root =>
    let forest := rw_index_forest state in
    let '(found, find_trace) := audit_uf_find audit_positive_encode root forest in
    (Some (fst found), [AuditCase 820 []; AuditCall (RIFindBase id parents (Some root) base_trace);
      AuditCase 823 []; AuditCall (RIFindForest root forest found find_trace);
      AuditConstruct 824 []])
  end.

Fixpoint rw_ri_find_fuel_budget (fuel : nat) (id : rw_id) (forest : UnionFind.t rw_id) : nat :=
  match fuel with
  | 0 => 16
  | S rest =>
    64 + 32 * Pos.size_nat id +
    match Map.get positive_encoding id (UnionFind.parents forest) with
    | None => 0
    | Some next => rw_ri_find_fuel_budget rest next forest
    end
  end.

Definition rw_ri_find_budget {K Sort V} (state : rw_index_state K Sort V) (id : rw_id) : nat :=
  10 + 5 * Pos.size_nat id +
  match rw_find (rw_index_base state) id with
  | None => 0
  | Some root =>
    rw_ri_find_fuel_budget (S (UnionFind.max_rank (rw_index_forest state))) root
      (rw_index_forest state)
  end.

Inductive rw_ri_canon_call : Type :=
  | RICanonFind : rw_id -> option rw_id -> audit_trace rw_ri_find_call -> rw_ri_canon_call.

Definition rw_ri_canon_event_cost (event : audit_event rw_ri_canon_call) : nat :=
  match event with
  | AuditCall (RICanonFind _ _ trace) => 1 + rw_ri_find_trace_cost trace
  | _ => 1
  end.

Definition rw_ri_canon_trace_cost (trace : audit_trace rw_ri_canon_call) : nat :=
  fold_right (fun event total => rw_ri_canon_event_cost event + total) 0 trace.

Fixpoint rw_ri_canon_children {K Sort V} (state : rw_index_state K Sort V) (ids : list rw_id) :
    list rw_id * audit_trace rw_ri_canon_call :=
  match ids with
  | nil => (nil, [AuditCase 825 []; AuditConstruct 826 []])
  | id :: rest =>
    let '(found, find_trace) := rw_ri_find_atomic state id in
    let current :=
      match found with
      | Some root => root
      | None => id
      end in
    let '(tail, trace) := rw_ri_canon_children state rest in
    (current :: tail, [AuditCase 827 []; AuditCall (RICanonFind id found find_trace);
      AuditCase 828 []] ++ trace ++ [AuditConstruct 829 []])
  end.

Definition rw_ri_canon_atomic {K Sort V} (state : rw_index_state K Sort V) (node : rw_node K Sort V)
    : rw_node K Sort V * audit_trace rw_ri_canon_call :=
  match node with
  | RWNVar s v => (RWNVar s v, [AuditCase 830 []; AuditConstruct 831 []])
  | RWNApp s op children =>
    let '(ids, trace) := rw_ri_canon_children state children in
    (RWNApp s op ids, [AuditCase 832 []] ++ trace ++ [AuditConstruct 833 []])
  end.

Fixpoint rw_ri_canon_children_budget {K Sort V} (state : rw_index_state K Sort V) (ids : list rw_id)
    : nat :=
  match ids with
  | nil => 2
  | id :: rest => 4 + rw_ri_find_budget state id + rw_ri_canon_children_budget state rest
  end.

Definition rw_ri_canon_budget {K Sort V} (state : rw_index_state K Sort V) (node : rw_node K Sort V)
    : nat :=
  match node with
  | RWNVar _ _ => 2
  | RWNApp _ _ ids => 2 + rw_ri_canon_children_budget state ids
  end.

(** Erasing find receipts yields the index's root lookup for the same identifier and state. *)
Definition rw_ri_find_erases_contract : Prop :=
  forall K Sort V (state : rw_index_state K Sort V) id,
    fst (rw_ri_find_atomic state id) = rw_index_find state id.

(** The expanded find trace cost is bounded by the budget for that state and identifier. *)
Definition rw_ri_find_bound_contract : Prop :=
  forall K Sort V (state : rw_index_state K Sort V) id,
    rw_ri_find_trace_cost (snd (rw_ri_find_atomic state id)) <= rw_ri_find_budget state id.

(** Erasing canonicalization receipts yields the index's canonical node for the same state. *)
Definition rw_ri_canon_erases_contract : Prop :=
  forall K Sort V (state : rw_index_state K Sort V) node,
    fst (rw_ri_canon_atomic state node) = rw_index_canonical_node state node.

(** The expanded canonicalization trace cost is bounded by the state and node budget. *)
Definition rw_ri_canon_bound_contract : Prop :=
  forall K Sort V (state : rw_index_state K Sort V) node,
    rw_ri_canon_trace_cost (snd (rw_ri_canon_atomic state node)) <= rw_ri_canon_budget state node.
