(** * RewriteAuditIndexProgramLaws

    This module defines agreement laws for callbacks, queries, and strategy programs.
    For example, a parent query for an identifier with no root must report an empty list.
    Builds on: RewriteAuditIndexPrograms and
    RewriteAuditIndexRules. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules.
Import List.ListNotations.

(** Variable, operator, hole, and guard callbacks agree with the signature and listed rules. *)
Definition rw_rp_callbacks_agree {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H)) : Prop :=
  (forall v, fst (rw_rp_var_sort callbacks v) = rw_var_sort sig v) /\
  (forall k args result, fst (rw_rp_operator_shape callbacks k args result) = rw_operator_shape sig
    k args result) /\
  (forall rule h, In rule rules -> fst (rw_rp_hole_sort callbacks rule h) = rw_hole_sort rule h) /\
  forall rule sub, In rule rules ->
    rw_rp_guard_plain sub (rw_rp_guard callbacks rule) = rw_condition rule sub.

(** A recorded query answer equals the corresponding lookup or enumeration in the index state. *)
Definition rw_rp_query_agrees {K Sort V} (EK : encoding K) (EV : encoding V)
    (state : rw_index_state K Sort V) (query : rw_rp_query K Sort V) : Prop :=
  match query with
  | RPQueryFind id answer => answer = rw_index_find state id
  | RPQuerySort id answer => answer = rw_class_sort (rw_index_base state) id
  | RPQueryNode id answer => answer = rw_node_at (rw_index_base state) id
  | RPQueryOperator k answer =>
    answer = FinSet.elements (rw_index_bucket EK k (rw_index_operators state))
  | RPQueryVariable v answer =>
    answer = FinSet.elements (rw_index_bucket EV v (rw_index_variables state))
  | RPQueryParents id answer =>
    answer =
      match rw_index_find state id with
      | None => nil
      | Some r =>
        FinSet.elements (rw_index_bucket positive_encoding r (rw_index_parent_buckets state))
      end
  | RPQueryRoots answer => answer = rw_roots (rw_index_graph state)
  | RPQueryNodes answer => answer = rw_nodes_in (rw_index_base state)
  | RPQueryGraph answer => answer = rw_index_graph state
  end.

(** For each index state, the strategy program agrees with the plain strategy on its
    view and has the specified execution witness. *)
Definition rw_rp_strategy_adapter_laws {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (adapter : rw_rp_strategy_adapter K Sort V H)
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H))
    (execution : rw_snapshot_view K Sort V ->
      rw_rp_view_program K Sort V (option (rw_attempt K Sort V H)) -> Prop) : Prop :=
  forall state,
    let view := rw_index_view EK ES EV state in
    rw_rp_view_plain view (rw_rp_strategy_program adapter) = strategy view /\
    execution view (rw_rp_strategy_program adapter).
