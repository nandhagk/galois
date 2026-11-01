(** * Dense must-set source primitives

    The models retain the actual trie traversal for subset, intersection and union.
    For example, a missing value stops a subset traversal before its later branches.
    Builds on: CollectionsAuditInter and CollectionsAuditUnion. *)
From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet
  CollectionsAuditElements CollectionsAuditInter CollectionsAuditUnion.
Import List.ListNotations.

(** * Dense must-set source primitives *)

Inductive audit_dense_subset_event (U : Type) : Type :=
  | DenseSubsetNode (node : Trie.ne (U * unit)) (other : FinSet.t U)
  | DenseSubsetValue (other : option (U * unit)).

Arguments DenseSubsetNode {U} _ _.

Arguments DenseSubsetValue {U} _.

(** Membership at the matching structural position needs no key encoding. *)
Definition audit_dense_subset_value {U} (other : option (U * unit)) :
    bool * list (audit_dense_subset_event U) :=
  (match other with
  Some _ => true
  | None => false
  end, [DenseSubsetValue other]).

(** This follows the source's seven trie shapes and selective later branches. *)
Fixpoint audit_dense_subset_ne {U} (node : Trie.ne (U * unit)) (other : FinSet.t U) :
    bool * list (audit_dense_subset_event U) :=
  let here := [DenseSubsetNode node other] in
  match node with
  | Trie.N001 r =>
    let '(out, events) := audit_dense_subset_ne r (Trie.right other) in (out, here ++ events)
  | Trie.N010 _ =>
    let '(out, events) := audit_dense_subset_value (Trie.value other) in (out, here ++ events)
  | Trie.N011 _ r =>
    let '(present, events) := audit_dense_subset_value (Trie.value other) in
    if present then
      let '(out, later) := audit_dense_subset_ne r (Trie.right other) in
      (out, here ++ events ++ later)
    else (false, here ++ events)
  | Trie.N100 l =>
    let '(out, events) := audit_dense_subset_ne l (Trie.left other) in (out, here ++ events)
  | Trie.N101 l r =>
    let '(present, events) := audit_dense_subset_ne l (Trie.left other) in
    if present then
      let '(out, later) := audit_dense_subset_ne r (Trie.right other) in
      (out, here ++ events ++ later)
    else (false, here ++ events)
  | Trie.N110 l _ =>
    let '(present, events) := audit_dense_subset_ne l (Trie.left other) in
    if present then
      let '(out, later) := audit_dense_subset_value (Trie.value other) in
      (out, here ++ events ++ later)
    else (false, here ++ events)
  | Trie.N111 l _ r =>
    let '(present, events) := audit_dense_subset_ne l (Trie.left other) in
    if present then
      let '(middle, middle_events) := audit_dense_subset_value (Trie.value other) in
      if middle then
        let '(out, later) := audit_dense_subset_ne r (Trie.right other) in
        (out, here ++ events ++ middle_events ++ later)
      else (false, here ++ events ++ middle_events)
    else (false, here ++ events)
  end.

(** The empty source set succeeds without visiting an operand node. *)
Definition audit_dense_subset {U} (left right : FinSet.t U) :
    bool * list (audit_dense_subset_event U) :=
  match left with
  | Trie.Empty => (true, [])
  | Trie.Nodes node => audit_dense_subset_ne node right
  end.

(** Every visited subset frame pays a fixed source-block charge. *)
Definition audit_dense_subset_work {U} (events : list (audit_dense_subset_event U)) : nat :=
  1 + 16 * length events.

(** Input nodes bound the source subset traversal independently of its output trace. *)
Definition audit_dense_subset_budget {U} (left : FinSet.t U) : nat :=
  1 + 32 * audit_trie_nodes left.

(** Subset returns the finite-set inclusion result within its input-node work bound. *)
Definition audit_dense_subset_statement : Prop :=
  forall (U : Type) (EU : encoding U) (left right : FinSet.t U),
    let '(out, events) := audit_dense_subset left right in
    out = FinSet.subset EU left right /\
      audit_dense_subset_work events <= audit_dense_subset_budget left.

(** Intersection and union retain the actual one-sided trie traversals. *)
Definition audit_dense_inter {U} (left right : FinSet.t U) := audit_finset_inter left right.

Definition audit_dense_union {U} (left right : FinSet.t U) := audit_finset_union left right.

(** The two lattice merge operations erase to the library's exact sets and input-node bounds. *)
Definition audit_dense_merge_statement : Prop :=
  forall (U : Type) (EU : encoding U) (left right : FinSet.t U),
    let '(intersection, inter_events) := audit_dense_inter left right in
    let '(union, union_events) := audit_dense_union left right in
    intersection = FinSet.inter EU left right /\ union = FinSet.union EU left right /\
      audit_finset_inter_source_work inter_events <= 64 * (1 + audit_trie_nodes left +
        audit_trie_nodes right) /\
      audit_finset_union_source_work union_events <= 64 * (1 + audit_trie_nodes left).
