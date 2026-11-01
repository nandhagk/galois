(** * Counted persistent set union

    This candidate mirrors shared one-sided subtrees and the actual merge recursion.
    For example, union with an empty right side retains the left subtree without visiting it.
    Builds on: CollectionsTrie, CollectionsMap and CollectionsFinSet. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet
  CollectionsAuditElements
  CollectionsAuditTrie.
Import List.ListNotations.

Inductive audit_union_event (K : Type) : Type :=
  | AuditUnionEnter (left : Trie.ne (K * unit)) (right : FinSet.t K)
  | AuditUnionNode (left : FinSet.t K) (value : option (K * unit))
      (right output : FinSet.t K)
  | AuditUnionRoot (left right : FinSet.t K).

Arguments AuditUnionEnter {K} _ _.
Arguments AuditUnionNode {K} _ _ _ _.
Arguments AuditUnionRoot {K} _ _.

(** This is the exact Map.union_with callback used by FinSet.union. *)
Definition audit_set_union_value {K} (a b : option (K * unit)) : option (K * unit) :=
  Trie.union_opt (fun x y => (fst x, (fun v _ => v) (snd x) (snd y))) a b.

(** The recursive call skips a whole subtree when its counterpart is empty. *)
Fixpoint audit_set_union_ne {K} (node : Trie.ne (K * unit)) (other : FinSet.t K)
    : FinSet.t K * list (audit_union_event K) :=
  let enter := [AuditUnionEnter node other] in
  match other with
  | Trie.Empty => (Trie.Nodes node, enter)
  | Trie.Nodes _ =>
      match node with
      | Trie.N001 r =>
          let l := Trie.left other in
          let v := audit_set_union_value None (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, enter ++ re ++ [AuditUnionNode l v rr out])
      | Trie.N010 x =>
          let l := Trie.left other in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node l v r in
          (out, enter ++ [AuditUnionNode l v r out])
      | Trie.N011 x r =>
          let l := Trie.left other in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, enter ++ re ++ [AuditUnionNode l v rr out])
      | Trie.N100 l =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value None (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, enter ++ le ++ [AuditUnionNode ll v r out])
      | Trie.N101 l r =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value None (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, enter ++ le ++ re ++ [AuditUnionNode ll v rr out])
      | Trie.N110 l x =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, enter ++ le ++ [AuditUnionNode ll v r out])
      | Trie.N111 l x r =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, enter ++ le ++ re ++ [AuditUnionNode ll v rr out])
      end
  end.

(** No encoding is called by the original set-union body. *)
Definition audit_finset_union {K} (left right : FinSet.t K)
    : FinSet.t K * list (audit_union_event K) :=
  match left with
  | Trie.Empty => (right, [AuditUnionRoot left right])
  | Trie.Nodes node =>
      let '(out, events) := audit_set_union_ne node right in
      (out, AuditUnionRoot left right :: events)
  end.

(** Discarding union events recovers the original set union. *)
Definition audit_finset_union_erases_statement : Prop :=
  forall K (enc : encoding K) left right,
    fst (audit_finset_union left right) = FinSet.union enc left right.

(** The selected merge-frame count is bounded by the first input's actual node count. *)
Definition audit_finset_union_count_statement : Prop :=
  forall K (left right : FinSet.t K),
    length (snd (audit_finset_union left right)) <=
      1 + 2 * match left with
              | Trie.Empty => 0
              | Trie.Nodes node => audit_elements_nodes node
              end.

(** Fixed source-frame charges include visited merge branches and actual rebuilt nodes. *)
Fixpoint audit_finset_union_source_work {K} (events : list (audit_union_event K)) : nat :=
  match events with
  | [] => 0
  | AuditUnionRoot _ _ :: rest => 1 + audit_finset_union_source_work rest
  | AuditUnionEnter _ _ :: rest => 10 + audit_finset_union_source_work rest
  | AuditUnionNode l value r _ :: rest =>
      audit_trie_node_work l value r + audit_finset_union_source_work rest
  end.

(** Set union source work is bounded by a constant plus fifteen times the left node count. *)
Definition audit_finset_union_source_bound_statement : Prop :=
  forall K (left right : FinSet.t K),
    audit_finset_union_source_work (snd (audit_finset_union left right)) <=
      1 + 15 * audit_trie_nodes left.
