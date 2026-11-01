(** * Counted finite-set intersection

    This mirror retains merge recursion and the original one-sided filtering work.
    For example, intersecting a nonempty tree with empty still visits its filtered nodes.
    Builds on: CollectionsFinSet and the shared trie model. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_inter_event (K : Type) : Type :=
  | AuditInterRoot (left right : FinSet.t K)
  | AuditInterMerge (node : Trie.ne (K * unit)) (other : FinSet.t K)
  | AuditInterDrop (node : Trie.ne (K * unit))
  | AuditInterDiscard (value : K * unit)
  | AuditInterValue (left right output : option (K * unit))
  | AuditInterNode (left : FinSet.t K) (value : option (K * unit)) (right output : FinSet.t K).

Arguments AuditInterRoot {K} _ _.
Arguments AuditInterMerge {K} _ _.
Arguments AuditInterDrop {K} _.
Arguments AuditInterDiscard {K} _.
Arguments AuditInterValue {K} _ _ _.
Arguments AuditInterNode {K} _ _ _ _.

(** A one-sided [Trie.filter_ne] still visits each node and rebuilds the empty result. *)
Fixpoint audit_inter_drop_ne {K} (node : Trie.ne (K * unit))
    : FinSet.t K * list (audit_inter_event K) :=
  let enter := [AuditInterDrop node] in
  match node with
  | Trie.N001 r =>
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node Trie.Empty None rr in
      (out, enter ++ re ++ [AuditInterNode Trie.Empty None rr out])
  | Trie.N010 value =>
      let out := Trie.node Trie.Empty None Trie.Empty in
      (out, enter ++ [AuditInterDiscard value; AuditInterNode Trie.Empty None Trie.Empty out])
  | Trie.N011 value r =>
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node Trie.Empty None rr in
      (out, enter ++ [AuditInterDiscard value] ++ re ++ [AuditInterNode Trie.Empty None rr out])
  | Trie.N100 l =>
      let '(ll, le) := audit_inter_drop_ne l in
      let out := Trie.node ll None Trie.Empty in
      (out, enter ++ le ++ [AuditInterNode ll None Trie.Empty out])
  | Trie.N101 l r =>
      let '(ll, le) := audit_inter_drop_ne l in
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node ll None rr in
      (out, enter ++ le ++ re ++ [AuditInterNode ll None rr out])
  | Trie.N110 l value =>
      let '(ll, le) := audit_inter_drop_ne l in
      let out := Trie.node ll None Trie.Empty in
      (out, enter ++ le ++ [AuditInterDiscard value; AuditInterNode ll None Trie.Empty out])
  | Trie.N111 l value r =>
      let '(ll, le) := audit_inter_drop_ne l in
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node ll None rr in
      (out, enter ++ le ++ [AuditInterDiscard value] ++ re ++ [AuditInterNode ll None rr out])
  end.

Definition audit_inter_drop {K} (input : FinSet.t K) : FinSet.t K * list (audit_inter_event K) :=
  match input with
  | Trie.Empty => (Trie.Empty, [])
  | Trie.Nodes node => audit_inter_drop_ne node
  end.

(** [Map.combine_pair] retains the left key only when both sides are present. *)
Definition audit_inter_value {K} (a b : option (K * unit))
    : option (K * unit) * list (audit_inter_event K) :=
  let out := match a, b with
  | Some (key, _), Some _ => Some (key, tt)
  | _, _ => None
  end in
  (out, [AuditInterValue a b out]).

(** The seven merge cases reproduce both original recursive and one-sided filtering calls. *)
Fixpoint audit_inter_merge_ne {K} (node : Trie.ne (K * unit)) (other : FinSet.t K)
    : FinSet.t K * list (audit_inter_event K) :=
  let enter := [AuditInterMerge node other] in
  match other with
  | Trie.Empty =>
      let '(out, events) := audit_inter_drop_ne node in (out, enter ++ events)
  | Trie.Nodes _ =>
      match node with
      | Trie.N001 r =>
          let '(l, le) := audit_inter_drop (Trie.left other) in
          let '(v, ve) := audit_inter_value None (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node l v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode l v
            rr out])
      | Trie.N010 kv =>
          let '(l, le) := audit_inter_drop (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(r, re) := audit_inter_drop (Trie.right other) in
          let out := Trie.node l v r in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode l v r out])
      | Trie.N011 kv r =>
          let '(l, le) := audit_inter_drop (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node l v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode l v
            rr out])
      | Trie.N100 l =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value None (Trie.value other) in
          let '(r, re) := audit_inter_drop (Trie.right other) in
          let out := Trie.node ll v r in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v
            r out])
      | Trie.N101 l r =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value None (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node ll v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v
            rr out])
      | Trie.N110 l kv =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(r, re) := audit_inter_drop (Trie.right other) in
          let out := Trie.node ll v r in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v
            r out])
      | Trie.N111 l kv r =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node ll v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v
            rr out])
      end
  end.

Definition audit_finset_inter {K} (left right : FinSet.t K)
    : FinSet.t K * list (audit_inter_event K) :=
  match left with
  | Trie.Empty =>
      let '(out, events) := audit_inter_drop right in (out, AuditInterRoot left right :: events)
  | Trie.Nodes node =>
      let '(out, events) := audit_inter_merge_ne node right in
      (out, AuditInterRoot left right :: events)
  end.

(** Discarding intersection events recovers the original set intersection. *)
Definition audit_finset_inter_erases_statement : Prop :=
  forall K (enc : encoding K) (left right : FinSet.t K),
    fst (audit_finset_inter left right) = FinSet.inter enc left right.

(** Intersection emits at most one event plus six per node in the two input tries. *)
Definition audit_finset_inter_count_statement : Prop :=
  forall K (left right : FinSet.t K),
    length (snd (audit_finset_inter left right)) <=
      1 + 6 * (audit_trie_nodes left + audit_trie_nodes right).

(** Fixed local source-block charges include actual one-sided filter and node work. *)
Fixpoint audit_finset_inter_source_work {K} (events : list (audit_inter_event K)) : nat :=
  match events with
  | [] => 0
  | AuditInterRoot _ _ :: rest => 2 + audit_finset_inter_source_work rest
  | AuditInterMerge _ _ :: rest => 12 + audit_finset_inter_source_work rest
  | AuditInterDrop _ :: rest => 9 + audit_finset_inter_source_work rest
  | AuditInterDiscard _ :: rest => 4 + audit_finset_inter_source_work rest
  | AuditInterValue _ _ _ :: rest => 7 + audit_finset_inter_source_work rest
  | AuditInterNode l value r _ :: rest =>
      audit_trie_node_work l value r + audit_finset_inter_source_work rest
  end.

(** Intersection source work is bounded by a constant and the total input trie-node count. *)
Definition audit_finset_inter_source_bound_statement : Prop :=
  forall K (left right : FinSet.t K),
    audit_finset_inter_source_work (snd (audit_finset_inter left right)) <=
      2 + 30 * (audit_trie_nodes left + audit_trie_nodes right).
