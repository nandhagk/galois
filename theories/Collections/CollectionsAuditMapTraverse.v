(** * Counted map transformations

    These mirrors retain every visited trie node and actual value callback operand and result.
    For example, a singleton map invokes its mapper exactly once.
    Builds on: CollectionsMap and the audit enumeration node measure. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsTrie CollectionsMap
  CollectionsAuditTrie CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_map_transform_event (K V W E : Type) : Type :=
  | AuditMapTransformNode (node : Trie.ne (K * V))
  | AuditMapTransformCall (key : K) (input : V) (output : W) (events : list E)
  | AuditMapTransformBuilt (left : Trie.t (K * W)) (value : option (K * W))
      (right output : Trie.t (K * W)).

Arguments AuditMapTransformNode {K V W E} _.
Arguments AuditMapTransformCall {K V W E} _ _ _ _.
Arguments AuditMapTransformBuilt {K V W E} _ _ _ _.

(** This follows the seven branches of [Trie.filter_ne] used by [Map.map]. *)
Fixpoint audit_map_transform_ne {K V W E} (f : V -> W * list E) (node : Trie.ne (K * V))
    : Trie.t (K * W) * list (audit_map_transform_event K V W E) :=
  let here := [AuditMapTransformNode node] in
  match node with
  | Trie.N001 r =>
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node Trie.Empty None rr in
      (out, here ++ re ++ [AuditMapTransformBuilt Trie.Empty None rr out])
  | Trie.N010 (key, value) =>
      let '(v, ve) := f value in
      let out := Trie.node Trie.Empty (Some (key, v)) Trie.Empty in
      (out, here ++ [AuditMapTransformCall key value v ve;
                     AuditMapTransformBuilt Trie.Empty (Some (key, v)) Trie.Empty out])
  | Trie.N011 (key, value) r =>
      let '(v, ve) := f value in
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node Trie.Empty (Some (key, v)) rr in
      (out, here ++ [AuditMapTransformCall key value v ve] ++ re ++
        [AuditMapTransformBuilt Trie.Empty (Some (key, v)) rr out])
  | Trie.N100 l =>
      let '(ll, le) := audit_map_transform_ne f l in
      let out := Trie.node ll None Trie.Empty in
      (out, here ++ le ++ [AuditMapTransformBuilt ll None Trie.Empty out])
  | Trie.N101 l r =>
      let '(ll, le) := audit_map_transform_ne f l in
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node ll None rr in
      (out, here ++ le ++ re ++ [AuditMapTransformBuilt ll None rr out])
  | Trie.N110 l (key, value) =>
      let '(ll, le) := audit_map_transform_ne f l in
      let '(v, ve) := f value in
      let out := Trie.node ll (Some (key, v)) Trie.Empty in
      (out, here ++ le ++ [AuditMapTransformCall key value v ve;
                           AuditMapTransformBuilt ll (Some (key, v)) Trie.Empty out])
  | Trie.N111 l (key, value) r =>
      let '(ll, le) := audit_map_transform_ne f l in
      let '(v, ve) := f value in
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node ll (Some (key, v)) rr in
      (out, here ++ le ++ [AuditMapTransformCall key value v ve] ++ re ++
        [AuditMapTransformBuilt ll (Some (key, v)) rr out])
  end.

Definition audit_map_transform {K V W E} (f : V -> W * list E) (input : Map.t K V)
    : Map.t K W * list (audit_map_transform_event K V W E) :=
  match input with
  | Trie.Empty => (Trie.Empty, [])
  | Trie.Nodes node => audit_map_transform_ne f node
  end.

(** These claims compare the actual same inputs and bound outer frames by input nodes. *)
Definition audit_map_transform_erases_statement : Prop :=
  forall K V W E (f : V -> W * list E) (original : V -> W) (input : Map.t K V),
    (forall value, fst (f value) = original value) ->
    fst (audit_map_transform f input) = Map.map original input.

(** Map transformation emits at most three events per input trie node. *)
Definition audit_map_transform_count_statement : Prop :=
  forall K V W E (f : V -> W * list E) (node : Trie.ne (K * V)),
    length (snd (audit_map_transform_ne f node)) <= 3 * audit_elements_nodes node.

(** * Map union with typed overlapping-value calls *)

Inductive audit_map_union_event (K V E : Type) : Type :=
  | AuditMapUnionEnter (node : Trie.ne (K * V)) (other : Map.t K V)
  | AuditMapUnionCall (left_key right_key : K) (left_value right_value output : V)
      (events : list E)
  | AuditMapUnionBuilt (left : Map.t K V) (value : option (K * V))
      (right output : Map.t K V)
  | AuditMapUnionRoot (left right : Map.t K V).

Arguments AuditMapUnionEnter {K V E} _ _.
Arguments AuditMapUnionCall {K V E} _ _ _ _ _ _.
Arguments AuditMapUnionBuilt {K V E} _ _ _ _.
Arguments AuditMapUnionRoot {K V E} _ _.

(** A callback occurs only for overlapping entries, with both original keys and values. *)
Definition audit_map_union_value {K V E} (f : V -> V -> V * list E)
    (a b : option (K * V)) : option (K * V) * list (audit_map_union_event K V E) :=
  match a, b with
  | Some (ka, va), Some (kb, vb) =>
      let '(v, events) := f va vb in
      (Some (ka, v), [AuditMapUnionCall ka kb va vb v events])
  | Some kv, None => (Some kv, [])
  | None, Some kv => (Some kv, [])
  | None, None => (None, [])
  end.

(** The source merges each overlapping node and shares a missing-side subtree. *)
Fixpoint audit_map_union_ne {K V E} (f : V -> V -> V * list E)
    (node : Trie.ne (K * V)) (other : Map.t K V)
    : Map.t K V * list (audit_map_union_event K V E) :=
  let here := [AuditMapUnionEnter node other] in
  match other with
  | Trie.Empty => (Trie.Nodes node, here)
  | Trie.Nodes _ =>
      match node with
      | Trie.N001 r =>
          let l := Trie.left other in
          let '(v, ve) := audit_map_union_value f None (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, here ++ ve ++ re ++ [AuditMapUnionBuilt l v rr out])
      | Trie.N010 kv =>
          let l := Trie.left other in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node l v r in
          (out, here ++ ve ++ [AuditMapUnionBuilt l v r out])
      | Trie.N011 kv r =>
          let l := Trie.left other in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, here ++ ve ++ re ++ [AuditMapUnionBuilt l v rr out])
      | Trie.N100 l =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f None (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, here ++ le ++ ve ++ [AuditMapUnionBuilt ll v r out])
      | Trie.N101 l r =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f None (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, here ++ le ++ ve ++ re ++ [AuditMapUnionBuilt ll v rr out])
      | Trie.N110 l kv =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, here ++ le ++ ve ++ [AuditMapUnionBuilt ll v r out])
      | Trie.N111 l kv r =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, here ++ le ++ ve ++ re ++ [AuditMapUnionBuilt ll v rr out])
      end
  end.

Definition audit_map_union {K V E} (f : V -> V -> V * list E) (left right : Map.t K V)
    : Map.t K V * list (audit_map_union_event K V E) :=
  match left with
  | Trie.Empty => (right, [AuditMapUnionRoot left right])
  | Trie.Nodes node =>
      let '(out, events) := audit_map_union_ne f node right in
      (out, AuditMapUnionRoot left right :: events)
  end.

(** Discarding the map union events recovers the corresponding original operation under its
  premises. *)
Definition audit_map_union_erases_statement : Prop :=
  forall K V E (f : V -> V -> V * list E) (original : V -> V -> V) (left right : Map.t K V),
    (forall x y, fst (f x y) = original x y) ->
    fst (audit_map_union f left right) = Map.union_with original left right.

(** Map union emits at most one event plus three per left-hand trie node. *)
Definition audit_map_union_count_statement : Prop :=
  forall K V E (f : V -> V -> V * list E) (left right : Map.t K V),
    length (snd (audit_map_union f left right)) <=
      1 + 3 * match left with
              | Trie.Empty => 0
              | Trie.Nodes node => audit_elements_nodes node
              end.

(** * Fixed source-frame charges and actual callback traces *)

Fixpoint audit_map_transform_source_work {K V W E} (child_work : list E -> nat)
    (events : list (audit_map_transform_event K V W E)) : nat :=
  match events with
  | [] => 0
  | AuditMapTransformNode _ :: rest => 10 + audit_map_transform_source_work child_work rest
  | AuditMapTransformCall _ _ _ child :: rest =>
      3 + child_work child + audit_map_transform_source_work child_work rest
  | AuditMapTransformBuilt l value r _ :: rest =>
      audit_trie_node_work l value r + audit_map_transform_source_work child_work rest
  end.

Fixpoint audit_map_transform_child_work {K V W E} (child_work : list E -> nat)
    (events : list (audit_map_transform_event K V W E)) : nat :=
  match events with
  | [] => 0
  | AuditMapTransformCall _ _ _ child :: rest =>
      child_work child + audit_map_transform_child_work child_work rest
  | _ :: rest => audit_map_transform_child_work child_work rest
  end.

(** Map transformation work is bounded by trie nodes and actual child callback work. *)
Definition audit_map_transform_source_bound_statement : Prop :=
  forall K V W E (f : V -> W * list E) child_work (input : Map.t K V),
    let events := snd (audit_map_transform f input) in
    audit_map_transform_source_work child_work events <=
      18 * audit_trie_nodes input + audit_map_transform_child_work child_work events.

Fixpoint audit_map_union_source_work {K V E} (child_work : list E -> nat)
    (events : list (audit_map_union_event K V E)) : nat :=
  match events with
  | [] => 0
  | AuditMapUnionRoot _ _ :: rest => 1 + audit_map_union_source_work child_work rest
  | AuditMapUnionEnter _ _ :: rest => 10 + audit_map_union_source_work child_work rest
  | AuditMapUnionCall _ _ _ _ _ child :: rest =>
      3 + child_work child + audit_map_union_source_work child_work rest
  | AuditMapUnionBuilt l value r _ :: rest =>
      audit_trie_node_work l value r + audit_map_union_source_work child_work rest
  end.

Fixpoint audit_map_union_child_work {K V E} (child_work : list E -> nat)
    (events : list (audit_map_union_event K V E)) : nat :=
  match events with
  | [] => 0
  | AuditMapUnionCall _ _ _ _ _ child :: rest =>
      child_work child + audit_map_union_child_work child_work rest
  | _ :: rest => audit_map_union_child_work child_work rest
  end.

(** Map union work is bounded by left trie nodes and actual child callback work. *)
Definition audit_map_union_source_bound_statement : Prop :=
  forall K V E (f : V -> V -> V * list E) child_work (left right : Map.t K V),
    let events := snd (audit_map_union f left right) in
    audit_map_union_source_work child_work events <=
      1 + 18 * audit_trie_nodes left + audit_map_union_child_work child_work events.
