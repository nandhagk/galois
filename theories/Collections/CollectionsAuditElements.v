(** * Counted trie and set enumeration

    This candidate mirrors the actual accumulator traversal and its final list passes.
    For example, a singleton emits its stored key and its trie position once.
    Builds on: CollectionsTrie, CollectionsMap and CollectionsFinSet. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsFinSet.
Import List.ListNotations.

(** * Concrete traversal frames *)

Inductive audit_elements_event (A : Type) : Type :=
  | AuditElementsNode (node : Trie.ne A) (acc : list (positive * A))
  | AuditElementsEmit (position : positive) (value : A) (acc : list (positive * A))
  | AuditElementsReverse (remaining acc : list (positive * A))
  | AuditElementsMap (remaining : list (positive * A)).

Arguments AuditElementsNode {A} _ _.
Arguments AuditElementsEmit {A} _ _ _.
Arguments AuditElementsReverse {A} _ _.
Arguments AuditElementsMap {A} _.

(** Preserve the exact original left-root-right traversal and accumulator. *)
Fixpoint audit_elements_fold_ne {A} (path : positive -> positive) (node : Trie.ne A)
    (acc : list (positive * A)) : list (positive * A) * list (audit_elements_event A) :=
  let here := [AuditElementsNode node acc] in
  match node with
  | Trie.N001 r =>
      let '(out, events) := audit_elements_fold_ne (fun p => path (xI p)) r acc in
      (out, here ++ events)
  | Trie.N010 v =>
      let p := path xH in ((p, v) :: acc, here ++ [AuditElementsEmit p v acc])
  | Trie.N011 v r =>
      let p := path xH in
      let next := (p, v) :: acc in
      let '(out, events) := audit_elements_fold_ne (fun q => path (xI q)) r next in
      (out, here ++ [AuditElementsEmit p v acc] ++ events)
  | Trie.N100 l =>
      let '(out, events) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      (out, here ++ events)
  | Trie.N101 l r =>
      let '(middle, le) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      let '(out, re) := audit_elements_fold_ne (fun p => path (xI p)) r middle in
      (out, here ++ le ++ re)
  | Trie.N110 l v =>
      let '(middle, le) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      let p := path xH in
      ((p, v) :: middle, here ++ le ++ [AuditElementsEmit p v middle])
  | Trie.N111 l v r =>
      let '(middle, le) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      let p := path xH in
      let next := (p, v) :: middle in
      let '(out, re) := audit_elements_fold_ne (fun q => path (xI q)) r next in
      (out, here ++ le ++ [AuditElementsEmit p v middle] ++ re)
  end.

(** This is [rev_append] on the same accumulator, including its final empty case. *)
Fixpoint audit_elements_reverse {A} (input acc : list (positive * A))
    : list (positive * A) * list (audit_elements_event A) :=
  match input with
  | [] => (acc, [AuditElementsReverse input acc])
  | x :: rest =>
      let '(out, events) := audit_elements_reverse rest (x :: acc) in
      (out, AuditElementsReverse input acc :: events)
  end.

(** The actual position-value enumeration is the traversal followed by reversal. *)
Definition audit_trie_elements {A} (input : Trie.t A)
    : list (positive * A) * list (audit_elements_event A) :=
  let '(reversed, fold_events) :=
    match input with
    | Trie.Empty => ([], [])
    | Trie.Nodes node => audit_elements_fold_ne (fun p => p) node []
    end in
  let '(out, reverse_events) := audit_elements_reverse reversed [] in
  (out, fold_events ++ reverse_events).

(** Map and set projection each visit the exact returned list. *)
Fixpoint audit_elements_values {A} (input : list (positive * A))
    : list A * list (audit_elements_event A) :=
  match input with
  | [] => ([], [AuditElementsMap input])
  | (_, value) :: rest =>
      let '(out, events) := audit_elements_values rest in
      (value :: out, AuditElementsMap input :: events)
  end.

Definition audit_map_elements {K V} (input : Map.t K V)
    : list (K * V) * list (audit_elements_event (K * V)) :=
  let '(positions, first) := audit_trie_elements input in
  let '(values, second) := audit_elements_values positions in
  (values, first ++ second).

Inductive audit_set_elements_event (K : Type) : Type :=
  | AuditSetElementsTrie (event : audit_elements_event (K * unit))
  | AuditSetElementsProject (remaining : list (K * unit)).

Arguments AuditSetElementsTrie {K} _.
Arguments AuditSetElementsProject {K} _.

Fixpoint audit_set_elements_project {K} (input : list (K * unit))
    : list K * list (audit_set_elements_event K) :=
  match input with
  | [] => ([], [AuditSetElementsProject input])
  | (key, _) :: rest =>
      let '(out, events) := audit_set_elements_project rest in
      (key :: out, AuditSetElementsProject input :: events)
  end.

Definition audit_finset_elements {K} (input : FinSet.t K)
    : list K * list (audit_set_elements_event K) :=
  let '(values, first) := audit_map_elements input in
  let '(keys, second) := audit_set_elements_project values in
  (keys, map AuditSetElementsTrie first ++ second).

(** * Future correctness and quantitative claims *)

Fixpoint audit_elements_nodes {A} (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => S (audit_elements_nodes r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r => S (audit_elements_nodes r)
  | Trie.N100 l => S (audit_elements_nodes l)
  | Trie.N101 l r => S (audit_elements_nodes l + audit_elements_nodes r)
  | Trie.N110 l _ => S (audit_elements_nodes l)
  | Trie.N111 l _ r => S (audit_elements_nodes l + audit_elements_nodes r)
  end.

(** Discarding the trie elements events recovers the corresponding original operation under its
  premises. *)
Definition audit_trie_elements_erases_statement : Prop :=
  forall A (input : Trie.t A), fst (audit_trie_elements input) = Trie.elements input.

(** Discarding the map elements events recovers the corresponding original operation under its
  premises. *)
Definition audit_map_elements_erases_statement : Prop :=
  forall K V (input : Map.t K V), fst (audit_map_elements input) = Map.elements input.

(** Discarding the finset elements events recovers the corresponding original operation under
  its premises. *)
Definition audit_finset_elements_erases_statement : Prop :=
  forall K (input : FinSet.t K), fst (audit_finset_elements input) = FinSet.elements input.

(** The elements fold emits at most two events per visited trie node. *)
Definition audit_elements_fold_count_statement : Prop :=
  forall A path (node : Trie.ne A) acc,
    length (snd (audit_elements_fold_ne path node acc)) <= 2 * audit_elements_nodes node.

(** * Fixed source-frame charges and input measures *)

(** Position construction pays for every bit of the concrete emitted position. *)
Fixpoint audit_elements_bits {A} (path : positive -> positive) (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => audit_elements_bits (fun p => path (xI p)) r
  | Trie.N010 _ => Pos.size_nat (path xH)
  | Trie.N011 _ r => Pos.size_nat (path xH) + audit_elements_bits (fun p => path (xI p)) r
  | Trie.N100 l => audit_elements_bits (fun p => path (xO p)) l
  | Trie.N101 l r => audit_elements_bits (fun p => path (xO p)) l +
      audit_elements_bits (fun p => path (xI p)) r
  | Trie.N110 l _ => audit_elements_bits (fun p => path (xO p)) l + Pos.size_nat (path xH)
  | Trie.N111 l _ r => audit_elements_bits (fun p => path (xO p)) l + Pos.size_nat (path xH) +
      audit_elements_bits (fun p => path (xI p)) r
  end.

Definition audit_elements_frame_work {A} (event : audit_elements_event A) : nat :=
  match event with
  | AuditElementsNode _ _ => 10
  | AuditElementsEmit position _ _ => 3 + Pos.size_nat position
  | AuditElementsReverse _ _ => 2
  | AuditElementsMap _ => 2
  end.

Fixpoint audit_elements_work {A} (events : list (audit_elements_event A)) : nat :=
  match events with
  | [] => 0
  | event :: rest => audit_elements_frame_work event + audit_elements_work rest
  end.

Fixpoint audit_set_elements_work {K} (events : list (audit_set_elements_event K)) : nat :=
  match events with
  | [] => 0
  | AuditSetElementsTrie event :: rest =>
      audit_elements_frame_work event + audit_set_elements_work rest
  | AuditSetElementsProject _ :: rest => 2 + audit_set_elements_work rest
  end.

Definition audit_trie_nodes {A} (input : Trie.t A) : nat :=
  match input with
  | Trie.Empty => 0
  | Trie.Nodes node => audit_elements_nodes node
  end.

Definition audit_trie_output_bits {A} (input : Trie.t A) : nat :=
  match input with
  | Trie.Empty => 0
  | Trie.Nodes node => audit_elements_bits (fun p => p) node
  end.

(** Bounds are input-derived and include emitted position bits and existing output traversals. *)
Definition audit_trie_elements_work_bound_statement : Prop :=
  forall A (input : Trie.t A),
    audit_elements_work (snd (audit_trie_elements input)) <=
      15 * audit_trie_nodes input + audit_trie_output_bits input + 2.

(** Map enumeration work is bounded by trie nodes and emitted position bits. *)
Definition audit_map_elements_work_bound_statement : Prop :=
  forall K V (input : Map.t K V),
    audit_elements_work (snd (audit_map_elements input)) <=
      17 * audit_trie_nodes input + audit_trie_output_bits input + 4.

(** Set enumeration work is bounded by trie nodes and emitted position bits. *)
Definition audit_finset_elements_work_bound_statement : Prop :=
  forall K (input : FinSet.t K),
    audit_set_elements_work (snd (audit_finset_elements input)) <=
      19 * audit_trie_nodes input + audit_trie_output_bits input + 6.
