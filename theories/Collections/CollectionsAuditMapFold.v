(** * Counted map fold

    This mirror retains each accumulator, stored key, value and computed trie position.
    For example, an accumulator of false does not stop later callback applications.
    Builds on: CollectionsMap and the audit trie enumeration measure. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap
  CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_map_fold_event (K V B E : Type) : Type :=
  | AuditMapFoldNode (node : Trie.ne (K * V)) (acc : B)
  | AuditMapFoldCall (position : positive) (key : K) (value : V)
      (before after : B) (events : list E).

Arguments AuditMapFoldNode {K V B E} _ _.
Arguments AuditMapFoldCall {K V B E} _ _ _ _ _ _.

(** The original position is computed even though [Map.fold] discards it in its callback. *)
Fixpoint audit_map_fold_ne {K V B E} (f : B -> K -> V -> B * list E)
    (path : positive -> positive) (node : Trie.ne (K * V)) (acc : B)
    : B * list (audit_map_fold_event K V B E) :=
  let here := [AuditMapFoldNode node acc] in
  match node with
  | Trie.N001 r =>
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r acc in (out, here ++ re)
  | Trie.N010 (key, value) =>
      let position := path xH in
      let '(out, ce) := f acc key value in
      (out, here ++ [AuditMapFoldCall position key value acc out ce])
  | Trie.N011 (key, value) r =>
      let position := path xH in
      let '(middle, ce) := f acc key value in
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r middle in
      (out, here ++ [AuditMapFoldCall position key value acc middle ce] ++ re)
  | Trie.N100 l =>
      let '(out, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in (out, here ++ le)
  | Trie.N101 l r =>
      let '(middle, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r middle in
      (out, here ++ le ++ re)
  | Trie.N110 l (key, value) =>
      let '(middle, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in
      let position := path xH in
      let '(out, ce) := f middle key value in
      (out, here ++ le ++ [AuditMapFoldCall position key value middle out ce])
  | Trie.N111 l (key, value) r =>
      let '(middle, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in
      let position := path xH in
      let '(next, ce) := f middle key value in
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r next in
      (out, here ++ le ++ [AuditMapFoldCall position key value middle next ce] ++ re)
  end.

Definition audit_map_fold {K V B E} (f : B -> K -> V -> B * list E) (input : Map.t K V)
    (acc : B) : B * list (audit_map_fold_event K V B E) :=
  match input with
  | Trie.Empty => (acc, [])
  | Trie.Nodes node => audit_map_fold_ne f (fun p => p) node acc
  end.

(** Discarding the map fold events recovers the corresponding original operation under its
  premises. *)
Definition audit_map_fold_erases_statement : Prop :=
  forall K V B E (f : B -> K -> V -> B * list E) (original : B -> K -> V -> B)
      (input : Map.t K V) acc,
    (forall b k v, fst (f b k v) = original b k v) ->
    fst (audit_map_fold f input acc) = Map.fold original input acc.

(** Node/call counts do not include the separately expanded callback's body. *)
Definition audit_map_fold_count_statement : Prop :=
  forall K V B E (f : B -> K -> V -> B * list E) (input : Map.t K V) acc,
    length (snd (audit_map_fold f input acc)) <= 2 * audit_trie_nodes input.

(** Fixed node and position charges include actual position reconstruction. *)
Fixpoint audit_map_fold_source_work {K V B E} (child_work : list E -> nat)
    (events : list (audit_map_fold_event K V B E)) : nat :=
  match events with
  | [] => 0
  | AuditMapFoldNode _ _ :: rest => 10 + audit_map_fold_source_work child_work rest
  | AuditMapFoldCall position _ _ _ _ child :: rest =>
      3 + Pos.size_nat position + child_work child + audit_map_fold_source_work child_work rest
  end.

Fixpoint audit_map_fold_child_work {K V B E} (child_work : list E -> nat)
    (events : list (audit_map_fold_event K V B E)) : nat :=
  match events with
  | [] => 0
  | AuditMapFoldCall _ _ _ _ _ child :: rest =>
      child_work child + audit_map_fold_child_work child_work rest
  | _ :: rest => audit_map_fold_child_work child_work rest
  end.

(** The input-derived outer work excludes only the explicitly retained child executions. *)
Definition audit_map_fold_source_work_bound_statement : Prop :=
  forall K V B E (f : B -> K -> V -> B * list E) child_work (input : Map.t K V) acc,
    let events := snd (audit_map_fold f input acc) in
    audit_map_fold_source_work child_work events <=
      13 * audit_trie_nodes input + audit_trie_output_bits input +
      audit_map_fold_child_work child_work events.
