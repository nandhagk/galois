(** * Independent collection callback budgets and actual source calls

    These bounds charge map, union and fold callbacks at their actual values and accumulators.
    For example, a fold callback changes the accumulator used by the rhs subtree's budget.
    Builds on: source-shaped traversal models and genuine foreign callback adapters. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap
  CollectionsAuditCallback
  CollectionsAuditElements
  CollectionsAuditMapTraverse
  CollectionsAuditMapFold.
Import List.ListNotations.

Definition audit_map_transform_calls_source {K V W E}
    (work : list E -> nat) (source : V -> W -> list E -> nat -> Prop)
    (events : list (audit_map_transform_event K V W E)) : Prop :=
  Forall (fun event => match event with
    | AuditMapTransformCall _ input output body => source input output body (work body)
    | _ => True
    end) events.

Definition audit_map_union_calls_source {K V E} (work : list E -> nat)
    (source : V * V -> V -> list E -> nat -> Prop)
    (events : list (audit_map_union_event K V E)) : Prop :=
  Forall (fun event => match event with
    | AuditMapUnionCall _ _ lhs rhs output body => source (lhs, rhs) output body (work body)
    | _ => True
    end) events.

Definition audit_map_fold_calls_source {K V B E} (work : list E -> nat)
    (source : B * (K * V) -> B -> list E -> nat -> Prop)
    (events : list (audit_map_fold_event K V B E)) : Prop :=
  Forall (fun event => match event with
    | AuditMapFoldCall _ key value before after body =>
        source (before, (key, value)) after body (work body)
    | _ => True
    end) events.

Definition audit_map_transform_input_budget {K V} (budget : V -> nat) (input : Map.t K V) : nat :=
  18 * audit_trie_nodes input +
    fold_right (fun binding total => budget (snd binding) + total) 0 (Map.elements input).

Definition audit_map_union_input_budget {K V} (budget : V * V -> nat)
    (lhs rhs : Map.t K V) : nat :=
  1 + 18 * audit_trie_nodes lhs +
    fold_right (fun first total =>
      fold_right (fun second subtotal => budget (snd first, snd second) + subtotal) 0
        (Map.elements rhs) + total) 0 (Map.elements lhs).

(** The independent fold recurrence has no event trace or returned event-work projection. *)
Fixpoint audit_map_fold_input_budget_ne {K V B E} (call : B -> K -> V -> B * list E)
    (budget : B * (K * V) -> nat) (path : positive -> positive)
    (node : Trie.ne (K * V)) (acc : B) : B * nat :=
  let cost := fun before key value => 3 + Pos.size_nat (path xH) + budget (before, (key, value)) in
  match node with
  | Trie.N001 rhs =>
      let '(out, rest) := audit_map_fold_input_budget_ne call budget (fun p => path (xI p)) rhs
        acc in
      (out, 10 + rest)
  | Trie.N010 (key, value) => (fst (call acc key value), 10 + cost acc key value)
  | Trie.N011 (key, value) rhs =>
      let middle := fst (call acc key value) in
      let '(out, rest) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xI p)) rhs middle in
      (out, 10 + cost acc key value + rest)
  | Trie.N100 lhs =>
      let '(out, rest) := audit_map_fold_input_budget_ne call budget (fun p => path (xO p)) lhs
        acc in
      (out, 10 + rest)
  | Trie.N101 lhs rhs =>
      let '(middle, first) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xO p)) lhs acc in
      let '(out, second) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xI p)) rhs middle in
      (out, 10 + first + second)
  | Trie.N110 lhs (key, value) =>
      let '(middle, first) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xO p)) lhs acc in
      (fst (call middle key value), 10 + first + cost middle key value)
  | Trie.N111 lhs (key, value) rhs =>
      let '(middle, first) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xO p)) lhs acc in
      let next := fst (call middle key value) in
      let '(out, second) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xI p)) rhs next in
      (out, 10 + first + cost middle key value + second)
  end.

Definition audit_map_fold_input_budget {K V B E} (call : B -> K -> V -> B * list E)
    (budget : B * (K * V) -> nat) (input : Map.t K V) (acc : B) : nat :=
  match input with
  | Trie.Empty => 0
  | Trie.Nodes node => snd (audit_map_fold_input_budget_ne call budget (fun p => p) node acc)
  end.

(** The mapper's source law covers each actual retained value, result and body. *)
Definition audit_map_transform_adapted_input_bound_statement : Prop :=
  forall K V W E (call : V -> W * list E) work source budget (input : Map.t K V),
    audit_external_callback_adapter call work source budget ->
    let events := snd (audit_map_transform call input) in
    audit_map_transform_calls_source work source events /\
    audit_map_transform_source_work work events <= audit_map_transform_input_budget budget input.

(** Union pays every overlap call from the original input values, including distinct stored keys. *)
Definition audit_map_union_adapted_input_bound_statement : Prop :=
  forall K V E (call : V -> V -> V * list E) work source budget (lhs rhs : Map.t K V),
    audit_external_callback_adapter (fun pair => call (fst pair) (snd pair)) work source budget ->
    let events := snd (audit_map_union call lhs rhs) in
    audit_map_union_calls_source work source events /\
    audit_map_union_source_work work events <= audit_map_union_input_budget budget lhs rhs.

(** Fold source and cost use the exact accumulator immediately before every actual callback. *)
Definition audit_map_fold_adapted_input_bound_statement : Prop :=
  forall K V B E (call : B -> K -> V -> B * list E) work source budget
      (input : Map.t K V) (acc : B),
    audit_external_callback_adapter
      (fun args => call (fst args) (fst (snd args)) (snd (snd args))) work source budget ->
    let events := snd (audit_map_fold call input acc) in
    audit_map_fold_calls_source work source events /\
    audit_map_fold_source_work work events <= audit_map_fold_input_budget call budget input acc.
