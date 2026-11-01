(** * Counted canonical trie calls

    These candidate operations retain the real path, operands and results of trie primitives.
    For example, an absent lookup still visits every bit of its positive key.
    Builds on: CollectionsTrie, CollectionsMap and the audit event vocabulary. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap
  CollectionsAuditCost.
Import List.ListNotations.

(** * Typed primitive events *)

Inductive audit_trie_call (A : Type) : Type :=
  | AuditTrieKey (key : positive) (input : Trie.t A)
  | AuditTrieLeft (input output : Trie.t A)
  | AuditTrieRight (input output : Trie.t A)
  | AuditTrieValue (input : Trie.t A) (output : option A)
  | AuditTrieNode (left : Trie.t A) (value : option A) (right output : Trie.t A).

Arguments AuditTrieKey {A} _ _.
Arguments AuditTrieLeft {A} _ _.
Arguments AuditTrieRight {A} _ _.
Arguments AuditTrieValue {A} _ _.
Arguments AuditTrieNode {A} _ _ _ _.

(** A lookup follows the original key and emits each selected accessor with its result. *)
Polymorphic Fixpoint audit_trie_get {A} (key : positive) (input : Trie.t A)
    : option A * audit_trace (audit_trie_call A) :=
  match key with
  | xH =>
      let value := Trie.value input in
      (value, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieValue input value)])
  | xO rest =>
      let left := Trie.left input in
      let '(result, events) := audit_trie_get rest left in
      (result, AuditCall (AuditTrieKey key input) :: AuditCall (AuditTrieLeft input left) :: events)
  | xI rest =>
      let right := Trie.right input in
      let '(result, events) := audit_trie_get rest right in
      (result, AuditCall (AuditTrieKey key input) ::
        AuditCall (AuditTrieRight input right) :: events)
  end.

(** Setting and removal share the source control flow; [value] fixes the actual leaf update. *)
Polymorphic Fixpoint audit_trie_update {A} (key : positive) (value : option A) (input : Trie.t A)
    : Trie.t A * audit_trace (audit_trie_call A) :=
  match key with
  | xH =>
      let left := Trie.left input in
      let right := Trie.right input in
      let output := Trie.node left value right in
      (output, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieLeft input left);
                AuditCall (AuditTrieRight input right);
                AuditCall (AuditTrieNode left value right output)])
  | xO rest =>
      let left := Trie.left input in
      let '(updated, events) := audit_trie_update rest value left in
      let old := Trie.value input in
      let right := Trie.right input in
      let output := Trie.node updated old right in
      (output, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieLeft input left)] ++
        events ++ [AuditCall (AuditTrieValue input old); AuditCall (AuditTrieRight input right);
                   AuditCall (AuditTrieNode updated old right output)])
  | xI rest =>
      let left := Trie.left input in
      let old := Trie.value input in
      let right := Trie.right input in
      let '(updated, events) := audit_trie_update rest value right in
      let output := Trie.node left old updated in
      (output, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieLeft input left);
                AuditCall (AuditTrieValue input old); AuditCall (AuditTrieRight input right)] ++
        events ++ [AuditCall (AuditTrieNode left old updated output)])
  end.

(** These wrappers retain the actual updated value or removal. *)
Polymorphic Definition audit_trie_set {A} (key : positive) (value : A) (input : Trie.t A)
    : Trie.t A * audit_trace (audit_trie_call A) := audit_trie_update key (Some value) input.

Definition audit_trie_remove {A} (key : positive) (input : Trie.t A)
    : Trie.t A * audit_trace (audit_trie_call A) := audit_trie_update key None input.

(** Map code lookup preserves the exact stored-pair lookup, including its discarded key. *)
Polymorphic Definition audit_map_code_get {K V} (key : positive) (input : Map.t K V)
    : option V * audit_trace (audit_trie_call (K * V)) :=
  let '(result, events) := audit_trie_get key input in
  (option_map snd result, events).

(** * Future implementation obligations *)

(** Erasure preserves each original public operation for all keys and tries. *)
Definition audit_trie_get_erases_statement : Prop :=
  forall A key (input : Trie.t A), fst (audit_trie_get key input) = Trie.get key input.

(** Discarding the trie set events recovers the corresponding original operation under its
  premises. *)
Definition audit_trie_set_erases_statement : Prop :=
  forall A key (value : A) input, fst (audit_trie_set key value input) = Trie.set key value input.

(** Discarding the trie remove events recovers the corresponding original operation under its
  premises. *)
Definition audit_trie_remove_erases_statement : Prop :=
  forall A key (input : Trie.t A), fst (audit_trie_remove key input) = Trie.remove key input.

(** Discarding the map code get events recovers the corresponding original operation under its
  premises. *)
Definition audit_map_code_get_erases_statement : Prop :=
  forall K V key (input : Map.t K V), fst (audit_map_code_get key input) = Map.code_get key input.

(** The number of selected typed events is bounded by the input key length. *)
Definition audit_trie_get_events_bound_statement : Prop :=
  forall A key (input : Trie.t A),
    audit_work (snd (audit_trie_get key input)) = 2 * Pos.size_nat key.

(** Trie update emits at most five events per key bit. *)
Definition audit_trie_update_events_bound_statement : Prop :=
  forall A key (value : option A) input,
    audit_work (snd (audit_trie_update key value input)) <= 5 * Pos.size_nat key.

(** * Fixed source-frame accounting *)

(** Each selected accessor inspects its outer constructor and, for nodes, its inner constructor. *)
Definition audit_trie_accessor_work {A} (input : Trie.t A) : nat :=
  match input with
  | Trie.Empty => 1
  | Trie.Nodes _ => 2
  end.

(** Node inspection charges three inputs and the selected output constructor frames. *)
Definition audit_trie_node_work {A} (left : Trie.t A) (value : option A) (right : Trie.t A)
    : nat :=
  match left, value, right with
  | Trie.Empty, None, Trie.Empty => 4
  | _, _, _ => 5
  end.

(** Lookup charges the fixpoint/match and each selected accessor and recursive application. *)
Fixpoint audit_trie_get_source_work {A} (key : positive) (input : Trie.t A) : nat :=
  match key with
  | xH => 2 + audit_trie_accessor_work input
  | xO rest => 3 + audit_trie_accessor_work input +
      audit_trie_get_source_work rest (Trie.left input)
  | xI rest => 3 + audit_trie_accessor_work input +
      audit_trie_get_source_work rest (Trie.right input)
  end.

(** Update charges all three strict node operands, selected accessors, recursion and rebuilding. *)
Fixpoint audit_trie_update_source_work {A} (key : positive) (value : option A)
    (input : Trie.t A) : nat :=
  match key with
  | xH => 5 + 2 * audit_trie_accessor_work input +
      audit_trie_node_work (Trie.left input) value (Trie.right input)
  | xO rest => 5 + 3 * audit_trie_accessor_work input +
      audit_trie_update_source_work rest value (Trie.left input) +
      audit_trie_node_work (fst (audit_trie_update rest value (Trie.left input)))
        (Trie.value input) (Trie.right input)
  | xI rest => 5 + 3 * audit_trie_accessor_work input +
      audit_trie_update_source_work rest value (Trie.right input) +
      audit_trie_node_work (Trie.left input) (Trie.value input)
        (fst (audit_trie_update rest value (Trie.right input)))
  end.

(** Bounds use only the original positive key, not the counted result or trace. *)
Definition audit_trie_get_source_work_bound_statement : Prop :=
  forall A key (input : Trie.t A), audit_trie_get_source_work key input <= 5 * Pos.size_nat key.

(** Trie update source work is at most sixteen times the key width. *)
Definition audit_trie_update_source_work_bound_statement : Prop :=
  forall A key (value : option A) input,
    audit_trie_update_source_work key value input <= 16 * Pos.size_nat key.

(** * Source-indexed derivations *)

(** The derivation fixes the selected source branch, returned result, trace and local charge. *)
Inductive audit_trie_get_run {A} : positive -> Trie.t A -> option A ->
    audit_trace (audit_trie_call A) -> nat -> Prop :=
  | AuditGetHere : forall input,
      audit_trie_get_run xH input (Trie.value input)
        [AuditCall (AuditTrieKey xH input); AuditCall (AuditTrieValue input (Trie.value input))]
        (2 + audit_trie_accessor_work input)
  | AuditGetLeft : forall rest input result events work,
      audit_trie_get_run rest (Trie.left input) result events work ->
      audit_trie_get_run (xO rest) input result
        (AuditCall (AuditTrieKey (xO rest) input) ::
         AuditCall (AuditTrieLeft input (Trie.left input)) :: events)
        (3 + audit_trie_accessor_work input + work)
  | AuditGetRight : forall rest input result events work,
      audit_trie_get_run rest (Trie.right input) result events work ->
      audit_trie_get_run (xI rest) input result
        (AuditCall (AuditTrieKey (xI rest) input) ::
         AuditCall (AuditTrieRight input (Trie.right input)) :: events)
        (3 + audit_trie_accessor_work input + work).

(** A trie lookup run agrees with the counted and original results and bounds its work. *)
Definition audit_trie_get_run_correct_statement : Prop :=
  forall A key (input : Trie.t A) result events work,
    audit_trie_get_run key input result events work ->
    result = Trie.get key input /\
    (result, events) = audit_trie_get key input /\
    work = audit_trie_get_source_work key input /\
    work <= 5 * Pos.size_nat key.

(** Every trie get input has a corresponding source run. *)
Definition audit_trie_get_run_total_statement : Prop :=
  forall A key (input : Trie.t A),
    exists result events work, audit_trie_get_run key input result events work.

(** The update derivation retains the exact child result used to construct the parent node. *)
Inductive audit_trie_update_run {A} : positive -> option A -> Trie.t A -> Trie.t A ->
    audit_trace (audit_trie_call A) -> nat -> Prop :=
  | AuditUpdateHere : forall value input,
      audit_trie_update_run xH value input (Trie.node (Trie.left input) value (Trie.right input))
        [AuditCall (AuditTrieKey xH input); AuditCall (AuditTrieLeft input (Trie.left input));
         AuditCall (AuditTrieRight input (Trie.right input));
         AuditCall (AuditTrieNode (Trie.left input) value (Trie.right input)
           (Trie.node (Trie.left input) value (Trie.right input)))]
        (5 + 2 * audit_trie_accessor_work input +
          audit_trie_node_work (Trie.left input) value (Trie.right input))
  | AuditUpdateLeft : forall rest value input child child_events child_work,
      audit_trie_update_run rest value (Trie.left input) child child_events child_work ->
      audit_trie_update_run (xO rest) value input
        (Trie.node child (Trie.value input) (Trie.right input))
        ([AuditCall (AuditTrieKey (xO rest) input);
          AuditCall (AuditTrieLeft input (Trie.left input))] ++ child_events ++
         [AuditCall (AuditTrieValue input (Trie.value input));
          AuditCall (AuditTrieRight input (Trie.right input));
          AuditCall (AuditTrieNode child (Trie.value input) (Trie.right input)
            (Trie.node child (Trie.value input) (Trie.right input)))])
        (5 + 3 * audit_trie_accessor_work input + child_work +
          audit_trie_node_work child (Trie.value input) (Trie.right input))
  | AuditUpdateRight : forall rest value input child child_events child_work,
      audit_trie_update_run rest value (Trie.right input) child child_events child_work ->
      audit_trie_update_run (xI rest) value input
        (Trie.node (Trie.left input) (Trie.value input) child)
        ([AuditCall (AuditTrieKey (xI rest) input);
          AuditCall (AuditTrieLeft input (Trie.left input));
          AuditCall (AuditTrieValue input (Trie.value input));
          AuditCall (AuditTrieRight input (Trie.right input))] ++ child_events ++
         [AuditCall (AuditTrieNode (Trie.left input) (Trie.value input) child
            (Trie.node (Trie.left input) (Trie.value input) child))])
        (5 + 3 * audit_trie_accessor_work input + child_work +
          audit_trie_node_work (Trie.left input) (Trie.value input) child).

(** A trie update source run agrees with the counted result and its work bounds. *)
Definition audit_trie_update_run_correct_statement : Prop :=
  forall A key (value : option A) input result events work,
    audit_trie_update_run key value input result events work ->
    (result, events) = audit_trie_update key value input /\
    work = audit_trie_update_source_work key value input /\
    work <= 16 * Pos.size_nat key.

(** Every trie update input has a corresponding source run. *)
Definition audit_trie_update_run_total_statement : Prop :=
  forall A key (value : option A) input,
    exists result events work, audit_trie_update_run key value input result events work.

(** * Same-trace source-frame folds *)

(** The lookup and update sites differ, so each fold uses its fixed source-specific charges. *)
Polymorphic Fixpoint audit_trie_get_trace_source_work {A}
    (events : audit_trace (audit_trie_call A)) : nat :=
  match events with
  | [] => 0
  | AuditCall (AuditTrieKey key _) :: rest =>
      (match key with
      | xH => 2
      | _ => 3
      end) + audit_trie_get_trace_source_work rest
  | AuditCall (AuditTrieLeft input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_get_trace_source_work rest
  | AuditCall (AuditTrieRight input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_get_trace_source_work rest
  | AuditCall (AuditTrieValue input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_get_trace_source_work rest
  | _ :: rest => audit_trie_get_trace_source_work rest
  end.

Polymorphic Fixpoint audit_trie_update_trace_source_work {A}
    (events : audit_trace (audit_trie_call A)) : nat :=
  match events with
  | [] => 0
  | AuditCall (AuditTrieKey _ _) :: rest => 5 + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieLeft input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieRight input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieValue input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieNode l value r _) :: rest =>
      audit_trie_node_work l value r + audit_trie_update_trace_source_work rest
  | _ :: rest => audit_trie_update_trace_source_work rest
  end.

(** The lookup trace work equals the work computed directly from its input. *)
Definition audit_trie_get_trace_adequate_statement : Prop :=
  forall A key (input : Trie.t A),
    audit_trie_get_trace_source_work (snd (audit_trie_get key input)) =
      audit_trie_get_source_work key input.

(** The update trace work equals the work computed directly from its input. *)
Definition audit_trie_update_trace_adequate_statement : Prop :=
  forall A key (value : option A) input,
    audit_trie_update_trace_source_work (snd (audit_trie_update key value input)) =
      audit_trie_update_source_work key value input.
