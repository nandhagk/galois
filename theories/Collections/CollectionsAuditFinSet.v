(** * Counted finite-set construction

    These mirrors preserve each actual encoded key, intermediate set and trie operation.
    For example, repeated input keys retain separate insertion events.
    Builds on: CollectionsFinSet and the audit trie model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

(** * Actual update and lookup calls *)

Inductive audit_set_event (K E : Type) : Type :=
  | AuditSetAdd (key : K) (code : positive) (input output : FinSet.t K)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * unit)))
  | AuditSetMem (key : K) (code : positive) (input : FinSet.t K) (output : bool)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * unit)))
  | AuditSetRemove (key : K) (code : positive) (input output : FinSet.t K)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * unit)))
  | AuditSetFold (remaining : list K) (input : FinSet.t K).

Arguments AuditSetAdd {K E} _ _ _ _ _ _.
Arguments AuditSetMem {K E} _ _ _ _ _ _.
Arguments AuditSetRemove {K E} _ _ _ _ _ _.
Arguments AuditSetFold {K E} _ _.

(** Add retains the concrete encoded key, source trie input and rebuilt trie. *)
Definition audit_finset_add {K E} (enc : K -> positive * list E) (key : K) (input : FinSet.t K)
    : FinSet.t K * list (audit_set_event K E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_set code (key, tt) input in
  (output, [AuditSetAdd key code input output ee te]).

Definition audit_finset_mem {K E} (enc : K -> positive * list E) (key : K) (input : FinSet.t K)
    : bool * list (audit_set_event K E) :=
  let '(code, ee) := enc key in
  let '(found, te) := audit_map_code_get code input in
  let output := match found with
  | Some _ => true
  | None => false
  end in
  (output, [AuditSetMem key code input output ee te]).

Definition audit_finset_remove {K E}
    (enc : K -> positive * list E) (key : K) (input : FinSet.t K)
    : FinSet.t K * list (audit_set_event K E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_remove code input in
  (output, [AuditSetRemove key code input output ee te]).

(** This fold keeps the actual accumulator at every occurrence and at termination. *)
Fixpoint audit_finset_fold {K E} (enc : K -> positive * list E)
    (remaining : list K) (input : FinSet.t K) : FinSet.t K * list (audit_set_event K E) :=
  match remaining with
  | [] => (input, [AuditSetFold remaining input])
  | key :: rest =>
      let '(next, call) := audit_finset_add enc key input in
      let '(output, events) := audit_finset_fold enc rest next in
      (output, AuditSetFold remaining input :: call ++ events)
  end.

Definition audit_finset_of_list {K E} (enc : K -> positive * list E) (input : list K)
    : FinSet.t K * list (audit_set_event K E) := audit_finset_fold enc input FinSet.empty.

(** * Future proof obligations *)

Definition audit_finset_of_list_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) (input : list K),
    (forall key, In key input -> fst (enc key) = encode original key) ->
    fst (audit_finset_of_list enc input) = FinSet.of_list original input.

(** Set construction emits one terminal frame and two events per input occurrence. *)
Definition audit_finset_of_list_count_statement : Prop :=
  forall K E (enc : K -> positive * list E) (input : list K),
    length (snd (audit_finset_of_list enc input)) = S (2 * length input).

(** Discarding the finset add events recovers the corresponding original operation under its
  premises. *)
Definition audit_finset_add_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) key input,
    fst (enc key) = encode original key ->
    fst (audit_finset_add enc key input) = FinSet.add original key input.

(** Discarding the finset mem events recovers the corresponding original operation under its
  premises. *)
Definition audit_finset_mem_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) key input,
    fst (enc key) = encode original key ->
    fst (audit_finset_mem enc key input) = FinSet.mem original key input.

(** Discarding the finset remove events recovers the corresponding original operation under its
  premises. *)
Definition audit_finset_remove_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) key input,
    fst (enc key) = encode original key ->
    fst (audit_finset_remove enc key input) = FinSet.remove original key input.

(** * Fixed source-frame charges and original-key budget *)

Fixpoint audit_finset_source_work {K E} (encoder_work : list E -> nat)
    (events : list (audit_set_event K E)) : nat :=
  match events with
  | [] => 0
  | AuditSetAdd _ _ _ _ ee te :: rest =>
      2 + encoder_work ee + audit_trie_update_trace_source_work te +
        audit_finset_source_work encoder_work rest
  | AuditSetMem _ _ _ output ee te :: rest =>
      2 + encoder_work ee + audit_trie_get_trace_source_work te +
        (if output then 4 else 2) + audit_finset_source_work encoder_work rest
  | AuditSetRemove _ _ _ _ ee te :: rest =>
      2 + encoder_work ee + audit_trie_update_trace_source_work te +
        audit_finset_source_work encoder_work rest
  | AuditSetFold _ _ :: rest => 1 + audit_finset_source_work encoder_work rest
  end.

Fixpoint audit_finset_of_list_budget {K E} (enc : K -> positive * list E)
    (encoder_work : list E -> nat) (input : list K) : nat :=
  match input with
  | [] => 1
  | key :: rest =>
      3 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
        audit_finset_of_list_budget enc encoder_work rest
  end.

(** The finset of list work is bounded by [audit_finset_of_list_budget]. *)
Definition audit_finset_of_list_source_bound_statement : Prop :=
  forall K E (enc : K -> positive * list E) encoder_work input,
    audit_finset_source_work encoder_work (snd (audit_finset_of_list enc input)) <=
      audit_finset_of_list_budget enc encoder_work input.
