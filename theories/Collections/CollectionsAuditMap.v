(** * Counted encoded map calls

    These mirrors compose real encoding calls with trie lookups, writes and removals.
    For example, a missing key still records its actual code and selected trie path.
    Builds on: CollectionsMap and the audit trie model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap
  CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

Inductive audit_map_event (K V E : Type) : Type :=
  | AuditMapGet (key : K) (code : positive) (input : Map.t K V) (output : option V)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * V)))
  | AuditMapSet (key : K) (value : V) (code : positive) (input output : Map.t K V)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * V)))
  | AuditMapRemove (key : K) (code : positive) (input output : Map.t K V)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * V))).

Arguments AuditMapGet {K V E} _ _ _ _ _ _.
Arguments AuditMapSet {K V E} _ _ _ _ _ _ _.
Arguments AuditMapRemove {K V E} _ _ _ _ _ _.

(** Lookup composes the encoder and code lookup on precisely the returned code. *)
Definition audit_map_get {K V E} (enc : K -> positive * list E) (key : K) (input : Map.t K V)
    : option V * list (audit_map_event K V E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_map_code_get code input in
  (output, [AuditMapGet key code input output ee te]).

Definition audit_map_set {K V E} (enc : K -> positive * list E)
    (key : K) (value : V) (input : Map.t K V)
    : Map.t K V * list (audit_map_event K V E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_set code (key, value) input in
  (output, [AuditMapSet key value code input output ee te]).

Definition audit_map_remove {K V E} (enc : K -> positive * list E)
    (key : K) (input : Map.t K V) : Map.t K V * list (audit_map_event K V E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_remove code input in
  (output, [AuditMapRemove key code input output ee te]).

(** * Future proof obligations *)

Definition audit_map_get_erases_statement : Prop :=
  forall K V E (enc : K -> positive * list E) (original : encoding K) key (input : Map.t K V),
    fst (enc key) = encode original key -> fst (audit_map_get enc key input) = Map.get original
      key input.

(** Discarding the map set events recovers the corresponding original operation under its
  premises. *)
Definition audit_map_set_erases_statement : Prop :=
  forall K V E (enc : K -> positive * list E) (original : encoding K) key value
      (input : Map.t K V),
    fst (enc key) = encode original key ->
    fst (audit_map_set enc key value input) = Map.set original key value input.

(** Discarding the map remove events recovers the corresponding original operation under its
  premises. *)
Definition audit_map_remove_erases_statement : Prop :=
  forall K V E (enc : K -> positive * list E) (original : encoding K) key (input : Map.t K V),
    fst (enc key) = encode original key ->
    fst (audit_map_remove enc key input) = Map.remove original key input.

(** * Same-call fixed source-frame folds *)

(** The encoder fold observes its actual child trace; internal bodies need their own proof. *)
Fixpoint audit_map_source_work {K V E} (encoder_work : list E -> nat)
    (events : list (audit_map_event K V E)) : nat :=
  match events with
  | [] => 0
  | AuditMapGet _ _ _ output enc_events trie_events :: rest =>
      1 + encoder_work enc_events + audit_trie_get_trace_source_work trie_events +
        (match output with
        | None => 2
        | Some _ => 4
        end) + audit_map_source_work encoder_work rest
  | AuditMapSet _ _ _ _ _ enc_events trie_events :: rest =>
      2 + encoder_work enc_events + audit_trie_update_trace_source_work trie_events +
        audit_map_source_work encoder_work rest
  | AuditMapRemove _ _ _ _ enc_events trie_events :: rest =>
      2 + encoder_work enc_events + audit_trie_update_trace_source_work trie_events +
        audit_map_source_work encoder_work rest
  end.

(** Bounds refer to the actual input key and actual child encoding trace, not a client price law. *)
Definition audit_map_get_source_work_bound_statement : Prop :=
  forall K V E (enc : K -> positive * list E) encoder_work key (input : Map.t K V),
    audit_map_source_work encoder_work (snd (audit_map_get enc key input)) <=
      5 + encoder_work (snd (enc key)) + 5 * Pos.size_nat (fst (enc key)).

(** Map insertion work is bounded by encoder work and the encoded key width. *)
Definition audit_map_set_source_work_bound_statement : Prop :=
  forall K V E (enc : K -> positive * list E) encoder_work key value (input : Map.t K V),
    audit_map_source_work encoder_work (snd (audit_map_set enc key value input)) <=
      2 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)).

(** Map removal work is bounded by encoder work and the encoded key width. *)
Definition audit_map_remove_source_work_bound_statement : Prop :=
  forall K V E (enc : K -> positive * list E) encoder_work key (input : Map.t K V),
    audit_map_source_work encoder_work (snd (audit_map_remove enc key input)) <=
      2 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)).
