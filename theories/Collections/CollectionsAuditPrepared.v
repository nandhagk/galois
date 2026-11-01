(** * Counted prepared-key operations

    These observers retain the actual initial encoding and subsequent direct trie operations.
    For example, repeated lookups reuse the prepared code without re-encoding the key.
    Builds on: G4 prepared keys and the shared trie and map observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap
  CollectionsAuditState
  CollectionsAuditCost
  CollectionsAuditTrie.
Import List.ListNotations.

Inductive audit_prepared_event (K V CE : Type) : Type :=
  | AuditPreparedEncode (key : K) (code : positive) (events : list CE)
  | AuditPreparedRead (code : positive) (result : option V)
      (events : audit_trace (audit_trie_call (K * V)))
  | AuditPreparedWrite (code : positive) (events : audit_trace (audit_trie_call (K * V)))
  | AuditPreparedRemove (code : positive) (events : audit_trace (audit_trie_call (K * V))).

Arguments AuditPreparedEncode {K V CE} _ _ _.
Arguments AuditPreparedRead {K V CE} _ _ _.
Arguments AuditPreparedWrite {K V CE} _ _.
Arguments AuditPreparedRemove {K V CE} _ _.

(** Preparation records the actual encoder invocation and returned positive code. *)
Definition audit_prepare_key {K V CE} (enc : K -> positive * list CE) (key : K)
    : prepared_key K * list (audit_prepared_event K V CE) :=
  let '(code, events) := enc key in (PreparedKey key code, [AuditPreparedEncode key code events]).

Definition audit_prepared_lookup {K V CE} (key : prepared_key K) (m : Map.t K V)
    : option V * list (audit_prepared_event K V CE) :=
  let '(result, events) := audit_map_code_get (key_code key) m in
  (result, [AuditPreparedRead (key_code key) result events]).

Definition audit_prepared_update {K V CE} (key : prepared_key K) (value : V) (m : Map.t K V)
    : Map.t K V * list (audit_prepared_event K V CE) :=
  let '(result, events) := audit_trie_set (key_code key) (key_value key, value) m in
  (result, [AuditPreparedWrite (key_code key) events]).

Definition audit_prepared_remove {K V CE} (key : prepared_key K) (m : Map.t K V)
    : Map.t K V * list (audit_prepared_event K V CE) :=
  let '(result, events) := audit_trie_remove (key_code key) m in
  (result, [AuditPreparedRemove (key_code key) events]).

(** The direct operation erasure claims require no validity premise. *)
Definition audit_prepare_key_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) key,
    fst (enc key) = encode original key -> fst (@audit_prepare_key K V CE enc key) =
      prepare_key original key.

(** Discarding the prepared lookup events recovers the corresponding original operation under
  its premises. *)
Definition audit_prepared_lookup_erases_statement : Prop :=
  forall K V CE (key : prepared_key K) (m : Map.t K V),
    fst (@audit_prepared_lookup K V CE key m) = prepared_lookup key m.

(** Discarding the prepared update events recovers the corresponding original operation under
  its premises. *)
Definition audit_prepared_update_erases_statement : Prop :=
  forall K V CE (key : prepared_key K) value (m : Map.t K V),
    fst (@audit_prepared_update K V CE key value m) = prepared_update key value m.

(** Discarding the prepared remove events recovers the corresponding original operation under
  its premises. *)
Definition audit_prepared_remove_erases_statement : Prop :=
  forall K V CE (key : prepared_key K) (m : Map.t K V),
    fst (@audit_prepared_remove K V CE key m) = prepared_remove key m.

(** Fixed direct-operation work retains each exact child trace. *)
Fixpoint audit_prepared_source_work {K V CE} (enc_work : list CE -> nat)
    (events : list (audit_prepared_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditPreparedEncode _ _ child :: rest => 1 + enc_work child + audit_prepared_source_work
    enc_work rest
  | AuditPreparedRead _ result child :: rest =>
      2 + (match result with
      | None => 2
      | Some _ => 4
      end) + audit_trie_get_trace_source_work child +
      audit_prepared_source_work enc_work rest
  | AuditPreparedWrite _ child :: rest => 2 + audit_trie_update_trace_source_work child +
      audit_prepared_source_work enc_work rest
  | AuditPreparedRemove _ child :: rest => 2 + audit_trie_update_trace_source_work child +
      audit_prepared_source_work enc_work rest
  end.

(** Prepared lookup work is bounded by a constant plus five times the key-code width. *)
Definition audit_prepared_lookup_source_bound_statement : Prop :=
  forall K V CE enc_work (key : prepared_key K) (m : Map.t K V),
    audit_prepared_source_work enc_work (snd (@audit_prepared_lookup K V CE key m)) <=
      6 + 5 * Pos.size_nat (key_code key).

(** Prepared update work is bounded by a constant plus sixteen times the key-code width. *)
Definition audit_prepared_update_source_bound_statement : Prop :=
  forall K V CE enc_work (key : prepared_key K) value (m : Map.t K V),
    audit_prepared_source_work enc_work (snd (@audit_prepared_update K V CE key value m)) <=
      2 + 16 * Pos.size_nat (key_code key).

(** Prepared removal work is bounded by a constant plus sixteen times the key-code width. *)
Definition audit_prepared_remove_source_bound_statement : Prop :=
  forall K V CE enc_work (key : prepared_key K) (m : Map.t K V),
    audit_prepared_source_work enc_work (snd (@audit_prepared_remove K V CE key m)) <=
      2 + 16 * Pos.size_nat (key_code key).

(** Prepared operations contain no encoder call; preparation itself has exactly one. *)
Fixpoint audit_prepared_encoder_calls {K V CE} (events : list (audit_prepared_event K V CE)) :
  nat :=
  match events with
  | [] => 0
  | AuditPreparedEncode _ _ _ :: rest => S (audit_prepared_encoder_calls rest)
  | _ :: rest => audit_prepared_encoder_calls rest
  end.

(** Preparing once and reusing a key avoids additional encoder calls in prepared operations. *)
Definition audit_prepared_encoder_reuse_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (key : prepared_key K) (m : Map.t K V) value,
    audit_prepared_encoder_calls (snd (@audit_prepare_key K V CE enc (key_value key))) = 1 /\
    audit_prepared_encoder_calls (snd (@audit_prepared_lookup K V CE key m)) = 0 /\
    audit_prepared_encoder_calls (snd (@audit_prepared_update K V CE key value m)) = 0 /\
    audit_prepared_encoder_calls (snd (@audit_prepared_remove K V CE key m)) = 0.
