(** * Prepared-key observer adequacy

    Prepared operations preserve their source results and charge their direct trie paths.
    For example, repeated reads do not invoke the encoder again.
    Builds on: CollectionsAuditPrepared and trie adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsAuditState CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditPrepared.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** If the encoder agrees at the key, discarding preparation events returns the original
    prepared key. *)
Theorem audit_prepare_key_erases : audit_prepare_key_erases_statement.
Proof.
  intros K V CE enc original key Hencode.
  unfold audit_prepare_key, prepare_key.
  destruct (enc key) as [code events]; cbn in *. now rewrite Hencode.
Qed.

(** Discarding events from a prepared lookup returns the direct code lookup for any prepared
    key. *)
Theorem audit_prepared_lookup_erases : audit_prepared_lookup_erases_statement.
Proof.
  intros K V CE key m.
  pose proof (audit_map_code_get_erases K V (key_code key) m) as Hresult.
  unfold audit_prepared_lookup, prepared_lookup.
  destruct (audit_map_code_get (key_code key) m); exact Hresult.
Qed.

(** Discarding events from a prepared update returns the persistent insertion for any prepared
    key. *)
Theorem audit_prepared_update_erases : audit_prepared_update_erases_statement.
Proof.
  intros K V CE key value m.
  pose proof (audit_trie_set_erases (K * V)%type (key_code key) (key_value key, value) m)
    as Hresult.
  unfold audit_prepared_update, prepared_update.
  destruct (audit_trie_set (key_code key) (key_value key, value) m); exact Hresult.
Qed.

(** Discarding events from a prepared removal returns the persistent removal for any prepared
    key. *)
Theorem audit_prepared_remove_erases : audit_prepared_remove_erases_statement.
Proof.
  intros K V CE key m.
  pose proof (audit_trie_remove_erases (K * V)%type (key_code key) m) as Hresult.
  unfold audit_prepared_remove, prepared_remove.
  destruct (audit_trie_remove (key_code key) m); exact Hresult.
Qed.

(** Prepared-lookup source work is bounded by a constant plus five times the stored code width. *)
Theorem audit_prepared_lookup_source_bound : audit_prepared_lookup_source_bound_statement.
Proof.
  intros K V CE enc_work key m.
  unfold audit_prepared_lookup, audit_map_code_get.
  pose proof (audit_trie_get_trace_adequate (K * V)%type (key_code key) m) as Htrace.
  pose proof (audit_trie_get_source_work_bound (K * V)%type (key_code key) m) as Hbound.
  destruct (audit_trie_get (key_code key) m) as [found events].
  cbn [snd] in Htrace; destruct found; cbn [snd option_map audit_prepared_source_work]; lia.
Qed.

(** Prepared-update source work is bounded by a constant plus sixteen times the stored code
    width. *)
Theorem audit_prepared_update_source_bound : audit_prepared_update_source_bound_statement.
Proof.
  intros K V CE enc_work key value m.
  pose proof (audit_trie_update_trace_adequate (K * V)%type (key_code key)
    (Some (key_value key, value)) m) as Htrace.
  pose proof (audit_trie_update_source_work_bound (K * V)%type (key_code key)
    (Some (key_value key, value)) m) as Hbound.
  unfold audit_prepared_update, audit_trie_set.
  destruct (audit_trie_update (key_code key) (Some (key_value key, value)) m).
  cbn [snd] in Htrace; cbn [snd audit_prepared_source_work]; lia.
Qed.

(** Prepared-removal source work is bounded by a constant plus sixteen times the stored code
    width. *)
Theorem audit_prepared_remove_source_bound : audit_prepared_remove_source_bound_statement.
Proof.
  intros K V CE enc_work key m.
  pose proof (audit_trie_update_trace_adequate (K * V)%type (key_code key) None m) as Htrace.
  pose proof (audit_trie_update_source_work_bound (K * V)%type (key_code key) None m) as Hbound.
  unfold audit_prepared_remove, audit_trie_remove.
  destruct (audit_trie_update (key_code key) None m).
  cbn [snd] in Htrace; cbn [snd audit_prepared_source_work]; lia.
Qed.

(** Preparation invokes the encoder once and subsequent prepared operations invoke it zero
    times. *)
Theorem audit_prepared_encoder_reuse : audit_prepared_encoder_reuse_statement.
Proof.
  intros K V CE enc key m value.
  unfold audit_prepare_key, audit_prepared_lookup, audit_prepared_update, audit_prepared_remove.
  destruct (enc (key_value key)), (audit_map_code_get (key_code key) m),
    (audit_trie_set (key_code key) (key_value key, value) m),
    (audit_trie_remove (key_code key) m); repeat split; reflexivity.
Qed.
