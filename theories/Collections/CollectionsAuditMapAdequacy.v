(** * Adequacy of encoded map operations

    The proofs preserve the encoder's actual returned code and the persistent trie
    passed to each operation. For example, a missing key still pays for its full lookup path.
    Builds on: CollectionsAuditMap and CollectionsAuditTrieAdequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditTrieAdequacy.
Import List.ListNotations.

(** Map lookup erasure uses the actual encoder result at the lookup site. *)
Theorem audit_map_get_erases : audit_map_get_erases_statement.
Proof.
  intros K V E enc original key input Hencode.
  unfold audit_map_get.
  destruct (enc key) as [code ee]; cbn in Hencode.
  pose proof (audit_map_code_get_erases K V code input) as Herases.
  destruct (audit_map_code_get code input) as [output te]; cbn in Herases.
  rewrite Herases, Hencode; reflexivity.
Qed.

(** Map insertion erasure retains the original key and supplied value. *)
Theorem audit_map_set_erases : audit_map_set_erases_statement.
Proof.
  intros K V E enc original key value input Hencode.
  unfold audit_map_set.
  destruct (enc key) as [code ee]; cbn in Hencode.
  pose proof (audit_trie_set_erases (K * V)%type code (key, value) input) as Herases.
  destruct (audit_trie_set code (key, value) input) as [output te]; cbn in Herases.
  rewrite Herases, Hencode; reflexivity.
Qed.

(** Map removal erasure clears precisely the actual encoded position. *)
Theorem audit_map_remove_erases : audit_map_remove_erases_statement.
Proof.
  intros K V E enc original key input Hencode.
  unfold audit_map_remove.
  destruct (enc key) as [code ee]; cbn in Hencode.
  pose proof (audit_trie_remove_erases (K * V)%type code input) as Herases.
  destruct (audit_trie_remove code input) as [output te]; cbn in Herases.
  rewrite Herases, Hencode; reflexivity.
Qed.

(** Map lookup work includes encoding, the full trie lookup and result projection. *)
Theorem audit_map_get_source_work_bound : audit_map_get_source_work_bound_statement.
Proof.
  intros K V E enc encoder_work key input.
  unfold audit_map_get; destruct (enc key) as [code ee]; cbn [fst snd].
  unfold audit_map_code_get.
  pose proof (audit_trie_get_trace_adequate (K * V)%type code input) as Htrace.
  pose proof (audit_trie_get_source_work_bound (K * V)%type code input) as Hbound.
  destruct (audit_trie_get code input) as [found te].
  cbn [snd] in Htrace; cbn [snd audit_map_source_work].
  destruct found; cbn; lia.
Qed.

(** Map insertion work includes its concrete encoding and all strict update frames. *)
Theorem audit_map_set_source_work_bound : audit_map_set_source_work_bound_statement.
Proof.
  intros K V E enc encoder_work key value input.
  unfold audit_map_set; destruct (enc key) as [code ee]; cbn [fst snd].
  pose proof (audit_trie_update_trace_adequate (K * V)%type code (Some (key, value)) input)
    as Htrace.
  pose proof (audit_trie_update_source_work_bound (K * V)%type code (Some (key, value)) input)
    as Hbound.
  unfold audit_trie_set.
  destruct (audit_trie_update code (Some (key, value)) input) as [output te].
  cbn [snd] in Htrace; cbn [snd audit_map_source_work].
  lia.
Qed.

(** Map removal work includes encoding and the same concrete update trace. *)
Theorem audit_map_remove_source_work_bound : audit_map_remove_source_work_bound_statement.
Proof.
  intros K V E enc encoder_work key input.
  unfold audit_map_remove; destruct (enc key) as [code ee]; cbn [fst snd].
  pose proof (audit_trie_update_trace_adequate (K * V)%type code None input) as Htrace.
  pose proof (audit_trie_update_source_work_bound (K * V)%type code None input) as Hbound.
  unfold audit_trie_remove.
  destruct (audit_trie_update code None input) as [output te].
  cbn [snd] in Htrace; cbn [snd audit_map_source_work].
  lia.
Qed.
