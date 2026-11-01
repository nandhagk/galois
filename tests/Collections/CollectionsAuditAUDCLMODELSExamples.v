(** * Collection audit model computations

    These examples observe concrete results and retained events in collection models.
    For example, repeated set entries produce separate insertion events.
    Builds on: the collection audit model definitions. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditCompare.
Import List.ListNotations.

Example audit_models_trie_present_and_absent :
  let tree := fst (audit_trie_set 2%positive 7 (Trie.empty : Trie.t nat)) in
  (fst (audit_trie_get 2%positive tree), fst (audit_trie_get 3%positive tree)) =
    (Some 7, None).
Proof.
  reflexivity.
Qed.

Example audit_models_empty_lookup_trace :
  length (snd (audit_trie_get 1%positive (Trie.empty : Trie.t nat))) = 2.
Proof.
  reflexivity.
Qed.

Example audit_models_duplicate_set_events :
  length (snd (audit_finset_of_list audit_positive_encode [2%positive; 2%positive])) = 5.
Proof.
  reflexivity.
Qed.

Example audit_models_carry_and_order :
  (fst (audit_positive_succ 3%positive),
   length (snd (audit_positive_succ 3%positive)),
   fst (audit_positive_ltb 3%positive 2%positive)) = (4%positive, 2, false).
Proof.
  reflexivity.
Qed.
