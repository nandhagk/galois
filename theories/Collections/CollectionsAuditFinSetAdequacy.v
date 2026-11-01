(** * Adequacy of finite-set construction

    The counted fold preserves the actual persistent accumulator at every input occurrence
    and accounts for duplicates. For example, adding the same key twice still emits two calls.
    Builds on: CollectionsAuditFinSet and CollectionsAuditTrieAdequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost CollectionsAuditTrie CollectionsAuditFinSet
  CollectionsAuditTrieAdequacy.
Import List.ListNotations.

(** Adding erases to insertion at the encoder's actual returned position. *)
Theorem audit_finset_add_erases : audit_finset_add_erases_statement.
Proof.
  intros K E enc original key input Hencode.
  unfold audit_finset_add; destruct (enc key) as [code ee]; cbn in Hencode.
  pose proof (audit_trie_set_erases (K * unit)%type code (key, tt) input) as Herases.
  destruct (audit_trie_set code (key, tt) input) as [output te]; cbn in Herases.
  rewrite Herases, Hencode; reflexivity.
Qed.

(** Membership erasure preserves both absent and present lookup outcomes. *)
Theorem audit_finset_mem_erases : audit_finset_mem_erases_statement.
Proof.
  intros K E enc original key input Hencode.
  unfold audit_finset_mem; destruct (enc key) as [code ee]; cbn in Hencode.
  pose proof (audit_map_code_get_erases K unit code input) as Herases.
  destruct (audit_map_code_get code input) as [found te]; cbn in Herases.
  rewrite Herases, Hencode; reflexivity.
Qed.

(** Removal erasure clears exactly the actual encoded position. *)
Theorem audit_finset_remove_erases : audit_finset_remove_erases_statement.
Proof.
  intros K E enc original key input Hencode.
  unfold audit_finset_remove; destruct (enc key) as [code ee]; cbn in Hencode.
  pose proof (audit_trie_remove_erases (K * unit)%type code input) as Herases.
  destruct (audit_trie_remove code input) as [output te]; cbn in Herases.
  rewrite Herases, Hencode; reflexivity.
Qed.

Lemma audit_finset_fold_erases K E (enc : K -> positive * list E) original remaining :
  (forall key, In key remaining -> fst (enc key) = encode original key) ->
  forall input, fst (audit_finset_fold enc remaining input) =
    List.fold_left (fun set key => FinSet.add original key set) remaining input.
Proof.
  induction remaining as [| key rest IH]; intros Hencode input.
  - reflexivity.
  - cbn [audit_finset_fold List.fold_left].
    pose proof (audit_finset_add_erases K E enc original key input
      (Hencode key (or_introl eq_refl)))
      as Hadd.
    destruct (audit_finset_add enc key input) as [next call]; cbn in Hadd.
    specialize (IH (fun k Hin => Hencode k (or_intror Hin)) next).
    destruct (audit_finset_fold enc rest next) as [output events]; cbn in *.
    rewrite IH, Hadd; reflexivity.
Qed.

(** List construction erases to the original left-to-right finite-set fold. *)
Theorem audit_finset_of_list_erases : audit_finset_of_list_erases_statement.
Proof.
  intros K E enc original input Hencode.
  exact (audit_finset_fold_erases K E enc original input Hencode FinSet.empty).
Qed.

Lemma audit_finset_fold_count K E (enc : K -> positive * list E) remaining :
  forall input, length (snd (audit_finset_fold enc remaining input)) = S (2 * length remaining).
Proof.
  induction remaining as [| key rest IH]; intro input.
  - reflexivity.
  - cbn [audit_finset_fold]; unfold audit_finset_add.
    destruct (enc key) as [code ee].
    destruct (audit_trie_set code (key, tt) input) as [next te].
    specialize (IH next).
    destruct (audit_finset_fold enc rest next) as [output events].
    cbn [snd List.length app] in *; lia.
Qed.

(** Each input occurrence contributes a fold event and an insertion event. *)
Theorem audit_finset_of_list_count : audit_finset_of_list_count_statement.
Proof.
  intros K E enc input; exact (audit_finset_fold_count K E enc input FinSet.empty).
Qed.

Lemma audit_finset_fold_source_bound K E (enc : K -> positive * list E) encoder_work remaining :
  forall input, audit_finset_source_work encoder_work (snd (audit_finset_fold enc remaining input))
    <= audit_finset_of_list_budget enc encoder_work remaining.
Proof.
  induction remaining as [| key rest IH]; intro input.
  - reflexivity.
  - cbn [audit_finset_fold audit_finset_of_list_budget]; unfold audit_finset_add.
    destruct (enc key) as [code ee]; cbn [fst snd].
    pose proof (audit_trie_update_trace_adequate (K * unit)%type code (Some (key, tt)) input)
      as Htrace.
    pose proof (audit_trie_update_source_work_bound (K * unit)%type code (Some (key, tt)) input)
      as Hbound.
    unfold audit_trie_set.
    destruct (audit_trie_update code (Some (key, tt)) input) as [next te].
    specialize (IH next).
    destruct (audit_finset_fold enc rest next) as [output events].
    cbn [snd app audit_finset_source_work] in *; lia.
Qed.

(** Set construction source work includes every duplicate occurrence and final fold frame. *)
Theorem audit_finset_of_list_source_bound : audit_finset_of_list_source_bound_statement.
Proof.
  intros K E enc encoder_work input.
  exact (audit_finset_fold_source_bound K E enc encoder_work input FinSet.empty).
Qed.
