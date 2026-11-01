(** * Adequacy of counted memory distinctness

    The recorded traversal retains the same first occurrence as the plain traversal.
    For example, a repeated edge is checked again but is not retained a second time.
    Builds on: AnalysesAuditMemoryDistinct and the finite-set and trie adequacy proofs. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsFinSet CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditTrie CollectionsAuditTrieAdequacy.
From Galois.Graph Require Import GraphDominance.
From Galois.Analyses Require Import AnalysesMemoryFrontier AnalysesAuditMemoryDistinct.

(** Matching codes preserve first occurrences for an arbitrary initial seen set. *)
Theorem audit_memory_distinct_from_erases : audit_memory_distinct_from_erases_statement.
Proof.
  intros A CE enc EA seen input.
  revert seen.
  induction input as [|key rest IH]; intros seen Henc.
  - reflexivity.
  - cbn [audit_memory_distinct_from virtual_entries_from].
    pose proof (audit_finset_mem_erases A CE enc EA key seen (Henc key (or_introl eq_refl)))
      as Hmem.
    destruct (audit_finset_mem enc key seen) as [found probes] eqn:Hprobe; cbn in Hmem.
    rewrite <- Hmem.
    destruct found.
    + specialize (IH seen (fun k H => Henc k (or_intror H))).
      destruct (audit_memory_distinct_from enc seen rest); cbn in *; exact IH.
    + pose proof (audit_finset_add_erases A CE enc EA key seen (Henc key (or_introl eq_refl)))
        as Hadd.
      destruct (audit_finset_add enc key seen) as [next adds] eqn:Hadd_call; cbn in Hadd.
      rewrite <- Hadd.
      specialize (IH next (fun k H => Henc k (or_intror H))).
      destruct (audit_memory_distinct_from enc next rest); cbn in *; now rewrite IH.
Qed.

(** Starting from an empty set yields the original distinct list. *)
Theorem audit_memory_distinct_erases : audit_memory_distinct_erases_statement.
Proof.
  intros A CE enc EA input Henc.
  apply audit_memory_distinct_from_erases; exact Henc.
Qed.

(** A membership call pays for the actual encoder and trie path. *)
Lemma audit_memory_distinct_mem_bound A CE (enc : A -> positive * list CE) work key seen :
  audit_finset_source_work work (snd (audit_finset_mem enc key seen)) <=
    6 + work (snd (enc key)) + 5 * Pos.size_nat (fst (enc key)).
Proof.
  unfold audit_finset_mem, audit_map_code_get.
  destruct (enc key) as [code events]; cbn [fst snd].
  pose proof (audit_trie_get_trace_adequate (A * unit)%type code seen) as Htrace.
  pose proof (audit_trie_get_source_work_bound (A * unit)%type code seen) as Hbound.
  destruct (audit_trie_get code seen) as [found calls].
  cbn [snd] in Htrace.
  destruct found; cbn [snd audit_finset_source_work option_map]; lia.
Qed.

(** An insertion pays for the actual encoder and trie update. *)
Lemma audit_memory_distinct_add_bound A CE (enc : A -> positive * list CE) work key seen :
  audit_finset_source_work work (snd (audit_finset_add enc key seen)) <=
    2 + work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)).
Proof.
  unfold audit_finset_add.
  destruct (enc key) as [code events]; cbn [fst snd].
  pose proof (audit_trie_update_trace_adequate (A * unit)%type code (Some (key, tt)) seen)
    as Htrace.
  pose proof (audit_trie_update_source_work_bound (A * unit)%type code (Some (key, tt)) seen)
    as Hbound.
  unfold audit_trie_set.
  destruct (audit_trie_update code (Some (key, tt)) seen) as [output calls].
  cbn [snd] in Htrace; cbn [snd audit_finset_source_work]; lia.
Qed.

(** Every input occurrence pays for a probe and its possible insertion. *)
Theorem audit_memory_distinct_source_bound : audit_memory_distinct_source_bound_statement.
Proof.
  intros A CE enc work seen input.
  revert seen.
  induction input as [|key rest IH]; intro seen.
  - reflexivity.
  - cbn [audit_memory_distinct_from audit_memory_distinct_budget].
    pose proof (audit_memory_distinct_mem_bound A CE enc work key seen) as Hmem.
    destruct (audit_finset_mem enc key seen) as [found probes] eqn:Hprobe.
    cbn in Hmem.
    destruct found.
    + specialize (IH seen).
      destruct (audit_memory_distinct_from enc seen rest) as [out events].
      cbn [snd app audit_memory_distinct_work] in *; lia.
    + pose proof (audit_memory_distinct_add_bound A CE enc work key seen) as Hadd.
      destruct (audit_finset_add enc key seen) as [next adds] eqn:Hadd_call.
      cbn in Hadd.
      specialize (IH next).
      destruct (audit_memory_distinct_from enc next rest) as [out events].
      cbn [snd app audit_memory_distinct_work] in *; lia.
Qed.
