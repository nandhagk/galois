(** * Dense preparation observer adequacy

    Preparation's observers retain first occurrences and their numbered positions.
    For example, a duplicate is probed but is not numbered twice.
    Builds on: CollectionsAuditDense and encoding, set and map adequacy. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet CollectionsAuditEncoding CollectionsAuditEncodingAdequacy
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditDense.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** Discarding events from binary successor returns the ordinary successor for every input. *)
Theorem audit_dense_N_succ_erases : audit_dense_N_succ_erases_statement.
Proof.
  intro input. unfold audit_dense_N_succ.
  pose proof (audit_N_encode_erases input) as Hresult.
  destruct (audit_N_encode input) as [code events]; cbn in *.
  rewrite Hresult. destruct input; reflexivity.
Qed.

(** Discarding conversion events returns the ordinary binary natural for every input. *)
Theorem audit_dense_N_of_nat_erases : audit_dense_N_of_nat_erases_statement.
Proof.
  intros [|input]; [reflexivity|].
  cbn [audit_dense_N_of_nat].
  pose proof (audit_nat_encode_erases input) as Hresult.
  destruct (audit_nat_encode input) as [code events]; cbn in *.
  now rewrite Hresult.
Qed.

(** When encoders agree on the input keys, discarding events preserves first-occurrence
    selection. *)
Theorem audit_dense_unique_erases : audit_dense_unique_erases_statement.
Proof.
  intros K CE enc original seen keys. revert seen.
  induction keys as [|key rest IH]; intros seen Henc; [reflexivity|].
  cbn [audit_dense_unique dense_unique].
  pose proof (audit_finset_mem_erases K CE enc original key seen
    (Henc key (or_introl eq_refl))) as Hmem.
  destruct (audit_finset_mem enc key seen) as [found probes]; cbn in Hmem.
  rewrite <- Hmem. destruct found.
  - specialize (IH seen (fun k Hin => Henc k (or_intror Hin))).
    destruct (audit_dense_unique enc seen rest); exact IH.
  - pose proof (audit_finset_add_erases K CE enc original key seen
      (Henc key (or_introl eq_refl))) as Hadd.
    destruct (audit_finset_add enc key seen) as [next adds]; cbn in Hadd.
    specialize (IH next (fun k Hin => Henc k (or_intror Hin))).
    destruct (audit_dense_unique enc next rest); cbn in *.
    now rewrite <- Hadd, <- IH.
Qed.

(** When encoders agree on the input keys, discarding events preserves numbering and map writes. *)
Theorem audit_dense_number_erases : audit_dense_number_erases_statement.
Proof.
  intros K CE enc original keys. induction keys as [|key rest IH]; intros index Henc;
    [reflexivity|].
  cbn [audit_dense_number dense_number].
  pose proof (audit_dense_N_succ_erases index) as Hnext.
  destruct (audit_dense_N_succ index) as [next events]; cbn in Hnext.
  specialize (IH next (fun k Hin => Henc k (or_intror Hin))).
  destruct (audit_dense_number enc rest next) as [tail te]; cbn in IH.
  pose proof (audit_map_set_erases K N CE enc original key index tail
    (Henc key (or_introl eq_refl))) as Hset.
  destruct (audit_map_set enc key index tail) as [out se]; cbn in *.
  now rewrite <- Hnext, <- IH, <- Hset.
Qed.

(** When encoders agree on the input keys, discarding preparation events preserves the dense
    universe. *)
Theorem audit_dense_prepare_erases : audit_dense_prepare_erases_statement.
Proof.
  intros K CE enc original keys Henc.
  pose proof (audit_dense_unique_erases K CE enc original FinSet.empty keys Henc) as Hunique.
  unfold audit_dense_prepare, dense_prepare.
  destruct (audit_dense_unique enc FinSet.empty keys) as [unique ue]; cbn in Hunique.
  assert (Hunique_enc : forall k, In k unique -> fst (enc k) = encode original k).
  { intros k Hin. apply Henc. rewrite Hunique in Hin.
    apply dense_unique_spec in Hin. exact (proj1 Hin). }
  pose proof (audit_dense_number_erases K CE enc original unique 0%N Hunique_enc) as Hnumber.
  destruct (audit_dense_number enc unique 0%N) as [index ie]; cbn in Hnumber.
  pose proof (audit_dense_N_of_nat_erases (length unique)) as Hlength.
  destruct (audit_dense_N_of_nat (length unique)) as [len le]; cbn in Hlength.
  cbn. now rewrite Hnumber, Hlength, Hunique.
Qed.

(** Membership work includes the encoder, trie path and result branch. *)
Lemma dense_finset_mem_bound K CE (enc : K -> positive * list CE) work key seen :
  audit_finset_source_work work (snd (audit_finset_mem enc key seen)) <=
    6 + work (snd (enc key)) + 5 * Pos.size_nat (fst (enc key)).
Proof.
  unfold audit_finset_mem. destruct (enc key) as [code ee]; cbn [fst snd].
  unfold audit_map_code_get.
  pose proof (audit_trie_get_trace_adequate (K * unit)%type code seen) as Htrace.
  pose proof (audit_trie_get_source_work_bound (K * unit)%type code seen) as Hbound.
  destruct (audit_trie_get code seen) as [found events]; cbn [snd] in Htrace.
  destruct found; cbn [snd option_map audit_finset_source_work]; lia.
Qed.

(** Insertion work includes the encoder and rebuilt trie path. *)
Lemma dense_finset_add_bound K CE (enc : K -> positive * list CE) work key seen :
  audit_finset_source_work work (snd (audit_finset_add enc key seen)) <=
    2 + work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)).
Proof.
  unfold audit_finset_add. destruct (enc key) as [code ee]; cbn [fst snd].
  pose proof (audit_trie_update_trace_adequate (K * unit)%type code (Some (key, tt)) seen)
    as Htrace.
  pose proof (audit_trie_update_source_work_bound (K * unit)%type code (Some (key, tt)) seen)
    as Hbound.
  unfold audit_trie_set. destruct (audit_trie_update code (Some (key, tt)) seen) as [out events].
  cbn [snd] in Htrace. cbn [snd audit_finset_source_work]. lia.
Qed.

(** Dense preparation work is additive across successive event segments. *)
Lemma dense_prepare_work_app K CE work (left right : list (audit_dense_prepare_event K CE)) :
  audit_dense_prepare_work work (left ++ right) =
    audit_dense_prepare_work work left + audit_dense_prepare_work work right.
Proof.
  induction left as [|event rest IH]; [reflexivity|].
  destruct event; cbn [app audit_dense_prepare_work]; rewrite IH; lia.
Qed.

(** Distinctness selection charges both probes when the key is new. *)
Lemma dense_unique_bound K CE (enc : K -> positive * list CE) work keys : forall seen,
  audit_dense_prepare_work work (snd (audit_dense_unique enc seen keys)) <=
    audit_dense_unique_budget enc work keys.
Proof.
  induction keys as [|key rest IH]; intro seen; [reflexivity|].
  cbn [audit_dense_unique audit_dense_unique_budget].
  pose proof (dense_finset_mem_bound K CE enc work key seen) as Hmem.
  destruct (audit_finset_mem enc key seen) as [found probes]; cbn [snd] in Hmem.
  destruct found.
  - specialize (IH seen). destruct (audit_dense_unique enc seen rest) as [unique events].
    cbn [snd] in IH. cbn [snd app audit_dense_prepare_work]. lia.
  - pose proof (dense_finset_add_bound K CE enc work key seen) as Hadd.
    destruct (audit_finset_add enc key seen) as [next adds]; cbn [snd] in Hadd.
    specialize (IH next). destruct (audit_dense_unique enc next rest) as [unique events].
    cbn [snd] in IH. cbn [snd app audit_dense_prepare_work]. lia.
Qed.

(** Numbering charges each successor and each returned map insertion. *)
Lemma dense_number_bound K CE (enc : K -> positive * list CE) work keys : forall index,
  audit_dense_prepare_work work (snd (audit_dense_number enc keys index)) <=
    audit_dense_number_budget enc work keys index.
Proof.
  induction keys as [|key rest IH]; intro index; [reflexivity|].
  cbn [audit_dense_number audit_dense_number_budget].
  destruct (audit_dense_N_succ index) as [next ne].
  specialize (IH next). destruct (audit_dense_number enc rest next) as [tail events].
  cbn [snd] in IH.
  pose proof (audit_map_set_source_work_bound K N CE enc work key index tail) as Hset.
  destruct (audit_map_set enc key index tail) as [out calls]; cbn [snd] in Hset.
  cbn [snd app audit_dense_prepare_work]. rewrite dense_prepare_work_app.
  cbn [audit_dense_prepare_work]. lia.
Qed.

(** Dense preparation source work is at most its selection, numbering and length-conversion
    budget. *)
Theorem audit_dense_prepare_source_bound : audit_dense_prepare_source_bound_statement.
Proof.
  intros K CE enc work keys.
  pose proof (dense_unique_bound K CE enc work keys FinSet.empty) as Hunique.
  unfold audit_dense_prepare, audit_dense_prepare_budget.
  destruct (audit_dense_unique enc FinSet.empty keys) as [unique ue]; cbn [fst snd] in *.
  pose proof (dense_number_bound K CE enc work unique 0%N) as Hnumber.
  destruct (audit_dense_number enc unique 0%N) as [index ie]; cbn [snd] in Hnumber.
  destruct (audit_dense_N_of_nat (length unique)) as [len le].
  cbn [fst snd]. rewrite !dense_prepare_work_app. cbn [audit_dense_prepare_work]. lia.
Qed.
