(** * Row-index derivation adequacy

    The source row call has a derivation retaining its actual key and map subruns.
    For example, a malformed row takes the no-key branch without updating the map.
    Builds on: RulesAuditIndexCounts RulesCompile RulesSyntax. *)

From Stdlib Require Import List PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditEncodingAdequacy CollectionsAuditFinSetAdequacy.
From Galois.Rules Require Import RulesAuditMaterializePrelude RulesAuditIndex
  RulesAuditIndexCounts RulesCompile RulesSyntax.
Import List.ListNotations.

(** * Row derivations *)

(** Every actual row call has a derivation preserving its returned value and trace. *)
Theorem mat_index_add_run_total : mat_index_add_run_total_statement.
Proof.
  unfold mat_index_add_run_total_statement.
  intros bound terms row before.
  unfold mat_index_add_full, mat_bind.
  destruct (mat_tuple_key bound terms row) as [[key |] key_events] eqn:Hkey.
  - destruct (mat_get_encoded mat_tuple_encoder key before) as [raw get_events] eqn:Hget.
    destruct (mat_set_encoded mat_tuple_encoder key
      (row :: match raw with
       | Some rows => rows
       | None => []
       end) before) as [out set_events] eqn:Hset.
    cbn [mat_return]; rewrite Hset; cbn.
    eapply MatIndexAddKey; [exact Hkey | exact Hget | reflexivity | exact Hset].
  - cbn [mat_return].
    apply MatIndexAddNoKey; exact Hkey.
Qed.

(** * Key trace structure *)

Lemma mat_import_count_app site first second :
  mat_import_count site (first ++ second) =
    mat_import_count site first + mat_import_count site second.
Proof.
  unfold mat_import_count; rewrite filter_app, length_app; reflexivity.
Qed.

Lemma mat_block_count_app site first second :
  mat_block_count site (first ++ second) =
    mat_block_count site first + mat_block_count site second.
Proof.
  unfold mat_block_count; rewrite filter_app, length_app; reflexivity.
Qed.

Lemma mat_tuple_key_import_count bound terms row site :
  site <> 102 -> mat_import_count site (snd (mat_tuple_key bound terms row)) = 0.
Proof.
  revert row; induction terms as [|term terms IH]; intros [|value row] Hsite;
    cbn [mat_tuple_key mat_mark mat_return mat_import_count]; try reflexivity.
  destruct (mat_tuple_key bound terms row) as [[key |] events] eqn:Hkey.
  - specialize (IH row Hsite); rewrite Hkey in IH; cbn in IH.
    destruct term as [variable | constant].
    + unfold mat_bound_term, mat_lift, mat_bind, mat_mark.
      destruct (CollectionsAuditFinSet.audit_finset_mem
        CollectionsAuditEncoding.audit_nat_encode variable bound) as [kept body].
      destruct kept; cbn [mat_bind mat_mark mat_return mat_import_count] in *;
        try rewrite filter_app, length_app; cbn;
        assert (Heq : (102 =? site) = false) by (apply Nat.eqb_neq; congruence);
        try rewrite Heq; cbn; rewrite filter_app, length_app; cbn;
        change (match site with
          | 102 => true
          | _ => false
          end = false) in Heq;
        rewrite Heq; cbn; lia.
    + unfold mat_bound_term, mat_bind, mat_mark;
      cbn [mat_bind mat_mark mat_return mat_import_count] in *.
      cbn; rewrite filter_app, length_app; cbn; lia.
  - specialize (IH row Hsite); rewrite Hkey in IH; cbn in IH.
    cbn [mat_bind mat_return mat_import_count] in *.
    cbn; rewrite filter_app, length_app; cbn; lia.
Qed.

Lemma mat_bound_term_erases bound term :
  fst (mat_bound_term bound term) = bound_term bound term.
Proof.
  destruct term as [variable | constant].
  - unfold mat_bound_term, mat_mark, mat_lift, bound_term.
    pose proof (audit_finset_mem_erases nat audit_nat_encoding_event audit_nat_encode
      nat_encoding variable bound (audit_nat_encode_erases variable)) as Hmem.
    destruct (audit_finset_mem audit_nat_encode variable bound) as [result events].
    exact Hmem.
  - reflexivity.
Qed.

Lemma mat_tuple_key_erases bound terms row :
  fst (mat_tuple_key bound terms row) = tuple_key bound terms row.
Proof.
  revert row; induction terms as [|term terms IH]; intros [|value row];
    cbn [mat_tuple_key mat_mark mat_return tuple_key]; try reflexivity.
  specialize (IH row).
  destruct (mat_tuple_key bound terms row) as [[key |] events] eqn:Hkey; cbn in IH.
  - pose proof (mat_bound_term_erases bound term) as Hbound.
    destruct (mat_bound_term bound term) as [kept frames] eqn:Hkept; cbn in Hbound.
    cbn [mat_bind mat_return]; rewrite <- Hbound, <- IH; reflexivity.
  - cbn [mat_bind mat_return]; rewrite <- IH; reflexivity.
Qed.

Lemma mat_index_get_counts key (before : tuple_index) :
  let events := snd (mat_get_encoded mat_tuple_encoder key before) in
  mat_import_count 10 events = 1 /\ mat_import_count 11 events = 0 /\
  mat_import_count 100 events = 1 /\ mat_block_count 5 events = 0.
Proof.
  unfold mat_get_encoded, mat_tuple_encoder, mat_bind, mat_lift.
  destruct (audit_list_encode audit_positive_encode key) as [code encoding_events].
  destruct (CollectionsAuditTrie.audit_map_code_get code before) as [result get_events].
  repeat split; reflexivity.
Qed.

Lemma mat_index_set_counts key (value : list tuple) (before : tuple_index) :
  let events := snd (mat_set_encoded mat_tuple_encoder key value before) in
  mat_import_count 10 events = 0 /\ mat_import_count 11 events = 1 /\
  mat_import_count 100 events = 1 /\ mat_block_count 5 events = 0.
Proof.
  unfold mat_set_encoded, mat_tuple_encoder, mat_bind, mat_lift.
  destruct (audit_list_encode audit_positive_encode key) as [code encoding_events].
  destruct (CollectionsAuditTrie.audit_trie_set code (key, value) before) as [out set_events].
  repeat split; reflexivity.
Qed.

Lemma mat_tuple_key_block_count bound terms row :
  mat_block_count 5 (snd (mat_tuple_key bound terms row)) = 0.
Proof.
  revert row; induction terms as [|term terms IH]; intros [|value row];
    cbn [mat_tuple_key mat_mark mat_return mat_block_count]; try reflexivity.
  destruct (mat_tuple_key bound terms row) as [[key |] events] eqn:Hkey.
  - specialize (IH row); rewrite Hkey in IH; cbn in IH.
    destruct term as [variable | constant].
    + unfold mat_bound_term, mat_lift, mat_bind, mat_mark.
      destruct (audit_finset_mem audit_nat_encode variable bound) as [kept body].
      destruct kept; cbn [mat_bind mat_mark mat_return mat_block_count] in *;
        cbn; rewrite filter_app, length_app; cbn; lia.
    + unfold mat_bound_term, mat_bind, mat_mark.
      cbn [mat_bind mat_mark mat_return mat_block_count] in *.
      cbn; rewrite filter_app, length_app; cbn; lia.
  - specialize (IH row); rewrite Hkey in IH; cbn in IH.
    cbn [mat_bind mat_return mat_block_count] in *.
    cbn; rewrite filter_app, length_app; cbn; lia.
Qed.

Lemma mat_index_row_trace_counts bound terms row before :
  let events := snd (mat_index_add_full bound terms row before) in
  mat_import_count 10 events = (if mat_index_success bound terms row then 1 else 0) /\
  mat_import_count 11 events = (if mat_index_success bound terms row then 1 else 0) /\
  mat_import_count 100 events = (if mat_index_success bound terms row then 2 else 0) /\
  mat_block_count 5 events = 0.
Proof.
  pose proof (mat_tuple_key_erases bound terms row) as Herase.
  pose proof (mat_tuple_key_import_count bound terms row 10 ltac:(lia)) as H10.
  pose proof (mat_tuple_key_import_count bound terms row 11 ltac:(lia)) as H11.
  pose proof (mat_tuple_key_import_count bound terms row 100 ltac:(lia)) as H100.
  pose proof (mat_tuple_key_block_count bound terms row) as Hblock.
  unfold mat_index_add_full, mat_bind, mat_index_success.
  destruct (mat_tuple_key bound terms row) as [[key |] key_events] eqn:Hkey;
    cbn in Herase, H10, H11, H100, Hblock; rewrite <- Herase.
  - pose proof (mat_index_get_counts key before) as Hgetcount.
    destruct (mat_get_encoded mat_tuple_encoder key before) as [raw get_events] eqn:Hget.
    cbn in Hgetcount.
    set (old := match raw with
      | Some rows => rows
      | None => []
      end).
    pose proof (mat_index_set_counts key (row :: old) before) as Hsetcount.
    destruct (mat_set_encoded mat_tuple_encoder key (row :: old) before)
      as [out set_events] eqn:Hset.
    cbn in Hsetcount.
    cbn [mat_return]; fold old; rewrite Hset; cbn.
    repeat rewrite mat_import_count_app; repeat rewrite mat_block_count_app.
    cbn [mat_import_count mat_block_count] in *; repeat rewrite filter_app;
    repeat rewrite length_app; cbn; destruct Hgetcount as [Hget10 [Hget11 [Hget100 Hgetblock]]];
    destruct Hsetcount as [Hset10 [Hset11 [Hset100 Hsetblock]]]; repeat split; lia.
  - cbn [mat_return]; repeat rewrite mat_import_count_app; repeat rewrite mat_block_count_app.
    cbn [mat_import_count mat_block_count] in *; repeat rewrite filter_app;
    repeat rewrite length_app; cbn; repeat rewrite filter_app;
    repeat rewrite length_app; cbn; repeat split; lia.
Qed.

(** Each successful row performs the specified get, set and two encodings. *)
Theorem mat_index_row_counts : mat_index_row_counts_statement.
Proof.
  unfold mat_index_row_counts_statement.
  intros bound terms row before.
  pose proof (mat_index_row_trace_counts bound terms row before) as Hcounts.
  destruct (mat_index_add_full bound terms row before) as [out events].
  cbn in Hcounts; tauto.
Qed.

(** The fold retains one row trace for each occurrence, including failed keys. *)
Theorem mat_index_fold_counts : mat_index_fold_counts_statement.
Proof.
  unfold mat_index_fold_counts_statement, mat_build_index_full.
  intros bound terms rows; induction rows as [|row rows IH].
  - cbn [mat_foldr mat_mark mat_return].
    exists []; repeat split; try constructor; reflexivity.
  - cbn [mat_foldr mat_mark mat_bind].
    destruct (mat_foldr (mat_index_add_full bound terms) rows CollectionsMap.Map.empty)
      as [before later] eqn:Hfold.
    cbn in IH.
    destruct IH as [chunks [Hrun [Hlength [Hblock [H10 [H11 H100]]]]]].
    pose proof (mat_index_row_trace_counts bound terms row before) as Hrow.
    destruct (mat_index_add_full bound terms row before) as [out here] eqn:Hadd.
    cbn in Hrow.
    cbn [mat_bind]; rewrite Hadd; cbn.
    exists (here :: chunks); split.
    + eapply MatIndexFoldCons; [exact Hrun | exact Hadd].
    + cbn [length]; split; [now rewrite Hlength |].
      repeat rewrite mat_import_count_app; repeat rewrite mat_block_count_app.
      unfold mat_block_count, mat_import_count in *.
      repeat rewrite filter_app; repeat rewrite length_app; cbn in *.
      destruct Hrow as [Hrow10 [Hrow11 [Hrow100 Hrowblock]]].
      destruct (mat_index_success bound terms row); cbn; repeat split; lia.
Qed.
