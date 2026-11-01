(** * Concrete encoder budget adequacy

    The event folds are bounded by input widths and the budgets of actual component calls.
    For example, a list charges each duplicate element occurrence separately.
    Builds on: CollectionsAuditEncoderBudget and counted encoding adequacy. *)

From Stdlib Require Import List NArith PArith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding
  CollectionsAuditEncoderBudget CollectionsAuditEncodingAdequacy
  CollectionsAuditStateENCAdequacy.
Import List.ListNotations.

(** * Fixed frame work *)

(** Code emission charges four units per input bit. *)
Lemma audit_emit_code_work : forall code tail,
  audit_encoding_frames_work (snd (audit_emit_code code tail)) = 4 * Pos.size_nat code.
Proof.
  induction code as [code IH|code IH|]; intro tail; simpl; try reflexivity;
    specialize (IH tail); destruct (audit_emit_code code tail) as [bits frames];
    simpl in *; lia.
Qed.

(** Stream conversion charges three units for each bit and the terminal frame. *)
Lemma audit_stream_positive_work : forall bits,
  audit_encoding_frames_work (snd (audit_stream_positive bits)) = 3 * S (length bits).
Proof.
  induction bits as [|[] rest IH]; simpl; try reflexivity;
    destruct (audit_stream_positive rest) as [result frames]; simpl in *; lia.
Qed.

(** Frame work is additive over concatenation. *)
Lemma audit_encoding_frames_work_app : forall xs ys,
  audit_encoding_frames_work (xs ++ ys) =
    audit_encoding_frames_work xs + audit_encoding_frames_work ys.
Proof.
  induction xs as [|x xs IH]; intro ys; simpl; try reflexivity. rewrite IH. lia.
Qed.

(** Pair frame wrapping preserves the fixed frame charges. *)
Lemma audit_pair_frames_work : forall A B EA EB first_work second_work frames,
  @audit_pair_events_work A B EA EB first_work second_work (map AuditPairFrame frames) =
    audit_encoding_frames_work frames.
Proof.
  intros A B EA EB first_work second_work frames.
  induction frames as [|frame frames IH]; simpl; try reflexivity. now rewrite IH.
Qed.

(** List frame wrapping preserves the fixed frame charges. *)
Lemma audit_list_frames_work : forall A E work frames,
  @audit_list_events_work A E work (map AuditListFrame frames) =
    audit_encoding_frames_work frames.
Proof.
  intros A E work frames. induction frames as [|frame frames IH]; simpl; try reflexivity.
  now rewrite IH.
Qed.

(** List event work is additive over concatenation. *)
Lemma audit_list_events_work_app : forall A E work (xs ys : list (audit_list_event A E)),
  audit_list_events_work work (xs ++ ys) =
    audit_list_events_work work xs + audit_list_events_work work ys.
Proof.
  intros A E work xs. induction xs as [|event xs IH]; intro ys; simpl; try reflexivity.
  destruct event; simpl; rewrite IH; lia.
Qed.

(** * Fixed primitive budgets *)

(** Each primitive's concrete event work fits its operand budget. *)
Theorem audit_base_encoder_input_bound : audit_base_encoder_input_bound_statement.
Proof.
  repeat split.
  - intros p. simpl. lia.
  - intros b. destruct b; simpl; lia.
  - intros []. simpl. lia.
  - intros z. destruct z; simpl; lia.
  - intros n. unfold audit_nat_events_work, audit_nat_input_budget.
    pose proof (audit_nat_encode_count n). nia.
  - intros [|p]; unfold audit_N_encoding_work; simpl; try lia.
    pose proof (audit_positive_succ_count p) as Hcount.
    destruct (audit_positive_succ p) as [result events]. simpl in *.
    rewrite length_map. nia.
Qed.

(** * Composite input budgets *)

(** Pair work is bounded by actual component budgets and their code widths. *)
Theorem audit_pair_input_bound : audit_pair_input_bound_statement.
Proof.
  intros A B EA EB first second first_work second_work first_budget second_budget [a b]
    Hfirst Hsecond.
  specialize (Hfirst a). specialize (Hsecond b).
  unfold audit_pair_encode, audit_pair_input_budget.
  cbn [fst snd].
  destruct (first a) as [ac ae]. destruct (second b) as [bc be].
  simpl in Hfirst, Hsecond.
  pose proof (audit_emit_code_work bc []) as Hbw.
  pose proof (audit_emit_code_erases bc []) as Hbe.
  destruct (audit_emit_code bc []) as [bt bf]. simpl in Hbw, Hbe.
  pose proof (audit_emit_code_work ac bt) as Haw.
  pose proof (audit_emit_code_erases ac bt) as Hae.
  destruct (audit_emit_code ac bt) as [bits af]. simpl in Haw, Hae.
  pose proof (audit_stream_positive_work bits) as Hsw.
  destruct (audit_stream_positive bits) as [result sf]. simpl in Hsw.
  simpl. rewrite audit_pair_frames_work, !audit_encoding_frames_work_app.
  rewrite Hae, Hbe, !emit_code_length in Hsw. simpl in Hsw. lia.
Qed.

(** List emission pays for each actual child and each emitted code frame. *)
Lemma audit_emit_list_work_bound : forall A E (element : A -> positive * list E) work budget keys,
  (forall a, work (snd (element a)) <= budget a) ->
  audit_list_events_work work (snd (audit_emit_list element keys)) <=
    1 + 2 * length keys + 4 * audit_encoded_bits element keys +
      audit_child_input_budget budget keys.
Proof.
  intros A E element work budget keys Hbudget.
  induction keys as [|key rest IH]; simpl; try lia.
  specialize (Hbudget key) as Hkey.
  destruct (element key) as [code child]. simpl in Hkey.
  destruct (audit_emit_list element rest) as [tail events]. simpl in IH.
  pose proof (audit_emit_code_work code tail) as Hframes.
  destruct (audit_emit_code code tail) as [bits frames]. simpl in Hframes.
  simpl. rewrite !audit_list_events_work_app, audit_list_frames_work. simpl. lia.
Qed.

(** List work is bounded by every actual occurrence and its code width. *)
Theorem audit_list_input_bound : audit_list_input_bound_statement.
Proof.
  intros A E element work budget keys Hbudget.
  pose proof (audit_emit_list_work_bound A E element work budget keys Hbudget) as Hwork.
  pose proof (audit_emit_list_length A E element keys) as Hlength.
  unfold audit_list_encode, audit_list_input_budget.
  destruct (audit_emit_list element keys) as [bits events]. simpl in Hwork, Hlength.
  pose proof (audit_stream_positive_work bits) as Hstream.
  destruct (audit_stream_positive bits) as [result frames]. simpl in Hstream.
  simpl. rewrite audit_list_events_work_app, audit_list_frames_work. lia.
Qed.

(** Sum and option budgets charge only the selected actual child. *)
Theorem audit_sum_option_input_bound : audit_sum_option_input_bound_statement.
Proof.
  split.
  - intros A E element work budget [key|] Hbudget; simpl; try lia.
    specialize (Hbudget key). destruct (element key) as [code events]. simpl in *. lia.
  - intros A B EA EB left right left_work right_work left_budget right_budget [a|b]
      Hleft Hright; simpl.
    + specialize (Hleft a). destruct (left a) as [code events]. simpl in *. lia.
    + specialize (Hright b). destruct (right b) as [code events]. simpl in *. lia.
Qed.
