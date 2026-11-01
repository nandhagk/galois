(** * Counted encoding adequacy

    Counted encoders retain the results and work of their concrete source operations.
    For example, a carry from one visits one positive frame.
    Builds on: CollectionsAuditEncoding and CollectionsAuditStateENCAdequacy. *)

From Stdlib Require Import List NArith PArith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding
  CollectionsAuditStateENCAdequacy.
Import List.ListNotations.

(** * Unary and positive encoders *)

(** The counted successor returns the ordinary positive successor. *)
Theorem audit_positive_succ_erases : audit_positive_succ_erases_statement.
Proof.
  unfold audit_positive_succ_erases_statement. intro input.
  induction input as [p IH|p IH|]; simpl; try reflexivity.
  destruct (audit_positive_succ p) as [result events] eqn:Hrun.
  simpl in IH. now rewrite IH.
Qed.

(** The counted unary encoder returns the ordinary natural encoding. *)
Theorem audit_nat_encode_erases : audit_nat_encode_erases_statement.
Proof.
  unfold audit_nat_encode_erases_statement. intro input.
  induction input as [|n IH]; simpl; try reflexivity.
  destruct (audit_nat_encode n) as [previous events] eqn:Hrun.
  simpl in IH.
  pose proof (audit_positive_succ_erases previous) as Hsucc.
  destruct (audit_positive_succ previous) as [result succ_events] eqn:Hsuccrun.
  simpl in Hsucc. simpl. rewrite Hsucc, IH. reflexivity.
Qed.

(** The carry trace contains at most one frame per input bit. *)
Theorem audit_positive_succ_count : audit_positive_succ_count_statement.
Proof.
  unfold audit_positive_succ_count_statement. intro input.
  induction input as [p IH|p IH|]; simpl; try lia.
  destruct (audit_positive_succ p) as [result events] eqn:Hrun.
  simpl in IH. simpl. lia.
Qed.

(** Successor cannot decrease positive width. *)
Lemma positive_succ_size : forall p, Pos.size_nat p <= Pos.size_nat (Pos.succ p).
Proof.
  induction p as [p IH|p IH|]; simpl; lia.
Qed.

(** Unary encoding events fit the bound from the input and output widths. *)
Theorem audit_nat_encode_count : audit_nat_encode_count_statement.
Proof.
  unfold audit_nat_encode_count_statement. intro input.
  induction input as [|n IH]; simpl; try lia.
  destruct (audit_nat_encode n) as [previous events] eqn:Hrun.
  pose proof (audit_nat_encode_erases n) as Herase.
  rewrite Hrun in Herase. simpl in Herase, IH.
  pose proof (audit_positive_succ_count previous) as Hcount.
  pose proof (positive_succ_size previous) as Hsize.
  destruct (audit_positive_succ previous) as [result succ_events] eqn:Hsucc.
  simpl in Hcount.
  simpl. rewrite length_app. simpl.
  rewrite <- Herase in *. simpl in *. nia.
Qed.

(** Every successor derivation agrees with its counted execution. *)
Theorem audit_positive_succ_run_correct : audit_positive_succ_run_correct_statement.
Proof.
  intros input output events work Hrun.
  induction Hrun as [|p|p result events work Hrun IH]; simpl in *; try (repeat split; lia).
  destruct IH as [Hout [Hcounted [Hwork Hbound]]].
  rewrite <- Hcounted. simpl. subst result. repeat split; try reflexivity; lia.
Qed.

(** Every positive input has an actual successor derivation. *)
Theorem audit_positive_succ_run_total : audit_positive_succ_run_total_statement.
Proof.
  unfold audit_positive_succ_run_total_statement. intro input.
  induction input as [p IH|p IH|].
  - destruct IH as [output [events [work Hrun]]].
    exists (xO output), (AuditPositiveSuccFrame (xI p) (xO output) :: events), (2 + work).
    now constructor.
  - exists (xI p), [AuditPositiveSuccFrame (xO p) (xI p)], 2. constructor.
  - exists (xO xH), [AuditPositiveSuccFrame xH (xO xH)], 2. constructor.
Qed.

(** Every unary source derivation agrees with its counted execution and bound. *)
Theorem audit_nat_encode_run_correct : audit_nat_encode_run_correct_statement.
Proof.
  intros input output events work Hrun.
  induction Hrun as [|input previous output events succ_events work succ_work Hnat IH Hsucc].
  - repeat split; simpl; lia.
  - destruct IH as [Hprevious [Hcounted [Hwork Hbound]]].
    pose proof (audit_positive_succ_run_correct _ _ _ _ Hsucc) as Hsucccorrect.
    destruct Hsucccorrect as [Houtput [Hsucccounted [Hsuccwork Hsuccbound]]].
    assert (Hresult : (output, AuditNatFrame (S input) :: events ++ succ_events) =
        audit_nat_encode (S input)).
    { simpl. rewrite <- Hcounted, <- Hsucccounted. reflexivity. }
    assert (Herase := audit_nat_encode_erases (S input)).
    assert (Hcount := audit_nat_encode_count (S input)).
    rewrite <- Hresult in Herase, Hcount. simpl in Herase, Hcount.
    repeat split; try assumption.
    + simpl. rewrite length_app. lia.
    + simpl. rewrite length_app in Hcount. simpl in Hcount. nia.
Qed.

(** Every unary input has an actual source derivation. *)
Theorem audit_nat_encode_run_total : audit_nat_encode_run_total_statement.
Proof.
  unfold audit_nat_encode_run_total_statement. intro input.
  induction input as [|input IH].
  - exists xH, [AuditNatFrame 0], 2. constructor.
  - destruct IH as [previous [events [work Hrun]]].
    destruct (audit_positive_succ_run_total previous) as [output [succ_events [succ_work Hsucc]]].
    exists output, (AuditNatFrame (S input) :: events ++ succ_events), (2 + work + succ_work).
    eapply AuditNatSuccessor; eassumption.
Qed.

(** * Primitive and composite erasure *)

(** The binary natural encoder returns the original code. *)
Theorem audit_N_encode_erases : audit_N_encode_erases_statement.
Proof.
  intros [|p]; simpl; try reflexivity.
  pose proof (audit_positive_succ_erases p) as Herase.
  destruct (audit_positive_succ p) as [result events]. simpl in *. exact Herase.
Qed.

(** Positive encoding retains the input code. *)
Theorem audit_positive_encode_erases : audit_positive_encode_erases_statement.
Proof.
  intros input. reflexivity.
Qed.

(** Boolean encoding returns the original code. *)
Theorem audit_bool_encode_erases : audit_bool_encode_erases_statement.
Proof.
  intros []. reflexivity. reflexivity.
Qed.

(** Unit encoding returns the original code. *)
Theorem audit_unit_encode_erases : audit_unit_encode_erases_statement.
Proof.
  intros []. reflexivity.
Qed.

(** Signed encoding returns the original code. *)
Theorem audit_z_encode_erases : audit_z_encode_erases_statement.
Proof.
  intros []; reflexivity.
Qed.

(** Emission returns the original delimited stream. *)
Theorem audit_emit_code_erases : audit_emit_code_erases_statement.
Proof.
  unfold audit_emit_code_erases_statement. intro p.
  induction p as [p IH|p IH|]; intro tail; simpl; try reflexivity;
    specialize (IH tail); destruct (audit_emit_code p tail) as [bits events];
    simpl in *; now rewrite IH.
Qed.

(** Stream conversion returns the original positive code. *)
Theorem audit_stream_positive_erases : audit_stream_positive_erases_statement.
Proof.
  unfold audit_stream_positive_erases_statement. intro bits.
  induction bits as [|[] rest IH]; simpl; try reflexivity;
    destruct (audit_stream_positive rest) as [result events]; simpl in *; now rewrite IH.
Qed.

(** Pair encoding preserves the two actual component codes. *)
Theorem audit_pair_encode_erases : audit_pair_encode_erases_statement.
Proof.
  intros A B EA EB first second e1 e2 a b Hfirst Hsecond.
  unfold audit_pair_encode. destruct (first a) as [ac ae].
  destruct (second b) as [bc be]. simpl in Hfirst, Hsecond.
  pose proof (audit_emit_code_erases bc []) as Hb.
  destruct (audit_emit_code bc []) as [bt bf]. simpl in Hb.
  pose proof (audit_emit_code_erases ac bt) as Ha.
  destruct (audit_emit_code ac bt) as [stream af]. simpl in Ha.
  pose proof (audit_stream_positive_erases stream) as Hstream.
  destruct (audit_stream_positive stream) as [result sf]. simpl in Hstream.
  simpl. rewrite Hstream, Ha, Hb, Hfirst, Hsecond. reflexivity.
Qed.

(** List emission preserves every actual element code. *)
Theorem audit_emit_list_erases : audit_emit_list_erases_statement.
Proof.
  intros A E element enc input.
  induction input as [|x rest IH]; intro Hagree; simpl; try reflexivity.
  pose proof (Hagree x (or_introl eq_refl)) as Hx.
  assert (Hrest : forall y, In y rest -> fst (element y) = encode enc y).
  { intros y Hy. apply Hagree. now right. }
  specialize (IH Hrest).
  destruct (element x) as [code child]. simpl in Hx.
  destruct (audit_emit_list element rest) as [tail events]. simpl in IH.
  pose proof (audit_emit_code_erases code tail) as Hemit.
  destruct (audit_emit_code code tail) as [result frames]. simpl in Hemit.
  simpl. now rewrite Hemit, Hx, IH.
Qed.

(** List encoding preserves the resulting delimited stream. *)
Theorem audit_list_encode_erases : audit_list_encode_erases_statement.
Proof.
  intros A E element enc input Hagree.
  pose proof (audit_emit_list_erases A E element enc input Hagree) as Hemit.
  unfold audit_list_encode.
  destruct (audit_emit_list element input) as [bits events]. simpl in Hemit.
  pose proof (audit_stream_positive_erases bits) as Hstream.
  destruct (audit_stream_positive bits) as [result frames]. simpl in Hstream.
  simpl. now rewrite Hstream, Hemit.
Qed.

(** Sum encoding preserves the selected actual component code. *)
Theorem audit_sum_encode_erases : audit_sum_encode_erases_statement.
Proof.
  intros A B EA EB left right e1 e2 [a|b] Hleft Hright; simpl.
  - specialize (Hleft a eq_refl). destruct (left a) as [code events].
    simpl in *. now rewrite Hleft.
  - specialize (Hright b eq_refl). destruct (right b) as [code events].
    simpl in *. now rewrite Hright.
Qed.

(** Option encoding preserves the selected actual component code. *)
Theorem audit_option_encode_erases : audit_option_encode_erases_statement.
Proof.
  intros A E element enc [a|] Hagree; simpl; try reflexivity.
  specialize (Hagree a eq_refl). destruct (element a) as [code events].
  simpl in *. now rewrite Hagree.
Qed.

(** * Frame counts *)

(** Code emission visits each positive input bit once. *)
Theorem audit_emit_code_count : audit_emit_code_count_statement.
Proof.
  unfold audit_emit_code_count_statement. intro code.
  induction code as [code IH|code IH|]; intro tail; simpl; try reflexivity;
    specialize (IH tail); destruct (audit_emit_code code tail) as [bits events];
    simpl in *; lia.
Qed.

(** Stream conversion visits each input bit and its terminal case. *)
Theorem audit_stream_positive_count : audit_stream_positive_count_statement.
Proof.
  unfold audit_stream_positive_count_statement. intro bits.
  induction bits as [|[] rest IH]; simpl; try reflexivity;
    destruct (audit_stream_positive rest) as [result events]; simpl in *; lia.
Qed.

(** List emission counts each element and its emitted code frames. *)
Theorem audit_emit_list_count : audit_emit_list_count_statement.
Proof.
  intros A E element input.
  induction input as [|x rest IH]; simpl; try reflexivity.
  destruct (element x) as [code child] eqn:Hchild.
  destruct (audit_emit_list element rest) as [tail events] eqn:Htail.
  pose proof (audit_emit_code_count code tail) as Hcount.
  destruct (audit_emit_code code tail) as [bits frames] eqn:Hframes.
  simpl in *. rewrite !length_app, length_map. simpl. lia.
Qed.

(** Emitted streams contain twice the widths of the actual component codes. *)
Lemma audit_emit_list_length : forall A E (element : A -> positive * list E) input,
  length (fst (audit_emit_list element input)) = 2 * audit_encoded_bits element input.
Proof.
  intros A E element input. induction input as [|x rest IH]; simpl; try reflexivity.
  destruct (element x) as [code child].
  destruct (audit_emit_list element rest) as [tail events]. simpl in IH.
  pose proof (audit_emit_code_erases code tail) as Herase.
  destruct (audit_emit_code code tail) as [bits frames]. simpl in Herase.
  simpl. rewrite Herase, emit_code_length, IH. lia.
Qed.

(** List encoding counts emission and stream conversion frames. *)
Theorem audit_list_encode_count : audit_list_encode_count_statement.
Proof.
  intros A E element input.
  pose proof (audit_emit_list_count A E element input) as Hcount.
  pose proof (audit_emit_list_length A E element input) as Hlength.
  unfold audit_list_encode.
  destruct (audit_emit_list element input) as [bits events]. simpl in Hcount, Hlength.
  pose proof (audit_stream_positive_count bits) as Hstream.
  destruct (audit_stream_positive bits) as [result frames]. simpl in Hstream.
  simpl. rewrite length_app, length_map. lia.
Qed.

(** Pair encoding counts both component widths and stream frames. *)
Theorem audit_pair_encode_count : audit_pair_encode_count_statement.
Proof.
  intros A B EA EB first second a b.
  unfold audit_pair_encode.
  destruct (first a) as [ac ae]. destruct (second b) as [bc be].
  pose proof (audit_emit_code_count bc []) as Hb.
  pose proof (audit_emit_code_erases bc []) as Heb.
  destruct (audit_emit_code bc []) as [bt bf]. simpl in Hb, Heb.
  pose proof (audit_emit_code_count ac bt) as Ha.
  pose proof (audit_emit_code_erases ac bt) as Hea.
  destruct (audit_emit_code ac bt) as [stream af]. simpl in Ha, Hea.
  pose proof (audit_stream_positive_count stream) as Hstream.
  destruct (audit_stream_positive stream) as [result sf]. simpl in Hstream.
  simpl. rewrite ?length_app, ?length_map, ?length_app.
  rewrite Hea, Heb, !emit_code_length in Hstream. simpl in Hstream. lia.
Qed.
