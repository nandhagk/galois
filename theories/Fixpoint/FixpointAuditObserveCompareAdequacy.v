(** * Adequacy of observation key comparisons

    The counted scans retain strict tails and both directed passes.
    For example, a match at the head still contributes comparisons with the tail.
    Builds on: FixpointAuditObserveCompare. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditPrimitive
  CollectionsAuditPrimitiveAdequacy.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditWorklistCallbacks
  FixpointAuditObserveCompare.
Import List.ListNotations.

(** * Erasure and frame work *)

Lemma fx_compare_work_app X (first last : list (fx_observe_compare_event X)) :
  fx_observe_compare_work (first ++ last) =
    fx_observe_compare_work first + fx_observe_compare_work last.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - change (fx_observe_compare_event_work event + fx_observe_compare_work (rest ++ last) =
      (fx_observe_compare_event_work event + fx_observe_compare_work rest) +
        fx_observe_compare_work last).
    rewrite IH; lia.
Qed.

Lemma fx_exists_key_adequate X (EX : encoding X) x ys :
  fst (fx_observe_exists_key EX x ys) = existsb (observation_key_eqb EX x) ys /\
  fx_observe_compare_work (snd (fx_observe_exists_key EX x ys)) =
    fx_observe_exists_key_budget EX x ys.
Proof.
  induction ys as [|y rest IH].
  - split; reflexivity.
  - cbn [fx_observe_exists_key fx_observe_key_compare fx_observe_exists_key_budget existsb].
    destruct (fx_observe_exists_key EX x rest) as [out events] eqn:Hrest.
    cbn in IH; destruct IH as [Hout Hwork].
    cbn [fst snd fx_observe_compare_work fold_right fx_observe_compare_event_work].
    unfold observation_key_eqb in *; rewrite Hout; split; [reflexivity |].
    unfold fx_observe_compare_work in *; cbn in *; lia.
Qed.

Lemma fx_all_keys_adequate X (EX : encoding X) xs ys :
  fst (fx_observe_all_keys EX xs ys) =
    forallb (fun x => existsb (observation_key_eqb EX x) ys) xs /\
  fx_observe_compare_work (snd (fx_observe_all_keys EX xs ys)) =
    fx_observe_all_keys_budget EX xs ys.
Proof.
  induction xs as [|x rest IH].
  - split; reflexivity.
  - cbn [fx_observe_all_keys fx_observe_all_keys_budget forallb].
    pose proof (fx_exists_key_adequate X EX x ys) as Hfirst.
    destruct (fx_observe_exists_key EX x ys) as [found first].
    destruct (fx_observe_all_keys EX rest ys) as [out tail].
    cbn in Hfirst, IH; destruct Hfirst as [Hfound Hfirst]; destruct IH as [Hout Htail].
    change (found && out = (existsb (observation_key_eqb EX x) ys &&
      forallb (fun x => existsb (observation_key_eqb EX x) ys) rest) /\
      1 + fx_observe_compare_work (first ++ tail) =
      1 + fx_observe_exists_key_budget EX x ys + fx_observe_all_keys_budget EX rest ys).
    rewrite fx_compare_work_app.
    change (fx_observe_compare_work first = fx_observe_exists_key_budget EX x ys) in Hfirst.
    change (fx_observe_compare_work tail = fx_observe_all_keys_budget EX rest ys) in Htail.
    rewrite Hfound, Hout, Hfirst, Htail; split; [reflexivity | lia].
Qed.

(** Both directed scans produce the source result and fit the input bound. *)
Theorem fx_observe_seteq_correct : fx_observe_seteq_statement.
Proof.
  intros X EX xs ys.
  pose proof (fx_all_keys_adequate X EX xs ys) as Hfirst.
  pose proof (fx_all_keys_adequate X EX ys xs) as Hsecond.
  unfold fx_observe_seteq, observation_seteq, fx_observe_seteq_budget.
  destruct (fx_observe_all_keys EX xs ys) as [a first].
  destruct (fx_observe_all_keys EX ys xs) as [b second].
  cbn in Hfirst, Hsecond; destruct Hfirst as [Ha Hfirst]; destruct Hsecond as [Hb Hsecond].
  change (a && b = (forallb (fun x => existsb (observation_key_eqb EX x) ys) xs &&
    forallb (fun y => existsb (observation_key_eqb EX y) xs) ys) /\
    1 + fx_observe_compare_work (first ++ second) <=
    1 + fx_observe_all_keys_budget EX xs ys + fx_observe_all_keys_budget EX ys xs).
  rewrite fx_compare_work_app.
  change (fx_observe_compare_work first = fx_observe_all_keys_budget EX xs ys) in Hfirst.
  change (fx_observe_compare_work second = fx_observe_all_keys_budget EX ys xs) in Hsecond.
  rewrite Ha, Hb, Hfirst, Hsecond; split; [reflexivity | lia].
Qed.

(** Every suffix scan contributes to the duplicate check and its input bound. *)
Theorem fx_observe_nodup_correct : fx_observe_nodup_statement.
Proof.
  intros X EX xs; induction xs as [|x rest IH].
  - split; reflexivity.
  - cbn [fx_observe_nodup observation_nodup_check fx_observe_nodup_budget].
    pose proof (fx_exists_key_adequate X EX x rest) as Hfirst.
    destruct (fx_observe_exists_key EX x rest) as [found first].
    destruct (fx_observe_nodup EX rest) as [out tail].
    cbn in Hfirst, IH; destruct Hfirst as [Hfound Hfirst]; destruct IH as [Hout Htail].
    change (negb found && out = (negb (existsb (observation_key_eqb EX x) rest) &&
      observation_nodup_check EX rest) /\
      1 + fx_observe_compare_work (first ++ tail) <=
      1 + fx_observe_exists_key_budget EX x rest + fx_observe_nodup_budget EX rest).
    rewrite fx_compare_work_app.
    change (fx_observe_compare_work first = fx_observe_exists_key_budget EX x rest) in Hfirst.
    change (fx_observe_compare_work tail <= fx_observe_nodup_budget EX rest) in Htail.
    rewrite Hfound, Hout; split; [reflexivity | lia].
Qed.

(** * Captured encoder operands *)

(** Each comparison's recorded codes are the encodings of its own operands. *)
Definition fx_compare_codes {X} (EX : encoding X) (event : fx_observe_compare_event X) : Prop :=
  match event with
  | FxObserveCompare x y code1 code2 _ => code1 = encode EX x /\ code2 = encode EX y
  | FxObserveCompareCase => True
  end.

Lemma fx_exists_key_codes X (EX : encoding X) x ys :
  Forall (fx_compare_codes EX) (snd (fx_observe_exists_key EX x ys)).
Proof.
  induction ys as [|y rest IH].
  - constructor; [exact I | constructor].
  - cbn [fx_observe_exists_key fx_observe_key_compare].
    destruct (fx_observe_exists_key EX x rest) as [out events].
    cbn in IH |- *; constructor; [exact I |].
    constructor; [split; reflexivity | exact IH].
Qed.

Lemma fx_all_keys_codes X (EX : encoding X) xs ys :
  Forall (fx_compare_codes EX) (snd (fx_observe_all_keys EX xs ys)).
Proof.
  induction xs as [|x rest IH].
  - constructor; [exact I | constructor].
  - cbn [fx_observe_all_keys].
    pose proof (fx_exists_key_codes X EX x ys) as Hfirst.
    destruct (fx_observe_exists_key EX x ys) as [found first].
    destruct (fx_observe_all_keys EX rest ys) as [out tail].
    cbn in Hfirst, IH |- *; constructor; [exact I |].
    apply Forall_app; split; assumption.
Qed.

Lemma fx_seteq_codes X (EX : encoding X) xs ys :
  Forall (fx_compare_codes EX) (snd (fx_observe_seteq EX xs ys)).
Proof.
  pose proof (fx_all_keys_codes X EX xs ys) as Hfirst.
  pose proof (fx_all_keys_codes X EX ys xs) as Hsecond.
  unfold fx_observe_seteq.
  destruct (fx_observe_all_keys EX xs ys) as [a first].
  destruct (fx_observe_all_keys EX ys xs) as [b second].
  cbn in Hfirst, Hsecond |- *; constructor; [exact I |].
  apply Forall_app; split; assumption.
Qed.

Lemma fx_nodup_codes X (EX : encoding X) xs :
  Forall (fx_compare_codes EX) (snd (fx_observe_nodup EX xs)).
Proof.
  induction xs as [|x rest IH].
  - constructor; [exact I | constructor].
  - cbn [fx_observe_nodup].
    pose proof (fx_exists_key_codes X EX x rest) as Hfirst.
    destruct (fx_observe_exists_key EX x rest) as [found first].
    destruct (fx_observe_nodup EX rest) as [out tail].
    cbn in Hfirst, IH |- *; constructor; [exact I |].
    apply Forall_app; split; assumption.
Qed.

Lemma fx_compare_sources X C A B (EX : encoding X)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events :
  fx_observe_compare_source_laws EX source budget ->
  Forall (fx_compare_codes EX) events ->
  exists bodies, Forall2 (fx_observe_compare_source source) events bodies /\
    fx_declared_body_work (fx_body_weight budget) bodies <=
      fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events.
Proof.
  intros [Hexists Hbound] Hcodes; induction Hcodes as [|event rest Hcode Hrest IH].
  - exists []; split; [constructor | reflexivity].
  - destruct IH as [tail [Htail Hwork]].
    destruct event as [x y left right result |].
    + cbn [fx_compare_codes] in Hcode; destruct Hcode as [Hleft Hright]; subst left right.
      destruct (Hexists x) as [body1 Hbody1].
      destruct (Hexists y) as [body2 Hbody2].
      exists ([body1; body2] :: tail); split.
      * constructor; [|exact Htail].
        exists body1, body2; repeat split; assumption || reflexivity.
      * pose proof (Hbound x (encode EX x) body1 Hbody1) as Hbound1.
        pose proof (Hbound y (encode EX y) body2 Hbody2) as Hbound2.
        cbn [fx_declared_body_work fx_observe_compare_external_budget fold_right].
        unfold fx_one_body_work in Hbound1, Hbound2; unfold fx_declared_body_work in Hwork; lia.
    + exists ([] :: tail); split.
      * constructor; [reflexivity | exact Htail].
      * cbn [fx_declared_body_work fx_observe_compare_external_budget fold_right];
        unfold fx_declared_body_work in Hwork; lia.
Qed.

(** Set equality's comparison receipts are bounded per actual encoder call. *)
Theorem fx_observe_seteq_source : fx_observe_seteq_source_statement.
Proof.
  intros X C A B EX source budget xs ys Hlaws.
  pose proof (fx_observe_seteq_correct X EX xs ys) as Hcorrect.
  pose proof (fx_seteq_codes X EX xs ys) as Hcodes.
  destruct (fx_observe_seteq EX xs ys) as [out events].
  cbn in Hcorrect, Hcodes |- *; destruct Hcorrect as [Hout Hframe].
  destruct (fx_compare_sources X C A B EX source budget events Hlaws Hcodes)
    as [bodies [Hsource Hwork]].
  exists bodies; repeat split; try assumption; lia.
Qed.

(** Duplicate checking retains receipts for all comparisons, including strict tails. *)
Theorem fx_observe_nodup_source : fx_observe_nodup_source_statement.
Proof.
  intros X C A B EX source budget xs Hlaws.
  pose proof (fx_observe_nodup_correct X EX xs) as Hcorrect.
  pose proof (fx_nodup_codes X EX xs) as Hcodes.
  destruct (fx_observe_nodup EX xs) as [out events].
  cbn in Hcorrect, Hcodes |- *; destruct Hcorrect as [Hout Hframe].
  destruct (fx_compare_sources X C A B EX source budget events Hlaws Hcodes)
    as [bodies [Hsource Hwork]].
  exists bodies; repeat split; try assumption; lia.
Qed.

(** * Shared positive comparison boundary *)

(** The shared primitive retains the result and bounds the work of each captured key comparison. *)
Lemma fx_compare_positive_primitive X (EX : encoding X) x y :
  let '(out, events) := fx_observe_key_compare EX x y in
  let '(result, trace) := audit_positive_eqb (encode EX x) (encode EX y) in
  out = result /\
  events = [FxObserveCompare x y (encode EX x) (encode EX y) result] /\
  audit_positive_eqb_source_work trace <=
    2 * Nat.min (Pos.size_nat (encode EX x)) (Pos.size_nat (encode EX y)).
Proof.
  pose proof (audit_positive_eqb_erases (encode EX x) (encode EX y)) as Herase.
  pose proof (audit_positive_eqb_source_bound (encode EX x) (encode EX y)) as Hbound.
  destruct (audit_positive_eqb (encode EX x) (encode EX y)) as [result trace].
  cbn in Herase, Hbound |- *; rewrite <- Herase; repeat split; assumption || reflexivity.
Qed.
