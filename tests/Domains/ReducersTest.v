(** * Value reducer observations

    Reducers exchange facts between tagged word payloads.
    For example, known low bits can refine an interval after a second exchange.
    Builds on: Reducers and the concrete word domains.

    Groups:
    - [ReductionTests] Pairwise reduction of wrapped, congruence and known-bit payloads.
    - [CertifiedTests] The certified wrapped-bits factory and the pins that check it.
    - [ClippingTests] The clipped interval reduced against a congruence. *)

From Stdlib Require Import NArith ZArith Lia Bool List.
From Argent Require Import Time Tactics Std.
From Galois.Domains Require Import BitsLang ValueSig WordSig Tagged Harness ThresholdsSig Thresholds
  Interval IntervalBack WrappedSig Wrapped WrappedOps KnownBitsSig KnownBits KnownBitsBack
  CongruenceSig Congruence IntervalSig ReducersSig Reducers.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The low multiplier configuration used by the known-bit modules. *)
Module Config.
  Definition multiplier := MulLow.
End Config.
Module W := WrappedCode WordLanguageCode.
Module K := KnownBitsCode WordLanguageCode Config.
Module G := CongruenceCode WordLanguageCode.
Module Scalar := IntervalBaseCode ThresholdsCode.
Module I := IntervalPayloadCode WordLanguageCode ThresholdsCode Scalar.
Module WT := WrappedTableCode WordLanguageCode W.
Module KT := KnownBitsTableCode WordLanguageCode Config K.
Module GT := CongruenceTableCode WordLanguageCode G.
Module IT := IntervalWordTableCode WordLanguageCode ThresholdsCode Scalar I.
Module WB := TaggedCode WordLanguageCode W.
Module KB := TaggedCode WordLanguageCode K.
Module GB := TaggedCode WordLanguageCode G.
Module IB := TaggedCode WordLanguageCode I.
Module WTT := TaggedTableCode WordLanguageCode W WT.
Module KTT := TaggedTableCode WordLanguageCode K KT.
Module GTT := TaggedTableCode WordLanguageCode G GT.
Module ITT := TaggedTableCode WordLanguageCode I IT.
Module WD := HarnessCode BitsLangCode WB WTT.
Module KD := HarnessCode BitsLangCode KB KTT.
Module GD := HarnessCode BitsLangCode GB GTT.
Module ID := HarnessCode BitsLangCode IB ITT.
Module WR := WrappedBitsCode WordLanguageCode W K WD KD.
Module IR := IntervalCongrCode WordLanguageCode I G ID GD.
Module BR := IntervalBitsCode WordLanguageCode I K ID KD.

(** * Reduction *)

Module ReductionTests.

  (** Reducing the arc from 4 to 7 with the known bits 0 1 gives the known bits 8 5. *)
  Example wrapped_arc_gives_known_bits :
    WR.reduce (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 0 1)) =
      (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 8 5)).
  Proof. vm_compute. reflexivity. Qed.

  (** A second reduction pass narrows the arc from 4 to 7 to the arc from 5 to 7. *)
  Example second_pass_narrows_arc :
    fst (WR.reduce (WR.reduce (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 0 1)))) =
      TVal 4%positive (WItv 5 7).
  Proof. vm_compute. reflexivity. Qed.

  (** Reducing the interval from 0 to 10 against the congruence C 4 1 gives 1 to 9. *)
  Example congruence_rounds_interval_endpoints :
    fst (IR.to_left (TVal 8%positive (I (Fin 0) (Fin 10)), TVal 8%positive (C 4 1))) =
      TVal 8%positive (I (Fin 1) (Fin 9)).
  Proof. vm_compute. reflexivity. Qed.

  (** Known bits 0 1 raise the lower bound of the interval from 0 to 7 to 1. *)
  Example bits_refine_interval_lower_bound :
    fst (BR.to_left (TVal 4%positive (I (Fin 0) (Fin 7)), TVal 4%positive (Tnum 0 1))) =
      TVal 4%positive (I (Fin 1) (Fin 7)).
  Proof. vm_compute. reflexivity. Qed.

  (** Operands of different widths are returned unchanged. *)
  Example mismatched_widths_are_unchanged :
    WR.reduce (TVal 4%positive (WItv 4 7), TVal 8%positive (Tnum 0 1)) =
      (TVal 4%positive (WItv 4 7), TVal 8%positive (Tnum 0 1)).
  Proof. vm_compute. reflexivity. Qed.

End ReductionTests.

(** * Certified fixtures *)

(** The certified modules over the word language, with their domains and tables. *)
Module WF := Wrapped WordLanguage.
Module KF := KnownBits WordLanguage Config.
Module GF := Congruence WordLanguage.
Module SF := IntervalBaseCode Thresholds.
Module IF := IntervalPayload WordLanguage Thresholds SF.
Module WTF := WrappedTable WordLanguage WF.
Module KTF := KnownBitsTable WordLanguage Config KF.
Module GTF := CongruenceTable WordLanguage GF.
Module ITF := IntervalWordTable WordLanguage Thresholds SF IF.
Module WDomain := WordDomain WordLanguage WF WTF.
Module KDomain := WordDomain WordLanguage KF KTF.
Module GDomain := WordDomain WordLanguage GF GTF.
Module IDomain := WordDomain WordLanguage IF ITF.
Module WRF := WrappedBits WordLanguage Config WF KF WDomain.Domain KDomain.Domain.
Module IRF := IntervalCongr WordLanguage Thresholds SF IF GF IDomain.Domain GDomain.Domain.
Module BRF := IntervalBits WordLanguage Config Thresholds SF IF KF IDomain.Domain KDomain.Domain.

(** * Certified *)

Module CertifiedTests.

  (** The certified factory keeps the arc from 4 to 7 for the known bits 0 1. *)
  Example certified_factory_keeps_arc :
    fst (WRF.reduce (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 0 1))) =
      TVal 4%positive (WItv 4 7).
  Proof. vm_compute. reflexivity. Qed.

End CertifiedTests.

(** The pins that check the certified modules against their interfaces. *)
Module WPin <: WRAPPED_BITS_PIN WordLanguage Config WF KF WDomain.Domain KDomain.Domain WRF := WRF.
Module IPin <: INTERVAL_CONGR_PIN WordLanguage IF GF IDomain.Domain GDomain.Domain IRF := IRF.
Module BPin <: INTERVAL_BITS_PIN WordLanguage Config IF KF IDomain.Domain KDomain.Domain BRF := BRF.

(** * Time fixtures *)

(** The clock modules of the wrapped, known-bit, congruence and interval tables. *)
Module WTTime := WrappedT WordLanguageT.
Module KTTime := KnownBitsT WordLanguageT Config.
Module GTTime := CongruenceT WordLanguageT.
Module STTime := IntervalBaseT ThresholdsT.
Module ITTime := IntervalPayloadT WordLanguageT ThresholdsT STTime.
Module WTTTime := WrappedTableT WordLanguageT WTTime.
Module KTTTime := KnownBitsTableT WordLanguageT Config KTTime.
Module GTTTime := CongruenceTableT WordLanguageT GTTime.
Module ITTTime := IntervalWordTableT WordLanguageT ThresholdsT STTime ITTime.
Module WDomainTime := WordDomainT WordLanguageT WTTime WTTTime.
Module KDomainTime := WordDomainT WordLanguageT KTTime KTTTime.
Module GDomainTime := WordDomainT WordLanguageT GTTime GTTTime.
Module IDomainTime := WordDomainT WordLanguageT ITTime ITTTime.
Module WRT := WrappedBitsT WordLanguageT Config WTTime KTTime
  WDomainTime.Domain KDomainTime.Domain.
Module IRT := IntervalCongrT WordLanguageT ThresholdsT STTime ITTime GTTime
  IDomainTime.Domain GDomainTime.Domain.
Module BRT := IntervalBitsT WordLanguageT Config ThresholdsT STTime ITTime KTTime
  IDomainTime.Domain KDomainTime.Domain.
Module WPinTime <: WRAPPED_BITS_PIN WordLanguage Config WTTime KTTime
  WDomainTime.Domain KDomainTime.Domain WRT := WRT.
Module IPinTime <: INTERVAL_CONGR_PIN WordLanguage ITTime GTTime
  IDomainTime.Domain GDomainTime.Domain IRT := IRT.
Module BPinTime <: INTERVAL_BITS_PIN WordLanguage Config ITTime KTTime
  IDomainTime.Domain KDomainTime.Domain BRT := BRT.

(** * Clipping *)

Module ClippingTests.

  (** The right reduction of the interval from 15 to 20 with the congruence C 1 0 gives C 0 15. *)
  Example clipped_interval_gives_congruence :
    snd (IR.to_right (TVal 4%positive (I (Fin 15) (Fin 20)), TVal 4%positive (C 1 0))) =
      TVal 4%positive (C 0 15).
  Proof. vm_compute. reflexivity. Qed.

End ClippingTests.

(** * Reducer proofs *)

(** These three interval shapes form a subalgebra of the payload lattice operations. *)
Definition reducer_simple_interval (w : positive) (a : itv) : bool :=
  match a with
  | IBot | I NegInf PosInf => true
  | I (Fin lo) (Fin hi) => (lo =? 0) && (hi =? Word.modulus w - 1)
  | _ => false
  end.

(** Storage may charge a quadratic premium outside the three simple interval shapes. *)
Definition reducer_interval_premium (w : positive) (a : itv) : nat :=
  if reducer_simple_interval w a then 0%nat else (Pos.to_nat w) ^ 2.

(** The Boolean classifier identifies exactly bottom, raw top, and unsigned word top. *)
Lemma reducer_simple_interval_cases : forall w a, reducer_simple_interval w a = true ->
  a = IBot \/ a = I NegInf PosInf \/ a = I (Fin 0) (Fin (Word.modulus w - 1)).
Proof.
  intros w [|[|lo|] [|hi|]] Hsimple; cbn [reducer_simple_interval] in Hsimple;
    try discriminate; try (left; reflexivity); try (right; left; reflexivity).
  apply andb_true_iff in Hsimple as [Hlo Hhi].
  apply Z.eqb_eq in Hlo; apply Z.eqb_eq in Hhi; subst; right; right; reflexivity.
Qed.

(** The canonical unsigned word interval is one of the simple shapes. *)
Lemma reducer_simple_word_top : forall w,
  reducer_simple_interval w (I (Fin 0) (Fin (Word.modulus w - 1))) = true.
Proof.
  intro w; unfold reducer_simple_interval; rewrite !Z.eqb_refl; reflexivity.
Qed.

(** A binary operation preserving the simple shapes cannot create an unpaid premium. *)
Lemma reducer_premium_binary : forall w (f : itv -> itv -> itv),
  (forall a b, reducer_simple_interval w a = true ->
    reducer_simple_interval w b = true -> reducer_simple_interval w (f a b) = true) ->
  forall a b, (reducer_interval_premium w (f a b) <=
    reducer_interval_premium w a + reducer_interval_premium w b)%nat.
Proof.
  intros w f Hsimple a b; unfold reducer_interval_premium.
  destruct (reducer_simple_interval w a) eqn:Ha,
    (reducer_simple_interval w b) eqn:Hb.
  - rewrite (Hsimple a b Ha Hb); lia.
  - destruct (reducer_simple_interval w (f a b)); lia.
  - destruct (reducer_simple_interval w (f a b)); lia.
  - destruct (reducer_simple_interval w (f a b)); lia.
Qed.

Module ReducerIntervalView (L : WORD_LANGUAGE) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) (P : INTERVAL_PAYLOAD_PINNED L T S)
    <: INTERVAL_PAYLOAD_PINNED L T S.
  Definition p := P.p.
  Definition pleb := P.pleb.
  Definition pjoin := P.pjoin.
  Definition pmeet := P.pmeet.
  Definition pbot := P.pbot.
  Definition ptop := P.ptop.
  Definition pis_bot := P.pis_bot.
  Definition pconst := P.pconst.
  Definition ppoint := P.ppoint.
  Definition pwparam := P.pwparam.
  Definition pwiden := P.pwiden.
  Definition pnarrow := P.pnarrow.
  Definition pgamma := P.pgamma.
  Definition pwrank := P.pwrank.
  Definition pwiden_ub_l := P.pwiden_ub_l.
  Definition pwiden_ub_r := P.pwiden_ub_r.
  Definition pwiden_stable := P.pwiden_stable.
  Definition pwrank_widen := P.pwrank_widen.
  Definition pwrank_widen_le := P.pwrank_widen_le.
  Definition pnarrow_between := P.pnarrow_between.
  Definition pleb_refl := P.pleb_refl.
  Definition pleb_trans := P.pleb_trans.
  Definition pbot_least := P.pbot_least.
  Definition ptop_greatest := P.ptop_greatest.
  Definition pis_bot_bot := P.pis_bot_bot.
  Definition pis_bot_least := P.pis_bot_least.
  Definition pjoin_ub_l := P.pjoin_ub_l.
  Definition pjoin_ub_r := P.pjoin_ub_r.
  Definition pmeet_lb_l := P.pmeet_lb_l.
  Definition pgamma_mono := P.pgamma_mono.
  Definition pgamma_bot := P.pgamma_bot.
  Definition ptop_full := P.ptop_full.
  Definition pgamma_meet := P.pgamma_meet.
  Definition pis_bot_sound := P.pis_bot_sound.
  Definition pis_bot_below := P.pis_bot_below.
  Definition pconst_sound := P.pconst_sound.
  Definition ppoint_sound := P.ppoint_sound.
  Definition count_gt := P.count_gt.
  Definition count_lt := P.count_lt.
  Definition payload_wrank := P.payload_wrank.
  Definition pleb_def := P.pleb_def.
  Definition pis_bot_def := P.pis_bot_def.
  Definition pjoin_def := P.pjoin_def.
  Definition pmeet_def := P.pmeet_def.
  Definition pwiden_def := P.pwiden_def.
  Definition pnarrow_def := P.pnarrow_def.
  Definition pwrank_def := P.pwrank_def.
  Definition pbot_def := P.pbot_def.
  Definition ptop_def := P.ptop_def.
  Definition pconst_def := P.pconst_def.
  Definition ppoint_def := P.ppoint_def.
  Definition pgamma_def := P.pgamma_def.
End ReducerIntervalView.

Module ReducerInflatedInterval (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T) (P : INTERVAL_PAYLOAD_ALL L T S)
    <: INTERVAL_PAYLOAD_PINNED_T L T S.
  Module Functional := ReducerIntervalView L T S P.
  Include Functional.

  Definition psize (w : positive) (a : itv) : nat :=
    P.psize w a + reducer_interval_premium w a.
  Definition pwsize := P.pwsize.
  Definition T_pwiden := P.T_pwiden.
  Definition T_pnarrow := P.T_pnarrow.
  Definition T_pleb := P.T_pleb.
  Definition T_pjoin := P.T_pjoin.
  Definition T_pmeet := P.T_pmeet.
  Definition T_pis_bot := P.T_pis_bot.
  Definition T_ppoint := P.T_ppoint.
  Definition T_pconst := P.T_pconst.
  Definition T_ptop := P.T_ptop.
  Definition T_pbot := P.T_pbot.
  Definition c_payload : N := P.c_payload + 1.

  (** The word range is nonempty at every positive width. *)
  Lemma word_top_nonempty : forall w, (0 <=? Word.modulus w - 1) = true.
  Proof.
    intro w; apply Z.leb_le; pose proof (Word.modulus_pos w); lia.
  Qed.

  (** Scalar clipping fixes the canonical unsigned word interval. *)
  Lemma clip_word_top : forall w,
    interval_payload_clip S.interval_meet w (I (Fin 0) (Fin (Word.modulus w - 1))) =
      I (Fin 0) (Fin (Word.modulus w - 1)).
  Proof.
    intro w; unfold interval_payload_clip, S.interval_meet, S.bound_max,
      S.bound_min, S.bounds_nonempty, S.bound_leb.
    rewrite !Z.leb_refl; cbn; rewrite word_top_nonempty; reflexivity.
  Qed.

  (** Scalar clipping replaces raw top by the canonical unsigned word interval. *)
  Lemma clip_raw_top : forall w,
    interval_payload_clip S.interval_meet w (I NegInf PosInf) =
      I (Fin 0) (Fin (Word.modulus w - 1)).
  Proof.
    intro w; unfold interval_payload_clip, S.interval_meet, S.bound_max,
      S.bound_min, S.bounds_nonempty, S.bound_leb.
    cbn; rewrite word_top_nonempty; reflexivity.
  Qed.

  (** Scalar clipping preserves bottom. *)
  Lemma clip_bottom : forall w, interval_payload_clip S.interval_meet w IBot = IBot.
  Proof.
    reflexivity.
  Qed.

  (** Payload join preserves the three simple shapes. *)
  Lemma simple_join : forall w a b, reducer_simple_interval w a = true ->
    reducer_simple_interval w b = true -> reducer_simple_interval w (pjoin w a b) = true.
  Proof.
    intros w a b Ha Hb; apply reducer_simple_interval_cases in Ha, Hb.
    destruct Ha as [-> | [-> | ->]], Hb as [-> | [-> | ->]]; rewrite pjoin_def;
      rewrite ?clip_bottom, ?clip_raw_top, ?clip_word_top;
      unfold S.interval_join, S.bound_min, S.bound_max, S.bound_leb;
      cbn; rewrite ?Z.leb_refl; cbn; try reflexivity; apply reducer_simple_word_top.
  Qed.

  (** Payload meet preserves the three simple shapes. *)
  Lemma simple_meet : forall w a b, reducer_simple_interval w a = true ->
    reducer_simple_interval w b = true -> reducer_simple_interval w (pmeet w a b) = true.
  Proof.
    intros w a b Ha Hb; apply reducer_simple_interval_cases in Ha, Hb.
    destruct Ha as [-> | [-> | ->]], Hb as [-> | [-> | ->]]; rewrite pmeet_def;
      rewrite ?clip_bottom, ?clip_raw_top, ?clip_word_top;
      unfold S.interval_meet, S.bound_min, S.bound_max, S.bounds_nonempty, S.bound_leb;
      cbn; rewrite ?Z.leb_refl, ?word_top_nonempty; cbn; try reflexivity;
      apply reducer_simple_word_top.
  Qed.

  (** Payload narrowing preserves the three simple shapes. *)
  Lemma simple_narrow : forall w a b, reducer_simple_interval w a = true ->
    reducer_simple_interval w b = true -> reducer_simple_interval w (pnarrow w a b) = true.
  Proof.
    intros w a b Ha Hb; apply reducer_simple_interval_cases in Ha, Hb.
    destruct Ha as [-> | [-> | ->]], Hb as [-> | [-> | ->]]; rewrite pnarrow_def;
      rewrite ?clip_bottom, ?clip_raw_top, ?clip_word_top;
      unfold S.interval_narrow, S.narrow_bound; cbn;
      try reflexivity; apply reducer_simple_word_top.
  Qed.

  (** Payload widening preserves the three simple shapes independently of thresholds. *)
  Lemma simple_widen : forall q w a b, reducer_simple_interval w a = true ->
    reducer_simple_interval w b = true -> reducer_simple_interval w (pwiden q w a b) = true.
  Proof.
    intros q w a b Ha Hb; apply reducer_simple_interval_cases in Ha, Hb.
    destruct Ha as [-> | [-> | ->]], Hb as [-> | [-> | ->]]; rewrite pwiden_def, pleb_def;
      rewrite ?clip_bottom, ?clip_raw_top, ?clip_word_top;
      unfold S.interval_leb, S.interval_stable_widen, S.interval_widen, S.bound_leb;
      cbn;
      rewrite ?Z.leb_refl; cbn;
      rewrite ?clip_bottom, ?clip_word_top;
      try reflexivity; apply reducer_simple_word_top.
  Qed.

  (** Enlarging a payload's storage measure preserves every original lower bound. *)
  Lemma original_size_le : forall w a, (P.psize w a <= psize w a)%nat.
  Proof.
    intros; unfold psize; lia.
  Qed.

  (** The premium never exceeds the square of the width. *)
  Lemma premium_le : forall w a,
    (reducer_interval_premium w a <= (Pos.to_nat w) ^ 2)%nat.
  Proof.
    intros; unfold reducer_interval_premium; destruct (reducer_simple_interval w a); lia.
  Qed.

  (** The original top-construction clock fits the enlarged public constant. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w; pose proof (P.T_ptop_le w); unfold T_ptop, c_payload; nia.
  Qed.
  (** The original bottom-construction clock fits the enlarged public constant. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w; pose proof (P.T_pbot_le w); unfold T_pbot, c_payload; nia.
  Qed.
  (** Canonical top incurs no premium. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w; pose proof (P.ptop_size w) as Hsize.
    unfold psize, reducer_interval_premium, c_payload.
    rewrite ptop_def, reducer_simple_word_top; cbn [Nat.add];
      rewrite <- (ptop_def w); nia.
  Qed.
  (** Bottom incurs no premium. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w; pose proof (P.pbot_size w) as Hsize.
    unfold psize, reducer_interval_premium, c_payload.
    rewrite pbot_def; cbn [reducer_simple_interval Nat.add]; rewrite <- (pbot_def w); nia.
  Qed.
  (** A constant's existing quadratic budget also pays for its premium. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z; pose proof (P.pconst_size w z) as Hsize.
    pose proof (premium_le w (pconst w z)) as Hpremium.
    unfold pconst in *.
    unfold psize, c_payload; rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *;
      nia.
  Qed.
  (** Any premium in a join result is already present in an operand. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.pjoin_size w a b) as Hsize.
    pose proof (reducer_premium_binary w (pjoin w) (simple_join w) a b) as Hpremium.
    unfold pjoin in *.
    unfold psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Any premium in a meet result is already present in an operand. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.pmeet_size w a b) as Hsize.
    pose proof (reducer_premium_binary w (pmeet w) (simple_meet w) a b) as Hpremium.
    unfold pmeet in *.
    unfold psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Widening cannot create a premium from two simple operands. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b; pose proof (P.pwiden_size q w a b) as Hsize.
    pose proof (reducer_premium_binary w (pwiden q w) (simple_widen q w) a b) as Hpremium.
    unfold pwiden in *.
    unfold psize, pwsize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Narrowing cannot create a premium from two simple operands. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.pnarrow_size w a b) as Hsize.
    pose proof (reducer_premium_binary w (pnarrow w) (simple_narrow w) a b) as Hpremium.
    unfold pnarrow in *.
    unfold psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand sizes preserves the original widening time bound. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b; pose proof (P.T_pwiden_le q w a b).
    unfold T_pwiden, psize, pwsize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand sizes preserves the original narrowing time bound. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.T_pnarrow_le w a b).
    unfold T_pnarrow, psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand sizes preserves the original inclusion time bound. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.T_pleb_le w a b).
    unfold T_pleb, psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand sizes preserves the original join time bound. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.T_pjoin_le w a b).
    unfold T_pjoin, psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand sizes preserves the original meet time bound. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b; pose proof (P.T_pmeet_le w a b).
    unfold T_pmeet, psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand size preserves the original bottom-test time bound. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a; pose proof (P.T_pis_bot_le w a).
    unfold T_pis_bot, psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** Enlarging operand size preserves the original point-query time bound. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a; pose proof (P.T_ppoint_le w a).
    unfold T_ppoint, psize, c_payload; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  (** The original constant-construction clock fits the enlarged public constant. *)
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z; pose proof (P.T_pconst_le w z); unfold T_pconst, c_payload; nia.
  Qed.
End ReducerInflatedInterval.

Module ReducerEmptyTableCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    <: WORD_TABLE_OPS L W.
  Definition wfwd (_ : L.op) (_ : positive) (_ : list (positive * W.p)) : option W.p :=
    None.
  Definition wbwd (_ : L.op) (_ : positive) (_ : W.p)
      (_ : list (positive * W.p)) : option (list W.p) := None.
End ReducerEmptyTableCode.

Module ReducerEmptyTable (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) <: WORD_TABLE L W.
  Include ReducerEmptyTableCode L W.
  (** No successful forward entry can violate the table's conditional soundness law. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wps cs z r H; discriminate.
  Qed.
  (** No successful backward entry can violate the table's conditional soundness law. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof.
    intros o rw q wps ys cs z H; discriminate.
  Qed.
End ReducerEmptyTable.

Module ReducerEmptyTableT (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    <: WORD_TABLE_T L W.
  Include ReducerEmptyTable L W.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_word_table : N := 1.
  (** The empty forward table's derived clock is constant. *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros; time_unfold T_wfwd; cbn beta iota zeta; unfold c_word_table.
    rewrite !Nat.pow_2_r, !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_add; nia.
  Qed.
  (** The empty backward table's derived clock is constant. *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q + fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros; time_unfold T_wbwd; cbn beta iota zeta; unfold c_word_table.
    rewrite !Nat.pow_2_r, !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_add; nia.
  Qed.
  (** The empty table produces no forward payload whose storage needs charging. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (W.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs r H; discriminate.
  Qed.
  (** The empty table produces no backward payload list whose storage needs charging. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q + fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs ys H; discriminate.
  Qed.
End ReducerEmptyTableT.

Module ReducerIntervalSizeCounterexample (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (T : THRESHOLDS_T) (S : INTERVAL_SCALAR_T T)
    (P : INTERVAL_PAYLOAD_ALL L T S) (K : KNOWN_BITS_T L C).
  Module Large := ReducerInflatedInterval L T S P.
  Module LeftTable := ReducerEmptyTableT L Large.
  Module RightTable := ReducerEmptyTableT L K.
  Module LeftDomain := WordDomainT L Large LeftTable.
  Module RightDomain := WordDomainT L K RightTable.
  Module Reduction := IntervalBits L C T S Large K LeftDomain.Domain RightDomain.Domain.

  (** Even a one-bit word has at least two possible unsigned values. *)
  Lemma word_modulus_two : forall w, 2 <= Word.modulus w.
  Proof.
    intro w; rewrite Word.modulus_half; pose proof (Word.half_pos w); lia.
  Qed.

  (** Requiring the low bit to be one excludes the lower endpoint of unsigned top. *)
  Lemma one_bit_hull : forall w,
    bits_interval w (Tnum 0 1) = I (Fin 1) (Fin (Word.modulus w - 1)).
  Proof.
    intro w; unfold bits_interval, bits_hull; cbn [zeros ones].
    rewrite !reducer_tnum_wrap, Word.wrap_0, Z.lxor_0_l, Z.ones_equiv.
    replace (Z.pred (2 ^ Zpos w)) with (Word.modulus w - 1)
      by (unfold Word.modulus; lia).
    rewrite Word.wrap_id by (unfold Word.is_word; pose proof (word_modulus_two w); lia).
    assert (Hnonempty : (1 <=? Word.modulus w - 1) = true).
    { apply Z.leb_le; pose proof (word_modulus_two w); lia. }
    rewrite Hnonempty; reflexivity.
  Qed.

  (** The one-bit hull already lies within the unsigned word range. *)
  Lemma clip_one_bit_hull : forall w,
    interval_payload_clip S.interval_meet w (I (Fin 1) (Fin (Word.modulus w - 1))) =
      I (Fin 1) (Fin (Word.modulus w - 1)).
  Proof.
    intro w; unfold interval_payload_clip, S.interval_meet, S.bound_max,
      S.bound_min, S.bounds_nonempty, S.bound_leb.
    rewrite !Z.leb_refl; cbn.
    change ((if (1 <=? Word.modulus w - 1) then
      I (Fin 1) (Fin (Word.modulus w - 1)) else IBot) =
      I (Fin 1) (Fin (Word.modulus w - 1))).
    assert (Hnonempty : (1 <=? Word.modulus w - 1) = true).
    { apply Z.leb_le; pose proof (word_modulus_two w); lia. }
    rewrite Hnonempty; reflexivity.
  Qed.

  (** The required precision pin maps raw top to the nontrivial one-bit hull. *)
  Lemma pinned_left_result : forall w,
    Large.pmeet w (I NegInf PosInf) (bits_interval w (Tnum 0 1)) =
      I (Fin 1) (Fin (Word.modulus w - 1)).
  Proof.
    intro w; rewrite one_bit_hull, Large.pmeet_def, Large.clip_raw_top, clip_one_bit_hull.
    unfold S.interval_meet, S.bound_max, S.bound_min, S.bounds_nonempty, S.bound_leb.
    rewrite !Z.leb_refl; cbn.
    change ((if (1 <=? Word.modulus w - 1) then
      I (Fin 1) (Fin (Word.modulus w - 1)) else IBot) =
      I (Fin 1) (Fin (Word.modulus w - 1))).
    assert (Hnonempty : (1 <=? Word.modulus w - 1) = true).
    { apply Z.leb_le; pose proof (word_modulus_two w); lia. }
    rewrite Hnonempty; reflexivity.
  Qed.

  (** Both input sizes grow only linearly with the width. *)
  Lemma initial_pair_size : forall w,
    (LeftDomain.Domain.size (TVal w (I NegInf PosInf)) +
      RightDomain.Domain.size (TVal w (Tnum 0 1)) + 1 = 4 * Pos.to_nat w + 6)%nat.
  Proof.
    intro w; change (Pos.to_nat w + Large.psize w (I NegInf PosInf) + 1 +
      (Pos.to_nat w + K.psize w (Tnum 0 1) + 1) + 1 = 4 * Pos.to_nat w + 6)%nat.
    unfold Large.psize, reducer_interval_premium.
    rewrite P.psize_def, K.psize_bits.
    change (Pos.to_nat w + (Pos.to_nat w + 0 + 1 + 0) + 1 +
      (Pos.to_nat w + (Pos.to_nat w + 1 + 1) + 1) + 1 = 4 * Pos.to_nat w + 6)%nat.
    lia.
  Qed.

  (** The pinned output carries the quadratic premium allowed by the payload interface. *)
  Lemma final_pair_size : forall w,
    (N.of_nat ((Pos.to_nat w) ^ 2) <=
      N.of_nat (LeftDomain.Domain.size (TVal w (I (Fin 1) (Fin (Word.modulus w - 1)))) +
        RightDomain.Domain.size (TVal w (Tnum 0 1))))%N.
  Proof.
    intro w; change (N.of_nat ((Pos.to_nat w) ^ 2) <=
      N.of_nat (Pos.to_nat w + Large.psize w (I (Fin 1) (Fin (Word.modulus w - 1))) + 1 +
        RightDomain.Domain.size (TVal w (Tnum 0 1))))%N.
    change (N.of_nat ((Pos.to_nat w) ^ 2) <=
      N.of_nat (Pos.to_nat w +
        (P.psize w (I (Fin 1) (Fin (Word.modulus w - 1))) + (Pos.to_nat w) ^ 2) + 1 +
        RightDomain.Domain.size (TVal w (Tnum 0 1))))%N.
    rewrite !Nat2N.inj_add; lia.
  Qed.

  (** No implementation retaining the exact precision pin can satisfy linear left storage. *)
  Theorem no_linear_precision_left_size : forall step,
    (forall w a b, step (TVal w a, TVal w b) =
      (TVal w (Large.pmeet w a (bits_interval w b)), TVal w b)) ->
    ~ exists c : N, forall a b,
      (N.of_nat (LeftDomain.Domain.size (fst (step (a, b))) + RightDomain.Domain.size b) <=
        c * N.of_nat (LeftDomain.Domain.size a + RightDomain.Domain.size b + 1))%N.
  Proof.
    intros step Hprecision [c Hbound].
    set (w := Pos.of_nat (8 * (N.to_nat c + 1))).
    specialize (Hbound (TVal w (I NegInf PosInf)) (TVal w (Tnum 0 1))).
    rewrite Hprecision, pinned_left_result in Hbound; cbn [fst] in Hbound.
    rewrite initial_pair_size in Hbound.
    pose proof (final_pair_size w) as Hlarge.
    assert (Hwidth : Pos.to_nat w = (8 * (N.to_nat c + 1))%nat).
    { unfold w; apply Nat2Pos.id; lia. }
    assert (Hsquare : (N.of_nat ((Pos.to_nat w) ^ 2) <=
      c * N.of_nat (4 * Pos.to_nat w + 6))%N) by (eapply N.le_trans; eassumption).
    rewrite Hwidth, Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add, N2Nat.id in Hsquare.
    clear -Hsquare; nia.
  Qed.
End ReducerIntervalSizeCounterexample.

Module ConcreteIntervalSizeCounterexample := ReducerIntervalSizeCounterexample
  WordLanguageT Config ThresholdsT STTime ITTime KTTime.
