(** * Interval backward operations

    Result assumptions refine comparisons and nonwrapping arithmetic.
    For example, equality to one refines both operands of an equality test.
    Builds on: IntervalOps and fixed-width word operators. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time Std.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import IntervalOps ThresholdsSig IntervalSig ValueSig WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module IntervalBackCode (T : THRESHOLDS_OPS) (Scalar : INTERVAL_SCALAR_OPS T).
  Include IntervalOpsCode T Scalar.
Definition interval_is_point (i : itv) (z : Z) : bool :=
  match interval_finite_helper i with
  | Some (lo, hi) => Z.eqb lo z && Z.eqb hi z
  | None => false
  end.

Definition interval_assume_pair (o : op) (w : width) (a b q : itv) : itv * itv :=
  match o with
  | bveq => if interval_is_point q 1 then interval_assume_equal a b
            else if interval_is_point q 0 then interval_assume_neq a b else (a, b)
  | bvne => if interval_is_point q 0 then interval_assume_equal a b
            else if interval_is_point q 1 then interval_assume_neq a b else (a, b)
  | bvult => if interval_is_point q 1 then interval_assume_ult a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ule b a)
             else (a, b)
  | bvule => if interval_is_point q 1 then interval_assume_ule a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ult b a)
             else (a, b)
  | bvslt => if interval_is_point q 1 then interval_assume_signed w true true a b
             else if interval_is_point q 0 then interval_assume_signed w true false a b
             else (a, b)
  | bvsle => if interval_is_point q 1 then interval_assume_signed w false true a b
             else if interval_is_point q 0 then interval_assume_signed w false false a b
             else (a, b)
  | bvadd => interval_assume_add w a b q
  | bvsub => interval_assume_sub a b q
  | _ => (a, b)
  end.

  Definition interval_bwd1 rw q (xs : list (width * itv)) : list itv :=
    match xs with
    | [(w, a)] => [interval_assume_rewrap rw (interval_clip w a) q]
    | _ => []
    end.
  Definition interval_bwd2 o (_ : width) q (xs : list (width * itv)) : list itv :=
    match xs with
    | [(wa, a); (wb, b)] =>
      let refined := interval_assume_pair o wa (interval_clip wa a) (interval_clip wb b) q in
      [fst refined; snd refined]
    | _ => []
    end.
End IntervalBackCode.

Module IntervalPayloadCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    (Scalar : INTERVAL_SCALAR_OPS T)
    <: (WORD_PAYLOAD_OPS L with Definition p := itv).
  Definition p := itv.
  Definition interval_top (w : positive) := I (Fin 0) (Fin (Word.modulus w - 1)).
  Definition interval_clip w a := interval_payload_clip Scalar.interval_meet w a.
  Definition pleb w a b := Scalar.interval_leb (interval_clip w a) (interval_clip w b).
  Definition pjoin w a b := Scalar.interval_join (interval_clip w a) (interval_clip w b).
  Definition pmeet w a b := Scalar.interval_meet (interval_clip w a) (interval_clip w b).
  Definition pbot (_ : positive) := IBot.
  Definition ptop w := interval_top w.
  Definition pis_bot w a := Scalar.interval_is_bot (interval_clip w a).
  Definition pconst w z := I (Fin (Word.wrap w z)) (Fin (Word.wrap w z)).
  Definition ppoint w a := Scalar.interval_singleton (interval_clip w a).
  Definition pwparam := ttree.
  Definition pwiden ts w a b :=
    if pleb w b a then a else interval_clip w
      (Scalar.interval_stable_widen ts (interval_clip w a) (interval_clip w b)).
  Definition pnarrow w a b := Scalar.interval_narrow (interval_clip w a) (interval_clip w b).
End IntervalPayloadCode.

Module IntervalWordTableCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    (Scalar : INTERVAL_SCALAR_OPS T)
    (D : WORD_PAYLOAD_OPS L with Definition p := itv) <: WORD_TABLE_OPS L D.
  Include IntervalBackCode T Scalar.
  Definition wfwd (o : L.op) (rw : positive) (xs : list (positive * D.p)) : option D.p :=
    match o, xs with
    | (bvnot | bvneg | bvclz | bvctz | bvpopcnt | bvzext _ | bvtrunc _ | bvsext _),
        [(w, a)] =>
      let a := interval_clip w a in
      Some (match o with
        | bvnot => interval_not rw a
        | bvneg => interval_neg rw a
        | bvclz | bvctz | bvpopcnt => interval_counts rw
        | bvzext _ | bvtrunc _ => interval_rewrap rw a
        | _ => interval_sext rw w a
        end)
    | (bvadd | bvsub | bvmul | bvudiv | bvurem | bvsdiv | bvsrem | bvsmod |
       bvand | bvor | bvxor | bvshl | bvlshr | bvashr | bveq | bvne |
       bvult | bvule | bvslt | bvsle | bvconcat), [(wa, a); (wb, b)] =>
      let a := interval_clip wa a in
      let b := interval_clip wb b in
      Some (match o with
        | bvadd => interval_add rw a b | bvsub => interval_sub rw a b
        | bvmul => interval_mul rw a b | bvudiv => interval_udiv rw a b
        | bvurem => interval_urem rw a b | bvsdiv => interval_sdiv rw a b
        | bvsrem => interval_srem rw a b | bvsmod => interval_smod rw a b
        | bvand => interval_and rw a b | bvor | bvxor => interval_or_xor rw a b
        | bvshl => interval_shl rw a b | bvlshr => interval_lshr rw a b
        | bvashr => interval_ashr rw a b | bveq => interval_eq a b
        | bvne => interval_bool_not (interval_eq a b) | bvult => interval_ult a b
        | bvule => interval_ule a b | bvslt => interval_signed_compare wa true a b
        | bvsle => interval_signed_compare wa false a b
        | _ => interval_concat rw wb a b
        end)
    | bvite, [_; (wa, a); (wb, b)] =>
      Some (Scalar.interval_join (interval_clip wa a) (interval_clip wb b))
    | _, _ => None
    end.
  Definition wbwd (o : L.op) (rw : positive) (q : D.p)
      (xs : list (positive * D.p)) : option (list D.p) :=
    match o, xs with
    | (bvzext _ | bvtrunc _), [_] => Some (interval_bwd1 rw q xs)
    | (bveq | bvne | bvult | bvule | bvslt | bvsle | bvadd | bvsub), [_; _] =>
      Some (interval_bwd2 o rw q xs)
    | _, _ => None
    end.
End IntervalWordTableCode.

Local Close Scope Z_scope.

Module IntervalPayload (L : WORD_LANGUAGE) (T : THRESHOLDS) (Scalar : INTERVAL_SCALAR_OPS T)
    <: INTERVAL_PAYLOAD_PINNED L T Scalar.
  Include IntervalPayloadCode L T Scalar.
  Include Scalar.
  Include INTERVAL_PAYLOAD_SPEC T Scalar.
  (** Every bound is below itself. *)
  Theorem bound_leb_refl : forall a, bound_leb a a = true.
  Proof.
    intros [|z|]; cbn; try reflexivity.
    apply Z.leb_refl.
  Qed.
  
  (** Bound comparison is transitive. *)
  Theorem bound_leb_trans : forall a b c,
    bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
  Proof.
    intros [|x|] [|y|] [|z|]; cbn; try discriminate; try reflexivity.
    intros Hxy Hyz. apply Z.leb_le in Hxy. apply Z.leb_le in Hyz.
    apply Z.leb_le. lia.
  Qed.
  
  (** Any two bounds are comparable. *)
  Theorem bound_leb_total : forall a b, bound_leb a b = true \/ bound_leb b a = true.
  Proof.
    intros [|x|] [|y|]; cbn; try (now left); try (now right).
    destruct (Z.leb x y) eqn:Hxy; [now left|right].
    apply Z.leb_gt in Hxy. apply Z.leb_le. lia.
  Qed.
  
  (** The minimum is below its left input. *)
  Theorem bound_min_lower_l : forall a b, bound_leb (bound_min a b) a = true.
  Proof.
    intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
    - apply bound_leb_refl.
    - destruct (bound_leb_total a b) as [H|H]; congruence.
  Qed.
  
  (** The minimum is below its right input. *)
  Theorem bound_min_lower_r : forall a b, bound_leb (bound_min a b) b = true.
  Proof.
    intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
    - exact Hab.
    - apply bound_leb_refl.
  Qed.
  
  (** A common lower bound is below the minimum. *)
  Theorem bound_min_greatest : forall a b c,
    bound_leb c a = true -> bound_leb c b = true -> bound_leb c (bound_min a b) = true.
  Proof.
    intros a b c Ha Hb. unfold bound_min. destruct (bound_leb a b); assumption.
  Qed.
  
  (** The maximum is above its left input. *)
  Theorem bound_max_upper_l : forall a b, bound_leb a (bound_max a b) = true.
  Proof.
    intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - exact Hab.
    - apply bound_leb_refl.
  Qed.
  
  (** The maximum is above its right input. *)
  Theorem bound_max_upper_r : forall a b, bound_leb b (bound_max a b) = true.
  Proof.
    intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - apply bound_leb_refl.
    - destruct (bound_leb_total a b) as [H|H]; congruence.
  Qed.
  
  (** The maximum is below every common upper bound. *)
  Theorem bound_max_least : forall a b c,
    bound_leb a c = true -> bound_leb b c = true -> bound_leb (bound_max a b) c = true.
  Proof.
    intros a b c Ha Hb. unfold bound_max. destruct (bound_leb a b); assumption.
  Qed.

  Definition pgamma (w : positive) (a : p) (z : Z) : Prop :=
    L.is_word w z /\ match a with IBot => False | I lo hi => in_bnd lo hi z end.
  Definition pwrank := payload_wrank.

  (** Mutual comparison identifies the same extended bound. *)
  Lemma bound_leb_antisym : forall a b,
    bound_leb a b = true -> bound_leb b a = true -> a = b.
  Proof.
    intros [|x|] [|y|]; cbn; try discriminate; try reflexivity.
    intros Hxy Hyx. apply Z.leb_le in Hxy, Hyx. f_equal. lia.
  Qed.

  (** A maximum retains its left input when that input is greater. *)
  Lemma bound_max_left : forall a b, bound_leb b a = true -> bound_max a b = a.
  Proof.
    intros a b Hba. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - symmetry. now apply bound_leb_antisym.
    - reflexivity.
  Qed.

  (** Raw interval inclusion is reflexive. *)
  Lemma interval_leb_refl : forall a, interval_leb a a = true.
  Proof.
    intros [|lo hi]; cbn; [reflexivity|]. now rewrite !bound_leb_refl.
  Qed.

  (** Raw interval inclusion composes. *)
  Lemma interval_leb_trans : forall a b c,
    interval_leb a b = true -> interval_leb b c = true -> interval_leb a c = true.
  Proof.
    intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc. apply andb_true_iff in Hab as [Hlb Hhb].
    apply andb_true_iff in Hbc as [Hlc Hhc]. apply andb_true_iff. split;
      eapply bound_leb_trans; eassumption.
  Qed.

  (** Raw intersection lies below its left operand. *)
  Lemma interval_meet_lower_l : forall a b, interval_leb (interval_meet a b) a = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity.
    destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
    apply andb_true_iff. split; [apply bound_max_upper_l|apply bound_min_lower_l].
  Qed.

  (** Raw intersection lies below its right operand. *)
  Lemma interval_meet_lower_r : forall a b, interval_leb (interval_meet a b) b = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity.
    destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
    apply andb_true_iff. split; [apply bound_max_upper_r|apply bound_min_lower_r].
  Qed.

  (** A finite nonempty common lower bound lies below the intersection. *)
  Lemma interval_meet_greatest : forall a b lo hi, (lo <= hi)%Z ->
    interval_leb (I (Fin lo) (Fin hi)) a = true ->
    interval_leb (I (Fin lo) (Fin hi)) b = true ->
    interval_leb (I (Fin lo) (Fin hi)) (interval_meet a b) = true.
  Proof.
    intros [|la ha] [|lb hb] lo hi Hordered; cbn; try discriminate.
    intros Ha Hb. apply andb_true_iff in Ha as [Hla Hha].
    apply andb_true_iff in Hb as [Hlb Hhb].
    assert (Hlo : bound_leb (bound_max la lb) (Fin lo) = true).
    { apply bound_max_least; assumption. }
    assert (Hhi : bound_leb (Fin hi) (bound_min ha hb) = true).
    { apply bound_min_greatest; assumption. }
    assert (Hends : bound_leb (bound_max la lb) (bound_min ha hb) = true).
    { eapply bound_leb_trans; [exact Hlo|].
      eapply bound_leb_trans; [|exact Hhi]. cbn. now apply Z.leb_le. }
    assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
    { destruct (bound_max la lb), (bound_min ha hb); cbn in *;
        try discriminate; assumption. }
    rewrite Hnonempty. apply andb_true_iff. now split.
  Qed.

  (** Every nonbottom clipped interval has finite ordered word endpoints. *)
  Lemma interval_clip_shape : forall w a,
    interval_clip w a = IBot \/ exists lo hi,
      interval_clip w a = I (Fin lo) (Fin hi) /\ (0 <= lo /\ lo <= hi /\ hi < Word.modulus w)%Z.
  Proof.
    intros w [|lo hi]; [left; reflexivity|].
    unfold interval_clip, interval_payload_clip, Scalar.interval_meet.
    remember (bound_max lo (Fin 0)) as lower eqn:Hlower.
    remember (bound_min hi (Fin (Word.modulus w - 1))) as upper eqn:Hupper.
    destruct (bounds_nonempty lower upper) eqn:Hnonempty; [right|left; reflexivity].
    assert (Hlo : bound_leb (Fin 0) lower = true).
    { subst lower. apply bound_max_upper_r. }
    assert (Hhi : bound_leb upper (Fin (Word.modulus w - 1)) = true).
    { subst upper. apply bound_min_lower_r. }
    destruct lower as [|l|], upper as [|h|]; cbn [bound_leb bounds_nonempty] in Hlo, Hhi, Hnonempty;
      try discriminate.
    exists l, h. split; [reflexivity|].
    apply Z.leb_le in Hlo, Hhi, Hnonempty. lia.
  Qed.

  (** Clipping leaves a finite interval inside its word range unchanged. *)
  Lemma interval_clip_fixed : forall w lo hi, (0 <= lo /\ lo <= hi /\ hi < Word.modulus w)%Z ->
    interval_clip w (I (Fin lo) (Fin hi)) = I (Fin lo) (Fin hi).
  Proof.
    intros w lo hi Hrange.
    unfold interval_clip, interval_payload_clip, Scalar.interval_meet.
    rewrite bound_max_left by (cbn; apply Z.leb_le; lia).
    unfold bound_min. cbn [bound_leb].
    rewrite (proj2 (Z.leb_le hi (Word.modulus w - 1))) by lia.
    cbn [bounds_nonempty bound_leb]. rewrite (proj2 (Z.leb_le lo hi)) by lia.
    reflexivity.
  Qed.

  (** Clipping twice is the same as clipping once. *)
  Lemma interval_clip_idem : forall w a, interval_clip w (interval_clip w a) = interval_clip w a.
  Proof.
    intros w a. destruct (interval_clip_shape w a) as [Hbot|[lo [hi [Hshape Hrange]]]].
    - rewrite Hbot. reflexivity.
    - rewrite Hshape. now apply interval_clip_fixed.
  Qed.

  (** Clipping preserves raw interval inclusion. *)
  Lemma interval_clip_mono : forall w a b,
    interval_leb a b = true -> interval_leb (interval_clip w a) (interval_clip w b) = true.
  Proof.
    intros w a b Hab. destruct (interval_clip_shape w a) as [Hbot|[lo [hi [Hshape Hrange]]]].
    - rewrite Hbot. reflexivity.
    - rewrite Hshape. unfold interval_clip, interval_payload_clip.
      apply interval_meet_greatest; [lia| |].
      + eapply interval_leb_trans; [|exact Hab].
        rewrite <- Hshape. apply interval_meet_lower_l.
      + rewrite <- Hshape. apply interval_meet_lower_r.
  Qed.

  (** Bound membership agrees with the two endpoint comparisons. *)
  Lemma in_bnd_leb : forall lo hi z, in_bnd lo hi z <->
    bound_leb lo (Fin z) = true /\ bound_leb (Fin z) hi = true.
  Proof.
    intros [|lo|] [|hi|] z; unfold in_bnd; cbn [bound_leb];
      rewrite ?Z.leb_le; intuition congruence.
  Qed.

  (** Raw interval inclusion preserves payload meaning. *)
  Lemma pgamma_raw_mono : forall w a b z,
    interval_leb a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w [|la ha] [|lb hb] z Hle [Hw Ha]; try contradiction; try discriminate.
    cbn in Hle. apply andb_true_iff in Hle as [Hlower Hupper].
    apply in_bnd_leb in Ha as [Hlo Hhi]. split; [exact Hw|].
    apply in_bnd_leb. split; eapply bound_leb_trans; eassumption.
  Qed.

  (** Raw intersection preserves every common word. *)
  Lemma pgamma_raw_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (interval_meet a b) z.
  Proof.
    intros w [|la ha] [|lb hb] z [Hw Ha] [_ Hb]; try contradiction.
    apply in_bnd_leb in Ha as [Hla Hha]. apply in_bnd_leb in Hb as [Hlb Hhb].
    assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
    { apply bound_max_least; assumption. }
    assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
    { apply bound_min_greatest; assumption. }
    assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
    { eapply bound_leb_trans; eassumption. }
    assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
    { destruct (bound_max la lb), (bound_min ha hb); cbn in *;
        try discriminate; assumption. }
    unfold interval_meet. rewrite Hnonempty. split; [exact Hw|].
    apply in_bnd_leb. now split.
  Qed.

  (** Clipping preserves every represented word. *)
  Lemma pgamma_clip : forall w a z, pgamma w a z -> pgamma w (interval_clip w a) z.
  Proof.
    intros w a z Ha. unfold interval_clip, interval_payload_clip.
    apply pgamma_raw_meet; [exact Ha|].
    destruct Ha as [Hw _]. split; [exact Hw|].
    unfold in_bnd. destruct Hw as [Hlo Hhi]. split; lia.
  Qed.

  (** Removing the clip preserves every represented word. *)
  Lemma pgamma_unclip : forall w a z, pgamma w (interval_clip w a) z -> pgamma w a z.
  Proof.
    intros w a z Ha. eapply pgamma_raw_mono; [|exact Ha].
    apply interval_meet_lower_l.
  Qed.
  (** Widening the lower endpoint covers the next endpoint. *)
  Lemma widen_lower_next : forall q old next,
    bound_leb (widen_lower q old next) next = true.
  Proof.
    intros q old next. unfold widen_lower. destruct (bound_leb old next) eqn:Hle.
    - exact Hle.
    - destruct next as [|z|]; cbn; try reflexivity.
      destruct (T.below q z) as [u|] eqn:Hbelow; [|reflexivity].
      cbn. apply Z.leb_le. exact (proj2 (T.below_sound q z u Hbelow)).
  Qed.

  (** Widening the lower endpoint covers the old endpoint. *)
  Lemma widen_lower_old : forall q old next,
    bound_leb (widen_lower q old next) old = true.
  Proof.
    intros q old next. unfold widen_lower. destruct (bound_leb old next) eqn:Hle.
    - apply bound_leb_refl.
    - eapply bound_leb_trans with (b := next).
      + pose proof (widen_lower_next q old next) as Hnext.
        unfold widen_lower in Hnext. now rewrite Hle in Hnext.
      + destruct (bound_leb_total old next) as [Hnext|Hnext]; congruence.
  Qed.

  (** Widening the upper endpoint covers the next endpoint. *)
  Lemma widen_upper_next : forall q old next,
    bound_leb next (widen_upper q old next) = true.
  Proof.
    intros q old next. unfold widen_upper. destruct (bound_leb next old) eqn:Hle.
    - exact Hle.
    - destruct next as [|z|]; cbn; try reflexivity.
      destruct (T.above q z) as [u|] eqn:Habove; [|reflexivity].
      cbn. apply Z.leb_le. exact (proj2 (T.above_sound q z u Habove)).
  Qed.

  (** Widening the upper endpoint covers the old endpoint. *)
  Lemma widen_upper_old : forall q old next,
    bound_leb old (widen_upper q old next) = true.
  Proof.
    intros q old next. unfold widen_upper. destruct (bound_leb next old) eqn:Hle.
    - apply bound_leb_refl.
    - eapply bound_leb_trans with (b := next).
      + destruct (bound_leb_total next old) as [Hnext|Hnext]; congruence.
      + pose proof (widen_upper_next q old next) as Hnext.
        unfold widen_upper in Hnext. now rewrite Hle in Hnext.
  Qed.

  (** Stable scalar widening contains its previous interval. *)
  Lemma interval_stable_widen_upper_l : forall q a b,
    interval_leb a (interval_stable_widen q a b) = true.
  Proof.
    intros q a b. unfold interval_stable_widen. destruct (interval_leb b a).
    - apply interval_leb_refl.
    - destruct a as [|la ha], b as [|lb hb]; cbn; try reflexivity;
        try (now rewrite !bound_leb_refl).
      apply andb_true_iff. split; [apply widen_lower_old|apply widen_upper_old].
  Qed.

  (** Stable scalar widening contains its candidate interval. *)
  Lemma interval_stable_widen_upper_r : forall q a b,
    interval_leb b (interval_stable_widen q a b) = true.
  Proof.
    intros q a b. unfold interval_stable_widen. destruct (interval_leb b a) eqn:Hle.
    - exact Hle.
    - destruct a as [|la ha], b as [|lb hb]; cbn; try reflexivity;
        try (now rewrite !bound_leb_refl).
      apply andb_true_iff. split; [apply widen_lower_next|apply widen_upper_next].
  Qed.

  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a); unfold pleb.
    - apply interval_leb_refl.
    - rewrite interval_clip_idem. rewrite <- (interval_clip_idem w a) at 1.
      apply interval_clip_mono. apply interval_stable_widen_upper_l.
  Qed.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a) eqn:Hle; [exact Hle|].
    unfold pleb. rewrite interval_clip_idem. rewrite <- (interval_clip_idem w b) at 1.
    apply interval_clip_mono. apply interval_stable_widen_upper_r.
  Qed.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof.
    intros q w a b Hle. unfold pwiden. now rewrite Hle.
  Qed.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: interval_widening_rank_on: The variable interval_rank was not found in the current environment. *)
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: interval_widening_rank_on: No product even after head-reduction. *)
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof.
    intros w a b Hle.
    assert (Hnarrow : pnarrow w a b = interval_clip w a).
    { unfold pnarrow. destruct (interval_clip_shape w a) as
        [Hbot|[lo [hi [Hshape Hrange]]]].
      - now rewrite Hbot.
      - rewrite Hshape. destruct (interval_clip w b); reflexivity. }
    unfold pleb in *. rewrite Hnarrow, interval_clip_idem.
    split; [exact Hle|apply interval_leb_refl].
  Qed.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof.
    intros w a. unfold pleb. destruct (interval_clip w a) as [|l h]; cbn; [reflexivity|].
    now rewrite !bound_leb_refl.
  Qed.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w a b c. unfold pleb.
    destruct (interval_clip w a) as [|la ha];
      destruct (interval_clip w b) as [|lb hb];
      destruct (interval_clip w c) as [|lc hc]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc. apply andb_true_iff in Hab as [Hlb Hhb].
    apply andb_true_iff in Hbc as [Hlc Hhc]. apply andb_true_iff. split;
      eapply bound_leb_trans; eassumption.
  Qed.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof.
    intro w. intros [|l h]; reflexivity.
  Qed.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof.
    intros w a. unfold pleb, ptop, interval_top.
    rewrite interval_clip_fixed by (pose proof (Word.modulus_pos w); lia).
    apply interval_meet_lower_r.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof.
    intro w. reflexivity.
  Qed.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof.
    intros w a b. unfold pis_bot, pleb.
    destruct (interval_clip w a); cbn; [reflexivity|discriminate].
  Qed.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof.
    intros w a b. unfold pleb, pjoin.
    rewrite <- (interval_clip_idem w a) at 1. apply interval_clip_mono.
    destruct (interval_clip w a) as [|la ha], (interval_clip w b) as [|lb hb];
      cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_l|apply bound_max_upper_l].
  Qed.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof.
    intros w a b. unfold pleb, pjoin.
    rewrite <- (interval_clip_idem w b) at 1. apply interval_clip_mono.
    destruct (interval_clip w a) as [|la ha], (interval_clip w b) as [|lb hb];
      cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_r|apply bound_max_upper_r].
  Qed.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.
    intros w a b. unfold pleb, pmeet.
    eapply interval_leb_trans; [apply interval_meet_lower_l|apply interval_meet_lower_l].
  Qed.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof.
    intros w a b. unfold pleb, pmeet.
    eapply interval_leb_trans; [apply interval_meet_lower_l|apply interval_meet_lower_r].
  Qed.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w a b z Hle Ha. apply pgamma_unclip.
    eapply pgamma_raw_mono; [exact Hle|now apply pgamma_clip].
  Qed.
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof.
    intros w z [_ Hempty]. exact Hempty.
  Qed.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof.
    intros w z Hword. split; [exact Hword|].
    unfold ptop, interval_top, in_bnd.
    destruct Hword as [Hlower Hupper]. split; lia.
  Qed.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    intros w a b z Ha Hb. apply pgamma_raw_meet; now apply pgamma_clip.
  Qed.
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w a z Hbot Ha. apply pgamma_clip in Ha.
    unfold pis_bot in Hbot. destruct (interval_clip w a); [exact (proj2 Ha)|discriminate].
  Qed.
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof.
    intros w a b. unfold pleb, pis_bot.
    destruct (interval_clip w a), (interval_clip w b); cbn;
      try discriminate; reflexivity.
  Qed.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros w z. split; [apply L.wrap_is_word|].
    unfold pconst, in_bnd. split; reflexivity.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof.
    intros w a z v Hpoint _ Ha. apply pgamma_clip in Ha.
    unfold ppoint, Scalar.interval_singleton, Scalar.interval_finite in Hpoint.
    destruct (interval_clip w a) as [|[|lo|] [|hi|]];
      cbn [interval_finite_helper] in Hpoint; try discriminate.
    destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
    injection Hpoint as Hv. subst v. apply Z.eqb_eq in Heq.
    destruct Ha as [_ [Hlo Hhi]]. cbn in Hlo, Hhi. lia.
  Qed.

  (** Payload inclusion reads both operands through the word range. *)
  Lemma F_pleb : forall w a b, pleb w a b = Scalar.interval_leb
    (interval_payload_clip Scalar.interval_meet w a)
    (interval_payload_clip Scalar.interval_meet w b).
  Proof.
    reflexivity.
  Qed.
  (** Payload bottom recognition reads the clipped interval. *)
  Lemma F_pis_bot : forall w a, pis_bot w a =
    Scalar.interval_is_bot (interval_payload_clip Scalar.interval_meet w a).
  Proof.
    reflexivity.
  Qed.
  (** Payload join combines clipped operands. *)
  Lemma F_pjoin : forall w a b, pjoin w a b = Scalar.interval_join
    (interval_payload_clip Scalar.interval_meet w a)
    (interval_payload_clip Scalar.interval_meet w b).
  Proof.
    reflexivity.
  Qed.
  (** Payload meet combines clipped operands. *)
  Lemma F_pmeet : forall w a b, pmeet w a b = Scalar.interval_meet
    (interval_payload_clip Scalar.interval_meet w a)
    (interval_payload_clip Scalar.interval_meet w b).
  Proof.
    reflexivity.
  Qed.
  (** Payload widening retains stable raw values and clips unstable results. *)
  Lemma F_pwiden : forall q w a b, pwiden q w a b =
    if pleb w b a then a else interval_payload_clip Scalar.interval_meet w
      (Scalar.interval_stable_widen q (interval_payload_clip Scalar.interval_meet w a)
        (interval_payload_clip Scalar.interval_meet w b)).
  Proof.
    reflexivity.
  Qed.
  (** Payload narrowing combines clipped operands. *)
  Lemma F_pnarrow : forall w a b, pnarrow w a b = Scalar.interval_narrow
    (interval_payload_clip Scalar.interval_meet w a)
    (interval_payload_clip Scalar.interval_meet w b).
  Proof.
    reflexivity.
  Qed.
  (** Payload rank treats unsigned word boundaries as terminal endpoints. *)
  Lemma F_pwrank : forall q w a, pwrank q w a = payload_wrank q w a.
  Proof.
    reflexivity.
  Qed.
  (** Payload bottom is the empty interval. *)
  Lemma F_pbot : forall w, pbot w = IBot.
  Proof.
    reflexivity.
  Qed.
  (** Payload top is the inclusive unsigned word range. *)
  Lemma F_ptop : forall w, ptop w = I (Fin 0) (Fin (Word.modulus w - 1)).
  Proof.
    reflexivity.
  Qed.
  (** Payload constants are wrapped singleton intervals. *)
  Lemma F_pconst : forall w z, pconst w z = I (Fin (L.wrap w z)) (Fin (L.wrap w z)).
  Proof.
    reflexivity.
  Qed.
  (** Payload points are recognized after clipping. *)
  Lemma F_ppoint : forall w a, ppoint w a =
    Scalar.interval_singleton (interval_payload_clip Scalar.interval_meet w a).
  Proof.
    reflexivity.
  Qed.
  (** Payload concretization intersects raw endpoints with normalized words. *)
  Lemma F_pgamma : forall w a z, pgamma w a z <-> L.is_word w z /\
    match a with IBot => False | I lo hi => in_bnd lo hi z end.
  Proof.
    reflexivity.
  Qed.
End IntervalPayload.

Module IntervalPayloadT (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (Scalar : INTERVAL_SCALAR_T T) <: INTERVAL_PAYLOAD_ALL L T Scalar.
  Include IntervalPayload L T Scalar.

  TimeFun interval_top.
  TimeFun interval_clip.
  TimeFun pleb.
  TimeFun pjoin.
  TimeFun pmeet.
  TimeFun pbot.
  TimeFun ptop.
  TimeFun pis_bot.
  TimeFun pconst.
  TimeFun ppoint.
  TimeFun pwiden.
  TimeFun pnarrow.

  Definition psize (w : positive) (a : p) : nat := Pos.to_nat w + interval_bits a + 1.
  Definition pwsize (q : pwparam) : nat := (T.depth q + 1) * (T.tree_bits q + 1).
  Definition c_payload : N := 1%N. (* STUB *)
  Definition k_payload_clip : N := 1%N. (* STUB *)

  (** Joined payloads fit within the combined operand sizes. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Met payloads fit within the combined operand sizes. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widened payloads fit within the operand and parameter sizes. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Narrowed payloads fit within the combined operand sizes. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload widening charges both operands and its parameters. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload narrowing charges both raw payload sizes. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload inclusion charges both raw payload sizes. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload join charges both raw payload sizes. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload meet charges both raw payload sizes. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload bottom recognition charges the raw endpoint bits and width. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload point recognition charges the raw endpoint bits and width. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Constant abstraction charges the width and raw literal bits. *)
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <= c_payload *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** Payload size charges its width and the raw endpoint bits. *)
  Lemma F_psize : forall w a, psize w a = Pos.to_nat w + interval_bits a + 1.
  Proof. Admitted. (* STUB *)
  (** Widening parameter size charges a threshold search path. *)
  Lemma F_pwsize : forall q, pwsize q = (T.depth q + 1) * (T.tree_bits q + 1).
  Proof. Admitted. (* STUB *)
  (** Payload rank never exceeds the scalar threshold envelope. *)
  Lemma F_pwrank_le : forall q w a, pwrank q w a <= 2 * (length (T.vals q) + 1).
  Proof. Admitted. (* STUB *)
  (** Constructing the unsigned modulus charges the resulting word width. *)
  Lemma T_modulus_le : forall w,
    (Word.T_modulus w <= k_payload_clip * N.of_nat (Pos.to_nat w + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Concrete wrapping charges the width and raw literal bits. *)
  Lemma T_wrap_le : forall w z,
    (Word.T_wrap w z <= k_payload_clip *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** Clipping pays for the word bound and the raw endpoint bits. *)
  Lemma T_clip_le : forall w a,
    (T_interval_payload_clip Scalar.interval_meet Scalar.T_interval_meet w a <=
      k_payload_clip * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
End IntervalPayloadT.

Module IntervalWordTable (L : WORD_LANGUAGE) (T : THRESHOLDS) (Scalar : INTERVAL_SCALAR_OPS T)
    (W : INTERVAL_PAYLOAD_PINNED L T Scalar)
    <: INTERVAL_WORD_TABLE L W.
  Include IntervalWordTableCode L T Scalar W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* CONVERT: interval_table_laws: Unexpected name (no introduction patterns were expected in the *)
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted. (* CONVERT: interval_table_laws: Unexpected name (no introduction patterns were expected in the *)
End IntervalWordTable.

Module IntervalWordTableT (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (Scalar : INTERVAL_SCALAR_T T)
    (W : INTERVAL_PAYLOAD_PINNED_T L T Scalar)
    <: INTERVAL_WORD_TABLE_T L W.
  Include IntervalWordTable L T Scalar W.
  TimeFun interval_top.
  TimeFun interval_const.
  TimeFun interval_clip.
  TimeFun interval_checked.
  TimeFun interval_add.
  TimeFun interval_add_modular.
  TimeFun interval_sub.
  TimeFun interval_mul.
  TimeFun interval_neg.
  TimeFun interval_concat.
  TimeFun interval_rewrap.
  TimeFun interval_counts.
  TimeFun interval_udiv.
  TimeFun interval_urem.
  TimeFun interval_not.
  TimeFun interval_and.
  TimeFun interval_mask.
  TimeFun interval_or_xor.
  TimeFun interval_truth.
  TimeFun interval_bool_not.
  TimeFun interval_ult.
  TimeFun interval_ule.
  TimeFun interval_eq.
  TimeFun interval_shl.
  TimeFun interval_lshr.
  TimeFun interval_sign.
  TimeFun interval_signed.
  TimeFun interval_sext.
  TimeFun interval_signed_compare.
  TimeFun interval_sdiv.
  TimeFun interval_srem.
  TimeFun interval_mod_choice.
  TimeFun interval_smod_base.
  TimeFun interval_smod.
  TimeFun interval_ashr_small.
  TimeFun interval_ashr.
  TimeFun interval_swap.
  TimeFun interval_assume_equal.
  TimeFun interval_assume_ult.
  TimeFun interval_assume_ule.
  TimeFun interval_assume_add.
  TimeFun interval_assume_sub.
  TimeFun interval_assume_rewrap.
  TimeFun interval_exclude.
  TimeFun interval_assume_neq.
  TimeFun interval_assume_signed.
  TimeFun interval_is_point.
  TimeFun interval_assume_pair.
  TimeFun interval_bwd1.
  TimeFun interval_bwd2.
  TimeFun wfwd.
  TimeFun wbwd.

  Definition c_word_table : N := 1%N. (* STUB *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (W.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
End IntervalWordTableT.
