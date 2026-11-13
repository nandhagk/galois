(** * Interval backward operations

    Result assumptions refine comparisons and nonwrapping arithmetic.
    For example, equality to one refines both operands of an equality test.
    Builds on: IntervalOps and fixed-width word operators. *)

From Stdlib Require Import ZArith Zpow_facts NArith List Bool Lia.
From Argent Require Import Time Tactics Std.
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

  (** Moving an endpoint right can only increase the number of smaller thresholds. *)
  Lemma count_lt_mono : forall q x y, (x <= y)%Z -> count_lt q x <= count_lt q y.
  Proof.
    intros q x y Hxy. unfold count_lt.
    induction (T.vals q) as [|u us IH]; cbn; [lia|].
    destruct (Z.ltb u x) eqn:Hux, (Z.ltb u y) eqn:Huy; cbn; lia.
  Qed.

  (** Moving an endpoint right can only decrease the number of larger thresholds. *)
  Lemma count_gt_mono : forall q x y, (x <= y)%Z -> count_gt q y <= count_gt q x.
  Proof.
    intros q x y Hxy. unfold count_gt.
    induction (T.vals q) as [|u us IH]; cbn; [lia|].
    destruct (Z.ltb y u) eqn:Hyu, (Z.ltb x u) eqn:Hxu; cbn; lia.
  Qed.

  (** Moving left to a stored threshold strictly consumes a lower-endpoint credit. *)
  Lemma count_lt_strict : forall q x y, In x (T.vals q) -> (x < y)%Z ->
    count_lt q x < count_lt q y.
  Proof.
    intros q x y Hin Hxy. unfold count_lt in *.
    induction (T.vals q) as [|u us IH]; cbn in *; [contradiction|].
    destruct Hin as [Heq|Hin].
    - subst u. rewrite Z.ltb_irrefl.
      rewrite (proj2 (Z.ltb_lt x y)) by exact Hxy. cbn.
      assert (Hmono : length (filter (fun z => (z <? x)%Z) us) <=
        length (filter (fun z => (z <? y)%Z) us)).
      { clear IH. induction us as [|z zs IHus]; cbn; [lia|].
        destruct (Z.ltb z x) eqn:Hzx, (Z.ltb z y) eqn:Hzy; cbn; lia. }
      lia.
    - specialize (IH Hin). destruct (Z.ltb u x) eqn:Hux, (Z.ltb u y) eqn:Huy;
        cbn in *; lia.
  Qed.

  (** Moving right to a stored threshold strictly consumes an upper-endpoint credit. *)
  Lemma count_gt_strict : forall q x y, In y (T.vals q) -> (x < y)%Z ->
    count_gt q y < count_gt q x.
  Proof.
    intros q x y Hin Hxy. unfold count_gt in *.
    induction (T.vals q) as [|u us IH]; cbn in *; [contradiction|].
    destruct Hin as [Heq|Hin].
    - subst u. rewrite Z.ltb_irrefl.
      rewrite (proj2 (Z.ltb_lt x y)) by exact Hxy. cbn.
      assert (Hmono : length (filter (fun z => (y <? z)%Z) us) <=
        length (filter (fun z => (x <? z)%Z) us)).
      { clear IH. induction us as [|z zs IHus]; cbn; [lia|].
        destruct (Z.ltb y z) eqn:Hyz, (Z.ltb x z) eqn:Hxz; cbn; lia. }
      lia.
    - specialize (IH Hin). destruct (Z.ltb y u) eqn:Hyu, (Z.ltb x u) eqn:Hxu;
        cbn in *; lia.
  Qed.

  (** Zero is the terminal lower endpoint of an unsigned payload. *)
  Definition lower_payload_rank (q : ttree) (lo : bnd) : nat :=
    match lo with
    | Fin z => if (z =? 0)%Z then 0 else 1 + count_lt q z
    | _ => 0
    end.

  (** The unsigned maximum is the terminal upper endpoint of a payload. *)
  Definition upper_payload_rank (q : ttree) (cap : Z) (hi : bnd) : nat :=
    match hi with
    | Fin z => if (z =? cap)%Z then 0 else 1 + count_gt q z
    | _ => 0
    end.

  (** Lower widening consumes a credit when it moves, including clipping to zero. *)
  Lemma lower_payload_progress : forall q old next, (0 <= old)%Z -> (0 <= next)%Z ->
    let lo := bound_max (widen_lower q (Fin old) (Fin next)) (Fin 0) in
    lower_payload_rank q lo <= lower_payload_rank q (Fin old) /\
    ((next < old)%Z -> lower_payload_rank q lo < lower_payload_rank q (Fin old)).
  Proof.
    intros q old next Hold Hnext. cbn beta zeta.
    unfold widen_lower. cbn [bound_leb]. destruct (Z.leb old next) eqn:Hmove.
    - rewrite bound_max_left by (cbn; apply Z.leb_le; exact Hold).
      apply Z.leb_le in Hmove. split; lia.
    - apply Z.leb_gt in Hmove.
      assert (Hold0 : (old =? 0)%Z = false) by (apply Z.eqb_neq; lia).
      destruct (T.below q next) as [u|] eqn:Hbelow.
      + destruct (T.below_sound q next u Hbelow) as [Hin Hu].
        unfold bound_max. cbn [bound_leb]. destruct (Z.leb u 0) eqn:Hu0.
        * cbn [lower_payload_rank]. rewrite Hold0, Z.eqb_refl. split; lia.
        * cbn [lower_payload_rank]. rewrite Hold0.
          destruct (Z.eqb u 0); [split; lia|].
          pose proof (count_lt_strict q u old Hin ltac:(lia)) as Hstrict. split; lia.
      + cbn [bound_max bound_leb lower_payload_rank]. rewrite Hold0, Z.eqb_refl.
        split; lia.
  Qed.

  (** Upper widening consumes a credit when it moves, including clipping to the maximum. *)
  Lemma upper_payload_progress : forall q cap old next, (old <= cap)%Z -> (next <= cap)%Z ->
    let hi := bound_min (widen_upper q (Fin old) (Fin next)) (Fin cap) in
    upper_payload_rank q cap hi <= upper_payload_rank q cap (Fin old) /\
    ((old < next)%Z -> upper_payload_rank q cap hi < upper_payload_rank q cap (Fin old)).
  Proof.
    intros q cap old next Hold Hnext. cbn beta zeta.
    unfold widen_upper. cbn [bound_leb]. destruct (Z.leb next old) eqn:Hmove.
    - unfold bound_min. cbn [bound_leb].
      rewrite (proj2 (Z.leb_le old cap)) by exact Hold.
      apply Z.leb_le in Hmove. split; lia.
    - apply Z.leb_gt in Hmove.
      assert (Holdcap : (old =? cap)%Z = false) by (apply Z.eqb_neq; lia).
      destruct (T.above q next) as [u|] eqn:Habove.
      + destruct (T.above_sound q next u Habove) as [Hin Hu].
        unfold bound_min. cbn [bound_leb]. destruct (Z.leb u cap) eqn:Hucap.
        * cbn [upper_payload_rank]. rewrite Holdcap.
          destruct (Z.eqb u cap); [split; lia|].
          pose proof (count_gt_strict q old u Hin ltac:(lia)) as Hstrict. split; lia.
        * cbn [upper_payload_rank]. rewrite Holdcap, Z.eqb_refl. split; lia.
      + cbn [bound_min bound_leb upper_payload_rank]. rewrite Holdcap, Z.eqb_refl.
        split; lia.
  Qed.

  (** Widening a nonempty word interval remains nonempty after clipping. *)
  Lemma clip_widen_eq : forall q w lo hi lo' hi',
    (0 <= lo /\ lo <= hi /\ hi < Word.modulus w)%Z ->
    interval_clip w (interval_widen q (I (Fin lo) (Fin hi)) (I lo' hi')) =
      I (bound_max (widen_lower q (Fin lo) lo') (Fin 0))
        (bound_min (widen_upper q (Fin hi) hi') (Fin (Word.modulus w - 1))).
  Proof.
    intros q w lo hi lo' hi' Hrange.
    assert (Hlo : bound_leb
      (bound_max (widen_lower q (Fin lo) lo') (Fin 0)) (Fin lo) = true).
    { apply bound_max_least; [apply widen_lower_old|cbn; apply Z.leb_le; lia]. }
    assert (Hhi : bound_leb (Fin hi)
      (bound_min (widen_upper q (Fin hi) hi') (Fin (Word.modulus w - 1))) = true).
    { apply bound_min_greatest; [apply widen_upper_old|cbn [bound_leb]; apply Z.leb_le; lia]. }
    assert (Hordered : bound_leb
      (bound_max (widen_lower q (Fin lo) lo') (Fin 0))
      (bound_min (widen_upper q (Fin hi) hi') (Fin (Word.modulus w - 1))) = true).
    { eapply bound_leb_trans; [exact Hlo|].
      eapply bound_leb_trans; [|exact Hhi]. cbn. apply Z.leb_le. lia. }
    assert (Hnonempty : bounds_nonempty
      (bound_max (widen_lower q (Fin lo) lo') (Fin 0))
      (bound_min (widen_upper q (Fin hi) hi') (Fin (Word.modulus w - 1))) = true).
    { destruct (bound_max (widen_lower q (Fin lo) lo') (Fin 0)),
        (bound_min (widen_upper q (Fin hi) hi') (Fin (Word.modulus w - 1)));
        cbn [bound_leb bounds_nonempty] in *; try discriminate; assumption. }
    unfold interval_clip, interval_payload_clip, Scalar.interval_widen, Scalar.interval_meet.
    now rewrite Hnonempty.
  Qed.

  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w a b Hbot Hle.
    destruct (interval_clip_shape w a) as [Ha|[la [ha [Ha Harange]]]].
    { unfold pis_bot in Hbot. rewrite Ha in Hbot. discriminate. }
    destruct (interval_clip_shape w b) as [Hb|[lb [hb [Hb Hbrange]]]].
    { unfold pleb in Hle. rewrite Hb in Hle. discriminate. }
    assert (Hraw : interval_leb (I (Fin lb) (Fin hb)) (I (Fin la) (Fin ha)) = false).
    { unfold pleb in Hle. now rewrite Ha, Hb in Hle. }
    unfold pwiden. rewrite Hle. unfold pwrank, payload_wrank.
    change ((match interval_clip w (interval_clip w
      (interval_stable_widen q (interval_clip w a) (interval_clip w b))) with
      | IBot => 0
      | I lo hi => upper_payload_rank q (Word.modulus w - 1) hi + lower_payload_rank q lo
      end) <
      (match interval_clip w a with
      | IBot => 0
      | I lo hi => upper_payload_rank q (Word.modulus w - 1) hi + lower_payload_rank q lo
      end))%nat.
    rewrite interval_clip_idem, Ha, Hb.
    unfold interval_stable_widen. rewrite Hraw. rewrite clip_widen_eq by exact Harange.
    cbn beta iota.
    destruct (lower_payload_progress q la lb ltac:(lia) ltac:(lia)) as [Hlower Hlower_strict].
    destruct (upper_payload_progress q (Word.modulus w - 1) ha hb ltac:(lia) ltac:(lia))
      as [Hupper Hupper_strict].
    change (andb (Z.leb la lb) (Z.leb hb ha) = false) in Hraw.
    apply andb_false_iff in Hraw as [Hmove|Hmove]; apply Z.leb_gt in Hmove.
    - specialize (Hlower_strict Hmove). lia.
    - specialize (Hupper_strict Hmove). lia.
  Qed.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof.
    intros q w a b Hbot. destruct (pleb w b a) eqn:Hle.
    - rewrite pwiden_stable by exact Hle. reflexivity.
    - apply Nat.lt_le_incl. now apply pwrank_widen.
  Qed.
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
  Definition k_payload_clip : N := (64 * (Scalar.c_scalar + 1))%N.
  Definition c_payload : N := (32 * (k_payload_clip + Scalar.c_scalar + 1))%N.

  (** A nonnegative integer below a power of two fits within that exponent. *)
  Lemma payload_bits_below_pow : forall z k,
    (0 <= z < 2 ^ Z.of_nat k)%Z -> Z.size_nat z <= k.
  Proof.
    intros [|z|z] k Hrange; cbn [Z.size_nat]; try lia.
    now apply Zpower2_Psize.
  Qed.

  (** Normalized word values use at most their declared number of bits. *)
  Lemma payload_word_bits : forall w z, Word.is_word w z ->
    Z.size_nat z <= Pos.to_nat w.
  Proof.
    intros w z Hword. apply payload_bits_below_pow.
    rewrite positive_nat_Z. exact Hword.
  Qed.

  (** The word modulus requires one extra bit beyond the width. *)
  Lemma payload_modulus_bits : forall w,
    Z.size_nat (Word.modulus w) <= Pos.to_nat w + 1.
  Proof.
    intro w. apply payload_bits_below_pow. split.
    - pose proof (Word.modulus_pos w); lia.
    - rewrite Word.modulus_value, Nat2Z.inj_add, positive_nat_Z.
      apply Z.pow_lt_mono_r; lia.
  Qed.

  (** The largest unsigned value stays within the word width. *)
  Lemma payload_cap_bits : forall w,
    Z.size_nat (Word.modulus w - 1) <= Pos.to_nat w.
  Proof.
    intro w. apply payload_word_bits. unfold Word.is_word.
    pose proof (Word.modulus_pos w); lia.
  Qed.

  (** The unsigned top interval stores only a width-sized upper endpoint. *)
  Lemma payload_top_bits : forall w, interval_bits (interval_top w) <= Pos.to_nat w.
  Proof.
    intro w. unfold interval_top, interval_bits. cbn [Z.size_nat].
    apply payload_cap_bits.
  Qed.

  (** Clipping removes infinities and bounds both finite endpoints by the width. *)
  Lemma payload_clip_bits : forall w a, interval_bits (interval_clip w a) <= Pos.to_nat w.
  Proof.
    intros w a. destruct (interval_clip_shape w a) as [Hbot|[lo [hi [Hshape Hrange]]]].
    - rewrite Hbot. cbn [interval_bits]; lia.
    - rewrite Hshape. cbn [interval_bits]. apply Nat.max_lub; apply payload_word_bits;
        unfold Word.is_word; lia.
  Qed.

  (** Joining chooses one endpoint from each side of its operands. *)
  Lemma payload_raw_join_bits : forall a b,
    interval_bits (Scalar.interval_join a b) <= interval_bits a + interval_bits b.
  Proof.
    intros [|lo hi] [|lo' hi']; cbn [Scalar.interval_join interval_bits]; try lia.
    unfold Scalar.bound_min, Scalar.bound_max.
    destruct (Scalar.bound_leb lo lo'), (Scalar.bound_leb hi hi');
      cbn [interval_bits]; lia.
  Qed.

  (** Intersecting selects existing endpoints or returns bottom. *)
  Lemma payload_raw_meet_bits : forall a b,
    interval_bits (Scalar.interval_meet a b) <= interval_bits a + interval_bits b.
  Proof.
    intros [|lo hi] [|lo' hi']; cbn [Scalar.interval_meet interval_bits]; try lia.
    destruct (Scalar.bounds_nonempty (Scalar.bound_max lo lo') (Scalar.bound_min hi hi'));
      cbn [interval_bits]; try lia.
    unfold Scalar.bound_min, Scalar.bound_max.
    destruct (Scalar.bound_leb lo lo'), (Scalar.bound_leb hi hi'); lia.
  Qed.

  (** Narrowing chooses its endpoints from the two operands. *)
  Lemma payload_raw_narrow_bits : forall a b,
    interval_bits (Scalar.interval_narrow a b) <= interval_bits a + interval_bits b.
  Proof.
    intros [|lo hi] [|lo' hi']; cbn [Scalar.interval_narrow interval_bits]; try lia.
    destruct lo, hi; cbn [Scalar.narrow_bound interval_bits]; lia.
  Qed.

  (** Repeated multiplication by two costs a constant per output bit. *)
  Lemma payload_modulus_time : forall w,
    (Word.T_modulus w <= 5 * N.of_nat (Pos.to_nat w) + 3)%N.
  Proof.
    intro w. pose proof (Std.Pos.T_iter_le (Z.mul 2)
      (fun x => Std.Z.T_mul 2 x) (fun _ => True) 3 1%Z w
      ltac:(easy) ltac:(intros; apply Std.Z.T_mul_two_le) ltac:(constructor)) as Hiter.
    unfold Word.T_modulus, Word.Z.T_pow, Word.Z.T_pow_pos. cbn beta iota zeta.
    rewrite <- (N2Nat.id (N.pos w)) in Hiter. change (N.to_nat (N.pos w)) with (Pos.to_nat w)
      in Hiter. lia.
  Qed.

  (** Concrete wrapping charges the width and raw literal bits. *)
  Lemma payload_wrap_time : forall w z,
    (Word.T_wrap w z <= k_payload_clip *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (payload_modulus_time w).
    pose proof (payload_modulus_bits w). pose proof (Pos2Nat.is_pos w).
    pose proof (Std.Z.T_modulo_le z (Word.modulus w)).
    unfold Word.T_wrap, k_payload_clip.
    rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.

  (** Clipping pays for the word bound and the raw endpoint bits. *)
  Lemma payload_shared_clip_time : forall w a,
    (T_interval_payload_clip Scalar.interval_meet Scalar.T_interval_meet w a <=
      k_payload_clip * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. pose proof (payload_modulus_time w).
    pose proof (payload_modulus_bits w). pose proof (payload_top_bits w).
    pose proof (Std.Z.T_sub_le (Word.modulus w) 1) as Hsub.
    change (Std.Z.T_sub (Word.modulus w) 1 <=
      3 * N.of_nat (Z.size_nat (Word.modulus w) + 1) + 3)%N in Hsub.
    pose proof (Scalar.T_interval_meet_le a (interval_top w)).
    unfold T_interval_payload_clip. fold (interval_top w).
    unfold psize, k_payload_clip. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** The local clipping wrapper adds one call to the shared clipping cost. *)
  Lemma payload_clip_time : forall w a,
    (T_interval_clip w a <= (k_payload_clip + 1) * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. pose proof (payload_shared_clip_time w a).
    change (1 + T_interval_payload_clip Scalar.interval_meet Scalar.T_interval_meet w a <=
      (k_payload_clip + 1) * N.of_nat (psize w a + 1))%N.
    unfold psize in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Inclusion pays for two clips and one scalar comparison. *)
  Lemma payload_leb_time : forall w a b,
    (T_pleb w a b <= 4 * (k_payload_clip + Scalar.c_scalar + 1) *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_time w a). pose proof (payload_clip_time w b).
    pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
    pose proof (Scalar.T_interval_leb_le (interval_clip w a) (interval_clip w b)).
    unfold T_pleb, psize in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** A larger coefficient and size budget preserve an established time bound. *)
  Lemma payload_time_weaken : forall (cost c d : N) (n m : nat),
    (cost <= c * N.of_nat n)%N -> (c <= d)%N -> n <= m ->
    (cost <= d * N.of_nat m)%N.
  Proof.
    intros cost c d n m Hcost Hcoeff Hsize. eapply N.le_trans; [exact Hcost|].
    apply N.mul_le_mono; [exact Hcoeff|lia].
  Qed.



  (** Joined payloads fit within the combined operand sizes. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
    pose proof (payload_raw_join_bits (interval_clip w a) (interval_clip w b)).
    unfold pjoin, psize, c_payload, k_payload_clip. rewrite !Nat2N.inj_add. nia.
  Qed.
  (** Met payloads fit within the combined operand sizes. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
    pose proof (payload_raw_meet_bits (interval_clip w a) (interval_clip w b)).
    unfold pmeet, psize, c_payload, k_payload_clip. rewrite !Nat2N.inj_add. nia.
  Qed.
  (** Widened payloads fit within the operand and parameter sizes. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a).
    - unfold psize, c_payload, k_payload_clip. rewrite !Nat2N.inj_add. nia.
    - pose proof (payload_clip_bits w
        (Scalar.interval_stable_widen q (interval_clip w a) (interval_clip w b))).
      unfold psize, c_payload, k_payload_clip. rewrite !Nat2N.inj_add. nia.
  Qed.
  (** Narrowed payloads fit within the combined operand sizes. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
    pose proof (payload_raw_narrow_bits (interval_clip w a) (interval_clip w b)).
    unfold pnarrow, psize, c_payload, k_payload_clip. rewrite !Nat2N.inj_add. nia.
  Qed.
  (** Payload widening charges both operands and its parameters. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b.
    set (budget := psize w a + psize w b + pwsize q + 1).
    set (k := (k_payload_clip + Scalar.c_scalar + 1)%N).
    assert (Hk : (1 <= k)%N) by (unfold k; lia).
    assert (Hbudget : (1 <= N.of_nat budget)%N) by (unfold budget; lia).
    assert (Hleb : (T_pleb w b a <= 4 * k * N.of_nat budget)%N).
    { eapply payload_time_weaken; [apply payload_leb_time|unfold k; lia|].
      unfold budget; lia. }
    assert (Hclipa : (T_interval_clip w a <= k * N.of_nat budget)%N).
    { eapply payload_time_weaken; [apply payload_clip_time|unfold k; lia|].
      unfold budget; lia. }
    assert (Hclipb : (T_interval_clip w b <= k * N.of_nat budget)%N).
    { eapply payload_time_weaken; [apply payload_clip_time|unfold k; lia|].
      unfold budget; lia. }
    assert (Hwiden :
      (Scalar.T_interval_stable_widen q (interval_clip w a) (interval_clip w b) <=
        k * N.of_nat budget)%N).
    { eapply payload_time_weaken;
        [apply Scalar.T_interval_stable_widen_le|unfold k; lia|].
      pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
      unfold budget, psize, pwsize. lia. }
    assert (Hresult :
      (T_interval_clip w
        (Scalar.interval_stable_widen q (interval_clip w a) (interval_clip w b)) <=
        k * N.of_nat (2 * budget))%N).
    { eapply payload_time_weaken; [apply payload_clip_time|unfold k; lia|].
      pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
      pose proof (Scalar.interval_stable_widen_bits q (interval_clip w a) (interval_clip w b)).
      assert (Htree : T.tree_bits q <= pwsize q) by (unfold pwsize; nia).
      unfold budget, psize. lia. }
    rewrite Nat2N.inj_mul in Hresult.
    unfold T_pwiden, c_payload. fold k budget.
    clearbody k budget.
    destruct (pleb w b a); nia.
  Qed.
  (** Payload narrowing charges both raw payload sizes. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_time w a). pose proof (payload_clip_time w b).
    pose proof (Scalar.T_interval_narrow_le (interval_clip w a) (interval_clip w b)).
    unfold T_pnarrow, psize, c_payload in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Payload inclusion charges both raw payload sizes. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_leb_time w a b). unfold c_payload. nia.
  Qed.
  (** Payload join charges both raw payload sizes. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_time w a). pose proof (payload_clip_time w b).
    pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
    pose proof (Scalar.T_interval_join_le (interval_clip w a) (interval_clip w b)).
    unfold T_pjoin, psize, c_payload in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Payload meet charges both raw payload sizes. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (payload_clip_time w a). pose proof (payload_clip_time w b).
    pose proof (payload_clip_bits w a). pose proof (payload_clip_bits w b).
    pose proof (Scalar.T_interval_meet_le (interval_clip w a) (interval_clip w b)).
    unfold T_pmeet, psize, c_payload in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Payload bottom recognition charges the raw endpoint bits and width. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. pose proof (payload_clip_time w a).
    pose proof (Scalar.T_interval_is_bot_le (interval_clip w a)).
    unfold T_pis_bot, psize, c_payload in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Payload point recognition charges the raw endpoint bits and width. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. pose proof (payload_clip_time w a). pose proof (payload_clip_bits w a).
    pose proof (Scalar.T_interval_singleton_le (interval_clip w a)).
    unfold T_ppoint, psize, c_payload in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Constant abstraction charges the width and raw literal bits. *)
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <= c_payload *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (payload_wrap_time w z).
    unfold T_pconst, c_payload. rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *.
    nia.
  Qed.
  (** Payload size charges its width and the raw endpoint bits. *)
  Lemma F_psize : forall w a, psize w a = Pos.to_nat w + interval_bits a + 1.
  Proof.
    reflexivity.
  Qed.
  (** Widening parameter size charges a threshold search path. *)
  Lemma F_pwsize : forall q, pwsize q = (T.depth q + 1) * (T.tree_bits q + 1).
  Proof.
    reflexivity.
  Qed.
  (** Payload rank never exceeds the scalar threshold envelope. *)
  Lemma F_pwrank_le : forall q w a, pwrank q w a <= 2 * (length (T.vals q) + 1).
  Proof.
    intros q w a. unfold pwrank, payload_wrank.
    destruct (interval_payload_clip Scalar.interval_meet w a) as [|lo hi]; [lia|].
    assert (Hgt : forall z, count_gt q z <= length (T.vals q)).
    { intro z. unfold count_gt. apply filter_length_le. }
    assert (Hlt : forall z, count_lt q z <= length (T.vals q)).
    { intro z. unfold count_lt. apply filter_length_le. }
    destruct lo as [|lo|], hi as [|hi|]; cbn beta iota zeta;
      try specialize (Hgt hi); try specialize (Hlt lo);
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
  Qed.
  (** Constructing the unsigned modulus charges the resulting word width. *)
  Lemma T_modulus_le : forall w,
    (Word.T_modulus w <= k_payload_clip * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intro w. pose proof (payload_modulus_time w).
    unfold k_payload_clip. rewrite Nat2N.inj_add. nia.
  Qed.
  (** Concrete wrapping charges the width and raw literal bits. *)
  Lemma T_wrap_le : forall w z,
    (Word.T_wrap w z <= k_payload_clip *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    exact payload_wrap_time.
  Qed.
  (** Clipping pays for the word bound and the raw endpoint bits. *)
  Lemma T_clip_le : forall w a,
    (T_interval_payload_clip Scalar.interval_meet Scalar.T_interval_meet w a <=
      k_payload_clip * N.of_nat (psize w a + 1))%N.
  Proof.
    exact payload_shared_clip_time.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. pose proof (payload_modulus_time w). pose proof (payload_modulus_bits w).
    pose proof (Std.Z.T_sub_le (Word.modulus w) 1) as Hsub.
    change (Std.Z.T_sub (Word.modulus w) 1 <=
      3 * N.of_nat (Z.size_nat (Word.modulus w) + 1) + 3)%N in Hsub.
    unfold T_ptop, T_interval_top, c_payload, k_payload_clip.
    rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold T_pbot, c_payload, k_payload_clip.
    rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. pose proof (payload_top_bits w). unfold ptop, psize, c_payload, k_payload_clip.
    rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold pbot, psize, interval_bits, c_payload, k_payload_clip.
    rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (payload_word_bits w (Word.wrap w z) (Word.wrap_is_word w z)).
    unfold pconst, psize, interval_bits, c_payload, k_payload_clip. rewrite Nat.max_id.
    rewrite Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add. nia.
  Qed.
End IntervalPayloadT.

Module IntervalWordTable (L : WORD_LANGUAGE) (T : THRESHOLDS) (Scalar : INTERVAL_SCALAR_OPS T)
    (W : INTERVAL_PAYLOAD_PINNED L T Scalar)
    <: INTERVAL_WORD_TABLE L W.
  Include IntervalWordTableCode L T Scalar W.
  Module Sound := IntervalOpsSound T Scalar.
  Local Abbreviation interval_pgamma := Sound.interval_pgamma.
  Local Open Scope Z_scope.

  (** The table's endpoint semantics agrees with the pinned payload meaning. *)
  Local Lemma interval_payload_spec w a z :
    W.pgamma w a z <-> interval_pgamma w a z.
  Proof.
    rewrite W.F_pgamma, Sound.interval_pgamma_spec. reflexivity.
  Qed.

  (** Each checked operand provides its width and its raw interval membership. *)
  Local Lemma interval_inputs_sound xs cs :
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    Forall2 (fun wp c => fst wp = fst c /\
      interval_pgamma (fst wp) (snd wp) (snd c)) xs cs.
  Proof.
    intros Hinputs. induction Hinputs as [|wp c xs cs [Hwidth [_ Ha]] Htail IH].
    - constructor.
    - constructor; [split; [exact Hwidth|now apply interval_payload_spec]|exact IH].
  Qed.

  (** A unary entry clips its operand before applying its scalar soundness law. *)
  Local Lemma interval_entry1_sound o (f : width -> width -> itv -> itv)
      (rw w : width) a cs z :
    Forall2 (fun wp c => fst wp = fst c /\
      interval_pgamma (fst wp) (snd wp) (snd c)) [(w, a)] cs ->
    eval_op o cs = Some (rw, z) ->
    (forall (w : width) a x, interval_pgamma w a x ->
      eval_op o [(w, x)] = Some (rw, z) ->
      interval_pgamma rw (f rw w a) z) ->
    interval_pgamma rw (f rw w (interval_clip w a)) z.
  Proof.
    intros Hinputs Heval Hscalar.
    inversion Hinputs as [|wp [v x] tail values [Hwidth Ha] Htail]; subst.
    inversion Htail; subst. change (w = v) in Hwidth. subst v.
    apply (Hscalar w (interval_clip w a) x); [now apply Sound.interval_clip_sound|].
    exact Heval.
  Qed.

  (** A binary entry clips both operands at their own checked widths. *)
  Local Lemma interval_entry2_sound o (f : width -> width -> width -> itv -> itv -> itv)
      (rw wa wb : width) a b cs z :
    Forall2 (fun wp c => fst wp = fst c /\
      interval_pgamma (fst wp) (snd wp) (snd c)) [(wa, a); (wb, b)] cs ->
    eval_op o cs = Some (rw, z) ->
    (forall (wa wb : width) a b x y, interval_pgamma wa a x -> interval_pgamma wb b y ->
      eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
      interval_pgamma rw (f rw wa wb a b) z) ->
    interval_pgamma rw (f rw wa wb (interval_clip wa a) (interval_clip wb b)) z.
  Proof.
    intros Hinputs Heval Hscalar.
    inversion Hinputs as [|wp [wx x] tail values [Hwa Ha] Htail]; subst.
    inversion Htail as [|wp [wy y] tail' values' [Hwb Hb] Hlast]; subst.
    inversion Hlast; subst.
    change (wa = wx) in Hwa. change (wb = wy) in Hwb. subst wx wy.
    apply (Hscalar wa wb (interval_clip wa a) (interval_clip wb b) x y);
      try now apply Sound.interval_clip_sound.
    exact Heval.
  Qed.

  (** A selected binary tag supplies its checked common width and concrete result. *)
  Local Lemma interval_binary_semantics o tag (f : width -> itv -> itv -> itv) :
    word_fun2 o = Some tag ->
    (forall (w : width) a b x y, interval_pgamma w a x -> interval_pgamma w b y ->
      interval_pgamma w (f w a b) (eval_binary_tag tag w x y)) ->
    forall (rw wa wb : width) a b x y z, interval_pgamma wa a x -> interval_pgamma wb b y ->
      eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
      interval_pgamma rw (f rw a b) z.
  Proof.
    intros Hkind Hscalar rw wa wb a b x y z Ha Hb Heval.
    pose proof (eval_op_fun2_width o tag wa wb x y (rw, z) Hkind Heval) as Hwidth.
    subst wb. rewrite (eval_op_fun2 o wa x y tag Hkind) in Heval.
    inversion Heval; subst. now apply Hscalar.
  Qed.

  (** A selected unary tag preserves the checked operand width. *)
  Local Lemma interval_unary_semantics o tag (f : width -> itv -> itv) :
    word_fun1 o = Some tag ->
    (forall (w : width) a x, interval_pgamma w a x ->
      interval_pgamma w (f w a) (eval_unary_tag tag w x)) ->
    forall (rw w : width) a x z, interval_pgamma w a x ->
      eval_op o [(w, x)] = Some (rw, z) -> interval_pgamma rw (f rw a) z.
  Proof.
    intros Hkind Hscalar rw w a x z Ha Heval.
    rewrite (eval_op_fun1 o w x tag Hkind) in Heval.
    inversion Heval; subst. now apply Hscalar.
  Qed.

  (** A selected comparison tag produces a one-bit Boolean at the common operand width. *)
  Local Lemma interval_comparison_semantics o tag (f : width -> itv -> itv -> itv) :
    word_cmp o = Some tag ->
    (forall (w : width) a b x y, interval_pgamma w a x -> interval_pgamma w b y ->
      interval_pgamma 1%positive (f w a b)
        (if eval_comparison_tag tag w x y then 1 else 0)) ->
    forall (rw wa wb : width) a b x y z, interval_pgamma wa a x -> interval_pgamma wb b y ->
      eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
      interval_pgamma rw (f wa a b) z.
  Proof.
    intros Hkind Hscalar rw wa wb a b x y z Ha Hb Heval.
    pose proof (eval_op_cmp_width o tag wa wb x y (rw, z) Hkind Heval) as Hwidth.
    subst wb. rewrite (eval_op_cmp o wa x y tag Hkind) in Heval.
    inversion Heval; subst. now apply Hscalar.
  Qed.

  (** The conditional entry contains either selected arm at their common checked width. *)
  Local Lemma interval_ite_entry_sound (rw wc wa wb : width) c a b cs z :
    Forall2 (fun wp v => fst wp = fst v /\
      interval_pgamma (fst wp) (snd wp) (snd v)) [(wc, c); (wa, a); (wb, b)] cs ->
    eval_op bvite cs = Some (rw, z) ->
    interval_pgamma rw (Scalar.interval_join (interval_clip wa a) (interval_clip wb b)) z.
  Proof.
    intros Hinputs Heval.
    inversion Hinputs as [|wp [vc t] tail values [Hwc Hc] Htail]; subst.
    inversion Htail as [|wp [va x] tail' values' [Hwa Ha] Hlast]; subst.
    inversion Hlast as [|wp [vb y] tail'' values'' [Hwb Hb] Hnil]; subst.
    inversion Hnil; subst.
    change (wc = vc) in Hwc. change (wa = va) in Hwa. change (wb = vb) in Hwb.
    subst vc va vb.
    destruct (eval_op_ite_width wc wa wb t x y (rw, z) Heval) as [Hcondition Harms].
    subst wc wb. rewrite eval_op_ite in Heval.
    rewrite (wrap_id wa x (proj1 Ha)), (wrap_id wa y (proj1 Hb)) in Heval.
    destruct (wrap 1%positive t =? 1) eqn:Hdecision; inversion Heval; subst rw z;
      apply Sound.interval_join_sound.
    - left. now apply Sound.interval_clip_sound.
    - right. now apply Sound.interval_clip_sound.
  Qed.

  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wps cs z r Hentry Hxs Heval.
    apply interval_payload_spec. apply interval_inputs_sound in Hxs.
    destruct wps as [|[wA aA] [|[wB aB] [|[wC aC] [|extra rest]]]];
      destruct o; cbn [wfwd] in Hentry; try discriminate; inversion Hentry; subst r.
    - eapply interval_entry1_sound with (f := fun rw _ => interval_not rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr.
      eapply (interval_unary_semantics bvnot UNot (fun w => interval_not w));
        [reflexivity|exact Sound.interval_not_sound|exact Ha|exact Hr].
    - eapply interval_entry1_sound with (f := fun rw _ => interval_neg rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr.
      eapply (interval_unary_semantics bvneg UNeg (fun w => interval_neg w));
        [reflexivity| |exact Ha|exact Hr].
      intros. cbn [eval_unary_tag]. rewrite Fun.wneg_value. now apply Sound.interval_neg_sound.
    - eapply interval_entry1_sound with (f := fun rw _ _ => interval_counts rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr.
      eapply (interval_unary_semantics bvclz UClz (fun w _ => interval_counts w));
        [reflexivity|intros; apply Sound.interval_clz_sound|exact Ha|exact Hr].
    - eapply interval_entry1_sound with (f := fun rw _ _ => interval_counts rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr.
      eapply (interval_unary_semantics bvctz UCtz (fun w _ => interval_counts w));
        [reflexivity|intros; apply Sound.interval_ctz_sound|exact Ha|exact Hr].
    - eapply interval_entry1_sound with (f := fun rw _ _ => interval_counts rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr.
      eapply (interval_unary_semantics bvpopcnt UPopcnt (fun w _ => interval_counts w));
        [reflexivity|intros; apply Sound.interval_popcnt_sound|exact Ha|exact Hr].
    - eapply interval_entry1_sound with (f := fun rw _ => interval_rewrap rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr. rewrite eval_op_zext, (wrap_id w x (proj1 Ha)) in Hr.
      inversion Hr; subst. now apply (Sound.interval_rewrap_sound _ w).
    - eapply interval_entry1_sound with (f := interval_sext);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr. rewrite eval_op_sext in Hr.
      inversion Hr; subst. now apply Sound.interval_sext_sound.
    - eapply interval_entry1_sound with (f := fun rw _ => interval_rewrap rw);
        [exact Hxs|exact Heval|].
      intros w a x Ha Hr. rewrite eval_op_trunc in Hr.
      destruct (Pos.leb target w); [|discriminate].
      rewrite (wrap_id w x (proj1 Ha)) in Hr.
      inversion Hr; subst. now apply (Sound.interval_rewrap_sound _ w).
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_add rw);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_binary_semantics bvadd BAdd interval_add);
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy. cbn [eval_binary_tag]. rewrite Fun.wadd_value.
      exact (Sound.interval_add_sound w w w a' b' x' y' Hx Hy).
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_sub rw);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_binary_semantics bvsub BSub interval_sub);
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy. cbn [eval_binary_tag]. rewrite Fun.wsub_value.
      exact (Sound.interval_sub_sound w w w a' b' x' y' Hx Hy).
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_mul rw);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_binary_semantics bvmul BMul interval_mul);
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy. cbn [eval_binary_tag]. rewrite Fun.wmul_value.
      exact (Sound.interval_mul_sound w w w a' b' x' y' Hx Hy).
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_udiv rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvudiv BUdiv interval_udiv);
        [reflexivity|exact Sound.interval_udiv_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_urem rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvurem BUrem interval_urem);
        [reflexivity|exact Sound.interval_urem_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_sdiv rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvsdiv BSdiv interval_sdiv);
        [reflexivity|exact Sound.interval_sdiv_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_srem rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvsrem BSrem interval_srem);
        [reflexivity|exact Sound.interval_srem_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_smod rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvsmod BSmod interval_smod);
        [reflexivity|exact Sound.interval_smod_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_and rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvand BAnd interval_and);
        [reflexivity|exact Sound.interval_and_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_or_xor rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvor BOr interval_or_xor);
        [reflexivity| |eassumption|eassumption|eassumption].
      intros w a' b' x' y' Hx Hy.
      exact (proj1 (Sound.interval_or_xor_sound w a' b' x' y' Hx Hy)).
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_or_xor rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvxor BXor interval_or_xor);
        [reflexivity| |eassumption|eassumption|eassumption].
      intros w a' b' x' y' Hx Hy.
      exact (proj2 (Sound.interval_or_xor_sound w a' b' x' y' Hx Hy)).
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_shl rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvshl BShl interval_shl);
        [reflexivity|exact Sound.interval_shl_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_lshr rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvlshr BLshr interval_lshr);
        [reflexivity|exact Sound.interval_lshr_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun rw _ _ => interval_ashr rw);
        [exact Hxs|exact Heval|].
      intros. eapply (interval_binary_semantics bvashr BAshr interval_ashr);
        [reflexivity|exact Sound.interval_ashr_sound|eassumption|eassumption|eassumption].
    - eapply interval_entry2_sound with (f := fun _ _ _ => interval_eq);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_comparison_semantics bveq CEq (fun _ => interval_eq));
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy.
      cbn [eval_comparison_tag]. rewrite (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
      now apply (Sound.interval_eq_sound w w).
    - eapply interval_entry2_sound with (f := fun _ _ _ a b => interval_bool_not (interval_eq a b));
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_comparison_semantics bvne CNe
        (fun _ a b => interval_bool_not (interval_eq a b)));
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy.
      cbn [eval_comparison_tag]. rewrite (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
      apply Sound.interval_bool_not_sound. now apply (Sound.interval_eq_sound w w).
    - eapply interval_entry2_sound with (f := fun _ _ _ => interval_ult);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_comparison_semantics bvult CUlt (fun _ => interval_ult));
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy.
      cbn [eval_comparison_tag].
      rewrite Fun.wult_value, (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
      now apply (Sound.interval_ult_sound w w).
    - eapply interval_entry2_sound with (f := fun _ _ _ => interval_ule);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_comparison_semantics bvule CUle (fun _ => interval_ule));
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros w a' b' x' y' Hx Hy.
      cbn [eval_comparison_tag].
      rewrite Fun.wule_value, (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
      now apply (Sound.interval_ule_sound w w).
    - eapply interval_entry2_sound with (f := fun _ w _ => interval_signed_compare w true);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_comparison_semantics bvslt CSlt
        (fun w => interval_signed_compare w true));
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros. cbn [eval_comparison_tag]. rewrite Fun.wslt_value.
      now apply (Sound.interval_signed_compare_sound _ _ _ _ _ _ true).
    - eapply interval_entry2_sound with (f := fun _ w _ => interval_signed_compare w false);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      eapply (interval_comparison_semantics bvsle CSle
        (fun w => interval_signed_compare w false));
        [reflexivity| |exact Ha|exact Hb|exact Hr].
      intros. cbn [eval_comparison_tag]. rewrite Fun.wsle_value.
      now apply (Sound.interval_signed_compare_sound _ _ _ _ _ _ false).
    - eapply interval_entry2_sound with (f := fun rw _ w => interval_concat rw w);
        [exact Hxs|exact Heval|].
      intros wa wb a b x y Ha Hb Hr.
      rewrite eval_op_concat, (wrap_id wa x (proj1 Ha)), (wrap_id wb y (proj1 Hb)) in Hr.
      inversion Hr; subst. now apply (Sound.interval_concat_sound _ wa wb).
    - eapply interval_ite_entry_sound; [exact Hxs|exact Heval].
  Qed.

  (** A successful point test identifies every represented concrete word. *)
  Local Lemma interval_is_point_sound (w : width) i z value :
    interval_pgamma w i value -> interval_is_point i z = true -> value = z.
  Proof.
    intros Hi Hpoint. unfold interval_is_point in Hpoint.
    destruct (interval_finite_helper i) as [[lo hi]|] eqn:Hfinite; [|discriminate].
    apply andb_true_iff in Hpoint as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
    pose proof (Sound.interval_finite_sound w i lo hi value Hi Hfinite). lia.
  Qed.

  (** Extension and truncation retain the original operand under a rewrapped result fact. *)
  Local Lemma interval_bwd1_sound o (rw w : width) q a cs z :
    (exists extra, o = bvzext extra) \/ (exists target, o = bvtrunc target) ->
    Forall2 (fun wp c => fst wp = fst c /\
      interval_pgamma (fst wp) (snd wp) (snd c)) [(w, a)] cs ->
    eval_op o cs = Some (rw, z) -> interval_pgamma rw q z ->
    Forall2 (fun wp c => interval_pgamma (fst wp) (snd wp) (snd c))
      (combine [w] (interval_bwd1 rw q [(w, a)])) cs.
  Proof.
    intros Hkind Hinputs Heval Hq.
    inversion Hinputs as [|wp [v x] tail values [Hwidth Ha] Htail]; subst.
    inversion Htail; subst. change (w = v) in Hwidth. subst v.
    constructor; [|constructor]. cbn [interval_bwd1 combine fst snd].
    apply Sound.interval_assume_rewrap_sound; [now apply Sound.interval_clip_sound|].
    destruct Hkind as [[extra ->]|[target ->]].
    - rewrite eval_op_zext, (wrap_id w x (proj1 Ha)) in Heval.
      inversion Heval; subst. exact Hq.
    - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
      rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst. exact Hq.
  Qed.

  (** Pair refinement retains operands whose checked evaluation satisfies the result fact. *)
  Local Lemma interval_assume_pair_sound o (w v : width) a b q x y (rw : width) z :
    interval_pgamma w a x -> interval_pgamma v b y -> interval_pgamma rw q z ->
    eval_op o [(w, x); (v, y)] = Some (rw, z) ->
    interval_pgamma w (fst (interval_assume_pair o w a b q)) x /\
    interval_pgamma v (snd (interval_assume_pair o w a b q)) y.
  Proof.
    intros Ha Hb Hq Heval. destruct o; try (solve [split; assumption]).
    all: assert (Hwv : w = v) by
      (match type of Heval with
       | eval_op ?o _ = _ =>
         first
           [ eapply (eval_op_fun2_width o); [reflexivity|exact Heval]
           | eapply (eval_op_cmp_width o); [reflexivity|exact Heval] ]
       end); subst v.
    - rewrite (eval_op_fun2 bvadd w x y BAdd eq_refl) in Heval.
      cbn [eval_binary_tag] in Heval.
      inversion Heval; subst rw z. rewrite Fun.wadd_value in Hq.
      now apply Sound.interval_assume_add_sound.
    - rewrite (eval_op_fun2 bvsub w x y BSub eq_refl) in Heval.
      cbn [eval_binary_tag] in Heval.
      inversion Heval; subst rw z. rewrite Fun.wsub_value in Hq.
      now apply Sound.interval_assume_sub_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bveq w x y CEq eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
        apply Z.eqb_eq in Heq. subst y. now apply Sound.interval_assume_equal_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate|].
        apply Z.eqb_neq in Heq. now apply Sound.interval_assume_neq_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvne w x y CNe eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 0) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 0 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
        apply Z.eqb_eq in Heq. subst y. now apply Sound.interval_assume_equal_sound.
      + destruct (interval_is_point q 1) eqn:Hpoint1; [|split; assumption].
        pose proof (interval_is_point_sound rw q 1 z Hq Hpoint1) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate|].
        apply Z.eqb_neq in Heq. now apply Sound.interval_assume_neq_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvult w x y CUlt eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wult_value in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [|discriminate].
        apply Z.ltb_lt in Hlt. now apply Sound.interval_assume_ult_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [discriminate|].
        apply Z.ltb_ge in Hlt.
        destruct (Sound.interval_assume_ule_sound w w b a y x Hb Ha Hlt) as [Hfirst Hsecond].
        split; assumption.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvule w x y CUle eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wule_value in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb x y) eqn:Hle; [|discriminate].
        apply Z.leb_le in Hle. now apply Sound.interval_assume_ule_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb x y) eqn:Hle; [discriminate|].
        apply Z.leb_gt in Hle.
        destruct (Sound.interval_assume_ult_sound w w b a y x Hb Ha Hle) as [Hfirst Hsecond].
        split; assumption.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvslt w x y CSlt eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wslt_value in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
          [|discriminate]. now apply Sound.interval_assume_signed_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
          [discriminate|]. now apply Sound.interval_assume_signed_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvsle w x y CSle eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wsle_value in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
          [|discriminate]. now apply Sound.interval_assume_signed_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
          [discriminate|]. now apply Sound.interval_assume_signed_sound.
  Qed.

  (** Binary backward dispatch preserves both clipped operands at their original widths. *)
  Local Lemma interval_bwd2_sound o (rw wa wb : width) q a b cs z :
    Forall2 (fun wp c => fst wp = fst c /\
      interval_pgamma (fst wp) (snd wp) (snd c)) [(wa, a); (wb, b)] cs ->
    eval_op o cs = Some (rw, z) -> interval_pgamma rw q z ->
    Forall2 (fun wp c => interval_pgamma (fst wp) (snd wp) (snd c))
      (combine [wa; wb] (interval_bwd2 o rw q [(wa, a); (wb, b)])) cs.
  Proof.
    intros Hinputs Heval Hq.
    inversion Hinputs as [|wp [wx x] tail values [Hwa Ha] Htail]; subst.
    inversion Htail as [|wp [wy y] tail' values' [Hwb Hb] Hlast]; subst.
    inversion Hlast; subst.
    change (wa = wx) in Hwa. change (wb = wy) in Hwb. subst wx wy.
    pose proof (interval_assume_pair_sound o wa wb
      (interval_clip wa a) (interval_clip wb b) q x y rw z
      (Sound.interval_clip_sound wa a x Ha) (Sound.interval_clip_sound wb b y Hb) Hq Heval)
      as [Hleft Hright].
    constructor; [exact Hleft|constructor; [exact Hright|constructor]].
  Qed.

  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof.
    intros o rw q wps ys cs z Hentry Hxs Heval Hq.
    apply interval_inputs_sound in Hxs. apply interval_payload_spec in Hq.
    assert (Hresult : Forall2 (fun wp c =>
      interval_pgamma (fst wp) (snd wp) (snd c)) (combine (map fst wps) ys) cs).
    { destruct wps as [|[wa a] [|[wb b] [|extra rest]]];
        destruct o; cbn [wbwd] in Hentry; try discriminate; inversion Hentry; subst ys.
      all: try (match type of Heval with
        | L.eval_op ?o _ = _ =>
          exact (interval_bwd2_sound o rw wa wb q a b cs z Hxs Heval Hq)
        end).
      - eapply interval_bwd1_sound;
          [left; eexists; reflexivity|exact Hxs|exact Heval|exact Hq].
      - eapply interval_bwd1_sound;
          [right; eexists; reflexivity|exact Hxs|exact Heval|exact Hq]. }
    clear Hentry Hxs Heval Hq.
    induction Hresult as [|wp c xs values Hhead Htail IH].
    - constructor.
    - constructor; [now apply interval_payload_spec|exact IH].
  Qed.
End IntervalWordTable.

Module IntervalWordTableT (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (Scalar : INTERVAL_SCALAR_T T)
    (W : INTERVAL_PAYLOAD_ALL L T Scalar)
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

  Module PayloadBounds := IntervalPayloadT L T Scalar.

  Local Lemma table_clip_bits : forall w a, interval_bits (interval_clip w a) <= Pos.to_nat w.
  Proof.
    exact PayloadBounds.payload_clip_bits.
  Qed.

  Local Lemma table_checked_bits : forall w lo hi, (lo <= hi)%Z ->
    interval_bits (interval_checked w lo hi) <= Pos.to_nat w.
  Proof.
    intros w lo hi Hordered.
    unfold interval_checked.
    destruct (Z.leb 0 lo && Z.ltb hi (Word.modulus w)) eqn:Hcheck.
    - apply andb_true_iff in Hcheck as [Hlo Hhi].
      apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
      cbn [interval_bits]. apply Nat.max_lub;
        apply PayloadBounds.payload_word_bits; unfold Word.is_word; lia.
    - exact (PayloadBounds.payload_top_bits w).
  Qed.

  Local Lemma table_truth_bits : forall decision,
    interval_bits (interval_truth decision) <= 1.
  Proof.
    intros [[|]|]; cbn [interval_truth interval_bits Z.size_nat Pos.size_nat]; lia.
  Qed.

  Local Lemma table_positive_bits : forall p, Pos.size_nat p <= Pos.to_nat p.
  Proof.
    induction p as [p IH|p IH|]; cbn [Pos.size_nat];
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
  Qed.

  Local Lemma table_counts_bits : forall w,
    interval_bits (interval_counts w) <= Pos.to_nat w.
  Proof.
    intro w.
    cbn [interval_counts interval_bits Z.size_nat].
    apply table_positive_bits.
  Qed.

  Local Lemma table_not_bits : forall rw w a,
    interval_bits (interval_not rw (interval_clip w a)) <= Pos.to_nat rw.
  Proof.
    intros rw w a.
    change (interval_bits (interval_not rw (PayloadBounds.interval_clip w a)) <=
      Pos.to_nat rw).
    destruct (PayloadBounds.interval_clip_shape w a)
      as [Hbot|[lo [hi [Hshape [_ [Hordered _]]]]]].
    - rewrite Hbot. cbn [interval_not interval_finite_helper].
      exact (PayloadBounds.payload_top_bits rw).
    - rewrite Hshape. cbn [interval_not interval_finite_helper].
      apply table_checked_bits. lia.
  Qed.

  Local Lemma table_rewrap_bits : forall rw w a,
    interval_bits (interval_rewrap rw (interval_clip w a)) <= Pos.to_nat rw.
  Proof.
    intros rw w a.
    change (interval_bits (interval_rewrap rw (PayloadBounds.interval_clip w a)) <=
      Pos.to_nat rw).
    destruct (PayloadBounds.interval_clip_shape w a)
      as [Hbot|[lo [hi [Hshape [_ [Hordered _]]]]]].
    - rewrite Hbot. cbn [interval_rewrap interval_finite_helper].
      exact (PayloadBounds.payload_top_bits rw).
    - rewrite Hshape. cbn [interval_rewrap interval_finite_helper].
      apply table_checked_bits. exact Hordered.
  Qed.

  Local Lemma table_neg_bits : forall rw w a,
    interval_bits (interval_neg rw (interval_clip w a)) <= Pos.to_nat rw.
  Proof.
    intros rw w a.
    change (interval_bits (interval_neg rw (PayloadBounds.interval_clip w a)) <=
      Pos.to_nat rw).
    destruct (PayloadBounds.interval_clip_shape w a)
      as [Hbot|[lo [hi [Hshape [_ [Hordered _]]]]]].
    - rewrite Hbot. cbn [interval_neg interval_finite_helper].
      exact (PayloadBounds.payload_top_bits rw).
    - rewrite Hshape. cbn [interval_neg interval_finite_helper].
      destruct (Z.eqb hi 0).
      + cbn [interval_bits Z.size_nat]. lia.
      + destruct (Z.ltb 0 lo).
        * apply table_checked_bits. lia.
        * exact (PayloadBounds.payload_top_bits rw).
  Qed.

  Local Lemma table_add_bits : forall rw wa wb a b,
    interval_bits (interval_add rw (interval_clip wa a) (interval_clip wb b)) <=
      Pos.to_nat rw.
  Proof.
    intros rw wa wb a b.
    change (interval_bits (interval_add rw
      (PayloadBounds.interval_clip wa a) (PayloadBounds.interval_clip wb b)) <= Pos.to_nat rw).
    destruct (PayloadBounds.interval_clip_shape wa a)
      as [Ha|[la [ha [Ha [_ [Ha_order _]]]]]];
      destruct (PayloadBounds.interval_clip_shape wb b)
      as [Hb|[lb [hb [Hb [_ [Hb_order _]]]]]];
      rewrite Ha, Hb; cbn [interval_add interval_finite_helper];
      try exact (PayloadBounds.payload_top_bits rw).
    apply table_checked_bits. lia.
  Qed.

  Local Lemma table_sub_bits : forall rw wa wb a b,
    interval_bits (interval_sub rw (interval_clip wa a) (interval_clip wb b)) <=
      Pos.to_nat rw.
  Proof.
    intros rw wa wb a b.
    change (interval_bits (interval_sub rw
      (PayloadBounds.interval_clip wa a) (PayloadBounds.interval_clip wb b)) <= Pos.to_nat rw).
    destruct (PayloadBounds.interval_clip_shape wa a)
      as [Ha|[la [ha [Ha [_ [Ha_order _]]]]]];
      destruct (PayloadBounds.interval_clip_shape wb b)
      as [Hb|[lb [hb [Hb [_ [Hb_order _]]]]]];
      rewrite Ha, Hb; cbn [interval_sub interval_finite_helper];
      try exact (PayloadBounds.payload_top_bits rw).
    apply table_checked_bits. lia.
  Qed.

  Local Lemma table_mul_bits : forall rw wa wb a b,
    interval_bits (interval_mul rw (interval_clip wa a) (interval_clip wb b)) <=
      Pos.to_nat rw.
  Proof.
    intros rw wa wb a b.
    change (interval_bits (interval_mul rw
      (PayloadBounds.interval_clip wa a) (PayloadBounds.interval_clip wb b)) <= Pos.to_nat rw).
    destruct (PayloadBounds.interval_clip_shape wa a)
      as [Ha|[la [ha [Ha [Ha_nonneg [Ha_order _]]]]]];
      destruct (PayloadBounds.interval_clip_shape wb b)
      as [Hb|[lb [hb [Hb [Hb_nonneg [Hb_order _]]]]]];
      rewrite Ha, Hb; cbn [interval_mul interval_finite_helper];
      try exact (PayloadBounds.payload_top_bits rw).
    destruct (Z.leb 0 la && Z.leb 0 lb).
    - apply table_checked_bits. nia.
    - exact (PayloadBounds.payload_top_bits rw).
  Qed.

  Local Lemma table_bool_not_bits : forall a,
    interval_bits (interval_bool_not a) <= 1.
  Proof.
    intro a.
    unfold interval_bool_not.
    destruct (interval_finite_helper a) as [[lo hi]|];
      try (destruct (Z.eqb lo 0); destruct (Z.eqb hi 0);
        destruct (Z.eqb lo 1); destruct (Z.eqb hi 1));
      apply table_truth_bits.
  Qed.

  Local Lemma table_eq_bits : forall a b, interval_bits (interval_eq a b) <= 1.
  Proof.
    intros a b.
    unfold interval_eq.
    destruct (interval_finite_helper a) as [[la ha]|];
      destruct (interval_finite_helper b) as [[lb hb]|];
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      apply table_truth_bits.
  Qed.

  Local Lemma table_ult_bits : forall a b, interval_bits (interval_ult a b) <= 1.
  Proof.
    intros a b.
    unfold interval_ult.
    destruct (interval_finite_helper a) as [[la ha]|];
      destruct (interval_finite_helper b) as [[lb hb]|];
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      apply table_truth_bits.
  Qed.

  Local Lemma table_ule_bits : forall a b, interval_bits (interval_ule a b) <= 1.
  Proof.
    intros a b.
    unfold interval_ule.
    destruct (interval_finite_helper a) as [[la ha]|];
      destruct (interval_finite_helper b) as [[lb hb]|];
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      apply table_truth_bits.
  Qed.

  Local Lemma table_signed_compare_bits : forall w strict a b,
    interval_bits (interval_signed_compare w strict a b) <= 1.
  Proof.
    intros w strict a b.
    unfold interval_signed_compare.
    destruct (interval_signed w a) as [[la ha]|];
      destruct (interval_signed w b) as [[lb hb]|]; destruct strict;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      apply table_truth_bits.
  Qed.

  Local Lemma table_clip_time : forall w a,
    (T_interval_clip w a <= (W.k_payload_clip + 1) *
      N.of_nat (W.psize w a + 1))%N.
  Proof.
    intros w a.
    pose proof (W.T_clip_le w a) as Hclip.
    unfold T_interval_clip.
    unfold T_interval_top.
    time_cbn.
    unfold T_interval_payload_clip in Hclip.
    time_cbn_all.
    unfold interval_top.
    unfold Word.modulus.
    replace (2 ^ Z.pos w)%Z with (Z.pow_pos 2 w) by reflexivity.
    rewrite Nat2N.inj_add in *.
    nia.
  Qed.

  Local Lemma table_raw_size : forall w a, interval_bits a <= W.psize w a.
  Proof.
    intros w a.
    rewrite W.F_psize.
    lia.
  Qed.

  Local Lemma table_ite_size : forall rw wa wb a b,
    W.psize rw (Scalar.interval_join (interval_clip wa a) (interval_clip wb b)) <=
      (Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2.
  Proof.
    intros rw wa wb a b.
    pose proof (PayloadBounds.payload_raw_join_bits
      (interval_clip wa a) (interval_clip wb b)) as Hjoin.
    pose proof (table_clip_bits wa a) as Ha.
    pose proof (table_clip_bits wb b) as Hb.
    pose proof (Pos2Nat.is_pos rw) as Hr.
    rewrite W.F_psize.
    rewrite Nat.pow_2_r.
    nia.
  Qed.

  Local Lemma table_boolean_size : forall rw r,
    interval_bits r <= 1 -> W.psize rw r <= (Pos.to_nat rw + 1) ^ 2.
  Proof.
    intros rw r Hbits.
    pose proof (Pos2Nat.is_pos rw) as Hwidth.
    rewrite W.F_psize, Nat.pow_2_r.
    nia.
  Qed.

  Local Lemma table_ite_time : forall rw wa wb a b,
    (T_interval_clip wa a + T_interval_clip wb b +
      Scalar.T_interval_join (interval_clip wa a) (interval_clip wb b) <=
      8 * (W.k_payload_clip + Scalar.c_scalar + 1) *
      N.of_nat ((Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
        W.psize wa a + W.psize wb b))%N.
  Proof.
    intros rw wa wb a b.
    pose proof (table_clip_time wa a) as Ha.
    pose proof (table_clip_time wb b) as Hb.
    pose proof (table_clip_bits wa a) as Hbits_a.
    pose proof (table_clip_bits wb b) as Hbits_b.
    pose proof (Scalar.T_interval_join_le (interval_clip wa a) (interval_clip wb b))
      as Hjoin.
    pose proof (Pos2Nat.is_pos rw) as Hr.
    assert (Hjoin' :
      (Scalar.T_interval_join (interval_clip wa a) (interval_clip wb b) <=
        Scalar.c_scalar * N.of_nat (Pos.to_nat wa + Pos.to_nat wb + 1))%N).
    { rewrite !Nat2N.inj_add in *.
      nia. }
    assert (Hwidth :
      (N.of_nat (Pos.to_nat wa + Pos.to_nat wb + 1) <=
        N.of_nat ((Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2))%N).
    { rewrite Nat.pow_2_r, !Nat2N.inj_add, !Nat2N.inj_mul. nia. }
    rewrite !Nat2N.inj_add in *.
    nia.
  Qed.

  Definition c_word_table : N := (1000000 * (W.k_payload_clip + Scalar.c_scalar + 1))%N.

  Local Lemma table_ite_dispatch_time : forall rw wc c wa a wb b,
    (T_wfwd bvite rw [(wc, c); (wa, a); (wb, b)] <= c_word_table * N.of_nat
      (((Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
        W.psize wc c + W.psize wa a + W.psize wb b)%nat))%N.
  Proof.
    intros rw wc c wa a wb b.
    pose proof (table_ite_time rw wa wb a b) as Hite.
    unfold T_wfwd, c_word_table.
    time_cbn.
    assert (Hbudget_nat :
      ((Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
        W.psize wa a + W.psize wb b <=
       (Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
        W.psize wc c + W.psize wa a + W.psize wb b)%nat).
    { assert (Hbase :
        (Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1 <=
         Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1)%nat)
        by lia.
      pose proof (Nat.pow_le_mono_l _ _ 2 Hbase) as Hsquare.
      lia. }
    set (small := N.of_nat ((Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
      W.psize wa a + W.psize wb b)) in *.
    set (large := N.of_nat ((Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa +
      Pos.to_nat wb + 1) ^ 2 + W.psize wc c + W.psize wa a + W.psize wb b)) in *.
    assert (Hbudget : (small <= large)%N) by (subst small large; lia).
    assert (Hpositive : (1 <= large)%N).
    { assert (Hbase :
        (0 < Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1)%nat)
        by lia.
      assert (Hpow :
        (0 < (Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2)%nat)
        by (rewrite Nat.pow_2_r; nia).
      subst large. lia. }
    assert (Hcoefficient : (1 <= W.k_payload_clip + Scalar.c_scalar + 1)%N) by lia.
    change (1 + (T_interval_clip wa a + T_interval_clip wb b +
      Scalar.T_interval_join (interval_clip wa a) (interval_clip wb b)) <=
      1000000 * (W.k_payload_clip + Scalar.c_scalar + 1) * large)%N.
    nia.
  Qed.

  Local Lemma table_ite_dispatch_size : forall rw wc c wa a wb b,
    (N.of_nat (W.psize rw (Scalar.interval_join (interval_clip wa a) (interval_clip wb b))) <=
      c_word_table * N.of_nat
        (((Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
          W.psize wc c + W.psize wa a + W.psize wb b)%nat))%N.
  Proof.
    intros rw wc c wa a wb b.
    pose proof (table_ite_size rw wa wb a b) as Hsize.
    assert (Hbudget_nat :
      ((Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 <=
       (Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2 +
        W.psize wc c + W.psize wa a + W.psize wb b)%nat).
    { apply Nat.le_trans with
        (m := (Pos.to_nat rw + Pos.to_nat wc + Pos.to_nat wa + Pos.to_nat wb + 1) ^ 2).
      - apply Nat.pow_le_mono_l. lia.
      - lia. }
    unfold c_word_table.
    assert (Hcoefficient : (1 <= 1000000 * (W.k_payload_clip + Scalar.c_scalar + 1))%N)
      by nia.
    nia.
  Qed.

  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs.
    time_step.
  Admitted. (* OPEN: bound the timed unary and binary interval dispatches. *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* OPEN: bound timed backward clipping and refinement dispatches. *)
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (W.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* OPEN: bound the raw result bits of each forward dispatch. *)
  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* OPEN: bound the raw result bits of backward refinements. *)
End IntervalWordTableT.
