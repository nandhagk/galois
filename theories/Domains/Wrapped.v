(** * Circular word intervals

    Circular arcs represent inclusive sets of words across either numeric pole.
    For example, the eight-bit arc from 250 to 3 contains zero.
    Builds on: WrappedSig, Interval and the bit-vector operations. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Bits Require Import Word Op Fun Arith.
From Galois.Domains Require Import ValueSig WordSig WrappedSig IntervalSig Interval IntervalOps
  Thresholds BitsLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Module WrappedScalar := IntervalBaseT ThresholdsT.

Definition arc_wrap (w : width) (z : Z) : Z := Z.land z (Z.ones (Zpos w)).
TimeFun arc_wrap.

(** The mask agrees with modular word reduction. *)
Lemma arc_wrap_agrees : forall w z, arc_wrap w z = wrap w z.
Proof.
  intros w z. symmetry. rewrite wrap_mod. unfold arc_wrap, modulus.
  symmetry. apply Z.land_ones. lia.
Qed.

(** The mask is integer remainder modulo the word modulus. *)
Lemma arc_wrap_mod : forall w z, arc_wrap w z = z mod modulus w.
Proof.
  intros w z. rewrite arc_wrap_agrees. apply wrap_mod.
Qed.

Definition wrapped_offset (w : width) (origin x : Z) : Z :=
  arc_wrap w (x - origin).
TimeFun wrapped_offset.

Definition wrapped_size (w : width) (a : wrapped) : Z :=
  match a with
  | WBot => 0
  | WFull => modulus w
  | WItv lo hi => wrapped_offset w lo hi + 1
  end.
TimeFun wrapped_size.

Definition wrapped_gamma (w : width) (a : wrapped) (z : Z) : Prop :=
  match a with
  | WBot => False
  | WFull => is_word w z
  | WItv lo hi => is_word w z /\ wrapped_offset w lo z <= wrapped_offset w lo hi
  end.

Definition wrapped_norm (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi =>
    if wrapped_offset w lo hi =? modulus w - 1
    then WFull else WItv (arc_wrap w lo) (arc_wrap w hi)
  | _ => a
  end.
TimeFun wrapped_norm.

Definition wrapped_leb (w : width) (a b : wrapped) : bool :=
  match a, b with
  | WBot, _ => true
  | _, WFull => true
  | _, WBot => false
  | WFull, WItv lo hi => wrapped_offset w lo hi =? modulus w - 1
  | WItv a b, WItv c d =>
    (wrapped_offset w c d =? modulus w - 1) ||
    (wrapped_offset w c a + wrapped_offset w a b <=? wrapped_offset w c d)
  end.
TimeFun wrapped_leb.

Definition wrapped_cover (w : width) (a b candidate : wrapped) : bool :=
  wrapped_leb w a candidate && wrapped_leb w b candidate.
TimeFun wrapped_cover.

Definition wrapped_choose (w : width) (a b first second : wrapped) : wrapped :=
  if wrapped_cover w a b first then
    if wrapped_cover w a b second then
      if wrapped_size w first <=? wrapped_size w second then first else second
    else first
  else if wrapped_cover w a b second then second else WFull.
TimeFun wrapped_choose.

Definition wrapped_join (w : width) (a b : wrapped) : wrapped :=
  wrapped_norm w
    (if wrapped_leb w a b then b else
     if wrapped_leb w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end).
TimeFun wrapped_join.

Definition wrapped_double (w : width) (a : wrapped) : wrapped :=
  match a with
  | WBot => WBot
  | WFull => WFull
  | WItv lo hi =>
    let size := wrapped_size w a in
    if modulus w <=? 3 * size then WFull
    else wrapped_norm w (WItv (lo - size) (hi + size))
  end.
TimeFun wrapped_double.

Definition wrapped_widen (w : width) (a b : wrapped) : wrapped :=
  if wrapped_leb w b a then wrapped_norm w a
  else wrapped_join w (wrapped_double w a) b.
TimeFun wrapped_widen.

Definition wrapped_narrow (w : width) (a b : wrapped) : wrapped :=
  match wrapped_norm w a with
  | WFull => wrapped_norm w b
  | _ => wrapped_norm w a
  end.
TimeFun wrapped_narrow.

Definition wrapped_range (w : width) (lo hi : Z) : wrapped :=
  if hi <? lo then WBot else
  if modulus w - 1 <=? hi - lo then WFull else wrapped_norm w (WItv lo hi).
TimeFun wrapped_range.

Definition wrapped_of_interval (w : width) (i : itv) : wrapped :=
  match i with
  | IBot => WBot
  | I (Fin lo) (Fin hi) => wrapped_range w lo hi
  | _ => WFull
  end.
TimeFun wrapped_of_interval.

Definition wrapped_parts_raw (w : width) (a : wrapped) : itv * itv :=
  match a with
  | WBot => (IBot, IBot)
  | WFull => (I (Fin 0) (Fin (modulus w - 1)), IBot)
  | WItv lo hi =>
    let lo' := arc_wrap w lo in
    let hi' := arc_wrap w hi in
    if lo' <=? hi' then (I (Fin lo') (Fin hi'), IBot)
    else (I (Fin lo') (Fin (modulus w - 1)), I (Fin 0) (Fin hi'))
  end.
TimeFun wrapped_parts_raw.

Definition wrapped_parts (w : width) (a : wrapped) : itv * itv :=
  wrapped_parts_raw w (wrapped_norm w a).
TimeFun wrapped_parts.

Definition wrapped_join_four (w : width) (a b c d : wrapped) : wrapped :=
  wrapped_join w (wrapped_join w a b) (wrapped_join w c d).
TimeFun wrapped_join_four.

Definition wrapped_meet (w : width) (a b : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pb := wrapped_parts w b in
  let candidate := wrapped_join_four w
    (wrapped_of_interval w (WrappedScalar.interval_meet (fst pa) (fst pb)))
    (wrapped_of_interval w (WrappedScalar.interval_meet (fst pa) (snd pb)))
    (wrapped_of_interval w (WrappedScalar.interval_meet (snd pa) (fst pb)))
    (wrapped_of_interval w (WrappedScalar.interval_meet (snd pa) (snd pb))) in
  if wrapped_leb w candidate a then candidate else wrapped_norm w a.
TimeFun wrapped_meet.

Definition wrapped_size_rank (w : width) (size : Z) : Z :=
  if size =? 0 then Zpos w + 2 else
  if size =? modulus w then 0 else Zpos w + 1 - Z.log2 size.

Definition wrapped_add (w : width) (a b : wrapped) : wrapped :=
  match a, b with
  | WBot, _ | _, WBot => WBot
  | WItv lo hi, WItv lo' hi' =>
    if modulus w <? wrapped_size w a + wrapped_size w b then WFull
    else wrapped_norm w (WItv (lo + lo') (hi + hi'))
  | _, _ => WFull
  end.
TimeFun wrapped_add.

Definition wrapped_neg (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi => wrapped_norm w (WItv (- hi) (- lo))
  | _ => a
  end.
TimeFun wrapped_neg.

Definition wrapped_sub (w : width) (a b : wrapped) : wrapped :=
  wrapped_add w a (wrapped_neg w b).
TimeFun wrapped_sub.

Definition wrapped_mul_piece (w : width) (a b : itv) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | I (Fin lo) (Fin hi), I (Fin lo') (Fin hi') =>
    let p1 := lo * lo' in
    let p2 := lo * hi' in
    let p3 := hi * lo' in
    let p4 := hi * hi' in
    wrapped_range w
      (Z.min (Z.min p1 p2) (Z.min p3 p4))
      (Z.max (Z.max p1 p2) (Z.max p3 p4))
  | _, _ => WFull
  end.
TimeFun wrapped_mul_piece.

Definition wrapped_shift_interval (delta : Z) (a : itv) : itv :=
  let shift := fun b =>
    match b with
    | Fin z => Fin (z + delta)
    | _ => b
    end in
  match a with
  | IBot => IBot
  | I lo hi => I (shift lo) (shift hi)
  end.
TimeFun wrapped_shift_interval.

Definition wrapped_signed_parts (w : width) (a : wrapped) : itv * itv :=
  let biased := wrapped_parts w (wrapped_add w a (WItv (half w) (half w))) in
  (wrapped_shift_interval (- half w) (fst biased),
   wrapped_shift_interval (- half w) (snd biased)).
TimeFun wrapped_signed_parts.

Definition wrapped_mul_parts (w : width) (a b : itv * itv) : wrapped :=
  wrapped_join_four w
    (wrapped_mul_piece w (fst a) (fst b))
    (wrapped_mul_piece w (fst a) (snd b))
    (wrapped_mul_piece w (snd a) (fst b))
    (wrapped_mul_piece w (snd a) (snd b)).
TimeFun wrapped_mul_parts.

Definition wrapped_mul_cut (pole : Z) (a : itv) : itv * itv :=
  (WrappedScalar.interval_meet a (I NegInf (Fin (pole - 1))),
   WrappedScalar.interval_meet a (I (Fin pole) PosInf)).
TimeFun wrapped_mul_cut.

Definition wrapped_mul_both_parts (w : width) (pole : Z) (a b : itv * itv) : wrapped :=
  let a0 := wrapped_mul_cut pole (fst a) in
  let a1 := wrapped_mul_cut pole (snd a) in
  let b0 := wrapped_mul_cut pole (fst b) in
  let b1 := wrapped_mul_cut pole (snd b) in
  wrapped_join_four w
    (wrapped_mul_parts w a0 b0) (wrapped_mul_parts w a0 b1)
    (wrapped_mul_parts w a1 b0) (wrapped_mul_parts w a1 b1).
TimeFun wrapped_mul_both_parts.

Definition wrapped_mul (w : width) (a b : wrapped) : wrapped :=
  let unsigned := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) in
  let signed := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b) in
  if wrapped_size w unsigned <=? wrapped_size w signed then unsigned else signed.
TimeFun wrapped_mul.

(** A cover with at most one value cannot be improved by the signed multiplication pass. *)
Definition wrapped_mul_fast (w : width) (a b : wrapped) : wrapped :=
  let unsigned := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) in
  let usize := wrapped_size w unsigned in
  if usize <=? 1 then unsigned else
  let signed := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b) in
  if usize <=? wrapped_size w signed then unsigned else signed.
TimeFun wrapped_mul_fast.

Definition wrapped_pole_cut (w : width) (a : itv) : itv * itv :=
  (WrappedScalar.interval_meet a (I (Fin 0) (Fin (half w - 1))),
   WrappedScalar.interval_meet a (I (Fin (half w)) (Fin (modulus w - 1)))).
TimeFun wrapped_pole_cut.

Definition wrapped_point w a : option Z :=
  match wrapped_norm w a with
  | WItv lo hi => if Z.eqb lo hi then Some lo else None
  | _ => None
  end.
TimeFun wrapped_point.

Module WrappedIntervalOps := IntervalOpsT ThresholdsT WrappedScalar.

Definition wrapped_interval_pair (w : width) (a : itv * itv) : wrapped :=
  wrapped_join w (wrapped_of_interval w (fst a)) (wrapped_of_interval w (snd a)).
TimeFun wrapped_interval_pair.

Definition wrapped_not_piece (w : width) (a : itv) : wrapped :=
  match a with
  | IBot => WBot
  | _ => wrapped_of_interval w (WrappedIntervalOps.interval_not w a)
  end.
TimeFun wrapped_not_piece.

Definition wrapped_not (w : width) (a : wrapped) : wrapped :=
  let parts := wrapped_parts w a in
  wrapped_join w
    (wrapped_not_piece w (fst parts))
    (wrapped_not_piece w (snd parts)).
TimeFun wrapped_not.

Definition wrapped_div_piece (remainder : bool) (w : width) (a b : itv) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | _, _ => wrapped_of_interval w
      (if remainder then WrappedIntervalOps.interval_urem w a b
       else WrappedIntervalOps.interval_udiv w a b)
  end.
TimeFun wrapped_div_piece.

Definition wrapped_div_cut (remainder : bool) (w : width) (a b : itv) : wrapped :=
  let pa := wrapped_pole_cut w a in
  let pb := wrapped_pole_cut w b in
  wrapped_join_four w
    (wrapped_div_piece remainder w (fst pa) (fst pb))
    (wrapped_div_piece remainder w (fst pa) (snd pb))
    (wrapped_div_piece remainder w (snd pa) (fst pb))
    (wrapped_div_piece remainder w (snd pa) (snd pb)).
TimeFun wrapped_div_cut.

Definition wrapped_div (remainder : bool) (w : width) (a b : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pb := wrapped_parts w b in
  wrapped_join_four w
    (wrapped_div_cut remainder w (fst pa) (fst pb))
    (wrapped_div_cut remainder w (fst pa) (snd pb))
    (wrapped_div_cut remainder w (snd pa) (fst pb))
    (wrapped_div_cut remainder w (snd pa) (snd pb)).
TimeFun wrapped_div.

Definition wrapped_udiv := wrapped_div false.
Definition wrapped_urem := wrapped_div true.
TimeFun wrapped_udiv.
TimeFun wrapped_urem.

Definition wrapped_interval_list (a : itv) : list (Z * Z) :=
  match a with
  | I (Fin lo) (Fin hi) => [(lo, hi)]
  | _ => []
  end.
TimeFun wrapped_interval_list.

Definition wrapped_split (w : width) (a : wrapped) : list (Z * Z) :=
  let parts := wrapped_parts w a in
  let lo := wrapped_pole_cut w (fst parts) in
  let hi := wrapped_pole_cut w (snd parts) in
  wrapped_interval_list (fst lo) ++ wrapped_interval_list (snd lo) ++
  wrapped_interval_list (fst hi) ++ wrapped_interval_list (snd hi).
TimeFun wrapped_split.

(** * Circular operations with a shared mask *)

Definition arc_wrap_m (m z : Z) : Z := Z.land z m.
TimeFun arc_wrap_m.

Definition wrapped_offset_m (m : Z) (_ : width) (origin x : Z) : Z :=
  arc_wrap_m m (x - origin).
TimeFun wrapped_offset_m.

Definition wrapped_size_m (m : Z) (w : width) (a : wrapped) : Z :=
  match a with
  | WBot => 0
  | WFull => m + 1
  | WItv lo hi => wrapped_offset_m m w lo hi + 1
  end.
TimeFun wrapped_size_m.

Definition wrapped_norm_m (m : Z) (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi =>
    if wrapped_offset_m m w lo hi =? m
    then WFull else WItv (arc_wrap_m m lo) (arc_wrap_m m hi)
  | _ => a
  end.
TimeFun wrapped_norm_m.

Definition wrapped_leb_m (m : Z) (w : width) (a b : wrapped) : bool :=
  match a, b with
  | WBot, _ => true
  | _, WFull => true
  | _, WBot => false
  | WFull, WItv lo hi => wrapped_offset_m m w lo hi =? m
  | WItv a b, WItv c d =>
    if wrapped_offset_m m w c d =? m then true else
    wrapped_offset_m m w c a + wrapped_offset_m m w a b <=?
      wrapped_offset_m m w c d
  end.
TimeFun wrapped_leb_m.

Definition wrapped_cover_m (m : Z) (w : width) (a b candidate : wrapped) : bool :=
  if wrapped_leb_m m w a candidate then wrapped_leb_m m w b candidate else false.
TimeFun wrapped_cover_m.

Definition wrapped_choose_m (m : Z) (w : width) (a b first second : wrapped) : wrapped :=
  if wrapped_cover_m m w a b first then
    if wrapped_cover_m m w a b second then
      if wrapped_size_m m w first <=? wrapped_size_m m w second then first else second
    else first
  else if wrapped_cover_m m w a b second then second else WFull.
TimeFun wrapped_choose_m.

Definition wrapped_join_m (m : Z) (w : width) (a b : wrapped) : wrapped :=
  wrapped_norm_m m w
    (if wrapped_leb_m m w a b then b else
     if wrapped_leb_m m w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose_m m w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end).
TimeFun wrapped_join_m.

Definition wrapped_double_m (m : Z) (w : width) (a : wrapped) : wrapped :=
  match a with
  | WBot => WBot
  | WFull => WFull
  | WItv lo hi =>
    let size := wrapped_size_m m w a in
    if m + 1 <=? 3 * size then WFull
    else wrapped_norm_m m w (WItv (lo - size) (hi + size))
  end.
TimeFun wrapped_double_m.

Definition wrapped_narrow_m (m : Z) (w : width) (a b : wrapped) : wrapped :=
  let normalized := wrapped_norm_m m w a in
  match normalized with
  | WFull => wrapped_norm_m m w b
  | _ => normalized
  end.
TimeFun wrapped_narrow_m.

(** The all-ones mask is the largest word of its width. *)
Lemma arc_mask_last : forall w, Z.ones (Zpos w) = modulus w - 1.
Proof.
  intro w. unfold modulus. apply Z.ones_equiv.
Qed.

(** Incrementing the all-ones mask gives the word modulus. *)
Lemma arc_mask_modulus : forall w, Z.ones (Zpos w) + 1 = modulus w.
Proof.
  intro w. rewrite arc_mask_last. lia.
Qed.

(** A prepared mask performs the same word reduction as the original helper. *)
Lemma arc_wrap_m_agrees : forall w z, arc_wrap_m (Z.ones (Zpos w)) z = arc_wrap w z.
Proof.
  reflexivity.
Qed.

(** Reusing the mask leaves circular offsets unchanged. *)
Lemma wrapped_offset_m_agrees : forall w origin x,
  wrapped_offset_m (Z.ones (Zpos w)) w origin x = wrapped_offset w origin x.
Proof.
  reflexivity.
Qed.

(** Reusing the mask leaves arc cardinality unchanged. *)
Lemma wrapped_size_m_agrees : forall w a,
  wrapped_size_m (Z.ones (Zpos w)) w a = wrapped_size w a.
Proof.
  intros w [| |lo hi]; cbn [wrapped_size_m wrapped_size]; try reflexivity.
  apply arc_mask_modulus.
Qed.

(** Reusing the mask leaves normalized endpoints and full circles unchanged. *)
Lemma wrapped_norm_m_agrees : forall w a,
  wrapped_norm_m (Z.ones (Zpos w)) w a = wrapped_norm w a.
Proof.
  intros w [| |lo hi]; cbn [wrapped_norm_m wrapped_norm]; reflexivity.
Qed.

(** Reusing the mask and short-circuiting the full test preserves circular inclusion. *)
Lemma wrapped_leb_m_agrees : forall w a b,
  wrapped_leb_m (Z.ones (Zpos w)) w a b = wrapped_leb w a b.
Proof.
  intros w [| |la ha] [| |lb hb]; cbn [wrapped_leb_m wrapped_leb]; try reflexivity.
  all: rewrite !wrapped_offset_m_agrees, arc_mask_last; reflexivity.
Qed.

(** A short-circuit cover test retains the original pair of inclusion checks. *)
Lemma wrapped_cover_m_agrees : forall w a b candidate,
  wrapped_cover_m (Z.ones (Zpos w)) w a b candidate = wrapped_cover w a b candidate.
Proof.
  intros w a b candidate. unfold wrapped_cover_m, wrapped_cover.
  rewrite !wrapped_leb_m_agrees. reflexivity.
Qed.

(** Prepared-mask selection chooses the same candidate, including cardinality ties. *)
Lemma wrapped_choose_m_agrees : forall w a b first second,
  wrapped_choose_m (Z.ones (Zpos w)) w a b first second =
    wrapped_choose w a b first second.
Proof.
  intros w a b first second. unfold wrapped_choose_m, wrapped_choose.
  rewrite !wrapped_cover_m_agrees, !wrapped_size_m_agrees. reflexivity.
Qed.

(** Prepared-mask joining returns exactly the original circular cover. *)
Lemma wrapped_join_m_agrees : forall w a b,
  wrapped_join_m (Z.ones (Zpos w)) w a b = wrapped_join w a b.
Proof.
  intros w a b. unfold wrapped_join_m, wrapped_join.
  rewrite wrapped_norm_m_agrees, !wrapped_leb_m_agrees.
  destruct a, b; cbn; reflexivity.
Qed.

(** Prepared-mask expansion retains the original tripling of circular cardinality. *)
Lemma wrapped_double_m_agrees : forall w a,
  wrapped_double_m (Z.ones (Zpos w)) w a = wrapped_double w a.
Proof.
  intros w [| |lo hi]; cbn [wrapped_double_m wrapped_double]; try reflexivity.
  rewrite wrapped_size_m_agrees, wrapped_norm_m_agrees, arc_mask_modulus. reflexivity.
Qed.

(** Sharing the first normalization leaves narrowing unchanged. *)
Lemma wrapped_narrow_m_agrees : forall w a b,
  wrapped_narrow_m (Z.ones (Zpos w)) w a b = wrapped_narrow w a b.
Proof.
  intros w a b. unfold wrapped_narrow_m, wrapped_narrow.
  rewrite !wrapped_norm_m_agrees. destruct (wrapped_norm w a); reflexivity.
Qed.

Module WrappedCode (L : WORD_LANGUAGE_OPS) <: WRAPPED_OPS L.
  Definition p := wrapped.
  Definition pleb w a b :=
    match a, b with
    | WBot, _ => true
    | _, WFull => true
    | _, WBot => false
    | _, _ => wrapped_leb_m (Z.ones (Zpos w)) w a b
    end.
  Definition pjoin w a b :=
    match a, b with
    | WBot, WBot => WBot
    | _, WFull => WFull
    | WFull, WBot => WFull
    | _, _ => wrapped_join_m (Z.ones (Zpos w)) w a b
    end.
  Definition pmeet := wrapped_meet.
  Definition pbot (_ : positive) := WBot.
  Definition ptop (_ : positive) := WFull.
  Definition pis_bot (_ : positive) (a : p) := match a with WBot => true | _ => false end.
  Definition pconst w z := wrapped_norm w (WItv z z).
  Definition ppoint := wrapped_point.
  Definition pwparam := unit.
  Definition pwiden (_ : unit) w a b :=
    match a, b with
    | _, WBot => a
    | WFull, _ => WFull
    | WBot, WFull => WFull
    | _, _ =>
      let m := Z.ones (Zpos w) in
      if wrapped_leb_m m w b a then a
      else wrapped_join_m m w (wrapped_double_m m w a) b
    end.
  Definition pnarrow w a b :=
    match a, b with
    | WBot, _ => WBot
    | WFull, WBot => WBot
    | WFull, WFull => WFull
    | _, _ => wrapped_narrow_m (Z.ones (Zpos w)) w a b
    end.
  Definition wrapped_norm := wrapped_norm.
  Definition wrapped_double := wrapped_double.
  Definition wrapped_neg := wrapped_neg.
  Definition wrapped_not := wrapped_not.
  Definition wrapped_add := wrapped_add.
  Definition wrapped_sub := wrapped_sub.
  Definition wrapped_mul := wrapped_mul_fast.
  Definition wrapped_udiv := wrapped_udiv.
  Definition wrapped_urem := wrapped_urem.
  Definition wrapped_split := wrapped_split.
End WrappedCode.

Theorem wrapped_offset_range w c x : 0 <= wrapped_offset w c x < modulus w.
Proof.
  unfold wrapped_offset; rewrite arc_wrap_agrees, wrap_mod.
  apply Z.mod_pos_bound. apply modulus_pos.
Qed.

Theorem wrapped_offset_self w c : wrapped_offset w c c = 0.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_mod. rewrite Z.sub_diag.
  apply Z.mod_0_l. apply modulus_nonzero.
Qed.

Theorem wrapped_offset_wrap w c x :
  wrapped_offset w (wrap w c) (wrap w x) = wrapped_offset w c x.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_agrees. rewrite !wrap_mod. symmetry. apply Zminus_mod.
Qed.

Theorem wrapped_offset_word w c x :
  wrapped_offset w c (wrap w x) = wrapped_offset w c x.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_agrees. rewrite !wrap_mod.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

Theorem wrapped_offset_origin w c x :
  wrapped_offset w (wrap w c) x = wrapped_offset w c x.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_agrees. rewrite !wrap_mod.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

Theorem wrapped_offset_add w c a x :
  wrapped_offset w c x =
  (wrapped_offset w c a + wrapped_offset w a x) mod modulus w.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_mod.
  replace (x - c) with ((a - c) + (x - a)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

Theorem wrapped_offset_sub w c a x :
  wrapped_offset w a x =
  (wrapped_offset w c x - wrapped_offset w c a) mod modulus w.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_mod.
  replace (x - a) with ((x - c) - (a - c)) by ring.
  apply Zminus_mod.
Qed.

Theorem wrapped_offset_step w c k :
  0 <= k < modulus w -> wrapped_offset w c (wrap w (c + k)) = k.
Proof.
  intro Hk. rewrite wrapped_offset_word.
  unfold wrapped_offset; rewrite !arc_wrap_mod. replace (c + k - c) with k by ring.
  apply Z.mod_small. exact Hk.
Qed.

Theorem wrapped_gamma_word w a z : wrapped_gamma w a z -> is_word w z.
Proof.
  destruct a; cbn; tauto.
Qed.

Theorem wrapped_norm_gamma w a z :
  wrapped_gamma w (wrapped_norm w a) z <-> wrapped_gamma w a z.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try tauto.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_gamma].
    try rewrite !arc_wrap_agrees.
    pose proof (wrapped_offset_range w lo z) as Hrange. split; [|tauto].
    intro Hz. split; [exact Hz|lia].
  - cbn [wrapped_gamma].
    try rewrite !arc_wrap_agrees.
    rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

Theorem wrapped_norm_size w a : wrapped_size w (wrapped_norm w a) = wrapped_size w a.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_size]. lia.
  - cbn [wrapped_size]. rewrite !arc_wrap_agrees. now rewrite wrapped_offset_wrap.
Qed.

Theorem wrapped_size_bounds w a : 0 <= wrapped_size w a <= modulus w.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_size];
    pose proof (modulus_pos w); try lia.
  pose proof (wrapped_offset_range w lo hi). lia.
Qed.

Local Lemma wrapped_arc_inclusion w a b c d :
  (forall z, is_word w z -> wrapped_offset w a z <= wrapped_offset w a b ->
    wrapped_offset w c z <= wrapped_offset w c d) <->
  wrapped_offset w c d = modulus w - 1 \/
  wrapped_offset w c a + wrapped_offset w a b <= wrapped_offset w c d.
Proof.
  pose proof (wrapped_offset_range w a b) as Hab.
  pose proof (wrapped_offset_range w c d) as Hcd.
  pose proof (wrapped_offset_range w c a) as Hca.
  split.
  - intro Hincl. destruct (Z.eq_dec (wrapped_offset w c d) (modulus w - 1))
      as [Hfull|Hproper]; [now left|right].
    pose proof (Hincl (wrap w a) (wrap_is_word w a)) as Hstart.
    rewrite wrapped_offset_word, wrapped_offset_self in Hstart.
    specialize (Hstart ltac:(lia)).
    assert (Hsum : wrapped_offset w c a + wrapped_offset w a b < modulus w).
    { destruct (Z_lt_ge_dec (wrapped_offset w c a + wrapped_offset w a b)
        (modulus w)) as [Hlt|Hge]; [exact Hlt|].
      set (k := modulus w - 1 - wrapped_offset w c a).
      assert (Hk : 0 <= k < modulus w) by (unfold k; lia).
      specialize (Hincl (wrap w (a + k)) (wrap_is_word w (a + k))).
      rewrite wrapped_offset_step in Hincl by exact Hk.
      specialize (Hincl ltac:(unfold k; lia)).
      rewrite (wrapped_offset_add w c a), wrapped_offset_step in Hincl by exact Hk.
      replace (wrapped_offset w c a + k) with (modulus w - 1) in Hincl
        by (unfold k; ring).
      rewrite Z.mod_small in Hincl by lia. lia. }
    pose proof (Hincl (wrap w b) (wrap_is_word w b)) as Hend.
    rewrite !wrapped_offset_word in Hend. specialize (Hend ltac:(lia)).
    rewrite (wrapped_offset_add w c a b), Z.mod_small in Hend by lia. exact Hend.
  - intros [Hfull|Hsum] z Hz Haz.
    + pose proof (wrapped_offset_range w c z). lia.
    + pose proof (wrapped_offset_range w a z).
      rewrite (wrapped_offset_add w c a z), Z.mod_small; lia.
Qed.

Theorem wrapped_leb_spec w left right :
  wrapped_leb w left right = true <->
  forall z, wrapped_gamma w left z -> wrapped_gamma w right z.
Proof.
  destruct left as [| |a b], right as [| |c d]; cbn [wrapped_leb wrapped_gamma];
    try (split; [intros; tauto|intros; reflexivity]).
  - split; [discriminate|intro Hempty].
    exfalso. exact (Hempty 0 (zero_is_word w)).
  - rewrite Z.eqb_eq. split.
    + intros Hfull z Hz. split; [exact Hz|].
      pose proof (wrapped_offset_range w c z). lia.
    + intro Hall.
      specialize (Hall (wrap w (c + (modulus w - 1)))
        (wrap_is_word w (c + (modulus w - 1)))).
      destruct Hall as [_ Hlast].
      rewrite wrapped_offset_step in Hlast by (pose proof (modulus_pos w); lia).
      pose proof (wrapped_offset_range w c d). lia.
  - split; [discriminate|intro Hempty].
    exfalso. apply (Hempty (wrap w a)). split; [apply wrap_is_word|].
    rewrite wrapped_offset_word, wrapped_offset_self.
    pose proof (wrapped_offset_range w a b). lia.
  - rewrite Bool.orb_true_iff, Z.eqb_eq, Z.leb_le, <- wrapped_arc_inclusion.
    split.
    + intros Hincl z [Hz Haz]. split; [exact Hz|]. now apply Hincl.
    + intros Hincl z Hz Haz. apply (Hincl z). split; assumption.
Qed.

Theorem wrapped_leb_refl w a : wrapped_leb w a a = true.
Proof.
  apply wrapped_leb_spec. tauto.
Qed.

Theorem wrapped_leb_trans w a b c :
  wrapped_leb w a b = true -> wrapped_leb w b c = true -> wrapped_leb w a c = true.
Proof.
  intros Hab Hbc. apply wrapped_leb_spec.
  pose proof (proj1 (wrapped_leb_spec w a b) Hab) as Hab_gamma.
  pose proof (proj1 (wrapped_leb_spec w b c) Hbc) as Hbc_gamma. auto.
Qed.

Theorem wrapped_norm_leb w a :
  wrapped_leb w a (wrapped_norm w a) = true /\
  wrapped_leb w (wrapped_norm w a) a = true.
Proof.
  split; apply wrapped_leb_spec; intros z Hz.
  - exact (proj2 (wrapped_norm_gamma w a z) Hz).
  - exact (proj1 (wrapped_norm_gamma w a z) Hz).
Qed.

(** Narrowing remains between its contained argument and its previous value. *)
Lemma wrapped_narrow_between w a b : wrapped_leb w b a = true ->
  wrapped_leb w b (wrapped_narrow w a b) = true /\
  wrapped_leb w (wrapped_narrow w a b) a = true.
Proof.
  intro Hcontained.
  destruct (wrapped_norm_leb w a) as [Han Hna].
  destruct (wrapped_norm_leb w b) as [Hbn Hnb].
  unfold wrapped_narrow. destruct (wrapped_norm w a);
    split; eauto using wrapped_leb_trans.
Qed.

Theorem wrapped_size_monotone w left right :
  wrapped_leb w left right = true -> wrapped_size w left <= wrapped_size w right.
Proof.
  intro Hle.
  pose proof (wrapped_size_bounds w left) as Ha.
  pose proof (wrapped_size_bounds w right) as Hb.
  destruct left as [| |a b], right as [| |c d];
    cbn [wrapped_leb wrapped_size] in *; try discriminate;
    try (apply Z.eqb_eq in Hle); try lia.
  apply Bool.orb_true_iff in Hle as [Hfull|Hspan].
  - apply Z.eqb_eq in Hfull. lia.
  - apply Z.leb_le in Hspan. pose proof (wrapped_offset_range w c a). lia.
Qed.

Local Lemma wrapped_choose_cover w a b first second :
  wrapped_cover w a b (wrapped_choose w a b first second) = true.
Proof.
  unfold wrapped_choose.
  destruct (wrapped_cover w a b first) eqn:Hfirst;
    destruct (wrapped_cover w a b second) eqn:Hsecond;
    try (destruct (wrapped_size w first <=? wrapped_size w second)); try assumption.
  all: unfold wrapped_cover; destruct a, b; reflexivity.
Qed.

Theorem wrapped_join_cover w a b : wrapped_cover w a b (wrapped_join w a b) = true.
Proof.
  unfold wrapped_cover. apply Bool.andb_true_iff.
  unfold wrapped_join.
  destruct (wrapped_leb w a b) eqn:Hab.
  - split.
    + eapply wrapped_leb_trans; [exact Hab|apply wrapped_norm_leb].
    + apply wrapped_norm_leb.
  - destruct (wrapped_leb w b a) eqn:Hba.
    + split.
      * apply wrapped_norm_leb.
      * eapply wrapped_leb_trans; [exact Hba|apply wrapped_norm_leb].
    + assert (Hcover : wrapped_cover w a b
        (match a, b with
         | WItv lo hi, WItv lo' hi' =>
           wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
         | _, _ => WFull
         end) = true).
      { destruct a, b; try reflexivity. apply wrapped_choose_cover. }
      apply Bool.andb_true_iff in Hcover as [Hleft Hright].
      split; eapply wrapped_leb_trans; try eassumption; apply wrapped_norm_leb.
Qed.

Theorem wrapped_offset_linear w c a x :
  wrapped_offset w c a + wrapped_offset w a x < modulus w ->
  wrapped_offset w c x = wrapped_offset w c a + wrapped_offset w a x.
Proof.
  intro Hbound. rewrite (wrapped_offset_add w c a x).
  apply Z.mod_small. pose proof (wrapped_offset_range w c a).
  pose proof (wrapped_offset_range w a x). lia.
Qed.

Theorem wrapped_offset_difference w c a x :
  wrapped_offset w c a <= wrapped_offset w c x ->
  wrapped_offset w a x = wrapped_offset w c x - wrapped_offset w c a.
Proof.
  intro Hle. rewrite (wrapped_offset_sub w c a x).
  apply Z.mod_small. pose proof (wrapped_offset_range w c a).
  pose proof (wrapped_offset_range w c x). lia.
Qed.

Local Lemma wrapped_expand_span w lo hi size :
  wrapped_offset w (lo - size) (hi + size) =
  (wrapped_offset w lo hi + 2 * size) mod modulus w.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_mod.
  replace (hi + size - (lo - size)) with ((hi - lo) + 2 * size) by ring.
  symmetry. apply Z.add_mod_idemp_l. apply modulus_nonzero.
Qed.

Local Lemma wrapped_expand_size w lo hi :
  let size := wrapped_size w (WItv lo hi) in
  3 * size < modulus w ->
  wrapped_size w (WItv (lo - size) (hi + size)) = 3 * size.
Proof.
  intros size Hbound. cbn [wrapped_size]. rewrite wrapped_expand_span.
  pose proof (wrapped_offset_range w lo hi). unfold size, wrapped_size in *.
  rewrite Z.mod_small by lia. lia.
Qed.

Theorem wrapped_double_upper w a : wrapped_leb w a (wrapped_double w a) = true.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_double]; try reflexivity.
  set (size := wrapped_size w (WItv lo hi)).
  destruct (modulus w <=? 3 * size) eqn:Hfull; [reflexivity|].
  apply Z.leb_gt in Hfull.
  eapply (wrapped_leb_trans w _ (WItv (lo - size) (hi + size))).
  2: exact (proj1 (wrapped_norm_leb w (WItv (lo - size) (hi + size)))).
  cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le.
  rewrite wrapped_expand_span.
  pose proof (wrapped_offset_range w lo hi) as Hspan.
  assert (Hsize : size = wrapped_offset w lo hi + 1) by reflexivity.
  assert (Hstart : wrapped_offset w (lo - size) lo = size).
  { unfold wrapped_offset; rewrite !arc_wrap_mod. replace (lo - (lo - size)) with size by ring.
    apply Z.mod_small. lia. }
  rewrite Hstart, Z.mod_small by lia. lia.
Qed.

Theorem wrapped_double_size w a :
  wrapped_size w (wrapped_double w a) =
  Z.min (modulus w) (3 * wrapped_size w a).
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_double].
  - cbn [wrapped_size]. pose proof (modulus_pos w). lia.
  - cbn [wrapped_size]. pose proof (modulus_pos w). lia.
  - destruct (modulus w <=? 3 * wrapped_size w (WItv lo hi)) eqn:Hfull.
    + apply Z.leb_le in Hfull. cbn [wrapped_size] in *. lia.
    + apply Z.leb_gt in Hfull. rewrite wrapped_norm_size, wrapped_expand_size by exact Hfull.
      lia.
Qed.

Local Lemma wrapped_choose_size w a b first second target :
  (wrapped_cover w a b first = true /\ wrapped_size w first <= target) \/
  (wrapped_cover w a b second = true /\ wrapped_size w second <= target) ->
  wrapped_size w (wrapped_choose w a b first second) <= target.
Proof.
  intro Hcandidate. unfold wrapped_choose.
  destruct (wrapped_cover w a b first) eqn:Hfirst;
    destruct (wrapped_cover w a b second) eqn:Hsecond;
    try (destruct (wrapped_size w first <=? wrapped_size w second) eqn:Hsize);
    try (apply Z.leb_le in Hsize); try (apply Z.leb_gt in Hsize);
    destruct Hcandidate as [[Hcandidate Hbound]|[Hcandidate Hbound]]; try discriminate; lia.
Qed.

Local Lemma wrapped_candidate_size w a b c d e f :
  wrapped_offset w e a + wrapped_offset w a b <= wrapped_offset w e f ->
  wrapped_offset w e c + wrapped_offset w c d <= wrapped_offset w e f ->
  wrapped_offset w e a <= wrapped_offset w e c ->
  wrapped_offset w e a + wrapped_offset w a b <=
    wrapped_offset w e c + wrapped_offset w c d ->
  wrapped_cover w (WItv a b) (WItv c d) (WItv a d) = true /\
  wrapped_size w (WItv a d) <= wrapped_size w (WItv e f).
Proof.
  intros Hab Hcd Hstart Hend.
  pose proof (wrapped_offset_range w e f) as Hspan.
  pose proof (wrapped_offset_range w e a) as Ha.
  pose proof (wrapped_offset_range w e c) as Hc.
  pose proof (wrapped_offset_range w c d) as Hcd_range.
  assert (Hd : wrapped_offset w e d = wrapped_offset w e c + wrapped_offset w c d).
  { apply wrapped_offset_linear. lia. }
  assert (Had : wrapped_offset w a d =
      wrapped_offset w e c + wrapped_offset w c d - wrapped_offset w e a).
  { rewrite (wrapped_offset_difference w e a d) by lia. lia. }
  assert (Hac : wrapped_offset w a c = wrapped_offset w e c - wrapped_offset w e a).
  { apply wrapped_offset_difference. exact Hstart. }
  split.
  - unfold wrapped_cover. apply Bool.andb_true_iff. split;
      cbn [wrapped_leb]; apply Bool.orb_true_iff; right; apply Z.leb_le.
    + rewrite wrapped_offset_self, Had. lia.
    + rewrite Hac, Had. lia.
  - cbn [wrapped_size]. rewrite Had. lia.
Qed.

Local Lemma wrapped_candidate_exists w a b c d e f :
  wrapped_offset w e f <> modulus w - 1 ->
  wrapped_leb w (WItv a b) (WItv e f) = true ->
  wrapped_leb w (WItv c d) (WItv e f) = true ->
  wrapped_leb w (WItv a b) (WItv c d) = false ->
  wrapped_leb w (WItv c d) (WItv a b) = false ->
  (wrapped_cover w (WItv a b) (WItv c d) (WItv a d) = true /\
   wrapped_size w (WItv a d) <= wrapped_size w (WItv e f)) \/
  (wrapped_cover w (WItv a b) (WItv c d) (WItv c b) = true /\
   wrapped_size w (WItv c b) <= wrapped_size w (WItv e f)).
Proof.
  intros Hproper Hac Hbc Hab Hba.
  cbn [wrapped_leb] in Hac, Hbc.
  destruct (wrapped_offset w e f =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. contradiction.
  - cbn in Hac, Hbc. apply Z.leb_le in Hac, Hbc.
    destruct (Z_le_gt_dec (wrapped_offset w e a) (wrapped_offset w e c))
      as [Hstart|Hstart].
    + left. apply wrapped_candidate_size; try assumption.
      destruct (Z_le_gt_dec (wrapped_offset w e a + wrapped_offset w a b)
        (wrapped_offset w e c + wrapped_offset w c d)) as [Hend|Hend]; [exact Hend|].
      assert (Hca : wrapped_offset w a c = wrapped_offset w e c - wrapped_offset w e a)
        by (apply wrapped_offset_difference; exact Hstart).
      assert (Hcontra : wrapped_leb w (WItv c d) (WItv a b) = true).
      { cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le. lia. }
      congruence.
    + right.
      assert (Hend : wrapped_offset w e c + wrapped_offset w c d <=
          wrapped_offset w e a + wrapped_offset w a b).
      { destruct (Z_le_gt_dec (wrapped_offset w e c + wrapped_offset w c d)
          (wrapped_offset w e a + wrapped_offset w a b)) as [Hend|Hend]; [exact Hend|].
        assert (Hac' : wrapped_offset w c a = wrapped_offset w e a - wrapped_offset w e c)
          by (apply wrapped_offset_difference; lia).
        assert (Hcontra : wrapped_leb w (WItv a b) (WItv c d) = true).
        { cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le. lia. }
        congruence. }
      destruct (wrapped_candidate_size w c d a b e f Hbc Hac ltac:(lia) Hend)
        as [Hcover Hsize]. split; [|exact Hsize].
      unfold wrapped_cover in *. now rewrite Bool.andb_comm.
Qed.

Local Lemma wrapped_join_size w left right target :
  wrapped_leb w left target = true -> wrapped_leb w right target = true ->
  wrapped_size w (wrapped_join w left right) <= wrapped_size w target.
Proof.
  intros Hac Hbc. unfold wrapped_join. rewrite wrapped_norm_size.
  destruct (wrapped_leb w left right) eqn:Hab.
  - now apply wrapped_size_monotone.
  - destruct (wrapped_leb w right left) eqn:Hba.
    + now apply wrapped_size_monotone.
    + destruct left as [| |a b], right as [| |c d];
        cbn [wrapped_leb] in Hab, Hba; try discriminate.
      destruct target as [| |e f].
      * discriminate.
      * apply wrapped_size_bounds.
      * destruct (Z.eq_dec (wrapped_offset w e f) (modulus w - 1)) as [Hfull|Hproper].
        -- pose proof (wrapped_size_bounds w
             (wrapped_choose w (WItv a b) (WItv c d) (WItv a d) (WItv c b))).
           cbn [wrapped_size]. lia.
        -- apply wrapped_choose_size.
           exact (wrapped_candidate_exists w a b c d e f Hproper Hac Hbc Hab Hba).
Qed.

Theorem wrapped_join_minimal w a b c :
  wrapped_leb w a c = true -> wrapped_leb w b c = true ->
  wrapped_size w (wrapped_join w a b) <= wrapped_size w c.
Proof.
  apply wrapped_join_size.
Qed.

Theorem wrapped_range_sound w lo hi z :
  lo <= z <= hi -> wrapped_gamma w (wrapped_range w lo hi) (wrap w z).
Proof.
  intro Hz. unfold wrapped_range.
  destruct (hi <? lo) eqn:Hempty; [apply Z.ltb_lt in Hempty; lia|].
  destruct (modulus w - 1 <=? hi - lo) eqn:Hfull; [apply wrap_is_word|].
  apply Z.leb_gt in Hfull. apply (proj2 (wrapped_norm_gamma w (WItv lo hi) _)).
  split; [apply wrap_is_word|].
  rewrite wrapped_offset_word. unfold wrapped_offset; rewrite !arc_wrap_agrees, !wrap_mod.
  rewrite !Z.mod_small by lia. lia.
Qed.

Theorem wrapped_offset_word_cases w c z :
  is_word w c -> is_word w z ->
  wrapped_offset w c z = if c <=? z then z - c else z - c + modulus w.
Proof.
  intros Hc Hz. unfold wrapped_offset; rewrite !arc_wrap_mod.
  destruct (c <=? z) eqn:Hle.
  - apply Z.leb_le in Hle. apply Z.mod_small. destruct Hc, Hz. lia.
  - apply Z.leb_gt in Hle. symmetry. apply Z.mod_unique with (q := -1);
      destruct Hc, Hz; lia.
Qed.

Theorem wrapped_norm_idempotent w a :
  wrapped_norm w (wrapped_norm w a) = wrapped_norm w a.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull; [reflexivity|].
  cbn [wrapped_norm]. rewrite !arc_wrap_agrees. rewrite wrapped_offset_wrap, Hfull, !wrap_wrap.
    reflexivity.
Qed.

Theorem wrapped_norm_endpoints w a lo hi :
  wrapped_norm w a = WItv lo hi -> is_word w lo /\ is_word w hi.
Proof.
  destruct a as [| |l h]; cbn [wrapped_norm]; try discriminate.
  destruct (wrapped_offset w l h =? modulus w - 1); [discriminate|].
  intro Hnorm. inversion Hnorm; subst lo hi. rewrite !arc_wrap_agrees. split; apply wrap_is_word.
Qed.

Theorem wrapped_parts_normalized w a :
  wrapped_parts w (wrapped_norm w a) = wrapped_parts w a.
Proof.
  unfold wrapped_parts. now rewrite wrapped_norm_idempotent.
Qed.

Theorem wrapped_join_sound w a b z :
  wrapped_gamma w a z \/ wrapped_gamma w b z -> wrapped_gamma w (wrapped_join w a b) z.
Proof.
  pose proof (wrapped_join_cover w a b) as Hcover.
  apply Bool.andb_true_iff in Hcover as [Hleft Hright].
  intros [Ha|Hb].
  - exact (proj1 (wrapped_leb_spec w a _) Hleft z Ha).
  - exact (proj1 (wrapped_leb_spec w b _) Hright z Hb).
Qed.

Theorem wrapped_join_four_sound w a b c d z :
  wrapped_gamma w a z \/ wrapped_gamma w b z \/
  wrapped_gamma w c z \/ wrapped_gamma w d z ->
  wrapped_gamma w (wrapped_join_four w a b c d) z.
Proof.
  intro Hcases. unfold wrapped_join_four.
  apply wrapped_join_sound. destruct Hcases as [Ha|[Hb|[Hc|Hd]]].
  - left. apply wrapped_join_sound. now left.
  - left. apply wrapped_join_sound. now right.
  - right. apply wrapped_join_sound. now left.
  - right. apply wrapped_join_sound. now right.
Qed.

Definition interval_pgamma (w : width) (a : itv) (z : Z) : Prop :=
  is_word w z /\ match a with IBot => False | I lo hi => in_bnd lo hi z end.
Local Lemma wrapped_arc_normalize_gamma w lo hi z :
  wrapped_gamma w (WItv lo hi) z <->
  wrapped_gamma w (WItv (wrap w lo) (wrap w hi)) z.
Proof.
  cbn [wrapped_gamma]. rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

Local Lemma wrapped_parts_raw_spec w a z :
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts_raw w a)) z \/
  interval_pgamma w (snd (wrapped_parts_raw w a)) z.
Proof.
  destruct a as [| |lo hi].
  - change (False <-> (is_word w z /\ False) \/ (is_word w z /\ False)). tauto.
  - change (is_word w z <->
      (is_word w z /\ (0 <= z <= modulus w - 1)) \/ (is_word w z /\ False)).
    split.
    + intro Hz. left. split; [exact Hz|]. unfold is_word in Hz. lia.
    + tauto.
  - cbn [wrapped_parts_raw]. rewrite (arc_wrap_agrees w lo), (arc_wrap_agrees w hi).
    rewrite wrapped_arc_normalize_gamma.
    pose proof (wrap_is_word w lo) as Hlo.
    pose proof (wrap_is_word w hi) as Hhi.
    destruct (wrap w lo <=? wrap w hi) eqn:Hends;
      cbn [fst snd wrapped_gamma interval_pgamma in_bnd]; split.
    + intros [Hz Hoffset]. left. split; [exact Hz|].
      change (wrap w lo <= z <= wrap w hi).
      rewrite !wrapped_offset_word_cases in Hoffset by assumption.
      rewrite Hends in Hoffset. apply Z.leb_le in Hends.
      destruct (wrap w lo <=? z) eqn:Hzlo;
        [apply Z.leb_le in Hzlo|apply Z.leb_gt in Hzlo];
        destruct Hlo, Hhi, Hz; lia.
    + intros [[Hz [Hzlo Hzhi]]|[_ Hempty]]; [|contradiction].
      split; [exact Hz|].
      rewrite !wrapped_offset_word_cases by assumption. rewrite Hends.
      assert (Hlower : (wrap w lo <=? z) = true) by (apply Z.leb_le; exact Hzlo).
      rewrite Hlower. lia.
    + intros [Hz Hoffset].
      rewrite !wrapped_offset_word_cases in Hoffset by assumption. rewrite Hends in Hoffset.
      destruct (wrap w lo <=? z) eqn:Hzlo.
      * apply Z.leb_le in Hzlo. left. split; [exact Hz|].
        change (wrap w lo <= z <= modulus w - 1). destruct Hz. lia.
      * apply Z.leb_gt in Hzlo. right. split; [exact Hz|].
        change (0 <= z <= wrap w hi). destruct Hz. lia.
    + intros [[Hz [Hzlo Hzhi]]|[Hz [Hzlo Hzhi]]]; split; try exact Hz;
        rewrite !wrapped_offset_word_cases by assumption; rewrite Hends;
        destruct (wrap w lo <=? z) eqn:Hzlo';
        try (apply Z.leb_le in Hzlo'); try (apply Z.leb_gt in Hzlo');
        destruct Hlo, Hhi, Hz; apply Z.leb_gt in Hends; lia.
Qed.

Theorem wrapped_parts_spec w a z :
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts w a)) z \/
  interval_pgamma w (snd (wrapped_parts w a)) z.
Proof.
  unfold wrapped_parts. rewrite <- wrapped_parts_raw_spec.
  symmetry. apply wrapped_norm_gamma.
Qed.

Definition interval_meaning (a : itv) (z : Z) : Prop :=
  match a with IBot => False | I lo hi => in_bnd lo hi z end.

Theorem wrapped_of_interval_sound w i z :
  interval_meaning i z -> wrapped_gamma w (wrapped_of_interval w i) (wrap w z).
Proof.
  destruct i as [|lo hi]; intro Hz; [exact Hz|].
  destruct lo as [|lo|], hi as [|hi|]; cbn [wrapped_of_interval];
    try apply wrap_is_word.
  apply wrapped_range_sound. exact Hz.
Qed.
Theorem wrapped_interval_value_sound w i z :
  interval_pgamma w i z -> wrapped_gamma w (wrapped_of_interval w i) z.
Proof.
  intros [Hword Hz]. rewrite <- (wrap_id w z Hword).
  now apply wrapped_of_interval_sound.
Qed.


Module WrappedIntervalSound := IntervalOpsSound ThresholdsT WrappedScalar.

(** Meeting two linear intervals retains each common normalized word. *)
Lemma wrapped_interval_meet_sound w a b z :
  interval_pgamma w a z -> interval_pgamma w b z ->
  interval_pgamma w (WrappedScalar.interval_meet a b) z.
Proof.
  intros Ha Hb. apply WrappedIntervalSound.interval_pgamma_spec.
  apply WrappedIntervalSound.interval_meet_sound;
    apply WrappedIntervalSound.interval_pgamma_spec; assumption.
Qed.

Theorem wrapped_meet_sound w a b z :
  wrapped_gamma w a z -> wrapped_gamma w b z -> wrapped_gamma w (wrapped_meet w a b) z.
Proof.
  intros Ha Hb. unfold wrapped_meet.
  destruct (wrapped_leb w _ a) eqn:Hleft.
  - pose proof (wrapped_gamma_word w a z Ha) as Hz.
    apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hb.
    apply wrapped_join_four_sound.
    destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
    + left. apply wrapped_interval_value_sound. now apply wrapped_interval_meet_sound.
    + right; left. apply wrapped_interval_value_sound. now apply wrapped_interval_meet_sound.
    + right; right; left. apply wrapped_interval_value_sound. now apply wrapped_interval_meet_sound.
    + right; right; right. apply wrapped_interval_value_sound. now apply
      wrapped_interval_meet_sound.
  - exact (proj2 (wrapped_norm_gamma w a z) Ha).
Qed.

Theorem wrapped_meet_lower_left w a b : wrapped_leb w (wrapped_meet w a b) a = true.
Proof.
  unfold wrapped_meet.
  match goal with
  | |- context [if ?test then _ else _] => destruct test eqn:Hleft
  end.
  - exact Hleft.
  - exact (proj2 (wrapped_norm_leb w a)).
Qed.

Theorem wrapped_size_zero w a : wrapped_size w a = 0 <-> a = WBot.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_size].
  - tauto.
  - pose proof (modulus_pos w). split; [lia|discriminate].
  - pose proof (wrapped_offset_range w lo hi). split; [lia|discriminate].
Qed.

Theorem wrapped_full_contains w a b :
  wrapped_size w a = modulus w -> wrapped_leb w b a = true.
Proof.
  intro Hsize. apply wrapped_leb_spec. intros z Hz.
  pose proof (wrapped_gamma_word w b z Hz) as Hword.
  destruct a as [| |lo hi]; cbn [wrapped_size wrapped_gamma] in *.
  - pose proof (modulus_pos w). lia.
  - exact Hword.
  - split; [exact Hword|]. pose proof (wrapped_offset_range w lo z). lia.
Qed.

Local Lemma wrapped_offset_sum w a b x y :
  wrapped_offset w (a + b) (x + y) =
  (wrapped_offset w a x + wrapped_offset w b y) mod modulus w.
Proof.
  unfold wrapped_offset; rewrite !arc_wrap_mod.
  replace (x + y - (a + b)) with ((x - a) + (y - b)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

Theorem wrapped_add_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_add w a b) (wrap w (x + y)).
Proof.
  destruct a as [| |lo hi], b as [| |lo' hi']; intros Hx Hy;
    cbn [wrapped_add] in *; try contradiction; try apply wrap_is_word.
  destruct (modulus w <? wrapped_size w (WItv lo hi) + wrapped_size w (WItv lo' hi'))
    eqn:Hfull; [apply wrap_is_word|].
  apply Z.ltb_ge in Hfull.
  apply (proj2 (wrapped_norm_gamma w (WItv (lo + lo') (hi + hi')) _)).
  destruct Hx as [Hx Hoffsetx], Hy as [Hy Hoffsety].
  split; [apply wrap_is_word|].
  rewrite wrapped_offset_word, !wrapped_offset_sum.
  pose proof (wrapped_offset_range w lo x).
  pose proof (wrapped_offset_range w lo' y).
  cbn [wrapped_size] in Hfull.
  rewrite !Z.mod_small by lia. lia.
Qed.

Local Lemma wrapped_offset_neg w a b :
  wrapped_offset w (- b) (- a) = wrapped_offset w a b.
Proof.
  unfold wrapped_offset. f_equal. ring.
Qed.

Theorem wrapped_neg_sound w a x :
  wrapped_gamma w a x -> wrapped_gamma w (wrapped_neg w a) (wrap w (- x)).
Proof.
  destruct a as [| |lo hi]; intro Hx; cbn [wrapped_neg] in *;
    try contradiction; try apply wrap_is_word.
  apply (proj2 (wrapped_norm_gamma w (WItv (- hi) (- lo)) _)).
  destruct Hx as [Hx Hoffset]. split; [apply wrap_is_word|].
  rewrite wrapped_offset_word, !wrapped_offset_neg.
  rewrite (wrapped_offset_difference w lo x hi) by exact Hoffset.
  pose proof (wrapped_offset_range w lo x). lia.
Qed.

Theorem wrapped_sub_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_sub w a b) (wrap w (x - y)).
Proof.
  intros Hx Hy. unfold wrapped_sub.
  replace (wrap w (x - y)) with (wrap w (x + wrap w (- y))).
  - apply wrapped_add_sound; [exact Hx|now apply wrapped_neg_sound].
  - replace (x - y) with (x + - y) by ring.
    rewrite (wrap_add w x (- y)), (wrap_add w x (wrap w (- y))), wrap_wrap. reflexivity.
Qed.



Theorem wrapped_point_sound w a x z :
  wrapped_gamma w a x -> wrapped_point w a = Some z -> x = z.
Proof.
  intros Ha Hpoint. unfold wrapped_point in Hpoint.
  pose proof (proj2 (wrapped_norm_gamma w a x) Ha) as Hnormal.
  destruct (wrapped_norm w a) as [| |lo hi] eqn:Hnorm; try discriminate.
  pose proof (wrapped_norm_endpoints w a lo hi Hnorm) as [Hlo Hhi].
  destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
  apply Z.eqb_eq in Heq. subst hi. inversion Hpoint; subst z.
  destruct Hnormal as [Hx Hoffset]. rewrite wrapped_offset_self in Hoffset.
  rewrite (wrapped_offset_word_cases w lo x Hlo Hx) in Hoffset.
  destruct (lo <=? x) eqn:Horder;
    [apply Z.leb_le in Horder|apply Z.leb_gt in Horder]; destruct Hlo, Hx; lia.
Qed.


(* The landed bundle statements used lattice, concretisation and widening-rank
   records that are absent from the current signatures. Their operations and
   individual obligations are now exposed through WRAPPED and WORD_PAYLOAD_LAWS.
Theorem wrapped_laws w : lattice_laws (wrapped_lattice w).
Theorem wrapped_gamma_laws w :
  concretisation_laws (wrapped_lattice w) (Concretisation wrapped Z (wrapped_gamma w)).
Theorem wrapped_widening_rank_on w :
  widening_rank_on (wrapped_lattice w) (fun _ => True).
*)

(** Endpoint membership agrees with the reflected scalar order. *)
Local Lemma wrapped_in_bnd_order lo hi z :
  in_bnd lo hi z <->
  WrappedScalar.bound_leb lo (Fin z) = true /\
  WrappedScalar.bound_leb (Fin z) hi = true.
Proof.
  destruct lo as [|lo|], hi as [|hi|]; unfold in_bnd;
    cbn [WrappedScalar.bound_leb]; rewrite ?Z.leb_le; intuition congruence.
Qed.

(** Meeting arbitrary mathematical intervals retains their common integers. *)
Local Lemma wrapped_interval_meet_gamma a b z :
  interval_meaning a z -> interval_meaning b z ->
  interval_meaning (WrappedScalar.interval_meet a b) z.
Proof.
  destruct a as [|la ha], b as [|lb hb]; intros Ha Hb; try contradiction.
  apply wrapped_in_bnd_order in Ha as [Hla Hha].
  apply wrapped_in_bnd_order in Hb as [Hlb Hhb].
  assert (Hlo : WrappedScalar.bound_leb (WrappedScalar.bound_max la lb) (Fin z) = true).
  { apply WrappedIntervalSound.bound_max_least; assumption. }
  assert (Hhi : WrappedScalar.bound_leb (Fin z) (WrappedScalar.bound_min ha hb) = true).
  { apply WrappedIntervalSound.bound_min_greatest; assumption. }
  assert (Hordered : WrappedScalar.bound_leb
      (WrappedScalar.bound_max la lb) (WrappedScalar.bound_min ha hb) = true).
  { eapply WrappedIntervalSound.bound_leb_trans; eassumption. }
  assert (Hnonempty : WrappedScalar.bounds_nonempty
      (WrappedScalar.bound_max la lb) (WrappedScalar.bound_min ha hb) = true).
  { destruct (WrappedScalar.bound_max la lb), (WrappedScalar.bound_min ha hb);
      cbn in *; try discriminate; assumption. }
  unfold WrappedScalar.interval_meet. rewrite Hnonempty.
  apply wrapped_in_bnd_order. split; assumption.
Qed.

Theorem wrapped_mul_cut_sound pole a z :
  interval_meaning a z ->
  interval_meaning (fst (wrapped_mul_cut pole a)) z \/
  interval_meaning (snd (wrapped_mul_cut pole a)) z.
Proof.
  intro Ha. unfold wrapped_mul_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z pole) as [Hlow|Hhigh].
  - left. apply wrapped_interval_meet_gamma; [exact Ha|].
    cbn [interval_meaning in_bnd]. split; [constructor|lia].
  - right. apply wrapped_interval_meet_gamma; [exact Ha|].
    cbn [interval_meaning in_bnd]. split; [lia|constructor].
Qed.

Local Lemma wrapped_product_bounds a b c d x y :
  a <= x <= b -> c <= y <= d ->
  Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d)) <= x * y <=
  Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d)).
Proof.
  intros Hx Hy.
  set (lo := Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d))).
  set (hi := Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d))).
  assert (Hlo : lo <= a * c /\ lo <= a * d /\ lo <= b * c /\ lo <= b * d).
  { unfold lo. repeat split; repeat rewrite Z.min_le_iff; intuition lia. }
  assert (Hhi : a * c <= hi /\ a * d <= hi /\ b * c <= hi /\ b * d <= hi).
  { unfold hi. repeat split; repeat rewrite Z.max_le_iff; intuition lia. }
  destruct Hlo as [Hac [Had [Hbc Hbd]]], Hhi as [Hac' [Had' [Hbc' Hbd']]].
  destruct (Z_le_gt_dec 0 x); destruct (Z_le_gt_dec 0 c); destruct (Z_le_gt_dec 0 d); nia.
Qed.

Theorem wrapped_mul_piece_sound w a b x y :
  interval_meaning a x -> interval_meaning b y ->
  wrapped_gamma w (wrapped_mul_piece w a b) (wrap w (x * y)).
Proof.
  destruct a as [|lo hi], b as [|lo' hi']; intros Hx Hy; cbn [wrapped_mul_piece];
    try contradiction; try apply wrap_is_word.
  destruct lo as [|lo|], hi as [|hi|], lo' as [|lo'|], hi' as [|hi'|];
    cbn [wrapped_mul_piece]; try apply wrap_is_word.
  apply wrapped_range_sound. now apply wrapped_product_bounds.
Qed.

Theorem wrapped_shift_interval_sound delta a z :
  interval_meaning a z -> interval_meaning (wrapped_shift_interval delta a) (z + delta).
Proof.
  destruct a as [|lo hi]; intro Hz; [exact Hz|].
  destruct lo as [|lo|], hi as [|hi|];
    cbn [wrapped_shift_interval interval_meaning] in *;
    unfold in_bnd in *; cbn in *; intuition lia.
Qed.

Local Lemma wrapped_signed_bias w x :
  is_word w x -> signed w x = wrap w (x + half w) - half w.
Proof.
  intro Hx. rewrite signed_value, (wrap_id w x Hx).
  pose proof (modulus_half w) as Hmod.
  pose proof (half_pos w) as Hhalf. destruct Hx as [Hlo Hhi].
  destruct (x <? half w) eqn:Hsign.
  - apply Z.ltb_lt in Hsign. rewrite wrap_id by (split; lia). lia.
  - apply Z.ltb_ge in Hsign.
    assert (Hwrap : wrap w (x + half w) = x + half w - modulus w).
    { rewrite wrap_mod. symmetry. apply Z.mod_unique with (q := 1); lia. }
    rewrite Hwrap. lia.
Qed.

Theorem wrapped_signed_parts_sound w a z :
  wrapped_gamma w a z ->
  interval_meaning (fst (wrapped_signed_parts w a)) (signed w z) \/
  interval_meaning (snd (wrapped_signed_parts w a)) (signed w z).
Proof.
  intro Hz. pose proof (wrapped_gamma_word w a z Hz) as Hword.
  assert (Hhalf : wrapped_gamma w (WItv (half w) (half w)) (half w)).
  { split.
    - split; pose proof (half_pos w); pose proof (modulus_half w); lia.
    - lia. }
  pose proof (wrapped_add_sound w a _ z _ Hz Hhalf) as Hbiased.
  apply wrapped_parts_spec in Hbiased.
  unfold wrapped_signed_parts. cbn [fst snd].
  rewrite (wrapped_signed_bias w z Hword).
  replace (wrap w (z + half w) - half w) with (wrap w (z + half w) + - half w) by ring.
  destruct Hbiased as [[_ Hfirst]|[_ Hsecond]].
  - left. now apply wrapped_shift_interval_sound.
  - right. now apply wrapped_shift_interval_sound.
Qed.

Local Lemma wrapped_mul_parts_sound w a b x y :
  (interval_meaning (fst a) x \/ interval_meaning (snd a) x) ->
  (interval_meaning (fst b) y \/ interval_meaning (snd b) y) ->
  wrapped_gamma w (wrapped_mul_parts w a b) (wrap w (x * y)).
Proof.
  intros Hx Hy. unfold wrapped_mul_parts. apply wrapped_join_four_sound.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - left. now apply wrapped_mul_piece_sound.
  - right; left. now apply wrapped_mul_piece_sound.
  - right; right; left. now apply wrapped_mul_piece_sound.
  - right; right; right. now apply wrapped_mul_piece_sound.
Qed.

Local Lemma wrapped_mul_both_parts_sound w pole a b x y :
  (interval_meaning (fst a) x \/ interval_meaning (snd a) x) ->
  (interval_meaning (fst b) y \/ interval_meaning (snd b) y) ->
  wrapped_gamma w (wrapped_mul_both_parts w pole a b) (wrap w (x * y)).
Proof.
  intros Hx Hy. unfold wrapped_mul_both_parts. apply wrapped_join_four_sound.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; right; left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; right; right. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
Qed.

(** An empty left pair makes every multiplication piece empty. *)
Local Lemma wrapped_mul_both_parts_bottom_left w pole b :
  wrapped_mul_both_parts w pole (IBot, IBot) b = WBot.
Proof.
  reflexivity.
Qed.

(** An empty right interval makes an individual product empty. *)
Local Lemma wrapped_mul_piece_bottom_right w a :
  wrapped_mul_piece w a IBot = WBot.
Proof.
  destruct a as [|[|lo|] [|hi|]]; reflexivity.
Qed.

(** An empty right pair makes all four products empty. *)
Local Lemma wrapped_mul_parts_bottom_right w a :
  wrapped_mul_parts w a (IBot, IBot) = WBot.
Proof.
  unfold wrapped_mul_parts. cbn [fst snd].
  rewrite !wrapped_mul_piece_bottom_right. reflexivity.
Qed.

(** Cutting an empty right pair leaves the complete multiplication pass empty. *)
Local Lemma wrapped_mul_both_parts_bottom_right w pole a :
  wrapped_mul_both_parts w pole a (IBot, IBot) = WBot.
Proof.
  unfold wrapped_mul_both_parts.
  cbn [wrapped_mul_cut WrappedScalar.interval_meet fst snd].
  rewrite !wrapped_mul_parts_bottom_right. reflexivity.
Qed.

(** A bottom operand makes the unsigned multiplication pass bottom. *)
Local Lemma wrapped_mul_unsigned_bottom w a b :
  a = WBot \/ b = WBot ->
  wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) = WBot.
Proof.
  intros [-> | ->].
  - change (wrapped_mul_both_parts w (half w) (IBot, IBot) (wrapped_parts w b) = WBot).
    apply wrapped_mul_both_parts_bottom_left.
  - change (wrapped_mul_both_parts w (half w) (wrapped_parts w a) (IBot, IBot) = WBot).
    apply wrapped_mul_both_parts_bottom_right.
Qed.

(** Every nonbottom arc has a word member, even when its stored endpoints are raw. *)
Local Lemma wrapped_nonempty w a :
  a <> WBot -> exists z, wrapped_gamma w a z.
Proof.
  intro Hnonempty. destruct a as [| |lo hi].
  - contradiction.
  - exists 0. apply zero_is_word.
  - exists (wrap w lo). split; [apply wrap_is_word|].
    rewrite wrapped_offset_word, wrapped_offset_self.
    pose proof (wrapped_offset_range w lo hi). lia.
Qed.

(** An arc that represents a word has positive cardinality. *)
Local Lemma wrapped_gamma_size_pos w a z :
  wrapped_gamma w a z -> 0 < wrapped_size w a.
Proof.
  intro Hmember. destruct a as [| |lo hi].
  - contradiction.
  - apply modulus_pos.
  - cbn [wrapped_size]. pose proof (wrapped_offset_range w lo hi). lia.
Qed.

(** A zero- or one-value unsigned cover is no larger than the signed cover. *)
Local Lemma wrapped_mul_small_unsigned w a b :
  let unsigned :=
    wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) in
  let signed :=
    wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b) in
  wrapped_size w unsigned <= 1 -> wrapped_size w unsigned <= wrapped_size w signed.
Proof.
  cbn beta iota zeta.
  set (u := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b)).
  set (v := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b)).
  intro Hsmall. pose proof (wrapped_size_bounds w v) as Hv.
  destruct (Z.eq_dec (wrapped_size w u) 0) as [Hzero|Hnonzero].
  - lia.
  - assert (Ha : a <> WBot).
    { intro Hbottom.
      assert (Hempty : u = WBot).
      { unfold u. apply wrapped_mul_unsigned_bottom. now left. }
      apply Hnonzero. rewrite Hempty. reflexivity. }
    assert (Hb : b <> WBot).
    { intro Hbottom.
      assert (Hempty : u = WBot).
      { unfold u. apply wrapped_mul_unsigned_bottom. now right. }
      apply Hnonzero. rewrite Hempty. reflexivity. }
    destruct (wrapped_nonempty w a Ha) as [x Hx].
    destruct (wrapped_nonempty w b Hb) as [y Hy].
    pose proof (wrapped_mul_both_parts_sound w 0
      (wrapped_signed_parts w a) (wrapped_signed_parts w b) (signed w x) (signed w y)
      (wrapped_signed_parts_sound w a x Hx) (wrapped_signed_parts_sound w b y Hy)) as Hmember.
    fold v in Hmember. pose proof (wrapped_gamma_size_pos w v _ Hmember) as Hpositive.
    lia.
Qed.

(** Skipping the signed pass on a smallest cover preserves the original result exactly. *)
Lemma wrapped_mul_fast_agrees : forall w a b,
  wrapped_mul_fast w a b = wrapped_mul w a b.
Proof.
  intros w a b. unfold wrapped_mul_fast, wrapped_mul. cbn beta iota zeta.
  set (u := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b)).
  set (v := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b)).
  destruct (wrapped_size w u <=? 1) eqn:Hsmall; [|reflexivity].
  apply Z.leb_le in Hsmall.
  pose proof (wrapped_mul_small_unsigned w a b Hsmall) as Horder.
  assert (Htest : (wrapped_size w u <=? wrapped_size w v) = true).
  { apply Z.leb_le. exact Horder. }
  now rewrite Htest.
Qed.

Theorem wrapped_mul_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_mul w a b) (wmul w x y).
Proof.
  intros Hx Hy. unfold wrapped_mul.
  destruct (wrapped_size w _ <=? wrapped_size w _) eqn:Hsize.
  - rewrite wmul_value. apply wrapped_mul_both_parts_sound.
    + apply wrapped_parts_spec in Hx. unfold interval_pgamma in Hx. tauto.
    + apply wrapped_parts_spec in Hy. unfold interval_pgamma in Hy. tauto.
  - rewrite wmul_signed. apply wrapped_mul_both_parts_sound;
      now apply wrapped_signed_parts_sound.
Qed.

Local Lemma wrapped_size_rank_bounds w size :
  0 <= size <= modulus w -> 0 <= wrapped_size_rank w size <= Zpos w + 2.
Proof.
  intro Hsize. unfold wrapped_size_rank.
  destruct (size =? 0) eqn:Hzero; [lia|].
  destruct (size =? modulus w) eqn:Hfull; [lia|].
  pose proof (Z.log2_nonneg size) as Hnonneg.
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)) as Hlog.
  rewrite modulus_log2 in Hlog. lia.
Qed.

Local Lemma wrapped_size_rank_positive w size :
  0 <= size < modulus w -> 0 < wrapped_size_rank w size.
Proof.
  intro Hsize. unfold wrapped_size_rank.
  destruct (size =? 0) eqn:Hzero; [lia|].
  destruct (size =? modulus w) eqn:Hfull; [apply Z.eqb_eq in Hfull; lia|].
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)) as Hlog.
  rewrite modulus_log2 in Hlog. lia.
Qed.

Local Lemma wrapped_size_rank_progress w old next :
  0 <= old < modulus w -> 0 < next <= modulus w ->
  Z.min (modulus w) (3 * old) <= next ->
  wrapped_size_rank w next < wrapped_size_rank w old.
Proof.
  intros Hold Hnext Hgrow.
  pose proof (wrapped_size_rank_positive w old Hold) as Hpositive.
  unfold wrapped_size_rank.
  destruct (next =? 0) eqn:Hnext_zero; [apply Z.eqb_eq in Hnext_zero; lia|].
  destruct (next =? modulus w) eqn:Hnext_full.
  - unfold wrapped_size_rank in Hpositive. exact Hpositive.
  - apply Z.eqb_neq in Hnext_full.
    destruct (old =? 0) eqn:Hold_zero.
    + pose proof (Z.log2_nonneg next). lia.
    + apply Z.eqb_neq in Hold_zero.
      destruct (old =? modulus w) eqn:Hold_full; [apply Z.eqb_eq in Hold_full; lia|].
      assert (Hdouble : 2 * old <= next) by lia.
      pose proof (Z.log2_le_mono (2 * old) next Hdouble) as Hlog.
      rewrite Z.log2_double in Hlog by lia. lia.
Qed.

Local Lemma wrapped_widen_size_progress w a b :
  wrapped_leb w b a = false ->
  0 < wrapped_size w (wrapped_widen w a b) <= modulus w /\
  Z.min (modulus w) (3 * wrapped_size w a) <= wrapped_size w (wrapped_widen w a b).
Proof.
  intro Hescape. unfold wrapped_widen. rewrite Hescape.
  pose proof (wrapped_join_cover w (wrapped_double w a) b) as Hcover.
  apply Bool.andb_true_iff in Hcover as [Hleft Hright].
  pose proof (wrapped_size_monotone w _ _ Hleft) as Hsize.
  rewrite wrapped_double_size in Hsize.
  pose proof (wrapped_size_bounds w (wrapped_join w (wrapped_double w a) b)) as Hbounds.
  split; [split; [|lia]|exact Hsize].
  destruct (Z.eq_dec (wrapped_size w (wrapped_join w (wrapped_double w a) b)) 0)
    as [Hzero|Hnonzero]; [|lia].
  apply wrapped_size_zero in Hzero. rewrite Hzero in Hright.
  destruct b; cbn [wrapped_leb] in Hright; try discriminate.
Qed.


(** Normalization stores at most two width-bounded endpoints. *)
Local Lemma wrapped_norm_bits w a :
  (wrapped_bits (wrapped_norm w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  destruct (wrapped_norm w a) as [| |lo hi] eqn:Hnorm; cbn [wrapped_bits]; try lia.
  destruct (wrapped_norm_endpoints w a lo hi Hnorm) as [Hlo Hhi].
  pose proof (WordTime.word_size_bound w lo Hlo).
  pose proof (WordTime.word_size_bound w hi Hhi). lia.
Qed.

(** Joining always normalizes the selected circular cover. *)
Local Lemma wrapped_join_bits w a b :
  (wrapped_bits (wrapped_join w a b) <= 2 * Pos.to_nat w)%nat.
Proof. unfold wrapped_join. apply wrapped_norm_bits. Qed.

(** Addition either normalizes its arc or returns a constructor without endpoints. *)
Local Lemma wrapped_add_bits w a b :
  (wrapped_bits (wrapped_add w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  destruct a as [| |lo hi], b as [| |lo' hi']; cbn [wrapped_add wrapped_bits]; try lia.
  destruct (modulus w <? wrapped_size w (WItv lo hi) + wrapped_size w (WItv lo' hi'));
    [cbn [wrapped_bits]; lia|apply wrapped_norm_bits].
Qed.

(** Negation normalizes every stored endpoint. *)
Local Lemma wrapped_neg_bits w a :
  (wrapped_bits (wrapped_neg w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_neg wrapped_bits]; try lia.
  apply wrapped_norm_bits.
Qed.

(** Both signed and unsigned multiplication covers end in a normalized join. *)
Local Lemma wrapped_mul_bits w a b :
  (wrapped_bits (wrapped_mul w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  unfold wrapped_mul.
  destruct (wrapped_size w (wrapped_mul_both_parts w (half w)
    (wrapped_parts w a) (wrapped_parts w b)) <=?
    wrapped_size w (wrapped_mul_both_parts w 0
      (wrapped_signed_parts w a) (wrapped_signed_parts w b)));
    unfold wrapped_mul_both_parts, wrapped_join_four; apply wrapped_join_bits.
Qed.

(** Finite clipping yields bottom or ordered endpoints within the clipping interval. *)
Local Lemma wrapped_finite_meet_shape a lo hi :
  WrappedScalar.interval_meet a (I (Fin lo) (Fin hi)) = IBot \/
  exists l h, WrappedScalar.interval_meet a (I (Fin lo) (Fin hi)) = I (Fin l) (Fin h) /\
    lo <= l /\ l <= h /\ h <= hi.
Proof.
  destruct a as [|lower upper]; [left; reflexivity|].
  unfold WrappedScalar.interval_meet.
  remember (WrappedScalar.bound_max lower (Fin lo)) as lbound eqn:Hlower.
  remember (WrappedScalar.bound_min upper (Fin hi)) as hbound eqn:Hupper.
  destruct (WrappedScalar.bounds_nonempty lbound hbound) eqn:Hnonempty;
    [right|left; reflexivity].
  assert (Hlo : WrappedScalar.bound_leb (Fin lo) lbound = true).
  { subst lbound. apply WrappedIntervalSound.bound_max_upper_r. }
  assert (Hhi : WrappedScalar.bound_leb hbound (Fin hi) = true).
  { subst hbound. apply WrappedIntervalSound.bound_min_lower_r. }
  destruct lbound as [|l|], hbound as [|h|];
    cbn [WrappedScalar.bound_leb WrappedScalar.bounds_nonempty] in Hlo, Hhi, Hnonempty;
    try discriminate.
  exists l, h. split; [reflexivity|].
  apply Z.leb_le in Hlo, Hhi, Hnonempty. lia.
Qed.

(** Split pieces have finite word endpoints whenever they are nonempty. *)
Definition wrapped_interval_word_shape w a : Prop :=
  a = IBot \/ exists lo hi, a = I (Fin lo) (Fin hi) /\ is_word w lo /\ is_word w hi.

Local Lemma wrapped_finite_meet_word_shape w a lo hi :
  is_word w lo -> is_word w hi ->
  wrapped_interval_word_shape w (WrappedScalar.interval_meet a (I (Fin lo) (Fin hi))).
Proof.
  intros Hlo Hhi. destruct (wrapped_finite_meet_shape a lo hi) as [Hbot|[l [h [Hshape Hrange]]]].
  - now left.
  - right. exists l, h. split; [exact Hshape|]. unfold is_word in *. lia.
Qed.

(** Pole clipping keeps both pieces inside the unsigned word range. *)
Local Lemma wrapped_pole_cut_word_shape w a :
  wrapped_interval_word_shape w (fst (wrapped_pole_cut w a)) /\
  wrapped_interval_word_shape w (snd (wrapped_pole_cut w a)).
Proof.
  pose proof (half_pos w). pose proof (modulus_half w).
  unfold wrapped_pole_cut. cbn [fst snd]. split; apply wrapped_finite_meet_word_shape;
    unfold is_word; lia.
Qed.

(** Cutting at the signed pole covers every represented word in the input interval. *)
Local Lemma wrapped_pole_cut_gamma w a z :
  interval_pgamma w a z -> interval_pgamma w (fst (wrapped_pole_cut w a)) z \/
    interval_pgamma w (snd (wrapped_pole_cut w a)) z.
Proof.
  intro Ha. pose proof (proj1 Ha) as Hword.
  unfold wrapped_pole_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z (half w)) as [Hlow|Hhigh].
  - left. apply wrapped_interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. change (0 <= z <= half w - 1). destruct Hword. lia.
  - right. apply wrapped_interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. change (half w <= z <= modulus w - 1). destruct Hword. lia.
Qed.

(** A single finite interval contributes at most one split piece. *)
Local Lemma wrapped_interval_list_length a : (length (wrapped_interval_list a) <= 1)%nat.
Proof. destruct a as [|[|lo|] [|hi|]]; cbn [wrapped_interval_list length]; lia. Qed.

(** The four pole projections contribute at most four ordinary intervals. *)
Local Lemma wrapped_split_length w a : (length (wrapped_split w a) <= 4)%nat.
Proof.
  unfold wrapped_split. rewrite !length_app.
  replace 4%nat with (1 + (1 + (1 + 1)))%nat by reflexivity.
  repeat apply Nat.add_le_mono; apply wrapped_interval_list_length.
Qed.

(** A represented value in a finite split piece lies between its listed endpoints. *)
Local Lemma wrapped_interval_list_cover w a z :
  wrapped_interval_word_shape w a -> interval_pgamma w a z ->
  exists lo hi, In (lo, hi) (wrapped_interval_list a) /\ lo <= z <= hi.
Proof.
  intros [->|[lo [hi [-> Hends]]]] Ha; [exact (False_rect _ (proj2 Ha))|].
  exists lo, hi. split; [left; reflexivity|exact (proj2 Ha)].
Qed.

(** The two pole pieces cover the concrete interval before list concatenation. *)
Local Lemma wrapped_cut_list_cover w a z : interval_pgamma w a z ->
  exists lo hi, In (lo, hi) (wrapped_interval_list (fst (wrapped_pole_cut w a)) ++
    wrapped_interval_list (snd (wrapped_pole_cut w a))) /\ lo <= z <= hi.
Proof.
  intro Ha. destruct (wrapped_pole_cut_word_shape w a) as [Hleft Hright].
  destruct (wrapped_pole_cut_gamma w a z Ha) as [Hgamma|Hgamma].
  - destruct (wrapped_interval_list_cover w _ z Hleft Hgamma) as [lo [hi [Hin Hrange]]].
    exists lo, hi. split; [apply in_or_app; now left|exact Hrange].
  - destruct (wrapped_interval_list_cover w _ z Hright Hgamma) as [lo [hi [Hin Hrange]]].
    exists lo, hi. split; [apply in_or_app; now right|exact Hrange].
Qed.

(** Splitting at zero and at the signed pole covers every circular arc member. *)
Local Lemma wrapped_split_cover w a z : wrapped_gamma w a z ->
  exists lo hi, In (lo, hi) (wrapped_split w a) /\ lo <= z <= hi.
Proof.
  intro Ha. apply wrapped_parts_spec in Ha. unfold wrapped_split.
  destruct Ha as [Ha|Ha];
    destruct (wrapped_cut_list_cover w _ z Ha) as [lo [hi [Hin Hrange]]];
    exists lo, hi; split; try exact Hrange;
    rewrite !in_app_iff in *; tauto.
Qed.

(** Listed endpoints of a bounded split piece fit the declared width. *)
Local Lemma wrapped_interval_list_bits w a lo hi :
  wrapped_interval_word_shape w a -> In (lo, hi) (wrapped_interval_list a) ->
  (Z.size_nat lo + Z.size_nat hi <= 2 * Pos.to_nat w)%nat.
Proof.
  intros [->|[l [h [-> [Hl Hh]]]]] Hin; [contradiction|].
  destruct Hin as [Heq|Hempty]; [inversion Heq; subst l h|contradiction].
  pose proof (WordTime.word_size_bound w lo Hl).
  pose proof (WordTime.word_size_bound w hi Hh). lia.
Qed.

(** Every piece produced by splitting has two width-bounded endpoints. *)
Local Lemma wrapped_split_bits_bound w a lo hi : In (lo, hi) (wrapped_split w a) ->
  (Z.size_nat lo + Z.size_nat hi <= 2 * Pos.to_nat w)%nat.
Proof.
  intro Hin. unfold wrapped_split in Hin. rewrite !in_app_iff in Hin.
  destruct (wrapped_pole_cut_word_shape w (fst (wrapped_parts w a))) as [Hfirst Hsecond].
  destruct (wrapped_pole_cut_word_shape w (snd (wrapped_parts w a))) as [Hthird Hfourth].
  destruct Hin as [Hin|[Hin|[Hin|Hin]]].
  - exact (wrapped_interval_list_bits w _ lo hi Hfirst Hin).
  - exact (wrapped_interval_list_bits w _ lo hi Hsecond Hin).
  - exact (wrapped_interval_list_bits w _ lo hi Hthird Hin).
  - exact (wrapped_interval_list_bits w _ lo hi Hfourth Hin).
Qed.

(** An all-ones mask fits the word width used to construct it. *)
Lemma arc_ones_word : forall w, is_word w (Z.ones (Zpos w)).
Proof.
  intro w. unfold is_word, modulus. rewrite Z.ones_equiv.
  pose proof (modulus_pos w). unfold modulus in *. lia.
Qed.

(** Constructing the mask performs linearly many bit operations. *)
Lemma arc_ones_time : forall w,
  (Word.Z.T_ones (Zpos w) <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w.
  pose proof (Std.Z.T_shiftl_le 1 (Zpos w)) as Hshift.
  pose proof (Std.Z.T_pred_le (Z.shiftl 1 (Zpos w))) as Hpred.
  assert (Hbits : (Z.size_nat (Z.shiftl 1 (Zpos w)) <= Pos.to_nat w + 1)%nat).
  { rewrite Z.shiftl_1_l. apply WordTime.word_modulus_size_bound. }
  change (Std.Z.T_shiftl 1 (Zpos w) <= 6 * N.pos w + 1)%N in Hshift.
  time_unfold Word.Z.T_ones. rewrite Nat2N.inj_add, positive_nat_N. nia.
Qed.

(** Masked normalization charges width and the raw integer's magnitude bits. *)
Lemma arc_wrap_time : forall w z,
  (T_arc_wrap w z <= 32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z.
  pose proof (arc_ones_time w) as Hones.
  pose proof (WordTime.word_size_bound w _ (arc_ones_word w)) as Hbits.
  pose proof (Std.Z.T_land_le z (Z.ones (Zpos w))) as Hland.
  time_unfold T_arc_wrap. time_cbn.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound arc_wrap_time.

(** Circular offsets are normalized words independently of their raw endpoints. *)
Lemma wrapped_offset_bits : forall w origin x,
  (Z.size_nat (wrapped_offset w origin x) <= Pos.to_nat w)%nat.
Proof.
  intros w origin x. unfold wrapped_offset. rewrite arc_wrap_agrees.
  apply WordTime.word_wrap_size_bound.
Qed.

(** Computing an offset charges subtraction followed by a linear mask. *)
Lemma wrapped_offset_time : forall w origin x,
  (T_wrapped_offset w origin x <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat origin + Z.size_nat x + 1))%N.
Proof.
  intros w origin x.
  pose proof (arc_wrap_time w (x - origin)) as Hwrap.
  pose proof (Std.Z.T_sub_le x origin) as Hsub.
  pose proof (WordTime.integer_sub_size x origin) as Hbits.
  time_unfold T_wrapped_offset. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound wrapped_offset_time.

(** Arc cardinality needs at most one more bit than a represented word. *)
Lemma wrapped_size_bits : forall w a,
  (Z.size_nat (wrapped_size w a) <= Pos.to_nat w + 1)%nat.
Proof.
  intros w a. pose proof (wrapped_size_bounds w a) as Hrange.
  apply WordTime.integer_size_bound. split; [lia|].
  eapply Z.le_lt_trans; [exact (proj2 Hrange)|].
  unfold modulus. rewrite Nat2Z.inj_add, positive_nat_Z.
  apply Z.pow_lt_mono_r; lia.
Qed.

(** Computing cardinality charges only width and the stored endpoints. *)
Lemma wrapped_size_time : forall w a,
  (T_wrapped_size w a <=
    256 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi].
  - time_unfold T_wrapped_size. cbn [wrapped_bits]. rewrite Nat2N.inj_add. nia.
  - pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
    time_unfold T_wrapped_size. cbn [wrapped_bits]. rewrite !Nat2N.inj_add in *. nia.
  - pose proof (wrapped_offset_time w lo hi) as Hoffset.
    pose proof (wrapped_offset_bits w lo hi) as Hbits.
    pose proof (Std.Z.T_add_le (wrapped_offset w lo hi) 1) as Hadd.
    time_unfold T_wrapped_size. cbn [wrapped_bits]. rewrite !Nat2N.inj_add in *.
    time_cbn_all. nia.
Qed.
TimeBound wrapped_size_time.

(** The largest word has no more bits than the declared width. *)
Lemma wrapped_last_word_bits : forall w,
  (Z.size_nat (modulus w - 1) <= Pos.to_nat w)%nat.
Proof.
  intro w. apply WordTime.word_size_bound. unfold is_word.
  pose proof (modulus_pos w). lia.
Qed.

(** Arc normalization charges two endpoint masks and a cardinality comparison. *)
Lemma wrapped_norm_time : forall w a,
  (T_wrapped_norm w a <=
    512 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi].
  - time_unfold T_wrapped_norm. cbn [wrapped_bits]. rewrite Nat2N.inj_add. nia.
  - time_unfold T_wrapped_norm. cbn [wrapped_bits]. rewrite Nat2N.inj_add. nia.
  - pose proof (wrapped_offset_time w lo hi) as Hoffset.
    pose proof (wrapped_offset_bits w lo hi) as Hoffsetbits.
    pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
    pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
    pose proof (wrapped_last_word_bits w) as Hlastbits.
    pose proof (Std.Z.T_sub_le (modulus w) 1) as Hsub.
    pose proof (Std.Z.T_eqb_le (wrapped_offset w lo hi) (modulus w - 1)) as Hequal.
    pose proof (arc_wrap_time w lo) as Hlo.
    pose proof (arc_wrap_time w hi) as Hhi.
    time_unfold T_wrapped_norm. cbn [wrapped_bits].
    destruct (wrapped_offset w lo hi =? modulus w - 1);
      rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
Qed.
TimeBound wrapped_norm_time.

(** Converting a finite interval charges its endpoints and the output width. *)
Lemma wrapped_range_time : forall w lo hi,
  (T_wrapped_range w lo hi <=
    1024 * N.of_nat (Pos.to_nat w + Z.size_nat lo + Z.size_nat hi + 1))%N.
Proof.
  intros w lo hi.
  pose proof (Std.Z.T_ltb_le hi lo) as Hempty.
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  pose proof (wrapped_last_word_bits w) as Hlastbits.
  pose proof (Std.Z.T_sub_le (modulus w) 1) as Hlast.
  pose proof (Std.Z.T_sub_le hi lo) as Hdifference.
  pose proof (Std.Z.T_leb_le (modulus w - 1) (hi - lo)) as Hfull.
  pose proof (wrapped_norm_time w (WItv lo hi)) as Hnorm.
  time_unfold T_wrapped_range. cbn [wrapped_bits] in Hnorm.
  destruct (hi <? lo), (modulus w - 1 <=? hi - lo);
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
Qed.
TimeBound wrapped_range_time.

(** Endpoint minimum selects one of the stored magnitudes. *)
Lemma wrapped_min_bits : forall x y,
  (Z.size_nat (Z.min x y) <= Z.size_nat x + Z.size_nat y)%nat.
Proof.
  intros x y. destruct (Z_le_dec x y) as [Hle|Hlt].
  - rewrite Z.min_l by exact Hle. lia.
  - rewrite Z.min_r by lia. lia.
Qed.

(** Endpoint maximum selects one of the stored magnitudes. *)
Lemma wrapped_max_bits : forall x y,
  (Z.size_nat (Z.max x y) <= Z.size_nat x + Z.size_nat y)%nat.
Proof.
  intros x y. destruct (Z_le_dec x y) as [Hle|Hlt].
  - rewrite Z.max_r by exact Hle. lia.
  - rewrite Z.max_l by lia. lia.
Qed.

(** A shared endpoint budget bounds one integer multiplication quadratically. *)
Lemma wrapped_product_time_budget : forall x y n,
  (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
  (Std.Z.T_mul x y <= 8 * N.of_nat (n ^ 2))%N.
Proof.
  intros x y n Hsize. pose proof (Std.Z.T_mul_le x y) as Hmul.
  apply time_of_nat_le in Hsize. cbn [Nat.pow].
  rewrite !Nat2N.inj_add in Hsize. rewrite !Nat2N.inj_mul. nia.
Qed.

(** A finite multiplication piece performs a fixed number of quadratic products. *)
Lemma wrapped_mul_piece_finite_time : forall w lo hi lo' hi',
  (T_wrapped_mul_piece w (I (Fin lo) (Fin hi)) (I (Fin lo') (Fin hi')) <=
    32768 * N.of_nat
      ((Pos.to_nat w + Z.size_nat lo + Z.size_nat hi + Z.size_nat lo' + Z.size_nat hi' + 1)
        ^ 2))%N.
Proof.
  intros w lo hi lo' hi'.
  set (n := (Pos.to_nat w + Z.size_nat lo + Z.size_nat hi +
    Z.size_nat lo' + Z.size_nat hi' + 1)%nat).
  pose proof (WordTime.integer_mul_size lo lo') as Hll.
  pose proof (WordTime.integer_mul_size lo hi') as Hlh.
  pose proof (WordTime.integer_mul_size hi lo') as Hhl.
  pose proof (WordTime.integer_mul_size hi hi') as Hhh.
  pose proof (wrapped_min_bits (lo * lo') (lo * hi')) as Hminl.
  pose proof (wrapped_min_bits (hi * lo') (hi * hi')) as Hminh.
  pose proof (wrapped_min_bits (Z.min (lo * lo') (lo * hi'))
    (Z.min (hi * lo') (hi * hi'))) as Hmin.
  pose proof (wrapped_max_bits (lo * lo') (lo * hi')) as Hmaxl.
  pose proof (wrapped_max_bits (hi * lo') (hi * hi')) as Hmaxh.
  pose proof (wrapped_max_bits (Z.max (lo * lo') (lo * hi'))
    (Z.max (hi * lo') (hi * hi'))) as Hmax.
  pose proof (wrapped_product_time_budget lo lo' n ltac:(unfold n; lia)) as HTll.
  pose proof (wrapped_product_time_budget lo hi' n ltac:(unfold n; lia)) as HTlh.
  pose proof (wrapped_product_time_budget hi lo' n ltac:(unfold n; lia)) as HThl.
  pose proof (wrapped_product_time_budget hi hi' n ltac:(unfold n; lia)) as HThh.
  pose proof (wrapped_range_time w
    (Z.min (Z.min (lo * lo') (lo * hi')) (Z.min (hi * lo') (hi * hi')))
    (Z.max (Z.max (lo * lo') (lo * hi')) (Z.max (hi * lo') (hi * hi')))) as Hrange.
  assert (Hrangebits : (Pos.to_nat w +
    Z.size_nat (Z.min (Z.min (lo * lo') (lo * hi')) (Z.min (hi * lo') (hi * hi'))) +
    Z.size_nat (Z.max (Z.max (lo * lo') (lo * hi')) (Z.max (hi * lo') (hi * hi'))) + 1
    <= 5 * n)%nat) by (unfold n; lia).
  assert (Hrangebudget : (T_wrapped_range w
    (Z.min (Z.min (lo * lo') (lo * hi')) (Z.min (hi * lo') (hi * hi')))
    (Z.max (Z.max (lo * lo') (lo * hi')) (Z.max (hi * lo') (hi * hi'))) <=
    5120 * N.of_nat n)%N).
  { apply time_of_nat_le in Hrangebits. rewrite Nat2N.inj_mul in Hrangebits. nia. }
  assert (Hleftbits : (Z.size_nat (lo * lo') <= n)%nat) by (unfold n; lia).
  assert (Hrightbits : (Z.size_nat (hi * lo') <= n)%nat) by (unfold n; lia).
  assert (Hminimum : (Z.size_nat (Z.min (lo * lo') (lo * hi')) <= 2 * n)%nat)
    by (unfold n; lia).
  assert (Hmaximum : (Z.size_nat (Z.max (lo * lo') (lo * hi')) <= 2 * n)%nat)
    by (unfold n; lia).
  assert (Hnatpositive : (1 <= n)%nat) by (unfold n; lia).
  pose proof (time_of_nat_le 1 n ltac:(unfold n; lia)) as Hpositive.
  clear Hll Hlh Hhl Hhh Hminl Hminh Hmin Hmaxl Hmaxh Hmax Hrange Hrangebits.
  clearbody n.
  set (square := N.of_nat (n ^ 2)) in *.
  assert (Hlinear : (N.of_nat n <= square)%N).
  { unfold square. clear - Hnatpositive. apply time_of_nat_le. cbn [Nat.pow]. nia. }
  clearbody square.
  apply time_of_nat_le in Hleftbits, Hrightbits, Hminimum, Hmaximum.
  rewrite Nat2N.inj_mul in Hminimum, Hmaximum.
  pose proof (Std.Z.T_min_le (lo * lo') (lo * hi')) as HTminl.
  pose proof (Std.Z.T_min_le (hi * lo') (hi * hi')) as HTminh.
  pose proof (Std.Z.T_min_le (Z.min (lo * lo') (lo * hi'))
    (Z.min (hi * lo') (hi * hi'))) as HTmin.
  pose proof (Std.Z.T_max_le (lo * lo') (lo * hi')) as HTmaxl.
  pose proof (Std.Z.T_max_le (hi * lo') (hi * hi')) as HTmaxh.
  pose proof (Std.Z.T_max_le (Z.max (lo * lo') (lo * hi'))
    (Z.max (hi * lo') (hi * hi'))) as HTmax.
  time_unfold T_wrapped_mul_piece. time_cbn.
  lia.
Qed.

(** Circular inclusion uses a fixed number of linear offset computations. *)
Lemma wrapped_leb_time : forall w a b,
  (T_wrapped_leb w a b <=
    1024 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intro w.
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  intros [| |la ha] [| |lb hb]; time_unfold T_wrapped_leb; cbn [wrapped_bits].
  all: try (rewrite !Nat2N.inj_add in *; time_cbn_all; lia).
  - pose proof (wrapped_offset_bits w lb hb) as Hbits.
    time_pose. rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  - pose proof (wrapped_offset_bits w lb hb) as Hcoverbits.
    pose proof (wrapped_offset_bits w lb la) as Hstartbits.
    pose proof (wrapped_offset_bits w la ha) as Hlengthbits.
    pose proof (WordTime.integer_add_size (wrapped_offset w lb la)
      (wrapped_offset w la ha)) as Hsumbits.
    time_pose. rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
Qed.
TimeBound wrapped_leb_time.

(** Checking a cover charges the two circular inclusion queries. *)
Lemma wrapped_cover_time : forall w a b candidate,
  (T_wrapped_cover w a b candidate <= 4096 * N.of_nat
    (Pos.to_nat w + wrapped_bits a + wrapped_bits b + wrapped_bits candidate + 1))%N.
Proof.
  intros w a b candidate. time_unfold T_wrapped_cover. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_cover_time.

(** Cover selection returns one of the candidates or full. *)
Lemma wrapped_choose_bits : forall w a b first second,
  (wrapped_bits (wrapped_choose w a b first second) <=
    wrapped_bits first + wrapped_bits second)%nat.
Proof.
  intros w a b first second. unfold wrapped_choose.
  destruct (wrapped_cover w a b first), (wrapped_cover w a b second),
    (wrapped_size w first <=? wrapped_size w second); cbn [wrapped_bits]; lia.
Qed.

(** Selecting a circular cover charges both candidates and the two inputs. *)
Lemma wrapped_choose_time : forall w a b first second,
  (T_wrapped_choose w a b first second <= 16384 * N.of_nat
    (Pos.to_nat w + wrapped_bits a + wrapped_bits b +
      wrapped_bits first + wrapped_bits second + 1))%N.
Proof.
  intros w a b first second.
  pose proof (wrapped_size_bits w first) as Hfirstbits.
  time_unfold T_wrapped_choose. time_cbn. time_pose.
  destruct (wrapped_cover w a b first), (wrapped_cover w a b second),
    (wrapped_size w first <=? wrapped_size w second);
    rewrite !Nat2N.inj_add in *; time_cbn_all; lia.
Qed.
TimeBound wrapped_choose_time.

(** The join candidate only combines endpoint magnitudes from its two inputs. *)
Lemma wrapped_join_candidate_bits : forall w a b,
  (wrapped_bits
    (if wrapped_leb w a b then b else
     if wrapped_leb w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end) <= wrapped_bits a + wrapped_bits b)%nat.
Proof.
  intros w a b. destruct (wrapped_leb w a b), (wrapped_leb w b a); try lia.
  destruct a as [| |lo hi], b as [| |lo' hi']; cbn [wrapped_bits]; try lia.
  pose proof (wrapped_choose_bits w (WItv lo hi) (WItv lo' hi')
    (WItv lo hi') (WItv lo' hi)) as Hbits. cbn [wrapped_bits] in Hbits. lia.
Qed.

(** Circular joining charges two inclusion queries, cover selection and normalization. *)
Lemma wrapped_join_time : forall w a b,
  (T_wrapped_join w a b <=
    65536 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w a b. pose proof (wrapped_join_candidate_bits w a b) as Hcandidate.
  time_unfold T_wrapped_join.
  destruct (wrapped_leb w a b).
  - time_cbn. time_pose. rewrite !Nat2N.inj_add in *. lia.
  - destruct (wrapped_leb w b a).
    + time_cbn. time_pose. rewrite !Nat2N.inj_add in *. lia.
    + destruct a as [| |lo hi], b as [| |lo' hi'];
        time_cbn; time_pose; cbn [wrapped_bits] in *;
        rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_join_time.

(** Expanding an arc charges cardinality, endpoint shifts and normalization. *)
Lemma wrapped_double_time : forall w a,
  (T_wrapped_double w a <=
    4096 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi].
  - time_unfold T_wrapped_double. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - time_unfold T_wrapped_double. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
    pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
    pose proof (wrapped_size_bits w (WItv lo hi)) as Hsizebits.
    pose proof (WordTime.integer_sub_size lo (wrapped_size w (WItv lo hi))) as Hlobits.
    pose proof (WordTime.integer_add_size hi (wrapped_size w (WItv lo hi))) as Hhibits.
    time_unfold T_wrapped_double. cbn beta iota zeta. time_pose.
    destruct (modulus w <=? 3 * wrapped_size w (WItv lo hi));
      cbn [wrapped_bits] in *; rewrite !Nat2N.inj_add in *; time_cbn_all; lia.
Qed.
TimeBound wrapped_double_time.

(** Narrowing returns one of the two normalized input arcs. *)
Lemma wrapped_narrow_bits : forall w a b,
  (wrapped_bits (wrapped_narrow w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b.
  pose proof (wrapped_norm_bits w a) as Ha.
  pose proof (wrapped_norm_bits w b) as Hb.
  unfold wrapped_narrow. destruct (wrapped_norm w a); assumption.
Qed.

(** Narrowing performs a bounded number of normalizations. *)
Lemma wrapped_narrow_time : forall w a b,
  (T_wrapped_narrow w a b <=
    2048 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_wrapped_narrow. time_cbn. time_pose.
  destruct (wrapped_norm w a); rewrite !Nat2N.inj_add in *; time_cbn_all; lia.
Qed.
TimeBound wrapped_narrow_time.

(** Point recognition compares the normalized endpoints. *)
Lemma wrapped_point_time : forall w a,
  (T_wrapped_point w a <=
    2048 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w a. pose proof (wrapped_norm_time w a) as Hnorm.
  time_unfold T_wrapped_point. destruct (wrapped_norm w a) as [| |lo hi] eqn:Hshape.
  - rewrite !Nat2N.inj_add in *. lia.
  - rewrite !Nat2N.inj_add in *. lia.
  - destruct (wrapped_norm_endpoints w a lo hi Hshape) as [Hlo Hhi].
    pose proof (WordTime.word_size_bound w lo Hlo) as Hlobits.
    time_cbn. time_pose. destruct (lo =? hi); rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_point_time.

(** Masking produces an endpoint within the declared bit width. *)
Lemma arc_wrap_bits : forall w z,
  (Z.size_nat (arc_wrap w z) <= Pos.to_nat w)%nat.
Proof. intros w z. rewrite arc_wrap_agrees. apply WordTime.word_wrap_size_bound. Qed.

(** Splitting a raw circular arc stores only normalized word endpoints. *)
Lemma wrapped_parts_raw_bits : forall w a,
  (interval_bits (fst (wrapped_parts_raw w a)) <= Pos.to_nat w)%nat /\
  (interval_bits (snd (wrapped_parts_raw w a)) <= Pos.to_nat w)%nat.
Proof.
  intros w [| |lo hi].
  - change ((0 <= Pos.to_nat w)%nat /\ (0 <= Pos.to_nat w)%nat).
    split; apply Nat.le_0_l.
  - change ((Z.size_nat (modulus w - 1) <= Pos.to_nat w)%nat /\
      (0 <= Pos.to_nat w)%nat).
    split; [apply wrapped_last_word_bits | apply Nat.le_0_l].
  - unfold wrapped_parts_raw. destruct (arc_wrap w lo <=? arc_wrap w hi).
    + change ((Nat.max (Z.size_nat (arc_wrap w lo)) (Z.size_nat (arc_wrap w hi))
        <= Pos.to_nat w)%nat /\ (0 <= Pos.to_nat w)%nat).
      split; [apply Nat.max_lub; apply arc_wrap_bits | apply Nat.le_0_l].
    + change ((Nat.max (Z.size_nat (arc_wrap w lo)) (Z.size_nat (modulus w - 1))
        <= Pos.to_nat w)%nat /\ (Z.size_nat (arc_wrap w hi) <= Pos.to_nat w)%nat).
      split; [apply Nat.max_lub; [apply arc_wrap_bits | apply wrapped_last_word_bits]
             | apply arc_wrap_bits].
Qed.

(** Normalized circular parts retain the same width-bounded endpoints. *)
Lemma wrapped_parts_bits : forall w a,
  (interval_bits (fst (wrapped_parts w a)) <= Pos.to_nat w)%nat /\
  (interval_bits (snd (wrapped_parts w a)) <= Pos.to_nat w)%nat.
Proof. intros w a. unfold wrapped_parts. apply wrapped_parts_raw_bits. Qed.

(** Raw splitting charges two masks and one comparison at the numeric pole. *)
Lemma wrapped_parts_raw_time : forall w a,
  (T_wrapped_parts_raw w a <=
    128 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intro w.
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  intros [| |lo hi]; time_unfold T_wrapped_parts_raw; cbn beta iota zeta; time_simpl; time_pose.
  all: try change (Z.size_nat 1) with 1%nat in *.
  - cbn [wrapped_bits]. rewrite !Nat2N.inj_add in *. lia.
  - cbn [wrapped_bits]. rewrite !Nat2N.inj_add in *. time_simpl. lia.
  - pose proof (arc_wrap_bits w lo) as Hlo.
    destruct (arc_wrap w lo <=? arc_wrap w hi);
      cbn [wrapped_bits]; rewrite !Nat2N.inj_add in *; time_simpl; lia.
Qed.
TimeBound wrapped_parts_raw_time.

(** Normalization followed by raw splitting is linear in stored input bits. *)
Lemma wrapped_parts_time : forall w a,
  (T_wrapped_parts w a <=
    2048 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w a. pose proof (wrapped_norm_bits w a) as Hbits.
  time_unfold T_wrapped_parts. cbn beta iota zeta. time_simpl. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_parts_time.

(** Interval conversion stores only normalized endpoint values. *)
Lemma wrapped_of_interval_bits : forall w a,
  (wrapped_bits (wrapped_of_interval w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w [|[|lo|] [|hi|]]; cbn [wrapped_of_interval wrapped_bits]; try lia.
  unfold wrapped_range. destruct (hi <? lo), (modulus w - 1 <=? hi - lo);
    try (cbn [wrapped_bits]; lia). apply wrapped_norm_bits.
Qed.

(** Converting an interval charges its largest endpoint and the target width. *)
Lemma wrapped_of_interval_time : forall w a,
  (T_wrapped_of_interval w a <=
    4096 * N.of_nat (Pos.to_nat w + interval_bits a + 1))%N.
Proof.
  intros w [|[|lo|] [|hi|]]; time_unfold T_wrapped_of_interval;
    cbn beta iota zeta; time_simpl; time_pose; cbn [interval_bits]; rewrite !Nat2N.inj_add in *;
      lia.
Qed.
TimeBound wrapped_of_interval_time.

(** Joining four pieces ends in a normalized circular join. *)
Lemma wrapped_join_four_bits : forall w a b c d,
  (wrapped_bits (wrapped_join_four w a b c d) <= 2 * Pos.to_nat w)%nat.
Proof. intros. unfold wrapped_join_four. apply wrapped_join_bits. Qed.

(** Joining four pieces charges a fixed tree of three linear joins. *)
Lemma wrapped_join_four_time : forall w a b c d,
  (T_wrapped_join_four w a b c d <= 524288 * N.of_nat
    (Pos.to_nat w + wrapped_bits a + wrapped_bits b + wrapped_bits c + wrapped_bits d + 1))%N.
Proof.
  intros w a b c d.
  pose proof (wrapped_join_bits w a b) as Hleft.
  pose proof (wrapped_join_bits w c d) as Hright.
  set (left := wrapped_join w a b) in *.
  set (right := wrapped_join w c d) in *.
  time_unfold T_wrapped_join_four. cbn beta iota zeta.
  fold left right. clearbody left right. time_simpl. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_join_four_time.

(** Intersecting circular arcs returns a normalized candidate or normalized left input. *)
Lemma wrapped_meet_bits : forall w a b,
  (wrapped_bits (wrapped_meet w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. unfold wrapped_meet.
  lazymatch goal with
  | |- context [if ?choice then _ else _] => destruct choice
  end.
  - apply wrapped_join_four_bits.
  - apply wrapped_norm_bits.
Qed.

(** Circular intersection performs four scalar intersections and a fixed join tree. *)
Lemma wrapped_meet_time : forall w a b,
  (T_wrapped_meet w a b <=
    16777216 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w a b.
  pose proof (wrapped_parts_bits w a) as [Ha0 Ha1].
  pose proof (wrapped_parts_bits w b) as [Hb0 Hb1].
  set (pa := wrapped_parts w a) in *.
  set (pb := wrapped_parts w b) in *.
  pose proof (WrappedScalar.interval_meet_bits (fst pa) (fst pb)) as H00.
  pose proof (WrappedScalar.interval_meet_bits (fst pa) (snd pb)) as H01.
  pose proof (WrappedScalar.interval_meet_bits (snd pa) (fst pb)) as H10.
  pose proof (WrappedScalar.interval_meet_bits (snd pa) (snd pb)) as H11.
  pose proof (WrappedScalar.T_interval_meet_le (fst pa) (fst pb)) as HT00.
  pose proof (WrappedScalar.T_interval_meet_le (fst pa) (snd pb)) as HT01.
  pose proof (WrappedScalar.T_interval_meet_le (snd pa) (fst pb)) as HT10.
  pose proof (WrappedScalar.T_interval_meet_le (snd pa) (snd pb)) as HT11.
  pose proof (wrapped_of_interval_bits w (WrappedScalar.interval_meet (fst pa) (fst pb)))
    as Hr00.
  pose proof (wrapped_of_interval_bits w (WrappedScalar.interval_meet (fst pa) (snd pb)))
    as Hr01.
  pose proof (wrapped_of_interval_bits w (WrappedScalar.interval_meet (snd pa) (fst pb)))
    as Hr10.
  pose proof (wrapped_of_interval_bits w (WrappedScalar.interval_meet (snd pa) (snd pb)))
    as Hr11.
  set (r00 := wrapped_of_interval w (WrappedScalar.interval_meet (fst pa) (fst pb))) in *.
  set (r01 := wrapped_of_interval w (WrappedScalar.interval_meet (fst pa) (snd pb))) in *.
  set (r10 := wrapped_of_interval w (WrappedScalar.interval_meet (snd pa) (fst pb))) in *.
  set (r11 := wrapped_of_interval w (WrappedScalar.interval_meet (snd pa) (snd pb))) in *.
  pose proof (wrapped_join_four_bits w r00 r01 r10 r11) as Hcandidatebits.
  set (candidate := wrapped_join_four w r00 r01 r10 r11) in *.
  time_unfold T_wrapped_meet. cbn beta iota zeta. fold pa pb r00 r01 r10 r11 candidate.
  clearbody pa pb r00 r01 r10 r11 candidate.
  time_simpl. time_pose. destruct (wrapped_leb w candidate a).
  all: unfold WrappedScalar.c_scalar, ThresholdsT.c_thresholds in *;
    rewrite !Nat2N.inj_add in *; time_cbn_all; lia.
Qed.
TimeBound wrapped_meet_time.

(** Expansion normalizes every resulting finite arc. *)
Lemma wrapped_double_bits : forall w a,
  (wrapped_bits (wrapped_double w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w [| |lo hi]; cbn [wrapped_double wrapped_bits]; try lia.
  destruct (modulus w <=? 3 * wrapped_size w (WItv lo hi));
    [cbn [wrapped_bits]; lia|apply wrapped_norm_bits].
Qed.

(** Negation charges endpoint sign changes and one normalization. *)
Lemma wrapped_neg_time : forall w a,
  (T_wrapped_neg w a <=
    2048 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi]; time_unfold T_wrapped_neg;
    cbn beta iota zeta; time_simpl; time_pose; cbn [wrapped_bits] in *;
    rewrite ?WordTime.integer_opp_size in *; rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_neg_time.

(** Addition charges cardinalities and linear endpoint sums. *)
Lemma wrapped_add_time : forall w a b,
  (T_wrapped_add w a b <=
    4096 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w [| |lo hi] [| |lo' hi'];
    try (time_unfold T_wrapped_add; cbn [wrapped_bits]; rewrite !Nat2N.inj_add; lia).
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  pose proof (wrapped_size_bits w (WItv lo hi)) as Habits.
  pose proof (wrapped_size_bits w (WItv lo' hi')) as Hbbits.
  pose proof (WordTime.integer_add_size lo lo') as Hlobits.
  pose proof (WordTime.integer_add_size hi hi') as Hhibits.
  time_unfold T_wrapped_add. cbn beta iota zeta. time_simpl. time_pose.
  destruct (modulus w <? wrapped_size w (WItv lo hi) + wrapped_size w (WItv lo' hi'));
    cbn [wrapped_bits] in *; rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_add_time.

(** Subtraction composes normalized negation and addition. *)
Lemma wrapped_sub_time : forall w a b,
  (T_wrapped_sub w a b <=
    16384 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w a b. pose proof (wrapped_neg_bits w b) as Hbits.
  time_unfold T_wrapped_sub. cbn beta iota zeta. time_simpl. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_sub_time.

(** Shifting an interval adds the displacement bits and one carry bit. *)
Lemma wrapped_shift_interval_bits : forall delta a,
  (interval_bits (wrapped_shift_interval delta a) <=
    interval_bits a + Z.size_nat delta + 1)%nat.
Proof.
  intros delta [|lower upper].
  - cbn [wrapped_shift_interval interval_bits]. lia.
  - pose proof (WrappedScalar.scalar_endpoint_bits lower upper) as [Hlo Hhi].
    destruct lower as [|lo|], upper as [|hi|];
      cbn [wrapped_shift_interval interval_bits WrappedScalar.scalar_bnd_bits] in *;
      try (pose proof (WordTime.integer_add_size lo delta));
      try (pose proof (WordTime.integer_add_size hi delta)); lia.
Qed.

(** Shifting an interval charges at most two integer additions. *)
Lemma wrapped_shift_interval_time : forall delta a,
  (T_wrapped_shift_interval delta a <=
    32 * N.of_nat (interval_bits a + Z.size_nat delta + 1))%N.
Proof.
  intros delta [|lower upper].
  - time_unfold T_wrapped_shift_interval. cbn [interval_bits].
    rewrite Nat2N.inj_add. lia.
  - pose proof (WrappedScalar.scalar_endpoint_bits lower upper) as [Hlo Hhi].
    destruct lower as [|lo|], upper as [|hi|];
      time_unfold T_wrapped_shift_interval; cbn beta iota zeta; time_simpl; time_pose;
      cbn [interval_bits WrappedScalar.scalar_bnd_bits] in *;
      rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_shift_interval_time.

(** Signed parts shift width-bounded unsigned endpoints by half a modulus. *)
Lemma wrapped_signed_parts_bits : forall w a,
  (interval_bits (fst (wrapped_signed_parts w a)) <= 2 * Pos.to_nat w + 1)%nat /\
  (interval_bits (snd (wrapped_signed_parts w a)) <= 2 * Pos.to_nat w + 1)%nat.
Proof.
  intros w a.
  pose proof (WordTime.word_half_size_bound w) as Hhalf.
  pose proof (wrapped_parts_bits w (wrapped_add w a (WItv (half w) (half w)))) as [Hl Hr].
  pose proof (wrapped_shift_interval_bits (- half w)
    (fst (wrapped_parts w (wrapped_add w a (WItv (half w) (half w)))))) as Hleft.
  pose proof (wrapped_shift_interval_bits (- half w)
    (snd (wrapped_parts w (wrapped_add w a (WItv (half w) (half w)))))) as Hright.
  unfold wrapped_signed_parts. cbn [fst snd]. rewrite WordTime.integer_opp_size in *. lia.
Qed.

(** Signed splitting composes linear addition, splitting and endpoint shifts. *)
Lemma wrapped_signed_parts_time : forall w a,
  (T_wrapped_signed_parts w a <=
    65536 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w a.
  pose proof (WordTime.word_half_time_bound w) as Hhalftime.
  pose proof (WordTime.word_half_size_bound w) as Hhalfbits.
  pose proof (wrapped_add_bits w a (WItv (half w) (half w))) as Haddedbits.
  pose proof (wrapped_parts_bits w (wrapped_add w a (WItv (half w) (half w)))) as [Hl Hr].
  time_unfold T_wrapped_signed_parts. cbn beta iota zeta. time_simpl. time_pose.
  cbn [wrapped_bits] in *. rewrite WordTime.integer_opp_size in *.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_signed_parts_time.

(** The predecessor of the signed pole is an unsigned word. *)
Lemma wrapped_half_last_bits : forall w,
  (Z.size_nat (half w - 1) <= Pos.to_nat w)%nat.
Proof.
  intro w. apply WordTime.word_size_bound. unfold is_word.
  pose proof (half_pos w). pose proof (modulus_half w). lia.
Qed.

(** Cutting at the signed pole charges two scalar intersections. *)
Lemma wrapped_pole_cut_time : forall w a,
  (T_wrapped_pole_cut w a <=
    1048576 * N.of_nat (Pos.to_nat w + interval_bits a + 1))%N.
Proof.
  intros w a.
  pose proof (WordTime.word_half_time_bound w) as Hhalftime.
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulustime.
  pose proof (WordTime.word_half_size_bound w) as Hhalfbits.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  pose proof (wrapped_half_last_bits w) as Hhalflastbits.
  pose proof (wrapped_last_word_bits w) as Hlastbits.
  pose proof (WrappedScalar.T_interval_meet_le a (I (Fin 0) (Fin (half w - 1)))) as Hleft.
  pose proof (WrappedScalar.T_interval_meet_le a (I (Fin (half w)) (Fin (modulus w - 1))))
    as Hright.
  set (hp := half w) in *.
  set (mp := modulus w) in *.
  set (hlast := hp - 1) in *.
  set (mlast := mp - 1) in *.
  time_unfold T_wrapped_pole_cut. cbn beta iota zeta.
  fold hp mp hlast mlast. clearbody hp mp hlast mlast.
  time_simpl. time_pose.
  unfold WrappedScalar.c_scalar, ThresholdsT.c_thresholds in *.
  cbn [interval_bits] in *.
  try change (Z.size_nat 0) with 0%nat in *.
  try change (Z.size_nat 1) with 1%nat in *.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_pole_cut_time.

(** A numeric pole adds only its own magnitude bits to clipped intervals. *)
Lemma wrapped_mul_cut_bits : forall pole a,
  (interval_bits (fst (wrapped_mul_cut pole a)) <=
    interval_bits a + Z.size_nat pole + 2)%nat /\
  (interval_bits (snd (wrapped_mul_cut pole a)) <=
    interval_bits a + Z.size_nat pole + 2)%nat.
Proof.
  intros pole a.
  pose proof (WrappedScalar.interval_meet_bits a (I NegInf (Fin (pole - 1)))) as Hl.
  pose proof (WrappedScalar.interval_meet_bits a (I (Fin pole) PosInf)) as Hr.
  pose proof (WordTime.integer_sub_size pole 1) as Hpred.
  change ((interval_bits (WrappedScalar.interval_meet a (I NegInf (Fin (pole - 1)))) <=
    interval_bits a + Z.size_nat pole + 2)%nat /\
    (interval_bits (WrappedScalar.interval_meet a (I (Fin pole) PosInf)) <=
    interval_bits a + Z.size_nat pole + 2)%nat).
  change (interval_bits (WrappedScalar.interval_meet a (I NegInf (Fin (pole - 1)))) <=
    interval_bits a + Z.size_nat (pole - 1))%nat in Hl.
  change (interval_bits (WrappedScalar.interval_meet a (I (Fin pole) PosInf)) <=
    interval_bits a + Nat.max (Z.size_nat pole) 0)%nat in Hr.
  rewrite Nat.max_0_r in Hr.
  change (Z.size_nat 1) with 1%nat in Hpred. lia.
Qed.

(** Cutting at an arbitrary numeric pole has linear endpoint cost. *)
Lemma wrapped_mul_cut_time : forall pole a,
  (T_wrapped_mul_cut pole a <=
    1048576 * N.of_nat (interval_bits a + Z.size_nat pole + 1))%N.
Proof.
  intros pole a.
  pose proof (WrappedScalar.T_interval_meet_le a (I NegInf (Fin (pole - 1)))) as Hl.
  pose proof (WrappedScalar.T_interval_meet_le a (I (Fin pole) PosInf)) as Hr.
  pose proof (WordTime.integer_sub_size pole 1) as Hpred.
  set (last := pole - 1) in *.
  time_unfold T_wrapped_mul_cut. cbn beta iota zeta. fold last. clearbody last.
  time_simpl. time_pose.
  unfold WrappedScalar.c_scalar, ThresholdsT.c_thresholds in *.
  cbn [interval_bits] in *. rewrite ?Nat.max_0_r in *. try change (Z.size_nat 1) with 1%nat in *.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_mul_cut_time.


(** Finite interval conversion always normalizes its stored circular endpoints. *)
Lemma wrapped_range_bits : forall w lo hi,
  (wrapped_bits (wrapped_range w lo hi) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w lo hi. unfold wrapped_range.
  destruct (hi <? lo), (modulus w - 1 <=? hi - lo);
    try (cbn [wrapped_bits]; lia). apply wrapped_norm_bits.
Qed.

(** Every multiplication piece stores at most two normalized words. *)
Lemma wrapped_mul_piece_bits : forall w a b,
  (wrapped_bits (wrapped_mul_piece w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w [|[|lo|] [|hi|]] [|[|lo'|] [|hi'|]];
    cbn [wrapped_mul_piece wrapped_bits]; try lia. apply wrapped_range_bits.
Qed.

(** Arbitrary interval pieces charge their endpoint maxima quadratically. *)
Lemma wrapped_mul_piece_time : forall w a b,
  (T_wrapped_mul_piece w a b <= 131072 * N.of_nat
    ((Pos.to_nat w + interval_bits a + interval_bits b + 1) ^ 2))%N.
Proof.
  intros w a b.
  pose proof (WordTime.time_square_floor 1
    (Pos.to_nat w + interval_bits a + interval_bits b + 1) ltac:(lia) ltac:(lia)) as Hpositive.
  destruct a as [|[|lo|] [|hi|]], b as [|[|lo'|] [|hi'|]];
    try (time_unfold T_wrapped_mul_piece; cbn beta iota zeta; lia).
  pose proof (wrapped_mul_piece_finite_time w lo hi lo' hi') as Hfinite.
  pose proof (WordTime.time_square_scale _ _ _
    (Pos.to_nat w + interval_bits (I (Fin lo) (Fin hi)) +
      interval_bits (I (Fin lo') (Fin hi')) + 1) 2 Hfinite
    ltac:(cbn [interval_bits]; lia)) as Hscaled.
  exact Hscaled.
Qed.
TimeBound wrapped_mul_piece_time.

(** Combining four multiplication pieces ends in a normalized join. *)
Lemma wrapped_mul_parts_bits : forall w a b,
  (wrapped_bits (wrapped_mul_parts w a b) <= 2 * Pos.to_nat w)%nat.
Proof. intros. unfold wrapped_mul_parts. apply wrapped_join_four_bits. Qed.

(** Four multiplication pieces share one quadratic endpoint budget. *)
Lemma wrapped_mul_parts_time : forall w a b,
  (T_wrapped_mul_parts w a b <= 16777216 * N.of_nat
    ((Pos.to_nat w + interval_bits (fst a) + interval_bits (snd a) +
      interval_bits (fst b) + interval_bits (snd b) + 1) ^ 2))%N.
Proof.
  intros w [a0 a1] [b0 b1].
  set (n := (Pos.to_nat w + interval_bits a0 + interval_bits a1 +
    interval_bits b0 + interval_bits b1 + 1)%nat).
  change (T_wrapped_mul_parts w (a0, a1) (b0, b1) <=
    16777216 * N.of_nat (n ^ 2))%N.
  assert (HT00 : (T_wrapped_mul_piece w a0 b0 <= 131072 * N.of_nat (n ^ 2))%N).
  { eapply WordTime.time_square_weaken; [apply wrapped_mul_piece_time|unfold n; lia]. }
  assert (HT01 : (T_wrapped_mul_piece w a0 b1 <= 131072 * N.of_nat (n ^ 2))%N).
  { eapply WordTime.time_square_weaken; [apply wrapped_mul_piece_time|unfold n; lia]. }
  assert (HT10 : (T_wrapped_mul_piece w a1 b0 <= 131072 * N.of_nat (n ^ 2))%N).
  { eapply WordTime.time_square_weaken; [apply wrapped_mul_piece_time|unfold n; lia]. }
  assert (HT11 : (T_wrapped_mul_piece w a1 b1 <= 131072 * N.of_nat (n ^ 2))%N).
  { eapply WordTime.time_square_weaken; [apply wrapped_mul_piece_time|unfold n; lia]. }
  pose proof (wrapped_mul_piece_bits w a0 b0) as H00.
  pose proof (wrapped_mul_piece_bits w a0 b1) as H01.
  pose proof (wrapped_mul_piece_bits w a1 b0) as H10.
  pose proof (wrapped_mul_piece_bits w a1 b1) as H11.
  pose proof (wrapped_join_four_time w (wrapped_mul_piece w a0 b0)
    (wrapped_mul_piece w a0 b1) (wrapped_mul_piece w a1 b0) (wrapped_mul_piece w a1 b1))
    as Hjoin.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) n
    ltac:(unfold n; lia) ltac:(unfold n; lia)) as Hwidth.
  set (square := N.of_nat (n ^ 2)) in *.
  clearbody n square.
  apply time_of_nat_le in H00, H01, H10, H11.
  rewrite Nat2N.inj_mul in H00, H01, H10, H11.
  time_unfold T_wrapped_mul_parts. cbn [fst snd]. time_simpl.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_mul_parts_time.

(** Multiplication after cutting both poles ends in a normalized join. *)
Lemma wrapped_mul_both_parts_bits : forall w pole a b,
  (wrapped_bits (wrapped_mul_both_parts w pole a b) <= 2 * Pos.to_nat w)%nat.
Proof. intros. unfold wrapped_mul_both_parts. apply wrapped_join_four_bits. Qed.

(** Cutting both inputs and combining the sixteen products has quadratic work. *)
Lemma wrapped_mul_both_parts_time : forall w pole a b,
  (T_wrapped_mul_both_parts w pole a b <= 17179869184 * N.of_nat
    ((Pos.to_nat w + Z.size_nat pole + interval_bits (fst a) + interval_bits (snd a) +
      interval_bits (fst b) + interval_bits (snd b) + 1) ^ 2))%N.
Proof.
  intros w pole [a0 a1] [b0 b1].
  set (n := (Pos.to_nat w + Z.size_nat pole + interval_bits a0 + interval_bits a1 +
    interval_bits b0 + interval_bits b1 + 1)%nat).
  change (T_wrapped_mul_both_parts w pole (a0, a1) (b0, b1) <=
    17179869184 * N.of_nat (n ^ 2))%N.
  pose proof (wrapped_mul_cut_bits pole a0) as [Ha00 Ha01].
  pose proof (wrapped_mul_cut_bits pole a1) as [Ha10 Ha11].
  pose proof (wrapped_mul_cut_bits pole b0) as [Hb00 Hb01].
  pose proof (wrapped_mul_cut_bits pole b1) as [Hb10 Hb11].
  assert (HTa0 : (T_wrapped_mul_cut pole a0 <= 1048576 * N.of_nat n)%N).
  { eapply N.le_trans; [apply wrapped_mul_cut_time|].
    apply N.mul_le_mono_l, time_of_nat_le. unfold n. lia. }
  assert (HTa1 : (T_wrapped_mul_cut pole a1 <= 1048576 * N.of_nat n)%N).
  { eapply N.le_trans; [apply wrapped_mul_cut_time|].
    apply N.mul_le_mono_l, time_of_nat_le. unfold n. lia. }
  assert (HTb0 : (T_wrapped_mul_cut pole b0 <= 1048576 * N.of_nat n)%N).
  { eapply N.le_trans; [apply wrapped_mul_cut_time|].
    apply N.mul_le_mono_l, time_of_nat_le. unfold n. lia. }
  assert (HTb1 : (T_wrapped_mul_cut pole b1 <= 1048576 * N.of_nat n)%N).
  { eapply N.le_trans; [apply wrapped_mul_cut_time|].
    apply N.mul_le_mono_l, time_of_nat_le. unfold n. lia. }
  set (ca0 := wrapped_mul_cut pole a0) in *.
  set (ca1 := wrapped_mul_cut pole a1) in *.
  set (cb0 := wrapped_mul_cut pole b0) in *.
  set (cb1 := wrapped_mul_cut pole b1) in *.
  assert (HT00 : (T_wrapped_mul_parts w ca0 cb0 <= 1358954496 * N.of_nat (n ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ n 9 (wrapped_mul_parts_time w ca0 cb0)
      ltac:(unfold n; lia)). }
  assert (HT01 : (T_wrapped_mul_parts w ca0 cb1 <= 1358954496 * N.of_nat (n ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ n 9 (wrapped_mul_parts_time w ca0 cb1)
      ltac:(unfold n; lia)). }
  assert (HT10 : (T_wrapped_mul_parts w ca1 cb0 <= 1358954496 * N.of_nat (n ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ n 9 (wrapped_mul_parts_time w ca1 cb0)
      ltac:(unfold n; lia)). }
  assert (HT11 : (T_wrapped_mul_parts w ca1 cb1 <= 1358954496 * N.of_nat (n ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ n 9 (wrapped_mul_parts_time w ca1 cb1)
      ltac:(unfold n; lia)). }
  pose proof (wrapped_mul_parts_bits w ca0 cb0) as H00.
  pose proof (wrapped_mul_parts_bits w ca0 cb1) as H01.
  pose proof (wrapped_mul_parts_bits w ca1 cb0) as H10.
  pose proof (wrapped_mul_parts_bits w ca1 cb1) as H11.
  pose proof (wrapped_join_four_time w (wrapped_mul_parts w ca0 cb0)
    (wrapped_mul_parts w ca0 cb1) (wrapped_mul_parts w ca1 cb0) (wrapped_mul_parts w ca1 cb1))
    as Hjoin.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) n
    ltac:(unfold n; lia) ltac:(unfold n; lia)) as Hwidth.
  pose proof (WordTime.time_square_floor n n ltac:(lia) ltac:(unfold n; lia)) as Hlinear.
  set (square := N.of_nat (n ^ 2)) in *.
  clearbody n square.
  apply time_of_nat_le in H00, H01, H10, H11.
  rewrite Nat2N.inj_mul in H00, H01, H10, H11.
  time_unfold T_wrapped_mul_both_parts. cbn [fst snd]. time_simpl. fold ca0 ca1 cb0 cb1.
  clearbody ca0 ca1 cb0 cb1.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_mul_both_parts_time.

(** Circular multiplication normalizes raw inputs before its quadratic word arithmetic. *)
Lemma wrapped_mul_time : forall w a b,
  (T_wrapped_mul w a b <= 17592186044416 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
Proof.
  intros w a b.
  pose proof (wrapped_parts_bits w a) as [Ha0 Ha1].
  pose proof (wrapped_parts_bits w b) as [Hb0 Hb1].
  pose proof (wrapped_signed_parts_bits w a) as [Hsa0 Hsa1].
  pose proof (wrapped_signed_parts_bits w b) as [Hsb0 Hsb1].
  pose proof (WordTime.word_half_size_bound w) as Hhalfbits.
  pose proof (WordTime.word_half_time_bound w) as Hhalftime.
  pose proof (wrapped_parts_time w a) as Hpartsa.
  pose proof (wrapped_parts_time w b) as Hpartsb.
  pose proof (wrapped_signed_parts_time w a) as Hsigneda.
  pose proof (wrapped_signed_parts_time w b) as Hsignedb.
  set (pa := wrapped_parts w a) in *.
  set (pb := wrapped_parts w b) in *.
  set (sa := wrapped_signed_parts w a) in *.
  set (sb := wrapped_signed_parts w b) in *.
  assert (Hunsigned : (T_wrapped_mul_both_parts w (half w) pa pb <=
    618475290624 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ (Pos.to_nat w + 1) 6
      (wrapped_mul_both_parts_time w (half w) pa pb) ltac:(lia)). }
  assert (Hsigned : (T_wrapped_mul_both_parts w 0 sa sb <=
    1391569403904 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ (Pos.to_nat w + 1) 9
      (wrapped_mul_both_parts_time w 0 sa sb) ltac:(cbn [Z.size_nat]; lia)). }
  pose proof (wrapped_mul_both_parts_bits w (half w) pa pb) as Hubits.
  pose proof (wrapped_mul_both_parts_bits w 0 sa sb) as Hvbits.
  set (u := wrapped_mul_both_parts w (half w) pa pb) in *.
  set (v := wrapped_mul_both_parts w 0 sa sb) in *.
  pose proof (wrapped_size_time w u) as Hucard.
  pose proof (wrapped_size_time w v) as Hvcard.
  pose proof (wrapped_size_bits w u) as Hucardbits.
  pose proof (Std.Z.T_leb_le (wrapped_size w u) (wrapped_size w v)) as Hcompare.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    ltac:(lia) ltac:(lia)) as Hwidth.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b)).
  change (T_wrapped_mul w a b <= 17592186044416 * budget)%N.
  assert (Hbudget : (square + N.of_nat (wrapped_bits a) + N.of_nat (wrapped_bits b) = budget)%N).
  { unfold square, budget. rewrite !Nat2N.inj_add. reflexivity. }
  apply time_of_nat_le in Hubits, Hvbits, Hucardbits.
  rewrite Nat2N.inj_mul in Hubits, Hvbits.
  time_unfold T_wrapped_mul. cbn beta iota zeta. time_simpl. fold pa pb sa sb u v.
  clearbody pa pb sa sb u v square budget.
  destruct (wrapped_size w u <=? wrapped_size w v);
    rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_mul_time.

(** The point shortcut retains the quadratic budget for raw multiplication inputs. *)
Lemma wrapped_mul_fast_time : forall w a b,
  (T_wrapped_mul_fast w a b <= 17592186044416 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
Proof.
  intros w a b.
  pose proof (wrapped_parts_bits w a) as [Ha0 Ha1].
  pose proof (wrapped_parts_bits w b) as [Hb0 Hb1].
  pose proof (wrapped_signed_parts_bits w a) as [Hsa0 Hsa1].
  pose proof (wrapped_signed_parts_bits w b) as [Hsb0 Hsb1].
  pose proof (WordTime.word_half_size_bound w) as Hhalfbits.
  pose proof (WordTime.word_half_time_bound w) as Hhalftime.
  pose proof (wrapped_parts_time w a) as Hpartsa.
  pose proof (wrapped_parts_time w b) as Hpartsb.
  pose proof (wrapped_signed_parts_time w a) as Hsigneda.
  pose proof (wrapped_signed_parts_time w b) as Hsignedb.
  set (pa := wrapped_parts w a) in *.
  set (pb := wrapped_parts w b) in *.
  set (sa := wrapped_signed_parts w a) in *.
  set (sb := wrapped_signed_parts w b) in *.
  assert (Hunsigned : (T_wrapped_mul_both_parts w (half w) pa pb <=
    618475290624 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ (Pos.to_nat w + 1) 6
      (wrapped_mul_both_parts_time w (half w) pa pb) ltac:(lia)). }
  assert (Hsigned : (T_wrapped_mul_both_parts w 0 sa sb <=
    1391569403904 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
  { exact (WordTime.time_square_scale _ _ _ (Pos.to_nat w + 1) 9
      (wrapped_mul_both_parts_time w 0 sa sb) ltac:(cbn [Z.size_nat]; lia)). }
  pose proof (wrapped_mul_both_parts_bits w (half w) pa pb) as Hubits.
  pose proof (wrapped_mul_both_parts_bits w 0 sa sb) as Hvbits.
  set (u := wrapped_mul_both_parts w (half w) pa pb) in *.
  set (v := wrapped_mul_both_parts w 0 sa sb) in *.
  pose proof (wrapped_size_time w u) as Hucard.
  pose proof (wrapped_size_time w v) as Hvcard.
  pose proof (wrapped_size_bits w u) as Hucardbits.
  pose proof (Std.Z.T_leb_le (wrapped_size w u) (wrapped_size w v)) as Hcompare.
  pose proof (Std.Z.T_leb_le (wrapped_size w u) 1) as Hsmall.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    ltac:(lia) ltac:(lia)) as Hwidth.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b)).
  change (T_wrapped_mul_fast w a b <= 17592186044416 * budget)%N.
  assert (Hbudget : (square + N.of_nat (wrapped_bits a) + N.of_nat (wrapped_bits b) = budget)%N).
  { unfold square, budget. rewrite !Nat2N.inj_add. reflexivity. }
  apply time_of_nat_le in Hubits, Hvbits, Hucardbits.
  rewrite Nat2N.inj_mul in Hubits, Hvbits.
  time_unfold T_wrapped_mul_fast. cbn beta iota zeta. time_simpl. fold pa pb sa sb u v.
  clearbody pa pb sa sb u v square budget.
  destruct (wrapped_size w u <=? 1), (wrapped_size w u <=? wrapped_size w v);
    rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_mul_fast_time.

(** Extracting one finite interval inspects only its constructors. *)
Lemma wrapped_interval_list_time : forall a, (T_wrapped_interval_list a <= 4)%N.
Proof.
  intros [|[|lo|] [|hi|]]; time_unfold T_wrapped_interval_list; lia.
Qed.
TimeBound wrapped_interval_list_time.

(** Splitting charges normalization, two pole cuts and bounded list concatenations. *)
Lemma wrapped_split_time : forall w a,
  (T_wrapped_split w a <=
    8388608 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w a.
  pose proof (wrapped_parts_bits w a) as [Hleftbits Hrightbits].
  pose proof (wrapped_parts_time w a) as Hparts.
  set (pieces := wrapped_parts w a) in *.
  pose proof (wrapped_pole_cut_time w (fst pieces)) as Hleftcut.
  pose proof (wrapped_pole_cut_time w (snd pieces)) as Hrightcut.
  set (low := wrapped_pole_cut w (fst pieces)) in *.
  set (high := wrapped_pole_cut w (snd pieces)) in *.
  pose proof (wrapped_interval_list_length (fst low)) as H00.
  pose proof (wrapped_interval_list_length (snd low)) as H01.
  pose proof (wrapped_interval_list_length (fst high)) as H10.
  pose proof (wrapped_interval_list_length (snd high)) as H11.
  set (l00 := wrapped_interval_list (fst low)) in *.
  set (l01 := wrapped_interval_list (snd low)) in *.
  set (l10 := wrapped_interval_list (fst high)) in *.
  set (l11 := wrapped_interval_list (snd high)) in *.
  time_unfold T_wrapped_split. cbn beta iota zeta. time_simpl.
  fold pieces low high l00 l01 l10 l11.
  clearbody pieces low high l00 l01 l10 l11.
  time_pose. rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_split_time.


(** Reading finite endpoints inspects only interval constructors. *)
Lemma wrapped_finite_helper_time : forall a,
  (T_interval_finite_helper a <= 4)%N.
Proof.
  intros [|[|lo|] [|hi|]]; time_unfold T_interval_finite_helper;
    cbn beta iota zeta; time_simpl; lia.
Qed.
TimeBound wrapped_finite_helper_time.

(** A full unsigned interval stores at most the declared word width. *)
Lemma wrapped_interval_top_bits : forall w,
  (interval_bits (WrappedIntervalOps.interval_top w) <= Pos.to_nat w)%nat.
Proof.
  intro w. change (Z.size_nat (modulus w - 1) <= Pos.to_nat w)%nat.
  apply wrapped_last_word_bits.
Qed.

(** Constructing the full interval computes one last-word endpoint. *)
Lemma wrapped_interval_top_time : forall w,
  (WrappedIntervalOps.T_interval_top w <= 64 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  time_unfold WrappedIntervalOps.T_interval_top. cbn beta iota zeta. time_simpl. time_pose.
  try change (Z.size_nat 1) with 1%nat in *. rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_interval_top_time.

(** Checked construction stores either the supplied endpoints or the full range. *)
Lemma wrapped_interval_checked_bits : forall w lo hi,
  (interval_bits (WrappedIntervalOps.interval_checked w lo hi) <=
    Pos.to_nat w + Z.size_nat lo + Z.size_nat hi)%nat.
Proof.
  intros w lo hi. unfold WrappedIntervalOps.interval_checked.
  destruct ((0 <=? lo) && (hi <? modulus w))%bool.
  - change (Nat.max (Z.size_nat lo) (Z.size_nat hi) <=
      Pos.to_nat w + Z.size_nat lo + Z.size_nat hi)%nat. lia.
  - pose proof (wrapped_interval_top_bits w). lia.
Qed.

(** Checked endpoints charge their comparison and possible full-range fallback. *)
Lemma wrapped_interval_checked_time : forall w lo hi,
  (WrappedIntervalOps.T_interval_checked w lo hi <=
    256 * N.of_nat (Pos.to_nat w + Z.size_nat lo + Z.size_nat hi + 1))%N.
Proof.
  intros w lo hi. pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  time_unfold WrappedIntervalOps.T_interval_checked. cbn beta iota zeta. time_simpl. time_pose.
  destruct ((0 <=? lo) && (hi <? modulus w))%bool;
    try change (Z.size_nat 0) with 0%nat in *; rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_interval_checked_time.

(** Interval complement grows endpoint magnitude by at most the word width. *)
Lemma wrapped_interval_not_bits : forall w a,
  (interval_bits (WrappedIntervalOps.interval_not w a) <=
    3 * Pos.to_nat w + 2 * interval_bits a + 2)%nat.
Proof.
  intros w [|[|lo|] [|hi|]];
    cbn [WrappedIntervalOps.interval_not interval_finite_helper];
    try (pose proof (wrapped_interval_top_bits w); lia).
  pose proof (wrapped_interval_checked_bits w (modulus w - 1 - hi) (modulus w - 1 - lo))
    as Hchecked.
  pose proof (WordTime.integer_sub_size (modulus w - 1) lo) as Hlo.
  pose proof (WordTime.integer_sub_size (modulus w - 1) hi) as Hhi.
  pose proof (wrapped_last_word_bits w) as Hlast.
  change (interval_bits (WrappedIntervalOps.interval_checked w
    (modulus w - 1 - hi) (modulus w - 1 - lo)) <=
    3 * Pos.to_nat w + 2 * Nat.max (Z.size_nat lo) (Z.size_nat hi) + 2)%nat.
  lia.
Qed.

(** Interval complement computes two linear endpoint differences. *)
Lemma wrapped_interval_not_time : forall w a,
  (WrappedIntervalOps.T_interval_not w a <=
    4096 * N.of_nat (Pos.to_nat w + interval_bits a + 1))%N.
Proof.
  intros w [|[|lo|] [|hi|]];
    try (time_unfold WrappedIntervalOps.T_interval_not; cbn beta iota zeta;
      cbn [interval_finite_helper]; time_simpl; time_pose; cbn [interval_bits]; rewrite
        !Nat2N.inj_add in *; lia).
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  pose proof (wrapped_last_word_bits w) as Hlast.
  pose proof (WordTime.integer_sub_size (modulus w - 1) lo) as Hlo.
  pose proof (WordTime.integer_sub_size (modulus w - 1) hi) as Hhi.
  set (last := modulus w - 1) in *.
  time_unfold WrappedIntervalOps.T_interval_not. cbn beta iota zeta. cbn [interval_finite_helper].
  fold last. clearbody last. time_simpl. time_pose.
  cbn [interval_bits]. try change (Z.size_nat 1) with 1%nat in *.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_interval_not_time.

(** Every complemented piece is normalized before being joined. *)
Lemma wrapped_not_piece_bits : forall w a,
  (wrapped_bits (wrapped_not_piece w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w [|lo hi].
  - change (0 <= 2 * Pos.to_nat w)%nat. lia.
  - unfold wrapped_not_piece. apply wrapped_of_interval_bits.
Qed.

(** Complementing one piece composes interval complement and normalization. *)
Lemma wrapped_not_piece_time : forall w a,
  (T_wrapped_not_piece w a <=
    65536 * N.of_nat (Pos.to_nat w + interval_bits a + 1))%N.
Proof.
  intros w [|lo hi].
  - time_unfold T_wrapped_not_piece. cbn [interval_bits]. rewrite Nat2N.inj_add. lia.
  - pose proof (wrapped_interval_not_bits w (I lo hi)) as Hbits.
    set (result := WrappedIntervalOps.interval_not w (I lo hi)) in *.
    time_unfold T_wrapped_not_piece. cbn beta iota zeta.
    fold result. clearbody result. time_simpl. time_pose.
    rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_not_piece_time.

(** Word complement splits normalized inputs and joins two normalized results. *)
Lemma wrapped_not_time : forall w a,
  (T_wrapped_not w a <= 1048576 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w a. pose proof (wrapped_parts_bits w a) as [Hleft Hright].
  set (parts := wrapped_parts w a) in *.
  pose proof (wrapped_not_piece_bits w (fst parts)) as Hleftbits.
  pose proof (wrapped_not_piece_bits w (snd parts)) as Hrightbits.
  set (left := wrapped_not_piece w (fst parts)) in *.
  set (right := wrapped_not_piece w (snd parts)) in *.
  time_unfold T_wrapped_not. cbn beta iota zeta.
  fold parts left right. clearbody parts left right. time_simpl. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_not_time.


(** Unsigned word division remains a word, including the integer zero-divisor case. *)
Lemma wrapped_word_div_word : forall w x y,
  is_word w x -> is_word w y -> is_word w (x / y).
Proof.
  intros w x y [Hx0 Hxhi] [Hy0 Hyhi].
  destruct (Z.eq_dec y 0) as [-> | Hynonzero].
  - rewrite Z.div_0_r. unfold is_word. pose proof (modulus_pos w). lia.
  - assert (Hypos : 0 < y) by lia. unfold is_word. split.
    + apply Z.div_pos; lia.
    + eapply Z.le_lt_trans; [|exact Hxhi]. apply Z.div_le_upper_bound; [exact Hypos|].
      replace x with (1 * x) at 1 by ring. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

(** Finite word-shaped intervals store at most the declared width. *)
Lemma wrapped_word_interval_bits : forall w a,
  wrapped_interval_word_shape w a -> (interval_bits a <= Pos.to_nat w)%nat.
Proof.
  intros w a [-> | [lo [hi [-> [Hlo Hhi]]]]].
  - change (0 <= Pos.to_nat w)%nat. lia.
  - change (Nat.max (Z.size_nat lo) (Z.size_nat hi) <= Pos.to_nat w)%nat.
    apply Nat.max_lub; apply WordTime.word_size_bound; assumption.
Qed.

(** Unsigned interval division stores only word-sized quotient endpoints. *)
Lemma wrapped_interval_udiv_bits_word : forall w a b,
  wrapped_interval_word_shape w a -> wrapped_interval_word_shape w b ->
  (interval_bits (WrappedIntervalOps.interval_udiv w a b) <= 3 * Pos.to_nat w)%nat.
Proof.
  intros w a b Ha Hb.
  destruct Ha as [-> | [la [ha [-> [Hla Hha]]]]];
    destruct Hb as [-> | [lb [hb [-> [Hlb Hhb]]]]];
    try (cbn [WrappedIntervalOps.interval_udiv interval_finite_helper];
      pose proof (wrapped_interval_top_bits w); lia).
  pose proof (WordTime.word_size_bound w (la / hb)
    (wrapped_word_div_word w la hb Hla Hhb)) as Hql.
  pose proof (WordTime.word_size_bound w (ha / lb)
    (wrapped_word_div_word w ha lb Hha Hlb)) as Hqr.
  pose proof (wrapped_last_word_bits w) as Hlast.
  pose proof (wrapped_interval_top_bits w) as Htop.
  pose proof (wrapped_interval_checked_bits w (la / hb) (ha / lb)) as Hfirst.
  pose proof (wrapped_interval_checked_bits w (la / hb) (modulus w - 1)) as Hsecond.
  unfold WrappedIntervalOps.interval_udiv. cbn [interval_finite_helper].
  destruct ((0 <=? la) && (0 <? lb))%bool; [exact (ltac:(lia))|].
  destruct ((0 <=? la) && (lb =? 0) && (0 <? hb))%bool; [exact (ltac:(lia))|].
  destruct ((lb =? 0) && (hb =? 0))%bool; [|exact (ltac:(lia))].
  change (Nat.max (Z.size_nat (modulus w - 1)) (Z.size_nat (modulus w - 1)) <=
    3 * Pos.to_nat w)%nat. lia.
Qed.

(** Unsigned interval division performs at most two quadratic word divisions. *)
Lemma wrapped_interval_udiv_time_word : forall w a b,
  wrapped_interval_word_shape w a -> wrapped_interval_word_shape w b ->
  (WrappedIntervalOps.T_interval_udiv w a b <=
    16384 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
Proof.
  intros w a b Ha Hb.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    (Nat.le_refl _) (ltac:(lia))) as Hfloor.
  destruct Ha as [-> | [la [ha [-> [Hla Hha]]]]];
    destruct Hb as [-> | [lb [hb [-> [Hlb Hhb]]]]];
    try (time_unfold WrappedIntervalOps.T_interval_udiv;
      cbn beta iota zeta; cbn [interval_finite_helper]; time_simpl; time_pose;
      rewrite !Nat2N.inj_add in *; lia).
  pose proof (WordTime.word_size_bound w la Hla) as Hlabits.
  pose proof (WordTime.word_size_bound w ha Hha) as Hhabits.
  pose proof (WordTime.word_size_bound w lb Hlb) as Hlbbits.
  pose proof (WordTime.word_size_bound w hb Hhb) as Hhbbits.
  pose proof (WordTime.integer_div_word_time_bound w la hb Hla Hhb) as Hlefttime.
  pose proof (WordTime.integer_div_word_time_bound w ha lb Hha Hlb) as Hrighttime.
  pose proof (WordTime.word_size_bound w (la / hb)
    (wrapped_word_div_word w la hb Hla Hhb)) as Hqlbits.
  pose proof (WordTime.word_size_bound w (ha / lb)
    (wrapped_word_div_word w ha lb Hha Hlb)) as Hqrbits.
  pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
  pose proof (WordTime.word_modulus_size_bound w) as Hmodulusbits.
  pose proof (wrapped_last_word_bits w) as Hlastbits.
  set (ql := la / hb) in *.
  set (qr := ha / lb) in *.
  set (last := modulus w - 1) in *.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  time_unfold WrappedIntervalOps.T_interval_udiv.
  cbn beta iota zeta. cbn [interval_finite_helper].
  fold ql qr last. clearbody ql qr last square. time_simpl. time_pose.
  repeat match goal with |- context [if ?choice then _ else _] => destruct choice end;
    try change (Z.size_nat 0) with 0%nat in *;
    try change (Z.size_nat 1) with 1%nat in *;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Remainder endpoints use one quotient product and one subtraction. *)
Lemma wrapped_interval_urem_bits_word : forall w a b,
  wrapped_interval_word_shape w a -> wrapped_interval_word_shape w b ->
  (interval_bits (WrappedIntervalOps.interval_urem w a b) <=
    7 * Pos.to_nat w + 2)%nat.
Proof.
  intros w a b Ha Hb.
  destruct Ha as [-> | [la [ha [-> [Hla Hha]]]]];
    destruct Hb as [-> | [lb [hb [-> [Hlb Hhb]]]]];
    try (cbn [WrappedIntervalOps.interval_urem interval_finite_helper];
      pose proof (wrapped_interval_top_bits w); lia).
  pose proof (WordTime.word_size_bound w la Hla) as Hlabits.
  pose proof (WordTime.word_size_bound w ha Hha) as Hhabits.
  pose proof (WordTime.word_size_bound w lb Hlb) as Hlbbits.
  pose proof (WordTime.word_size_bound w hb Hhb) as Hhbbits.
  pose proof (WordTime.word_size_bound w (la / hb)
    (wrapped_word_div_word w la hb Hla Hhb)) as Hqbits.
  pose proof (WordTime.integer_mul_size (la / hb) hb) as Hplbits.
  pose proof (WordTime.integer_mul_size (la / hb) lb) as Hprbits.
  pose proof (WordTime.integer_sub_size la ((la / hb) * hb)) as Hleftbits.
  pose proof (WordTime.integer_sub_size ha ((la / hb) * lb)) as Hrightbits.
  pose proof (WordTime.integer_sub_size hb 1) as Hlastbits.
  pose proof (wrapped_min_bits ha (hb - 1)) as Hminbits.
  pose proof (wrapped_interval_checked_bits w (la - (la / hb) * hb)
    (ha - (la / hb) * lb)) as Hfirst.
  pose proof (wrapped_interval_checked_bits w 0 (Z.min ha (hb - 1))) as Hsecond.
  pose proof (wrapped_interval_checked_bits w 0 ha) as Hthird.
  try change (Z.size_nat 0) with 0%nat in *.
  try change (Z.size_nat 1) with 1%nat in *.
  unfold WrappedIntervalOps.interval_urem. cbn [interval_finite_helper].
  destruct ((0 <=? la) && (0 <? lb) && (la / hb =? ha / lb))%bool;
    [exact (ltac:(lia))|].
  destruct (0 <? lb); lia.
Qed.

(** Interval remainder has a fixed number of word divisions and multiplications. *)
Lemma wrapped_interval_urem_time_word : forall w a b,
  wrapped_interval_word_shape w a -> wrapped_interval_word_shape w b ->
  (WrappedIntervalOps.T_interval_urem w a b <=
    32768 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
Proof.
  intros w a b Ha Hb.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    (Nat.le_refl _) (ltac:(lia))) as Hfloor.
  destruct Ha as [-> | [la [ha [-> [Hla Hha]]]]];
    destruct Hb as [-> | [lb [hb [-> [Hlb Hhb]]]]];
    try (time_unfold WrappedIntervalOps.T_interval_urem;
      cbn beta iota zeta; cbn [interval_finite_helper]; time_simpl; time_pose;
      rewrite !Nat2N.inj_add in *; lia).
  pose proof (WordTime.word_size_bound w la Hla) as Hlabits.
  pose proof (WordTime.word_size_bound w ha Hha) as Hhabits.
  pose proof (WordTime.word_size_bound w lb Hlb) as Hlbbits.
  pose proof (WordTime.word_size_bound w hb Hhb) as Hhbbits.
  pose proof (wrapped_word_div_word w la hb Hla Hhb) as Hquotient.
  pose proof (WordTime.word_size_bound w (la / hb) Hquotient) as Hqbits.
  pose proof (WordTime.word_size_bound w (ha / lb)
    (wrapped_word_div_word w ha lb Hha Hlb)) as Hqrbits.
  pose proof (WordTime.integer_div_word_time_bound w la hb Hla Hhb) as Hlefttime.
  pose proof (WordTime.integer_div_word_time_bound w ha lb Hha Hlb) as Hrighttime.
  pose proof (WordTime.integer_mul_word_time_bound w (la / hb) hb Hquotient Hhb) as Hpltime.
  pose proof (WordTime.integer_mul_word_time_bound w (la / hb) lb Hquotient Hlb) as Hprtime.
  pose proof (WordTime.integer_mul_size (la / hb) hb) as Hplbits.
  pose proof (WordTime.integer_mul_size (la / hb) lb) as Hprbits.
  pose proof (WordTime.integer_sub_size la ((la / hb) * hb)) as Hleftbits.
  pose proof (WordTime.integer_sub_size ha ((la / hb) * lb)) as Hrightbits.
  pose proof (WordTime.integer_sub_size hb 1) as Hlastbits.
  pose proof (wrapped_min_bits ha (hb - 1)) as Hminbits.
  set (ql := la / hb) in *.
  set (qr := ha / lb) in *.
  set (pl := ql * hb) in *.
  set (pr := ql * lb) in *.
  set (left := la - pl) in *.
  set (right := ha - pr) in *.
  set (last := hb - 1) in *.
  set (low := Z.min ha last) in *.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  time_unfold WrappedIntervalOps.T_interval_urem.
  cbn beta iota zeta. cbn [interval_finite_helper].
  fold ql qr pl pr left right last low.
  clearbody ql qr pl pr left right last low square. time_simpl. time_pose.
  repeat match goal with |- context [if ?choice then _ else _] => destruct choice end;
    try change (Z.size_nat 0) with 0%nat in *;
    try change (Z.size_nat 1) with 1%nat in *;
    rewrite !Nat2N.inj_add in *; lia.
Qed.


(** A normalized quotient or remainder piece stores at most two word endpoints. *)
Lemma wrapped_div_piece_bits : forall remainder w a b,
  (wrapped_bits (wrapped_div_piece remainder w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros remainder w [|la ha] [|lb hb];
    try (change (0 <= 2 * Pos.to_nat w)%nat; lia).
  unfold wrapped_div_piece. apply wrapped_of_interval_bits.
Qed.

(** Division of word-shaped pieces charges a fixed quadratic word budget. *)
Lemma wrapped_div_piece_time_word : forall remainder w a b,
  wrapped_interval_word_shape w a -> wrapped_interval_word_shape w b ->
  (T_wrapped_div_piece remainder w a b <=
    262144 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
Proof.
  intros remainder w a b Ha Hb.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    (Nat.le_refl _) (ltac:(lia))) as Hfloor.
  destruct a as [|la ha], b as [|lb hb];
    try (time_unfold T_wrapped_div_piece; cbn beta iota zeta;
      rewrite !Nat2N.inj_add in *; lia).
  pose proof (wrapped_interval_udiv_time_word w (I la ha) (I lb hb) Ha Hb) as Hdivision.
  pose proof (wrapped_interval_urem_time_word w (I la ha) (I lb hb) Ha Hb) as Hremainder.
  pose proof (wrapped_interval_udiv_bits_word w (I la ha) (I lb hb) Ha Hb) as Hdivisionbits.
  pose proof (wrapped_interval_urem_bits_word w (I la ha) (I lb hb) Ha Hb) as Hremainderbits.
  set (u := WrappedIntervalOps.interval_udiv w (I la ha) (I lb hb)) in *.
  set (r := WrappedIntervalOps.interval_urem w (I la ha) (I lb hb)) in *.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  time_unfold T_wrapped_div_piece. cbn beta iota zeta.
  fold u r. clearbody u r square.
  destruct remainder; cbn beta iota zeta; time_simpl; time_pose;
    rewrite !Nat2N.inj_add in *; lia.
Qed.

(** Pole-clipped division joins four normalized result pieces. *)
Lemma wrapped_div_cut_bits : forall remainder w a b,
  (wrapped_bits (wrapped_div_cut remainder w a b) <= 2 * Pos.to_nat w)%nat.
Proof. intros. unfold wrapped_div_cut. apply wrapped_join_four_bits. Qed.

(** Pole clipping separates raw input costs from quadratic word arithmetic. *)
Lemma wrapped_div_cut_time : forall remainder w a b,
  (T_wrapped_div_cut remainder w a b <= 33554432 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + interval_bits a + interval_bits b))%N.
Proof.
  intros remainder w a b.
  pose proof (wrapped_pole_cut_word_shape w a) as [Ha0 Ha1].
  pose proof (wrapped_pole_cut_word_shape w b) as [Hb0 Hb1].
  set (pa := wrapped_pole_cut w a) in *.
  set (pb := wrapped_pole_cut w b) in *.
  pose proof (wrapped_div_piece_time_word remainder w (fst pa) (fst pb) Ha0 Hb0) as HT00.
  pose proof (wrapped_div_piece_time_word remainder w (fst pa) (snd pb) Ha0 Hb1) as HT01.
  pose proof (wrapped_div_piece_time_word remainder w (snd pa) (fst pb) Ha1 Hb0) as HT10.
  pose proof (wrapped_div_piece_time_word remainder w (snd pa) (snd pb) Ha1 Hb1) as HT11.
  pose proof (wrapped_div_piece_bits remainder w (fst pa) (fst pb)) as H00.
  pose proof (wrapped_div_piece_bits remainder w (fst pa) (snd pb)) as H01.
  pose proof (wrapped_div_piece_bits remainder w (snd pa) (fst pb)) as H10.
  pose proof (wrapped_div_piece_bits remainder w (snd pa) (snd pb)) as H11.
  set (r00 := wrapped_div_piece remainder w (fst pa) (fst pb)) in *.
  set (r01 := wrapped_div_piece remainder w (fst pa) (snd pb)) in *.
  set (r10 := wrapped_div_piece remainder w (snd pa) (fst pb)) in *.
  set (r11 := wrapped_div_piece remainder w (snd pa) (snd pb)) in *.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    (Nat.le_refl _) (ltac:(lia))) as Hfloor.
  rewrite !Nat2N.inj_add in *.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  time_unfold T_wrapped_div_cut. cbn beta iota zeta.
  fold pa pb r00 r01 r10 r11.
  clearbody pa pb r00 r01 r10 r11 square. time_simpl. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_div_cut_time.

(** Circular division separates raw endpoint normalization from bounded word pieces. *)
Lemma wrapped_div_time : forall remainder w a b,
  (T_wrapped_div remainder w a b <= 1073741824 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
Proof.
  intros remainder w a b.
  pose proof (wrapped_parts_bits w a) as [Ha0 Ha1].
  pose proof (wrapped_parts_bits w b) as [Hb0 Hb1].
  set (pa := wrapped_parts w a) in *.
  set (pb := wrapped_parts w b) in *.
  pose proof (wrapped_div_cut_time remainder w (fst pa) (fst pb)) as HT00.
  pose proof (wrapped_div_cut_time remainder w (fst pa) (snd pb)) as HT01.
  pose proof (wrapped_div_cut_time remainder w (snd pa) (fst pb)) as HT10.
  pose proof (wrapped_div_cut_time remainder w (snd pa) (snd pb)) as HT11.
  pose proof (wrapped_div_cut_bits remainder w (fst pa) (fst pb)) as H00.
  pose proof (wrapped_div_cut_bits remainder w (fst pa) (snd pb)) as H01.
  pose proof (wrapped_div_cut_bits remainder w (snd pa) (fst pb)) as H10.
  pose proof (wrapped_div_cut_bits remainder w (snd pa) (snd pb)) as H11.
  set (r00 := wrapped_div_cut remainder w (fst pa) (fst pb)) in *.
  set (r01 := wrapped_div_cut remainder w (fst pa) (snd pb)) in *.
  set (r10 := wrapped_div_cut remainder w (snd pa) (fst pb)) in *.
  set (r11 := wrapped_div_cut remainder w (snd pa) (snd pb)) in *.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
    (Nat.le_refl _) (ltac:(lia))) as Hfloor.
  rewrite !Nat2N.inj_add in *.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  time_unfold T_wrapped_div. cbn beta iota zeta.
  fold pa pb r00 r01 r10 r11.
  clearbody pa pb r00 r01 r10 r11 square. time_simpl. time_pose.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_div_time.

(** Unsigned quotient dispatch adds one fixed step to circular division. *)
Lemma wrapped_udiv_time : forall w a b,
  (T_wrapped_udiv w a b <= 2147483648 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
Proof.
  intros w a b. pose proof (wrapped_div_time false w a b) as Htime.
  pose proof (WordTime.time_square_floor 1 (Pos.to_nat w + 1)
    (ltac:(lia)) (ltac:(lia))) as Hpositive.
  time_unfold T_wrapped_udiv. cbn beta iota zeta. time_simpl.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_udiv_time.

(** Unsigned remainder dispatch adds one fixed step to circular division. *)
Lemma wrapped_urem_time : forall w a b,
  (T_wrapped_urem w a b <= 2147483648 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
Proof.
  intros w a b. pose proof (wrapped_div_time true w a b) as Htime.
  pose proof (WordTime.time_square_floor 1 (Pos.to_nat w + 1)
    (ltac:(lia)) (ltac:(lia))) as Hpositive.
  time_unfold T_wrapped_urem. cbn beta iota zeta. time_simpl.
  rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_urem_time.

(** * Linear clocks for prepared masks *)

(** A prepared word mask charges only the bitwise intersection. *)
Lemma arc_wrap_m_time : forall w z,
  (T_arc_wrap_m (Z.ones (Zpos w)) z <=
    32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z.
  pose proof (WordTime.word_size_bound w _ (arc_ones_word w)) as Hbits.
  pose proof (Std.Z.T_land_le z (Z.ones (Zpos w))) as Hland.
  time_unfold T_arc_wrap_m. rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound arc_wrap_m_time.

(** Prepared circular offsets have the original linear endpoint budget. *)
Lemma wrapped_offset_m_time : forall w origin x,
  (T_wrapped_offset_m (Z.ones (Zpos w)) w origin x <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat origin + Z.size_nat x + 1))%N.
Proof.
  intros w origin x.
  pose proof (arc_wrap_m_time w (x - origin)) as Hwrap.
  pose proof (Std.Z.T_sub_le x origin) as Hsub.
  pose proof (WordTime.integer_sub_size x origin) as Hbits.
  time_unfold T_wrapped_offset_m. rewrite !Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_offset_m_time.

(** Prepared offsets are word-sized independently of their raw endpoints. *)
Lemma wrapped_offset_m_bits : forall w origin x,
  (Z.size_nat (wrapped_offset_m (Z.ones (Zpos w)) w origin x) <= Pos.to_nat w)%nat.
Proof.
  intros w origin x. rewrite wrapped_offset_m_agrees. apply wrapped_offset_bits.
Qed.

(** Prepared cardinality costs linear work in the width and stored endpoints. *)
Lemma wrapped_size_m_time : forall w a,
  (T_wrapped_size_m (Z.ones (Zpos w)) w a <=
    256 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi].
  - time_unfold T_wrapped_size_m. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - pose proof (WordTime.word_size_bound w _ (arc_ones_word w)) as Hbits.
    pose proof (Std.Z.T_add_le (Z.ones (Zpos w)) 1) as Hadd.
    time_unfold T_wrapped_size_m. cbn [wrapped_bits].
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  - pose proof (wrapped_offset_m_time w lo hi) as Hoffset.
    pose proof (wrapped_offset_m_bits w lo hi) as Hbits.
    pose proof (Std.Z.T_add_le (wrapped_offset_m (Z.ones (Zpos w)) w lo hi) 1) as Hadd.
    time_unfold T_wrapped_size_m. cbn [wrapped_bits].
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
Qed.
TimeBound wrapped_size_m_time.

(** Prepared cardinality has the original width-dependent bit bound. *)
Lemma wrapped_size_m_bits : forall w a,
  (Z.size_nat (wrapped_size_m (Z.ones (Zpos w)) w a) <= Pos.to_nat w + 1)%nat.
Proof.
  intros w a. rewrite wrapped_size_m_agrees. apply wrapped_size_bits.
Qed.

(** Prepared normalization retains the original linear time budget. *)
Lemma wrapped_norm_m_time : forall w a,
  (T_wrapped_norm_m (Z.ones (Zpos w)) w a <=
    512 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi].
  - time_unfold T_wrapped_norm_m. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - time_unfold T_wrapped_norm_m. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - pose proof (wrapped_offset_m_time w lo hi) as Hoffset.
    pose proof (wrapped_offset_m_bits w lo hi) as Hoffsetbits.
    pose proof (WordTime.word_size_bound w _ (arc_ones_word w)) as Hmaskbits.
    pose proof (Std.Z.T_eqb_le (wrapped_offset_m (Z.ones (Zpos w)) w lo hi)
      (Z.ones (Zpos w))) as Hequal.
    pose proof (arc_wrap_m_time w lo) as Hlo.
    pose proof (arc_wrap_m_time w hi) as Hhi.
    time_unfold T_wrapped_norm_m. cbn [wrapped_bits].
    destruct (wrapped_offset_m (Z.ones (Zpos w)) w lo hi =? Z.ones (Zpos w));
      rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_norm_m_time.

(** Short-circuit inclusion charges at most four prepared circular offsets. *)
Lemma wrapped_leb_m_time : forall w a b,
  (T_wrapped_leb_m (Z.ones (Zpos w)) w a b <=
    1024 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intro w.
  pose proof (WordTime.word_size_bound w _ (arc_ones_word w)) as Hmaskbits.
  intros [| |la ha] [| |lb hb]; time_unfold T_wrapped_leb_m; cbn [wrapped_bits].
  all: try (rewrite !Nat2N.inj_add in *; lia).
  - pose proof (wrapped_offset_m_bits w lb hb) as Hbits.
    time_pose. rewrite !Nat2N.inj_add in *. lia.
  - pose proof (wrapped_offset_m_bits w lb hb) as Hcoverbits.
    pose proof (wrapped_offset_m_bits w lb la) as Hstartbits.
    pose proof (wrapped_offset_m_bits w la ha) as Hlengthbits.
    pose proof (WordTime.integer_add_size
      (wrapped_offset_m (Z.ones (Zpos w)) w lb la)
      (wrapped_offset_m (Z.ones (Zpos w)) w la ha)) as Hsumbits.
    time_pose.
    destruct (wrapped_offset_m (Z.ones (Zpos w)) w lb hb =? Z.ones (Zpos w));
      rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_leb_m_time.

(** Prepared cover checking short-circuits after a failed first inclusion. *)
Lemma wrapped_cover_m_time : forall w a b candidate,
  (T_wrapped_cover_m (Z.ones (Zpos w)) w a b candidate <= 4096 * N.of_nat
    (Pos.to_nat w + wrapped_bits a + wrapped_bits b + wrapped_bits candidate + 1))%N.
Proof.
  intros w a b candidate. time_unfold T_wrapped_cover_m. time_pose.
  destruct (wrapped_leb_m (Z.ones (Zpos w)) w a candidate);
    rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_cover_m_time.

(** Prepared selection returns one of its candidates or the full circle. *)
Lemma wrapped_choose_m_bits : forall m w a b first second,
  (wrapped_bits (wrapped_choose_m m w a b first second) <=
    wrapped_bits first + wrapped_bits second)%nat.
Proof.
  intros m w a b first second. unfold wrapped_choose_m.
  destruct (wrapped_cover_m m w a b first), (wrapped_cover_m m w a b second),
    (wrapped_size_m m w first <=? wrapped_size_m m w second); cbn [wrapped_bits]; lia.
Qed.

(** Prepared selection retains the original linear input and candidate budget. *)
Lemma wrapped_choose_m_time : forall w a b first second,
  (T_wrapped_choose_m (Z.ones (Zpos w)) w a b first second <= 16384 * N.of_nat
    (Pos.to_nat w + wrapped_bits a + wrapped_bits b +
      wrapped_bits first + wrapped_bits second + 1))%N.
Proof.
  intros w a b first second.
  pose proof (wrapped_size_m_bits w first) as Hfirstbits.
  time_unfold T_wrapped_choose_m. time_pose.
  destruct (wrapped_cover_m (Z.ones (Zpos w)) w a b first),
    (wrapped_cover_m (Z.ones (Zpos w)) w a b second),
    (wrapped_size_m (Z.ones (Zpos w)) w first <=?
      wrapped_size_m (Z.ones (Zpos w)) w second);
    rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_choose_m_time.

(** Prepared join candidates contain only endpoint magnitudes from their inputs. *)
Lemma wrapped_join_m_candidate_bits : forall m w a b,
  (wrapped_bits
    (if wrapped_leb_m m w a b then b else
     if wrapped_leb_m m w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose_m m w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end) <= wrapped_bits a + wrapped_bits b)%nat.
Proof.
  intros m w a b.
  destruct (wrapped_leb_m m w a b), (wrapped_leb_m m w b a); try lia.
  destruct a as [| |lo hi], b as [| |lo' hi']; cbn [wrapped_bits]; try lia.
  pose proof (wrapped_choose_m_bits m w (WItv lo hi) (WItv lo' hi')
    (WItv lo hi') (WItv lo' hi)) as Hbits. cbn [wrapped_bits] in Hbits. lia.
Qed.

(** Prepared joining retains the original linear budget for both raw arcs. *)
Lemma wrapped_join_m_time : forall w a b,
  (T_wrapped_join_m (Z.ones (Zpos w)) w a b <=
    65536 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w a b.
  pose proof (wrapped_join_m_candidate_bits (Z.ones (Zpos w)) w a b) as Hcandidate.
  time_unfold T_wrapped_join_m.
  destruct (wrapped_leb_m (Z.ones (Zpos w)) w a b).
  - cbn beta iota zeta. time_pose. rewrite !Nat2N.inj_add in *. lia.
  - destruct (wrapped_leb_m (Z.ones (Zpos w)) w b a).
    + cbn beta iota zeta. time_pose. rewrite !Nat2N.inj_add in *. lia.
    + destruct a as [| |lo hi], b as [| |lo' hi'];
        cbn beta iota zeta; time_pose; cbn [wrapped_bits] in *;
        rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_join_m_time.

(** Prepared expansion shares its mask with cardinality and endpoint normalization. *)
Lemma wrapped_double_m_time : forall w a,
  (T_wrapped_double_m (Z.ones (Zpos w)) w a <=
    4096 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi].
  - time_unfold T_wrapped_double_m. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - time_unfold T_wrapped_double_m. cbn [wrapped_bits]. rewrite Nat2N.inj_add. lia.
  - pose proof (WordTime.word_size_bound w _ (arc_ones_word w)) as Hmaskbits.
    assert (Hmodulusbits : (Z.size_nat (Z.ones (Zpos w) + 1) <= Pos.to_nat w + 1)%nat).
    { rewrite arc_mask_modulus. apply WordTime.word_modulus_size_bound. }
    pose proof (wrapped_size_m_bits w (WItv lo hi)) as Hsizebits.
    pose proof (WordTime.integer_sub_size lo
      (wrapped_size_m (Z.ones (Zpos w)) w (WItv lo hi))) as Hlobits.
    pose proof (WordTime.integer_add_size hi
      (wrapped_size_m (Z.ones (Zpos w)) w (WItv lo hi))) as Hhibits.
    time_unfold T_wrapped_double_m. cbn beta iota zeta. time_pose.
    destruct (Z.ones (Zpos w) + 1 <=?
      3 * wrapped_size_m (Z.ones (Zpos w)) w (WItv lo hi));
      cbn [wrapped_bits] in *; rewrite !Nat2N.inj_add in *; time_cbn_all; lia.
Qed.
TimeBound wrapped_double_m_time.

(** Prepared narrowing charges at most the two input normalizations. *)
Lemma wrapped_narrow_m_time : forall w a b,
  (T_wrapped_narrow_m (Z.ones (Zpos w)) w a b <=
    2048 * N.of_nat (Pos.to_nat w + wrapped_bits a + wrapped_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_wrapped_narrow_m. cbn beta iota zeta. time_pose.
  destruct (wrapped_norm_m (Z.ones (Zpos w)) w a);
    rewrite !Nat2N.inj_add in *; lia.
Qed.
TimeBound wrapped_narrow_m_time.


Module Wrapped (L : WORD_LANGUAGE) <: WRAPPED L.
  Include WrappedCode L.
  Include WRAPPED_SPEC L.

  (** The payload comparison shares a mask without changing circular inclusion. *)
  Lemma pleb_agrees : forall w a b, pleb w a b = wrapped_leb w a b.
  Proof.
    intros w a b. unfold pleb.
    destruct a, b; try reflexivity; apply wrapped_leb_m_agrees.
  Qed.

  (** The payload join chooses the same normalized circular cover. *)
  Lemma pjoin_agrees : forall w a b, pjoin w a b = wrapped_join w a b.
  Proof.
    intros w a b. unfold pjoin.
    destruct a, b; try reflexivity; apply wrapped_join_m_agrees.
  Qed.

  (** Shared-mask widening keeps the original raw arc when it is stable. *)
  Lemma pwiden_agrees : forall q w a b,
    pwiden q w a b =
      if wrapped_leb w b a then a else wrapped_join w (wrapped_double w a) b.
  Proof.
    intros q w a b. unfold pwiden.
    destruct a, b; cbn beta iota zeta; try reflexivity.
    all: rewrite ?wrapped_leb_m_agrees, ?wrapped_double_m_agrees,
      ?wrapped_join_m_agrees; reflexivity.
  Qed.

  (** Shared-mask narrowing agrees with the original normalization rule. *)
  Lemma pnarrow_agrees : forall w a b, pnarrow w a b = wrapped_narrow w a b.
  Proof.
    intros w a b. unfold pnarrow.
    destruct a, b; try reflexivity; apply wrapped_narrow_m_agrees.
  Qed.

  Definition pgamma := arc_gamma.
  Definition pwrank (_ : pwparam) (w : positive) (a : p) : nat := size_rank w (card w a).
  (** The public arc meaning agrees with the checked circular helpers. *)
  Lemma pgamma_wrapped : forall w a z, pgamma w a z <-> wrapped_gamma w a z.
  Proof.
    intros w [| |lo hi] z; cbn [pgamma arc_gamma wrapped_gamma]; try reflexivity.
    unfold offset, wrapped_offset. rewrite !arc_wrap_mod. reflexivity.
  Qed.

  (** Public cardinality is the size used by circular expansion. *)
  Lemma card_wrapped_size : forall w a, card w a = wrapped_size w a.
  Proof.
    intros w [| |lo hi]; cbn [card wrapped_size]; try reflexivity.
    unfold offset, wrapped_offset. rewrite arc_wrap_mod. reflexivity.
  Qed.

  (** Natural widening credit is the nonnegative logarithmic size rank. *)
  Lemma pwrank_wrapped : forall q w a,
    pwrank q w a = Z.to_nat (wrapped_size_rank w (wrapped_size w a)).
  Proof.
    intros q w a. unfold pwrank. rewrite card_wrapped_size. reflexivity.
  Qed.

  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof.
    intros q w a b. rewrite pleb_agrees, pwiden_agrees.
    destruct (wrapped_leb w b a) eqn:Hcontained.
    - apply wrapped_leb_refl.
    - eapply wrapped_leb_trans; [apply wrapped_double_upper|].
      exact (proj1 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w _ b))).
  Qed.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w a b. rewrite pleb_agrees, pwiden_agrees.
    destruct (wrapped_leb w b a) eqn:Hcontained.
    - exact Hcontained.
    - exact (proj2 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w _ b))).
  Qed.
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof.
    intros q w a b Hcontained. rewrite pleb_agrees in Hcontained.
    now rewrite pwiden_agrees, Hcontained.
  Qed.
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w a b Hnonbottom Hescape.
    rewrite pleb_agrees in Hescape.
    rewrite !pwrank_wrapped, pwiden_agrees, Hescape.
    pose proof (wrapped_size_bounds w a) as Hold.
    assert (Hproper : wrapped_size w a < modulus w).
    { destruct (Z.eq_dec (wrapped_size w a) (modulus w)) as [Hfull|Hproper]; [|lia].
      pose proof (wrapped_full_contains w a b Hfull). congruence. }
    destruct (wrapped_widen_size_progress w a b Hescape) as [Hnext Hgrow].
    unfold wrapped_widen in Hnext, Hgrow. rewrite Hescape in Hnext, Hgrow.
    pose proof (wrapped_size_rank_progress w (wrapped_size w a)
      (wrapped_size w (wrapped_join w (wrapped_double w a) b))
      ltac:(lia) Hnext Hgrow) as Hrank.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w a) Hold) as Hrank_old.
    pose proof (wrapped_size_rank_bounds w
      (wrapped_size w (wrapped_join w (wrapped_double w a) b))
      (wrapped_size_bounds w (wrapped_join w (wrapped_double w a) b))) as Hrank_next.
    change (Z.to_nat (wrapped_size_rank w
      (wrapped_size w (wrapped_join w (wrapped_double w a) b))) <
      Z.to_nat (wrapped_size_rank w (wrapped_size w a)))%nat.
    apply Z2Nat.inj_lt; lia.
  Qed.
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof.
    intros q w a b Hnonbottom. destruct (pleb w b a) eqn:Hcontained.
    - rewrite pwiden_stable by exact Hcontained. lia.
    - pose proof (pwrank_widen q w a b Hnonbottom Hcontained). lia.
  Qed.
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof.
    intros w a b. rewrite !pleb_agrees, !pnarrow_agrees.
    apply wrapped_narrow_between.
  Qed.
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof.
    intros w a. rewrite pleb_agrees.
    apply wrapped_leb_refl.
  Qed.
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w a b c. rewrite !pleb_agrees.
    apply wrapped_leb_trans.
  Qed.
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof.
    intros w a. reflexivity.
  Qed.
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof.
    intros w [| |lo hi]; reflexivity.
  Qed.
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof.
    intro w. reflexivity.
  Qed.
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof.
    intros w [| |lo hi] b Hbottom; try discriminate. reflexivity.
  Qed.
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof.
    intros w a b. rewrite pleb_agrees, pjoin_agrees.
    exact (proj1 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w a b))).
  Qed.
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof.
    intros w a b. rewrite pleb_agrees, pjoin_agrees.
    exact (proj2 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w a b))).
  Qed.
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.
    intros w a b. rewrite pleb_agrees.
    apply wrapped_meet_lower_left.
  Qed.
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w a b z Hle. rewrite !pgamma_wrapped.
    rewrite pleb_agrees in Hle.
    exact (proj1 (wrapped_leb_spec w a b) Hle z).
  Qed.
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof.
    intros w z Hempty. exact Hempty.
  Qed.
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof.
    intros w z Hword. exact Hword.
  Qed.
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    intros w a b z. rewrite !pgamma_wrapped. apply wrapped_meet_sound.
  Qed.
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w [| |lo hi] z Hbottom; try discriminate. intro Hempty. exact Hempty.
  Qed.
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof.
    intros w [| |la ha] [| |lb hb] Hle Hbottom; try discriminate. reflexivity.
  Qed.
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros w z. rewrite pgamma_wrapped. unfold pconst.
    apply wrapped_norm_gamma. split; [apply wrap_is_word|].
    rewrite wrapped_offset_word, wrapped_offset_self. lia.
  Qed.
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof.
    intros w a z v Hpoint Hword Hgamma. apply pgamma_wrapped in Hgamma.
    exact (wrapped_point_sound w a z v Hgamma Hpoint).
  Qed.
  Lemma gamma_arc : forall w a z, pgamma w a z <-> arc_gamma w a z.
  Proof. intros; reflexivity. Qed.
  Lemma wrapped_neg_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvneg ((w, x) :: nil) = Some (w, z) -> pgamma w (wrapped_neg w a) z.
  Proof.
    intros w a x z Hword Hgamma Heval.
    change (eval_op bvneg [(w, x)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun1 bvneg w x UNeg eq_refl) in Heval.
    cbn [eval_unary_tag] in Heval. inversion Heval; subst z.
    rewrite pgamma_wrapped in *. rewrite wneg_value. now apply wrapped_neg_sound.
  Qed.
  Lemma wrapped_add_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvadd ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (wrapped_add w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvadd [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvadd w x y BAdd eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst z.
    rewrite !pgamma_wrapped in *. rewrite wadd_value. now apply wrapped_add_sound.
  Qed.
  Lemma wrapped_sub_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvsub ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (wrapped_sub w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvsub [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvsub w x y BSub eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst z.
    rewrite !pgamma_wrapped in *. rewrite wsub_value. now apply wrapped_sub_sound.
  Qed.
  Lemma wrapped_mul_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvmul ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (wrapped_mul w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvmul [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvmul w x y BMul eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst z.
    rewrite !pgamma_wrapped in *.
    unfold wrapped_mul. rewrite wrapped_mul_fast_agrees. now apply wrapped_mul_sound.
  Qed.
End Wrapped.

Module WrappedT (L : WORD_LANGUAGE_T) <: WRAPPED_ALL L.
  Include Wrapped L.
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
  TimeFun wrapped_norm.
  TimeFun wrapped_double.
  TimeFun wrapped_neg.
  TimeFun wrapped_not.
  TimeFun wrapped_add.
  TimeFun wrapped_sub.
  TimeFun wrapped_mul.
  TimeFun wrapped_udiv.
  TimeFun wrapped_urem.
  TimeFun wrapped_split.

  Definition psize (w : positive) (a : p) : nat := Pos.to_nat w + wrapped_bits a + 1.
  Definition pwsize (_ : pwparam) : nat := 0.
  Definition c_payload : N := 67108864.
  Definition c_wrapped : N := 1125899906842624.

  (** Constructing top fits the published width cost. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_ptop. unfold c_payload. cbn [Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul. nia.
  Qed.
  (** Constructing bottom fits the published width cost. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_pbot. unfold c_payload. cbn [Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul. nia.
  Qed.
  (** Top payload storage fits the published width cost. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold c_payload, psize, ptop. cbn [wrapped_bits Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul. nia.
  Qed.
  (** Bottom payload storage fits the published width cost. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold c_payload, psize, pbot. cbn [wrapped_bits Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul. nia.
  Qed.
  (** Constant payload storage fits its construction budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (wrapped_norm_bits w (WItv z z)) as Hbits.
    pose proof (Pos2Nat.is_pos w) as Hwidth.
    unfold c_payload, psize, pconst. cbn [Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.
  (** Joined payload storage fits the combined input budget. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_join_bits w a b) as Hbits.
    rewrite pjoin_agrees. unfold c_payload, psize. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Met payload storage fits the combined input budget. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_meet_bits w a b) as Hbits.
    unfold c_payload, psize, pmeet. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Widened storage fits both inputs and its parameter. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b. rewrite pwiden_agrees. destruct (wrapped_leb w b a).
    - unfold c_payload, psize, pwsize. rewrite !Nat2N.inj_add in *. lia.
    - pose proof (wrapped_join_bits w (wrapped_double w a) b) as Hbits.
      unfold c_payload, psize, pwsize. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Narrowed storage fits both inputs. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_narrow_bits w a b) as Hbits.
    rewrite pnarrow_agrees. unfold c_payload, psize. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Payload widening charges both values and the parameter. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b.
    pose proof (arc_ones_time w) as Hmask.
    pose proof (wrapped_leb_m_time w b a) as Hcompare.
    pose proof (wrapped_double_m_time w a) as Hdouble.
    pose proof (wrapped_double_bits w a) as Hdoublebits.
    pose proof (wrapped_join_m_time w (wrapped_double w a) b) as Hjoin.
    unfold wrapped_double in Hjoin.
    destruct (wrapped_leb w b a) eqn:Hcontained;
      destruct a, b; time_unfold T_pwiden; cbn beta iota zeta;
      rewrite ?wrapped_double_m_agrees, ?wrapped_leb_m_agrees, ?Hcontained;
      time_simpl; unfold c_payload, psize, pwsize;
      rewrite !Nat2N.inj_add in *; lia.
  Qed.
  (** Payload narrowing charges both input values. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_narrow_m_time w a b) as Htime.
    pose proof (arc_ones_time w) as Hmask.
    destruct a, b; time_unfold T_pnarrow; cbn beta iota zeta;
      time_simpl; unfold c_payload, psize; rewrite !Nat2N.inj_add in *; lia.
  Qed.
  (** Payload comparison charges both values. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_leb_m_time w a b) as Htime.
    pose proof (arc_ones_time w) as Hmask.
    destruct a, b; time_unfold T_pleb; cbn beta iota zeta;
      time_simpl; unfold c_payload, psize; rewrite !Nat2N.inj_add in *; lia.
  Qed.
  (** Payload join charges both values. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_join_m_time w a b) as Htime.
    pose proof (arc_ones_time w) as Hmask.
    destruct a, b; time_unfold T_pjoin; cbn beta iota zeta;
      time_simpl; unfold c_payload, psize; rewrite !Nat2N.inj_add in *; lia.
  Qed.
  (** Payload meet charges both values. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (wrapped_meet_time w a b) as Htime.
    time_unfold T_pmeet. cbn beta iota zeta. time_simpl. unfold c_payload, psize.
    rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Bottom recognition charges the stored value. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w [| |lo hi]; time_unfold T_pis_bot;
      unfold c_payload, psize; rewrite !Nat2N.inj_add; nia.
  Qed.
  (** Point recognition charges the stored value. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. pose proof (wrapped_point_time w a) as Htime.
    time_unfold T_ppoint. cbn beta iota zeta. time_simpl. unfold c_payload, psize.
    rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Constant construction charges width and literal size. *)
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <= c_payload *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (wrapped_norm_time w (WItv z z)) as Htime.
    time_unfold T_pconst. cbn beta iota zeta. time_simpl. unfold c_payload. cbn [wrapped_bits
      Nat.pow] in *.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  (** Arc normalization charges raw endpoints and output width. *)
  Lemma T_wrapped_norm_le : forall w a,
    (T_wrapped_norm w a <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  Proof.
    intros w a. pose proof (wrapped_norm_time w a) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_norm. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Arc expansion charges raw endpoints and output width. *)
  Lemma T_wrapped_double_le : forall w a,
    (T_wrapped_double w a <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  Proof.
    intros w a. pose proof (wrapped_double_time w a) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_double. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Arithmetic negation charges raw endpoints and output width. *)
  Lemma T_wrapped_neg_le : forall w a,
    (T_wrapped_neg w a <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  Proof.
    intros w a. pose proof (wrapped_neg_time w a) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_neg. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Bitwise negation charges raw endpoints and output width. *)
  Lemma T_wrapped_not_le : forall w a,
    (T_wrapped_not w a <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  Proof.
    intros w a. pose proof (wrapped_not_time w a) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_not. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Circular multiplication charges width and both endpoint sets. *)
  Lemma T_wrapped_mul_le : forall w a b,
    (T_wrapped_mul w a b <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  Proof.
    intros w a b. pose proof (wrapped_mul_fast_time w a b) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_mul. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Circular addition charges width and both endpoint sets. *)
  Lemma T_wrapped_add_le : forall w a b,
    (T_wrapped_add w a b <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  Proof.
    intros w a b. pose proof (wrapped_add_time w a b) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_add. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Circular subtraction charges width and both endpoint sets. *)
  Lemma T_wrapped_sub_le : forall w a b,
    (T_wrapped_sub w a b <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  Proof.
    intros w a b. pose proof (wrapped_sub_time w a b) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_sub. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Arc splitting charges endpoint normalization at both poles. *)
  Lemma T_wrapped_split_le : forall w a,
    (T_wrapped_split w a <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  Proof.
    intros w a. pose proof (wrapped_split_time w a) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_split. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Unsigned division charges width and both endpoint sets. *)
  Lemma T_wrapped_udiv_le : forall w a b,
    (T_wrapped_udiv w a b <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  Proof.
    intros w a b. pose proof (wrapped_udiv_time w a b) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_udiv. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Unsigned remainder charges width and both endpoint sets. *)
  Lemma T_wrapped_urem_le : forall w a b,
    (T_wrapped_urem w a b <= c_wrapped *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  Proof.
    intros w a b. pose proof (wrapped_urem_time w a b) as Htime.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      (Nat.le_refl _) (ltac:(lia))) as Hfloor.
    time_unfold T_wrapped_urem. cbn beta iota zeta. time_simpl.
    unfold c_wrapped. rewrite !Nat2N.inj_add in *. lia.
  Qed.
  (** Circular multiplication has the published quadratic work bound. *)
  Lemma mul_bigO : bigO (fun _ => True)
    (fun x : positive * (wrapped * wrapped) => N.of_nat
      ((Pos.to_nat (fst x) + 1) ^ 2 + wrapped_bits (fst (snd x)) +
        wrapped_bits (snd (snd x))))
    (fun x => T_wrapped_mul (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 17592186044416%N. intros [w [a b]] _.
    change (T_wrapped_mul w a b <= 17592186044416 *
      (N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b) + 1))%N.
    pose proof (wrapped_mul_fast_time w a b) as Htime.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b)) in *.
    clearbody budget.
    time_unfold T_wrapped_mul. cbn beta iota zeta. time_simpl. lia.
  Qed.

  (** Normalization is linear in the width and raw endpoint bits. *)
  Lemma norm_bigO : bigO (X := positive * wrapped) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (snd x) + 1))
    (fun x => T_wrapped_norm (fst x) (snd x)).
  Proof.
    exists 512%N. intros [w a] _. cbn [fst snd].
    pose proof (wrapped_norm_time w a) as Htime.
    time_unfold T_wrapped_norm. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Arithmetic negation is linear in the width and raw endpoint bits. *)
  Lemma neg_bigO : bigO (X := positive * wrapped) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (snd x) + 1))
    (fun x => T_wrapped_neg (fst x) (snd x)).
  Proof.
    exists 2048%N. intros [w a] _. cbn [fst snd].
    pose proof (wrapped_neg_time w a) as Htime.
    time_unfold T_wrapped_neg. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Circular expansion is linear in the width and raw endpoint bits. *)
  Lemma double_bigO : bigO (X := positive * wrapped) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (snd x) + 1))
    (fun x => T_wrapped_double (fst x) (snd x)).
  Proof.
    exists 4096%N. intros [w a] _. cbn [fst snd].
    pose proof (wrapped_double_time w a) as Htime.
    time_unfold T_wrapped_double. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Bitwise negation is linear in the width and raw endpoint bits. *)
  Lemma not_bigO : bigO (X := positive * wrapped) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (snd x) + 1))
    (fun x => T_wrapped_not (fst x) (snd x)).
  Proof.
    exists 1048576%N. intros [w a] _. cbn [fst snd].
    pose proof (wrapped_not_time w a) as Htime.
    time_unfold T_wrapped_not. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Pole splitting is linear in the width and raw endpoint bits. *)
  Lemma split_bigO : bigO (X := positive * wrapped) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (snd x) + 1))
    (fun x => T_wrapped_split (fst x) (snd x)).
  Proof.
    exists 8388608%N. intros [w a] _. cbn [fst snd].
    pose proof (wrapped_split_time w a) as Htime.
    time_unfold T_wrapped_split. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Addition is linear in the width and both raw endpoint sets. *)
  Lemma add_bigO : bigO (X := positive * (wrapped * wrapped)) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (fst (snd x)) +
      wrapped_bits (snd (snd x)) + 1))
    (fun x => T_wrapped_add (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 4096%N. intros [w [a b]] _. cbn [fst snd].
    pose proof (wrapped_add_time w a b) as Htime.
    time_unfold T_wrapped_add. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Subtraction is linear in the width and both raw endpoint sets. *)
  Lemma sub_bigO : bigO (X := positive * (wrapped * wrapped)) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + wrapped_bits (fst (snd x)) +
      wrapped_bits (snd (snd x)) + 1))
    (fun x => T_wrapped_sub (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 16384%N. intros [w [a b]] _. cbn [fst snd].
    pose proof (wrapped_sub_time w a b) as Htime.
    time_unfold T_wrapped_sub. cbn beta iota zeta. time_simpl.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Unsigned division has the published quadratic class. *)
  Lemma udiv_bigO : bigO (X := positive * (wrapped * wrapped)) (fun _ => True)
    (fun x => N.of_nat ((Pos.to_nat (fst x) + 1) ^ 2 +
      wrapped_bits (fst (snd x)) + wrapped_bits (snd (snd x))))
    (fun x => T_wrapped_udiv (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists c_wrapped. intros [w [a b]] _. cbn [fst snd].
    eapply N.le_trans; [apply T_wrapped_udiv_le|].
    apply N.mul_le_mono_l. lia.
  Qed.

  (** Unsigned remainder has the published quadratic class. *)
  Lemma urem_bigO : bigO (X := positive * (wrapped * wrapped)) (fun _ => True)
    (fun x => N.of_nat ((Pos.to_nat (fst x) + 1) ^ 2 +
      wrapped_bits (fst (snd x)) + wrapped_bits (snd (snd x))))
    (fun x => T_wrapped_urem (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists c_wrapped. intros [w [a b]] _. cbn [fst snd].
    eapply N.le_trans; [apply T_wrapped_urem_le|].
    apply N.mul_le_mono_l. lia.
  Qed.

  Definition mul_piece (w : positive) (a b : Z * Z) : wrapped :=
    wrapped_mul_piece w
      (I (Fin (fst a)) (Fin (snd a)))
      (I (Fin (fst b)) (Fin (snd b))).
  TimeFun mul_piece.
  Definition k_split : N := 1. (* STUB *)
  Definition k_mul_piece : N := 65536.

  (* Gamma and multiplication laws now live in WRAPPED_LAWS. *)
  (** Arc cardinality lies between zero and the modulus. *)
  Lemma F2_card : forall w a, (0 <= card w a <= Word.modulus w)%Z.
  Proof.
    intros w a. rewrite card_wrapped_size. apply wrapped_size_bounds.
  Qed.
  (** Pole splitting returns at most four pieces. *)
  Lemma F3_split_len : forall w a, (length (wrapped_split w a) <= 4)%nat.
  Proof. apply wrapped_split_length. Qed.
  (** Every represented word belongs to a returned split interval. *)
  Lemma F4_split_covers : forall w a z, pgamma w a z ->
    exists lo hi, In (lo, hi) (wrapped_split w a) /\ (lo <= z <= hi)%Z.
  Proof.
    intros w a z Ha. apply wrapped_split_cover. exact (proj1 (pgamma_wrapped w a z) Ha).
  Qed.
  (** A multiplication piece contains every product from its intervals. *)
  Lemma F5_mul_piece : forall w lo hi lo' hi' x y,
    (lo <= x <= hi)%Z -> (lo' <= y <= hi')%Z ->
    pgamma w (mul_piece w (lo, hi) (lo', hi')) (L.wrap w (x * y)).
  Proof.
    intros w lo hi lo' hi' x y Hx Hy. rewrite pgamma_wrapped.
    apply wrapped_mul_piece_sound; assumption.
  Qed.
  (** Widening retains a contained candidate and otherwise expands first. *)
  Lemma F7_widen : forall q w a b,
    pwiden q w a b = if pleb w b a then a else pjoin w (wrapped_double w a) b.
  Proof.
    intros q w a b. rewrite pwiden_agrees, pleb_agrees, pjoin_agrees. reflexivity.
  Qed.
  (** Expansion triples cardinality until it reaches the modulus. *)
  Lemma F8_double_card : forall w a,
    card w (wrapped_double w a) = Z.min (Word.modulus w) (3 * card w a)%Z.
  Proof.
    intros w a. rewrite !card_wrapped_size. apply wrapped_double_size.
  Qed.
  (** Expansion contains the old arc. *)
  Lemma F8a_double_contains : forall w a, pleb w a (wrapped_double w a) = true.
  Proof.
    intros w a. rewrite pleb_agrees.
    apply wrapped_double_upper.
  Qed.
  (** Cardinality is monotone in the payload order. *)
  Lemma F8b_card_mono : forall w a b,
    pleb w a b = true -> (card w a <= card w b)%Z.
  Proof.
    intros w a b Hle. rewrite pleb_agrees in Hle.
    rewrite !card_wrapped_size. now apply wrapped_size_monotone.
  Qed.
  (** Widening rank is determined by arc cardinality. *)
  Lemma F9_rank : forall q w a, pwrank q w a = size_rank w (card w a).
  Proof.
    intros q w a. reflexivity.
  Qed.
  (** Arc widening credit is at most width plus two. *)
  Lemma F10_rank_bound : forall q w a, (pwrank q w a <= Pos.to_nat w + 2)%nat.
  Proof.
    intros q w a. rewrite pwrank_wrapped.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w a) (wrapped_size_bounds w a))
      as Hbounds.
    replace (Pos.to_nat w + 2)%nat with (Z.to_nat (Zpos w + 2)) by lia.
    apply Z2Nat.inj_le; lia.
  Qed.
  (** Payload storage charges width and endpoint bit lengths. *)
  Lemma psize_bits : forall w a,
    psize w a = (Pos.to_nat w + wrapped_bits a + 1)%nat.
  Proof.
    intros w a. reflexivity.
  Qed.
  (** Arithmetic transfer results have endpoints within the word width. *)
  Lemma wrapped_result_bits : forall w a b,
    (wrapped_bits (wrapped_add w a b) <= 2 * Pos.to_nat w)%nat /\
    (wrapped_bits (wrapped_sub w a b) <= 2 * Pos.to_nat w)%nat /\
    (wrapped_bits (wrapped_mul w a b) <= 2 * Pos.to_nat w)%nat /\
    (wrapped_bits (wrapped_neg w a) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b. repeat split.
    - apply wrapped_add_bits.
    - apply wrapped_add_bits.
    - unfold wrapped_mul. rewrite wrapped_mul_fast_agrees. apply wrapped_mul_bits.
    - apply wrapped_neg_bits.
  Qed.
  (** Every split piece has endpoints within the word width. *)
  Lemma wrapped_split_bits : forall w a lo hi,
    In (lo, hi) (wrapped_split w a) ->
    (Z.size_nat lo + Z.size_nat hi <= 2 * Pos.to_nat w)%nat.
  Proof. apply wrapped_split_bits_bound. Qed.
  (** Multiplication pieces charge width and all endpoint bit lengths. *)
  Lemma T1_mul_piece : forall w lo hi lo' hi',
    (T_mul_piece w (lo, hi) (lo', hi') <= k_mul_piece * N.of_nat
      ((Pos.to_nat w + Z.size_nat lo + Z.size_nat hi + Z.size_nat lo' + Z.size_nat hi' + 1)
        ^ 2))%N.
  Proof.
    intros w lo hi lo' hi'.
    pose proof (wrapped_mul_piece_finite_time w lo hi lo' hi') as Hpiece.
    set (budget := N.of_nat
      ((Pos.to_nat w + Z.size_nat lo + Z.size_nat hi + Z.size_nat lo' + Z.size_nat hi' + 1)
        ^ 2)) in *.
    assert (Hpositive : (1 <= budget)%N).
    { unfold budget. apply (time_of_nat_le 1). cbn [Nat.pow]. nia. }
    clearbody budget.
    time_unfold T_mul_piece. time_cbn. time_simpl. unfold k_mul_piece. lia.
  Qed.
End WrappedT.
