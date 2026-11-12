(** * Circular word intervals

    Circular arcs represent inclusive sets of words across either numeric pole.
    For example, the eight-bit arc from 250 to 3 contains zero.
    Builds on: WrappedSig, Interval and the bit-vector operations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import Word Op Fun.
From Galois.Domains Require Import ValueSig WordSig WrappedSig IntervalSig Interval IntervalOps Thresholds.
Import List.ListNotations.
Local Open Scope Z_scope.

Module WrappedScalar := IntervalBaseCode ThresholdsCode.

Definition wrapped_offset (w : width) (origin x : Z) : Z :=
  (x - origin) mod modulus w.

Definition wrapped_size (w : width) (a : wrapped) : Z :=
  match a with
  | WBot => 0
  | WFull => modulus w
  | WItv lo hi => wrapped_offset w lo hi + 1
  end.

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
    then WFull else WItv (wrap w lo) (wrap w hi)
  | _ => a
  end.

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

Definition wrapped_cover (w : width) (a b candidate : wrapped) : bool :=
  wrapped_leb w a candidate && wrapped_leb w b candidate.

Definition wrapped_choose (w : width) (a b first second : wrapped) : wrapped :=
  if wrapped_cover w a b first then
    if wrapped_cover w a b second then
      if wrapped_size w first <=? wrapped_size w second then first else second
    else first
  else if wrapped_cover w a b second then second else WFull.

Definition wrapped_join (w : width) (a b : wrapped) : wrapped :=
  wrapped_norm w
    (if wrapped_leb w a b then b else
     if wrapped_leb w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end).

Definition wrapped_double (w : width) (a : wrapped) : wrapped :=
  match a with
  | WBot => WBot
  | WFull => WFull
  | WItv lo hi =>
    let size := wrapped_size w a in
    if modulus w <=? 3 * size then WFull
    else wrapped_norm w (WItv (lo - size) (hi + size))
  end.

Definition wrapped_widen (w : width) (a b : wrapped) : wrapped :=
  if wrapped_leb w b a then wrapped_norm w a
  else wrapped_join w (wrapped_double w a) b.

Definition wrapped_narrow (w : width) (a b : wrapped) : wrapped :=
  match wrapped_norm w a with
  | WFull => wrapped_norm w b
  | _ => wrapped_norm w a
  end.

Definition wrapped_range (w : width) (lo hi : Z) : wrapped :=
  if hi <? lo then WBot else
  if modulus w - 1 <=? hi - lo then WFull else wrapped_norm w (WItv lo hi).

Definition wrapped_of_interval (w : width) (i : itv) : wrapped :=
  match i with
  | IBot => WBot
  | I (Fin lo) (Fin hi) => wrapped_range w lo hi
  | _ => WFull
  end.

Definition wrapped_parts_raw (w : width) (a : wrapped) : itv * itv :=
  match a with
  | WBot => (IBot, IBot)
  | WFull => (I (Fin 0) (Fin (modulus w - 1)), IBot)
  | WItv lo hi =>
    let lo' := wrap w lo in
    let hi' := wrap w hi in
    if lo' <=? hi' then (I (Fin lo') (Fin hi'), IBot)
    else (I (Fin lo') (Fin (modulus w - 1)), I (Fin 0) (Fin hi'))
  end.

Definition wrapped_parts (w : width) (a : wrapped) : itv * itv :=
  wrapped_parts_raw w (wrapped_norm w a).

Definition wrapped_join_four (w : width) (a b c d : wrapped) : wrapped :=
  wrapped_join w (wrapped_join w a b) (wrapped_join w c d).

Definition wrapped_meet (w : width) (a b : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pb := wrapped_parts w b in
  let candidate := wrapped_join_four w
    (wrapped_of_interval w (WrappedScalar.interval_meet (fst pa) (fst pb)))
    (wrapped_of_interval w (WrappedScalar.interval_meet (fst pa) (snd pb)))
    (wrapped_of_interval w (WrappedScalar.interval_meet (snd pa) (fst pb)))
    (wrapped_of_interval w (WrappedScalar.interval_meet (snd pa) (snd pb))) in
  if wrapped_leb w candidate a then candidate else wrapped_norm w a.

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

Definition wrapped_neg (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi => wrapped_norm w (WItv (- hi) (- lo))
  | _ => a
  end.

Definition wrapped_sub (w : width) (a b : wrapped) : wrapped :=
  wrapped_add w a (wrapped_neg w b).

Definition wrapped_mul_piece (w : width) (a b : itv) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | I (Fin lo) (Fin hi), I (Fin lo') (Fin hi') =>
    wrapped_range w
      (Z.min (Z.min (lo * lo') (lo * hi')) (Z.min (hi * lo') (hi * hi')))
      (Z.max (Z.max (lo * lo') (lo * hi')) (Z.max (hi * lo') (hi * hi')))
  | _, _ => WFull
  end.

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

Definition wrapped_signed_parts (w : width) (a : wrapped) : itv * itv :=
  let biased := wrapped_parts w (wrapped_add w a (WItv (half w) (half w))) in
  (wrapped_shift_interval (- half w) (fst biased),
   wrapped_shift_interval (- half w) (snd biased)).

Definition wrapped_mul_parts (w : width) (a b : itv * itv) : wrapped :=
  wrapped_join_four w
    (wrapped_mul_piece w (fst a) (fst b))
    (wrapped_mul_piece w (fst a) (snd b))
    (wrapped_mul_piece w (snd a) (fst b))
    (wrapped_mul_piece w (snd a) (snd b)).

Definition wrapped_mul_cut (pole : Z) (a : itv) : itv * itv :=
  (WrappedScalar.interval_meet a (I NegInf (Fin (pole - 1))),
   WrappedScalar.interval_meet a (I (Fin pole) PosInf)).

Definition wrapped_mul_both_parts (w : width) (pole : Z) (a b : itv * itv) : wrapped :=
  let a0 := wrapped_mul_cut pole (fst a) in
  let a1 := wrapped_mul_cut pole (snd a) in
  let b0 := wrapped_mul_cut pole (fst b) in
  let b1 := wrapped_mul_cut pole (snd b) in
  wrapped_join_four w
    (wrapped_mul_parts w a0 b0) (wrapped_mul_parts w a0 b1)
    (wrapped_mul_parts w a1 b0) (wrapped_mul_parts w a1 b1).

Definition wrapped_mul (w : width) (a b : wrapped) : wrapped :=
  let unsigned := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) in
  let signed := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b) in
  if wrapped_size w unsigned <=? wrapped_size w signed then unsigned else signed.

Definition wrapped_pole_cut (w : width) (a : itv) : itv * itv :=
  (WrappedScalar.interval_meet a (I (Fin 0) (Fin (half w - 1))),
   WrappedScalar.interval_meet a (I (Fin (half w)) (Fin (modulus w - 1)))).

Definition wrapped_point w a : option Z :=
  match wrapped_norm w a with
  | WItv lo hi => if Z.eqb lo hi then Some lo else None
  | _ => None
  end.

Module WrappedIntervalOps := IntervalOpsCode ThresholdsCode WrappedScalar.

Definition wrapped_interval_pair (w : width) (a : itv * itv) : wrapped :=
  wrapped_join w (wrapped_of_interval w (fst a)) (wrapped_of_interval w (snd a)).

Definition wrapped_not_piece (w : width) (a : itv) : wrapped :=
  match a with
  | IBot => WBot
  | _ => wrapped_of_interval w (WrappedIntervalOps.interval_not w a)
  end.

Definition wrapped_not (w : width) (a : wrapped) : wrapped :=
  let parts := wrapped_parts w a in
  wrapped_join w
    (wrapped_not_piece w (fst parts))
    (wrapped_not_piece w (snd parts)).

Definition wrapped_div_piece (remainder : bool) (w : width) (a b : itv) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | _, _ => wrapped_of_interval w
      (if remainder then WrappedIntervalOps.interval_urem w a b
       else WrappedIntervalOps.interval_udiv w a b)
  end.

Definition wrapped_div_cut (remainder : bool) (w : width) (a b : itv) : wrapped :=
  let pa := wrapped_pole_cut w a in
  let pb := wrapped_pole_cut w b in
  wrapped_join_four w
    (wrapped_div_piece remainder w (fst pa) (fst pb))
    (wrapped_div_piece remainder w (fst pa) (snd pb))
    (wrapped_div_piece remainder w (snd pa) (fst pb))
    (wrapped_div_piece remainder w (snd pa) (snd pb)).

Definition wrapped_div (remainder : bool) (w : width) (a b : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pb := wrapped_parts w b in
  wrapped_join_four w
    (wrapped_div_cut remainder w (fst pa) (fst pb))
    (wrapped_div_cut remainder w (fst pa) (snd pb))
    (wrapped_div_cut remainder w (snd pa) (fst pb))
    (wrapped_div_cut remainder w (snd pa) (snd pb)).

Definition wrapped_udiv := wrapped_div false.
Definition wrapped_urem := wrapped_div true.

Definition wrapped_interval_list (a : itv) : list (Z * Z) :=
  match a with
  | I (Fin lo) (Fin hi) => [(lo, hi)]
  | _ => []
  end.

Definition wrapped_split (w : width) (a : wrapped) : list (Z * Z) :=
  let parts := wrapped_parts w a in
  let lo := wrapped_pole_cut w (fst parts) in
  let hi := wrapped_pole_cut w (snd parts) in
  wrapped_interval_list (fst lo) ++ wrapped_interval_list (snd lo) ++
  wrapped_interval_list (fst hi) ++ wrapped_interval_list (snd hi).

Module WrappedCode (L : WORD_LANGUAGE_OPS) <: WRAPPED_OPS L.
  Definition p := wrapped.
  Definition pleb := wrapped_leb.
  Definition pjoin := wrapped_join.
  Definition pmeet := wrapped_meet.
  Definition pbot (_ : positive) := WBot.
  Definition ptop (_ : positive) := WFull.
  Definition pis_bot (_ : positive) (a : p) := match a with WBot => true | _ => false end.
  Definition pconst w z := wrapped_norm w (WItv z z).
  Definition ppoint := wrapped_point.
  Definition pwparam := unit.
  Definition pwiden (_ : unit) w a b :=
    if pleb w b a then a else pjoin w (wrapped_double w a) b.
  Definition pnarrow := wrapped_narrow.
  Definition wrapped_norm := wrapped_norm.
  Definition wrapped_double := wrapped_double.
  Definition wrapped_neg := wrapped_neg.
  Definition wrapped_not := wrapped_not.
  Definition wrapped_add := wrapped_add.
  Definition wrapped_sub := wrapped_sub.
  Definition wrapped_mul := wrapped_mul.
  Definition wrapped_udiv := wrapped_udiv.
  Definition wrapped_urem := wrapped_urem.
  Definition wrapped_split := wrapped_split.
End WrappedCode.

Module Wrapped (L : WORD_LANGUAGE) <: WRAPPED L.
  Include WrappedCode L.
  Include WRAPPED_SPEC L.
  Definition pgamma := arc_gamma.
  Definition pwrank (_ : pwparam) (w : positive) (a : p) : nat := size_rank w (card w a).
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted. (* STUB *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted. (* STUB *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted. (* STUB *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. Admitted. (* STUB *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof. Admitted. (* STUB *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. Admitted. (* STUB *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted. (* STUB *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted. (* STUB *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted. (* STUB *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. Admitted. (* STUB *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. Admitted. (* STUB *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted. (* STUB *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof. Admitted. (* STUB *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* STUB *)
End Wrapped.

Theorem wrapped_offset_range w c x : 0 <= wrapped_offset w c x < modulus w.
Proof.
  apply Z.mod_pos_bound. apply modulus_pos.
Qed.

Theorem wrapped_offset_self w c : wrapped_offset w c c = 0.
Proof.
  unfold wrapped_offset. rewrite Z.sub_diag.
  apply Z.mod_0_l. apply modulus_nonzero.
Qed.

Theorem wrapped_offset_wrap w c x :
  wrapped_offset w (wrap w c) (wrap w x) = wrapped_offset w c x.
Proof.
  unfold wrapped_offset. rewrite !wrap_mod. symmetry. apply Zminus_mod.
Qed.

Theorem wrapped_offset_word w c x :
  wrapped_offset w c (wrap w x) = wrapped_offset w c x.
Proof.
  unfold wrapped_offset. rewrite !wrap_mod.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

Theorem wrapped_offset_origin w c x :
  wrapped_offset w (wrap w c) x = wrapped_offset w c x.
Proof.
  unfold wrapped_offset. rewrite !wrap_mod.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

Theorem wrapped_offset_add w c a x :
  wrapped_offset w c x =
  (wrapped_offset w c a + wrapped_offset w a x) mod modulus w.
Proof.
  unfold wrapped_offset.
  replace (x - c) with ((a - c) + (x - a)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

Theorem wrapped_offset_sub w c a x :
  wrapped_offset w a x =
  (wrapped_offset w c x - wrapped_offset w c a) mod modulus w.
Proof.
  unfold wrapped_offset.
  replace (x - a) with ((x - c) - (a - c)) by ring.
  apply Zminus_mod.
Qed.

Theorem wrapped_offset_step w c k :
  0 <= k < modulus w -> wrapped_offset w c (wrap w (c + k)) = k.
Proof.
  intro Hk. rewrite wrapped_offset_word.
  unfold wrapped_offset. replace (c + k - c) with k by ring.
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
    pose proof (wrapped_offset_range w lo z) as Hrange. split; [|tauto].
    intro Hz. split; [exact Hz|lia].
  - cbn [wrapped_gamma].
    rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

Theorem wrapped_norm_size w a : wrapped_size w (wrapped_norm w a) = wrapped_size w a.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_size]. lia.
  - cbn [wrapped_size]. now rewrite wrapped_offset_wrap.
Qed.

Theorem wrapped_size_bounds w a : 0 <= wrapped_size w a <= modulus w.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_size];
    pose proof (modulus_pos w); try lia.
  pose proof (wrapped_offset_range w lo hi). lia.
Qed.

Theorem wrapped_leb_spec w left right :
  wrapped_leb w left right = true <->
  forall z, wrapped_gamma w left z -> wrapped_gamma w right z.
Proof. Admitted. (* CONVERT: wrapped_leb_spec: The variable wrapped_arc_inclusion was not found in the current *)

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

Theorem wrapped_join_cover w a b : wrapped_cover w a b (wrapped_join w a b) = true.
Proof. Admitted. (* CONVERT: wrapped_join_cover: The variable wrapped_choose_cover was not found in the current *)

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

Theorem wrapped_double_upper w a : wrapped_leb w a (wrapped_double w a) = true.
Proof. Admitted. (* CONVERT: wrapped_double_upper: The variable wrapped_expand_span was not found in the current *)

Theorem wrapped_double_size w a :
  wrapped_size w (wrapped_double w a) =
  Z.min (modulus w) (3 * wrapped_size w a).
Proof. Admitted. (* CONVERT: wrapped_double_size: The variable wrapped_expand_size was not found in the current *)

Theorem wrapped_join_minimal w a b c :
  wrapped_leb w a c = true -> wrapped_leb w b c = true ->
  wrapped_size w (wrapped_join w a b) <= wrapped_size w c.
Proof. Admitted. (* CONVERT: wrapped_join_minimal: The variable wrapped_join_size was not found in the current *)

Theorem wrapped_range_sound w lo hi z :
  lo <= z <= hi -> wrapped_gamma w (wrapped_range w lo hi) (wrap w z).
Proof.
  intro Hz. unfold wrapped_range.
  destruct (hi <? lo) eqn:Hempty; [apply Z.ltb_lt in Hempty; lia|].
  destruct (modulus w - 1 <=? hi - lo) eqn:Hfull; [apply wrap_is_word|].
  apply Z.leb_gt in Hfull. apply (proj2 (wrapped_norm_gamma w (WItv lo hi) _)).
  split; [apply wrap_is_word|].
  rewrite wrapped_offset_word. unfold wrapped_offset.
  rewrite !Z.mod_small by lia. lia.
Qed.

Theorem wrapped_offset_word_cases w c z :
  is_word w c -> is_word w z ->
  wrapped_offset w c z = if c <=? z then z - c else z - c + modulus w.
Proof.
  intros Hc Hz. unfold wrapped_offset.
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
  cbn [wrapped_norm]. rewrite wrapped_offset_wrap, Hfull, !wrap_wrap. reflexivity.
Qed.

Theorem wrapped_norm_endpoints w a lo hi :
  wrapped_norm w a = WItv lo hi -> is_word w lo /\ is_word w hi.
Proof.
  destruct a as [| |l h]; cbn [wrapped_norm]; try discriminate.
  destruct (wrapped_offset w l h =? modulus w - 1); [discriminate|].
  intro Hnorm. inversion Hnorm; subst lo hi. split; apply wrap_is_word.
Qed.

Theorem wrapped_parts_normalized w a :
  wrapped_parts w (wrapped_norm w a) = wrapped_parts w a.
Proof.
  unfold wrapped_parts. now rewrite wrapped_norm_idempotent.
Qed.

Theorem wrapped_join_sound w a b z :
  wrapped_gamma w a z \/ wrapped_gamma w b z -> wrapped_gamma w (wrapped_join w a b) z.
Proof. Admitted. (* CONVERT: wrapped_join_sound: The variable gamma_monotone was not found in the current environment. *)

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

Theorem wrapped_meet_sound w a b z :
  wrapped_gamma w a z -> wrapped_gamma w b z -> wrapped_gamma w (wrapped_meet w a b) z.
Proof. Admitted. (* CONVERT: wrapped_meet_sound: The variable wrapped_parts_spec was not found in the current *)

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

Theorem wrapped_add_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_add w a b) (wrap w (x + y)).
Proof. Admitted. (* CONVERT: wrapped_add_sound: The variable wrapped_offset_sum was not found in the current *)

Theorem wrapped_neg_sound w a x :
  wrapped_gamma w a x -> wrapped_gamma w (wrapped_neg w a) (wrap w (- x)).
Proof. Admitted. (* CONVERT: wrapped_neg_sound: The variable wrapped_offset_neg was not found in the current *)

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

Theorem wrapped_mul_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_mul w a b) (wmul w x y).
Proof. Admitted. (* CONVERT: wrapped_mul_sound: The variable wrapped_mul_both_parts_sound was not found in the current *)

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

Definition interval_pgamma (w : width) (a : itv) (z : Z) : Prop :=
  is_word w z /\ match a with IBot => False | I lo hi => in_bnd lo hi z end.
Theorem wrapped_parts_spec w a z :
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts w a)) z \/
  interval_pgamma w (snd (wrapped_parts w a)) z.
Proof. Admitted. (* CONVERT: wrapped_parts_spec: The variable wrapped_parts_raw_spec was not found in the current environment. *)

Definition interval_meaning (a : itv) (z : Z) : Prop :=
  match a with IBot => False | I lo hi => in_bnd lo hi z end.

Theorem wrapped_of_interval_sound w i z :
  interval_meaning i z -> wrapped_gamma w (wrapped_of_interval w i) (wrap w z).
Proof. Admitted. (* CONVERT: wrapped_of_interval_sound: The reference interval_gamma was not found in the current environment. *)
Theorem wrapped_interval_value_sound w i z :
  interval_pgamma w i z -> wrapped_gamma w (wrapped_of_interval w i) z.
Proof.
  intros [Hword Hz]. rewrite <- (wrap_id w z Hword).
  now apply wrapped_of_interval_sound.
Qed.
