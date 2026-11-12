(** * Circular word intervals

    Circular arcs represent inclusive sets of words across either numeric pole.
    For example, the eight-bit arc from 250 to 3 contains zero.
    Builds on: WrappedSig, Interval and the bit-vector operations. *)

From Stdlib Require Import ZArith List Bool.
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
