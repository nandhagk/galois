(** * Two-step value reduction interfaces

    Reductions exchange facts between two abstractions of the same concrete word.
    For example, an interval can discard endpoints outside a congruence class.
    Builds on: ProductSig and ValueSig. *)

From Stdlib Require Import ZArith List.
From Argent Require Import Time Std BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig BitsLang WordSig
  KnownBitsSig WrappedSig IntervalSig CongruenceSig.

(** The arc between the least and the greatest member of a known-bit payload. *)
Definition bits_hull (w : positive) (b : tnum) : wrapped :=
  let lo := tnum_wrap w (ones b) in
  let hi := Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w)) in
  if Z.leb lo hi then WItv lo hi else WBot.
TimeFun bits_hull.

Module Z.
  TimeFun Z.lnot.
End Z.

(** The common prefix of a nonwrapping arc as a known-bit payload. *)
Definition arc_prefix (w : positive) (a : wrapped) : tnum :=
  match a with
  | WItv lo hi =>
    let lo' := tnum_wrap w lo in
    let hi' := tnum_wrap w hi in
    if Z.leb lo' hi' then
      let m := Z.ones (Z.log2 (Z.lxor lo' hi') + 1) in
      Tnum (Z.land (Z.lnot (Z.lor lo' m)) (Z.ones (Zpos w))) (Z.land lo' (Z.lnot m))
    else Tnum 0 0
  | _ => Tnum 0 0
  end.
TimeFun arc_prefix.

(** Word interval queries first discard integers outside the unsigned word domain. *)
Definition interval_word_clip (w : positive) (a : itv) : itv :=
  match a with
  | IBot => IBot
  | I PosInf _ | I _ NegInf => IBot
  | I lo hi =>
    let lo' := match lo with Fin z => Z.max 0 z | _ => 0%Z end in
    let hi' := match hi with Fin z => Z.min (Z.ones (Zpos w)) z
      | _ => Z.ones (Zpos w) end in
    if Z.leb lo' hi' then I (Fin lo') (Fin hi') else IBot
  end.
TimeFun interval_word_clip.

(** Finite bounds round inward to the residue class, and a singleton fixes both bounds. *)
Definition congr_interval (w : positive) (a : itv) (b : congr) : itv :=
  let a' := interval_word_clip w a in
  match a', b with
  | IBot, _ | _, CBot => IBot
  | _, C m r =>
    if Z.eqb m 0 then I (Fin r) (Fin r) else
    match a' with
    | IBot => IBot
    | I lo hi => I
        (match lo with Fin z => Fin (z + (r - z) mod Z.abs m) | _ => lo end)
        (match hi with Fin z => Fin (z - (z - r) mod Z.abs m) | _ => hi end)
    end
  end.
TimeFun congr_interval.

(** A singleton interval supplies an exact residue, and other intervals supply no residue fact. *)
Definition interval_congr (a : itv) : congr :=
  match a with
  | IBot => CBot
  | I (Fin lo) (Fin hi) => if Z.eqb lo hi then C 0 lo else C 1 0
  | _ => C 1 0
  end.
TimeFun interval_congr.

(** The least and greatest known-bit members bound an ordinary interval. *)
Definition bits_interval (w : positive) (b : tnum) : itv :=
  match bits_hull w b with
  | WItv lo hi => I (Fin lo) (Fin hi)
  | WBot => IBot
  | WFull => I NegInf PosInf
  end.
TimeFun bits_interval.

(** Common-prefix extraction first intersects the interval with the unsigned word range. *)
Definition interval_prefix (w : positive) (a : itv) : tnum :=
  match interval_word_clip w a with
  | I (Fin lo) (Fin hi) => arc_prefix w (WItv lo hi)
  | _ => Tnum 0 0
  end.
TimeFun interval_prefix.

Module Type REDUCTION_STEPS_OPS (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L).
  Include REDUCER_OPS A B.
  Parameter to_left : A.t * B.t -> A.t * B.t.
  Parameter to_right : A.t * B.t -> A.t * B.t.
End REDUCTION_STEPS_OPS.

Module Type REDUCTION_STEPS_LAWS (L : LANG) (A B : VALUE_DOMAIN L)
    (Import R : REDUCTION_STEPS_OPS L A B).
  (** One exchange to the left leaves the right component unchanged. *)
  Parameter left_frame : forall x, snd (to_left x) = snd x.
  (** One exchange to the right leaves the left component unchanged. *)
  Parameter right_frame : forall x, fst (to_right x) = fst x.
  (** The first exchange retains every value shared by the input pair. *)
  Parameter left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  (** The second exchange retains every value shared by the input pair. *)
  Parameter right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  (** The first exchange refines the left component. *)
  Parameter left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  (** The second exchange refines the right component. *)
  Parameter right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  (** A reduction performs the two exchanges in order. *)
  Parameter reduce_steps : forall x, reduce x = to_right (to_left x).
End REDUCTION_STEPS_LAWS.

Module Type REDUCTION_STEPS (L : LANG) (A B : VALUE_DOMAIN L) :=
  REDUCTION_STEPS_OPS L A B <+ REDUCER_LOWER A B <+ VALUE_REDUCER_SOUND L A B <+
  REDUCTION_STEPS_LAWS L A B.

Module Type REDUCTION_STEPS_TIME (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import R : REDUCTION_STEPS L A B).
  Include VALUE_REDUCER_TIME L A B R.
  Parameter T_to_left T_to_right : A.t * B.t -> N.
  Parameter c_exchange : N.
  (** The left exchange charges both component sizes. *)
  Parameter T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** The right exchange charges both component sizes. *)
  Parameter T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** The first exchange has linearly bounded output storage. *)
  Parameter left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** The second exchange has linearly bounded output storage. *)
  Parameter right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** Reduction has the published combined-size asymptotic budget. *)
  Parameter reduce_bigO : bigO (fun _ => True)
    (fun x => N.of_nat (A.size (fst x) + B.size (snd x) + 1)) T_reduce.
End REDUCTION_STEPS_TIME.

Module Type REDUCTION_STEPS_T (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  REDUCTION_STEPS L A B <+ REDUCTION_STEPS_TIME L A B.

Module Type REDUCTION_STEPS_PLAN (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import R : REDUCTION_STEPS_T L A B).
  Parameter k_exchange : N.
  (** The two exchange soundness laws compose into reduction soundness. *)
  Parameter F1_steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  (** The two reductive exchange laws compose into componentwise descent. *)
  Parameter F2_steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  (** Reduction charges each exchange at the actual intermediate value. *)
  Parameter T1_steps : forall x, (T_reduce x <= k_exchange *
    (T_to_left x + T_to_right (to_left x) + 1))%N.
End REDUCTION_STEPS_PLAN.

Module Type REDUCTION_STEPS_ALL (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  REDUCTION_STEPS_T L A B <+ REDUCTION_STEPS_PLAN L A B.

(** WrappedBits exposes the two directional exchange obligations for word values. *)
Module Type WRAPPED_BITS_OPS (A B : VALUE_DOMAIN_OPS BitsLangCode) :=
  REDUCTION_STEPS_OPS BitsLangCode A B.
Module Type WRAPPED_BITS (A B : VALUE_DOMAIN BitsLang) := REDUCTION_STEPS BitsLang A B.
Module Type WRAPPED_BITS_T (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_T BitsLangT A B.
Module Type WRAPPED_BITS_PLAN (A B : VALUE_DOMAIN_T BitsLangT)
    (R : WRAPPED_BITS_T A B) := REDUCTION_STEPS_PLAN BitsLangT A B R.
Module Type WRAPPED_BITS_ALL (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_ALL BitsLangT A B.

(** IntervalCongr exposes the two directional exchange obligations for word values. *)
Module Type INTERVAL_CONGR_OPS (A B : VALUE_DOMAIN_OPS BitsLangCode) :=
  REDUCTION_STEPS_OPS BitsLangCode A B.
Module Type INTERVAL_CONGR (A B : VALUE_DOMAIN BitsLang) := REDUCTION_STEPS BitsLang A B.
Module Type INTERVAL_CONGR_T (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_T BitsLangT A B.
Module Type INTERVAL_CONGR_PLAN (A B : VALUE_DOMAIN_T BitsLangT)
    (R : INTERVAL_CONGR_T A B) := REDUCTION_STEPS_PLAN BitsLangT A B R.
Module Type INTERVAL_CONGR_ALL (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_ALL BitsLangT A B.

(** IntervalBits exposes the two directional exchange obligations for word values. *)
Module Type INTERVAL_BITS_OPS (A B : VALUE_DOMAIN_OPS BitsLangCode) :=
  REDUCTION_STEPS_OPS BitsLangCode A B.
Module Type INTERVAL_BITS (A B : VALUE_DOMAIN BitsLang) := REDUCTION_STEPS BitsLang A B.
Module Type INTERVAL_BITS_T (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_T BitsLangT A B.
Module Type INTERVAL_BITS_PLAN (A B : VALUE_DOMAIN_T BitsLangT)
    (R : INTERVAL_BITS_T A B) := REDUCTION_STEPS_PLAN BitsLangT A B R.
Module Type INTERVAL_BITS_ALL (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_ALL BitsLangT A B.

Module Type WRAPPED_BITS_PIN (L : WORD_LANGUAGE) (C : TNUM_CONFIG)
    (W : WRAPPED L) (K : KNOWN_BITS L C)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged W.p)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged K.p)
    (R : WRAPPED_BITS A B).
  (** The left exchange meets the arc with the bit hull at the same width. *)
  Parameter F_to_left : forall w a b, R.to_left (TVal w a, TVal w b) =
    (TVal w (W.pmeet w a (bits_hull w b)), TVal w b).
  (** The right exchange meets the bits with the arc's common prefix at the same width. *)
  Parameter F_to_right : forall w a b, R.to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (K.pmeet w b (arc_prefix w a))).
  (** Pairs of other shapes are left unchanged. *)
  Parameter F_other : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    R.to_left x = x /\ R.to_right x = x.
End WRAPPED_BITS_PIN.

Module Type INTERVAL_CONGR_PIN (L : WORD_LANGUAGE)
    (I : INTERVAL_PAYLOAD L) (G : CONGRUENCE L)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged I.p)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged G.p)
    (R : INTERVAL_CONGR A B).
  (** The left exchange meets the interval with inward residue rounding at the same width. *)
  Parameter F_to_left : forall w a b, R.to_left (TVal w a, TVal w b) =
    (TVal w (I.pmeet w a (congr_interval w a b)), TVal w b).
  (** The right exchange meets the congruence with the interval's singleton fact. *)
  Parameter F_to_right : forall w a b, R.to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (G.pmeet w b (interval_congr a))).
  (** Pairs of other shapes are left unchanged. *)
  Parameter F_other : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    R.to_left x = x /\ R.to_right x = x.
End INTERVAL_CONGR_PIN.

Module Type INTERVAL_BITS_PIN (L : WORD_LANGUAGE) (C : TNUM_CONFIG)
    (I : INTERVAL_PAYLOAD L) (K : KNOWN_BITS L C)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged I.p)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged K.p)
    (R : INTERVAL_BITS A B).
  (** The left exchange meets the interval with the known bits' hull at the same width. *)
  Parameter F_to_left : forall w a b, R.to_left (TVal w a, TVal w b) =
    (TVal w (I.pmeet w a (bits_interval w b)), TVal w b).
  (** The right exchange meets the bits with the interval's word-range common prefix. *)
  Parameter F_to_right : forall w a b, R.to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (K.pmeet w b (interval_prefix w a))).
  (** Pairs of other shapes are left unchanged. *)
  Parameter F_other : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    R.to_left x = x /\ R.to_right x = x.
End INTERVAL_BITS_PIN.
