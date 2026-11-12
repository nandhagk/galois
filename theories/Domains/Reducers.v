(** * Value reducers

    Reducers exchange facts between abstractions of the same concrete word.
    For example, a known-bit payload can refine an interval endpoint.
    Builds on: ReducersSig and Tagged. *)

From Stdlib Require Import NArith ZArith.
From Argent Require Import Time Std BigO.
From Galois.Domains Require Import ValueSig BitsLang WordSig KnownBitsSig WrappedSig
  IntervalSig CongruenceSig ThresholdsSig ReducersSig Tagged.

(** The order used by tagged word domains. *)
Definition reducer_tagged_leb {P} (pleb : positive -> P -> P -> bool)
    (pis_bot : positive -> P -> bool) (a b : tagged P) : bool :=
  match a, b with
  | TBot, _ => true
  | _, TAny => true
  | TVal w p, TVal v q => if Pos.eqb w v then pleb w p q else pis_bot w p
  | TVal w p, TBot => pis_bot w p
  | _, _ => false
  end.

Module WrappedBitsCode (L : WORD_LANGUAGE_OPS) (A0 : WORD_PAYLOAD_OPS L with Definition p := wrapped)
    (B0 : WORD_PAYLOAD_OPS L with Definition p := tnum)
    (A : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged A0.p)
    (B : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged B0.p)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  Definition to_left (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w (A0.pmeet w a (bits_hull w b)), TVal v b) else x
    | _ => x
    end.
  Definition to_right (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w a, TVal v (B0.pmeet w b (arc_prefix w a))) else x
    | _ => x
    end.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End WrappedBitsCode.

Module WrappedBits (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (A0 : WRAPPED L)
    (B0 : KNOWN_BITS L C)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged A0.p
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged B0.p
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: REDUCTION_STEPS BitsLang A B.
  Include WrappedBitsCode L A0 B0 A B.
  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma left_frame : forall x, snd (to_left x) = snd x.
  Proof. Admitted. (* STUB *)
  Lemma right_frame : forall x, fst (to_right x) = fst x.
  Proof. Admitted. (* STUB *)
  Lemma left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  Proof. Admitted. (* STUB *)
  Lemma right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma reduce_steps : forall x, reduce x = to_right (to_left x).
  Proof. Admitted. (* STUB *)
  Lemma F_to_left : forall w a b, to_left (TVal w a, TVal w b) =
    (TVal w (A0.pmeet w a (bits_hull w b)), TVal w b).
  Proof. Admitted. (* STUB *)
  Lemma F_to_right : forall w a b, to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (B0.pmeet w b (arc_prefix w a))).
  Proof. Admitted. (* STUB *)
  Lemma F_other : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    to_left x = x /\ to_right x = x.
  Proof. Admitted. (* STUB *)

End WrappedBits.

Module IntervalCongrCode (L : WORD_LANGUAGE_OPS) (A0 : WORD_PAYLOAD_OPS L with Definition p := itv)
    (B0 : WORD_PAYLOAD_OPS L with Definition p := congr)
    (A : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged A0.p)
    (B : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged B0.p)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  Definition to_left (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w (A0.pmeet w a (congr_interval w a b)), TVal v b) else x
    | _ => x
    end.
  Definition to_right (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w a, TVal v (B0.pmeet w b (interval_congr a))) else x
    | _ => x
    end.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End IntervalCongrCode.

Module IntervalCongr (L : WORD_LANGUAGE) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) (A0 : INTERVAL_PAYLOAD_PINNED L T S)
    (B0 : CONGRUENCE L)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged A0.p
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged B0.p
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: REDUCTION_STEPS BitsLang A B.
  Include IntervalCongrCode L A0 B0 A B.
  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma left_frame : forall x, snd (to_left x) = snd x.
  Proof. Admitted. (* STUB *)
  Lemma right_frame : forall x, fst (to_right x) = fst x.
  Proof. Admitted. (* STUB *)
  Lemma left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  Proof. Admitted. (* STUB *)
  Lemma right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma reduce_steps : forall x, reduce x = to_right (to_left x).
  Proof. Admitted. (* STUB *)
  Lemma F_to_left : forall w a b, to_left (TVal w a, TVal w b) =
    (TVal w (A0.pmeet w a (congr_interval w a b)), TVal w b).
  Proof. Admitted. (* STUB *)
  Lemma F_to_right : forall w a b, to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (B0.pmeet w b (interval_congr a))).
  Proof. Admitted. (* STUB *)
  Lemma F_other : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    to_left x = x /\ to_right x = x.
  Proof. Admitted. (* STUB *)

End IntervalCongr.

Module IntervalBitsCode (L : WORD_LANGUAGE_OPS) (A0 : WORD_PAYLOAD_OPS L with Definition p := itv)
    (B0 : WORD_PAYLOAD_OPS L with Definition p := tnum)
    (A : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged A0.p)
    (B : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged B0.p)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  Definition to_left (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w (A0.pmeet w a (bits_interval w b)), TVal v b) else x
    | _ => x
    end.
  Definition to_right (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w a, TVal v (B0.pmeet w b (interval_prefix w a))) else x
    | _ => x
    end.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End IntervalBitsCode.

Module IntervalBits (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) (A0 : INTERVAL_PAYLOAD_PINNED L T S)
    (B0 : KNOWN_BITS L C)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged A0.p
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged B0.p
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: REDUCTION_STEPS BitsLang A B.
  Include IntervalBitsCode L A0 B0 A B.
  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma left_frame : forall x, snd (to_left x) = snd x.
  Proof. Admitted. (* STUB *)
  Lemma right_frame : forall x, fst (to_right x) = fst x.
  Proof. Admitted. (* STUB *)
  Lemma left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  Proof. Admitted. (* STUB *)
  Lemma left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  Proof. Admitted. (* STUB *)
  Lemma right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma reduce_steps : forall x, reduce x = to_right (to_left x).
  Proof. Admitted. (* STUB *)
  Lemma F_to_left : forall w a b, to_left (TVal w a, TVal w b) =
    (TVal w (A0.pmeet w a (bits_interval w b)), TVal w b).
  Proof. Admitted. (* STUB *)
  Lemma F_to_right : forall w a b, to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (B0.pmeet w b (interval_prefix w a))).
  Proof. Admitted. (* STUB *)
  Lemma F_other : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    to_left x = x /\ to_right x = x.
  Proof. Admitted. (* STUB *)

End IntervalBits.

Module WrappedBitsT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (A0 : WRAPPED_T L)
    (B0 : KNOWN_BITS_T L C)
    (A : VALUE_DOMAIN_T BitsLangT with Definition t := tagged A0.p
      with Definition size := tagged_size A0.psize
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN_T BitsLangT with Definition t := tagged B0.p
      with Definition size := tagged_size B0.psize
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: WRAPPED_BITS_ALL A B.
  Include WrappedBits L C A0 B0 A B.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.
  Definition c_exchange : N := 1. (* STUB *)
  Definition c_reduce : N := 1. (* STUB *)
  Definition k_exchange : N := 1. (* STUB *)
  Lemma T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F1_steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof. Admitted. (* STUB *)
  Lemma F2_steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma T1_steps : forall x, (T_reduce x <=
    k_exchange * (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_bigO : bigO (fun _ => True)
    (fun x => N.of_nat (A.size (fst x) + B.size (snd x) + 1)) T_reduce.
  Proof. Admitted. (* STUB *)
End WrappedBitsT.

Module IntervalCongrT (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T)
    (A0 : INTERVAL_PAYLOAD_PINNED_T L T S)
    (B0 : CONGRUENCE_T L)
    (A : VALUE_DOMAIN_T BitsLangT with Definition t := tagged A0.p
      with Definition size := tagged_size A0.psize
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN_T BitsLangT with Definition t := tagged B0.p
      with Definition size := tagged_size B0.psize
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: INTERVAL_CONGR_ALL A B.
  Include IntervalCongr L T S A0 B0 A B.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.
  Definition c_exchange : N := 1. (* STUB *)
  Definition c_reduce : N := 1. (* STUB *)
  Definition k_exchange : N := 1. (* STUB *)
  Lemma T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F1_steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof. Admitted. (* STUB *)
  Lemma F2_steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma T1_steps : forall x, (T_reduce x <=
    k_exchange * (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_bigO : bigO (fun _ => True)
    (fun x => N.of_nat (A.size (fst x) + B.size (snd x) + 1)) T_reduce.
  Proof. Admitted. (* STUB *)
End IntervalCongrT.

Module IntervalBitsT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T) (A0 : INTERVAL_PAYLOAD_PINNED_T L T S)
    (B0 : KNOWN_BITS_T L C)
    (A : VALUE_DOMAIN_T BitsLangT with Definition t := tagged A0.p
      with Definition size := tagged_size A0.psize
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN_T BitsLangT with Definition t := tagged B0.p
      with Definition size := tagged_size B0.psize
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: INTERVAL_BITS_ALL A B.
  Include IntervalBits L C T S A0 B0 A B.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.
  Definition c_exchange : N := 1. (* STUB *)
  Definition c_reduce : N := 1. (* STUB *)
  Definition k_exchange : N := 1. (* STUB *)
  Lemma T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F1_steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof. Admitted. (* STUB *)
  Lemma F2_steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma T1_steps : forall x, (T_reduce x <=
    k_exchange * (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_bigO : bigO (fun _ => True)
    (fun x => N.of_nat (A.size (fst x) + B.size (snd x) + 1)) T_reduce.
  Proof. Admitted. (* STUB *)
End IntervalBitsT.
