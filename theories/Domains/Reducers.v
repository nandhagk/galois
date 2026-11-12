(** * Value reducers

    Reducers exchange facts between abstractions of the same concrete value.
    For example, an interval can remove endpoints excluded by a congruence.
    Builds on: ReducersSig, ProductSig, ValueSig and BitsLang. *)

From Stdlib Require Import NArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig BitsLang ReducersSig.

Module ReductionStepsCode (A B : VALUE_DOMAIN_OPS BitsLangCode)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  (* STUB-CODE *)
  Definition to_left (x : A.t * B.t) : A.t * B.t := x.
  (* STUB-CODE *)
  Definition to_right (x : A.t * B.t) : A.t * B.t := x.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End ReductionStepsCode.

Module ReductionSteps (A B : VALUE_DOMAIN BitsLang) <: REDUCTION_STEPS BitsLang A B.
  Include ReductionStepsCode A B.

  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof. Admitted. (* STUB *)

  Lemma reduce_mono : forall a b a' b',
    A.leb a a' = true -> B.leb b b' = true ->
    A.leb (fst (reduce (a, b))) (fst (reduce (a', b'))) = true /\
    B.leb (snd (reduce (a, b))) (snd (reduce (a', b'))) = true.
  Proof. Admitted. (* STUB *)

  Lemma reduce_idem : forall a b,
    A.leb (fst (reduce (a, b))) (fst (reduce (reduce (a, b)))) = true /\
    B.leb (snd (reduce (a, b))) (snd (reduce (reduce (a, b)))) = true.
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
End ReductionSteps.

Module ReductionStepsT (A B : VALUE_DOMAIN_T BitsLangT)
    <: REDUCTION_STEPS_ALL BitsLangT A B.
  Include ReductionSteps A B.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.

  Definition c_reduce : N := 1. (* STUB *)
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition c_exchange : N := 1. (* STUB *)
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
  Lemma reduce_bigO : bigO (fun _ => True)
    (fun x => N.of_nat (A.size (fst x) + B.size (snd x) + 1)) T_reduce.
  Proof. Admitted. (* STUB *)

  Definition k_exchange : N := 1. (* STUB *)
  Lemma F1_steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof. Admitted. (* STUB *)
  Lemma F2_steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof. Admitted. (* STUB *)
  Lemma T1_steps : forall x, (T_reduce x <= k_exchange *
    (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof. Admitted. (* STUB *)
End ReductionStepsT.

Module WrappedBitsCode := ReductionStepsCode.
Module WrappedBits := ReductionSteps.
Module WrappedBitsT := ReductionStepsT.
Module IntervalCongrCode := ReductionStepsCode.
Module IntervalCongr := ReductionSteps.
Module IntervalCongrT := ReductionStepsT.
Module IntervalBitsCode := ReductionStepsCode.
Module IntervalBits := ReductionSteps.
Module IntervalBitsT := ReductionStepsT.
