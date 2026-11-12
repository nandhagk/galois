(** * Circular interval port observations

    These examples exercise the public tagged harness and its circular interval table.
    For example, arithmetic across zero retains the circular result.
    Builds on: WrappedOps, Tagged and Harness. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang WordSig WrappedSig Wrapped WrappedOps Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.
Local Abbreviation w8 := 8%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w16 := 16%positive.
Module W := WrappedCode WordLanguageCode.
Module T := WrappedTableCode WordLanguageCode W.
Module B := TaggedCode WordLanguageCode W.
Module TT := TaggedTableCode WordLanguageCode W T.
Module D := HarnessCode BitsLangCode B TT.
Definition tag (p : positive * wrapped) := TVal (fst p) (snd p).
Definition untag (p : tagged wrapped) : wrapped :=
  match p with TBot => WBot | TAny => WFull | TVal _ a => a end.
Definition fwd (o : op) (xs : list (positive * wrapped)) (_ : positive) : wrapped :=
  untag (D.forward (BOp o) (map tag xs)).
Definition back (o : op) (xs : list (positive * wrapped)) (rw : positive) (q : wrapped)
    : list wrapped := map untag (D.backward (BOp o) (TVal rw q) (map tag xs)).

Example wrapped_narrow_full :
  W.pnarrow w8 (WItv 10 9) (WItv 250 3) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_one_bit_full : wrapped_norm 1%positive (WItv 1 0) = WFull.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_single_arc :
  W.pmeet w8 (WItv 250 3) (WItv 0 2) = WItv 0 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_two_arcs :
  W.pmeet w8 (WItv 0 200) (WItv 150 50) = WItv 0 200.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_disjoint : W.pmeet w8 (WItv 250 3) (WItv 10 20) = WBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_add_wrap :
  fwd bvadd [(w8, WItv 250 255); (w8, WItv 1 7)] w8 = WItv 251 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_sub_wrap :
  fwd bvsub [(w8, WItv 0 3); (w8, WItv 250 255)] w8 = WItv 1 9.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_neg_wrap :
  fwd bvneg [(w8, WItv 250 3)] w8 = WItv 253 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_unsigned :
  fwd bvmul [(w8, WItv 10 12); (w8, WItv 2 3)] w8 = WItv 20 36.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_signed :
  fwd bvmul [(w8, WItv 250 255); (w8, WItv 2 3)] w8 = WItv 238 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_unsigned_zero_divisor :
  fwd bvudiv [(w8, WItv 1 3); (w8, WItv 0 0)] w8 = WItv 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_division_cross_zero :
  fwd bvsdiv [(w8, WItv 250 255); (w8, WItv 2 2)] w8 = WItv 253 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_remainder_cross_zero :
  fwd bvsrem [(w8, WItv 250 255); (w8, WItv 2 2)] w8 = WItv 255 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_trunc_modular_span :
  fwd (bvtrunc w4) [(w8, WItv 250 255)] w4 = WItv 10 15.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_zext :
  fwd (bvzext w8) [(w8, WItv 250 255)] w16 = WItv 250 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_sext :
  fwd (bvsext w8) [(w8, WItv 250 255)] w16 = WItv 65530 65535.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_unsigned_comparison :
  fwd bvult [(w8, WItv 0 3); (w8, WItv 10 20)] w1 = WItv 1 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_comparison :
  fwd bvslt [(w8, WItv 250 3); (w8, WItv 10 20)] w1 = WItv 1 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_unsigned_true :
  back bvult [(w8, WItv 0 20); (w8, WItv 10 10)] w1
    (WItv 1 1) = [WItv 0 9; WItv 10 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_equal :
  back bveq [(w8, WItv 250 3); (w8, WItv 0 2)] w1
    (WItv 1 1) = [WItv 0 2; WItv 0 2].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_modular_add :
  back bvadd [(w8, WItv 250 3); (w8, WItv 10 10)] w8
    (WItv 5 5) = [WItv 251 251; WItv 10 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_sext :
  back (bvsext w8) [(w8, WItv 250 255)] w16
    (WItv 65532 65534) = [WItv 252 254].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_trunc_fitting :
  back (bvtrunc w4) [(w8, WItv 0 10)] w4
    (WItv 3 5) = [WItv 3 5].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_and_mask :
  fwd bvand [(w8, WItv 240 255); (w8, WItv 15 15)] w8 = WItv 0 15.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_or_bound :
  fwd bvor [(w8, WItv 1 2); (w8, WItv 4 4)] w8 = WItv 0 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_xor_bound :
  fwd bvxor [(w8, WItv 1 2); (w8, WItv 4 4)] w8 = WItv 0 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_modulus_negative_divisor :
  fwd bvsmod [(w8, WItv 3 3); (w8, WItv 254 254)] w8 = WItv 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_negative_division_by_zero :
  fwd bvsdiv [(w8, WItv 250 255); (w8, WItv 0 0)] w8 = WItv 1 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_division_bottom :
  fwd bvsdiv [(w8, WBot); (w8, WItv 2 2)] w8 = WBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_cover :
  fwd bvite [(w1, WFull); (w8, WItv 250 3); (w8, WItv 4 8)] w8 = WItv 250 8.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_unsigned_false :
  back bvult [(w8, WItv 0 20); (w8, WItv 10 10)] w1
    (WItv 0 0) = [WItv 10 20; WItv 10 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_signed_true :
  back bvslt [(w8, WItv 250 20); (w8, WItv 255 255)] w1
    (WItv 1 1) = [WItv 250 254; WItv 255 255].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_modular_sub :
  back bvsub [(w8, WItv 250 3); (w8, WItv 250 250)] w8
    (WItv 5 5) = [WItv 255 255; WItv 250 250].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_zext :
  back (bvzext w8) [(w8, WItv 250 3)] w16 (WItv 0 3) = [WItv 0 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_impossible_signed :
  back bvslt [(w8, WItv 0 20); (w8, WItv 255 255)] w1 (WItv 1 1) = [WBot; WBot].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_full_neutral : W.pmeet w8 WFull (WItv 250 3) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_both_poles :
  fwd bvmul [(w8, WItv 100 50); (w8, WItv 2 2)] w8 = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_both_poles_right :
  fwd bvmul [(w8, WItv 2 2); (w8, WItv 100 50)] w8 = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_full_by_two :
  fwd bvmul [(w8, WFull); (w8, WItv 2 2)] w8 = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_parts :
  map (wrapped_parts w8) [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] =
  repeat (wrapped_parts w8 WFull) 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_sext :
  map (fun a => fwd (bvsext w8) [(w8, a)] w16)
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat WFull 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_zext :
  map (fun a => fwd (bvzext w8) [(w8, a)] w16)
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat (WItv 0 255) 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_trunc :
  map (fun a => fwd (bvtrunc w4) [(w8, a)] w4)
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat WFull 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_assume_sext :
  map (fun a => back (bvsext w8) [(w8, a)] w16 (WItv 65532 65534))
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat [WItv 252 254] 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_assume_unsigned :
  map (fun a => back bvult [(w8, a); (w8, WItv 10 10)] w1 (WItv 1 1))
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] =
  repeat [WItv 0 9; WItv 10 10] 4.
Proof.
  vm_compute. reflexivity.
Qed.

Definition malformed_backward_inputs : list (list (positive * wrapped)) :=
  [[]; [(w1, WItv (-1) 2); (w4, WItv (-1) 17); (w8, WItv 10 9)]].

(* The source expected [WFull; WItv 15 1; WFull]. The shared harness returns
   [WItv (-1) 2; WItv (-1) 17; WItv 10 9] for the malformed three-operand input. *)
Example wrapped_backward_malformed_fallback_count_and_refinement :
  map (fun xs =>
    let ys := back bvadd xs w1 (WItv 1 1) in
    (ys, Nat.eqb (length ys) (length xs),
     forallb (fun p => W.pleb (fst (fst p)) (snd p) (snd (fst p))) (combine xs ys)))
    malformed_backward_inputs =
  [([], true, true); ([WItv (-1) 2; WItv (-1) 17; WItv 10 9], true, true)].
Proof. vm_compute. reflexivity. Qed.

(* The landed observation used the old payload-level malformed fallback.
Example wrapped_backward_malformed_fallback_count_and_refinement :
  map (fun xs =>
    let ys := passume D bvadd xs w1 (WItv 1 1) in
    (ys, Nat.eqb (length ys) (length xs),
     forallb (fun p =>
       leb (plat D (fst (fst p))) (snd p) (snd (fst p))) (combine xs ys)))
    wrapped_malformed_backward_inputs =
  [([], true, true); ([WFull; WItv 15 1; WFull], true, true)].
Proof.
  vm_compute. reflexivity.
Qed.
*)

Module Ops := WrappedOpsCode WordLanguageCode W.
Example wrapped_payload_malformed_backward :
  map (fun xs =>
    let ys := Ops.backward bvadd w1 (WItv 1 1) xs in
    (ys, Nat.eqb (length ys) (length xs),
     forallb (fun p => W.pleb (fst (fst p)) (snd p) (snd (fst p))) (combine xs ys)))
    malformed_backward_inputs =
  [([], true, true); ([WFull; WItv 15 1; WFull], true, true)].
Proof. vm_compute. reflexivity. Qed.
