(** * Circular interval port observations

    These examples exercise the public tagged harness and its circular interval table.
    For example, arithmetic across zero retains the circular result.

    Groups:
    - [NarrowingTests] Meets and narrowing of single arcs and pairs of arcs.
    - [ArithmeticTests] Modular, signed and division results of arcs, including crossing zero.
    - [WidthTests] Truncation, zero extension and sign extension.
    - [ComparisonTests] Unsigned, signed, choice and bitwise results over arcs.
    - [BackwardTests] Assumptions that narrow the operands of each operation.
    - [FullAliasTests] Full-width arcs under each width change.
    - [MalformedTests] Backward inputs with the wrong number of operands.
    - [ConsistencyTests] The assumed consistency of two operand arcs.

    Builds on: WrappedOps, Tagged and Harness. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang WordSig ValueSig IntervalSig WrappedSig Wrapped
  WrappedOps Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.
Local Abbreviation w8 := 8%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w16 := 16%positive.

(** * Fixtures *)

(** The wrapped interval module over the word language. *)
Module W := WrappedCode WordLanguageCode.
(** The wrapped interval table over the word language. *)
Module T := WrappedTableCode WordLanguageCode W.
(** The tagged wrapped module over the word language. *)
Module B := TaggedCode WordLanguageCode W.
(** The tagged table over the word language. *)
Module TT := TaggedTableCode WordLanguageCode W T.
(** The harness that runs the operations over the tagged table. *)
Module D := HarnessCode BitsLangCode B TT.
(** The operation modules of the wrapped domain, used for the payload observations. *)
Module Ops := WrappedOpsCode WordLanguageCode W.

(** Tags a wrapped value with its width-carrying position. *)
Definition tag (p : positive * wrapped) := TVal (fst p) (snd p).

(** Removes the tag, mapping bottom to the bottom and the unknown tag to the full range. *)
Definition untag (p : tagged wrapped) : wrapped :=
  match p with TBot => WBot | TAny => WFull | TVal _ a => a end.

(** The forward result of an operation over tagged operands. *)
Definition fwd (o : op) (xs : list (positive * wrapped)) (_ : positive) : wrapped :=
  untag (D.forward (BOp o) (map tag xs)).

(** The backward results of an operation for a result with the given width and value. *)
Definition back (o : op) (xs : list (positive * wrapped)) (rw : positive) (q : wrapped)
    : list wrapped := map untag (D.backward (BOp o) (TVal rw q) (map tag xs)).

(** Operand lists with the wrong number of operands for the backward operation. *)
Definition malformed_backward_inputs : list (list (positive * wrapped)) :=
  [[]; [(w1, WItv (-1) 2); (w4, WItv (-1) 17); (w8, WItv 10 9)]].

(** * Narrowing *)

Module NarrowingTests.

  (** Narrowing the full arc by the arc from 250 to 3 gives that arc. *)
  Example narrow_full :
    W.pnarrow w8 (WItv 10 9) (WItv 250 3) = WItv 250 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A one-bit arc from one to zero normalizes to the full range. *)
  Example one_bit_full : wrapped_norm 1%positive (WItv 1 0) = WFull.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Meeting the arc from 250 to 3 with the arc from 0 to 2 keeps the short arc. *)
  Example meet_single_arc :
    W.pmeet w8 (WItv 250 3) (WItv 0 2) = WItv 0 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Meeting two overlapping arcs keeps the arc from 0 to 200. *)
  Example meet_two_arcs :
    W.pmeet w8 (WItv 0 200) (WItv 150 50) = WItv 0 200.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Meeting two disjoint arcs gives bottom. *)
  Example meet_disjoint : W.pmeet w8 (WItv 250 3) (WItv 10 20) = WBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Meeting the full range with an arc gives the arc. *)
  Example meet_full_neutral : W.pmeet w8 WFull (WItv 250 3) = WItv 250 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NarrowingTests.

(** * Arithmetic *)

Module ArithmeticTests.

  (** Adding two arcs that wrap past 255 gives the arc from 251 to 6. *)
  Example add_wrap :
    fwd bvadd [(w8, WItv 250 255); (w8, WItv 1 7)] w8 = WItv 251 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Subtracting two arcs that wrap gives the arc from 1 to 9. *)
  Example sub_wrap :
    fwd bvsub [(w8, WItv 0 3); (w8, WItv 250 255)] w8 = WItv 1 9.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Negating the arc from 250 to 3 gives the arc from 253 to 6. *)
  Example neg_wrap :
    fwd bvneg [(w8, WItv 250 3)] w8 = WItv 253 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the unsigned arcs from 10 to 12 and from 2 to 3 gives the arc from 20 to 36. *)
  Example mul_unsigned :
    fwd bvmul [(w8, WItv 10 12); (w8, WItv 2 3)] w8 = WItv 20 36.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the arc from 250 to 255 by the arc from 2 to 3 gives the arc from 238 to 254. *)
  Example mul_signed :
    fwd bvmul [(w8, WItv 250 255); (w8, WItv 2 3)] w8 = WItv 238 254.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the arcs from 2 to 5 and from 3 to 4 gives the arc from 6 to 20. *)
  Example port_mul_shared_products :
    fwd bvmul [(w8, WItv 2 5); (w8, WItv 3 4)] w8 = WItv 6 20.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the arc from 250 to 3 that crosses zero by the arc from 2 to 2 gives 244 to 6. *)
  Example port_mul_shared_cross_zero :
    fwd bvmul [(w8, WItv 250 3); (w8, WItv 2 2)] w8 = WItv 244 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the full range by the zero arc gives the zero arc. *)
  Example port_mul_fast_zero :
    fwd bvmul [(w8, WFull); (w8, WItv 0 0)] w8 = WItv 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the arc from 100 to 50 by the arc from 2 to 2 gives 0 to 254. *)
  Example mul_both_poles :
    fwd bvmul [(w8, WItv 100 50); (w8, WItv 2 2)] w8 = WItv 0 254.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the point two by the arc from 100 to 50 also gives 0 to 254. *)
  Example mul_both_poles_right :
    fwd bvmul [(w8, WItv 2 2); (w8, WItv 100 50)] w8 = WItv 0 254.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the full range by two gives the arc from 0 to 254. *)
  Example mul_full_by_two :
    fwd bvmul [(w8, WFull); (w8, WItv 2 2)] w8 = WItv 0 254.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unsigned division by the zero arc gives the arc from 255 to 255. *)
  Example unsigned_zero_divisor :
    fwd bvudiv [(w8, WItv 1 3); (w8, WItv 0 0)] w8 = WItv 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division of the arc from 250 to 255 by two gives the arc from 253 to 0. *)
  Example signed_division_cross_zero :
    fwd bvsdiv [(w8, WItv 250 255); (w8, WItv 2 2)] w8 = WItv 253 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed remainder of the arc from 250 to 255 by two gives the arc from 255 to 0. *)
  Example signed_remainder_cross_zero :
    fwd bvsrem [(w8, WItv 250 255); (w8, WItv 2 2)] w8 = WItv 255 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division of a negative arc by the zero arc gives the arc from 1 to 1. *)
  Example negative_division_by_zero :
    fwd bvsdiv [(w8, WItv 250 255); (w8, WItv 0 0)] w8 = WItv 1 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division of bottom by an arc gives bottom. *)
  Example signed_division_bottom :
    fwd bvsdiv [(w8, WBot); (w8, WItv 2 2)] w8 = WBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed modulus by the arc from 254 to 254 gives the arc from 255 to 255. *)
  Example modulus_negative_divisor :
    fwd bvsmod [(w8, WItv 3 3); (w8, WItv 254 254)] w8 = WItv 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ArithmeticTests.

(** * Widths *)

Module WidthTests.

  (** Truncating the arc from 250 to 255 to four bits gives the arc from 10 to 15. *)
  Example trunc_modular_span :
    fwd (bvtrunc w4) [(w8, WItv 250 255)] w4 = WItv 10 15.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Zero extension of the arc from 250 to 255 keeps the arc at width sixteen. *)
  Example zext :
    fwd (bvzext w8) [(w8, WItv 250 255)] w16 = WItv 250 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Sign extension of the arc from 250 to 255 gives the arc from 65530 to 65535. *)
  Example sext :
    fwd (bvsext w8) [(w8, WItv 250 255)] w16 = WItv 65530 65535.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WidthTests.

(** * Comparisons *)

Module ComparisonTests.

  (** An unsigned less-than of the arcs from 0 to 3 and from 10 to 20 gives true. *)
  Example unsigned_comparison :
    fwd bvult [(w8, WItv 0 3); (w8, WItv 10 20)] w1 = WItv 1 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A signed less-than of the arc from 250 to 3 and the arc from 10 to 20 gives true. *)
  Example signed_comparison :
    fwd bvslt [(w8, WItv 250 3); (w8, WItv 10 20)] w1 = WItv 1 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A choice between the arcs from 250 to 3 and from 4 to 8 covers both arcs. *)
  Example ite_cover :
    fwd bvite [(w1, WFull); (w8, WItv 250 3); (w8, WItv 4 8)] w8 = WItv 250 8.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Bitwise and of the arc from 240 to 255 with 15 gives the arc from 0 to 15. *)
  Example and_mask :
    fwd bvand [(w8, WItv 240 255); (w8, WItv 15 15)] w8 = WItv 0 15.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Bitwise or of the arc from 1 to 2 with 4 gives the arc from 0 to 7. *)
  Example or_bound :
    fwd bvor [(w8, WItv 1 2); (w8, WItv 4 4)] w8 = WItv 0 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Bitwise exclusive or of the arc from 1 to 2 with 4 gives the arc from 0 to 7. *)
  Example xor_bound :
    fwd bvxor [(w8, WItv 1 2); (w8, WItv 4 4)] w8 = WItv 0 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ComparisonTests.

(** * Backward *)

Module BackwardTests.

  (** Assuming the unsigned less-than holds narrows the first operand to the arc from 0 to 9. *)
  Example assume_unsigned_true :
    back bvult [(w8, WItv 0 20); (w8, WItv 10 10)] w1
      (WItv 1 1) = [WItv 0 9; WItv 10 10].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming the unsigned less-than fails narrows the first operand to the arc from 10 to 20. *)
  Example assume_unsigned_false :
    back bvult [(w8, WItv 0 20); (w8, WItv 10 10)] w1
      (WItv 0 0) = [WItv 10 20; WItv 10 10].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming equality narrows both operands to the arc from 0 to 2. *)
  Example assume_equal :
    back bveq [(w8, WItv 250 3); (w8, WItv 0 2)] w1
      (WItv 1 1) = [WItv 0 2; WItv 0 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a modular sum of 5 narrows the first operand to 251. *)
  Example assume_modular_add :
    back bvadd [(w8, WItv 250 3); (w8, WItv 10 10)] w8
      (WItv 5 5) = [WItv 251 251; WItv 10 10].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a modular difference of 5 narrows the first operand to 255. *)
  Example assume_modular_sub :
    back bvsub [(w8, WItv 250 3); (w8, WItv 250 250)] w8
      (WItv 5 5) = [WItv 255 255; WItv 250 250].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a signed less-than holds narrows the first operand to the arc from 250 to 254. *)
  Example assume_signed_true :
    back bvslt [(w8, WItv 250 20); (w8, WItv 255 255)] w1
      (WItv 1 1) = [WItv 250 254; WItv 255 255].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a signed less-than that cannot hold gives bottom for both operands. *)
  Example assume_impossible_signed :
    back bvslt [(w8, WItv 0 20); (w8, WItv 255 255)] w1 (WItv 1 1) = [WBot; WBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a sign extension lands in 65532 to 65534 narrows the operand to 252 to 254. *)
  Example assume_sext :
    back (bvsext w8) [(w8, WItv 250 255)] w16
      (WItv 65532 65534) = [WItv 252 254].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a zero extension lands in 0 to 3 keeps the operand arc. *)
  Example assume_zext :
    back (bvzext w8) [(w8, WItv 250 3)] w16 (WItv 0 3) = [WItv 0 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a truncation to 3 to 5 keeps the operand arc that fits. *)
  Example assume_trunc_fitting :
    back (bvtrunc w4) [(w8, WItv 0 10)] w4
      (WItv 3 5) = [WItv 3 5].
  Proof.
    vm_compute. reflexivity.
  Qed.

End BackwardTests.

(** * Full aliases *)

Module FullAliasTests.

  (** The parts of each full-width arc equal the parts of the full range at width eight. *)
  Example parts_of_full_aliases :
    map (wrapped_parts w8) [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] =
    repeat (wrapped_parts w8 WFull) 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Sign extension of every full-width arc gives the full range. *)
  Example sext_of_full_aliases :
    map (fun a => fwd (bvsext w8) [(w8, a)] w16)
      [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat WFull 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Zero extension of every full-width arc gives the arc from 0 to 255. *)
  Example zext_of_full_aliases :
    map (fun a => fwd (bvzext w8) [(w8, a)] w16)
      [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat (WItv 0 255) 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Truncation of every full-width arc to four bits gives the full range. *)
  Example trunc_of_full_aliases :
    map (fun a => fwd (bvtrunc w4) [(w8, a)] w4)
      [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat WFull 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming a sign extension narrows every full-width arc to 252 to 254. *)
  Example assume_sext_of_full_aliases :
    map (fun a => back (bvsext w8) [(w8, a)] w16 (WItv 65532 65534))
      [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat [WItv 252 254] 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Assuming an unsigned less-than narrows every full-width arc against 10 to 10. *)
  Example assume_unsigned_of_full_aliases :
    map (fun a => back bvult [(w8, a); (w8, WItv 10 10)] w1 (WItv 1 1))
      [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] =
    repeat [WItv 0 9; WItv 10 10] 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FullAliasTests.

(** * Malformed *)

Module MalformedTests.

  (** The shared harness keeps the lengths of malformed backward inputs and refines them. *)
  Example harness_malformed_backward :
    map (fun xs =>
      let ys := back bvadd xs w1 (WItv 1 1) in
      (ys, Nat.eqb (length ys) (length xs),
       forallb (fun p => W.pleb (fst (fst p)) (snd p) (snd (fst p))) (combine xs ys)))
      malformed_backward_inputs =
    [([], true, true); ([WItv (-1) 2; WItv (-1) 17; WItv 10 9], true, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** The payload backward operation gives full, narrowed and full arcs for malformed input. *)
  Example payload_malformed_backward :
    map (fun xs =>
      let ys := Ops.backward bvadd w1 (WItv 1 1) xs in
      (ys, Nat.eqb (length ys) (length xs),
       forallb (fun p => W.pleb (fst (fst p)) (snd p) (snd (fst p))) (combine xs ys)))
      malformed_backward_inputs =
    [([], true, true); ([WFull; WItv 15 1; WFull], true, true)].
  Proof. vm_compute. reflexivity. Qed.

End MalformedTests.

(** * Consistency *)

Module ConsistencyTests.

  (** Two operand arcs that overlap at 4 to 5 are consistent with the result arc. *)
  Example accepts_overlapping_result :
    Ops.assume_consistent bvadd w8 w8 (I (Fin 1) (Fin 3)) (I (Fin 2) (Fin 4))
      (I (Fin 4) (Fin 5)) = true.
  Proof. vm_compute. auto. Qed.

  (** Two operand arcs are not consistent with a result arc from 20 to 21. *)
  Example rejects_disjoint_result :
    Ops.assume_consistent bvadd w8 w8 (I (Fin 1) (Fin 3)) (I (Fin 2) (Fin 4))
      (I (Fin 20) (Fin 21)) = false.
  Proof. vm_compute. auto. Qed.

  (** Operands of different widths are never consistent. *)
  Example rejects_width_mismatch :
    Ops.assume_consistent bvadd w8 w4 (I (Fin 1) (Fin 3)) (I (Fin 2) (Fin 4))
      (I (Fin 4) (Fin 5)) = false.
  Proof. vm_compute. auto. Qed.

End ConsistencyTests.
