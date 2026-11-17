(** * Sign domain examples

    These examples exercise transfers, numeric refinement, intersection and finite height.
    For example, incompatible sign classes intersect to bottom.

    Groups:
    - [MeetTests] Intersection of sign classes.
    - [OneBitTests] Transfers at width one.
    - [ComparisonTests] Comparisons decide on signs.
    - [TransferTests] Bitwise and arithmetic transfers.
    - [ExtensionTests] Extensions and selection.
    - [ConstantTests] Constants and tagged abstraction at width sixty-four.
    - [RefinementTests] Tagged meet refines a sign.
    - [EmptyOperandTests] Empty operands give empty signs.

    Builds on: Sign. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr.
From Galois.Domains Require Import WordSig Tagged Sign SignSig BitsLang Harness.
Import List.ListNotations Expr.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Payload := SignCode WordLanguageCode.
Module Table := SignTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.

(** The forward transfer of an operation over tagged operands. *)
Definition forward_signs o xs := Domain.forward (BOp o) xs.

(** A tagged constant of width w with value z. *)
Definition const_signs w z := TVal w (Payload.pconst w z).

(** A tagged top of width w. *)
Definition top_signs w := TVal w (Payload.ptop w).

(** The payload of a tagged value at width w, with bottom and top read as payloads. *)
Definition payload_at w (a : tagged sgn) :=
  match a with TBot => Payload.pbot w | TVal _ p => p | TAny => Payload.ptop w end.

(** The payload of a forward transfer on (width, payload) operands. *)
Definition forward_payload o xs rw :=
  payload_at rw (forward_signs o (map (fun wp => TVal (fst wp) (snd wp)) xs)).

(** One-bit width. *)
Definition w1 : width := 1%positive.

(** Eight-bit width. *)
Definition w8 : width := 8%positive.

(** Sixteen-bit width. *)
Definition w16 : width := 16%positive.

(** The operand table that the empty-operand examples read. *)
Definition sign_entry_cases :=
  [(bvnot, [(w8, (Payload.ptop w8))], w8); (bvneg, [(w8, (Payload.ptop w8))], w8);
   (bvzext w8, [(w8, (Payload.ptop w8))], w16); (bvsext w8, [(w8, (Payload.ptop w8))], w16);
   (bvand, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8);
   (bvor, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8);
   (bvxor, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8);
   (bveq, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvne, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvult, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvule, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvslt, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvsle, [(w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w1);
   (bvite, [(w1, (Payload.ptop w8)); (w8, (Payload.ptop w8)); (w8, (Payload.ptop w8))], w8)].

(** * Meet *)

Module MeetTests.

  (** The meet of two sign classes keeps the sign that both contain. *)
  Example meet_keeps_common_sign :
    Payload.pmeet 8%positive (Sgn true true false) (Sgn false true true) =
      Sgn false true false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet of two disjoint sign classes is bottom. *)
  Example meet_of_disjoint_signs_is_bottom :
    Payload.pmeet 8%positive (Sgn true false false) (Sgn false false true) =
      Payload.pbot 8%positive.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MeetTests.

(** * One-bit operands *)

Module OneBitTests.

  (** The one-bit constant one has the negative sign. *)
  Example one_bit_one_has_negative_sign :
    const_signs w1 1 = TVal w1 (Sgn true false false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equal one-bit constants compare as true. *)
  Example one_bit_equal_constants_compare_true :
    forward_signs bveq [const_signs w1 1; const_signs w1 1] =
      TVal w1 (Sgn true false false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each binary operation with the sign it gives on two one-bit negatives. *)
  Definition one_bit_binary_cases : list (op * sgn) :=
    [(bvand, Sgn true false false); (bvor, Sgn true false false); (bvxor, Sgn false true true);
     (bveq, Sgn true false false); (bvne, Sgn false true false); (bvult, Sgn false true false);
     (bvule, Sgn true false false); (bvslt, Sgn false true false); (bvsle, Sgn true false false)].

  (** Every binary operation on two one-bit negatives gives the sign of its table row. *)
  Example one_bit_binary_entries :
    map (fun c => forward_payload (fst c)
      [(w1, Sgn true false false); (w1, Sgn true false false)] w1) one_bit_binary_cases =
      map snd one_bit_binary_cases.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Bitwise not of a one-bit negative is nonnegative. *)
  Example one_bit_not_of_negative_is_nonnegative :
    forward_payload bvnot [(w1, Sgn true false false)] w1 = Sgn false true true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Negation of a one-bit negative is nonzero. *)
  Example one_bit_neg_of_negative_is_nonzero :
    forward_payload bvneg [(w1, Sgn true false false)] w1 = Sgn true false true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Zero extension of a one-bit negative to two bits is nonnegative. *)
  Example one_bit_zero_extension_of_negative_is_nonnegative :
    forward_payload (bvzext 1%positive) [(w1, Sgn true false false)] 2%positive =
      Sgn false true true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Sign extension of a one-bit negative to two bits is negative. *)
  Example one_bit_sign_extension_of_negative_is_negative :
    forward_payload (bvsext 1%positive) [(w1, Sgn true false false)] 2%positive =
      Sgn true false false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A one-bit selection with an unknown condition joins the two branches. *)
  Example one_bit_ite_with_unknown_condition_joins_branches :
    forward_payload bvite
      [(w1, (Payload.ptop w8)); (w1, Sgn true false false); (w1, Sgn false true false)] w1 =
      Sgn true true false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End OneBitTests.

(** * Comparisons *)

Module ComparisonTests.

  (** Signed less than orders a negative value below a positive one. *)
  Example signed_less_than_orders_negative_first :
    forward_signs bvslt [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
      TVal w1 (Sgn true false false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unsigned less than orders a negative value as large, above a nonnegative one. *)
  Example unsigned_less_than_orders_negative_as_large :
    forward_signs bvult [TVal w8 (Sgn true false false); TVal w8 (Sgn false true true)] =
      TVal w1 (Sgn false true false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equality of a negative and a positive value is false. *)
  Example equality_of_negative_and_positive_is_false :
    forward_signs bveq [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
      TVal w1 (Sgn false true false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every comparison of a negative and a positive value gives its fixed answer. *)
  Example all_comparisons_of_negative_and_positive :
    map (fun o => forward_signs o
      [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)])
      [bveq; bvne; bvult; bvule; bvslt; bvsle] =
      [TVal w1 (Sgn false true false); TVal w1 (Sgn true false false);
       TVal w1 (Sgn false true false); TVal w1 (Sgn false true false);
       TVal w1 (Sgn true false false); TVal w1 (Sgn true false false)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ComparisonTests.

(** * Transfers *)

Module TransferTests.

  (** Bitwise and of a negative and a positive value is nonnegative. *)
  Example and_of_negative_and_positive_is_nonnegative :
    forward_signs bvand [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
      TVal w8 (Sgn false true true).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Bitwise or of a negative and a positive value is negative. *)
  Example or_of_negative_and_positive_is_negative :
    forward_signs bvor [TVal w8 (Sgn true false false); TVal w8 (Sgn false false true)] =
      TVal w8 (Sgn true false false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Exclusive or of two negatives is nonnegative. *)
  Example xor_of_two_negatives_is_nonnegative :
    forward_signs bvxor [TVal w8 (Sgn true false false); TVal w8 (Sgn true false false)] =
      TVal w8 (Sgn false true true).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Bitwise not of a negative is nonnegative. *)
  Example not_of_negative_is_nonnegative :
    forward_signs bvnot [TVal w8 (Sgn true false false)] = TVal w8 (Sgn false true true).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Negating the constant 128 at width eight gives a nonzero sign. *)
  Example neg_of_constant_128_is_nonzero :
    forward_signs bvneg [const_signs w8 128] = TVal w8 (Sgn true false true).
  Proof.
    vm_compute. reflexivity.
  Qed.

End TransferTests.

(** * Extensions *)

Module ExtensionTests.

  (** Zero extension of a negative eight-bit value to sixteen bits is nonnegative. *)
  Example zero_extension_of_negative_is_nonnegative :
    forward_signs (bvzext w8) [TVal w8 (Sgn true false false)] =
      TVal w16 (Sgn false true true).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Sign extension of a negative eight-bit value to sixteen bits stays negative. *)
  Example sign_extension_of_negative_is_negative :
    forward_signs (bvsext w8) [TVal w8 (Sgn true false false)] =
      TVal w16 (Sgn true false false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A selection with an unknown one-bit condition joins its two branches. *)
  Example ite_with_unknown_condition_joins_branches :
    forward_signs bvite [top_signs w1; TVal w8 (Sgn true false false);
      TVal w8 (Sgn false false true)] = TVal w8 (Sgn true false true).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ExtensionTests.

(** * Constants *)

Module ConstantTests.

  (** A constant beyond the width's range has the sign of its residue. *)
  Example overflowing_constant_has_sign_of_residue :
    Payload.pconst 64%positive (2 ^ 64 + 5) = Sgn false false true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant in range is positive. *)
  Example constant_in_range_is_positive :
    Payload.pconst 64%positive 5 = Sgn false false true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Minus one is negative at width sixty-four. *)
  Example minus_one_is_negative :
    Payload.pconst 64%positive (-1) = Sgn true false false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw tagged abstraction rejects a value above the unsigned range. *)
  Example abstraction_rejects_above_unsigned_range :
    Base.abst (64%positive, 2 ^ 64 + 5) = TAny.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw tagged abstraction gives a positive sign to five. *)
  Example abstraction_of_five_is_positive :
    Base.abst (64%positive, 5) = TVal 64%positive (Sgn false false true).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw tagged abstraction rejects a negative value. *)
  Example abstraction_rejects_negative :
    Base.abst (64%positive, -1) = TAny.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw tagged abstraction gives the zero sign to zero. *)
  Example abstraction_of_zero_is_zero_sign :
    Base.abst (64%positive, 0) = TVal 64%positive (Sgn false true false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw tagged abstraction gives a negative sign to the largest unsigned value. *)
  Example abstraction_of_maximum_is_negative :
    Base.abst (64%positive, 2 ^ 64 - 1) = TVal 64%positive (Sgn true false false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw tagged abstraction rejects the value just above the largest unsigned value. *)
  Example abstraction_rejects_unsigned_overflow :
    Base.abst (64%positive, 2 ^ 64) = TAny.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ConstantTests.

(** * Refinement *)

Module RefinementTests.

  (** The tagged meet keeps the zero sign that both operands contain. *)
  Example tagged_meet_keeps_common_sign :
    Base.meet (TVal w8 (Sgn false true true)) (TVal w8 (Sgn true true false)) =
      TVal w8 (Sgn false true false).
  Proof.
    vm_compute. reflexivity.
  Qed.

End RefinementTests.

(** * Empty operands *)

Module EmptyOperandTests.

  (** Every entry of the operand table gives the empty sign when its operands are empty. *)
  Example empty_operands_give_empty_signs :
    Forall (fun s => s = Sgn false false false)
      (map (fun '(o, xs, rw) => forward_payload o
        (map (fun wp => (fst wp, Sgn false false false)) xs) rw) sign_entry_cases).
  Proof.
    vm_compute. repeat constructor.
  Qed.

End EmptyOperandTests.
