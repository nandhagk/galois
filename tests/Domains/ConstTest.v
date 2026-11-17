(** * Constant domain examples

    These examples exercise annihilators, inverses and numeric expressions.
    For example, assuming x + 3 = 7 refines x to 4.

    Groups:
    - RawPayloadTests: a raw constant payload keeps its integer outside the width.
    - ForwardTests: forward transfers on constant operands.
    - AnnihilatorTests: zero and maximum operands fix the result of an operation.
    - TaggedTests: tagged operands of mismatched widths.
    - InverseTests: backward transfers from a known result.
    Builds on: Const and Tagged. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr.
From Galois.Domains Require Import WordSig Tagged Const ConstSig BitsLang Harness.
Import List.ListNotations Expr.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Payload := ConstWordCode WordLanguageCode.
Module Table := ConstWordTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
Module FunctionalPayload := ConstWord WordLanguage.

(** The forward transfer of an operation over tagged operands. *)
Definition forward_constants o xs := Domain.forward (BOp o) xs.

(** The backward transfer of an operation from a tagged result. *)
Definition assume_constants o r xs := Domain.backward (BOp o) r xs.

(** A tagged constant of width w with value z. *)
Definition const_constants w z := TVal w (Payload.pconst w z).

(** A tagged top of width w. *)
Definition top_constants w := TVal w (Payload.ptop w).

(** The payload of a tagged value at width rw, with bottom and top read as payloads. *)
Definition payload_at w (a : tagged (flat Z)) :=
  match a with TBot => FBot | TVal _ p => p | TAny => Payload.ptop w end.

(** Tagged operands built from (width, payload) pairs. *)
Definition tagged_args (xs : list (positive * flat Z)) :=
  map (fun wp => TVal (fst wp) (snd wp)) xs.

(** The payload of a forward transfer on (width, payload) operands. *)
Definition forward_payload o xs rw :=
  payload_at rw (forward_constants o (tagged_args xs)).

(** The payloads of a backward transfer from a payload result. *)
Definition assume_payload o xs rw r :=
  map (payload_at rw) (assume_constants o (TVal rw r) (tagged_args xs)).

(** One-bit width. *)
Definition w1 : width := 1%positive.

(** Eight-bit width. *)
Definition w8 : width := 8%positive.

(** Sixteen-bit width. *)
Definition w16 : width := 16%positive.

(** The operations whose forward transfer annihilates a zero or maximum operand. *)
Definition const_forward_ops := [bvmul; bvand; bvor; bvshl; bvlshr; bvashr; bvurem].

(** The operations that the backward examples invert. *)
Definition const_backward_ops := [bveq; bvne; bvadd; bvsub; bvxor].

(** * Raw payloads *)

Module RawPayloadTests.

  (** A raw constant of width eight holds the integer 257 outside the eight-bit range. *)
  Example raw_constant_holds_its_value :
    FunctionalPayload.pgamma 8%positive (FVal 257) 257.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A raw constant of width eight does not hold the integer 1. *)
  Example raw_constant_rejects_other_integer :
    ~ FunctionalPayload.pgamma 8%positive (FVal 257) 1.
  Proof.
    vm_compute. discriminate.
  Qed.

End RawPayloadTests.

(** * Forward transfers *)

Module ForwardTests.

  (** Adding constants wraps the sum modulo the width. *)
  Example add_wraps_modulo_width :
    forward_constants bvadd [const_constants w8 250; const_constants w8 10] =
      TVal w8 (FVal 4).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every forward operation rejects a bottom operand alongside a top operand. *)
  Example bottom_operand_rejected_by_forward_ops :
    map (fun o => forward_payload o [(w8, FBot); (w8, FTop)] w8)
      const_forward_ops = repeat FBot 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A maximum constant gives the maximum for or and top for the other forward operations. *)
  Example maximum_operand_forward_table :
    map (fun o => forward_payload o [(w8, FVal 255); (w8, FTop)] w8)
      const_forward_ops = [FTop; FTop; FVal 255; FTop; FTop; FTop; FTop].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ForwardTests.

(** * Annihilators *)

Module AnnihilatorTests.

  (** A zero operand fixes each forward operation's result, and a maximum operand fixes or. *)
  Example annihilators_of_forward_ops :
    [forward_constants bvmul [const_constants w8 0; top_constants w8];
     forward_constants bvand [top_constants w8; const_constants w8 0];
     forward_constants bvor [top_constants w8; const_constants w8 255];
     forward_constants bvshl [const_constants w8 0; top_constants w8];
     forward_constants bvlshr [const_constants w8 0; top_constants w8];
     forward_constants bvashr [const_constants w8 0; top_constants w8];
     forward_constants bvurem [const_constants w8 0; top_constants w8]] =
    [TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 255); TVal w8 (FVal 0);
     TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 0)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, the annihilators of each forward operation give the same results. *)
  Example one_bit_annihilators_of_forward_ops :
    map (fun o => forward_payload o
      [(w1, FVal (if match o with bvor => true | _ => false end then 1 else 0));
       (w1, FTop)] w1) const_forward_ops =
      [FVal 0; FVal 0; FVal 1; FVal 0; FVal 0; FVal 0; FVal 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

End AnnihilatorTests.

(* Old meet returned TBot; Base.meet now returns TVal w8 FBot.
Example tagged_payload_bottom :
  forward_constants bvadd [TVal w8 FBot; TAny] = TBot /\
  Base.meet (TVal w8 FBot) TAny = TBot.
Proof.
  vm_compute. split; reflexivity.
Qed.

*)

(** * Tagged operands *)

Module TaggedTests.

  (** A bottom payload operand makes the tagged forward result bottom. *)
  Example bottom_payload_forward_is_tagged_bottom :
    forward_constants bvadd [TVal w8 FBot; TAny] = TBot.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining operands of different widths gives the unknown tagged value. *)
  Example join_of_different_widths_is_any :
    Base.join (TVal w8 (FVal 0)) (TVal w16 (FVal 0)) = TAny.
  Proof. vm_compute. reflexivity. Qed.

  (** A forward addition of operands of different widths is the tagged bottom. *)
  Example forward_of_different_widths_is_tagged_bottom :
    forward_constants bvadd [TVal w8 (FVal 0); TVal w16 (FVal 0)] = TBot.
  Proof. vm_compute. reflexivity. Qed.

End TaggedTests.

(* Old backward returned [TBot; TBot]; current result is [TVal w8 FTop; TVal w16 FTop].
Example incompatible_widths :
  Base.join (TVal w8 (FVal 0)) (TVal w16 (FVal 0)) = TAny /\
  forward_constants bvadd [TVal w8 (FVal 0); TVal w16 (FVal 0)] = TBot /\
  assume_constants bvadd (TVal w8 (FVal 0)) [TVal w8 FTop; TVal w16 FTop] = [TBot; TBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

*)

(** * Inverses *)

Module InverseTests.

  (** An addition result and one operand refine the unknown operand. *)
  Example add_inverse_refines_unknown_operand :
    assume_constants bvadd (TVal w8 (FVal 7)) [TVal w8 FTop; TVal w8 (FVal 3)] =
      [TVal w8 (FVal 4); TVal w8 (FVal 3)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A subtraction result refines the unknown second operand. *)
  Example sub_inverse_refines_unknown_operand :
    assume_constants bvsub (TVal w8 (FVal 250)) [TVal w8 (FVal 3); TVal w8 FTop] =
      [TVal w8 (FVal 3); TVal w8 (FVal 9)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An exclusive-or result refines the unknown operand. *)
  Example xor_inverse_refines_unknown_operand :
    assume_constants bvxor (TVal w8 (FVal 5)) [TVal w8 FTop; TVal w8 (FVal 3)] =
      [TVal w8 (FVal 6); TVal w8 (FVal 3)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A complement result recovers the operand. *)
  Example not_inverse_recovers_operand :
    assume_constants bvnot (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 5)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negation result recovers the operand. *)
  Example neg_inverse_recovers_operand :
    assume_constants bvneg (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 6)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A true equality forces the unknown operand to equal the known one. *)
  Example eq_true_forces_equal_operand :
    assume_constants bveq (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 (FVal 42)] =
      [TVal w8 (FVal 42); TVal w8 (FVal 42)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A false disequality forces the unknown operand to equal the known one. *)
  Example ne_false_forces_equal_operand :
    assume_constants bvne (TVal w1 (FVal 0)) [TVal w8 (FVal 42); TVal w8 FTop] =
      [TVal w8 (FVal 42); TVal w8 (FVal 42)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Conflicting constants make add, subtract and exclusive-or inverses bottom. *)
  Example arithmetic_inverse_rejects_conflicting_constants :
    map (fun o => assume_payload o [(w8, FVal 1); (w8, FVal 2)]
      w8 (FVal 0)) [bvadd; bvsub; bvxor] = repeat [FBot; FBot] 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A complement inverse of an inconsistent constant is bottom. *)
  Example not_inverse_rejects_inconsistent_constant :
    assume_payload bvnot [(w8, FVal 0)] w8 (FVal 0) = [FBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negation inverse of an inconsistent constant is bottom. *)
  Example neg_inverse_rejects_inconsistent_constant :
    assume_payload bvneg [(w8, FVal 1)] w8 (FVal 0) = [FBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A true equality of distinct constants is bottom for both operands. *)
  Example eq_inverse_rejects_distinct_constants :
    assume_payload bveq [(w8, FVal 1); (w8, FVal 2)] w1 (FVal 1) = [FBot; FBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A false disequality of distinct constants is bottom for both operands. *)
  Example ne_inverse_rejects_distinct_constants :
    assume_payload bvne [(w8, FVal 1); (w8, FVal 2)] w1 (FVal 0) = [FBot; FBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, add, subtract, exclusive-or and equality refine the unknown operand. *)
  Example width_one_inverses_refine_unknown_operand :
    map (fun o => assume_payload o [(w1, FTop); (w1, FVal 1)]
      w1 (FVal 1)) [bvadd; bvsub; bvxor; bveq] =
      [[FVal 0; FVal 1]; [FVal 0; FVal 1]; [FVal 0; FVal 1]; [FVal 1; FVal 1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a false disequality forces the unknown operand to one. *)
  Example width_one_ne_inverse_forces_one :
    assume_payload bvne [(w1, FTop); (w1, FVal 1)] w1 (FVal 0) = [FVal 1; FVal 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a complement result of one recovers the operand zero. *)
  Example width_one_not_inverse_gives_zero :
    assume_payload bvnot [(w1, FTop)] w1 (FVal 1) = [FVal 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, a negation result of one recovers the operand one. *)
  Example width_one_neg_inverse_gives_one :
    assume_payload bvneg [(w1, FTop)] w1 (FVal 1) = [FVal 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

End InverseTests.

(* The old numeric expression assumption returned TVal w8 (FVal 4).
Example nested_expression_refinement :
  num_assume constants (fun _ => top_constants w8)
    (App bvadd [Var 0; Const w8 3]) (TVal w8 (FVal 7)) 0%nat = TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

*)
(* Old bottom-result backward returned [TBot; TBot]; current result is [TAny; TVal w8 FTop].
   The old mismatched-result-width case also returned [TBot; TBot]; current result is
   [TVal w8 FTop; TVal w8 FTop].
Example impossible_result_refines_every_operand :
  assume_constants bvadd TBot [TAny; TVal w8 FTop] = [TBot; TBot] /\
  assume_constants bvadd (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 FTop] = [TBot; TBot].
Proof.
  vm_compute. split; reflexivity.
Qed.

*)
(* The old numeric expression evaluator returned TVal w8 (FVal 9).
Example nested_abstract_evaluation :
  num_eval constants (fun _ => const_constants w8 5)
    (App bvadd [App bvmul [Var 0; Const w8 3]; Const w8 250]) = TVal w8 (FVal 9).
Proof.
  vm_compute. reflexivity.
Qed.



*)
