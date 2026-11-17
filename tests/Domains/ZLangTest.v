(** * Integer language observations

    Integer operators evaluate their documented operand shapes.
    For example, integer addition adds two signed operands.
    Builds on: ZLang. *)

(* Groups:
   - Arithmetic: addition, subtraction and multiplication, with their arity.
   - Division: quotient, remainder and shifts, with their zero and negative cases.
   - Literals: constants and comparisons. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import IntervalSig ZLang.
Import List.ListNotations.

(** * Arithmetic *)

Module ArithmeticTests.

  Local Open Scope Z_scope.

  (** Addition of a negative and a positive operand gives their sum. *)
  Example add_signed_operands :
    ZLangCode.eval ZAdd [(-2); 5] = Some 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Subtraction gives the first operand minus the second. *)
  Example sub_gives_difference :
    ZLangCode.eval ZSub [2; 5] = Some (-3).
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplication of a negative and a positive operand gives a negative product. *)
  Example mul_signed_operands :
    ZLangCode.eval ZMul [(-2); 5] = Some (-10).
  Proof. vm_compute. reflexivity. Qed.

  (** Addition with one operand has no result. *)
  Example add_rejects_wrong_arity :
    ZLangCode.eval ZAdd [2] = None.
  Proof. vm_compute. reflexivity. Qed.

End ArithmeticTests.

(** * Division and shifts *)

Module DivisionTests.

  Local Open Scope Z_scope.

  (** Division truncates the quotient of two positive operands. *)
  Example div_truncates_quotient :
    ZLangCode.eval ZDiv [7; 2] = Some 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Division by zero has no result. *)
  Example div_by_zero_has_no_result :
    ZLangCode.eval ZDiv [7; 0] = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Division of a negative dividend has no result. *)
  Example div_rejects_negative_dividend :
    ZLangCode.eval ZDiv [(-1); 2] = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Remainder gives what is left after division. *)
  Example rem_gives_remainder :
    ZLangCode.eval ZRem [7; 2] = Some 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift multiplies by a power of two. *)
  Example shl_multiplies_by_power_of_two :
    ZLangCode.eval ZShl [3; 2] = Some 12.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by a negative amount has no result. *)
  Example shl_rejects_negative_amount :
    ZLangCode.eval ZShl [3; (-1)] = None.
  Proof. vm_compute. reflexivity. Qed.

End DivisionTests.

(** * Literals and comparisons *)

Module LiteralTests.

  Local Open Scope Z_scope.

  (** An integer constant is a literal with its value. *)
  Example constant_is_literal :
    ZLangCode.literal (ZConst (-4)) = Some (-4).
  Proof. vm_compute. reflexivity. Qed.

  (** An operator is not a literal. *)
  Example operator_is_not_literal :
    ZLangCode.literal ZAdd = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A less-than comparison that holds evaluates to one. *)
  Example lt_holds_gives_one :
    ZLangCode.eval (ZCmp Lt) [2; 3] = Some 1.
  Proof. vm_compute. reflexivity. Qed.

  (** An equality comparison that fails evaluates to zero. *)
  Example eq_fails_gives_zero :
    ZLangCode.eval (ZCmp Eq) [2; 3] = Some 0.
  Proof. vm_compute. reflexivity. Qed.

End LiteralTests.
