(** * Integer language observations

    Integer operators evaluate their documented operand shapes.
    For example, integer addition adds two signed operands.
    Builds on: ZLang. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import IntervalSig ZLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Example arithmetic_and_arity :
  ZLangCode.eval ZAdd [(-2); 5] = Some 3 /\
  ZLangCode.eval ZSub [2; 5] = Some (-3) /\
  ZLangCode.eval ZMul [(-2); 5] = Some (-10) /\
  ZLangCode.eval ZAdd [2] = None.
Proof. vm_compute. repeat split. Qed.

Example division_and_shifts :
  ZLangCode.eval ZDiv [7; 2] = Some 3 /\
  ZLangCode.eval ZDiv [7; 0] = None /\
  ZLangCode.eval ZDiv [(-1); 2] = None /\
  ZLangCode.eval ZRem [7; 2] = Some 1 /\
  ZLangCode.eval ZShl [3; 2] = Some 12 /\
  ZLangCode.eval ZShl [3; (-1)] = None.
Proof. vm_compute. repeat split. Qed.

Example literals_and_comparisons :
  ZLangCode.literal (ZConst (-4)) = Some (-4) /\
  ZLangCode.literal ZAdd = None /\
  ZLangCode.eval (ZCmp Lt) [2; 3] = Some 1 /\
  ZLangCode.eval (ZCmp Eq) [2; 3] = Some 0.
Proof. vm_compute. repeat split. Qed.
