(** * Integer interval guards

    These examples check comparison refinement and half-infinite arithmetic.
    For example, x < 10 bounds x above by 9.
    Builds on: Interval, ZLang and Thresholds. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig Thresholds ZLang Interval.
Import List.ListNotations.
Local Open Scope Z_scope.

Module IV := IntervalCode ZLangCode ThresholdsCode.

Example lt_half_infinite :
  IV.guard (ZGuardCmp Lt) [I (Fin 0) PosInf; IV.abst 10] =
    [I (Fin 0) (Fin 9); IV.abst 10].
Proof. vm_compute; reflexivity. Qed.

Example gt_empty :
  IV.guard (ZGuardCmp Gt) [I (Fin 0) (Fin 10); IV.abst 10] =
    [IBot; IBot].
Proof. vm_compute; reflexivity. Qed.

Example eq_disjoint :
  IV.guard (ZGuardCmp Eq) [IV.abst 9; IV.abst 10] = [IBot; IBot].
Proof. vm_compute; reflexivity. Qed.

Example strict_both_unbounded :
  IV.guard (ZGuardCmp Lt) [IV.top; IV.top] = [IV.top; IV.top].
Proof. vm_compute; reflexivity. Qed.

Example add_half_infinite :
  IV.add (I (Fin 0) PosInf) (IV.abst 1) = I (Fin 1) PosInf.
Proof. vm_compute; reflexivity. Qed.

Example sub_half_infinite :
  IV.sub (I NegInf (Fin 10)) (IV.abst 1) = I NegInf (Fin 9).
Proof. vm_compute; reflexivity. Qed.
