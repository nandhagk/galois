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

(** Bottom returns before the shift cutoff is computed. *)
Example shl_bottom_before_cutoff :
  IV.shl IBot (I (Fin 2) (Fin 3)) = IBot.
Proof.
  vm_compute. reflexivity.
Qed.

(** An unbounded lower endpoint returns top before cutoff preparation. *)
Example shl_top_before_cutoff :
  IV.shl IV.top (I (Fin 2) (Fin 3)) = IV.top.
Proof.
  vm_compute. reflexivity.
Qed.

(** Finite operands still compute both shifted endpoints below the cutoff. *)
Example shl_finite_below_cutoff :
  IV.shl (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 3)) = I (Fin 4) (Fin 32).
Proof.
  vm_compute. reflexivity.
Qed.

(** A shift beyond the cutoff retains the lower endpoint and drops the upper bound. *)
Example shl_finite_beyond_cutoff :
  IV.shl (I (Fin 1) (Fin 4)) (I (Fin 128) (Fin 129)) = I (Fin 1) PosInf.
Proof.
  vm_compute. reflexivity.
Qed.

(** Sharing the half-width power preserves the wholly nonnegative split. *)
Example signed_split_shared_half_positive :
  IV.signed_split 64%positive (I (Fin 1) (Fin 4)) = [I (Fin 1) (Fin 4); IBot].
Proof.
  vm_compute. reflexivity.
Qed.

(** A split across the sign boundary keeps both signed ranges. *)
Example signed_split_shared_half_crossing :
  IV.signed_split 8%positive (I (Fin 120) (Fin 140)) =
    [I (Fin 120) (Fin 127); I (Fin (-128)) (Fin (-116))].
Proof.
  vm_compute. reflexivity.
Qed.

(** The smallest positive width keeps zero and translates its sign bit to minus one. *)
Example signed_split_shared_half_one_bit :
  IV.signed_split 1%positive (I (Fin 0) (Fin 1)) =
    [I (Fin 0) (Fin 0); I (Fin (-1)) (Fin (-1))].
Proof.
  vm_compute. reflexivity.
Qed.
