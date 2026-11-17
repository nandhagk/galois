(** * Integer interval guards

    These examples check comparison refinement and half-infinite arithmetic.
    For example, x < 10 bounds x above by 9.

    Groups:
    - [GuardTests] Comparisons narrow or empty their operands.
    - [ArithmeticTests] Adding or subtracting a constant shifts a half-infinite range.
    - [ShiftTests] Left shifts below and beyond the shift cutoff.
    - [SignedSplitTests] Splitting an interval at the sign boundary.
    Builds on: Interval, ZLang and Thresholds. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig Thresholds ZLang Interval.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module IV := IntervalCode ZLangCode ThresholdsCode.

(** * Guards *)

Module GuardTests.

  (** A strict upper bound on a value bounds its half-infinite interval above by one less. *)
  Example strict_less_than_bounds_upper_endpoint :
    IV.guard (ZGuardCmp Lt) [I (Fin 0) PosInf; IV.abst 10] =
      [I (Fin 0) (Fin 9); IV.abst 10].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A strict comparison with an interval entirely above it leaves no value. *)
  Example strict_greater_than_disjoint_is_empty :
    IV.guard (ZGuardCmp Gt) [I (Fin 0) (Fin 10); IV.abst 10] =
      [IBot; IBot].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Equality of two disjoint singletons leaves no value. *)
  Example equality_of_disjoint_singletons_is_empty :
    IV.guard (ZGuardCmp Eq) [IV.abst 9; IV.abst 10] = [IBot; IBot].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A strict comparison of two unbounded intervals keeps both unchanged. *)
  Example strict_less_than_unbounded_pair_keeps_both :
    IV.guard (ZGuardCmp Lt) [IV.top; IV.top] = [IV.top; IV.top].
  Proof.
    vm_compute; reflexivity.
  Qed.

End GuardTests.

(** * Arithmetic *)

Module ArithmeticTests.

  (** Adding one to a range that is unbounded above shifts its lower bound to one. *)
  Example add_half_infinite_shifts_lower_bound :
    IV.add (I (Fin 0) PosInf) (IV.abst 1) = I (Fin 1) PosInf.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Subtracting one from a range that is unbounded below shifts its upper bound to nine. *)
  Example sub_half_infinite_shifts_upper_bound :
    IV.sub (I NegInf (Fin 10)) (IV.abst 1) = I NegInf (Fin 9).
  Proof.
    vm_compute; reflexivity.
  Qed.

End ArithmeticTests.

(** * Shifts *)

Module ShiftTests.

  (** Bottom returns before the shift cutoff is computed. *)
  Example shl_bottom_is_bottom :
    IV.shl IBot (I (Fin 2) (Fin 3)) = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An unbounded lower endpoint returns top before cutoff preparation. *)
  Example shl_top_is_top :
    IV.shl IV.top (I (Fin 2) (Fin 3)) = IV.top.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Finite operands still compute both shifted endpoints below the cutoff. *)
  Example shl_finite_below_cutoff_gives_both_endpoints :
    IV.shl (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 3)) = I (Fin 4) (Fin 32).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A shift beyond the cutoff retains the lower endpoint and drops the upper bound. *)
  Example shl_beyond_cutoff_drops_upper_bound :
    IV.shl (I (Fin 1) (Fin 4)) (I (Fin 128) (Fin 129)) = I (Fin 1) PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ShiftTests.

(** * Signed split *)

Module SignedSplitTests.

  (** Sharing the half-width power keeps a wholly nonnegative interval in the first part. *)
  Example nonnegative_range_stays_in_first_part :
    IV.signed_split 64%positive (I (Fin 1) (Fin 4)) = [I (Fin 1) (Fin 4); IBot].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A split across the sign boundary keeps both signed ranges. *)
  Example range_crossing_sign_boundary_gives_two_ranges :
    IV.signed_split 8%positive (I (Fin 120) (Fin 140)) =
      [I (Fin 120) (Fin 127); I (Fin (-128)) (Fin (-116))].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The smallest positive width keeps zero and translates its sign bit to minus one. *)
  Example one_bit_split_maps_sign_bit_to_minus_one :
    IV.signed_split 1%positive (I (Fin 0) (Fin 1)) =
      [I (Fin 0) (Fin 0); I (Fin (-1)) (Fin (-1))].
  Proof.
    vm_compute. reflexivity.
  Qed.

End SignedSplitTests.
