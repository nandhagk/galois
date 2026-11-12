(** * Circular interval boundary observations

    These examples cover normalization, joins and expanding widening.
    For example, the arc from 250 to 3 crosses zero at width eight.
    Builds on: Wrapped and BitsLang. *)

From Stdlib Require Import ZArith List.
From Galois.Domains Require Import WrappedSig Wrapped BitsLang.
Local Open Scope Z_scope.
Module W := WrappedCode WordLanguageCode.
Local Abbreviation w8 := 8%positive.

Example wrapped_bottom_size : wrapped_size w8 WBot = 0.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_cross_zero_size : wrapped_size w8 (WItv 250 3) = 10.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_raw_endpoints : wrapped_norm w8 (WItv (-6) 259) = WItv 250 3.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_full_normalization : wrapped_norm w8 (WItv 10 9) = WFull.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_full_equivalence : wrapped_leb w8 WFull (WItv 10 9) = true.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_inside_cross_zero : wrapped_leb w8 (WItv 250 3) (WItv 240 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_outside_cross_zero : wrapped_leb w8 (WItv 240 5) (WItv 250 3) = false.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_join_bottom : wrapped_join w8 WBot (WItv (-6) 259) = WItv 250 3.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_join_across_zero : wrapped_join w8 (WItv 250 3) (WItv 4 8) = WItv 250 8.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_join_equal_candidates : wrapped_join w8 (WItv 0 0) (WItv 128 128) = WItv 0 128.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_join_covers_circle : wrapped_join w8 (WItv 0 200) (WItv 150 10) = WFull.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_widen_bottom : W.pwiden tt w8 WBot (WItv 250 3) = WItv 250 3.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_widen_doubles : W.pwiden tt w8 (WItv 10 11) (WItv 10 12) = WItv 8 13.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_widen_stable : W.pwiden tt w8 (WItv 250 3) (WItv 255 1) = WItv 250 3.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_widen_full : W.pwiden tt w8 (WItv 0 100) (WItv 100 101) = WFull.
Proof. vm_compute. reflexivity. Qed.

(** The old normalized widening returned WItv 0 0 for this input. *)
Example wrapped_raw_widen_stable :
  W.pwiden tt 4%positive (WItv 16 0) (WItv 0 0) = WItv 16 0.
Proof. vm_compute. reflexivity. Qed.

Example wrapped_mul_unsigned : wrapped_mul w8 (WItv 10 12) (WItv 2 3) = WItv 20 36.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_mul_signed : wrapped_mul w8 (WItv 250 255) (WItv 2 3) = WItv 238 254.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_unsigned_zero_divisor :
  wrapped_udiv w8 (WItv 1 3) (WItv 0 0) = WItv 255 255.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_mul_both_poles : wrapped_mul w8 (WItv 100 50) (WItv 2 2) = WItv 0 254.
Proof. vm_compute. reflexivity. Qed.
