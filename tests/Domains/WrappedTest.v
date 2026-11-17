(** * Circular interval boundary observations

    These examples cover normalization, joins and expanding widening.
    For example, the arc from 250 to 3 crosses zero at width eight.
    Builds on: Wrapped and BitsLang. *)

From Stdlib Require Import ZArith List.
From Galois.Domains Require Import WrappedSig Wrapped BitsLang.
Import List.ListNotations.
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

Definition wrapped_mask_observation (w : positive) (a b : wrapped) :=
  (W.pleb w a b, W.pjoin w a b, W.pwiden tt w a b, W.pnarrow w a b).

Example wrapped_mask_cross_zero :
  map (fun w => wrapped_mask_observation w (WItv 250 3) (WItv 1 9))
    [8%positive; 64%positive] =
  [(false, WItv 250 9, WItv 240 13, WItv 250 3);
   (false, WItv 250 9, WFull, WItv 250 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_disjoint :
  map (fun w => wrapped_mask_observation w (WItv 10 11) (WItv 20 21))
    [8%positive; 64%positive] =
  [(false, WItv 10 21, WItv 8 21, WItv 10 11);
   (false, WItv 10 21, WItv 8 21, WItv 10 11)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_bottom_left :
  map (fun w => wrapped_mask_observation w WBot (WItv 250 3))
    [8%positive; 64%positive] =
  [(true, WItv 250 3, WItv 250 3, WBot);
   (true, WItv 250 3, WItv 250 3, WBot)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_bottom_right :
  map (fun w => wrapped_mask_observation w (WItv 250 3) WBot)
    [8%positive; 64%positive] =
  [(false, WItv 250 3, WItv 250 3, WItv 250 3);
   (false, WItv 250 3, WItv 250 3, WItv 250 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_full_left :
  map (fun w => wrapped_mask_observation w WFull (WItv 250 3))
    [8%positive; 64%positive] =
  [(false, WFull, WFull, WItv 250 3);
   (false, WFull, WFull, WItv 250 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_full_right :
  map (fun w => wrapped_mask_observation w (WItv 250 3) WFull)
    [8%positive; 64%positive] =
  [(true, WFull, WFull, WItv 250 3);
   (true, WFull, WFull, WItv 250 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_raw_widen_stable :
  map (fun w => W.pwiden tt w (WItv (2 ^ Zpos w) 0) (WItv 0 0))
    [8%positive; 64%positive] = [WItv 256 0; WItv (2 ^ 64) 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mask_raw_endpoints :
  wrapped_mask_observation w8 (WItv (-6) 259) (WItv 250 3) =
  (true, WItv 250 3, WItv (-6) 259, WItv 250 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_unsigned : wrapped_mul w8 (WItv 10 12) (WItv 2 3) = WItv 20 36.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_mul_signed : wrapped_mul w8 (WItv 250 255) (WItv 2 3) = WItv 238 254.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_unsigned_zero_divisor :
  wrapped_udiv w8 (WItv 1 3) (WItv 0 0) = WItv 255 255.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_mul_both_poles : wrapped_mul w8 (WItv 100 50) (WItv 2 2) = WItv 0 254.
Proof. vm_compute. reflexivity. Qed.

Example wrapped_mul_shared_products :
  W.wrapped_mul w8 (WItv 2 5) (WItv 3 4) = WItv 6 20.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_shared_points :
  W.wrapped_mul w8 (WItv 2 2) (WItv 3 3) = WItv 6 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_shared_cross_zero :
  W.wrapped_mul w8 (WItv 250 3) (WItv 2 2) = WItv 244 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_shared_bottom :
  W.wrapped_mul w8 WBot (WItv 2 5) = WBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_shared_full :
  W.wrapped_mul w8 WFull (WItv 2 2) = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_shared_products_64 :
  W.wrapped_mul 64%positive (WItv 2 5) (WItv 3 4) = WItv 6 20.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_shared_cross_zero_64 :
  W.wrapped_mul 64%positive (WItv 250 3) (WItv 2 2) = WItv 0 (2 ^ 64 - 2).
Proof.
  vm_compute. reflexivity.
Qed.

Module WF := Wrapped WordLanguage.
Example wrapped_rank_progress :
  Nat.ltb (WF.pwrank tt w8 (WItv 8 13)) (WF.pwrank tt w8 (WItv 10 11)) = true.
Proof. vm_compute. reflexivity. Qed.
Example wrapped_full_rank : WF.pwrank tt w8 (WItv 10 9) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** The payload meet contract requires a lower bound on its left operand. *)
Example wrapped_two_arcs_do_not_refine_right :
  W.pleb w8 (W.pmeet w8 (WItv 0 200) (WItv 150 50)) (WItv 150 50) = false.
Proof. vm_compute. reflexivity. Qed.
