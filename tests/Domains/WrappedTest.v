(** * Circular interval boundary observations

    These examples cover normalization, joins and expanding widening.
    For example, the arc from 250 to 3 crosses zero at width eight.

    Groups:
    - [NormalizationTests] The size and the normal form of circular arcs.
    - [OrderTests] The inclusion test on arcs, including arcs that cross zero.
    - [JoinTests] The least arc that covers two arcs.
    - [WideningTests] The expanding widening, with stable and full results.
    - [MaskTests] Order, join and widening observed together at two widths.
    - [MultiplicationTests] Products of arcs at width eight and at width sixty-four.
    - [DivisionTests] Unsigned division by zero.
    - [RankTests] The rank that decreases along widening.
    - [MeetTests] The meet of two arcs against its right operand.

    Builds on: Wrapped and BitsLang. *)

From Stdlib Require Import ZArith List.
From Galois.Domains Require Import WrappedSig Wrapped BitsLang.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The circular domain over the word language. *)
Module W := WrappedCode WordLanguageCode.
(** The word width used by most examples. *)
Local Abbreviation w8 := 8%positive.

(** The rank of the payload operations over the word language. *)
Module WF := Wrapped WordLanguage.

(** * Size and normalization *)

Module NormalizationTests.

  (** The bottom arc has size zero. *)
  Example bottom_has_size_zero : wrapped_size w8 WBot = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The arc from 250 to 3 at width eight has size ten. *)
  Example arc_crossing_zero_has_size_ten : wrapped_size w8 (WItv 250 3) = 10.
  Proof. vm_compute. reflexivity. Qed.

  (** Raw endpoints outside the range are reduced to the arc they cover. *)
  Example raw_endpoints_reduce_to_arc : wrapped_norm w8 (WItv (-6) 259) = WItv 250 3.
  Proof. vm_compute. reflexivity. Qed.

  (** An arc from 10 around to 9 covers every point, so it normalises to the full arc. *)
  Example wrapping_arc_normalises_to_full : wrapped_norm w8 (WItv 10 9) = WFull.
  Proof. vm_compute. reflexivity. Qed.

End NormalizationTests.

(** * Order *)

Module OrderTests.

  (** The full arc includes the wrapping arc from 10 to 9. *)
  Example full_arc_includes_wrapping_arc : wrapped_leb w8 WFull (WItv 10 9) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** An arc inside an arc that crosses zero is below it. *)
  Example arc_inside_crossing_zero_is_below : wrapped_leb w8 (WItv 250 3) (WItv 240 5) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** An arc that crosses zero is not below an arc that lies inside it. *)
  Example crossing_zero_is_not_below_inner_arc :
    wrapped_leb w8 (WItv 240 5) (WItv 250 3) = false.
  Proof. vm_compute. reflexivity. Qed.

End OrderTests.

(** * Join *)

Module JoinTests.

  (** Joining the bottom arc with an arc gives that arc. *)
  Example join_bottom_gives_arc : wrapped_join w8 WBot (WItv (-6) 259) = WItv 250 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining two arcs that cross zero gives the arc that covers both. *)
  Example join_across_zero_covers_both : wrapped_join w8 (WItv 250 3) (WItv 4 8) = WItv 250 8.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining two points half a circle apart gives the arc from zero to 128. *)
  Example join_equal_candidates : wrapped_join w8 (WItv 0 0) (WItv 128 128) = WItv 0 128.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining two arcs that together cover the circle gives the full arc. *)
  Example join_covers_circle_is_full : wrapped_join w8 (WItv 0 200) (WItv 150 10) = WFull.
  Proof. vm_compute. reflexivity. Qed.

End JoinTests.

(** * Widening *)

Module WideningTests.

  (** Widening the bottom arc gives the other arc. *)
  Example widen_from_bottom_gives_arc : W.pwiden tt w8 WBot (WItv 250 3) = WItv 250 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Widening an arc that grows at both ends expands both ends. *)
  Example widen_doubles_growing_ends : W.pwiden tt w8 (WItv 10 11) (WItv 10 12) = WItv 8 13.
  Proof. vm_compute. reflexivity. Qed.

  (** Widening keeps an arc that already contains the new one. *)
  Example widen_keeps_containing_arc : W.pwiden tt w8 (WItv 250 3) (WItv 255 1) = WItv 250 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Widening an arc that grows to cover the circle gives the full arc. *)
  Example widen_to_full_circle : W.pwiden tt w8 (WItv 0 100) (WItv 100 101) = WFull.
  Proof. vm_compute. reflexivity. Qed.

  (** Widening keeps a raw arc whose upper endpoint is zero. *)
  Example raw_widen_keeps_arc :
    W.pwiden tt 4%positive (WItv 16 0) (WItv 0 0) = WItv 16 0.
  Proof. vm_compute. reflexivity. Qed.

End WideningTests.

(** * Masks *)

(** The order, join, widening and narrowing of two arcs, observed together. *)
Definition wrapped_mask_observation (w : positive) (a b : wrapped) :=
  (W.pleb w a b, W.pjoin w a b, W.pwiden tt w a b, W.pnarrow w a b).

(** Whether two arcs give the same expected observation at widths eight and sixty-four. *)
Definition same_at_both_widths (a b : wrapped) (expected : bool * wrapped * wrapped * wrapped)
  : Prop :=
  Forall (fun w => wrapped_mask_observation w a b = expected) [8%positive; 64%positive].

(** * Mask *)

Module MaskTests.

  (** Two arcs that cross zero widen to an arc short of the full circle at width eight. *)
  Example mask_arcs_crossing_zero_width_8 :
    wrapped_mask_observation 8%positive (WItv 250 3) (WItv 1 9) =
      (false, WItv 250 9, WItv 240 13, WItv 250 3).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two arcs that cross zero widen to the full arc at width sixty-four. *)
  Example mask_arcs_crossing_zero_width_64 :
    wrapped_mask_observation 64%positive (WItv 250 3) (WItv 1 9) =
      (false, WItv 250 9, WFull, WItv 250 3).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two disjoint arcs give the same observations at widths eight and sixty-four. *)
  Example mask_disjoint_arcs :
    same_at_both_widths (WItv 10 11) (WItv 20 21)
      (false, WItv 10 21, WItv 8 21, WItv 10 11).
  Proof.
    unfold same_at_both_widths.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The bottom arc on the left is below an arc at both widths. *)
  Example mask_bottom_left :
    same_at_both_widths WBot (WItv 250 3) (true, WItv 250 3, WItv 250 3, WBot).
  Proof.
    unfold same_at_both_widths.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The bottom arc on the right is not above an arc at both widths. *)
  Example mask_bottom_right :
    same_at_both_widths (WItv 250 3) WBot
      (false, WItv 250 3, WItv 250 3, WItv 250 3).
  Proof.
    unfold same_at_both_widths.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The full arc on the left is not below an arc at both widths. *)
  Example mask_full_left :
    same_at_both_widths WFull (WItv 250 3) (false, WFull, WFull, WItv 250 3).
  Proof.
    unfold same_at_both_widths.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The full arc on the right is above an arc at both widths. *)
  Example mask_full_right :
    same_at_both_widths (WItv 250 3) WFull (true, WFull, WFull, WItv 250 3).
  Proof.
    unfold same_at_both_widths.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** Widening a raw arc whose upper endpoint is zero keeps it at both widths. *)
  Example mask_raw_widen_keeps_arc :
    map (fun w => W.pwiden tt w (WItv (2 ^ Zpos w) 0) (WItv 0 0))
      [8%positive; 64%positive] = [WItv 256 0; WItv (2 ^ 64) 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Order, join and narrowing reduce a raw arc at width eight, and widening keeps it. *)
  Example mask_raw_endpoints_reduce :
    wrapped_mask_observation w8 (WItv (-6) 259) (WItv 250 3) =
    (true, WItv 250 3, WItv (-6) 259, WItv 250 3).
  Proof.
    vm_compute. reflexivity.
  Qed.

End MaskTests.

(** * Multiplication *)

Module MultiplicationTests.

  (** Multiplying two unsigned arcs gives the arc of their products. *)
  Example mul_unsigned_arcs : wrapped_mul w8 (WItv 10 12) (WItv 2 3) = WItv 20 36.
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplying arcs that wrap as signed values gives the arc of their products. *)
  Example mul_signed_arcs : wrapped_mul w8 (WItv 250 255) (WItv 2 3) = WItv 238 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplying an arc that crosses both signed poles by two gives the arc from 0 to 254. *)
  Example mul_arcs_across_both_poles : wrapped_mul w8 (WItv 100 50) (WItv 2 2) = WItv 0 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplying shared arcs at width eight gives the arc of their products. *)
  Example mul_shared_products :
    W.wrapped_mul w8 (WItv 2 5) (WItv 3 4) = WItv 6 20.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying two points gives their product as a point. *)
  Example mul_shared_points :
    W.wrapped_mul w8 (WItv 2 2) (WItv 3 3) = WItv 6 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying an arc that crosses zero by a point gives an arc that crosses zero. *)
  Example mul_shared_crossing_zero :
    W.wrapped_mul w8 (WItv 250 3) (WItv 2 2) = WItv 244 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the bottom arc by anything gives the bottom arc. *)
  Example mul_shared_bottom : W.wrapped_mul w8 WBot (WItv 2 5) = WBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the full arc by a point at width eight gives the arc from 0 to 254. *)
  Example mul_shared_full : W.wrapped_mul w8 WFull (WItv 2 2) = WItv 0 254.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying shared arcs at width sixty-four gives the arc of their products. *)
  Example mul_shared_products_width_64 :
    W.wrapped_mul 64%positive (WItv 2 5) (WItv 3 4) = WItv 6 20.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying an arc that crosses zero by a point at width sixty-four wraps. *)
  Example mul_shared_crossing_zero_width_64 :
    W.wrapped_mul 64%positive (WItv 250 3) (WItv 2 2) = WItv 0 (2 ^ 64 - 2).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying two points at width sixty-four gives their product as a point. *)
  Example mul_fast_points_width_64 :
    W.wrapped_mul 64%positive (WItv 2 2) (WItv 3 3) = WItv 6 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying the full arc by zero at width sixty-four gives zero. *)
  Example mul_fast_full_by_zero_width_64 :
    W.wrapped_mul 64%positive WFull (WItv 0 0) = WItv 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying minus one by two at width eight gives minus two. *)
  Example mul_fast_negative_point :
    W.wrapped_mul w8 (WItv 255 255) (WItv 2 2) = WItv 254 254.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying a raw point of width four by three gives zero. *)
  Example mul_fast_raw_point_width_4 :
    W.wrapped_mul 4%positive (WItv 16 0) (WItv 3 3) = WItv 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying a raw negative point of width one by three gives one. *)
  Example mul_fast_raw_point_width_1 :
    W.wrapped_mul 1%positive (WItv (-1) (-1)) (WItv 3 3) = WItv 1 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Multiplying by the bottom arc at width sixty-four gives the bottom arc. *)
  Example mul_fast_empty_right_width_64 :
    W.wrapped_mul 64%positive (WItv 2 5) WBot = WBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MultiplicationTests.

(** * Division *)

Module DivisionTests.

  (** Unsigned division by zero gives the all-ones value 255 at width eight. *)
  Example udiv_by_zero_is_top :
    wrapped_udiv w8 (WItv 1 3) (WItv 0 0) = WItv 255 255.
  Proof. vm_compute. reflexivity. Qed.

End DivisionTests.

(** * Rank *)

Module RankTests.

  (** Widening to a larger arc lowers the rank. *)
  Example widening_lowers_rank :
    Nat.ltb (WF.pwrank tt w8 (WItv 8 13)) (WF.pwrank tt w8 (WItv 10 11)) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The full arc has rank zero. *)
  Example full_arc_has_rank_zero : WF.pwrank tt w8 (WItv 10 9) = 0%nat.
  Proof. vm_compute. reflexivity. Qed.

End RankTests.

(** * Meet *)

Module MeetTests.

  (** The meet of the arcs 0 to 200 and 150 to 50 is not below the second arc. *)
  Example two_arcs_do_not_refine_right :
    W.pleb w8 (W.pmeet w8 (WItv 0 200) (WItv 150 50)) (WItv 150 50) = false.
  Proof. vm_compute. reflexivity. Qed.

End MeetTests.
