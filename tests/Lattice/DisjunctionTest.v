(** * Disjunction fixtures

    Capped joins combine flat alternatives.
    For example, cap one collapses incomparable values to top.
    Builds on: Disjunction, Flat and Key.

    Groups:
    - CapTests: clipping and joining under caps of zero, one and two.
    - OrderTests: the order of disjunctions, including its least elements.
    - BottomTests: testing for the bottom disjunction.
    - BoundTests: the time bounds of inclusion, join, bottom test and clipping. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import LatticeSig Disjunction Flat Simple.
Import List.ListNotations.

(** * Fixtures *)

(** The flat boolean lattice, as a code module. *)
Module FlatBool := FlatCode BoolKeyCode.

(** The cap of zero alternatives. *)
Module Cap0. Definition k := 0. End Cap0.

(** The cap of one alternative. *)
Module Cap1. Definition k := 1. End Cap1.

(** The cap of two alternatives. *)
Module Cap2. Definition k := 2. End Cap2.

(** Disjunctions over flat booleans under each cap. *)
Module D0 := DisjunctionCode FlatBool Cap0.
Module D1 := DisjunctionCode FlatBool Cap1.
Module D2 := DisjunctionCode FlatBool Cap2.

(** Disjunctions over booleans under cap one. *)
Module BoolDisjunction := DisjunctionCode BoolLatCode Cap1.

(** The size bound on the join of booleans. *)
Module BoolJoinSize <: JOIN_SIZE BoolLatT.
  (** Boolean joins keep the constant component size. *)
  Lemma join_size : forall a b,
    (N.of_nat (BoolLatT.size (BoolLatT.join a b)) <=
      BoolLatT.c_lat * N.of_nat (BoolLatT.size a + BoolLatT.size b + 1))%N.
  Proof.
    intros a b. apply N.leb_le. vm_compute. reflexivity.
  Qed.
End BoolJoinSize.

(** The timed disjunction under cap one, for the time bounds. *)
Module TimedDisjunction := DisjunctionT BoolLatT BoolJoinSize Cap1.

(** * Cap *)

Module CapTests.

  (** Under cap one, joining two alternatives collapses them to top. *)
  Example cap_one_join_collapses_to_top :
    proj1_sig (D1.join (D1.clip [FVal false]) (D1.clip [FVal true; FBot])) = [FTop].
  Proof. vm_compute. reflexivity. Qed.

  (** Under cap two, joining two alternatives keeps both. *)
  Example cap_two_join_keeps_both :
    proj1_sig (D2.join (D2.clip [FVal false]) (D2.clip [FVal true; FBot])) =
      [FVal false; FVal true].
  Proof. vm_compute. reflexivity. Qed.

  (** Under cap zero, clipping drops every alternative. *)
  Example cap_zero_clip_is_empty : proj1_sig (D0.clip [FVal false]) = [].
  Proof. vm_compute. reflexivity. Qed.

  (** The empty disjunction under cap zero joins to empty. *)
  Example cap_zero_join_of_empties_is_empty :
    proj1_sig (D0.join D0.bot D0.bot) = [].
  Proof. vm_compute. reflexivity. Qed.

  (** The empty disjunction under cap zero is below itself. *)
  Example cap_zero_empty_below_itself : D0.leb D0.bot D0.bot = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Under cap one, the selective join of two singletons is below their clipped union. *)
  Example selective_leastness :
    BoolDisjunction.leb (BoolDisjunction.join (BoolDisjunction.clip [false])
      (BoolDisjunction.clip [true])) (BoolDisjunction.clip [false; true]) = true.
  Proof. vm_compute. reflexivity. Qed.

End CapTests.

(** * Order *)

Module OrderTests.

  (** Under cap two, the disjunction with true is not below the one with false. *)
  Example disjunction_negative :
    D2.leb (D2.clip [FVal true]) (D2.clip [FVal false]) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A disjunction with a bottom alternative is not below the empty disjunction under cap one. *)
  Example empty_right_is_not_above_bottom_alternative :
    D1.leb (D1.clip [FBot]) D1.bot = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The disjunction of false and true is below itself. *)
  Example disjunction_below_itself :
    D2.leb (D2.clip [FVal false; FVal true]) (D2.clip [FVal false; FVal true]) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A singleton disjunction is below the two-alternative disjunction that contains it. *)
  Example singleton_below_containing_disjunction :
    D2.leb (D2.clip [FVal false]) (D2.clip [FVal false; FVal true]) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The join of the two-alternative disjunction with a singleton is not below it. *)
  Example join_with_singleton_is_not_below_larger :
    D2.leb (D2.join (D2.clip [FVal false; FVal true]) (D2.clip [FVal false]))
      (D2.clip [FVal false; FVal true]) = false.
  Proof. vm_compute. reflexivity. Qed.

End OrderTests.

(** * Bottom *)

Module BottomTests.

  (** The bottom disjunction under cap one is bottom. *)
  Example bottom_disjunction_is_bottom : D1.is_bot D1.bot = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A disjunction with a bottom alternative is not the bottom disjunction. *)
  Example bottom_alternative_is_not_bottom : D1.is_bot (D1.clip [FBot]) = false.
  Proof. vm_compute. reflexivity. Qed.

End BottomTests.

(** * Bounds *)

Module BoundTests.

  (** Inclusion uses the sum of the two public sizes as its big-O measure. *)
  Example disjunction_inclusion_bigO_bound :
    let a := TimedDisjunction.clip [false] in
    let b := TimedDisjunction.clip [true] in
    (TimedDisjunction.T_leb a b <= TimedDisjunction.c_lat *
      (N.of_nat (TimedDisjunction.size a + TimedDisjunction.size b) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** Joining singleton alternatives exercises clipping at cap one. *)
  Example disjunction_join_bigO_bound :
    let a := TimedDisjunction.clip [false] in
    let b := TimedDisjunction.clip [true] in
    (TimedDisjunction.T_join a b <= TimedDisjunction.c_lat *
      (N.of_nat (TimedDisjunction.size a + TimedDisjunction.size b) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** Bottom testing is bounded by the size of one alternative. *)
  Example disjunction_bottom_bigO_bound :
    let a := TimedDisjunction.clip [false] in
    (TimedDisjunction.T_is_bot a <=
      TimedDisjunction.c_lat * (N.of_nat (TimedDisjunction.size a) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** Two alternatives reach the clipping theorem's twice-cap boundary. *)
  Example disjunction_clip_bigO_bound :
    let xs := [false; true] in
    (TimedDisjunction.T_clip xs <= TimedDisjunction.c_lat *
      (N.of_nat (length xs + fold_right (fun a n => (BoolLatT.size a + n)%nat) 0%nat xs) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

End BoundTests.

(* At cap zero the old raw join [FVal false] [] returned [FVal false].
   That input is outside the bounded carrier, and clipping it now returns [].
   The old cap-one nonleast counterexample was
   (D1.leb [FVal false] [FVal false; FVal true],
    D1.leb [FVal true] [FVal false; FVal true],
    D1.leb (D1.join [FVal false] [FVal true]) [FVal false; FVal true]) =
     (true, true, false). Its two-element target lies outside the carrier.
   The old raw widening examples are deferred to the D1 state-disjunction component.
   Their expected results were [FTop] for widening [FVal false] by [FVal true],
   [FTop; FVal true] for widening [FTop; FVal true] by [FVal false], and []
   for widening [] by [] at cap zero. The old rank client expected (3, 3, 0)
   on [false; false] and its widening by [true]. Cost.ticks examples are retired. *)
