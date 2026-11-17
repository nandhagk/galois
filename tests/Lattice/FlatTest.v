(** * Flat fixtures

    Flat booleans distinguish two incomparable known values.
    For example, their join is top even though neither covers the other.
    Builds on: Flat.

    Groups:
    - JoinTests: joins of known, bottom and top values.
    - OrderTests: the order of known values.
    - RankTests: the rank of each level of the flat lattice. *)

From Stdlib Require Import Bool NArith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Flat.

(** * Fixtures *)

(** The flat lattice over booleans, as a code module. *)
Module FlatBool := FlatCode BoolKeyCode.

(** The flat lattice over booleans, as a lattice module. *)
Module FlatBoolLat := Flat BoolKey.

(** The height structure of the flat boolean lattice. *)
Module FlatBoolHeight := FlatHeight BoolKey FlatBoolLat.

(** * Join *)

Module JoinTests.

  (** Joining a known value with itself gives that value. *)
  Example joining_known_value_with_itself : FlatBool.join (FVal true) (FVal true) = FVal true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Bottom joined with bottom is bottom. *)
  Example joining_bottoms_gives_bottom : FlatBool.join FBot FBot = FBot.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Top absorbs a known value in a join. *)
  Example top_absorbs_known_value : FlatBool.join (FVal false) FTop = FTop.
  Proof.
    vm_compute; reflexivity.
  Qed.

End JoinTests.

(** * Order *)

Module OrderTests.

  (** Two distinct known values are not ordered. *)
  Example distinct_known_values_are_not_ordered : FlatBool.leb (FVal true) (FVal false) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End OrderTests.

(** * Rank *)

Module RankTests.

  (** Bottom has rank zero. *)
  Example bottom_has_rank_zero : FlatBoolHeight.rank FBot = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known value has rank one. *)
  Example known_value_has_rank_one : FlatBoolHeight.rank (FVal false) = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Top has rank two. *)
  Example top_has_rank_two : FlatBoolHeight.rank FTop = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RankTests.

(* LatticeFlatTest.flat_leb_ticks and flat_join_ticks retire with Cost.ticks. *)
