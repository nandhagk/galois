(** * Top-lift fixtures

    Unknown absorbs joins and lies above every known element.
    For example, joining Unknown with Elem false gives Unknown.

    Groups:
    - [JoinTests] Joins with the top element, and the bottom.
    - [OrderTests] The order of the top element against a known value.
    - [RankTests] The heights and the ranks of the lifted lattice.

    Builds on: WithTop and Simple. *)

From Stdlib Require Import NArith.
From Galois.Lattice Require Import WithTop Simple JoinWidening.

(** * Fixtures *)

(** The top-lifted boolean lattice, as a code module. *)
Module TopBool := WithTopCode BoolLatCode.

(** The top-lifted boolean lattice, as a lattice module. *)
Module TopBoolLat := WithTop BoolLat.

(** The height structure of the top-lifted boolean lattice. *)
Module TopBoolHeight := WithTopHeight BoolLat BoolLatHeight TopBoolLat.

(** The widening rank of the top-lifted boolean lattice. *)
Module TopBoolRank := JoinWidening TopBoolLat TopBoolHeight.

(** * Join *)

Module JoinTests.

  (** Joining two known values gives the larger one. *)
  Example joining_known_values_gives_true :
    TopBool.join (Elem false) (Elem true) = Elem true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Joining a known value with Unknown gives Unknown. *)
  Example joining_known_with_unknown_is_unknown :
    TopBool.join (Elem false) Unknown = Unknown.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The bottom of the lifted lattice is the known value false. *)
  Example lifted_bottom_is_false : TopBool.bot = Elem false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End JoinTests.

(** * Order *)

Module OrderTests.

  (** Unknown is not below a known value. *)
  Example unknown_not_below_known : TopBool.leb Unknown (Elem true) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End OrderTests.

(** * Rank *)

Module RankTests.

  (** The top-lifted boolean lattice has height two. *)
  Example top_height_is_two : TopBoolHeight.height = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unknown has rank two. *)
  Example unknown_rank_is_two : TopBoolHeight.rank Unknown = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known value has rank zero. *)
  Example known_rank_is_zero : TopBoolHeight.rank (Elem false) = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The height is still two on the widening client. *)
  Example widened_height_is_two : TopBoolHeight.height = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unknown has widening rank zero. *)
  Example unknown_widening_rank_is_zero : TopBoolRank.wrank tt Unknown = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known value has widening rank two. *)
  Example known_widening_rank_is_two : TopBoolRank.wrank tt (Elem false) = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RankTests.
