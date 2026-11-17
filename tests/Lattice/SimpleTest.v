(** * Simple and lifted lattice fixtures

    These examples check boolean and unit lattice operations and lifted bottom.
    For example, [Some false] lies above [None].

    Groups:
    - [BooleanTests] The boolean lattice, its order, join and widening.
    - [UnitTests] The unit lattice.
    - [LiftTests] The lifted boolean lattice with a fresh bottom, and its heights.

    Builds on: Simple and WithBot. *)

From Stdlib Require Import Bool List.
From Galois.Lattice Require Import Simple WithBot JoinWidening.
Import List.ListNotations.

(** * Fixtures *)

(** The boolean lattice with a fresh bottom added, as a code module. *)
Module LiftedBool := WithBotCode BoolLatCode.

(** The widening adapters of the boolean, unit and lifted lattices. *)
Module BoolWide := JoinWideningCode BoolLatCode.
Module UnitWide := JoinWideningCode UnitLatCode.
Module LiftedWide := JoinWideningCode LiftedBool.

(** The lifted boolean lattice, as a lattice module, with its height and widening rank. *)
Module LiftedBoolLat := WithBot BoolLat.
Module LiftedHeight := WithBotHeight BoolLat BoolLatHeight LiftedBoolLat.
Module LiftedRank := JoinWidening LiftedBoolLat LiftedHeight.

(** * Boolean *)

Module BooleanTests.

  (** The widening of two booleans, as (old, new, result). It is the join. *)
  Definition widen_cases : list (bool * bool * bool) :=
    [(false, false, false); (false, true, true); (true, false, true); (true, true, true)].

  (** The narrowing of two booleans, as (old, new, result). It keeps the old value. *)
  Definition narrow_cases : list (bool * bool * bool) :=
    [(false, false, false); (false, true, false); (true, false, true); (true, true, true)].

  (** The boolean order, as (left, right, whether left is below right). False is below true. *)
  Definition leb_cases : list (bool * bool * bool) :=
    [(false, false, true); (false, true, true); (true, false, false); (true, true, true)].

  (** The boolean join, as (left, right, result). It is the disjunction. *)
  Definition join_cases : list (bool * bool * bool) :=
    [(false, false, false); (false, true, true); (true, false, true); (true, true, true)].

  (** Widening agrees with every case of its table. *)
  Example widen_table :
    forallb (fun c => let '(x, y, r) := c in Bool.eqb (BoolWide.widen tt x y) r) widen_cases = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing agrees with every case of its table. *)
  Example narrow_table :
    forallb (fun c => let '(x, y, r) := c in Bool.eqb (BoolWide.narrow x y) r) narrow_cases = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The order agrees with every case of its table. *)
  Example order_table :
    forallb (fun c => let '(x, y, r) := c in Bool.eqb (BoolLatCode.leb x y) r) leb_cases = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join agrees with every case of its table. *)
  Example join_table :
    forallb (fun c => let '(x, y, r) := c in Bool.eqb (BoolLatCode.join x y) r) join_cases = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of false with top is true. *)
  Example bool_domain_join_with_top : BoolLatCode.join false BoolLatCode.top = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Top is not below false in the boolean domain. *)
  Example bool_domain_top_not_below_false : BoolLatCode.leb BoolLatCode.top false = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End BooleanTests.

(** * Unit *)

Module UnitTests.

  (** Widening the unit values gives the unit value. *)
  Example unit_widen_is_unit : UnitWide.widen tt tt tt = tt.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing the unit values gives the unit value. *)
  Example unit_narrow_is_unit : UnitWide.narrow tt tt = tt.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unit value is below itself. *)
  Example unit_order_reflexive : UnitLatCode.leb tt tt = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of the unit value with itself is the unit value. *)
  Example unit_join_is_unit : UnitLatCode.join tt tt = tt.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unit lattice has rank zero. *)
  Example unit_rank : UnitLatHeight.rank tt = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnitTests.

(** * Lifted *)

Module LiftTests.

  (** Equality of lifted booleans, where [None] is the fresh bottom. *)
  Definition lifted_eqb (x y : option bool) : bool :=
    match x, y with
    | None, None => true
    | Some a, Some b => Bool.eqb a b
    | _, _ => false
    end.

  (** The widening of two lifted booleans, as (old, new, result). *)
  Definition widen_cases : list (option bool * option bool * option bool) :=
    [(None, None, None); (Some false, Some true, Some true)].

  (** The narrowing of two lifted booleans, as (old, new, result). *)
  Definition narrow_cases : list (option bool * option bool * option bool) :=
    [(None, None, None); (Some false, None, Some false); (Some true, Some false, Some true)].

  (** The lifted order, as (left, right, whether left is below right). None is the bottom. *)
  Definition leb_cases : list (option bool * option bool * bool) :=
    [(None, None, true); (None, Some false, true); (Some false, None, false);
     (Some true, Some false, false)].

  (** The lifted join, as (left, right, result). *)
  Definition join_cases : list (option bool * option bool * option bool) :=
    [(None, None, None); (None, Some false, Some false); (Some false, Some true, Some true)].

  (** Widening agrees with every case of its table. *)
  Example lift_widen_table :
    forallb (fun c => let '(x, y, r) := c in lifted_eqb (LiftedWide.widen tt x y) r) widen_cases
      = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing agrees with every case of its table. *)
  Example lift_narrow_table :
    forallb (fun c => let '(x, y, r) := c in lifted_eqb (LiftedWide.narrow x y) r) narrow_cases
      = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The order agrees with every case of its table. *)
  Example lift_order_table :
    forallb (fun c => let '(x, y, r) := c in Bool.eqb (LiftedBool.leb x y) r) leb_cases = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join agrees with every case of its table. *)
  Example lift_join_table :
    forallb (fun c => let '(x, y, r) := c in lifted_eqb (LiftedBool.join x y) r) join_cases
      = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The ranks of none, a known false and a known true are zero, one and two. *)
  Example lift_ranks : map LiftedHeight.rank [None; Some false; Some true] = [0; 1; 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The widening ranks of none, a known false and a known true are two, one and zero. *)
  Example lift_widening_ranks :
    map (LiftedRank.wrank tt) [None; Some false; Some true] = [2; 1; 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lifted boolean lattice has height two. *)
  Example lift_height_is_two : LiftedHeight.height = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lifted boolean lattice has height two on the widening client too. *)
  Example lift_height_is_two_on_widening_client : LiftedHeight.height = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LiftTests.
