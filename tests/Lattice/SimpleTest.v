(** * Simple and lifted lattice fixtures

    These examples check boolean and unit lattice operations and lifted bottom.
    For example, [Some false] lies above [None].
    Builds on: Simple and WithBot.

    Groups:
    - BooleanTests: the boolean lattice, its order, join and widening.
    - UnitTests: the unit lattice.
    - LiftTests: the lifted boolean lattice with a fresh bottom, and its heights. *)

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

  (** Widening false with false gives false. *)
  Example widen_false_false : BoolWide.widen tt false false = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing false with false gives false. *)
  Example narrow_false_false : BoolWide.narrow false false = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening false with true gives true. *)
  Example widen_false_true : BoolWide.widen tt false true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing false with true gives false. *)
  Example narrow_false_true : BoolWide.narrow false true = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening true with false gives true. *)
  Example widen_true_false : BoolWide.widen tt true false = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing true with false gives true. *)
  Example narrow_true_false : BoolWide.narrow true false = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening true with true gives true. *)
  Example widen_true_true : BoolWide.widen tt true true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing true with true gives true. *)
  Example narrow_true_true : BoolWide.narrow true true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** False is below false in the boolean order. *)
  Example bool_order_false_false : BoolLatCode.leb false false = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of false with itself is false. *)
  Example bool_join_false_false : BoolLatCode.join false false = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** False is below true in the boolean order. *)
  Example bool_order_false_true : BoolLatCode.leb false true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of false and true is true. *)
  Example bool_join_false_true : BoolLatCode.join false true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** True is not below false in the boolean order. *)
  Example bool_order_true_false : BoolLatCode.leb true false = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of true and false is true. *)
  Example bool_join_true_false : BoolLatCode.join true false = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** True is below itself in the boolean order. *)
  Example bool_order_true_true : BoolLatCode.leb true true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of true with itself is true. *)
  Example bool_join_true_true : BoolLatCode.join true true = true.
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

  (** The threshold widening keeps false when both arguments are false. *)
  Example threshold_false_false : BoolWide.widen tt false false = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The threshold widening reaches true from false to true. *)
  Example threshold_false_true : BoolWide.widen tt false true = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The threshold widening keeps true when the old value is true. *)
  Example threshold_true_false : BoolWide.widen tt true false = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The threshold widening keeps true when both arguments are true. *)
  Example threshold_true_true : BoolWide.widen tt true true = true.
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

  (** Widening none with none gives none. *)
  Example lift_widen_none_none : LiftedWide.widen tt None None = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing none with none gives none. *)
  Example lift_narrow_none_none : LiftedWide.narrow None None = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing a known false with none gives the known false. *)
  Example lift_narrow_some_false_with_none : LiftedWide.narrow (Some false) None = Some false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening a known false with a known true gives the known true. *)
  Example lift_widen_some_false_some_true :
    LiftedWide.widen tt (Some false) (Some true) = Some true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing a known true with a known false gives the known true. *)
  Example lift_narrow_some_true_some_false :
    LiftedWide.narrow (Some true) (Some false) = Some true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** None is below none in the lifted order. *)
  Example lift_none_below_none : LiftedBool.leb None None = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of none with none is none. *)
  Example lift_join_none_none : LiftedBool.join None None = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** None is below a known false. *)
  Example lift_none_below_some_false : LiftedBool.leb None (Some false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known false is not below none. *)
  Example lift_some_false_not_below_none : LiftedBool.leb (Some false) None = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of none with a known false is that known false. *)
  Example lift_join_none_with_some_false :
    LiftedBool.join None (Some false) = Some false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known true is not below a known false. *)
  Example lift_some_true_not_below_some_false :
    LiftedBool.leb (Some true) (Some false) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of a known false and a known true is a known true. *)
  Example lift_join_some_false_some_true :
    LiftedBool.join (Some false) (Some true) = Some true.
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

(* LatticeSimpleTest.lift_empty_meaning uses the retired lift_bot_gamma dictionary.
   WithBot exports the lattice operations. It exports no concretisation adapter.
   The Cost.ticks coordinates of unit_boundary, lift_none_none, lift_none_some and
   lift_some_some retire with Cost. The value coordinates are checked above. *)

(* LatticeCoreTest.of_pure_values is the public boolean implementation above.
   threshold_keeps_order_join uses the unchanged BoolLat operations, while
   threshold_boundaries uses the public JoinWidening adapter. The boolean
   threshold function has the same table as this adapter.
   threshold_laws and costed_replacement_laws prove laws of the deleted
   with_widen and with_widen_c dictionaries.
   of_pure_ticks and the tick coordinate of threshold_boundaries retire with Cost.
   costed_replacement_ticks expects (7%N, 1%N, true, false). It replaces a stored
   widen_c closure while keeping join_c. Lattice operations and widening now
   belong to separate modules, so the with_widen_c dictionary replacement retires.
   bool_domain_computes keeps the underlying join/top/order observations above.
   domain_of_simple assembly and its bool_domain_laws proof client retire with the
   domain dictionary. weak_join_laws and weak_join_is_not_least are symbolic proof
   clients of the deleted simple and lub_laws dictionaries.
   LatticeTacticsTest tests the deleted order_solver tactic, as core section 4 specifies. *)
