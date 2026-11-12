(** * Simple and lifted lattice fixtures

    These examples check boolean and unit lattice operations and lifted bottom.
    For example, [Some false] lies above [None].
    Builds on: Simple and WithBot. *)

From Stdlib Require Import Bool List.
From Galois.Lattice Require Import Simple WithBot JoinWidening.
Import List.ListNotations.

Module LiftedBool := WithBotCode BoolLatCode.
Module BoolWide := JoinWideningCode BoolLatCode.
Module UnitWide := JoinWideningCode UnitLatCode.
Module LiftedWide := JoinWideningCode LiftedBool.
Module LiftedBoolLat := WithBot BoolLat.
Module LiftedHeight := WithBotHeight BoolLat BoolLatHeight LiftedBoolLat.
Module LiftedRank := JoinWidening LiftedBoolLat LiftedHeight.

Example boolean_widen_narrow_table :
  map (fun xy => let '(x, y) := xy in (BoolWide.widen tt x y, BoolWide.narrow x y))
    [(false, false); (false, true); (true, false); (true, true)] =
  [(false, false); (true, false); (true, true); (true, true)].
Proof.
  vm_compute. reflexivity.
Qed.

Example unit_widen_narrow : (UnitWide.widen tt tt tt, UnitWide.narrow tt tt) = (tt, tt).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_widen_narrow :
  (LiftedWide.widen tt None None, LiftedWide.narrow None None,
   LiftedWide.narrow (Some false) None,
   LiftedWide.widen tt (Some false) (Some true),
   LiftedWide.narrow (Some true) (Some false)) =
  (None, None, Some false, Some true, Some true).
Proof.
  vm_compute. reflexivity.
Qed.

Example boolean_table :
  map (fun xy => let '(x, y) := xy in
    (BoolLatCode.leb x y, BoolLatCode.join x y))
    [(false, false); (false, true); (true, false); (true, true)] =
  [(true, false); (true, true); (false, true); (true, true)].
Proof.
  vm_compute. reflexivity.
Qed.

Example unit_boundary :
  (UnitLatCode.leb tt tt, UnitLatCode.join tt tt) = (true, tt).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_none_none :
  (LiftedBool.leb None None, LiftedBool.join None None) = (true, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_none_some :
  (LiftedBool.leb None (Some false), LiftedBool.leb (Some false) None,
   LiftedBool.join None (Some false)) = (true, false, Some false).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_some_some :
  (LiftedBool.leb (Some true) (Some false),
   LiftedBool.join (Some false) (Some true)) = (false, Some true).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_measures :
  (map LiftedHeight.rank [None; Some false; Some true],
   map (LiftedRank.wrank tt) [None; Some false; Some true],
   LiftedHeight.height, LiftedHeight.height) = ([0; 1; 2], [2; 1; 0], 2, 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example unit_rank : UnitLatHeight.rank tt = 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example of_pure_values :
  (BoolLatCode.leb false true, BoolLatCode.leb true false, BoolLatCode.join false true,
   BoolWide.widen tt false true, BoolWide.narrow false true) = (true, false, true, true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_boundaries :
  (BoolWide.widen tt false false, BoolWide.widen tt false true,
   BoolWide.widen tt true false, BoolWide.widen tt true true) = (false, true, true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example bool_domain_computes :
  (BoolLatCode.join false BoolLatCode.top, BoolLatCode.leb BoolLatCode.top false) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

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
