(** * Simple and lifted lattice fixtures

    Small observations distinguish reached bottom from unreachable bottom and retain exact costs.
    For example, [Some false] is strictly above [None].
    Builds on: LatticeSimple and LatticeAdjoin. *)

From Stdlib Require Import Bool NArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeSimple
  LatticeAdjoin.
Import List.ListNotations.

Example boolean_table :
  map (fun xy => let '(x, y) := xy in
    (leb bool_lattice x y, join bool_lattice x y,
     widen bool_lattice x y, narrow bool_lattice x y))
    [(false, false); (false, true); (true, false); (true, true)] =
  [(true, false, false, false); (true, true, true, false);
   (false, true, true, true); (true, true, true, true)].
Proof.
  vm_compute; reflexivity.
Qed.

Example unit_boundary :
  (leb unit_lattice tt tt, join unit_lattice tt tt, widen unit_lattice tt tt,
   narrow unit_lattice tt tt, rank unit_height tt,
   Cost.ticks (narrow_c unit_lattice tt tt)) = (true, tt, tt, tt, 0, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

Definition lifted_bool := lift_bot bool_lattice.

Example lift_none_none :
  (leb lifted_bool None None, join lifted_bool None None, widen lifted_bool None None,
   narrow lifted_bool None None, Cost.ticks (join_c lifted_bool None None)) =
  (true, None, None, None, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_none_some :
  (leb lifted_bool None (Some false), leb lifted_bool (Some false) None,
   join lifted_bool None (Some false), narrow lifted_bool (Some false) None,
   Cost.ticks (leb_c lifted_bool (Some false) None)) =
  (true, false, Some false, Some false, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_some_some :
  (leb lifted_bool (Some true) (Some false),
   join lifted_bool (Some false) (Some true),
   widen lifted_bool (Some false) (Some true),
   narrow lifted_bool (Some true) (Some false),
   Cost.ticks (join_c lifted_bool (Some false) (Some true))) =
  (false, Some true, Some true, Some true, 3%N).
Proof.
  vm_compute; reflexivity.
Qed.

Definition lifted_height := lift_bot_height bool_lattice bool_laws bool_height.

Definition lifted_wrank := lift_bot_wrank bool_lattice bool_wrank.

Example lift_measures :
  (map (rank lifted_height) [None; Some false; Some true],
   map (wrank lifted_wrank) [None; Some false; Some true],
   bound lifted_height, wbound lifted_wrank) = ([0; 1; 2], [2; 1; 0], 2, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_empty_meaning : ~ gamma (lift_bot_gamma (@bool_gamma nat)) None 0.
Proof.
  vm_compute; tauto.
Qed.
