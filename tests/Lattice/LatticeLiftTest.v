(** * Top-lift fixtures

    Unknown absorbs joins and narrowing can descend from it.
    For example, narrowing Unknown toward Elem false gives Elem false.
    Builds on: LatticeLift and LatticeSimple. *)

From Stdlib Require Import NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeLift LatticeSimple.
Import Cost.Notations.

Example lift_positive :
  join (lift_top_lattice bool_lattice) (Elem false) (Elem true) = Elem true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_negative :
  leb (lift_top_lattice bool_lattice) Unknown (Elem true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_unknown :
  join (lift_top_lattice bool_lattice) (Elem false) Unknown = Unknown.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_narrow_unknown :
  narrow (lift_top_lattice bool_lattice) Unknown (Elem false) = Elem false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_bottom :
  bot (lift_top_lattice bool_lattice) = Elem false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_leb_ticks :
  Cost.ticks (leb_c (lift_top_lattice bool_lattice) (Elem false) (Elem true)) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_join_ticks :
  Cost.ticks (join_c (lift_top_lattice bool_lattice) (Elem false) (Elem true)) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_unknown_ticks :
  Cost.ticks (join_c (lift_top_lattice bool_lattice) Unknown (Elem true)) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_measure_client :
  let H := lift_top_height bool_lattice bool_height in
  let W := lift_top_wrank bool_lattice bool_wrank in
  (bound H, rank H Unknown, rank H (Elem false),
   wbound W, wrank W Unknown, wrank W (Elem false)) = (2, 2, 0, 2, 0, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_callback_charges :
  let L := lift_top_lattice
    (with_widen_c bool_lattice (fun _ _ => Cost.tick 7 ;; Cost.ret true)) in
  (widen L (Elem false) (Elem false),
   Cost.ticks (widen_c L (Elem false) (Elem false))) = (Elem true, 9%N).
Proof.
  vm_compute; reflexivity.
Qed.
