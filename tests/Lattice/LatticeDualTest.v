(** * Dual boolean fixtures

    Reversing boolean implication makes conjunction the join.
    For example, the dual bottom is true.
    Builds on: LatticeDual and LatticeSimple. *)

From Stdlib Require Import Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeDual LatticeSimple.
Import Cost.Notations.

Definition bool_meet_c (a b : bool) : Cost.t bool := Cost.step ;; Cost.ret (andb a b).
Definition dual_bool := dual bool_lattice bool_top bool_meet_c.

Example dual_positive : leb dual_bool true false = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_negative : leb dual_bool false true = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_join : join dual_bool true false = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_boundary : (bot dual_bool, join dual_bool true true) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_leb_ticks : Cost.ticks (leb_c dual_bool true false) = 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_join_ticks : Cost.ticks (join_c dual_bool true false) = 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example bool_meet_contract :
  meet_laws bool_lattice (fun a b => Cost.value (bool_meet_c a b)).
Proof.
  constructor.
  - intros [] []; vm_compute; reflexivity.
  - intros [] []; vm_compute; reflexivity.
  - intros [] [] []; vm_compute; congruence.
Qed.

Example dual_height_client :
  let H := dual_height bool_lattice bool_top bool_meet_c bool_laws bool_lub
    bool_meet_contract bool_height in
  (bound H, rank H true, rank H false) = (1, 0, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_callback_charges :
  Cost.ticks (join_c
    (dual bool_lattice bool_top (fun a b => Cost.tick 7 ;; Cost.ret (andb a b)))
    true false) = 8%N.
Proof.
  vm_compute; reflexivity.
Qed.
