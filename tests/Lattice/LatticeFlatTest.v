(** * Flat fixtures

    Flat booleans distinguish two incomparable known values.
    For example, their join is top even though neither covers the other.
    Builds on: LatticeFlat. *)

From Stdlib Require Import Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeFlat LatticeHeight.

Example flat_positive : join (flat_lattice Bool.eqb) (FVal true) (FVal true) = FVal true.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_negative : leb (flat_lattice Bool.eqb) (FVal true) (FVal false) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_bottom : join (flat_lattice Bool.eqb) FBot FBot = FBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_top_absorbs : join (flat_lattice Bool.eqb) (FVal false) FTop = FTop.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_leb_ticks :
  Cost.ticks (leb_c (flat_lattice Bool.eqb) (FVal true) (FVal false)) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_join_ticks :
  Cost.ticks (join_c (flat_lattice Bool.eqb) (FVal true) (FVal false)) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_rank_levels :
  (rank (flat_height Bool.eqb Bool.eqb_true_iff) FBot,
   rank (flat_height Bool.eqb Bool.eqb_true_iff) (FVal false),
   rank (flat_height Bool.eqb Bool.eqb_true_iff) FTop) = (0, 1, 2).
Proof.
  vm_compute; reflexivity.
Qed.
