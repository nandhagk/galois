(** * Differential simple-lattice tests

    New and legacy operations agree on every boolean and unit input.
    For example, narrowing true by false keeps true in both libraries.
    Builds on: LatticeSimple and legacy OrderBasic. *)

From Galois.Lattice Require Import LatticeCore LatticeSimple.
From GaloisLegacy.Order Require OrderLattice OrderBasic.

Example bool_all_inputs :
  forall a b,
  (leb bool_lattice a b, join bool_lattice a b,
   widen bool_lattice a b, narrow bool_lattice a b) =
  (OrderLattice.leb OrderBasic.bool_lattice a b,
   OrderLattice.join OrderBasic.bool_lattice a b,
   OrderLattice.widen OrderBasic.bool_lattice a b,
   OrderLattice.narrow OrderBasic.bool_lattice a b).
Proof.
  vm_compute; reflexivity.
Qed.

Example unit_all_inputs :
  forall a b,
  (leb unit_lattice a b, join unit_lattice a b,
   widen unit_lattice a b, narrow unit_lattice a b) =
  (OrderLattice.leb OrderBasic.unit_lattice a b,
   OrderLattice.join OrderBasic.unit_lattice a b,
   OrderLattice.widen OrderBasic.unit_lattice a b,
   OrderLattice.narrow OrderBasic.unit_lattice a b).
Proof.
  intros [] []; vm_compute; reflexivity.
Qed.
