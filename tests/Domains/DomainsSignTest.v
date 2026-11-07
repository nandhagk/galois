(** * Sign lattice examples

    These examples exercise intersection and the finite height.
    For example, incompatible sign classes intersect to bottom.
    Builds on: DomainsSign. *)

From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Domains Require Import DomainsSign.

Example sign_intersection_zero :
  sign_meet (Sign true true false) (Sign false true true) = Sign false true false.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_intersection_disjoint :
  sign_meet (Sign true false false) (Sign false false true) = bot sign_lattice.
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_height_bound : bound sign_height_on = 3.
Proof.
  vm_compute. reflexivity.
Qed.
