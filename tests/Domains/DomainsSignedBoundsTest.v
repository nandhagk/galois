(** * Exact hemisphere reduction fixtures

    These examples check zero-sign reduction, malformed ranges and canonical hulls.
    For example, the feasible part of {0,4} inside [1,6] is the singleton 4.
    Builds on: DomainsSignedBounds and DomainsTnum. *)

From Stdlib Require Import ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds DomainsSignedBoundsDomain.

Local Open Scope Z_scope.

Example signed_zero_sign_reduction :
  sb_reduce_half 4%positive false (SBRange (Tnum 11 0) 1 6) =
    SBRange (Tnum 11 4) 4 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_raw_masks :
  sb_reduce_half 4%positive false (SBRange (Tnum 27 16) 1 6) =
    SBRange (Tnum 11 4) 4 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_conflicting :
  sb_reduce_half 4%positive false (SBRange (Tnum 1 1) 0 15) = SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_inverted :
  sb_reduce_half 4%positive false (SBRange tnum_top 6 1) = SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_out_of_range :
  sb_reduce_half 4%positive false (SBRange tnum_top (-5) 20) = SBRange (Tnum 8 0) 0 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_wrong_hemispheres :
  signed_bounds_reduce 4%positive
    (SignedBounds (SBRange tnum_top 8 15) (SBRange tnum_top 0 7)) =
    SignedBounds SBEmpty SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_one_bit :
  signed_bounds_reduce 1%positive
    (SignedBounds (SBRange tnum_top 0 1) (SBRange tnum_top 0 1)) =
    SignedBounds (SBRange (Tnum 1 0) 0 0) (SBRange (Tnum 0 1) 1 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_empty_cost :
  Cost.ticks (signed_bounds_reduce_c 4%positive (SignedBounds SBEmpty SBEmpty)) = 2%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_empty_queries :
  signed_bounds_query 4%positive (SignedBounds (SBRange (Tnum 11 0) 1 6) SBEmpty) true =
    None /\
  signed_bounds_query 4%positive (SignedBounds SBEmpty SBEmpty) false = None.
Proof.
  vm_compute. auto.
Qed.

Example signed_pair_query :
  let a := SignedBounds (SBRange (Tnum 9 0) 0 7) (SBRange (Tnum 0 9) 8 15) in
  signed_bounds_query 4%positive a false = Some (Tnum 9 0, 0, 6) /\
  signed_bounds_query 4%positive a true = Some (Tnum 0 9, 9, 15).
Proof.
  vm_compute. auto.
Qed.

Example signed_full_cube_cost :
  Cost.ticks (sb_reduce_half_c 4%positive false (SBRange tnum_top 0 15)) = 2%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_obsolete_remainder_rank_counterexample :
  Z.log2 (32 - 1) = Z.log2 (32 - 2).
Proof.
  vm_compute. reflexivity.
Qed.
