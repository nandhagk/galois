(** * Exact hemisphere reduction fixtures

    These examples check zero-sign reduction, malformed ranges and canonical hulls.
    For example, the feasible part of {0,4} inside [1,6] is the singleton 4.
    Builds on: DomainsSignedBounds and DomainsTnum. *)

From Stdlib Require Import ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds DomainsSignedOrder
  DomainsSignedWiden DomainsSignedBoundsRange DomainsSignedBoundsDomain DomainsSignedBoundsCost.

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

Example signed_raw_order_requires_reduction :
  sb_order 4%positive (SBRange (Tnum 1 1) 0 7) SBEmpty = false /\
  sb_leb 4%positive false (SBRange (Tnum 1 1) 0 7) SBEmpty = true /\
  sb_leb 4%positive false (SBRange tnum_top 6 1) SBEmpty = true.
Proof.
  vm_compute. auto.
Qed.

Example signed_join_raw_inverted :
  signed_bounds_join 4%positive
    (SignedBounds (SBRange tnum_top 6 1) SBEmpty)
    (SignedBounds (SBRange (Tnum 11 0) 1 6) SBEmpty) =
    SignedBounds (SBRange (Tnum 11 4) 4 4) SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

(** The reduction-aware logarithmic candidate fails on this even-word half. *)
Example signed_reduction_requires_rank_fallback :
  let a := SignedBounds (SBRange (Tnum 9 0) 0 4) SBEmpty in
  let b := SignedBounds (SBRange (Tnum 9 6) 6 6) SBEmpty in
  let next := sb_widen_with WidenDouble 4%positive a b in
  next = SignedBounds (SBRange (Tnum 9 0) 0 7) SBEmpty /\
  signed_bounds_reduce 4%positive next = SignedBounds (SBRange (Tnum 9 0) 0 6) SBEmpty /\
  signed_bounds_leb 4%positive b a = false /\
  signed_bounds_wrank 4%positive (signed_bounds_reduce 4%positive next) =
    signed_bounds_wrank 4%positive a /\
  Nat.ltb (signed_bounds_wrank 4%positive next) (signed_bounds_wrank 4%positive a) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example signed_default_width_eight_bound :
  wbound (signed_bounds_widening_rank_on 8%positive) = 52%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Definition signed_test_prefix (k : Z) : signed_bounds :=
  signed_bounds_reduce 6%positive (SignedBounds (SBRange tnum_top 0 k) SBEmpty).

Fixpoint signed_test_chain (strategy : sb_widening) (n : nat) (k : Z) (a : signed_bounds)
    : nat :=
  match n with
  | O => O
  | S n =>
    let next := sb_widen_with strategy 6%positive a (signed_test_prefix k) in
    let strict := if signed_bounds_leb 6%positive next a then O else 1%nat in
    (strict + signed_test_chain strategy n (k + 1) next)%nat
  end.

Example signed_strict_widening_chain_comparison :
  signed_test_chain WidenJoin 31 1 (signed_test_prefix 0) = 31%nat /\
  signed_test_chain WidenDouble 31 1 (signed_test_prefix 0) = 9%nat /\
  Nat.ltb (signed_test_chain WidenDouble 31 1 (signed_test_prefix 0))
    (wbound (signed_bounds_widening_rank_on 6%positive)) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example signed_threshold_unsorted :
  sb_widen_with (WidenThresholds (5 :: 0 :: 5 :: 7 :: nil)) 4%positive
    (SignedBounds (SBRange (Tnum 15 0) 0 0) SBEmpty)
    (SignedBounds (SBRange (Tnum 14 1) 1 1) SBEmpty) =
    SignedBounds (SBRange (Tnum 14 0) 0 5) SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_cost_bound_clients :
  (Cost.ticks (signed_bounds_reduce_c 4%positive
    (SignedBounds (SBRange tnum_top 1 6) SBEmpty)) <= 64)%N /\
  Cost.ticks (sb_widen_with_c WidenDouble 4%positive
    (signed_bounds_top 4%positive) (signed_bounds_top 4%positive)) = 1%N.
Proof.
  vm_compute. intuition discriminate.
Qed.
