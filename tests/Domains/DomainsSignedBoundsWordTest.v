(** * Signed-bound word and tagged regressions

    These fixtures port the independent DOM-9 word, query and operator observations.
    For example, [6,7] plus one splits into the singleton positive seven and negative eight.
    Builds on: DomainsSignedBoundsDomain and DomainsTagged. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTagged DomainsTnum DomainsTnumMul
  DomainsKnownBitsForward DomainsSignedBounds DomainsSignedOrder DomainsSignedWiden
  DomainsSignedBoundsRange DomainsSignedBoundsJoinRank DomainsSignedBoundsDomain.
Import List.ListNotations.

Local Open Scope Z_scope.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w2 := 2%positive.
Local Abbreviation w3 := 3%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w5 := 5%positive.

Definition sb_test_const := pconst signed_bounds_domain.

Definition sb_test_forward (w : width) (o : op) (xs : list signed_bounds) : signed_bounds :=
  pforward signed_bounds_domain o (map (fun a => (w, a)) xs) w.

Definition sb_test_classic_forward (w : width) (o : op) (xs : list signed_bounds)
    : signed_bounds :=
  pforward signed_bounds_classic_domain o (map (fun a => (w, a)) xs) w.

Definition sb_test_contains (w : width) (a : signed_bounds) (z : Z) : bool :=
  match if msb w z then sb_one a else sb_zero a with
  | SBEmpty => false
  | SBRange t lo hi =>
    (Z.land z (wrap w (zeros t)) =? 0) &&
      (Z.land (wrap w (ones t)) (Z.lnot z) =? 0) && (lo <=? z) && (z <=? hi)
  end.

Example sb_word_width_one :
  signed_bounds_top w1 =
    SignedBounds (SBRange (Tnum 1 0) 0 0) (SBRange (Tnum 0 1) 1 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_non_power_width :
  signed_bounds_query w3 (signed_bounds_top w3) false = Some (Tnum 4 0, 0, 3) /\
  signed_bounds_query w3 (signed_bounds_top w3) true = Some (Tnum 0 4, 4, 7).
Proof.
  vm_compute. auto.
Qed.

Example sb_word_outside_words :
  sb_reduce_half w3 true (SBRange tnum_top 8 15) = SBEmpty /\
  sb_test_const w3 (-1) = sb_test_const w3 7.
Proof.
  vm_compute. auto.
Qed.

Example sb_word_wrap_add :
  sb_test_forward w4 bvadd [sb_test_const w4 15; sb_test_const w4 1] = sb_test_const w4 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_sign_crossing :
  sb_test_forward w4 bvadd [sb_lift w4 tnum_top 6 7; sb_test_const w4 1] =
    SignedBounds (SBRange (Tnum 8 7) 7 7) (SBRange (Tnum 7 8) 8 8).
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_zero_divisors :
  sb_test_forward w4 bvudiv [sb_test_const w4 7; sb_test_const w4 0] = sb_test_const w4 15 /\
  sb_test_forward w4 bvsdiv [sb_test_const w4 8; sb_test_const w4 0] = sb_test_const w4 1 /\
  sb_test_forward w4 bvurem [sb_test_const w4 7; sb_test_const w4 0] = sb_test_const w4 7 /\
  sb_test_contains w4 (sb_test_forward w4 bvsrem [sb_test_const w4 9; sb_test_const w4 0]) 9 =
    true /\
  sb_test_contains w4 (sb_test_forward w4 bvsmod [sb_test_const w4 9; sb_test_const w4 0]) 9 =
    true /\
  eval_op bvsrem [(w4, 9); (w4, 0)] = Some (w4, 9) /\
  eval_op bvsmod [(w4, 9); (w4, 0)] = Some (w4, 9).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sb_word_overshifts_and_rotation :
  sb_test_forward w3 bvshl [sb_test_const w3 1; sb_test_const w3 7] = sb_test_const w3 0 /\
  sb_test_forward w3 bvlshr [sb_test_const w3 4; sb_test_const w3 7] = sb_test_const w3 0 /\
  sb_test_forward w3 bvashr [sb_test_const w3 4; sb_test_const w3 7] = sb_test_const w3 7 /\
  sb_test_forward w3 bvrotl [sb_test_const w3 1; sb_test_const w3 4] = sb_test_const w3 2.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sb_word_width_changes :
  pforward signed_bounds_domain (bvzext w1) [(w3, sb_test_const w3 7)] w4 =
    sb_test_const w4 7 /\
  pforward signed_bounds_domain (bvsext w1) [(w3, sb_test_const w3 7)] w4 =
    sb_test_const w4 15 /\
  pforward signed_bounds_domain (bvtrunc w2) [(w3, sb_test_const w3 7)] w2 =
    sb_test_const w2 3 /\
  pforward signed_bounds_domain (bvextract 2 1) [(w3, sb_test_const w3 7)] w2 =
    sb_test_const w2 3 /\
  pforward signed_bounds_domain bvconcat
    [(w3, sb_test_const w3 2); (w2, sb_test_const w2 3)] w5 = sb_test_const w5 11.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sb_word_all_eight_ite_branches :
  pforward signed_bounds_domain bvite
    [(w1, signed_bounds_top w1); (w3, sb_lift w3 (Tnum 3 0) 0 7);
     (w3, sb_lift w3 (Tnum 2 1) 0 7)] w3 =
    SignedBounds (SBRange (Tnum 6 0) 0 1) (SBRange (Tnum 2 4) 4 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_two_modular_pieces_one_sign :
  signed_bounds_query w4 (sb_from_ranges w4 tnum_top (sb_mod_ranges w4 6 19)) false =
    Some (Tnum 8 0, 0, 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_full_modular_range :
  sb_from_ranges w3 tnum_top (sb_mod_ranges w3 0 7) = signed_bounds_top w3.
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_guard_equality :
  passume signed_bounds_domain bveq
    [(w4, sb_lift w4 tnum_top 0 7); (w4, sb_test_const w4 3)] w1 (sb_test_const w1 1) =
    [sb_test_const w4 3; sb_test_const w4 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_guard_unsigned :
  passume signed_bounds_domain bvult
    [(w4, sb_lift w4 tnum_top 0 7); (w4, sb_test_const w4 4)] w1 (sb_test_const w1 1) =
    [sb_lift w4 tnum_top 0 3; sb_test_const w4 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_guard_signed_crossing :
  passume signed_bounds_domain bvslt
    [(w4, signed_bounds_top w4); (w4, sb_test_const w4 0)] w1 (sb_test_const w1 1) =
    [sb_lift w4 tnum_top 8 15; sb_test_const w4 0] /\
  passume signed_bounds_domain bvslt
    [(w1, signed_bounds_top w1); (w1, sb_test_const w1 0)] w1 (sb_test_const w1 1) =
    [sb_test_const w1 1; sb_test_const w1 0].
Proof.
  vm_compute. auto.
Qed.

Example sb_word_empty_guard :
  passume signed_bounds_domain bvadd
    [(w3, signed_bounds_top w3); (w3, signed_bounds_top w3)] w3
    (SignedBounds SBEmpty SBEmpty) = [SignedBounds SBEmpty SBEmpty; SignedBounds SBEmpty SBEmpty].
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_ite_backward_fallback :
  passume signed_bounds_domain bvite
    [(w1, signed_bounds_top w1); (w3, sb_lift w3 (Tnum 3 0) 0 7);
     (w3, sb_lift w3 (Tnum 2 1) 0 7)] w3 (sb_test_const w3 4) =
    [signed_bounds_top w1; sb_lift w3 (Tnum 3 0) 0 7; sb_lift w3 (Tnum 2 1) 0 7] /\
  pmeet signed_bounds_domain w3 (sb_test_const w3 0) (sb_test_const w3 1) =
    SignedBounds SBEmpty SBEmpty.
Proof.
  vm_compute. auto.
Qed.

Definition sb_test_different_masks : signed_bounds :=
  SignedBounds (SBRange (Tnum 9 0) 0 7) (SBRange (Tnum 0 9) 8 15).

Example sb_word_malformed_refinement :
  passume signed_bounds_domain bvadd
    [(w3, sb_test_different_masks); (w4, sb_test_different_masks)] w3 (signed_bounds_top w3) =
    [signed_bounds_reduce w3 sb_test_different_masks;
     signed_bounds_reduce w4 sb_test_different_masks] /\
  length (passume signed_bounds_domain bvite
    [(w3, signed_bounds_top w3); (w3, signed_bounds_top w3);
     (w3, signed_bounds_top w3); (w3, signed_bounds_top w3)] w3 (signed_bounds_top w3)) = 4%nat.
Proof.
  vm_compute. auto.
Qed.

Example sb_word_tagged_boundaries :
  forward (tagged_domain signed_bounds_domain) bvadd
    [TVal w3 (sb_test_const w3 1); TVal w4 (sb_test_const w4 1)] = TBot /\
  forward (tagged_domain signed_bounds_domain) bvadd [TBot; TAny] = TBot /\
  forward (tagged_domain signed_bounds_domain) bvadd
    [TAny; TVal w3 (sb_test_const w3 1)] = TAny.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition sb_test_mul_choices : signed_bounds := sb_lift w5 (Tnum 28 1) 1 3.

Example sb_word_precise_multiplication :
  let precise := sb_test_forward w5 bvmul [sb_test_mul_choices; sb_test_const w5 3] in
  let classic := sb_test_classic_forward w5 bvmul [sb_test_mul_choices; sb_test_const w5 3] in
  signed_bounds_query w5 precise false = Some (Tnum 16 1, 3, 9) /\
  signed_bounds_query w5 precise true = None /\
  sb_test_contains w5 precise 3 = true /\ sb_test_contains w5 precise 9 = true /\
  sb_test_contains w5 precise 4 = false /\ sb_test_contains w5 classic 4 = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sb_word_both_multiplication_boundaries :
  let check := fun D =>
    pforward D bvmul [(w1, sb_test_const w1 1); (w1, sb_test_const w1 1)] w1 =
      sb_test_const w1 1 /\
    pforward D bvmul [(w5, sb_test_const w5 7); (w5, sb_test_const w5 5)] w5 =
      sb_test_const w5 3 /\
    pforward D bvmul [(w5, SignedBounds (SBRange (Tnum 1 1) 0 15) SBEmpty);
      (w5, sb_test_const w5 3)] w5 = SignedBounds SBEmpty SBEmpty /\
    pforward D bvmul [(w5, sb_test_const w5 0);
      (w5, SignedBounds SBEmpty (SBRange (Tnum 1 1) 16 31))] w5 =
      SignedBounds SBEmpty SBEmpty in
  check signed_bounds_domain /\ check signed_bounds_classic_domain.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sb_word_multiplication_fallbacks :
  let check := fun xs rw =>
    pforward signed_bounds_domain bvmul xs rw =
      pforward signed_bounds_classic_domain bvmul xs rw in
  check [] w5 /\ check [(w5, sb_test_mul_choices)] w5 /\
  check [(w5, sb_test_mul_choices); (w4, sb_test_const w4 3)] w5 /\
  check [(w5, sb_test_mul_choices); (w5, sb_test_const w5 3)] w4 /\
  check [(w5, sb_test_mul_choices); (w5, sb_test_const w5 3); (w5, sb_test_mul_choices)] w5 /\
  check [(w5, sb_test_mul_choices); (w5, sb_test_mul_choices);
    (w5, sb_test_mul_choices); (w5, sb_test_mul_choices)] w5.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition sb_test_words (w : width) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat (modulus w))).

Example sb_word_multiplication_sets :
  filter (sb_test_contains w5
    (sb_test_forward w5 bvmul [sb_test_mul_choices; sb_test_const w5 3])) (sb_test_words w5) =
    [3; 5; 7; 9] /\
  map (fun x => wmul w5 x 3) (filter (sb_test_contains w5 sb_test_mul_choices) (sb_test_words w5)) =
    [3; 9].
Proof.
  vm_compute. auto.
Qed.

Example sb_word_multiplication_tagged_clients :
  let precise := SignedBounds (SBRange (Tnum 16 1) 3 9) SBEmpty in
  let classic := SignedBounds (SBRange (Tnum 16 0) 3 9) SBEmpty in
  forward (tagged_domain signed_bounds_domain) bvmul
    [TVal w5 sb_test_mul_choices; TVal w5 (sb_test_const w5 3)] = TVal w5 precise /\
  forward (tagged_domain signed_bounds_classic_domain) bvmul
    [TVal w5 sb_test_mul_choices; TVal w5 (sb_test_const w5 3)] = TVal w5 classic.
Proof.
  vm_compute. auto.
Qed.

Example sb_word_constant_cost_boundaries :
  Cost.ticks (signed_bounds_top_c w4) = 1%N /\
  Cost.ticks (signed_bounds_const_c w4 4) = 4%N.
Proof.
  vm_compute. auto.
Qed.

Example sb_word_nullary_legacy_choices :
  pforward signed_bounds_domain bvadd [] w4 = signed_bounds_top w4 /\
  pforward signed_bounds_classic_domain bvmul [] w4 = signed_bounds_top w4.
Proof.
  vm_compute. auto.
Qed.

Example sb_word_nonempty_builder_charge_control :
  pforward_c (signed_bounds_word_domain signed_bounds_default_options) bvadd
    [(w4, sb_lift w4 tnum_top 6 7); (w4, sb_test_const w4 1)] w4 =
  pforward_c (signed_bounds_word_builder signed_bounds_default_options) bvadd
    [(w4, sb_lift w4 tnum_top 6 7); (w4, sb_test_const w4 1)] w4.
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_remaining_query_boundaries :
  sb_reduce_half w4 false (SBRange tnum_top 8 15) = SBEmpty /\
  signed_bounds_query w4 (sb_test_const w4 4) true = None /\
  signed_bounds_query w4 (SignedBounds SBEmpty SBEmpty) false = None /\
  signed_bounds_query w4 (SignedBounds SBEmpty SBEmpty) true = None /\
  signed_bounds_query w4 (SignedBounds (SBRange tnum_top 6 1) SBEmpty) false = None /\
  signed w4 9 = -7 /\ signed w4 15 = -1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition sb_test_legacy_precise : word_domain signed_bounds :=
  signed_bounds_word_domain (SignedBoundsOptions known_bits_default_options WidenJoin).

(** Non-multiplication parity holds for arbitrary raw values, widths and arities. *)
Example sb_word_nonmultiplication_agrees : forall o xs rw, o <> bvmul ->
  pforward signed_bounds_domain o xs rw = pforward signed_bounds_classic_domain o xs rw.
Proof.
  intros o xs rw Hother. unfold pforward.
  change (Cost.value (pforward_c (signed_bounds_word_domain signed_bounds_default_options)
    o xs rw) = Cost.value
      (pforward_c (signed_bounds_word_domain signed_bounds_classic_options) o xs rw)).
  now rewrite (signed_bounds_nonmultiplication_agrees
    signed_bounds_default_options signed_bounds_classic_options o Hother).
Qed.

Example sb_word_legacy_join_progress :
  Nat.ltb (signed_bounds_join_wrank w3
    (widen (signed_bounds_lattice WidenJoin w3) (sb_test_const w3 0) (sb_test_const w3 1)))
    (signed_bounds_join_wrank w3 (sb_test_const w3 0)) = true /\
  narrow (signed_bounds_lattice WidenJoin w3) sb_test_different_masks (signed_bounds_top w3) =
    signed_bounds_reduce w3 sb_test_different_masks.
Proof.
  vm_compute. auto.
Qed.

Example sb_word_legacy_raw_join_progress :
  let raw := SignedBounds (SBRange (Tnum 27 16) 1 6) SBEmpty in
  signed_bounds_join_wrank w4 raw = signed_bounds_join_wrank w4 (sb_test_const w4 4) /\
  Nat.ltb (signed_bounds_join_wrank w4
    (widen (signed_bounds_lattice WidenJoin w4) raw (sb_test_const w4 5)))
    (signed_bounds_join_wrank w4 raw) = true.
Proof.
  vm_compute. auto.
Qed.

