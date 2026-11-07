(** * Differential mask and multiplier fixtures

    The new mask operations and multipliers are compared with their legacy implementations.
    For example, nonconstant low-zero multiplication keeps the legacy trailing-zero result.
    Builds on: new and legacy known-bit multiplication and signed-half reduction. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith DomainsTnumMul
  DomainsSignedBounds DomainsNumeric DomainsKnownBits DomainsSignedBoundsRange
  DomainsSignedBoundsDomain.
From GaloisLegacy.Bits Require BitsOp.
From GaloisLegacy.Domains Require DomainsNumeric DomainsKnownBits DomainsKnownBitsFast
  DomainsSignedBounds DomainsSignedBoundsDomain.
Import List.ListNotations.

Module OldBits := GaloisLegacy.Domains.DomainsKnownBits.
Module OldMul := GaloisLegacy.Domains.DomainsKnownBitsFast.
Module OldBounds := GaloisLegacy.Domains.DomainsSignedBounds.
Module OldSB := GaloisLegacy.Domains.DomainsSignedBoundsDomain.
Module OldNumeric := GaloisLegacy.Domains.DomainsNumeric.
Module OldOp := GaloisLegacy.Bits.BitsOp.

Local Open Scope Z_scope.

Definition legacy_tnum (a : tnum) : OldBits.tnum := OldBits.Tnum (zeros a) (ones a).

Definition legacy_tnum_agrees (a : tnum) (b : OldBits.tnum) : bool :=
  (zeros a =? OldBits.zeros b) && (ones a =? OldBits.ones b).

Definition legacy_mul_fixtures (w : width) : list tnum :=
  [tnum_top; tnum_const w 0; tnum_const w 1; tnum_const w (-1);
   Tnum 1 0; Tnum 0 1; Tnum 1 1; Tnum (-2) 256; Tnum 3 0; Tnum 28 1].

Definition legacy_mul_comparison (w : width) : bool :=
  forallb (fun a => forallb (fun b =>
    legacy_tnum_agrees (tnum_mul w a b) (OldBits.tnum_mul w (legacy_tnum a) (legacy_tnum b)) &&
    legacy_tnum_agrees (tnum_mul_stages w a b)
      (OldMul.tnum_mul_precise w (legacy_tnum a) (legacy_tnum b)) &&
    legacy_tnum_agrees (tnum_add w a b)
      (OldBits.tnum_add w (legacy_tnum a) (legacy_tnum b)) &&
    legacy_tnum_agrees (tnum_sub w a b)
      (OldBits.tnum_sub w (legacy_tnum a) (legacy_tnum b)))
    (legacy_mul_fixtures w)) (legacy_mul_fixtures w).

Example legacy_multipliers_widths_one_four_eight :
  forallb legacy_mul_comparison [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_half (h : sb_half) : OldBounds.sb_half :=
  match h with
  | SBEmpty => OldBounds.SBEmpty
  | SBRange t lo hi => OldBounds.SBRange (legacy_tnum t) lo hi
  end.

Definition legacy_half_agrees (a : sb_half) (b : OldBounds.sb_half) : bool :=
  match a, b with
  | SBEmpty, OldBounds.SBEmpty => true
  | SBRange ta la ua, OldBounds.SBRange tb lb ub =>
    legacy_tnum_agrees ta tb && (la =? lb) && (ua =? ub)
  | _, _ => false
  end.

Definition legacy_reduction_comparison (w : width) : bool :=
  forallb (fun t => forallb (fun s => forallb (fun r =>
    let '(lo, hi) := r in
    legacy_half_agrees (sb_reduce_half w s (SBRange t lo hi))
      (OldBounds.sb_reduce_half w s (legacy_half (SBRange t lo hi))))
    [(0, modulus w - 1); (1, 6); (-5, modulus w + 4); (6, 1)])
    [false; true]) (legacy_mul_fixtures w).

Example legacy_reduction_widths_one_four_eight :
  forallb legacy_reduction_comparison [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Fixpoint legacy_payloads_agree (xs : list tnum) (ys : list OldBits.tnum) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => legacy_tnum_agrees x y && legacy_payloads_agree xs ys
  | _, _ => false
  end.

Definition legacy_test_operators : list op :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvadd; bvsub; bvmul; bvudiv; bvurem;
   bvsdiv; bvsrem; bvsmod; bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl; bvrotr;
   bveq; bvne; bvult; bvule; bvslt; bvsle; bvite; bvzext 1%positive; bvsext 1%positive;
   bvtrunc 1%positive; bvextract 0 0; bvconcat].

Definition legacy_operator (o : op) : OldOp.op :=
  match o with
  | bvnot => OldOp.bvnot
  | bvneg => OldOp.bvneg
  | bvclz => OldOp.bvclz
  | bvctz => OldOp.bvctz
  | bvpopcnt => OldOp.bvpopcnt
  | bvadd => OldOp.bvadd
  | bvsub => OldOp.bvsub
  | bvmul => OldOp.bvmul
  | bvudiv => OldOp.bvudiv
  | bvurem => OldOp.bvurem
  | bvsdiv => OldOp.bvsdiv
  | bvsrem => OldOp.bvsrem
  | bvsmod => OldOp.bvsmod
  | bvand => OldOp.bvand
  | bvor => OldOp.bvor
  | bvxor => OldOp.bvxor
  | bvshl => OldOp.bvshl
  | bvlshr => OldOp.bvlshr
  | bvashr => OldOp.bvashr
  | bvrotl => OldOp.bvrotl
  | bvrotr => OldOp.bvrotr
  | bveq => OldOp.bveq
  | bvne => OldOp.bvne
  | bvult => OldOp.bvult
  | bvule => OldOp.bvule
  | bvslt => OldOp.bvslt
  | bvsle => OldOp.bvsle
  | bvite => OldOp.bvite
  | bvzext n => OldOp.bvzext n
  | bvsext n => OldOp.bvsext n
  | bvtrunc n => OldOp.bvtrunc n
  | bvextract hi lo => OldOp.bvextract hi lo
  | bvconcat => OldOp.bvconcat
  end.

Definition legacy_test_inputs {P} (w : width) (o : op) (a b : P) : list (width * P) :=
  match arity o with
  | 1%nat => [(w, a)]
  | 2%nat => [(w, a); (w, b)]
  | _ => [(1%positive, a); (w, a); (w, b)]
  end.

Definition legacy_operator_comparison_at (w : width) (o : op) (a b : tnum)
    (rw : width) : bool :=
  let xs := legacy_test_inputs w o a b in
  let oldxs := map (fun wp => (fst wp, legacy_tnum (snd wp))) xs in
  let oldop := legacy_operator o in
  legacy_tnum_agrees (pforward known_bits_classic_domain o xs rw)
    (OldNumeric.pforward OldBits.known_bits_domain oldop oldxs rw) &&
  legacy_tnum_agrees (pforward known_bits_domain o xs rw)
    (OldNumeric.pforward OldMul.known_bits_precise_domain oldop oldxs rw) &&
  legacy_payloads_agree (passume known_bits_classic_domain o xs rw a)
    (OldNumeric.passume OldBits.known_bits_domain oldop oldxs rw (legacy_tnum a)) &&
  legacy_payloads_agree (passume known_bits_domain o xs rw a)
    (OldNumeric.passume OldMul.known_bits_precise_domain oldop oldxs rw (legacy_tnum a)).

Definition legacy_operator_comparison (w : width) (o : op) (a b : tnum) : bool :=
  let rw := match result_width o (map fst (legacy_test_inputs w o a b)) with
    | Some r => r | None => w end in
  legacy_operator_comparison_at w o a b rw.

Definition legacy_all_operators_comparison (w : width) : bool :=
  forallb (fun o => forallb (fun a => forallb (legacy_operator_comparison w o a)
    (legacy_mul_fixtures w)) (legacy_mul_fixtures w)) legacy_test_operators.

Example legacy_full_known_bits_widths_one_four_eight :
  forallb legacy_all_operators_comparison [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_signed (a : signed_bounds) : OldBounds.signed_bounds :=
  OldBounds.SignedBounds (legacy_half (sb_zero a)) (legacy_half (sb_one a)).

Definition legacy_signed_agrees (a : signed_bounds) (b : OldBounds.signed_bounds) : bool :=
  legacy_half_agrees (sb_zero a) (OldBounds.sb_zero b) &&
    legacy_half_agrees (sb_one a) (OldBounds.sb_one b).

Fixpoint legacy_signed_list_agrees (xs : list signed_bounds)
    (ys : list OldBounds.signed_bounds) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => legacy_signed_agrees x y && legacy_signed_list_agrees xs ys
  | _, _ => false
  end.

Definition legacy_signed_fixtures (w : width) : list signed_bounds :=
  [signed_bounds_top w; pconst signed_bounds_domain w 0; pconst signed_bounds_domain w 1;
   pconst signed_bounds_domain w (-1); sb_lift w tnum_top 0 3;
   sb_lift w (Tnum 1 0) 0 (modulus w - 1);
   SignedBounds (SBRange (Tnum 1 1) 0 7) SBEmpty].

Definition legacy_signed_operator_observation_at (w : width) (o : op)
    (a b : signed_bounds) (rw : width) : bool * bool :=
  let xs := legacy_test_inputs w o a b in
  let oldxs := map (fun wp => (fst wp, legacy_signed (snd wp))) xs in
  let oldop := legacy_operator o in
  (legacy_signed_agrees (pforward signed_bounds_classic_domain o xs rw)
    (OldNumeric.pforward OldSB.signed_bounds_classic_domain oldop oldxs rw) &&
  legacy_signed_agrees (pforward signed_bounds_domain o xs rw)
    (OldNumeric.pforward OldSB.signed_bounds_domain oldop oldxs rw),
  legacy_signed_list_agrees (passume signed_bounds_classic_domain o xs rw a)
    (OldNumeric.passume OldSB.signed_bounds_classic_domain oldop oldxs rw (legacy_signed a)) &&
  legacy_signed_list_agrees (passume signed_bounds_domain o xs rw a)
    (OldNumeric.passume OldSB.signed_bounds_domain oldop oldxs rw (legacy_signed a))).

Definition legacy_signed_operator_comparison_at (w : width) (o : op)
    (a b : signed_bounds) (rw : width) : bool :=
  let compared := legacy_signed_operator_observation_at w o a b rw in
  fst compared && snd compared.

Definition legacy_signed_operator_comparison (w : width) (o : op)
    (a b : signed_bounds) : bool :=
  let rw := match result_width o (map fst (legacy_test_inputs w o a b)) with
    | Some r => r | None => w end in
  legacy_signed_operator_comparison_at w o a b rw.

Definition legacy_signed_first_difference (w : width)
    : option (op * signed_bounds * signed_bounds) :=
  find (fun c => let '(o, a, b) := c in
    negb (legacy_signed_operator_comparison w o a b))
    (flat_map (fun o => flat_map (fun a => map (fun b => (o, a, b))
      (legacy_signed_fixtures w)) (legacy_signed_fixtures w)) legacy_test_operators).

Example legacy_signed_zero_remainder_control :
  let w := 1%positive in
  let a := pconst signed_bounds_domain w 1 in
  let b := pconst signed_bounds_domain w 0 in
  let xs := [(w, a); (w, b)] in
  let oldxs := [(w, legacy_signed a); (w, legacy_signed b)] in
  (legacy_signed_agrees (pforward signed_bounds_classic_domain bvsrem xs w)
    (OldNumeric.pforward OldSB.signed_bounds_classic_domain OldOp.bvsrem oldxs w),
   legacy_signed_list_agrees (passume signed_bounds_classic_domain bvsrem xs w a)
    (OldNumeric.passume OldSB.signed_bounds_classic_domain OldOp.bvsrem oldxs w
      (legacy_signed a))) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_signed_width_one : legacy_signed_first_difference 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_signed_multiplication_control :
  let w := 4%positive in
  let a := pconst signed_bounds_domain w (-1) in
  let b := signed_bounds_top w in
  let xs := [(w, a); (w, b)] in
  let oldxs := [(w, legacy_signed a); (w, legacy_signed b)] in
  (legacy_signed_agrees (pforward signed_bounds_classic_domain bvmul xs w)
    (OldNumeric.pforward OldSB.signed_bounds_classic_domain OldOp.bvmul oldxs w),
   legacy_signed_list_agrees (passume signed_bounds_classic_domain bvmul xs w a)
    (OldNumeric.passume OldSB.signed_bounds_classic_domain OldOp.bvmul oldxs w
      (legacy_signed a))) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_signed_width_four : legacy_signed_first_difference 4%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_signed_width_eight : legacy_signed_first_difference 8%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_requested_width_operators : list op :=
  [bvnot; bvneg; bvclz; bvadd; bvmul; bvudiv; bvsdiv; bvsrem; bveq; bvshl;
   bvzext 1%positive; bvsext 1%positive; bvtrunc 1%positive; bvextract 0 0; bvconcat].

Definition legacy_requested_widths : list width :=
  [1%positive; 2%positive; 3%positive; 5%positive; 8%positive].

Definition legacy_signed_requested_width_fixtures : list signed_bounds :=
  legacy_signed_fixtures 4%positive ++
    [sb_lift 4%positive tnum_top 3 4; sb_lift 4%positive tnum_top 0 6].

Definition legacy_distinct_requested_width {P} (w : width) (o : op) (a b : P)
    (rw : width) : bool :=
  match result_width o (map fst (legacy_test_inputs w o a b)) with
  | Some generated => negb (Pos.eqb generated rw)
  | None => false
  end.

Example legacy_known_bits_distinct_requested_widths :
  forallb (fun o => forallb (fun a => forallb (fun b => forallb (fun rw =>
    if legacy_distinct_requested_width 4%positive o a b rw
    then legacy_operator_comparison_at 4%positive o a b rw else true)
    legacy_requested_widths) (legacy_mul_fixtures 4%positive))
    (legacy_mul_fixtures 4%positive)) legacy_requested_width_operators = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_signed_requested_width_agreement (backward : bool) (o : op) (rw : width)
    : bool :=
  forallb (fun a => forallb (fun b =>
    if legacy_distinct_requested_width 4%positive o a b rw then
      let compared := legacy_signed_operator_observation_at 4%positive o a b rw in
      if backward then snd compared else fst compared
    else true) legacy_signed_requested_width_fixtures) legacy_signed_requested_width_fixtures.

Definition legacy_signed_requested_width_diagnostics : list (op * list width) :=
  filter (fun p => negb (Nat.eqb (length (snd p)) 0))
    (map (fun o => (o, filter (fun rw =>
      negb (legacy_signed_requested_width_agreement false o rw)) legacy_requested_widths))
      legacy_requested_width_operators).

(** Mismatched-annotation exceptions make no semantic refinement claim. *)
Example legacy_signed_requested_width_exception_inventory :
  legacy_signed_requested_width_diagnostics =
    [(bvnot, [1%positive; 2%positive; 3%positive]);
     (bvneg, [1%positive; 2%positive; 3%positive; 5%positive; 8%positive]);
     (bvclz, [1%positive; 2%positive]);
     (bvadd, [1%positive; 2%positive; 3%positive; 5%positive; 8%positive]);
     (bvmul, [1%positive; 2%positive; 3%positive; 8%positive]);
     (bvudiv, [1%positive; 2%positive; 3%positive]);
     (bvsdiv, [1%positive]);
     (bvsrem, [1%positive; 2%positive; 3%positive]);
     (bvshl, [1%positive; 2%positive; 3%positive]);
     (bvzext 1%positive, [1%positive; 2%positive; 3%positive]);
     (bvsext 1%positive, [1%positive; 2%positive; 3%positive]);
     (bvtrunc 1%positive, [2%positive; 3%positive; 5%positive; 8%positive]);
     (bvconcat, [1%positive; 2%positive; 3%positive; 5%positive])].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_signed_requested_width_backward_controls :
  forallb (fun o => forallb (legacy_signed_requested_width_agreement true o)
    legacy_requested_widths) legacy_requested_width_operators = true.
Proof.
  vm_compute. reflexivity.
Qed.

Record legacy_width_witness : Type := LegacyWidthWitness {
  width_witness_op : op;
  width_witness_inputs : list (width * signed_bounds);
  width_witness_requested : width;
  width_witness_new : signed_bounds;
  width_witness_old : signed_bounds
}.

Definition legacy_width_witnesses : list legacy_width_witness :=
  let w1 := 1%positive in
  let w2 := 2%positive in
  let w3 := 3%positive in
  let w4 := 4%positive in
  let w5 := 5%positive in
  let c := pconst signed_bounds_domain in
  let empty := SignedBounds SBEmpty SBEmpty in
  [LegacyWidthWitness bvnot [(w4, c w4 0)] w3 empty (c w3 7);
   LegacyWidthWitness bvneg [(w4, c w4 1)] w5 (c w5 15) (c w5 31);
   LegacyWidthWitness bvmul [(w4, c w4 15); (w4, sb_lift w4 tnum_top 0 3)] w3
     (signed_bounds_top w3)
     (SignedBounds (SBRange (Tnum 7 0) 0 0) (SBRange (Tnum 0 4) 5 7));
   LegacyWidthWitness bvsdiv [(w4, c w4 1); (w4, c w4 15)] w1
     (signed_bounds_top w1) (c w1 1);
   LegacyWidthWitness bvneg [(w4, sb_lift w4 tnum_top 0 6)] w1
     (signed_bounds_top w1) (c w1 0);
   LegacyWidthWitness bvmul [(w4, sb_lift w4 tnum_top 3 4); (w4, c w4 1)] w2
     (SignedBounds (SBRange (Tnum 3 0) 0 0) (SBRange (Tnum 0 3) 3 3))
     (SignedBounds (SBRange (Tnum 3 0) 0 0) (SBRange (Tnum 0 3) 3 3));
   LegacyWidthWitness (bvzext w1) [(w4, c w4 15)] w3 empty (c w3 7);
   LegacyWidthWitness bvconcat [(w4, c w4 2); (w4, c w4 3)] w3 empty (c w3 3);
   LegacyWidthWitness bvadd [(w4, c w4 15); (w4, c w4 1)] w5 (c w5 0) (c w5 16);
   LegacyWidthWitness bvmul [(w4, c w4 15); (w4, sb_lift w4 tnum_top 3 4)] w2
     (signed_bounds_top w2) (SignedBounds (SBRange (Tnum 2 0) 0 1) SBEmpty);
   LegacyWidthWitness bvmul [(w4, c w4 15); (w4, c w4 3)] w3 empty (c w3 5)].

Definition legacy_width_witness_observed (c : legacy_width_witness) : bool :=
  let o := width_witness_op c in
  let xs := width_witness_inputs c in
  let rw := width_witness_requested c in
  let oldxs := map (fun wp => (fst wp, legacy_signed (snd wp))) xs in
  let oldop := legacy_operator o in
  legacy_signed_agrees (pforward signed_bounds_classic_domain o xs rw)
    (legacy_signed (width_witness_new c)) &&
  legacy_signed_agrees (pforward signed_bounds_domain o xs rw)
    (legacy_signed (width_witness_new c)) &&
  legacy_signed_agrees (width_witness_old c)
    (OldNumeric.pforward OldSB.signed_bounds_classic_domain oldop oldxs rw) &&
  legacy_signed_agrees (width_witness_old c)
    (OldNumeric.pforward OldSB.signed_bounds_domain oldop oldxs rw).

Example legacy_requested_width_exact_witness_observations :
  forallb legacy_width_witness_observed legacy_width_witnesses = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_width_witness_impossible (c : legacy_width_witness) : bool :=
  match result_width (width_witness_op c) (map fst (width_witness_inputs c)) with
  | Some generated => negb (Pos.eqb generated (width_witness_requested c))
  | None => true
  end.

Example legacy_requested_width_shape_controls :
  forallb legacy_width_witness_impossible legacy_width_witnesses = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Every recorded requested width is impossible for a successful evaluation of those shapes. *)
Example legacy_requested_width_nonsuccess : forall c cs z,
  In c legacy_width_witnesses ->
  map fst cs = map fst (width_witness_inputs c) ->
  eval_op (width_witness_op c) cs <> Some (width_witness_requested c, z).
Proof.
  intros c cs z Hin Hwidths Heval.
  pose proof (eval_op_width _ cs (width_witness_requested c, z) Heval) as Hgenerated.
  cbn [fst] in Hgenerated. rewrite Hwidths in Hgenerated.
  pose proof legacy_requested_width_shape_controls as Hcontrols.
  apply forallb_forall with (x := c) in Hcontrols; [|exact Hin].
  unfold legacy_width_witness_impossible in Hcontrols. rewrite Hgenerated in Hcontrols.
  rewrite Pos.eqb_refl in Hcontrols. discriminate.
Qed.
