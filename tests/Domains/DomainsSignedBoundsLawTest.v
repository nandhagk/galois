(** * Symbolic signed multiplication clients

    Both selected word-law records give the original universal multiplication client.
    For example, every member of {1,3} times three is in both selected abstract results.
    Builds on: DomainsSignedBoundsWordTest and the public word-law records. *)

From Stdlib Require Import ZArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTransfer DomainsKnownBitsForward
  DomainsSignedBounds DomainsSignedWiden DomainsSignedBoundsDomain.
From Galois.Tests.Domains Require Import DomainsSignedBoundsWordTest.
Import List.ListNotations.

Local Open Scope Z_scope.
Local Abbreviation w5 := 5%positive.

(** Both selected word-law records give the original universal multiplication client. *)
Example sb_word_both_multiplication_laws : forall x,
  signed_bounds_gamma w5 sb_test_mul_choices x ->
  signed_bounds_gamma w5
    (sb_test_forward w5 bvmul [sb_test_mul_choices; sb_test_const w5 3]) (wmul w5 x 3) /\
  signed_bounds_gamma w5
    (sb_test_classic_forward w5 bvmul [sb_test_mul_choices; sb_test_const w5 3]) (wmul w5 x 3).
Proof.
  intros x Hx.
  assert (Hword : is_word w5 x).
  { assert (Hhalf : forall s h, sb_bit_gamma w5 s h x -> is_word w5 x).
    { intros s [|t lo hi] H; [contradiction|exact (proj1 H)]. }
    destruct Hx as [[Hbit _]|[Hbit _]].
    - exact (Hhalf false (sb_zero sb_test_mul_choices) Hbit).
    - exact (Hhalf true (sb_one sb_test_mul_choices) Hbit). }
  assert (Hpayload : Forall2 (payload_sound signed_bounds_gamma)
    [(w5, sb_test_mul_choices); (w5, sb_test_const w5 3)] [(w5, x); (w5, 3)]).
  { constructor; [split; [reflexivity|split; assumption]|].
    constructor; [|constructor]. split; [reflexivity|]. split.
    - exact (wrap_is_word w5 3).
    - exact (pconst_sound (signed_bounds_word_laws signed_bounds_default_options) w5 3). }
  split.
  - exact (pforward_sound (signed_bounds_word_laws signed_bounds_default_options)
      bvmul _ _ w5 _ Hpayload (eval_op_fun2 bvmul w5 x 3 wmul eq_refl)).
  - exact (pforward_sound (signed_bounds_word_laws signed_bounds_classic_options)
      bvmul _ _ w5 _ Hpayload (eval_op_fun2 bvmul w5 x 3 wmul eq_refl)).
Qed.

Example sb_word_shared_backward_and_legacy_lattice :
  passume sb_test_legacy_precise = passume signed_bounds_classic_domain.
Proof.
  exact (signed_bounds_backward_values_agree
    (SignedBoundsOptions known_bits_default_options WidenJoin) signed_bounds_classic_options).
Qed.

Example sb_word_shared_legacy_static_fields :
  plat sb_test_legacy_precise = plat signed_bounds_classic_domain /\
  pmeet sb_test_legacy_precise = pmeet signed_bounds_classic_domain /\
  pconst sb_test_legacy_precise = pconst signed_bounds_classic_domain /\
  ptop sb_test_legacy_precise = ptop signed_bounds_classic_domain.
Proof.
  cbv beta iota zeta delta [sb_test_legacy_precise signed_bounds_classic_domain
    signed_bounds_word_domain signed_bounds_word_builder word_of_table
    signed_bounds_classic_options signed_bounds_default_options
    plat pmeet pmeet_c pconst pconst_c ptop sb_widening_choice].
  repeat split; reflexivity.
Qed.
