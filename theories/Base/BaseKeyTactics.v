(** * Key and round-trip tactics

    These tactics expose equality cases and solve structural decoder round trips.
    For example, [case_key] replaces an encoded boolean test by a key equality case.
    Builds on: BaseEncoding and BaseEq. *)

From Stdlib Require Import Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq.

(** Split one key test in the goal or context using a matching injectivity law.
    Both branches retain a key equality or disequality and rewrite every matching test. *)
Ltac case_key :=
  match goal with
  | HE : encoding_laws ?E |- _ =>
    let split_test a b :=
      let Htest := fresh "Hkey_test" in
      let Hkey := fresh "Hkey" in
      destruct (eqb E a b) eqn:Htest;
      [ pose proof (proj1 (eqb_true_iff E HE a b) Htest) as Hkey
      | pose proof (proj1 (eqb_false_iff E HE a b) Htest) as Hkey ];
      try rewrite Htest in *;
      try rewrite <- (eqb_equation E a b) in *;
      try rewrite Htest in * in
    first
      [ match goal with
        | |- context [eqb E ?a ?b] => split_test a b
        | H : context [eqb E ?a ?b] |- _ => split_test a b
        end
      | match goal with
        | |- context [Pos.eqb (encode E ?a) (encode E ?b)] => split_test a b
        | H : context [Pos.eqb (encode E ?a) (encode E ?b)] |- _ => split_test a b
        end ]
  end.

(** Induct on the round-trip input, reduce constructor matches and rewrite recursive
    and explicitly supplied decoder round trips. Unrelated equalities stay untouched. *)
Ltac solve_roundtrip :=
  intros;
  match goal with
  | |- _ = Some ?x => induction x
  end;
  autorewrite with galois_cost;
  cbn;
  repeat match goal with
  | H : codec_laws ?C |-
      context [decode ?C (Cost.value (encode_c (codec_enc ?C) ?x))] =>
    let Hrt := fresh "Hroundtrip" in
    pose proof (decode_encode H x) as Hrt;
    unfold encode in Hrt; rewrite Hrt; clear Hrt; cbn
  | H : codec_laws ?C |- context [decode ?C (encode (codec_enc ?C) ?x)] =>
    rewrite (decode_encode H x); cbn
  | H : forall x, ?f (?g x) = Some x |- context [?f (?g ?y)] => progress rewrite (H y)
  | H : ?f (Cost.value (?g ?x)) = Some ?x |-
      context [?f (Cost.value (?g ?x))] => progress rewrite H
  | H : ?f (?g ?x) = Some ?x |- context [?f (?g ?x)] => progress rewrite H
  end;
  try reflexivity.
