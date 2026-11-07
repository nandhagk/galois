(** * Concretisation automation

    The tactic uses registered semantic facts and leaves unsupported premises visible.
    For example, a known operand relation and evaluation equation close a transfer goal.
    Builds on: DomainsValue and LatticeTactics. *)

From Stdlib Require Import List Lia.
From Galois.Lattice Require Import LatticeConcrete LatticeTactics.
From Galois.Domains Require Import DomainsValue.

#[export] Hint Resolve Forall2_nil Forall2_cons : galois_gamma.

(** Semantic search uses a fixed depth and simplifies conjunctions before leaving side goals. *)
Ltac gamma_solver :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  end;
  try solve [eauto 6 with galois_gamma];
  repeat match goal with
  | H : value_laws ?D ?M ?gam |- gamma ?gam (ValueAbs.op ?D ?k ?xs) ?c =>
    eapply (op_sound H k xs)
  | H : value_laws ?D ?M ?gam |- Forall2 (gamma ?gam) (ValueAbs.back ?D ?k ?a ?xs) ?cs =>
    eapply (back_sound H k a xs cs)
  | H : value_laws ?D ?M ?gam |- Forall2 (gamma ?gam) (ValueAbs.guard ?D ?g ?xs) ?cs =>
    eapply (guard_sound H g xs cs)
  end;
  try order_solver;
  try lia.
