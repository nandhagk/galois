(** * Queries and definitions of bodies

    The query of a body whose premises hold in the value rows of a view matches, with fresh
    variables from the first fresh variable of its clause on. The definitions that a body
    gives its equations compute the values of the premises when they are present, and the
    checks that a rule puts after its table atoms do not change what its query matches.
    For example, the body [Holds edge [PVar 1; PVar 2]; Computes succ [PVar 2] (PVar 3)], where
    no table atom binds variable 3, has one query atom and one [Let] of variable 3.

    Builds on: the lowering signature and the facts of the specifications. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig.

Import List.ListNotations.

Module LowerBodies <: LOWER_BODY.
  Lemma query_body_matches : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) bound next ps e (s : @env V),
    (body_top ps < next)%positive -> Forall (premise_in prim (view_rows w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\
      matches prim w (fst (fst (query_body bound next ps))) s'.
  Proof.
  Admitted. (* STUB *)

  Lemma query_body_lets : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) bound next ps e (s : @env V) rest,
    (body_top ps < next)%positive -> Forall (premise_in prim (view_rows w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    present prim merge w s (snd (fst (query_body bound next ps)) ++ rest) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\ present prim merge w s' rest.
  Proof.
  Admitted. (* STUB *)

  Lemma checks_last_matches : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) q (s : @env V),
    matches prim w (checks_last q) s <-> matches prim w q s.
  Proof.
  Admitted. (* STUB *)
End LowerBodies.
