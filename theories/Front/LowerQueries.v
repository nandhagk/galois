(** * Queries of patterns and their values

    The query of patterns agrees with the values of the patterns. It reads the variables of
    the patterns and fresh variables, it matches when its fresh variables hold the values of
    the subpatterns, and a matched query of patterns without constructors gives the values
    back.
    For example, the query of [POp q [PVar 1; PVal v]] is one primitive atom, and its result
    variable holds [q] applied to the value of variable 1 and to [v].

    Builds on: the lowering signature. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model RunSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerQueries <: LOWER_QUERIES.
  Lemma query_pats_fresh : forall {V} next (ps : list (pat V)),
    (next <= snd (query_pats next ps))%positive /\
    forall x, In x (flat_map atom_vars (fst (fst (query_pats next ps))) ++
        flat_map term_vars (snd (fst (query_pats next ps)))) ->
      In x (flat_map pat_vars ps) \/
      ((next <= x)%positive /\ (x < snd (query_pats next ps))%positive).
  Proof.
  Admitted. (* STUB *)

  Lemma query_pats_complete : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) next ps e vs (s : @env V),
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_pats next ps) <= x)%positive ->
        s' x = s x) /\
      matches prim w (fst (fst (query_pats next ps))) s' /\
      terms_value s' (snd (fst (query_pats next ps))) (map Val vs).
  Proof.
  Admitted. (* STUB *)

  Lemma query_pats_sound : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) next ps (s : @env V) vs,
    forallb pat_free ps = true ->
    matches prim w (fst (fst (query_pats next ps))) s ->
    terms_value s (snd (fst (query_pats next ps))) (map Val vs) ->
    pat_values prim (val_env s) ps = Some vs.
  Proof.
  Admitted. (* STUB *)
End LowerQueries.
