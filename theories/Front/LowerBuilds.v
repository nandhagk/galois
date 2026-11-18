(** * Actions that build patterns, and their values

    The actions that build patterns agree with the values of the patterns. They read the
    variables of the patterns and bind distinct fresh variables. When they are present in a
    view, they compute the values of the patterns, and a derivation passes through them in both
    directions.
    For example, the actions that build [POp q [PVar 1]] are one [Let] of a fresh variable,
    which holds [q] applied to the value of variable 1 when the [Let] is present.

    Builds on: the lowering signature. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model RunSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerBuilds <: LOWER_BUILDS.
  Lemma build_pats_fresh : forall {V} next (ps : list (pat V)),
    (next <= snd (build_pats next ps))%positive /\
    (forall x, In x (flat_map term_vars (flat_map action_terms (fst (fst (build_pats next ps)))) ++
        flat_map term_vars (snd (fst (build_pats next ps)))) ->
      In x (flat_map pat_vars ps) \/
      ((next <= x)%positive /\ (x < snd (build_pats next ps))%positive)) /\
    (forall x, In x (flat_map action_binds (fst (fst (build_pats next ps)))) ->
      (next <= x)%positive /\ (x < snd (build_pats next ps))%positive) /\
    NoDup (flat_map action_binds (fst (fst (build_pats next ps)))).
  Proof.
  Admitted. (* STUB *)

  Lemma build_pats_present_sound : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) next ps e vs (s : @env V) rest,
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    present prim merge w s (fst (fst (build_pats next ps)) ++ rest) ->
    exists s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) /\
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) /\
      present prim merge w s' rest.
  Proof.
  Admitted. (* STUB *)

  Lemma build_pats_derivation : forall {V} (prim : positive -> list V -> option V)
      next ps e vs (s : @env V) rest f k,
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    (forall s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) ->
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) ->
      derivation_action prim s' rest f k) ->
    derivation_action prim s (fst (fst (build_pats next ps)) ++ rest) f k.
  Proof.
  Admitted. (* STUB *)

  Lemma build_pats_derivation_sound : forall {V} (prim : positive -> list V -> option V)
      next ps (s : @env V) rest f k,
    (pats_top ps < next)%positive ->
    (forall x, In x (flat_map pat_vars ps) -> exists v, s x = Some (Val v)) ->
    derivation_action prim s (fst (fst (build_pats next ps)) ++ rest) f k ->
    exists s' vs, (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) /\
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) /\
      pat_values prim (val_env s') ps = Some vs /\ derivation_action prim s' rest f k.
  Proof.
  Admitted. (* STUB *)
End LowerBuilds.
