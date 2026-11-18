(** * Patterns and their values

    The query and the actions of patterns agree with the values of the patterns. The query of
    patterns with values matches when its fresh variables hold the values of the
    subpatterns, and a matched query gives the values back. A derivation, or a view that
    closes the rules, passes through the actions that build patterns with values.
    For example, the query of [POp q [PVar 1; PVal v]] is one primitive atom, and its result
    variable holds [q] applied to the value of variable 1 and to [v].

    Builds on: the lowering signature. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model RunSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerValues <: LOWER_VALUES.
  Lemma query_pats_fresh : forall {V} next (ps : list (pat V)),
    (next <= snd (query_pats next ps))%positive /\
    forall x, In x (flat_map atom_vars (fst (fst (query_pats next ps))) ++
        flat_map term_vars (snd (fst (query_pats next ps)))) ->
      In x (flat_map pat_vars ps) \/
      ((next <= x)%positive /\ (x < snd (query_pats next ps))%positive).
  Proof.
  Admitted. (* STUB *)

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

  Lemma build_pats_present : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) next ps e vs (s : @env V) rest,
    (pats_top ps < next)%positive -> pat_values prim e ps = Some vs ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    (forall s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) ->
      terms_value s' (snd (fst (build_pats next ps))) (map Val vs) ->
      present prim merge w s' rest) ->
    present prim merge w s (fst (fst (build_pats next ps)) ++ rest).
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
End LowerValues.
