(** * Patterns in models and in represented terms

    The query atoms of patterns hold in a model as the meanings of the patterns say, and the
    actions that build patterns hold in a model when the patterns have meanings. In a view, the
    actions that build patterns find cells that represent the terms of the patterns.
    For example, the query of [PNode f [PVar 1]] is one atom of the table [f], whose output
    variable then means [con M f] applied to the meaning of variable 1.

    Builds on: the lowering signature. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerModels <: LOWER_MODELS.
  Lemma query_pats_meaning : forall {V} (prim : positive -> list V -> option V)
      (M : @model V) ds next ps (s : model_env M) xs,
    forallb (pat_kinds ds) ps = true ->
    Forall (model_atom prim M (lookup_kind ds) s) (fst (fst (query_pats next ps))) ->
    Forall2 (model_term M s) (snd (fst (query_pats next ps))) xs ->
    pat_meanings prim M s ps = Some xs.
  Proof.
  Admitted. (* STUB *)

  Lemma build_pats_model : forall {V} (prim : positive -> list V -> option V)
      (M : @model V) ds next ps (s : model_env M) xs rest,
    (pats_top ps < next)%positive -> forallb (pat_kinds ds) ps = true ->
    pat_meanings prim M s ps = Some xs ->
    (forall s', (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) ->
      Forall2 (model_term M s') (snd (fst (build_pats next ps))) xs ->
      model_actions prim M (lookup_kind ds) s' rest) ->
    model_actions prim M (lookup_kind ds) s (fst (fst (build_pats next ps)) ++ rest).
  Proof.
  Admitted. (* STUB *)

  Lemma build_pats_represents : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) next ps e ts (s : @env V) rest,
    (pats_top ps < next)%positive -> (forall i, same w i i) ->
    pat_terms prim e ps = Some ts ->
    (forall x t, In x (flat_map pat_vars ps) -> e x = Some t ->
      exists c, s x = Some c /\ represents w c t) ->
    present prim merge w s (fst (fst (build_pats next ps)) ++ rest) ->
    exists s' cs, (forall x, (x < next)%positive \/ (snd (build_pats next ps) <= x)%positive ->
        s' x = s x) /\
      terms_value s' (snd (fst (build_pats next ps))) cs /\
      Forall2 (represents w) cs ts /\ present prim merge w s' rest.
  Proof.
  Admitted. (* STUB *)
End LowerModels.
