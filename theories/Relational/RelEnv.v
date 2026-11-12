(** * Relational and value-state composition

    Relational environments combine a numeric state with a value state.
    For example, a numeric range query can refine an interval value.
    Builds on: RelEnvSig, NumStateSig, StateSig and ValueSig. *)

From Stdlib Require Import NArith List.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Relational Require Import LinearizeSig NumStateSig RelEnvSig.

Module RelEnvCode (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (F : LINEARIZE_OPS X L) (R : NUM_STATE_OPS X L F) (E : STATE_DOMAIN_OPS X L V)
    (RR : REL_RANGE_REFINE_OPS L V)
    (P : LATTICE_OPS with Definition t := (R.t * E.t)%type)
    <: REL_ENV_OPS X L V F R E RR P.
  Definition t := (R.t * E.t)%type.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top : t := (R.top, E.top).
  Definition meet (a b : t) : t := (R.meet (fst a) (fst b), E.meet (snd a) (snd b)).
  Definition wparam := (R.wparam * E.wparam)%type.
  Definition widen (p : wparam) (a b : t) : t :=
    if is_bot b then a
    else (R.widen (fst p) (fst a) (fst b), E.widen (snd p) (snd a) (snd b)).
  Definition narrow (a b : t) : t :=
    (R.narrow (fst a) (fst b), E.narrow (snd a) (snd b)).
  Definition assign x e (s : t) : t := (R.assign x e (fst s), E.assign x e (snd s)).
  Definition havoc x (s : t) : t := (R.havoc x (fst s), E.havoc x (snd s)).
  Definition assume g es (s : t) : t := (R.assume g es (fst s), E.assume g es (snd s)).
  Definition eval e (s : t) : V.t :=
    let bounds := R.range e (fst s) in
    RR.refine_range (fst bounds) (snd bounds) (E.eval e (snd s)).
End RelEnvCode.
