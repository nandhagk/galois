(** * Queries of bodies whose reads see the stored values

    The query of a body whose premises hold in a view matches, when each read of a lattice
    table sees the value that the view stores. A read [Equals f args v] gives the query atoms of
    its arguments and of its value, then the function atom [Fun f ts (Some t)], which matches
    the stored row. The definitions that the body gives its equations compute their values when
    they are present. These are the laws [query_body_matches] and [query_body_lets] of the
    lowering, with reads as well as rows.

    For example, the body [Equals dist [PVar 1; PVar 2] (PVar 4); Holds edge [PVar 2; PVar 3;
    PVar 5]] has the query [dist(1, 2) = 4, edge(2, 3, 5)], which matches where the view stores
    the distance [4] at [[1; 2]].

    Builds on: the lattice-read signature and the pattern laws of the lowering. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig LatticeReadSig.

Import List.ListNotations.

Module LatticeReadQueries (PV : LOWER_VALUES) <: LATTICE_READ_QUERY_PLAN.
  (* STUB: induction on the premises, as for [query_body_matches]. A read uses
     [PV.query_pats_complete] for its arguments and for [[v]], and its function atom matches the
     stored row. *)
  Lemma query_body_stored_matches : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) bound next ps e (s : @env V),
    (body_top ps < next)%positive ->
    Forall (premise_lat_in prim (view_rows w) (stored_at w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\
      matches prim w (fst (fst (query_body bound next ps))) s'.
  Proof.
  Admitted. (* STUB *)

  (* STUB: induction on the premises, as for [query_body_lets]. A read gives no definition. *)
  Lemma query_body_stored_lets : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) bound next ps e (s : @env V) rest,
    (body_top ps < next)%positive ->
    Forall (premise_lat_in prim (view_rows w) (stored_at w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    present prim merge w s (snd (fst (query_body bound next ps)) ++ rest) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\ present prim merge w s' rest.
  Proof.
  Admitted. (* STUB *)
End LatticeReadQueries.
