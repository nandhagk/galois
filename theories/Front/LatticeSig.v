(** * Lattice tables

    A lattice table keeps, for each key, the merge of the values that the clauses assign to
    it. In every outcome a stored value is the merge of finitely many assigned values
    ([solve_sound]), and in a saturated outcome every assigned value is below the stored value
    ([solve_complete]). The merge laws of the values make the merge independent of the order.
    For example, a table of upper bounds with [Z.max] as its merge keeps the largest bound
    that the clauses derive.

    Builds on: the specifications, the runner and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig.

Import List.ListNotations.

(** A lattice specification: every clause reads only rows and primitives and derives a row or
    assigns a value, and its lowered program has no identifier. *)
Definition lattice_spec {V} (s : spec V) : bool :=
  forallb (fun c =>
    forallb (fun p => match p with Equals _ _ _ => false | _ => true end) (body c) &&
    match head c with
    | Derive _ _ | Assign _ _ _ => true
    | _ => false
    end) (clauses s).

Module Type LATTICE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In every outcome a stored value of a lattice table is the merge of assigned values. *)
  Parameter solve_sound : forall (s : spec V.t) rows lim f m ks v,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) f (map Val ks) (Some (Val v)) ->
    exists w ws, assigned V.prim s (rows_in rows) f ks w /\
      Forall (assigned V.prim s (rows_in rows) f ks) ws /\ v = fold_left (V.merge m) ws w.
  (** In a saturated outcome every assigned value is below the stored value. *)
  Parameter solve_complete : forall (s : spec V.t) rows lim db f m ks w,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    assigned V.prim s (rows_in rows) f ks w ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\ V.merge m w v = v.
End LATTICE.
