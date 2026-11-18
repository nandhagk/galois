(** * Lattice tables

    A lattice table keeps, for each key, the merge of the values that the clauses assign to
    it. In every outcome a stored value is the merge of finitely many assigned values
    ([solve_sound]), and in a saturated outcome every assigned value is below the stored value
    ([solve_complete]). The merge laws of the values make the merge independent of the order.
    A lattice specification has no constructor table, so its program builds no term, and its
    clauses read relations and primitives and derive rows or assign values.
    For example, a table of upper bounds with [Z.max] as its merge keeps the largest bound
    that the clauses derive.

    Main results
    - [solve_sound] In every outcome a stored value of a lattice table is the merge of assigned
      values.
    - [solve_complete] In a saturated outcome every assigned value is below the stored value.

    Builds on: the specifications, their lowering, the runner and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig.

Import List.ListNotations.

(** A lattice specification. No table is a constructor table, every clause reads only rows and
    primitives, and every head derives a row or assigns a value. With the kind check of
    [spec_ok], no pattern is a constructor application, so the lowered program has no
    identifier. *)
Definition lattice_spec {V} (s : spec V) : bool :=
  forallb (fun d => match out d with OId => false | _ => true end) (tables s) &&
  forallb (fun c =>
    forallb (fun p => match p with Equals _ _ _ => false | _ => true end) (body c) &&
    match head c with
    | Derive _ _ | Assign _ _ _ => true
    | _ => false
    end) (clauses s).

(** * Theorems *)

(** Soundness of lattice tables. *)
Module Type LATTICE_SOUND (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In every outcome a stored value of a lattice table is the merge of assigned values. *)
  Parameter solve_sound : forall (s : spec V.t) rows lim f m ks v,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) f (map Val ks) (Some (Val v)) ->
    exists w ws, assigned V.prim s (rows_in rows) f ks w /\
      Forall (assigned V.prim s (rows_in rows) f ks) ws /\ v = fold_left (V.merge m) ws w.
End LATTICE_SOUND.

(** Completeness of lattice tables. *)
Module Type LATTICE_COMPLETE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In a saturated outcome every assigned value is below the stored value. *)
  Parameter solve_complete : forall (s : spec V.t) rows lim db f m ks w,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    assigned V.prim s (rows_in rows) f ks w ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\ V.merge m w v = v.
End LATTICE_COMPLETE.

Module Type LATTICE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) :=
  LATTICE_SOUND V I J D R X <+ LATTICE_COMPLETE V I J D R X.

(** * Proof plan *)

(** The model of derived rows and merged assigned values. *)
Module Type LATTICE_MODEL_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** A lattice specification has a model of its input rows whose relations hold exactly of
      the derived rows, and whose lattice values are merges of assigned values. *)
  Parameter lattice_model : forall (s : spec V.t) rows,
    spec_ok s = true -> lattice_spec s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      (forall r xs, rel M r xs <->
        exists vs, xs = map inr vs /\ derived V.prim s (rows_in rows) r vs) /\
      (forall f m xs v, lookup_kind (tables s) f = Some (OLat m) -> lat M f xs v ->
        exists ks w ws, xs = map inr ks /\ assigned V.prim s (rows_in rows) f ks w /\
          Forall (assigned V.prim s (rows_in rows) f ks) ws /\ v = fold_left (V.merge m) ws w).
End LATTICE_MODEL_PLAN.

(** Assigned values in a closed view. *)
Module Type LATTICE_ASSIGN_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** A view that the rules of a specification close, with the kinds of its tables and no
      output in its relation rows, stores at each assigned key a value above each value that
      the clauses assign there. *)
  Parameter lower_assigned : forall (s : spec V.t) (w : @view V.t) f ks v,
    spec_ok s = true -> closed V.prim V.merge (spec_program s) w ->
    (forall g, kind w g = lookup_kind (tables s) g) ->
    (forall g k o, row w g k o -> lookup_kind (tables s) g = Some ORel -> o = None) ->
    assigned V.prim s (view_rows w) f ks v ->
    exists m v', lookup_kind (tables s) f = Some (OLat m) /\
      row w f (map Val ks) (Some (Val v')) /\ V.merge m v v' = v'.
End LATTICE_ASSIGN_PLAN.
