(** * Soundness of lattice tables

    Every outcome keeps a model of a lattice specification whose relations hold exactly of the
    derived rows and whose lattice values are merges of assigned values. Merging two such
    values gives another, by the merge laws of the values, so the model is closed under merge.
    A stored value of an outcome holds in the model, so it is a merge of assigned values. The
    theorem instantiates its own plan [LatticeModel] as [Model], which reads the head variables
    from the plan of the lowering.
    For example, a table of upper bounds stores only bounds that the clauses derive and their
    maximum.

    Builds on: the lattice signature, the runner facts, the lowering laws and its plan, and the
    run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig LatticeSig.

Import List.ListNotations.

Module LatticeModel (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (PS : LOWER_PLAN) <: LATTICE_MODEL_PLAN V I J D R X.
  (* STUB: the relations of the model hold of the derived rows, and its lattice values are the
     merges of assigned values. [PS.head_vars_bound] binds every head variable, so a clause
     whose body holds in the model derives or assigns its head. *)
  Lemma lattice_model : forall (s : spec V.t) rows,
    spec_ok s = true -> lattice_spec s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      (forall r xs, rel M r xs <->
        exists vs, xs = map inr vs /\ derived V.prim s (rows_in rows) r vs) /\
      (forall f m xs v, lookup_kind (tables s) f = Some (OLat m) -> lat M f xs v ->
        exists ks w ws, xs = map inr ks /\ assigned V.prim s (rows_in rows) f ks w /\
          Forall (assigned V.prim s (rows_in rows) f ks) ws /\ v = fold_left (V.merge m) ws w).
  Proof.
  Admitted. (* STUB *)
End LatticeModel.

Module LatticeSound (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PS : LOWER_PLAN) <: LATTICE_SOUND V I J D R X.
  Module Model := LatticeModel V I J D R X PS.

  Lemma solve_sound : forall (s : spec V.t) rows lim f m ks v,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) f (map Val ks) (Some (Val v)) ->
    exists w ws, assigned V.prim s (rows_in rows) f ks w /\
      Forall (assigned V.prim s (rows_in rows) f ks) ws /\ v = fold_left (V.merge m) ws w.
  Proof.
  Admitted. (* STUB *)
End LatticeSound.
