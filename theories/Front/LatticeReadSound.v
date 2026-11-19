(** * Soundness of lattice tables that clauses read

    Every outcome keeps a model of a specification that reads lattice tables, whose relations
    hold only of derived rows and whose lattice values are merges of assigned values. The model
    is closed under the merges by the constructor [lat_merged_merge], and a read in a premise
    sees a lattice value of the model, which is a merge. A stored value of an outcome holds in
    the model, so it is a merge of assigned values, and a stored row is derived. The theorems
    instantiate their own plan [LatticeReadModel] as [Model], which reads the head variables
    from the plan of the lowering.

    For example, a table of shortest distances stores only lengths of paths and their minima.

    Builds on: the lattice-read signature, the runner facts, the lowering laws and its plan,
    and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig LatticeReadSig.

Import List.ListNotations.

Module LatticeReadModel (V : VALUE) (PS : LOWER_PLAN) <: LATTICE_READ_MODEL_PLAN V.
  (* STUB: the carrier is [unit], [rel r xs] says [xs = map inr vs] for a derived row [r vs],
     and [lat f xs v] says [xs = map inr ks] for a merge [v] at [ks]. A premise that holds in
     the model holds in [lat_body] by [lat_body_intro], and [PS.head_vars_bound] gives every
     head variable a value. [lat_merged_merge] closes the model under the merges. *)
  Lemma read_model : forall (s : spec V.t) rows,
    spec_ok s = true -> lattice_reads s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      (forall r xs, rel M r xs ->
        exists vs, xs = map inr vs /\ lat_derived V.prim V.merge s (rows_in rows) r vs) /\
      (forall f xs v, lat M f xs v ->
        exists ks, xs = map inr ks /\ lat_merged V.prim V.merge s (rows_in rows) f ks v).
  Proof.
  Admitted. (* STUB *)
End LatticeReadModel.

Module LatticeReadSound (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PS : LOWER_PLAN) <: LATTICE_READ_SOUND V I J D R X.
  Module Model := LatticeReadModel V PS.

  Lemma solve_sound : forall (s : spec V.t) rows lim f ks v,
    spec_ok s = true -> lattice_reads s = true -> rows_ok s rows = true ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) f (map Val ks) (Some (Val v)) ->
    lat_merged V.prim V.merge s (rows_in rows) f ks v.
  Proof.
  Admitted. (* STUB *)

  Lemma solve_rows_sound : forall (s : spec V.t) rows lim r vs,
    spec_ok s = true -> lattice_reads s = true -> rows_ok s rows = true ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) r (map Val vs) None ->
    lat_derived V.prim V.merge s (rows_in rows) r vs.
  Proof.
  Admitted. (* STUB *)
End LatticeReadSound.
