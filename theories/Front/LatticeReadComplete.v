(** * Completeness of lattice tables that clauses read

    A saturated outcome is closed under the rules, keeps the input rows and is well formed, so
    its view is functional and holds the kinds of the tables. The plan [LATTICE_READ_CLOSED_PLAN]
    then says that the view holds every derived row of its own rows and stores a value above
    each assigned value. The meaning grows with the input rows ([lat_mono]), so the view holds the
    derived rows and the assigned values of the input rows of the solve.

    For example, a saturated run of shortest paths stores at each pair of nodes a distance at
    most the length of each path between them.

    Builds on: the lattice-read signature and its plan, the runner facts, the meaning of lattice
    reads and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig LatticeReadSig.

Import List.ListNotations.

Module LatticeReadComplete (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X)
    (CL : LATTICE_READ_CLOSED_PLAN V) <: LATTICE_READ_COMPLETE V I J D R X.
  (* STUB: [X.solve_unfold], [R.run_closed] and [R.run_wf] give a closed, well-formed and loaded
     outcome. The load gives the kinds, and [view_sorted] gives no output in relation rows.
     [D.row_functional] makes the view functional, and [F.solve_keeps] with [lat_mono] moves the
     assigned value to the rows of the outcome. [CL.lower_reads_closed] then gives the stored
     value, and the kind of the table fixes its merge. *)
  Lemma solve_complete : forall (s : spec V.t) rows lim db f m ks w,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s -> lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    lat_assigned V.prim V.merge s (rows_in rows) f ks w ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\ V.merge m w v = v.
  Proof.
  Admitted. (* STUB *)

  (* STUB: as [solve_complete], with the first half of [CL.lower_reads_closed]. *)
  Lemma solve_rows_complete : forall (s : spec V.t) rows lim db r vs,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    lat_derived V.prim V.merge s (rows_in rows) r vs ->
    row (D.view db) r (map Val vs) None.
  Proof.
  Admitted. (* STUB *)
End LatticeReadComplete.
