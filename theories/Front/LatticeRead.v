(** * Lattice tables that clauses read, proved

    The theorems of lattice tables that clauses read, assembled from the files that prove their
    parts. [LatticeReadSound.v] proves that stored values and rows are sound,
    [LatticeReadQueries.v], [LatticeReadRaise.v] and [LatticeReadClosed.v] prove that a closed
    view holds the meaning, and [LatticeReadComplete.v] proves completeness at saturation. This
    file derives exactness and the condition for saturation from soundness and completeness.

    For example, [LatticeRead] applied to a runner of shortest paths says that a saturated run
    stores at each pair of nodes the length of a shortest path.

    Main results
    - [solve_exact] In a saturated outcome of a monotone specification the stored value is a
      merge of assigned values that is above every assigned value.
    - [unbounded_unsaturated] No run of a monotone specification saturates when the assigned
      values at a key have no merge above all of them.

    Builds on: the lattice-read signature and the files of its parts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig LatticeReadSig
  LatticeReadSound LatticeReadQueries LatticeReadRaise LatticeReadClosed LatticeReadComplete.

Import List.ListNotations.

Module LatticeRead (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PS : LOWER_PLAN) <: LATTICE_READ V I J D R X.
  Module Queries := LatticeReadQueries LW.
  Module Closed := LatticeReadClosed V LW Queries LatticeReadRaise.
  Module SoundLaws := LatticeReadSound V I J D R X F LW PS.
  Module CompleteLaws := LatticeReadComplete V I J D R X F Closed.
  Include SoundLaws.
  Include CompleteLaws.

  (** The outcome of a solve of a specification that passes its checks is well formed. *)
  Lemma solve_wf : forall (s : spec V.t) rows lim,
    spec_ok s = true -> rows_ok s rows = true -> D.wf (snd (X.solve (spec_program s) rows lim)).
  Proof.
    intros s rows lim Hok Hrows.
    rewrite X.solve_unfold.
    destruct (F.seed_ready s rows Hok Hrows) as [Hwf [_ [Hloaded _]]].
    exact (proj1 (R.run_wf _ _ lim _ (F.plan_ok s Hok) Hwf Hloaded)).
  Qed.

  (** In a saturated outcome of a monotone specification, the value stored at a key with an
      assigned value is a merge of assigned values that is above every assigned value. *)
  Lemma solve_exact : forall (s : spec V.t) rows lim db f m ks w0,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s -> lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    lat_assigned V.prim V.merge s (rows_in rows) f ks w0 ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\
      lat_merged V.prim V.merge s (rows_in rows) f ks v /\
      forall w, lat_assigned V.prim V.merge s (rows_in rows) f ks w -> V.merge m w v = v.
  Proof.
    intros s rows lim db f m ks w0 Hok Hlat Hreads Hrows Hmono Hkind Hsolve Hw0.
    assert (Hwf : D.wf db).
    { pose proof (solve_wf s rows lim Hok Hrows) as Hwf. rewrite Hsolve in Hwf. exact Hwf. }
    destruct (solve_complete s rows lim db f m ks w0 Hok Hlat Hreads Hrows Hmono Hkind Hsolve
      Hw0) as [v [Hrow _]].
    exists v.
    split; [exact Hrow |].
    split.
    - apply (solve_sound s rows lim f ks v Hok Hlat Hrows).
      rewrite Hsolve.
      exact Hrow.
    - intros w Hw.
      destruct (solve_complete s rows lim db f m ks w Hok Hlat Hreads Hrows Hmono Hkind Hsolve
        Hw) as [v' [Hrow' Hle]].
      pose proof (D.row_functional db f (map Val ks) _ _ Hwf Hrow Hrow') as Hsame.
      injection Hsame as Hv.
      subst v'.
      exact Hle.
  Qed.

  (** No run of a monotone specification saturates when a key has an assigned value and every
      merge of assigned values there lies below some other assigned value. *)
  Lemma unbounded_unsaturated : forall (s : spec V.t) rows lim f m ks w0,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s -> lookup_kind (tables s) f = Some (OLat m) ->
    lat_assigned V.prim V.merge s (rows_in rows) f ks w0 ->
    (forall v, lat_merged V.prim V.merge s (rows_in rows) f ks v ->
      exists w, lat_assigned V.prim V.merge s (rows_in rows) f ks w /\ V.merge m w v <> v) ->
    fst (X.solve (spec_program s) rows lim) <> Saturated.
  Proof.
    intros s rows lim f m ks w0 Hok Hlat Hreads Hrows Hmono Hkind Hw0 Hunbounded Hsat.
    destruct (X.solve (spec_program s) rows lim) as [st db] eqn:Hsolve.
    cbn in Hsat. subst st.
    destruct (solve_exact s rows lim db f m ks w0 Hok Hlat Hreads Hrows Hmono Hkind Hsolve Hw0)
      as [v [_ [Hmerged Habove]]].
    destruct (Hunbounded v Hmerged) as [w [Hw Hnot]].
    exact (Hnot (Habove w Hw)).
  Qed.
End LatticeRead.
