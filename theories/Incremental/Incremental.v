(** * Placeholder incremental solving

    Incremental states retain values between demands and edits.
    For example, an initial state has no stored values.
    Builds on: IncrementalSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig CheckSig PolicySig.
From Galois.Incremental Require Import RestrictSig IncrementalSig.

Import List.ListNotations.

Module IncrementalCode (L : WLATTICE_OPS) (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key)
    (R : RESTRICT_OPS L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK_OPS L S)
    <: INCREMENTAL_OPS L S RS R Sol Checker.
  Definition state := list (S.key * L.t).
  (* STUB-CODE *)
  Definition init : state := [].
  (* STUB-CODE *)
  Definition value (_ : state) (_ : S.key) : option L.t := None.
  (* STUB-CODE *)
  Definition demand (_ : S.prog) (_ : policy L.wparam) (_ : list S.key) (_ : N)
      (st : state) : demand_status * state := (DemandOutOfFuel, st).
  (* STUB-CODE *)
  Definition edit (_ _ : S.prog) (_ : list S.row) (st : state) : state := st.
End IncrementalCode.

Module Incremental (L : WLATTICE) (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L RS Sol) <: INCREMENTAL L S RS R Sol Checker Least.
  Include IncrementalCode L S RS R Sol Checker.
  Include INCREMENTAL_SPEC L S RS R Sol Checker.
  Lemma init_inv : forall p, inv p init /\ least_on p init.
  Proof. Admitted.

  Lemma demand_inv : forall p pol roots fuel st o st', inv p st ->
    demand p pol roots fuel st = (o, st') -> inv p st'.
  Proof. Admitted.

  Lemma demand_covers : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') -> forall x, In x roots -> dom st' x.
  Proof. Admitted.

  Lemma demand_noop : forall p pol roots fuel st,
    (forall x, In x roots -> dom st x) -> demand p pol roots fuel st = (Done, st).
  Proof. Admitted.

  Lemma demand_rejected : forall p pol roots fuel st why st',
    demand p pol roots fuel st = (DemandRejected why, st') -> st' = st.
  Proof. Admitted.

  Lemma edit_inv : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    inv p' (edit p p' ch st).
  Proof. Admitted.

  Lemma edit_keeps : forall p p' ch st x v,
    value (edit p p' ch st) x = Some v -> value st x = Some v.
  Proof. Admitted.

  Lemma demand_least : forall p pol roots fuel st o st', S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  Proof. Admitted.

  Lemma edit_least : forall p p' ch st, edit_covers p p' ch ->
    inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  Proof. Admitted.

  Lemma from_scratch_agrees : forall p st s x v, S.monotone p ->
    inv p st -> least_on p st -> least_solution p s -> value st x = Some v ->
    L.leb (s x) v = true /\ L.leb v (s x) = true.
  Proof. Admitted.

End Incremental.

Module IncrementalT (L : WLATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L RS Sol) <: INCREMENTAL_ALL L S RS R Sol Checker Least.
  Include Incremental L S RS R Sol Checker Least.
  TimeFun init.
  TimeFun value.
  TimeFun demand.
  TimeFun edit.
  Definition region (_ : S.prog) (_ : list S.key) (_ : state) : list S.row := [].
  Definition invalidated (_ : S.prog) (_ : list S.row) (_ : state) : list S.key := [].
  Definition frozen (_ : S.prog) (_ : list S.key) (_ : state) : list (S.key * L.t) := [].
  Definition infl_deg (_ : state) (_ : S.key) : nat := 0.
  Definition width (_ : S.prog) (_ : state) : nat := 0.
  Definition c_inc : nat := 1. (* STUB *)
  Lemma T_demand_le : forall p pol roots fuel st, inv p st ->
    T_demand p pol roots fuel st <=
      c_inc * (fold_right Nat.add 0
        (map (fun r => length (S.deps p r) + 1) (region p roots st)) +
        length roots + 1) * (width p st + 1) +
      Sol.c_solve * (Sol.work (R.mk p (frozen p roots st) (region p roots st)) pol +
        N.size_nat fuel + 1).
  Proof. Admitted. (* STUB *)

  Lemma T_edit_le : forall p p' ch st,
    T_edit p p' ch st <= c_inc *
      (fold_right Nat.add 0 (map (fun x => infl_deg st x + 1) (invalidated p' ch st)) +
       fold_right Nat.add 0 (map (fun r => length (S.deps p' r) + 1) ch) + 1) *
      (width p' st + 1).
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition discover (_ : S.prog) (_ : list S.key) (_ : state) : list S.key := [].
  TimeFun discover.
  (* STUB-CODE *)
  Definition invalidate (_ : S.prog) (_ : list S.row) (_ : state) : list S.key := [].
  TimeFun invalidate.
  (* STUB-CODE *)
  Definition merge_region (st : state) (_ : list S.key) (_ : kmap S.key L.t) : state := st.
  TimeFun merge_region.
  Lemma discover_closed : forall p roots st, inv p st ->
    closed p (fun x => dom st x \/ In x (discover p roots st)).
  Proof. Admitted. (* STUB *)

  Lemma region_closed : forall p roots st r x, inv p st ->
    In r (region p roots st) -> In x (S.writes p r ++ S.deps p r) ->
    dom st x \/ In x (discover p roots st).
  Proof. Admitted. (* STUB *)

  Lemma frame_post : forall p st s, inv p st ->
    (forall x, dom st x -> s x = look st x) ->
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  Proof. Admitted. (* STUB *)

  Lemma merge_inv : forall p roots st m, inv p st ->
    Checker.check_rows p (region p roots st) m = true ->
    (forall x, dom st x -> Checker.look m x = look st x) ->
    inv p (merge_region st (discover p roots st) m).
  Proof. Admitted. (* STUB *)

  Lemma demand_certificate : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') ->
    exists m, Checker.check_rows p (region p roots st) m = true.
  Proof. Admitted. (* STUB *)

  Lemma invalidate_closed : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    closed p' (fun x => dom st x /\ ~ In x (invalidate p' ch st)).
  Proof. Admitted. (* STUB *)

  Lemma edit_frame : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    post_on p' (edit p p' ch st).
  Proof. Admitted. (* STUB *)

  Lemma region_least_restricted : forall p pol roots fuel st m,
    S.wf p -> S.monotone p -> Least.widening_free pol -> inv p st -> least_on p st ->
    Sol.run (R.mk p (frozen p roots st) (region p roots st)) pol fuel = Solved m ->
    forall s, S.post_solution p s -> forall x,
      L.leb (look_or S.key_code L.bot m x) (s x) = true.
  Proof. Admitted. (* STUB *)

  Lemma region_least : forall p (E : S.key -> Prop) rs small global,
    S.wf p -> S.monotone p -> closed p E ->
    (forall r, In r rs <-> In r (S.rows p) /\ exists x, E x /\ In x (S.writes p r)) ->
    S.post_on p rs small ->
    (forall s, S.post_on p rs s -> S.below small s) ->
    least_solution p global ->
    forall x, E x -> L.leb (small x) (global x) = true /\
      L.leb (global x) (small x) = true.
  Proof. Admitted. (* STUB *)

End IncrementalT.
