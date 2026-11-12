(** * Incremental solving of dependency-closed regions

    Incremental states retain checked values and invalidate the influence closure of edits.
    For example, demanding one root discovers its contributors and their dependencies.
    Builds on: SystemSig, SolverSig, CheckSig, PolicySig and RestrictSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig CheckSig PolicySig.
From Galois.Incremental Require Import RestrictSig.

Import List.ListNotations.

Inductive demand_status :=
  | Done
  | DemandOutOfFuel
  | DemandRejected (why : reason).

Module Type INCREMENTAL_OPS (L : WLATTICE_OPS) (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key)
    (R : RESTRICT_OPS L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK_OPS L S).
  Parameter state : Type.
  Parameter init : state.
  Parameter value : state -> S.key -> option L.t.
  Parameter demand : S.prog -> policy L.wparam -> list S.key -> N -> state ->
    demand_status * state.
  Parameter edit : S.prog -> S.prog -> list S.row -> state -> state.
End INCREMENTAL_OPS.

Module Type INCREMENTAL_SPEC (L : WLATTICE) (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (R : RESTRICT_OPS L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK_OPS L S)
    (Import X : INCREMENTAL_OPS L S RS R Sol Checker).
  Definition dom (st : state) (x : S.key) : Prop := exists v, value st x = Some v.
  Definition look (st : state) (x : S.key) : L.t :=
    match value st x with
    | None => L.bot
    | Some v => v
    end.
  (** A region contains every write and read of any row that writes into the region. *)
  Definition closed (p : S.prog) (D : S.key -> Prop) : Prop :=
    forall r y x, In r (S.rows p) -> In y (S.writes p r) -> D y ->
      In x (S.writes p r ++ S.deps p r) -> D x.
  Definition post_on (p : S.prog) (st : state) : Prop :=
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_ok L.leb (look st) (S.target p r) (S.eval p r (look st)) = true.
  Definition inv (p : S.prog) (st : state) : Prop :=
    closed p (dom st) /\ post_on p st.
  Definition least_on (p : S.prog) (st : state) : Prop :=
    forall s, S.post_solution p s ->
    forall x v, value st x = Some v -> L.leb v (s x) = true.
  Definition least_solution (p : S.prog) (s : S.key -> L.t) : Prop :=
    S.post_solution p s /\ forall u, S.post_solution p u -> S.below s u.
  Definition edit_covers (p p' : S.prog) (ch : list S.row) : Prop :=
    forall r, ~ In r ch ->
      (In r (S.rows p) <-> In r (S.rows p')) /\
      (In r (S.rows p) -> S.target p r = S.target p' r /\
        S.deps p r = S.deps p' r /\
        forall look, S.eval p r look = S.eval p' r look).
End INCREMENTAL_SPEC.

Module Type INCREMENTAL_LAWS (L : WLATTICE) (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L RS Sol)
    (Import X : INCREMENTAL_OPS L S RS R Sol Checker)
    (Import XS : INCREMENTAL_SPEC L S RS R Sol Checker X).
  (** The empty state is sound and below all post-solutions. *)
  Parameter init_inv : forall p, inv p init /\ least_on p init.
  (** Demand returns a sound state for every outcome. *)
  Parameter demand_inv : forall p pol roots fuel st o st', inv p st ->
    demand p pol roots fuel st = (o, st') -> inv p st'.
  (** Completed demand covers every requested root. *)
  Parameter demand_covers : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') -> forall x, In x roots -> dom st' x.
  (** A demand already covered by the domain leaves the state unchanged. *)
  Parameter demand_noop : forall p pol roots fuel st,
    (forall x, In x roots -> dom st x) -> demand p pol roots fuel st = (Done, st).
  (** Rejected demand leaves the previously checked state unchanged. *)
  Parameter demand_rejected : forall p pol roots fuel st why st',
    demand p pol roots fuel st = (DemandRejected why, st') -> st' = st.
  (** Covered edits keep a sound state after invalidation. *)
  Parameter edit_inv : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    inv p' (edit p p' ch st).
  (** Invalidation retains old values verbatim. *)
  Parameter edit_keeps : forall p p' ch st x v,
    value (edit p p' ch st) x = Some v -> value st x = Some v.
  (** Widening-free demand keeps every stored value below all post-solutions. *)
  Parameter demand_least : forall p pol roots fuel st o st', S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  (** Covered edits keep the least-value property on the retained domain. *)
  Parameter edit_least : forall p p' ch st, edit_covers p p' ch ->
    inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  (** Stored least values agree in both lattice directions with a global least solution. *)
  Parameter from_scratch_agrees : forall p st s x v, S.monotone p ->
    inv p st -> least_on p st -> least_solution p s -> value st x = Some v ->
    L.leb (s x) v = true /\ L.leb v (s x) = true.
End INCREMENTAL_LAWS.

Module Type INCREMENTAL (L : WLATTICE) (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L RS Sol) :=
  INCREMENTAL_OPS L S RS R Sol Checker <+
  INCREMENTAL_SPEC L S RS R Sol Checker <+
  INCREMENTAL_LAWS L S RS R Sol Checker Least.

Module Type INCREMENTAL_TIME (L : WLATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L RS Sol)
    (Import X : INCREMENTAL L S RS R Sol Checker Least).
  (* spec: region invalidated frozen infl_deg width *)
  Parameter region : S.prog -> list S.key -> state -> list S.row.
  Parameter invalidated : S.prog -> list S.row -> state -> list S.key.
  Parameter frozen : S.prog -> list S.key -> state -> list (S.key * L.t).
  Parameter infl_deg : state -> S.key -> nat.
  Parameter width : S.prog -> state -> nat.
  Parameter T_init : nat.
  Parameter T_value : state -> S.key -> nat.
  Parameter T_demand : S.prog -> policy L.wparam -> list S.key -> N -> state -> nat.
  Parameter T_edit : S.prog -> S.prog -> list S.row -> state -> nat.
  Parameter c_inc : nat.
  (** Demand pays for discovery and the restricted solver including fuel bits. *)
  Parameter T_demand_le : forall p pol roots fuel st, inv p st ->
    T_demand p pol roots fuel st <=
      c_inc * (fold_right Nat.add 0
        (map (fun r => length (S.deps p r) + 1) (region p roots st)) +
        length roots + 1) * (width p st + 1) +
      Sol.c_solve * (Sol.work (R.mk p (frozen p roots st) (region p roots st)) pol +
        N.size_nat fuel + 1).
  (** Editing pays for invalidated influence edges and changed dependencies. *)
  Parameter T_edit_le : forall p p' ch st,
    T_edit p p' ch st <= c_inc *
      (fold_right Nat.add 0 (map (fun x => infl_deg st x + 1) (invalidated p' ch st)) +
       fold_right Nat.add 0 (map (fun r => length (S.deps p' r) + 1) ch) + 1) *
      (width p' st + 1).
End INCREMENTAL_TIME.

Module Type INCREMENTAL_T (L : WLATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L RS Sol) :=
  INCREMENTAL L S RS R Sol Checker Least <+
  INCREMENTAL_TIME L S RS R Sol Checker Least.

Module Type INCREMENTAL_PLAN (L : WLATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L RS Sol)
    (Import X : INCREMENTAL_T L S RS R Sol Checker Least).
  Parameter discover : S.prog -> list S.key -> state -> list S.key.
  Parameter invalidate : S.prog -> list S.row -> state -> list S.key.
  Parameter merge_region : state -> list S.key -> kmap S.key L.t -> state.
  Parameter T_discover : S.prog -> list S.key -> state -> nat.
  Parameter T_invalidate : S.prog -> list S.row -> state -> nat.
  Parameter T_merge_region : state -> list S.key -> kmap S.key L.t -> nat.
  (** Discovery extends the old domain to a closed domain. *)
  Parameter discover_closed : forall p roots st, inv p st ->
    closed p (fun x => dom st x \/ In x (discover p roots st)).
  (** Every discovered row has all its writes and reads in the extended domain. *)
  Parameter region_closed : forall p roots st r x, inv p st ->
    In r (region p roots st) -> In x (S.writes p r ++ S.deps p r) ->
    dom st x \/ In x (discover p roots st).
  (** Old rows keep their post-solution property when the old domain agrees. *)
  Parameter frame_post : forall p st s, inv p st ->
    (forall x, dom st x -> s x = look st x) ->
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  (** Accepted regional certificates combine with the old frame to give a sound state. *)
  Parameter merge_inv : forall p roots st m, inv p st ->
    Checker.check_rows p (region p roots st) m = true ->
    (forall x, dom st x -> Checker.look m x = look st x) ->
    inv p (merge_region st (discover p roots st) m).
  (** Completed demand has an accepted certificate for the discovered rows. *)
  Parameter demand_certificate : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') ->
    exists m, Checker.check_rows p (region p roots st) m = true.
  (** Removing the forward influence closure keeps a closed domain. *)
  Parameter invalidate_closed : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    closed p' (fun x => dom st x /\ ~ In x (invalidate p' ch st)).
  (** Unchanged rows writing into the retained domain keep their accepted contributions. *)
  Parameter edit_frame : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    post_on p' (edit p p' ch st).
  (** Restricted least solving and frozen least seeds give regional least values. *)
  (* SIG-QUESTION: RESTRICT does not yet connect restricted monotonicity or key codes
     to the original system. Frozen seeds and selected rows also need their discovery
     correspondence before SOLVER_LEAST.run_least establishes this unchanged claim. *)
  Parameter region_least_restricted : forall p pol roots fuel st m,
    S.wf p -> S.monotone p -> Least.widening_free pol -> inv p st -> least_on p st ->
    Sol.run (R.mk p (frozen p roots st) (region p roots st)) pol fuel = Solved m ->
    forall s, S.post_solution p s -> forall x,
      L.leb (look_or S.key_code L.bot m x) (s x) = true.
  (** A closed restricted least solution agrees with a global least solution on its region. *)
  (* Source statement in FixpointLocalLeast.v at 87192fe, under its Agreement context.
     Theorem region_least x :
       FinSet.mem EX x E = true -> leb L (small x) (global x) = true /\
         leb L (global x) (small x) = true.
     The declaration below makes the closed-region and least-solution context explicit. *)
  Parameter region_least : forall p (E : S.key -> Prop) rs small global,
    S.wf p -> S.monotone p -> closed p E ->
    (forall r, In r rs <-> In r (S.rows p) /\ exists x, E x /\ In x (S.writes p r)) ->
    S.post_on p rs small ->
    (forall s, S.post_on p rs s -> S.below small s) ->
    least_solution p global ->
    forall x, E x -> L.leb (small x) (global x) = true /\
      L.leb (global x) (small x) = true.
End INCREMENTAL_PLAN.

Module Type INCREMENTAL_ALL (L : WLATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L RS Sol) :=
  INCREMENTAL_T L S RS R Sol Checker Least <+
  INCREMENTAL_PLAN L S RS R Sol Checker Least.
