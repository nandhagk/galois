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

(** Rows with one primary target share their recorded write occurrences. *)
Record incremental_snapshot (K : Type) := {
  snapshot_owner : K;
  snapshot_writes : list K;
  snapshot_live : bool
}.

Arguments snapshot_owner {K}.
Arguments snapshot_writes {K}.
Arguments snapshot_live {K}.

TimeFun snapshot_owner.
TimeFun snapshot_writes.
TimeFun snapshot_live.

Inductive demand_status :=
  | Done
  | DemandOutOfFuel
  | DemandRejected (why : reason).

Module Type INCREMENTAL_OPS (L : WLATTICE_OPS) (S : LOCAL_SYSTEM_OPS L)
    (RS : SYSTEM_OPS L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_OPS L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK_OPS L S).
  Parameter state : Type.
  Parameter init : state.
  Parameter value : state -> S.key -> option L.t.
  Parameter demand : S.prog -> policy L.wparam -> list S.key -> N -> state ->
    demand_status * state.
  Parameter edit : S.prog -> S.prog -> list S.row -> state -> state.
End INCREMENTAL_OPS.

Module Type INCREMENTAL_SPEC (L : WLATTICE) (S : LOCAL_SYSTEM L)
    (RS : SYSTEM L with Definition key := S.key
      with Definition key_code := S.key_code)
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
        S.deps p r = S.deps p' r /\ S.sides p r = S.sides p' r /\
        forall look, S.eval p r look = S.eval p' r look).
End INCREMENTAL_SPEC.

Module Type INCREMENTAL_LAWS (L : WLATTICE) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM L)
    (RS : SYSTEM L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L LB RS Sol)
    (Import X : INCREMENTAL_OPS L S RS R Sol Checker)
    (Import XS : INCREMENTAL_SPEC L S RS R Sol Checker X).
  (** The empty state is sound and below all post-solutions. *)
  Parameter init_inv : forall p, inv p init /\ least_on p init.
  (** Demand returns a sound state for every outcome. *)
  Parameter demand_inv : forall p pol roots fuel st o st', S.wf p -> inv p st ->
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
  Parameter edit_inv : forall p p' ch st, S.wf p' -> edit_covers p p' ch -> inv p st ->
    inv p' (edit p p' ch st).
  (** Invalidation retains old values verbatim. *)
  Parameter edit_keeps : forall p p' ch st x v,
    value (edit p p' ch st) x = Some v -> value st x = Some v.
  (** Widening-free demand keeps every stored value below all post-solutions. *)
  Parameter demand_least : forall p pol roots fuel st o st', S.wf p -> S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  (** Covered edits keep the least-value property on the retained domain. *)
  Parameter edit_least : forall p p' ch st, S.wf p -> edit_covers p p' ch ->
    inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  (** Stored least values agree in both lattice directions with a global least solution. *)
  Parameter from_scratch_agrees : forall p st s x v, S.wf p -> S.monotone p ->
    inv p st -> least_on p st -> least_solution p s -> value st x = Some v ->
    L.leb (s x) v = true /\ L.leb v (s x) = true.
End INCREMENTAL_LAWS.

Module Type INCREMENTAL (L : WLATTICE) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM L)
    (RS : SYSTEM L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L LB RS Sol) :=
  INCREMENTAL_OPS L S RS R Sol Checker <+
  INCREMENTAL_SPEC L S RS R Sol Checker <+
  INCREMENTAL_LAWS L LB Top S RS R Sol Checker Least.

Module Type INCREMENTAL_TIME (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol)
    (Import X : INCREMENTAL L LB Top S RS R Sol Checker Least).
  (* spec: region invalidated frozen infl_deg infl_mass kwidth width state_ok *)
  Parameter state_ok : state -> Prop.
  (** Initialization and public transitions keep the representation invariant. *)
  Parameter state_ok_init : state_ok init.
  Parameter state_ok_demand : forall p pol roots fuel st o st', state_ok st ->
    demand p pol roots fuel st = (o, st') -> state_ok st'.
  Parameter state_ok_edit : forall p p' ch st, state_ok st -> state_ok (edit p p' ch st).
  Parameter region : S.prog -> list S.key -> state -> list S.row.
  Parameter invalidated : S.prog -> S.prog -> list S.row -> state -> list S.key.
  Parameter frozen : S.prog -> list S.key -> state -> list (S.key * L.t).
  Parameter infl_deg : state -> S.key -> nat.
  Parameter infl_mass : state -> nat.
  Parameter kwidth : state -> nat.
  Definition width (p : S.prog) (_ : state) : nat :=
    S.kw p + N.to_nat (S.row_work p 0).
  Parameter T_init : N.
  Parameter T_value : state -> S.key -> N.
  Parameter T_demand : S.prog -> policy L.wparam -> list S.key -> N -> state -> N.
  Parameter T_edit : S.prog -> S.prog -> list S.row -> state -> N.
  Parameter c_inc : N.
  (** Regional checking restores the frozen values in the solver candidate. *)
  Definition checked (p : S.prog) (roots : list S.key) (st : state)
      (m : kmap S.key L.t) : kmap S.key L.t :=
    fold_left (fun acc xv => PTrieCode.set (S.key_code (fst xv)) xv acc)
      (frozen p roots st) m.
  (** Demand pays for discovery and the restricted solver including fuel bits. *)
  Definition demand_solver_work p pol roots fuel st : N :=
    let fz := frozen p roots st in
    let rg := region p roots st in
    (Sol.T_run (R.mk p fz rg) pol fuel + R.T_mk p fz rg +
      match Sol.run (R.mk p fz rg) pol fuel with
      | Solved m => Checker.T_check_rows p rg (checked p roots st m)
      | _ => 0
      end)%N.

  Parameter T_demand_le : forall p pol roots fuel st, S.wf p -> inv p st ->
    (T_demand p pol roots fuel st <=
      c_inc * N.of_nat ((fold_right Nat.add 0%nat
        (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st)) +
        length roots + 1)%nat) * N.of_nat (width p st + 1) +
      c_inc * N.of_nat (fold_right Nat.add 0%nat (map (fun x => S.key_bits x + 1)%nat roots)) +
      c_inc * demand_solver_work p pol roots fuel st)%N.
  (** Invalidation lists each removed stored key once. *)
  Parameter invalidated_spec : forall p p' ch st x,
    In x (invalidated p p' ch st) <-> dom st x /\ ~ dom (edit p p' ch st) x.
  Parameter invalidated_nodup : forall p p' ch st, NoDup (invalidated p p' ch st).
  (** The empty state stores no key and no influence entry. *)
  Parameter infl_mass_init : infl_mass init = 0.
  Parameter kwidth_init : kwidth init = 0.
  (** Every stored key fits the key width of the state. *)
  Parameter kwidth_dom : forall st x, state_ok st -> dom st x -> S.key_bits x <= kwidth st.
  (** Demand adds influence mass within twice its charged region occurrences. *)
  Parameter infl_mass_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    infl_mass st' <= infl_mass st + 2 * (length roots + fold_right Nat.add 0%nat
      (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st))).
  (** Demand widens the state only to program keys and roots. *)
  Parameter kwidth_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    kwidth st' <= Nat.max (kwidth st) (fold_right Nat.max (S.kw p) (map S.key_bits roots)).
  (** Editing releases the stored key and the entries of every invalidated key. *)
  Parameter infl_mass_edit : forall p p' ch st, state_ok st ->
    infl_mass (edit p p' ch st) +
      fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (invalidated p p' ch st)) <=
    infl_mass st.
  (** Editing never widens the state. *)
  Parameter kwidth_edit : forall p p' ch st, kwidth (edit p p' ch st) <= kwidth st.
  (** Editing pays for the influence mass that it releases and for the changed rows. *)
  Parameter T_edit_le : forall p p' ch st, S.wf p -> S.wf p' -> state_ok st ->
    (forall r, In r ch -> In r (S.rows p) \/ In r (S.rows p')) ->
    (T_edit p p' ch st <= c_inc *
      N.of_nat (((infl_mass st - infl_mass (edit p p' ch st)) +
        fold_right Nat.add 0%nat (map (fun r => length (S.writes p r) + length (S.writes p' r) +
          length (S.deps p r) + length (S.deps p' r) + 1) ch) + 1)%nat) *
      N.of_nat (width p st + width p' st + kwidth st + 1))%N.
  (** Frozen pairs are stored checked values. *)
  Parameter frozen_spec : forall p roots st x v,
    In (x, v) (frozen p roots st) -> value st x = Some v.
  (** Frozen pairs have distinct keys read or written by region rows. *)
  Parameter frozen_region : forall p roots st x v, In (x, v) (frozen p roots st) ->
    exists r, In r (region p roots st) /\ In x (S.writes p r ++ S.deps p r).
  Parameter frozen_nodup : forall p roots st, NoDup (map fst (frozen p roots st)).
  (** Discovery selects declared rows. *)
  Parameter region_rows : forall p roots st r,
    In r (region p roots st) -> In r (S.rows p).
  (** Every selected row writes a key outside the old checked domain. *)
  Parameter region_new : forall p roots st r,
    In r (region p roots st) -> exists y, In y (S.writes p r) /\ ~ dom st y.

End INCREMENTAL_TIME.

Module Type INCREMENTAL_T (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol) :=
  INCREMENTAL L LB Top S RS R Sol Checker Least <+
  INCREMENTAL_TIME L LB Top S RS R Sol Checker Least.

Module Type INCREMENTAL_PLAN (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol)
    (Import X : INCREMENTAL_T L LB Top S RS R Sol Checker Least).
  Parameter discover : S.prog -> list S.key -> state -> list S.key.
  Parameter invalidate : S.prog -> S.prog -> list S.row -> state -> list S.key.
  Parameter stored : state -> list S.key.
  Parameter infl_at : state -> S.key -> list positive.
  Parameter snapshot_keys : state -> list S.key.
  (* spec: snapshot_mass snapshots cowrite_at *)
  Parameter snapshot_mass : state -> nat.
  Parameter snapshots : state -> list (positive * incremental_snapshot S.key).
  Parameter cowrite_at : state -> S.key -> list positive.
  Parameter snapshot_get : positive -> state -> option (incremental_snapshot S.key).
  Parameter snapshot_set : positive -> incremental_snapshot S.key -> state -> state.
  Parameter snapshot_record : S.key -> list S.key -> state -> state.
  Parameter T_snapshot_get : positive -> state -> N.
  Parameter T_snapshot_set : positive -> incremental_snapshot S.key -> state -> N.
  Parameter T_snapshot_record : S.key -> list S.key -> state -> N.
  (** Snapshot access walks the identifier once. *)
  Parameter T_snapshot_get_le : forall id st,
    (T_snapshot_get id st <= c_inc * N.of_nat (Pos.size_nat id + 1))%N.
  Parameter T_snapshot_set_le : forall id ss st,
    (T_snapshot_set id ss st <= c_inc * N.of_nat (Pos.size_nat id + 1))%N.
  (** Recording pays for the owner code and the new write occurrences. *)
  Parameter T_snapshot_record_le : forall owner writes st,
    (T_snapshot_record owner writes st <=
      c_inc * N.of_nat (S.key_bits owner + length writes + 1))%N.
  (** Trie lookup reads precisely the recorded snapshot inventory. *)
  Parameter snapshot_get_pin : forall st id ss,
    snapshot_get id st = Some ss <-> In (id, ss) (snapshots st).
  (** Trie update changes precisely one shared snapshot. *)
  Parameter snapshot_set_pin : forall st id ss q,
    snapshot_get q (snapshot_set id ss st) =
      if Pos.eqb q id then Some ss else snapshot_get q st.
  (** Recording copies the new row's writes once before the previous live group. *)
  Parameter snapshot_record_pin : forall st owner writes,
    snapshot_get (S.key_code owner) (snapshot_record owner writes st) =
      Some {| snapshot_owner := owner;
        snapshot_writes := writes ++
          match snapshot_get (S.key_code owner) st with
          | Some ss => if snapshot_live ss then snapshot_writes ss else []
          | None => []
          end;
        snapshot_live := true |}.
  (** Snapshot mass counts each unvisited write occurrence once. *)
  Parameter snapshot_mass_pin : forall st, snapshot_mass st =
    fold_right (fun ss n =>
      if snapshot_live (snd ss) then length (snapshot_writes (snd ss)) + n else n)
      0 (snapshots st).
  (** The recorded key inventory includes visited snapshots for identifier width accounting. *)
  Parameter snapshot_keys_pin : forall st, snapshot_keys st =
    flat_map (fun ss => snapshot_writes (snd ss)) (snapshots st).
  (** Every snapshot identifier is the code of an owner among its writes. *)
  Parameter snapshot_owner_pin : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    id = S.key_code (snapshot_owner ss) /\ In (snapshot_owner ss) (snapshot_writes ss).
  (** Snapshot identifiers occur once in the inventory. *)
  Parameter snapshots_nodup : forall st, NoDup (map fst (snapshots st)).
  (** Read entries resolve to a retained shared snapshot, including stale entries. *)
  Parameter infl_snapshot_pin : forall st x id, state_ok st -> In id (infl_at st x) ->
    exists ss, In (id, ss) (snapshots st).
  (** Unvisited snapshots contain stored keys. *)
  Parameter snapshot_stored_pin : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    snapshot_live ss = true -> forall x, In x (snapshot_writes ss) -> dom st x.
  (** Co-write memberships are precisely the unvisited snapshot key occurrences. *)
  Parameter cowrite_count_pin : forall st x id, state_ok st ->
    length (filter (Pos.eqb id) (cowrite_at st x)) =
    fold_right (fun iss n =>
      if (Pos.eqb id (fst iss) && snapshot_live (snd iss))%bool then
        length (filter (S.key_eqb x) (snapshot_writes (snd iss))) + n else n)
      0 (snapshots st).
  (** Shared snapshot mass pays the co-write memberships without a second inventory charge. *)
  Parameter cowrite_mass_pin : forall st, state_ok st -> snapshot_mass st =
    fold_right Nat.add 0 (map (fun x => length (cowrite_at st x)) (stored st)).
  (** Every retained snapshot identifier fits the stored key width. *)
  Parameter snapshot_id_width : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    Pos.size_nat id <= kwidth st.
  (** Demands record write occurrences only from their discovered rows. *)
  Parameter snapshot_keys_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') -> forall x, In x (snapshot_keys st') ->
    In x (snapshot_keys st) \/ exists r, In r (region p roots st) /\ In x (S.writes p r).
  (** Demand records keys, read entries and shared write occurrences within their exact charges. *)
  Parameter demand_record_counts : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    let reads := fold_right Nat.add 0 (map (fun r => length (S.deps p r)) (region p roots st)) in
    let writes := fold_right Nat.add 0 (map (fun r => length (S.writes p r)) (region p roots st)) in
    length (stored st') <= length (stored st) + length roots + reads + writes /\
    fold_right Nat.add 0 (map (fun x => length (infl_at st' x)) (stored st')) <=
      fold_right Nat.add 0 (map (fun x => length (infl_at st x)) (stored st)) + reads /\
    snapshot_mass st' <= snapshot_mass st + writes.
  (** Edits retain read entries of every retained key, including changed-row entries. *)
  Parameter edit_infl_keeps : forall p p' ch st x, dom (edit p p' ch st) x ->
    infl_at (edit p p' ch st) x = infl_at st x.
  (** Visiting a snapshot removes all its writes and retires every co-write membership. *)
  Parameter edit_snapshot_visit : forall p p' ch st id ss, state_ok st ->
    In (id, ss) (snapshots st) -> snapshot_live ss = true ->
    (exists x, In x (snapshot_writes ss) /\ In x (invalidated p p' ch st)) ->
    (forall x, In x (snapshot_writes ss) -> ~ dom (edit p p' ch st) x) /\
    (forall x, ~ In id (cowrite_at (edit p p' ch st) x)) /\
    (forall ss', In (id, ss') (snapshots (edit p p' ch st)) -> snapshot_live ss' = false).
  (** The stored key list enumerates the domain once. *)
  Parameter stored_spec : forall st x, state_ok st -> (In x (stored st) <-> dom st x).
  Parameter stored_nodup : forall st, state_ok st -> NoDup (stored st).
  (** The influence degree counts the recorded entries of a key, stale ones included. *)
  Parameter infl_deg_spec : forall st x, infl_deg st x = length (infl_at st x).
  (** Influence mass counts stored keys, their entries and the unvisited snapshot keys. *)
  Parameter infl_mass_spec : forall st, infl_mass st =
    fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (stored st)) + snapshot_mass st.
  (** The key width covers the stored keys and every key of a recorded snapshot. *)
  Parameter kwidth_spec : forall st, kwidth st =
    fold_right Nat.max 0 (map S.key_bits (stored st ++ snapshot_keys st)).
  (** The public invalidation list is the plan's closure. *)
  Parameter invalidated_pin : forall p p' ch st,
    invalidated p p' ch st = invalidate p p' ch st.
  (** The closure lists stored keys only, each once. *)
  Parameter invalidate_dom : forall p p' ch st x,
    In x (invalidate p p' ch st) -> dom st x.
  Parameter invalidate_nodup : forall p p' ch st, NoDup (invalidate p p' ch st).
  Parameter merge_region : state -> list S.key -> kmap S.key L.t -> state.
  Parameter T_discover : S.prog -> list S.key -> state -> N.
  Parameter T_invalidate : S.prog -> S.prog -> list S.row -> state -> N.
  Parameter T_merge_region : state -> list S.key -> kmap S.key L.t -> N.
  (** Discovery extends the old domain to a closed domain. *)
  Parameter discover_closed : forall p roots st, inv p st ->
    closed p (fun x => dom st x \/ In x (discover p roots st)).
  (** Every discovered row has all its writes and reads in the extended domain. *)
  Parameter region_closed : forall p roots st r x, inv p st ->
    In r (region p roots st) -> In x (S.writes p r ++ S.deps p r) ->
    dom st x \/ In x (discover p roots st).
  (** Old rows keep their post-solution property when the old domain agrees. *)
  Parameter frame_post : forall p st s, S.wf p -> inv p st ->
    (forall x, dom st x -> s x = look st x) ->
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  (** Accepted regional certificates combine with the old frame to give a sound state. *)
  Parameter merge_inv : forall p roots st m, S.wf p -> inv p st ->
    Checker.check_rows p (region p roots st) m = true ->
    (forall x, dom st x -> Checker.look m x = look st x) ->
    inv p (merge_region st (discover p roots st) m).
  (** Completed demand has an accepted certificate for the discovered rows. *)
  Parameter demand_certificate : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') ->
    exists m, Checker.check_rows p (region p roots st) m = true.
  (** Removing the forward influence closure keeps a closed domain. *)
  Parameter invalidate_closed : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    closed p' (fun x => dom st x /\ ~ In x (invalidate p p' ch st)).
  (** Editing removes precisely the invalidated stored values. *)
  Parameter edit_value : forall p p' ch st x,
    value (edit p p' ch st) x =
      if existsb (S.key_eqb x) (invalidate p p' ch st) then None else value st x.
  (** Changed writes in either program invalidate their old stored values. *)
  Parameter invalidate_changed : forall p p' ch st r y, In r ch ->
    (In r (S.rows p) /\ In y (S.writes p r) \/
      In r (S.rows p') /\ In y (S.writes p' r)) ->
    dom st y -> In y (invalidate p p' ch st).
  (** Unchanged rows writing into the retained domain keep their accepted contributions. *)
  Parameter edit_frame : forall p p' ch st, S.wf p' -> edit_covers p p' ch -> inv p st ->
    post_on p' (edit p p' ch st).
  (** Restricted least solving and frozen least seeds give regional least values. *)
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

Module Type INCREMENTAL_ALL (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol) :=
  INCREMENTAL_T L LB Top S RS R Sol Checker Least <+
  INCREMENTAL_PLAN L LB Top S RS R Sol Checker Least.
