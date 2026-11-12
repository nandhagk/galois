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

Record incremental_state (K A : Type) := {
  inc_values : PTrieCode.t (K * A);
  inc_influence : PTrieCode.t (list positive);
  inc_cowrites : PTrieCode.t (list positive);
  inc_snapshots : PTrieCode.t (incremental_snapshot K)
}.

Arguments inc_values {K A}.
Arguments inc_influence {K A}.
Arguments inc_snapshots {K A}.
Arguments inc_cowrites {K A}.

TimeFun inc_values.
TimeFun inc_influence.
TimeFun inc_snapshots.
TimeFun inc_cowrites.

Module IncrementalCode (L : WLATTICE_OPS) (S : LOCAL_SYSTEM_OPS L)
    (RS : SYSTEM_OPS L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_OPS L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK_OPS L S)
    <: INCREMENTAL_OPS L S RS R Sol Checker.
  Definition state := incremental_state S.key L.t.
  (* STUB-CODE *)
  Definition init : state :=
    {| inc_values := PTrieCode.empty; inc_influence := PTrieCode.empty;
       inc_cowrites := PTrieCode.empty; inc_snapshots := PTrieCode.empty |}.
  (* STUB-CODE *)
  Definition value (_ : state) (_ : S.key) : option L.t := None.
  (* STUB-CODE *)
  Definition demand (_ : S.prog) (_ : policy L.wparam) (_ : list S.key) (_ : N)
      (st : state) : demand_status * state := (DemandOutOfFuel, st).
  (* STUB-CODE *)
  Definition edit (_ _ : S.prog) (_ : list S.row) (st : state) : state := st.
  Definition snapshot_get (id : positive) (st : state)
      : option (incremental_snapshot S.key) := PTrieCode.get id (inc_snapshots st).
  Definition snapshot_set (id : positive) (ss : incremental_snapshot S.key) (st : state)
      : state :=
    {| inc_values := inc_values st; inc_influence := inc_influence st;
       inc_cowrites := inc_cowrites st; inc_snapshots := PTrieCode.set id ss (inc_snapshots st) |}.
  Definition snapshot_record (owner : S.key) (writes : list S.key) (st : state) : state :=
    let id := S.key_code owner in
    let previous := match snapshot_get id st with
      | Some ss => if snapshot_live ss then snapshot_writes ss else []
      | None => []
      end in
    snapshot_set id
      {| snapshot_owner := owner; snapshot_writes := writes ++ previous; snapshot_live := true |}
      st.
End IncrementalCode.

Module Incremental (L : WLATTICE) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM L)
    (RS : SYSTEM L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L LB RS Sol) <: INCREMENTAL L LB Top S RS R Sol Checker Least.
  Include IncrementalCode L S RS R Sol Checker.
  Include INCREMENTAL_SPEC L S RS R Sol Checker.
  Lemma init_inv : forall p, inv p init /\ least_on p init.
  Proof. Admitted.

  Lemma demand_inv : forall p pol roots fuel st o st', S.wf p -> inv p st ->
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

  Lemma edit_inv : forall p p' ch st, S.wf p' -> edit_covers p p' ch -> inv p st ->
    inv p' (edit p p' ch st).
  Proof. Admitted.

  Lemma edit_keeps : forall p p' ch st x v,
    value (edit p p' ch st) x = Some v -> value st x = Some v.
  Proof. Admitted.

  Lemma demand_least : forall p pol roots fuel st o st', S.wf p -> S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  Proof. Admitted.

  Lemma edit_least : forall p p' ch st, S.wf p -> edit_covers p p' ch ->
    inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  Proof. Admitted.

  Lemma from_scratch_agrees : forall p st s x v, S.wf p -> S.monotone p ->
    inv p st -> least_on p st -> least_solution p s -> value st x = Some v ->
    L.leb (s x) v = true /\ L.leb v (s x) = true.
  Proof. Admitted.

End Incremental.

Module IncrementalT (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol) <: INCREMENTAL_ALL L LB Top S RS R Sol Checker Least.
  Include Incremental L LB Top S RS R Sol Checker Least.
  TimeFun init.
  TimeFun value.
  TimeFun demand.
  TimeFun edit.
  TimeFun snapshot_get.
  TimeFun snapshot_set.
  TimeFun snapshot_record.
  Definition region (_ : S.prog) (_ : list S.key) (_ : state) : list S.row := [].
  Definition invalidated (_ _ : S.prog) (_ : list S.row) (_ : state) : list S.key := [].
  Definition frozen (_ : S.prog) (_ : list S.key) (_ : state) : list (S.key * L.t) := [].
  Definition stored (st : state) : list S.key :=
    map (fun binding => fst (snd binding)) (PTrieCode.elements (inc_values st)).
  Definition infl_at (st : state) (x : S.key) : list positive :=
    match PTrieCode.get (S.key_code x) (inc_influence st) with
    | Some entries => entries
    | None => []
    end.
  Definition cowrite_at (st : state) (x : S.key) : list positive :=
    match PTrieCode.get (S.key_code x) (inc_cowrites st) with
    | Some entries => entries
    | None => []
    end.
  Definition snapshots (st : state) : list (positive * incremental_snapshot S.key) :=
    PTrieCode.elements (inc_snapshots st).
  Definition snapshot_keys (st : state) : list S.key :=
    flat_map (fun ss => snapshot_writes (snd ss)) (snapshots st).
  Definition snapshot_mass (st : state) : nat :=
    fold_right (fun ss n =>
      if snapshot_live (snd ss) then length (snapshot_writes (snd ss)) + n else n)
      0 (snapshots st).
  Definition infl_deg (st : state) (x : S.key) : nat := length (infl_at st x).
  Definition infl_mass (st : state) : nat :=
    fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (stored st)) + snapshot_mass st.
  Definition kwidth (st : state) : nat :=
    fold_right Nat.max 0 (map S.key_bits (stored st ++ snapshot_keys st)).

  Definition width (p : S.prog) (_ : state) : nat :=
    S.kw p + N.to_nat (S.row_work p 0).
  Definition c_inc : N := 1. (* STUB *)
  (** Regional checking restores the frozen values in the solver candidate. *)
  Definition checked (p : S.prog) (roots : list S.key) (st : state)
      (m : kmap S.key L.t) : kmap S.key L.t :=
    fold_left (fun acc xv => PTrieCode.set (S.key_code (fst xv)) xv acc)
      (frozen p roots st) m.
  Definition demand_solver_work p pol roots fuel st : N :=
    let fz := frozen p roots st in
    let rg := region p roots st in
    (Sol.T_run (R.mk p fz rg) pol fuel + R.T_mk p fz rg +
      match Sol.run (R.mk p fz rg) pol fuel with
      | Solved m => Checker.T_check_rows p rg (checked p roots st m)
      | _ => 0
      end)%N.

  Lemma T_demand_le : forall p pol roots fuel st, S.wf p -> inv p st ->
    (T_demand p pol roots fuel st <=
      c_inc * N.of_nat ((fold_right Nat.add 0%nat
        (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st)) +
        length roots + 1)%nat) * N.of_nat (width p st + 1) +
      c_inc * N.of_nat (fold_right Nat.add 0%nat (map (fun x => S.key_bits x + 1)%nat roots)) +
      c_inc * demand_solver_work p pol roots fuel st)%N.
  Proof. Admitted. (* STUB *)

  (** Invalidation lists each removed stored key once. *)
  Lemma invalidated_spec : forall p p' ch st x,
    In x (invalidated p p' ch st) <-> dom st x /\ ~ dom (edit p p' ch st) x.
  Proof. Admitted. (* STUB *)
  Lemma invalidated_nodup : forall p p' ch st, NoDup (invalidated p p' ch st).
  Proof. Admitted. (* STUB *)
  (** The empty state stores no key and no influence entry. *)
  Lemma infl_mass_init : infl_mass init = 0.
  Proof. Admitted. (* STUB *)
  Lemma kwidth_init : kwidth init = 0.
  Proof. Admitted. (* STUB *)
  (** Every stored key fits the key width of the state. *)
  Lemma kwidth_dom : forall st x, dom st x -> S.key_bits x <= kwidth st.
  Proof. Admitted. (* STUB *)
  (** Demand adds influence mass within twice its charged region occurrences. *)
  Lemma infl_mass_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    infl_mass st' <= infl_mass st + 2 * (length roots + fold_right Nat.add 0%nat
      (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st))).
  Proof. Admitted. (* STUB *)
  (** Demand widens the state only to program keys and roots. *)
  Lemma kwidth_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    kwidth st' <= Nat.max (kwidth st) (fold_right Nat.max (S.kw p) (map S.key_bits roots)).
  Proof. Admitted. (* STUB *)
  (** Editing releases the stored key and the entries of every invalidated key. *)
  Lemma infl_mass_edit : forall p p' ch st,
    infl_mass (edit p p' ch st) +
      fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (invalidated p p' ch st)) <=
    infl_mass st.
  Proof. Admitted. (* STUB *)
  (** Editing never widens the state. *)
  Lemma kwidth_edit : forall p p' ch st, kwidth (edit p p' ch st) <= kwidth st.
  Proof. Admitted. (* STUB *)
  (** Editing pays for the influence mass that it releases and for the changed rows. *)
  Lemma T_edit_le : forall p p' ch st, S.wf p -> S.wf p' ->
    (forall r, In r ch -> In r (S.rows p) \/ In r (S.rows p')) ->
    (T_edit p p' ch st <= c_inc *
      N.of_nat (((infl_mass st - infl_mass (edit p p' ch st)) +
        fold_right Nat.add 0%nat (map (fun r => length (S.writes p r) + length (S.writes p' r) +
          length (S.deps p r) + length (S.deps p' r) + 1) ch) + 1)%nat) *
      N.of_nat (width p st + width p' st + kwidth st + 1))%N.
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition discover (_ : S.prog) (_ : list S.key) (_ : state) : list S.key := [].
  TimeFun discover.
  (* STUB-CODE *)
  Definition invalidate (_ _ : S.prog) (_ : list S.row) (_ : state) : list S.key := [].
  TimeFun invalidate.
  (** Trie lookup reads precisely the recorded snapshot inventory. *)
  Lemma snapshot_get_pin : forall st id ss,
    snapshot_get id st = Some ss <-> In (id, ss) (snapshots st).
  Proof. Admitted. (* STUB *)
  (** Trie update changes precisely one shared snapshot. *)
  Lemma snapshot_set_pin : forall st id ss q,
    snapshot_get q (snapshot_set id ss st) =
      if Pos.eqb q id then Some ss else snapshot_get q st.
  Proof. Admitted. (* STUB *)
  (** Recording copies the new row's writes once before the previous live group. *)
  Lemma snapshot_record_pin : forall st owner writes,
    snapshot_get (S.key_code owner) (snapshot_record owner writes st) =
      Some {| snapshot_owner := owner;
        snapshot_writes := writes ++
          match snapshot_get (S.key_code owner) st with
          | Some ss => if snapshot_live ss then snapshot_writes ss else []
          | None => []
          end;
        snapshot_live := true |}.
  Proof. Admitted. (* STUB *)
  (** Snapshot mass counts each unvisited write occurrence once. *)
  Lemma snapshot_mass_pin : forall st, snapshot_mass st =
    fold_right (fun ss n =>
      if snapshot_live (snd ss) then length (snapshot_writes (snd ss)) + n else n)
      0 (snapshots st).
  Proof. Admitted. (* STUB *)
  (** The recorded key inventory includes visited snapshots for identifier width accounting. *)
  Lemma snapshot_keys_pin : forall st, snapshot_keys st =
    flat_map (fun ss => snapshot_writes (snd ss)) (snapshots st).
  Proof. Admitted. (* STUB *)
  (** Every snapshot identifier is the code of an owner among its writes. *)
  Lemma snapshot_owner_pin : forall st id ss, In (id, ss) (snapshots st) ->
    id = S.key_code (snapshot_owner ss) /\ In (snapshot_owner ss) (snapshot_writes ss).
  Proof. Admitted. (* STUB *)
  (** Snapshot identifiers occur once in the inventory. *)
  Lemma snapshots_nodup : forall st, NoDup (map fst (snapshots st)).
  Proof. Admitted. (* STUB *)
  (** Read entries resolve to a retained shared snapshot, including stale entries. *)
  Lemma infl_snapshot_pin : forall st x id, In id (infl_at st x) ->
    exists ss, In (id, ss) (snapshots st).
  Proof. Admitted. (* STUB *)
  (** Unvisited snapshots contain stored keys. *)
  Lemma snapshot_stored_pin : forall st id ss, In (id, ss) (snapshots st) ->
    snapshot_live ss = true -> forall x, In x (snapshot_writes ss) -> dom st x.
  Proof. Admitted. (* STUB *)
  (** Co-write memberships are precisely the unvisited snapshot key occurrences. *)
  Lemma cowrite_count_pin : forall st x id,
    length (filter (Pos.eqb id) (cowrite_at st x)) =
    fold_right (fun iss n =>
      if (Pos.eqb id (fst iss) && snapshot_live (snd iss))%bool then
        length (filter (S.key_eqb x) (snapshot_writes (snd iss))) + n else n)
      0 (snapshots st).
  Proof. Admitted. (* STUB *)
  (** Shared snapshot mass pays the co-write memberships without a second inventory charge. *)
  Lemma cowrite_mass_pin : forall st, snapshot_mass st =
    fold_right Nat.add 0 (map (fun x => length (cowrite_at st x)) (stored st)).
  Proof. Admitted. (* STUB *)
  (** Every retained snapshot identifier fits the stored key width. *)
  Lemma snapshot_id_width : forall st id ss, In (id, ss) (snapshots st) ->
    Pos.size_nat id <= kwidth st.
  Proof. Admitted. (* STUB *)
  (** Demands record write occurrences only from their discovered rows. *)
  Lemma snapshot_keys_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') -> forall x, In x (snapshot_keys st') ->
    In x (snapshot_keys st) \/ exists r, In r (region p roots st) /\ In x (S.writes p r).
  Proof. Admitted. (* STUB *)
  (** Demand records keys, read entries and shared write occurrences within their exact charges. *)
  Lemma demand_record_counts : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    let reads := fold_right Nat.add 0 (map (fun r => length (S.deps p r)) (region p roots st)) in
    let writes := fold_right Nat.add 0 (map (fun r => length (S.writes p r)) (region p roots st)) in
    length (stored st') <= length (stored st) + length roots + reads + writes /\
    fold_right Nat.add 0 (map (fun x => length (infl_at st' x)) (stored st')) <=
      fold_right Nat.add 0 (map (fun x => length (infl_at st x)) (stored st)) + reads /\
    snapshot_mass st' <= snapshot_mass st + writes.
  Proof. Admitted. (* STUB *)
  (** Edits retain read entries of every retained key, including changed-row entries. *)
  Lemma edit_infl_keeps : forall p p' ch st x, dom (edit p p' ch st) x ->
    infl_at (edit p p' ch st) x = infl_at st x.
  Proof. Admitted. (* STUB *)
  (** Visiting a snapshot removes all its writes and retires every co-write membership. *)
  Lemma edit_snapshot_visit : forall p p' ch st id ss,
    In (id, ss) (snapshots st) -> snapshot_live ss = true ->
    (exists x, In x (snapshot_writes ss) /\ In x (invalidated p p' ch st)) ->
    (forall x, In x (snapshot_writes ss) -> ~ dom (edit p p' ch st) x) /\
    (forall x, ~ In id (cowrite_at (edit p p' ch st) x)) /\
    (forall ss', In (id, ss') (snapshots (edit p p' ch st)) -> snapshot_live ss' = false).
  Proof. Admitted. (* STUB *)

  (** The stored key list enumerates the domain once. *)
  Lemma stored_spec : forall st x, In x (stored st) <-> dom st x.
  Proof. Admitted. (* STUB *)
  Lemma stored_nodup : forall st, NoDup (stored st).
  Proof. Admitted. (* STUB *)
  (** The influence degree counts the recorded entries of a key, stale ones included. *)
  Lemma infl_deg_spec : forall st x, infl_deg st x = length (infl_at st x).
  Proof. Admitted. (* STUB *)
  (** Influence mass counts stored keys, their entries and the unvisited snapshot keys. *)
  Lemma infl_mass_spec : forall st, infl_mass st =
    fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (stored st)) + snapshot_mass st.
  Proof. Admitted. (* STUB *)
  (** The key width covers the stored keys and every key of a recorded snapshot. *)
  Lemma kwidth_spec : forall st, kwidth st =
    fold_right Nat.max 0 (map S.key_bits (stored st ++ snapshot_keys st)).
  Proof. Admitted. (* STUB *)
  (** The public invalidation list is the plan's closure. *)
  Lemma invalidated_pin : forall p p' ch st,
    invalidated p p' ch st = invalidate p p' ch st.
  Proof. Admitted. (* STUB *)
  (** The closure lists stored keys only, each once. *)
  Lemma invalidate_dom : forall p p' ch st x,
    In x (invalidate p p' ch st) -> dom st x.
  Proof. Admitted. (* STUB *)
  Lemma invalidate_nodup : forall p p' ch st, NoDup (invalidate p p' ch st).
  Proof. Admitted. (* STUB *)
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

  Lemma frame_post : forall p st s, S.wf p -> inv p st ->
    (forall x, dom st x -> s x = look st x) ->
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  Proof. Admitted. (* STUB *)

  Lemma merge_inv : forall p roots st m, S.wf p -> inv p st ->
    Checker.check_rows p (region p roots st) m = true ->
    (forall x, dom st x -> Checker.look m x = look st x) ->
    inv p (merge_region st (discover p roots st) m).
  Proof. Admitted. (* STUB *)

  Lemma demand_certificate : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') ->
    exists m, Checker.check_rows p (region p roots st) m = true.
  Proof. Admitted. (* STUB *)

  Lemma invalidate_closed : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    closed p' (fun x => dom st x /\ ~ In x (invalidate p p' ch st)).
  Proof. Admitted. (* STUB *)

  (** Editing removes precisely the invalidated stored values. *)
  Lemma edit_value : forall p p' ch st x,
    value (edit p p' ch st) x =
      if existsb (S.key_eqb x) (invalidate p p' ch st) then None else value st x.
  Proof. Admitted. (* STUB *)

  (** Changed writes in either program invalidate their old stored values. *)
  Lemma invalidate_changed : forall p p' ch st r y, In r ch ->
    (In r (S.rows p) /\ In y (S.writes p r) \/
      In r (S.rows p') /\ In y (S.writes p' r)) ->
    dom st y -> In y (invalidate p p' ch st).
  Proof. Admitted. (* STUB *)

  Lemma edit_frame : forall p p' ch st, S.wf p' -> edit_covers p p' ch -> inv p st ->
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

  (** Frozen pairs are stored checked values. *)
  Lemma frozen_spec : forall p roots st x v,
    In (x, v) (frozen p roots st) -> value st x = Some v.
  Proof. Admitted. (* STUB *)
  (** Discovery selects declared rows. *)
  Lemma region_rows : forall p roots st r,
    In r (region p roots st) -> In r (S.rows p).
  Proof. Admitted. (* STUB *)
  (** Every selected row writes a key outside the old checked domain. *)
  Lemma region_new : forall p roots st r,
    In r (region p roots st) -> exists y, In y (S.writes p r) /\ ~ dom st y.
  Proof. Admitted. (* STUB *)


End IncrementalT.
