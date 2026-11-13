(** * Checked incremental solving

    Incremental states retain values between demands and edits.
    For example, an initial state has no stored values.
    Builds on: IncrementalSig. *)

From Stdlib Require Import List Bool PArith NArith Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Code MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig CheckSig PolicySig Indexed.
From Galois.Incremental Require Import RestrictSig Restrict IncrementalSig.

Import List.ListNotations.
Import Code.List.

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
  Include SourceBindingsCode L S Checker.
  Definition state := incremental_state S.key L.t.
  Definition init : state :=
    {| inc_values := PTrieCode.empty; inc_influence := PTrieCode.empty;
       inc_cowrites := PTrieCode.empty; inc_snapshots := PTrieCode.empty |}.
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

  Definition value (st : state) (x : S.key) : option L.t :=
    lookup (inc_values st) x.

  Definition present (st : state) (x : S.key) : bool :=
    match value st x with Some _ => true | None => false end.

  Definition missing (st : state) (x : S.key) : bool := negb (present st x).
  Definition row_writes (p : S.prog) (r : S.row) : list S.key :=
    S.target p r :: S.sides p r.
  Definition row_keys (p : S.prog) (r : S.row) : list S.key :=
    row_writes p r ++ S.deps p r.

  Definition active (p : S.prog) (st : state) (known : list S.key) (r : S.row) : bool :=
    existsb (fun x => missing st x && mem x known) (row_writes p r).

  Definition discovery_seed (st : state) (roots : list S.key) : list S.key :=
    footprint_adds S.key_eqb (missing st) roots [].

  Definition plan (p : S.prog) (roots : list S.key) (st : state)
      : footprint_result S.key S.row :=
    footprint_run S.key_eqb (row_writes p) (row_keys p) (missing st)
      (discovery_seed st roots) (S.rows p).

  Definition discovery_keys (p : S.prog) (roots : list S.key) (st : state) : list S.key :=
    footprint_seen (plan p roots st).

  (** Filtering the original list preserves row order and duplicate occurrences. *)
  Definition region_for (p : S.prog) (st : state) (known : list S.key) : list S.row :=
    filter (active p st known) (S.rows p).

  Definition discovery_region (p : S.prog) (roots : list S.key) (st : state)
      : list S.row :=
    region_for p st (discovery_keys p roots st).

  Definition freeze_values (st : state) (xs : list S.key) : list (S.key * L.t) :=
    flat_map (fun x =>
      match value st x with Some v => [(x, v)] | None => [] end) xs.

  Definition frozen_for_rows (p : S.prog) (rs : list S.row) (st : state)
      : list (S.key * L.t) :=
    freeze_values st (unique (flat_map (row_keys p) rs)).

  Definition frozen_pairs (p : S.prog) (roots : list S.key) (st : state)
      : list (S.key * L.t) :=
    frozen_for_rows p (discovery_region p roots st) st.

  Definition merge_discovered (st : state) (xs : list S.key) (m : kmap S.key L.t) : state :=
    {| inc_values := fill xs m (inc_values st);
       inc_influence := inc_influence st;
       inc_cowrites := inc_cowrites st;
       inc_snapshots := inc_snapshots st |}.

  (** Validation makes dropping malformed cells observationally invisible at every key.
      The inventory is read once from the original map; pruning does not re-enumerate. *)
  Definition canonical_values (st : state) : kmap S.key L.t :=
    prune_values (PTrieCode.elements (inc_values st)) (inc_values st).

  Definition normalize_values (st : state) : state :=
    {| inc_values := canonical_values st;
       inc_influence := inc_influence st;
       inc_cowrites := inc_cowrites st;
       inc_snapshots := inc_snapshots st |}.

  Definition remove_buckets (xs : list S.key) (buckets : PTrieCode.t (list positive))
      : PTrieCode.t (list positive) :=
    fold_left (fun acc x => PTrieCode.remove (S.key_code x) acc) xs buckets.

  (** Before an absent key becomes stored, its uncounted stale buckets must be cleared. *)
  Definition clear_new_buckets (xs : list S.key) (st : state) : state :=
    {| inc_values := inc_values st;
       inc_influence := remove_buckets xs (inc_influence st);
       inc_cowrites := remove_buckets xs (inc_cowrites st);
       inc_snapshots := inc_snapshots st |}.

  Definition push_entry (x : S.key) (id : positive)
      (buckets : PTrieCode.t (list positive)) : PTrieCode.t (list positive) :=
    let code := S.key_code x in
    let previous := match PTrieCode.get code buckets with Some ids => ids | None => [] end in
    PTrieCode.set code (id :: previous) buckets.

  Definition record_row (p : S.prog) (r : S.row) (st : state) : state :=
    let owner := S.target p r in
    let id := S.key_code owner in
    let writes := row_writes p r in
    let with_snapshot := snapshot_record owner writes st in
    {| inc_values := inc_values with_snapshot;
       inc_influence := fold_left (fun acc x => push_entry x id acc)
         (S.deps p r) (inc_influence with_snapshot);
       inc_cowrites := fold_left (fun acc x => push_entry x id acc)
         writes (inc_cowrites with_snapshot);
       inc_snapshots := inc_snapshots with_snapshot |}.

  Definition record_rows (p : S.prog) (rs : list S.row) (st : state) : state :=
    fold_left (fun acc r => record_row p r acc) rs st.

  Definition finish_demand (p : S.prog) (st : state) (xs : list S.key)
      (rs : list S.row) (m : kmap S.key L.t) : state :=
    record_rows p rs
      (clear_new_buckets xs (merge_discovered (normalize_values st) xs m)).

  Definition demand (p : S.prog) (pol : policy L.wparam) (roots : list S.key)
      (fuel : N) (st : state) : demand_status * state :=
    if forallb (present st) roots then (Done, st)
    else
      let xs := discovery_keys p roots st in
      let rs := region_for p st xs in
      let fz := frozen_for_rows p rs st in
      match Sol.run (R.mk p fz rs) pol fuel with
      | OutOfFuel _ => (DemandOutOfFuel, st)
      | Rejected why => (DemandRejected why, st)
      | Solved m =>
          let candidate := restore fz m in
          if Checker.check_rows p rs candidate
          then (Done, finish_demand p st xs rs candidate)
          else (DemandRejected Check_failed, st)
      end.
  Definition row_footprint (p : S.prog) (r : S.row) : edit_footprint S.key :=
    {| edit_triggers := row_keys p r; edit_outputs := row_writes p r |}.

  Definition snapshot_footprint (ss : incremental_snapshot S.key) : edit_footprint S.key :=
    {| edit_triggers := snapshot_writes ss; edit_outputs := snapshot_writes ss |}.

  Definition edit_footprints (p p' : S.prog) (st : state) : list (edit_footprint S.key) :=
    map (row_footprint p) (S.rows p) ++
    map (row_footprint p') (S.rows p') ++
    map (fun entry => snapshot_footprint (snd entry))
      (filter (fun entry => snapshot_live (snd entry))
        (PTrieCode.elements (inc_snapshots st))).

  Definition changed_keys (p p' : S.prog) (ch : list S.row) : list S.key :=
    flat_map (fun r => row_writes p r ++ row_writes p' r) ch.

  Definition changed_seeds (p p' : S.prog) (ch : list S.row) (st : state) : list S.key :=
    footprint_adds S.key_eqb (present st) (changed_keys p p' ch) [].

  Definition invalidate_keys (p p' : S.prog) (ch : list S.row) (st : state) : list S.key :=
    let seeds := changed_seeds p p' ch st in
    match seeds with
    | [] => []
    | _ :: _ =>
      footprint_seen (footprint_run S.key_eqb edit_triggers edit_outputs (present st)
        seeds (edit_footprints p p' st))
    end.

  Definition retire_snapshot (bad : list S.key) (ss : incremental_snapshot S.key)
      : incremental_snapshot S.key :=
    {| snapshot_owner := snapshot_owner ss;
       snapshot_writes := snapshot_writes ss;
       snapshot_live := snapshot_live ss &&
         negb (existsb (fun x => mem x bad) (snapshot_writes ss)) |}.

  Definition edit (p p' : S.prog) (ch : list S.row) (st : state) : state :=
    let bad := invalidate_keys p p' ch st in
    match bad with
    | [] => st
    | _ :: _ =>
      {| inc_values := remove_keys bad (inc_values st);
         inc_influence := remove_keys bad (inc_influence st);
         inc_cowrites := remove_keys bad (inc_cowrites st);
         inc_snapshots := PTrieCode.map (retire_snapshot bad) (inc_snapshots st) |}
    end.

  (** The public region and invalidation views are the operational plans. *)
  Definition region := discovery_region.
  Definition frozen := frozen_pairs.
  Definition discover := discovery_keys.
  Definition invalidate := invalidate_keys.
  Definition invalidated := invalidate.
  Definition merge_region := merge_discovered.
End IncrementalCode.

Module Incremental (L : WLATTICE) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM L)
    (RS : SYSTEM L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L LB RS Sol) <: INCREMENTAL L LB Top S RS R Sol Checker Least.
  Include IncrementalCode L S RS R Sol Checker.
  Include INCREMENTAL_SPEC L S RS R Sol Checker.
  Include SourceBindingFacts L S Checker.
  Include SourceRowFacts L S.
  Module TopFacts := SourceTopFacts L Top S.

  (** Initialization has no stored value at any key. *)
  Lemma value_init : forall x, value init x = None.
  Proof.
    intro x; unfold value, lookup, init; cbn [inc_values].
    rewrite PTrie.get_empty; reflexivity.
  Qed.

  (** The empty checked region is sound and below every post-solution. *)
  Lemma init_inv : forall p, inv p init /\ least_on p init.
  Proof.
    intro p; split.
    - split.
      + intros r y x Hrow Hwrite [v Hvalue] Hkey.
        rewrite value_init in Hvalue; discriminate Hvalue.
      + intros r y Hrow Hwrite [v Hvalue].
        rewrite value_init in Hvalue; discriminate Hvalue.
    - intros s Hpost x v Hvalue.
      rewrite value_init in Hvalue; discriminate Hvalue.
  Qed.

  Lemma present_spec : forall st x, present st x = true <-> dom st x.
  Proof.
    intros st x; unfold present, dom.
    destruct (value st x) as [v|] eqn:Hvalue.
    - split; [intros _; exists v; reflexivity|intros _; reflexivity].
    - split; [discriminate|intros [v Hvalue']; discriminate Hvalue'].
  Qed.

  Lemma missing_spec : forall st x, missing st x = true <-> value st x = None.
  Proof.
    intros st x; unfold missing, present.
    destruct (value st x); cbn; split; intro H; congruence.
  Qed.

  Lemma active_spec : forall p st known r,
    active p st known r = true <->
    exists x, In x (row_writes p r) /\ value st x = None /\ In x known.
  Proof.
    intros p st known r; unfold active; rewrite existsb_exists; split.
    - intros [x [Hx Hactive]].
      apply andb_true_iff in Hactive as [Hmissing Hknown].
      exists x; repeat split; [exact Hx|now apply missing_spec|now apply mem_spec].
    - intros [x [Hx [Hmissing Hknown]]].
      exists x; split; [exact Hx|apply andb_true_iff; split].
      + now apply missing_spec.
      + now apply mem_spec.
  Qed.

  Lemma discovery_seed_spec : forall st roots x,
    In x (discovery_seed st roots) <-> In x roots /\ value st x = None.
  Proof.
    intros st roots x; unfold discovery_seed.
    rewrite (footprint_adds_spec S.key_eqb (missing st) key_eqb_true).
    cbn [In]; rewrite missing_spec; tauto.
  Qed.

  Lemma discovery_keys_missing : forall p roots st x,
    In x (discovery_keys p roots st) -> value st x = None.
  Proof.
    intros p roots st x Hx; apply missing_spec.
    unfold discovery_keys, plan, footprint_run in Hx.
    apply (footprint_close_allowed S.key_eqb (row_writes p) (row_keys p)
      (missing st) key_eqb_true (length (S.rows p)) (discovery_seed st roots)
      (S.rows p)); [|exact Hx].
    intros y Hy; apply discovery_seed_spec in Hy; apply missing_spec; tauto.
  Qed.

  Lemma discovery_roots : forall p roots st x,
    In x roots -> dom st x \/ In x (discovery_keys p roots st).
  Proof.
    intros p roots st x Hx; destruct (value st x) as [v|] eqn:Hvalue.
    - left; exists v; exact Hvalue.
    - right; unfold discovery_keys, plan, footprint_run.
      apply (footprint_close_seed S.key_eqb (row_writes p) (row_keys p)
        (missing st) key_eqb_true).
      apply discovery_seed_spec; auto.
  Qed.

  Lemma region_for_spec : forall p st xs r,
    In r (region_for p st xs) <->
    In r (S.rows p) /\
      exists x, In x (row_writes p r) /\ value st x = None /\ In x xs.
  Proof.
    intros p st xs r; unfold region_for; rewrite filter_In, active_spec; reflexivity.
  Qed.

  Lemma region_rows : forall p roots st r,
    In r (region p roots st) -> In r (S.rows p).
  Proof.
    unfold region.
    intros p roots st r Hr; apply region_for_spec in Hr; tauto.
  Qed.

  Definition discovery_region_rows := region_rows.

  Lemma region_new : forall p roots st r,
    In r (region p roots st) -> exists y, In y (S.writes p r) /\ ~ dom st y.
  Proof.
    unfold region.
    intros p roots st r Hr; apply region_for_spec in Hr.
    destruct Hr as [_ [x [Hx [Hnone _]]]].
    exists x; split; [exact Hx|].
    intros [v Hvalue]; rewrite Hnone in Hvalue; discriminate Hvalue.
  Qed.

  Definition discovery_region_new := region_new.

  (** This closure fact has no wf or inv precondition. *)
  Lemma discovery_region_support : forall p roots st r x,
    In r (discovery_region p roots st) -> In x (row_keys p r) ->
    dom st x \/ In x (discovery_keys p roots st).
  Proof.
    intros p roots st r x Hr Hx; destruct (value st x) as [v|] eqn:Hvalue.
    - left; exists v; exact Hvalue.
    - right; apply region_for_spec in Hr as [Hr [y [Hy [_ Hknown]]]].
      unfold discovery_keys, plan.
      apply (footprint_run_closed S.key_eqb (row_writes p) (row_keys p)
        (missing st) key_eqb_true (discovery_seed st roots) (S.rows p) r x).
      + exact Hr.
      + apply (footprint_active_spec S.key_eqb (row_writes p) key_eqb_true).
        exists y; split; [exact Hy|exact Hknown].
      + exact Hx.
      + apply missing_spec; exact Hvalue.
  Qed.

  Lemma discover_closed : forall p roots st, inv p st ->
    closed p (fun x => dom st x \/ In x (discover p roots st)).
  Proof.
    unfold discover.
    intros p roots st [Hclosed Hpost] r y x Hr Hy [Hold|Hnew] Hx.
    - left; eapply Hclosed; eauto.
    - apply (discovery_region_support p roots st r x); [|exact Hx].
      apply region_for_spec; split; [exact Hr|].
      exists y; repeat split; [exact Hy| |exact Hnew].
      apply (discovery_keys_missing p roots st y Hnew).
  Qed.

  Definition discovery_closed := discover_closed.

  (** Unlike raw trie lookup, validated lookup exposes exactly the requested payload key. *)
  Lemma value_cell : forall st x v,
    value st x = Some v -> PTrieCode.get (S.key_code x) (inc_values st) = Some (x, v).
  Proof.
    intros st x v; unfold value, lookup.
    destruct (PTrieCode.get (S.key_code x) (inc_values st)) as [[y w]|] eqn:Hget;
      [|discriminate].
    destruct (S.key_eqb_spec x y) as [->|Hneq]; [|discriminate].
    intro Hvalue; injection Hvalue as <-; reflexivity.
  Qed.

  Lemma normalize_values_value : forall st x,
    value (normalize_values st) x = value st x.
  Proof.
    intros st x; unfold value, normalize_values, canonical_values; cbn [inc_values].
    apply prune_values_lookup.
    - intros path y v Hin; now apply PTrie.elements_spec in Hin.
    - intro y; reflexivity.
  Qed.

  Lemma merge_old_value : forall st xs m x v,
    (forall y, In y xs -> value st y = None) -> value st x = Some v ->
    value (merge_discovered st xs m) x = Some v.
  Proof.
    intros st xs m x v Hmissing Hvalue.
    unfold value, merge_discovered; cbn [inc_values]; rewrite fill_lookup.
    change (Bindings.mem x xs) with (mem x xs).
    destruct (mem x xs) eqn:Hmem; [|exact Hvalue].
    apply mem_spec in Hmem; specialize (Hmissing x Hmem); congruence.
  Qed.

  Lemma merge_old_look : forall st xs m x,
    (forall y, In y xs -> value st y = None) -> dom st x ->
    look (merge_discovered st xs m) x = look st x.
  Proof.
    intros st xs m x Hmissing [v Hvalue]; unfold look.
    rewrite (merge_old_value st xs m x v Hmissing Hvalue), Hvalue; reflexivity.
  Qed.

  Lemma merge_dom : forall st xs m x,
    dom (merge_discovered st xs m) x <-> dom st x \/ In x xs.
  Proof.
    intros st xs m x; unfold dom, value, merge_discovered; cbn [inc_values].
    rewrite fill_lookup.
    change (Bindings.mem x xs) with (mem x xs).
    destruct (mem x xs) eqn:Hmem.
    - split.
      + intros _; right; now apply mem_spec.
      + intros _; exists (Checker.look m x); reflexivity.
    - split.
      + intros [v Hv]; left; exists v; exact Hv.
      + intros [[v Hv]|Hin]; [exists v; exact Hv|].
        pose proof (proj2 (mem_spec x xs) Hin) as Htrue.
        change (mem x xs = true) in Htrue; congruence.
  Qed.

  Lemma merge_new_look : forall st xs m x,
    In x xs -> look (merge_discovered st xs m) x = Checker.look m x.
  Proof.
    intros st xs m x Hin; unfold look, value, merge_discovered; cbn [inc_values].
    rewrite fill_lookup, (proj2 (mem_spec x xs) Hin); reflexivity.
  Qed.

  Lemma freeze_values_spec : forall st xs x v,
    In (x, v) (freeze_values st xs) <-> In x xs /\ value st x = Some v.
  Proof.
    intros st xs x v; unfold freeze_values; rewrite in_flat_map; split.
    - intros [y [Hy Hin]].
      destruct (value st y) as [w|] eqn:Hvalue; cbn [In] in Hin; [|contradiction].
      destruct Hin as [Heq|Hin]; [|contradiction].
      inversion Heq; subst; split; assumption.
    - intros [Hx Hvalue]; exists x; split; [exact Hx|].
      rewrite Hvalue; now left.
  Qed.

  Lemma frozen_for_rows_sound : forall p rs st x v,
    In (x, v) (frozen_for_rows p rs st) -> value st x = Some v.
  Proof.
    intros p rs st x v Hin; unfold frozen_for_rows in Hin.
    apply freeze_values_spec in Hin; tauto.
  Qed.

  Lemma frozen_for_rows_complete : forall p rs st r x v,
    In r rs -> In x (row_keys p r) -> value st x = Some v ->
    In (x, v) (frozen_for_rows p rs st).
  Proof.
    intros p rs st r x v Hr Hx Hvalue; unfold frozen_for_rows.
    apply freeze_values_spec; split; [|exact Hvalue].
    apply unique_spec, in_flat_map; exists r; auto.
  Qed.

  (** The authoritative checker sees each frozen old value exactly after restoration. *)
  Lemma restored_old_support : forall p rs st m r x v,
    In r rs -> In x (row_keys p r) -> value st x = Some v ->
    Checker.look (restore (frozen_for_rows p rs st) m) x = v.
  Proof.
    intros p rs st m r x v Hr Hx Hvalue; rewrite Checker.look_spec.
    apply restore_hit.
    - intros w Hw; apply frozen_for_rows_sound in Hw.
      rewrite Hvalue in Hw; injection Hw as Heq; symmetry; exact Heq.
    - eapply frozen_for_rows_complete; eauto.
  Qed.

  Lemma clear_buckets_value : forall xs st x,
    value (clear_new_buckets xs st) x = value st x.
  Proof.
    reflexivity.
  Qed.

  Lemma record_row_value : forall p r st x, value (record_row p r st) x = value st x.
  Proof.
    reflexivity.
  Qed.

  Lemma record_rows_value : forall p rs st x, value (record_rows p rs st) x = value st x.
  Proof.
    intros p rs; induction rs as [|r rest IH]; intros st x; cbn [record_rows fold_left].
    - reflexivity.
    - change (value (record_rows p rest (record_row p r st)) x = value st x).
      rewrite IH, record_row_value; reflexivity.
  Qed.

  Lemma finish_demand_value : forall p st xs rs m x,
    value (finish_demand p st xs rs m) x = value (merge_discovered st xs m) x.
  Proof.
    intros p st xs rs m x; unfold finish_demand.
    rewrite record_rows_value, clear_buckets_value.
    unfold value, merge_discovered; cbn [inc_values].
    rewrite !fill_lookup; change (Bindings.mem x xs) with (mem x xs).
    destruct (mem x xs); [reflexivity|].
    exact (normalize_values_value st x).
  Qed.

  Lemma finish_demand_dom : forall p st xs rs m x,
    dom (finish_demand p st xs rs m) x <-> dom st x \/ In x xs.
  Proof.
    intros p st xs rs m x; rewrite <- (merge_dom st xs m x).
    unfold dom; rewrite finish_demand_value; reflexivity.
  Qed.

  (** Value-preserving metadata changes preserve the functional invariant. *)
  Lemma inv_same_values : forall p left right,
    S.wf p -> (forall x, value left x = value right x) -> inv p left -> inv p right.
  Proof.
    intros p left right Hwf Hvalues [Hclosed Hpost].
    assert (Hdom : forall x, dom left x <-> dom right x).
    { intro x; unfold dom; rewrite Hvalues; reflexivity. }
    assert (Hlook : forall x, look left x = look right x).
    { intro x; unfold look; now rewrite Hvalues. }
    split.
    - intros r y x Hr Hy Hdy Hx; apply (proj1 (Hdom x)).
      eapply Hclosed; eauto; apply (proj2 (Hdom y)); exact Hdy.
    - intros r y Hr Hy Hdy.
      assert (Hrow : row_ok L.leb (look right) (S.target p r) (S.eval p r (look right)) =
        row_ok L.leb (look left) (S.target p r) (S.eval p r (look left))).
      { apply row_look_transport; [exact Hwf|exact Hr|].
        intros x Hx; symmetry; apply Hlook. }
      rewrite Hrow; eapply Hpost; eauto; apply (proj2 (Hdom y)); exact Hdy.
  Qed.

  (** A checked regional candidate and its frozen old support combine with the old frame. *)
  Lemma merge_checked_inv : forall p roots st m,
    S.wf p -> inv p st ->
    Checker.check_rows p (discovery_region p roots st) m = true ->
    (forall r x, In r (discovery_region p roots st) -> In x (row_keys p r) ->
      dom st x -> Checker.look m x = look st x) ->
    inv p (merge_discovered st (discovery_keys p roots st) m).
  Proof.
    intros p roots st m Hwf Hinv Hcheck Hfrozen.
    destruct Hinv as [Hclosed Hpost].
    assert (Hmissing : forall x, In x (discovery_keys p roots st) -> value st x = None).
    { exact (discovery_keys_missing p roots st). }
    split.
    - intros r y x Hr Hy Hdom Hx; apply (proj2 (merge_dom st _ m x)).
      eapply (discovery_closed p roots st (conj Hclosed Hpost));
        [exact Hr|exact Hy| |exact Hx].
      apply (proj1 (merge_dom st _ m y)); exact Hdom.
    - intros r y Hr Hy Hdom.
      destruct (value st y) as [v|] eqn:Hvalue.
      + assert (Hold : dom st y) by (exists v; exact Hvalue).
        assert (Hrow :
          row_ok L.leb (look (merge_discovered st (discovery_keys p roots st) m))
            (S.target p r)
            (S.eval p r (look (merge_discovered st (discovery_keys p roots st) m))) =
          row_ok L.leb (look st) (S.target p r) (S.eval p r (look st))).
        { apply row_look_transport; [exact Hwf|exact Hr|].
          intros x Hx; apply merge_old_look; [exact Hmissing|].
          eapply Hclosed; eauto. }
        rewrite Hrow; eapply Hpost; eauto.
      + assert (Hnew : In y (discovery_keys p roots st)).
        { apply (proj1 (merge_dom st _ m y)) in Hdom.
          destruct Hdom as [[w Hw]|Hin]; [rewrite Hvalue in Hw; discriminate Hw|exact Hin]. }
        assert (Hregion : In r (discovery_region p roots st)).
        { apply region_for_spec; split; [exact Hr|].
          exists y; repeat split; assumption. }
        assert (Hrow :
          row_ok L.leb (look (merge_discovered st (discovery_keys p roots st) m))
            (S.target p r)
            (S.eval p r (look (merge_discovered st (discovery_keys p roots st) m))) =
          row_ok L.leb (Checker.look m) (S.target p r) (S.eval p r (Checker.look m))).
        { apply row_look_transport; [exact Hwf|exact Hr|].
          intros x Hx; destruct (discovery_region_support p roots st r x Hregion Hx)
            as [Hold|Hin].
          - rewrite (merge_old_look st _ m x Hmissing Hold).
            symmetry; eapply Hfrozen; eauto.
          - apply merge_new_look; exact Hin. }
        rewrite Hrow; apply (proj1 (Checker.check_rows_iff p _ m) Hcheck r Hregion).
  Qed.

  Lemma finish_checked_inv : forall p roots st m,
    S.wf p -> inv p st ->
    Checker.check_rows p (discovery_region p roots st)
      (restore (frozen_pairs p roots st) m) = true ->
    inv p (finish_demand p st (discovery_keys p roots st)
      (discovery_region p roots st) (restore (frozen_pairs p roots st) m)).
  Proof.
    intros p roots st m Hwf Hinv Hcheck.
    eapply inv_same_values with
      (left := merge_discovered st (discovery_keys p roots st)
        (restore (frozen_pairs p roots st) m)).
    - exact Hwf.
    - intro x; symmetry; apply finish_demand_value.
    - apply merge_checked_inv; [exact Hwf|exact Hinv|exact Hcheck|].
      intros r x Hr Hx [v Hvalue]; unfold look; rewrite Hvalue.
      eapply restored_old_support; eauto.
  Qed.

  Lemma demand_inv : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') -> inv p st'.
  Proof.
    intros p pol roots fuel st o st' Hwf Hinv Hrun; unfold demand in Hrun.
    destruct (forallb (present st) roots); [inversion Hrun; subst; exact Hinv|].
    cbv zeta in Hrun.
    fold (discovery_region p roots st) in Hrun.
    fold (frozen_pairs p roots st) in Hrun.
    destruct (Sol.run (R.mk p (frozen_pairs p roots st) (discovery_region p roots st))
      pol fuel) as [m|m|why] eqn:Hsolver.
    - destruct (Checker.check_rows p (discovery_region p roots st)
        (restore (frozen_pairs p roots st) m)) eqn:Hcheck.
      + inversion Hrun; subst; apply finish_checked_inv; assumption.
      + inversion Hrun; subst; exact Hinv.
    - inversion Hrun; subst; exact Hinv.
    - inversion Hrun; subst; exact Hinv.
  Qed.

  Lemma demand_covers : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') -> forall x, In x roots -> dom st' x.
  Proof.
    intros p pol roots fuel st st' Hinv Hrun x Hx; unfold demand in Hrun.
    destruct (forallb (present st) roots) eqn:Hready.
    - inversion Hrun; subst; apply present_spec.
      exact ((proj1 (@forallb_forall _ _ _) Hready) x Hx).
    - cbv zeta in Hrun.
      fold (discovery_region p roots st) in Hrun.
      fold (frozen_pairs p roots st) in Hrun.
      destruct (Sol.run (R.mk p (frozen_pairs p roots st) (discovery_region p roots st))
        pol fuel) as [m|m|why] eqn:Hsolver; [|discriminate Hrun|discriminate Hrun].
      destruct (Checker.check_rows p (discovery_region p roots st)
        (restore (frozen_pairs p roots st) m)) eqn:Hcheck; [|discriminate Hrun].
      inversion Hrun; subst; apply (proj2 (finish_demand_dom p st _ _ _ x)).
      apply discovery_roots; exact Hx.
  Qed.

  Lemma demand_noop : forall p pol roots fuel st,
    (forall x, In x roots -> dom st x) -> demand p pol roots fuel st = (Done, st).
  Proof.
    intros p pol roots fuel st Hcovered.
    assert (Hready : forallb (present st) roots = true).
    { apply (proj2 (@forallb_forall _ _ _)).
      intros x Hx; apply present_spec, Hcovered, Hx. }
    unfold demand; now rewrite Hready.
  Qed.

  Lemma demand_rejected : forall p pol roots fuel st why st',
    demand p pol roots fuel st = (DemandRejected why, st') -> st' = st.
  Proof.
    intros p pol roots fuel st why st'; unfold demand.
    destruct (forallb (present st) roots); [discriminate|].
    set (xs := discovery_keys p roots st).
    set (rs := region_for p st xs).
    destruct (Sol.run (R.mk p (frozen_for_rows p rs st) rs) pol fuel) as [m|m|reason].
    - destruct (Checker.check_rows p rs (restore (frozen_for_rows p rs st) m));
        intro Hresult; inversion Hresult; reflexivity.
    - discriminate.
    - intro Hresult; inversion Hresult; reflexivity.
  Qed.

  (** Seeds are precisely old-present changed writes from either program. *)
  Lemma changed_seeds_spec : forall p p' ch st x,
    In x (changed_seeds p p' ch st) <-> dom st x /\
      exists r, In r ch /\ In x (S.writes p r ++ S.writes p' r).
  Proof.
    intros p p' ch st x; unfold changed_seeds.
    rewrite (footprint_adds_spec S.key_eqb (present st) key_eqb_true).
    cbn [In]; rewrite present_spec; unfold changed_keys; rewrite in_flat_map.
    change (False \/ ((exists r, In r ch /\
      In x (S.writes p r ++ S.writes p' r)) /\ dom st x) <->
      dom st x /\ exists r, In r ch /\ In x (S.writes p r ++ S.writes p' r)).
    tauto.
  Qed.

  Lemma changed_seeds_nodup : forall p p' ch st, NoDup (changed_seeds p p' ch st).
  Proof.
    intros p p' ch st; unfold changed_seeds.
    apply (footprint_adds_nodup S.key_eqb (present st) key_eqb_true); constructor.
  Qed.

  (** Every seed remains in the saturated invalidation list. *)
  Lemma invalidate_keys_seed : forall p p' ch st,
    incl (changed_seeds p p' ch st) (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st; unfold invalidate_keys.
    destruct (changed_seeds p p' ch st) as [|x xs]; cbn beta iota zeta.
    - intros y Hy; contradiction.
    - unfold footprint_run.
      apply (footprint_close_seed S.key_eqb edit_triggers edit_outputs (present st) key_eqb_true).
  Qed.

  (** Invalidation can only remove keys that were actually present. *)
  Lemma invalidate_dom : forall p p' ch st x,
    In x (invalidate p p' ch st) -> dom st x.
  Proof.
    unfold invalidate.
    intros p p' ch st x Hin; apply (proj1 (present_spec st x)).
    unfold invalidate_keys in Hin.
    destruct (changed_seeds p p' ch st) as [|y ys] eqn:Hseeds; [contradiction|].
    cbn beta iota zeta in Hin; unfold footprint_run in Hin.
    eapply (footprint_close_allowed S.key_eqb edit_triggers edit_outputs
      (present st) key_eqb_true); [|exact Hin].
    intros z Hz; apply (proj2 (present_spec st z)).
    assert (Hseed : In z (changed_seeds p p' ch st)) by (rewrite Hseeds; exact Hz).
    exact (proj1 (proj1 (changed_seeds_spec p p' ch st z) Hseed)).
  Qed.

  Definition invalidate_keys_dom := invalidate_dom.

  (** Invalidation lists each removed key once. *)
  Lemma invalidate_nodup : forall p p' ch st, NoDup (invalidate p p' ch st).
  Proof.
    unfold invalidate.
    intros p p' ch st; unfold invalidate_keys.
    destruct (changed_seeds p p' ch st) as [|x xs] eqn:Hseeds; [constructor|].
    cbn beta iota zeta; unfold footprint_run.
    apply (footprint_close_nodup S.key_eqb edit_triggers edit_outputs (present st) key_eqb_true).
    rewrite <- Hseeds; apply changed_seeds_nodup.
  Qed.

  Definition invalidate_keys_nodup := invalidate_nodup.

  (** Every activated footprint loses all of its old-present outputs. *)
  Lemma invalidate_keys_footprint : forall p p' ch st fp x y,
    In fp (edit_footprints p p' st) -> In x (edit_triggers fp) ->
    In x (invalidate_keys p p' ch st) -> In y (edit_outputs fp) -> dom st y ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st fp x y Hfp Htrigger Hbad Houtput Hdom.
    unfold invalidate_keys in Hbad |- *.
    destruct (changed_seeds p p' ch st) as [|z zs]; [contradiction|].
    cbn beta iota zeta in Hbad |- *.
    apply (footprint_run_closed S.key_eqb edit_triggers edit_outputs (present st)
      key_eqb_true (z :: zs) (edit_footprints p p' st) fp y).
    - exact Hfp.
    - apply (proj2 (footprint_active_spec S.key_eqb edit_triggers key_eqb_true _ fp)).
      exists x; split; assumption.
    - exact Houtput.
    - apply (proj2 (present_spec st y)); exact Hdom.
  Qed.

  (** Old rows propagate invalidation from reads and co-writes to every stored write. *)
  Lemma invalidate_keys_old : forall p p' ch st r x y,
    In r (S.rows p) -> In x (S.writes p r ++ S.deps p r) ->
    In x (invalidate_keys p p' ch st) -> In y (S.writes p r) -> dom st y ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st r x y Hr Hx Hbad Hy Hdom.
    eapply (invalidate_keys_footprint p p' ch st (row_footprint p r) x y).
    - unfold edit_footprints; apply in_or_app; left; apply in_map; exact Hr.
    - exact Hx.
    - exact Hbad.
    - exact Hy.
    - exact Hdom.
  Qed.

  (** New rows propagate invalidation from reads and co-writes to every stored write. *)
  Lemma invalidate_keys_new : forall p p' ch st r x y,
    In r (S.rows p') -> In x (S.writes p' r ++ S.deps p' r) ->
    In x (invalidate_keys p p' ch st) -> In y (S.writes p' r) -> dom st y ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st r x y Hr Hx Hbad Hy Hdom.
    eapply (invalidate_keys_footprint p p' ch st (row_footprint p' r) x y).
    - unfold edit_footprints; apply in_or_app; right; apply in_or_app; left.
      apply in_map; exact Hr.
    - exact Hx.
    - exact Hbad.
    - exact Hy.
    - exact Hdom.
  Qed.

  (** Listed changed writes in either program are seed invalidations. *)
  Lemma invalidate_changed : forall p p' ch st r y, In r ch ->
    (In r (S.rows p) /\ In y (S.writes p r) \/
      In r (S.rows p') /\ In y (S.writes p' r)) ->
    dom st y -> In y (invalidate p p' ch st).
  Proof.
    unfold invalidate.
    intros p p' ch st r y Hchanged Hwrite Hdom.
    apply (invalidate_keys_seed p p' ch st).
    apply (proj2 (changed_seeds_spec p p' ch st y)).
    split; [exact Hdom|]; exists r; split; [exact Hchanged|].
    apply in_or_app; destruct Hwrite as [[_ Hy]|[_ Hy]]; [now left|now right].
  Qed.

  Definition invalidate_keys_changed := invalidate_changed.

  (** A row with a retained new write cannot be one of the changed rows. *)
  Lemma retained_row_unchanged : forall p p' ch st r y,
    In r (S.rows p') -> In y (S.writes p' r) -> dom st y ->
    ~ In y (invalidate_keys p p' ch st) -> ~ In r ch.
  Proof.
    intros p p' ch st r y Hr Hy Hdom Hkeep Hchanged; apply Hkeep.
    eapply invalidate_keys_changed; [exact Hchanged|right; split; eassumption|exact Hdom].
  Qed.

  (** The retained domain remains closed for the old program. *)
  Lemma invalidate_keys_closed_old : forall p p' ch st, inv p st ->
    closed p (fun x => dom st x /\ ~ In x (invalidate_keys p p' ch st)).
  Proof.
    intros p p' ch st [Hclosed Hpost] r y x Hr Hy [Hdom Hkeep] Hx; split.
    - exact (Hclosed r y x Hr Hy Hdom Hx).
    - intro Hbad; apply Hkeep.
      exact (invalidate_keys_old p p' ch st r x y Hr Hx Hbad Hy Hdom).
  Qed.

  (** Removing the closure leaves a closed domain in the new program. *)
  Lemma invalidate_closed : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    closed p' (fun x => dom st x /\ ~ In x (invalidate p p' ch st)).
  Proof.
    unfold invalidate.
    intros p p' ch st Hcovers [Hclosed Hpost] r y x Hr' Hy' [Hdom Hkeep] Hx'.
    pose proof (retained_row_unchanged p p' ch st r y Hr' Hy' Hdom Hkeep) as Hunchanged.
    destruct (Hcovers r Hunchanged) as [Hrows Hbody].
    pose proof (proj2 Hrows Hr') as Hr.
    destruct (Hbody Hr) as [Htarget [Hdeps [Hsides Heval]]].
    assert (Hwrites : S.writes p r = S.writes p' r).
    { unfold S.writes; now rewrite Htarget, Hsides. }
    assert (Hy : In y (S.writes p r)) by (rewrite Hwrites; exact Hy').
    assert (Hx : In x (S.writes p r ++ S.deps p r)).
    { rewrite Hwrites, Hdeps; exact Hx'. }
    split.
    - exact (Hclosed r y x Hr Hy Hdom Hx).
    - intro Hbad; apply Hkeep.
      exact (invalidate_keys_new p p' ch st r x y Hr' Hx' Hbad Hy' Hdom).
  Qed.

  Definition invalidate_keys_closed := invalidate_closed.

  (** Metadata retirement does not alter exact value deletion. *)
  Lemma edit_value : forall p p' ch st x,
    value (edit p p' ch st) x =
      if existsb (S.key_eqb x) (invalidate p p' ch st) then None else value st x.
  Proof.
    unfold invalidate.
    intros p p' ch st x; unfold edit.
    destruct (invalidate_keys p p' ch st) as [|y bad]; [reflexivity|].
    unfold value; cbn [inc_values]; apply lookup_remove_keys.
  Qed.

  Definition edit_value_keys : forall p p' ch st x,
    value (edit p p' ch st) x =
      if mem x (invalidate_keys p p' ch st) then None else value st x := edit_value.

  (** Retained values are exactly old values outside the invalidation list. *)
  Lemma edit_dom_keys : forall p p' ch st x,
    dom (edit p p' ch st) x <->
      dom st x /\ ~ In x (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st x; unfold dom; rewrite edit_value_keys.
    destruct (mem x (invalidate_keys p p' ch st)) eqn:Hmem.
    - split.
      + intros [v Hvalue]; discriminate Hvalue.
      + intros [_ Hkeep]; exfalso; apply Hkeep.
        apply (proj1 (mem_spec x (invalidate_keys p p' ch st))); exact Hmem.
    - split.
      + intro Hvalue; split; [exact Hvalue|].
        intro Hin.
        pose proof (proj2 (mem_spec x (invalidate_keys p p' ch st)) Hin) as Htrue.
        change (mem x (invalidate_keys p p' ch st) = true) in Htrue; congruence.
      + intros [Hvalue _]; exact Hvalue.
  Qed.

  (** The public invalidation inventory equals the actual removed domain, on all states. *)
  Lemma invalidated_spec : forall p p' ch st x,
    In x (invalidated p p' ch st) <-> dom st x /\ ~ dom (edit p p' ch st) x.
  Proof.
    unfold invalidated, invalidate.
    intros p p' ch st x; split.
    - intro Hin; split; [eapply invalidate_keys_dom; exact Hin|].
      intro Hnew; apply (proj1 (edit_dom_keys p p' ch st x)) in Hnew as [_ Hkeep].
      exact (Hkeep Hin).
    - intros [Hold Hremoved].
      destruct (mem x (invalidate_keys p p' ch st)) eqn:Hmem.
      + apply (proj1 (mem_spec x (invalidate_keys p p' ch st))); exact Hmem.
      + exfalso; apply Hremoved; apply (proj2 (edit_dom_keys p p' ch st x)).
        split; [exact Hold|].
        intro Hin.
        pose proof (proj2 (mem_spec x (invalidate_keys p p' ch st)) Hin) as Htrue.
        change (mem x (invalidate_keys p p' ch st) = true) in Htrue; congruence.
  Qed.

  Definition invalidated_keys_spec := invalidated_spec.

  (** Values at retained keys agree pointwise with their old lookups. *)
  Lemma edit_look_kept : forall p p' ch st x,
    ~ In x (invalidate_keys p p' ch st) -> look (edit p p' ch st) x = look st x.
  Proof.
    intros p p' ch st x Hkeep; unfold look; rewrite edit_value_keys.
    destruct (mem x (invalidate_keys p p' ch st)) eqn:Hmem; [|reflexivity].
    exfalso; apply Hkeep.
    apply (proj1 (mem_spec x (invalidate_keys p p' ch st))); exact Hmem.
  Qed.

  (** Unchanged retained rows keep their accepted contributions under the edited lookup. *)
  Lemma edit_frame : forall p p' ch st, S.wf p' -> edit_covers p p' ch -> inv p st ->
    post_on p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hwf Hcovers Hinv r y Hr' Hy' Hnew.
    apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew as [Hdom Hkeep].
    pose proof (retained_row_unchanged p p' ch st r y Hr' Hy' Hdom Hkeep) as Hunchanged.
    destruct (Hcovers r Hunchanged) as [Hrows Hbody].
    pose proof (proj2 Hrows Hr') as Hr.
    destruct (Hbody Hr) as [Htarget [Hdeps [Hsides Heval]]].
    assert (Hy : In y (S.writes p r)).
    { unfold S.writes; rewrite Htarget, Hsides; exact Hy'. }
    pose proof (proj2 Hinv r y Hr Hy Hdom) as Hrow.
    rewrite Htarget, Heval in Hrow.
    assert (Hagree : forall x, In x (row_keys p' r) ->
      look st x = look (edit p p' ch st) x).
    { intros x Hx; symmetry; apply edit_look_kept.
      exact (proj2 (invalidate_keys_closed p p' ch st Hcovers Hinv r y x
        Hr' Hy' (conj Hdom Hkeep) Hx)). }
    rewrite (row_look_transport p' r (look st) (look (edit p p' ch st))
      Hwf Hr' Hagree) in Hrow.
    exact Hrow.
  Qed.

  Definition edit_frame_keys := edit_frame.

  Lemma edit_inv : forall p p' ch st,
    S.wf p' -> edit_covers p p' ch -> inv p st -> inv p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hwf Hcovers Hinv; split.
    - intros r y x Hr Hy Hnew Hx; apply (proj2 (edit_dom_keys p p' ch st x)).
      apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew.
      exact (invalidate_keys_closed p p' ch st Hcovers Hinv r y x Hr Hy Hnew Hx).
    - exact (edit_frame_keys p p' ch st Hwf Hcovers Hinv).
  Qed.

  Lemma edit_keeps : forall p p' ch st x v,
    value (edit p p' ch st) x = Some v -> value st x = Some v.
  Proof.
    intros p p' ch st x v Hvalue; rewrite edit_value_keys in Hvalue.
    destruct (mem x (invalidate_keys p p' ch st)); [discriminate Hvalue|exact Hvalue].
  Qed.

  (** Restricted least solving with old least seeds bounds every raw candidate value. *)
  Lemma regional_run_below : forall p pol roots fuel st m,
    S.wf p -> S.monotone p -> Least.widening_free pol -> least_on p st ->
    Sol.run (R.mk p (frozen_pairs p roots st) (discovery_region p roots st))
      pol fuel = Solved m ->
    forall upper, S.post_solution p upper -> forall x,
      L.leb (look_or S.key_code L.bot m x) (upper x) = true.
  Proof.
    intros p pol roots fuel st m Hwf Hmono Hfree Hleast Hrun upper Hpost x.
    pose proof (discovery_region_rows p roots st) as Hrows.
    assert (Hseeds : forall y v, In (y, v) (frozen_pairs p roots st) ->
      L.leb v (upper y) = true).
    { intros y v Hin; apply (Hleast upper Hpost y v).
      exact (frozen_for_rows_sound p (discovery_region p roots st) st y v Hin). }
    eapply (Least.run_least
      (R.mk p (frozen_pairs p roots st) (discovery_region p roots st))
      pol fuel m upper).
    - apply R.mk_wf; [exact Hwf|exact Hrows].
    - apply R.mk_monotone; [exact Hmono|exact Hrows].
    - exact Hfree.
    - exact Hrun.
    - apply R.restrict_complete; [exact Hpost|exact Hrows|exact Hseeds].
  Qed.

  (** Restored candidate bindings and retained old bindings both remain globally bounded. *)
  Lemma finish_demand_least : forall p roots st m,
    least_on p st ->
    (forall upper, S.post_solution p upper -> forall x,
      L.leb (look_or S.key_code L.bot m x) (upper x) = true) ->
    least_on p (finish_demand p st (discovery_keys p roots st)
      (discovery_region p roots st) (restore (frozen_pairs p roots st) m)).
  Proof.
    intros p roots st m Hleast Hcandidate upper Hpost x v Hvalue.
    rewrite finish_demand_value in Hvalue.
    unfold value, merge_discovered in Hvalue; cbn [inc_values] in Hvalue.
    rewrite fill_lookup in Hvalue.
    destruct (Bindings.mem x (discovery_keys p roots st)) eqn:Hmem.
    - injection Hvalue as <-; rewrite Checker.look_spec.
      apply restore_below.
      + exact (Hcandidate upper Hpost).
      + intros y w Hin; apply (Hleast upper Hpost y w).
        exact (frozen_for_rows_sound p (discovery_region p roots st) st y w Hin).
    - exact (Hleast upper Hpost x v Hvalue).
  Qed.

  Lemma demand_least : forall p pol roots fuel st o st', S.wf p -> S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  Proof.
    intros p pol roots fuel st o st' Hwf Hmono Hfree Hinv Hleast Hrun.
    unfold demand in Hrun.
    destruct (forallb (present st) roots); [inversion Hrun; subst; exact Hleast|].
    cbv zeta in Hrun.
    fold (discovery_region p roots st) in Hrun.
    fold (frozen_pairs p roots st) in Hrun.
    destruct (Sol.run (R.mk p (frozen_pairs p roots st) (discovery_region p roots st))
      pol fuel) as [m|m|why] eqn:Hsolver.
    - destruct (Checker.check_rows p (discovery_region p roots st)
        (restore (frozen_pairs p roots st) m)) eqn:Hcheck.
      + inversion Hrun; subst; apply finish_demand_least; [exact Hleast|].
        exact (regional_run_below p pol roots fuel st m Hwf Hmono Hfree Hleast Hsolver).
      + inversion Hrun; subst; exact Hleast.
    - inversion Hrun; subst; exact Hleast.
    - inversion Hrun; subst; exact Hleast.
  Qed.

  (** State-domain closedness is the Boolean support condition of the shared helper. *)
  Lemma present_support_closed : forall p st,
    closed p (dom st) -> TopFacts.support_closed p (present st).
  Proof.
    intros p st Hclosed r y x Hr Hy HE Hx; apply (proj2 (present_spec st x)).
    exact (Hclosed r y x Hr Hy (proj1 (present_spec st y) HE) Hx).
  Qed.

  (** A closed partial post-solution extends to a global one by top outside its domain. *)
  Lemma top_extend_state_post : forall p kept s,
    S.wf p -> closed p (dom kept) ->
    (forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom kept y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true) ->
    S.post_solution p (TopFacts.top_extend (present kept) s).
  Proof.
    intros p kept s Hwf Hclosed Hpost; apply TopFacts.top_extend_post.
    - exact Hwf.
    - apply present_support_closed; exact Hclosed.
    - intros r y Hr Hy HE; exact (Hpost r y Hr Hy (proj1 (present_spec kept y) HE)).
  Qed.

  (** A sound stored lookup has a global post-solution extension. *)
  Lemma inv_top_post : forall p st, S.wf p -> inv p st ->
    S.post_solution p (TopFacts.top_extend (present st) (look st)).
  Proof.
    intros p st Hwf [Hclosed Hpost]; apply top_extend_state_post; assumption.
  Qed.

  (** Exact deletion preserves the old-program closure on the edited domain. *)
  Lemma edit_closed_old : forall p p' ch st, inv p st -> closed p (dom (edit p p' ch st)).
  Proof.
    intros p p' ch st Hinv r y x Hr Hy Hnew Hx.
    apply (proj2 (edit_dom_keys p p' ch st x)).
    apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew.
    exact (invalidate_keys_closed_old p p' ch st Hinv r y x Hr Hy Hnew Hx).
  Qed.

  (** A retained old write excludes its row from the changed list. *)
  Lemma retained_old_row_unchanged : forall p p' ch st r y,
    In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
    ~ In y (invalidate_keys p p' ch st) -> ~ In r ch.
  Proof.
    intros p p' ch st r y Hr Hy Hdom Hkeep Hchanged; apply Hkeep.
    eapply invalidate_keys_changed; [exact Hchanged|left; split; eassumption|exact Hdom].
  Qed.

  (** New global post-solutions satisfy unchanged old rows touching retained keys. *)
  Lemma new_post_retained_old : forall p p' ch st s,
    edit_covers p p' ch -> S.post_solution p' s ->
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom (edit p p' ch st) y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  Proof.
    intros p p' ch st s Hcovers Hpost r y Hr Hy Hnew.
    apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew as [Hdom Hkeep].
    pose proof (retained_old_row_unchanged p p' ch st r y Hr Hy Hdom Hkeep) as Hunchanged.
    destruct (Hcovers r Hunchanged) as [Hrows Hbody].
    destruct (Hbody Hr) as [Htarget [Hdeps [Hsides Heval]]].
    rewrite Htarget, Heval; apply Hpost; apply (proj1 Hrows); exact Hr.
  Qed.

  Lemma edit_least : forall p p' ch st, S.wf p -> edit_covers p p' ch ->
    inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hwf Hcovers Hinv Hleast s Hpost x v Hvalue.
    assert (Hpatched : S.post_solution p
      (TopFacts.top_extend (present (edit p p' ch st)) s)).
    { apply top_extend_state_post; [exact Hwf|apply edit_closed_old; exact Hinv|].
      exact (new_post_retained_old p p' ch st s Hcovers Hpost). }
    pose proof (Hleast (TopFacts.top_extend (present (edit p p' ch st)) s) Hpatched x v
      (edit_keeps p p' ch st x v Hvalue)) as Hbound.
    assert (Hpresent : present (edit p p' ch st) x = true).
    { apply (proj2 (present_spec (edit p p' ch st) x)); exists v; exact Hvalue. }
    rewrite (TopFacts.top_extend_on (present (edit p p' ch st)) s x Hpresent) in Hbound.
    exact Hbound.
  Qed.

  Lemma from_scratch_agrees : forall p st s x v, S.wf p -> S.monotone p ->
    inv p st -> least_on p st -> least_solution p s -> value st x = Some v ->
    L.leb (s x) v = true /\ L.leb v (s x) = true.
  Proof.
    intros p st s x v Hwf Hmono Hinv Hleast [Hpost Hglobal] Hvalue; split.
    - pose proof (inv_top_post p st Hwf Hinv) as Hextended.
      pose proof (Hglobal (TopFacts.top_extend (present st) (look st)) Hextended x) as Hbound.
      assert (Hpresent : present st x = true).
      { apply (proj2 (present_spec st x)); exists v; exact Hvalue. }
      rewrite (TopFacts.top_extend_on (present st) (look st) x Hpresent) in Hbound.
      unfold look in Hbound; rewrite Hvalue in Hbound; exact Hbound.
    - exact (Hleast s Hpost x v Hvalue).
  Qed.

End Incremental.

Module IncrementalT (L : WLATTICE_T) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM_T L)
    (RS : SYSTEM_T L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT_T L S RS) (Sol : SOLVER_T L RS) (Checker : CHECK_T L S)
    (Least : SOLVER_LEAST L LB RS Sol) <: INCREMENTAL_ALL L LB Top S RS R Sol Checker Least.
  Include Incremental L LB Top S RS R Sol Checker Least.
  TimeFun init.
  TimeFun snapshot_get.
  TimeFun snapshot_set.
  TimeFun snapshot_record.
  TimeFun lookup.
  TimeFun value.
  TimeFun present.
  TimeFun missing.
  TimeFun mem.
  TimeFun row_writes.
  TimeFun row_keys.
  TimeFun active.
  TimeFun discovery_seed.
  TimeFun plan.
  TimeFun discovery_keys.
  TimeFun region_for.
  TimeFun discovery_region.
  TimeFun unique.
  TimeFun freeze_values.
  TimeFun frozen_for_rows.
  TimeFun frozen_pairs.
  TimeFun restore.
  TimeFun fill.
  TimeFun merge_discovered.
  TimeFun prune_values.
  TimeFun canonical_values.
  TimeFun normalize_values.
  TimeFun remove_keys.
  TimeFun remove_buckets.
  TimeFun clear_new_buckets.
  TimeFun push_entry.
  TimeFun record_row.
  TimeFun record_rows.
  TimeFun finish_demand.
  TimeFun demand.
  TimeFun row_footprint.
  TimeFun snapshot_footprint.
  TimeFun edit_footprints.
  TimeFun changed_keys.
  TimeFun changed_seeds.
  TimeFun invalidate_keys.
  TimeFun retire_snapshot.
  TimeFun edit.
  TimeFun invalidate.
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

  (** Stored bindings and retained groups agree with their trie inventories. *)
  Definition state_ok (st : state) : Prop :=
    (forall x, (In x (stored st) <-> dom st x)) /\
    (NoDup (stored st)) /\
    (forall id ss, In (id, ss) (snapshots st) ->
    id = S.key_code (snapshot_owner ss) /\ In (snapshot_owner ss) (snapshot_writes ss)) /\
    (forall x id, In id (infl_at st x) ->
    exists ss, In (id, ss) (snapshots st)) /\
    (forall id ss, In (id, ss) (snapshots st) ->
    snapshot_live ss = true -> forall x, In x (snapshot_writes ss) -> dom st x) /\
    (forall x id,
    length (filter (Pos.eqb id) (cowrite_at st x)) =
    fold_right (fun iss n =>
      if (Pos.eqb id (fst iss) && snapshot_live (snd iss))%bool then
        length (filter (S.key_eqb x) (snapshot_writes (snd iss))) + n else n)
      0 (snapshots st)) /\
    (snapshot_mass st =
    fold_right Nat.add 0 (map (fun x => length (cowrite_at st x)) (stored st))) /\
    (forall id ss, In (id, ss) (snapshots st) ->
    Pos.size_nat id <= kwidth st).

  (** The independent representation fields determine mass and identifier widths. *)
  Module Inventory := SourceBindingInventory L S Checker.

  Module Core.
    Definition state_core (st : state) : Prop :=
      Inventory.canonical (inc_values st) /\
      (forall id ss, snapshot_get id st = Some ss ->
        id = S.key_code (snapshot_owner ss) /\
        In (snapshot_owner ss) (snapshot_writes ss)) /\
      (forall x id, In id (infl_at st x) ->
        exists ss, snapshot_get id st = Some ss) /\
      (forall id ss, snapshot_get id st = Some ss -> snapshot_live ss = true ->
        forall x, In x (snapshot_writes ss) -> dom st x) /\
      (forall x id, length (filter (Pos.eqb id) (cowrite_at st x)) =
        match snapshot_get id st with
        | Some ss => if snapshot_live ss
            then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0
        | None => 0
        end).

    Lemma snapshot_get_elements : forall st id ss,
      snapshot_get id st = Some ss <-> In (id, ss) (snapshots st).
    Proof.
      intros st id ss; unfold snapshot_get, snapshots; symmetry.
      apply PTrie.elements_spec.
    Qed.

    Lemma snapshot_ids_nodup : forall st, NoDup (map fst (snapshots st)).
    Proof.
      intro st; unfold snapshots; apply PTrie.elements_nodup.
    Qed.

    (** The public occurrence fold selects one unique snapshot. *)
    Lemma snapshot_count_lookup : forall st x id,
      fold_right (fun iss n =>
        if (Pos.eqb id (fst iss) && snapshot_live (snd iss))%bool then
          length (filter (S.key_eqb x) (snapshot_writes (snd iss))) + n else n)
        0 (snapshots st) =
      match snapshot_get id st with
      | Some ss => if snapshot_live ss
          then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0
      | None => 0
      end.
    Proof.
      intros st x id; rewrite finite_fold_choice.
      unfold snapshot_get, snapshots.
      rewrite <- (trie_selected_sum _ (inc_snapshots st) id
        (fun ss => if snapshot_live ss
          then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0)).
      apply finite_sum_ext; intros [q ss] Hin; cbn [fst snd].
      destruct (Pos.eqb id q), (snapshot_live ss); reflexivity.
    Qed.

    Lemma state_ok_core : forall st, state_ok st -> state_core st.
    Proof.
      intros st [Hstored [Hnodup [Howner [Hrefs [Hlive [Hcounts [Hmass Hwidth]]]]]]].
      split; [apply Inventory.canonical_of_inventory; assumption|].
      split.
      - intros id ss Hget; apply Howner; now apply snapshot_get_elements.
      - split.
        + intros x id Hin; destruct (Hrefs x id Hin) as [ss Hss].
          exists ss; now apply snapshot_get_elements.
        + split.
          * intros id ss Hget; apply Hlive with (id := id).
            now apply snapshot_get_elements.
          * intros x id; rewrite Hcounts; apply snapshot_count_lookup.
    Qed.

    (** Exact occurrence counts imply that every co-write identifier resolves. *)
    Lemma core_cowrite_ids : forall st, state_core st -> forall x,
      incl (cowrite_at st x) (map fst (snapshots st)).
    Proof.
      intros st [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]] x id Hin.
      destruct (snapshot_get id st) as [ss|] eqn:Hget.
      - apply in_map_iff; exists (id, ss); split; [reflexivity|].
        now apply snapshot_get_elements.
      - pose proof (Hcounts x id) as Hzero; rewrite Hget in Hzero.
        assert (Hfilter : In id (filter (Pos.eqb id) (cowrite_at st x))).
        { apply filter_In; split; [exact Hin|apply Pos.eqb_refl]. }
        apply length_zero_iff_nil in Hzero; rewrite Hzero in Hfilter; contradiction.
    Qed.

    (** The representation's mass equation follows by counting each occurrence once. *)
    Lemma state_core_mass : forall st, state_core st ->
      snapshot_mass st =
        fold_right Nat.add 0 (map (fun x => length (cowrite_at st x)) (stored st)).
    Proof.
      intros st Hcore.
      pose proof Hcore as [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]].
      assert (Hbucket : forall x, length (cowrite_at st x) =
        finite_sum (fun entry => if snapshot_live (snd entry)
          then length (filter (S.key_eqb x) (snapshot_writes (snd entry))) else 0)
          (snapshots st)).
      { intro x.
        rewrite <- (histogram_length Pos.eqb Pos.eqb_eq (map fst (snapshots st))
          (cowrite_at st x) (snapshot_ids_nodup st) (core_cowrite_ids st Hcore x)).
        change (finite_sum (fun id => length (filter (Pos.eqb id) (cowrite_at st x)))
          (map fst (snapshots st)) =
          finite_sum (fun entry => if snapshot_live (snd entry)
            then length (filter (S.key_eqb x) (snapshot_writes (snd entry))) else 0)
            (snapshots st)).
        rewrite finite_sum_map; apply finite_sum_ext; intros [id ss] Hin; cbn [fst snd].
        rewrite Hcounts, (proj2 (snapshot_get_elements st id ss) Hin); reflexivity. }
      unfold snapshot_mass; rewrite finite_fold_choice; symmetry.
      change (finite_sum (fun x => length (cowrite_at st x)) (stored st) =
        finite_sum (fun entry => if snapshot_live (snd entry)
          then length (snapshot_writes (snd entry)) else 0) (snapshots st)).
      transitivity (finite_sum (fun x => finite_sum
        (fun entry => if snapshot_live (snd entry)
          then length (filter (S.key_eqb x) (snapshot_writes (snd entry))) else 0)
        (snapshots st)) (stored st)).
      - apply finite_sum_ext; intros x Hin; apply Hbucket.
      - rewrite finite_sum_swap; apply finite_sum_ext; intros [id ss] Hin; cbn [fst snd].
        destruct (snapshot_live ss) eqn:Hss.
        + apply histogram_length; [exact Inventory.key_eqb_true| |].
          * apply Inventory.raw_keys_nodup; exact Hcanonical.
          * intros x Hx; apply (proj2 (Inventory.raw_keys_dom _ Hcanonical x)).
            exact (Hlive id ss (proj2 (snapshot_get_elements st id ss) Hin) Hss x Hx).
        + apply finite_sum_zero.
    Qed.

    (** Snapshot ownership places every identifier within the recorded key width. *)
    Lemma state_core_width : forall st, state_core st -> forall id ss,
      In (id, ss) (snapshots st) -> Pos.size_nat id <= kwidth st.
    Proof.
      intros st [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]] id ss Hin.
      destruct (Howner id ss (proj2 (snapshot_get_elements st id ss) Hin)) as [Hid Hwrite].
      rewrite Hid; change (S.key_bits (snapshot_owner ss) <= kwidth st).
      unfold kwidth; apply finite_max_member; apply in_or_app; right.
      unfold snapshot_keys; apply in_flat_map; exists (id, ss); auto.
    Qed.

    Lemma state_core_ok : forall st, state_core st -> state_ok st.
    Proof.
      intros st Hcore.
      pose proof Hcore as [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]].
      split; [intro x; apply Inventory.raw_keys_dom; exact Hcanonical|].
      split; [apply Inventory.raw_keys_nodup; exact Hcanonical|].
      split.
      - intros id ss Hin; apply Howner; now apply snapshot_get_elements.
      - split.
        + intros x id Hin; destruct (Hrefs x id Hin) as [ss Hget].
          exists ss; now apply snapshot_get_elements.
        + split.
          * intros id ss Hin; apply Hlive with (id := id).
            now apply snapshot_get_elements.
          * split.
            -- intros x id; rewrite Hcounts, snapshot_count_lookup; reflexivity.
            -- split; [now apply state_core_mass|now apply state_core_width].
    Qed.

    (** In particular, empty maps satisfy all independent fields. *)
    Lemma state_core_init : state_core init.
    Proof.
      split; [apply Inventory.canonical_empty|].
      split.
      - intros id ss Hget; unfold snapshot_get, init in Hget; cbn [inc_snapshots] in Hget.
        rewrite PTrie.get_empty in Hget; discriminate Hget.
      - split.
        + intros x id Hin; unfold infl_at, init in Hin; cbn [inc_influence] in Hin.
          rewrite PTrie.get_empty in Hin; contradiction.
        + split.
          * intros id ss Hget; unfold snapshot_get, init in Hget;
              cbn [inc_snapshots] in Hget.
            rewrite PTrie.get_empty in Hget; discriminate Hget.
          * intros x id; unfold cowrite_at, snapshot_get, init;
              cbn [inc_cowrites inc_snapshots].
            now rewrite !PTrie.get_empty.
    Qed.
  End Core.

  Module Buckets.
    Definition bucket_at (buckets : PTrieCode.t (list positive)) (x : S.key)
        : list positive :=
      match PTrieCode.get (S.key_code x) buckets with
      | Some entries => entries
      | None => []
      end.

    (** One push prepends its identifier exactly at the selected key. *)
    Lemma push_entry_at : forall y id buckets x,
      bucket_at (push_entry y id buckets) x =
        if S.key_eqb x y then id :: bucket_at buckets x else bucket_at buckets x.
    Proof.
      intros y id buckets x; unfold push_entry, bucket_at.
      destruct (S.key_eqb_spec x y) as [->|Hneq].
      - rewrite PTrie.get_set_same; reflexivity.
      - rewrite PTrie.get_set_other; [reflexivity|].
        intro Heq; apply Hneq; now apply S.key_code_inj.
    Qed.

    (** A row's metadata update preserves the raw value map. *)
    Lemma record_row_values : forall p r st,
      inc_values (record_row p r st) = inc_values st.
    Proof.
      reflexivity.
    Qed.

    (** Recording any row list preserves the raw value map. *)
    Lemma record_rows_values : forall p rs st,
      inc_values (record_rows p rs st) = inc_values st.
    Proof.
      intros p rs; induction rs as [|r rest IH]; intro st; cbn [record_rows fold_left].
      - reflexivity.
      - change (inc_values (record_rows p rest (record_row p r st)) = inc_values st).
        rewrite IH, record_row_values; reflexivity.
    Qed.
  End Buckets.

  Module DemandState.
    (** Prepending one identifier per listed key preserves exact occurrence counts. *)
    Lemma push_entries_count : forall ys id buckets x q,
      length (filter (Pos.eqb q) (Buckets.bucket_at
        (fold_left (fun acc y => push_entry y id acc) ys buckets) x)) =
      length (filter (Pos.eqb q) (Buckets.bucket_at buckets x)) +
        if Pos.eqb q id then length (filter (S.key_eqb x) ys) else 0.
    Proof.
      induction ys as [|y rest IH]; intros id buckets x q.
      - cbn [fold_left filter length]; destruct (Pos.eqb q id); lia.
      - cbn [fold_left]; rewrite IH, Buckets.push_entry_at.
        cbn [filter]; destruct (S.key_eqb x y); cbn [filter];
          destruct (Pos.eqb q id); cbn [length]; lia.
    Qed.

    (** New bucket occurrences carry the recorded identifier; all others were already present. *)
    Lemma push_entries_members : forall ys id buckets x q,
      In q (Buckets.bucket_at
        (fold_left (fun acc y => push_entry y id acc) ys buckets) x) ->
      q = id \/ In q (Buckets.bucket_at buckets x).
    Proof.
      induction ys as [|y rest IH]; intros id buckets x q Hin.
      - right; exact Hin.
      - cbn [fold_left] in Hin; apply IH in Hin as [Heq|Hin]; [now left|].
        rewrite Buckets.push_entry_at in Hin; destruct (S.key_eqb x y).
        + destruct Hin as [Heq|Hin]; [left; now symmetry|now right].
        + now right.
    Qed.

    (** An absent value cannot have a live co-write membership. *)
    Lemma core_cowrite_absent : forall st x,
      Core.state_core st -> value st x = None -> cowrite_at st x = [].
    Proof.
      intros st x [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]] Hnone.
      destruct (cowrite_at st x) as [|id rest] eqn:Hbucket; [reflexivity|].
      assert (Hpositive : 0 < length (filter (Pos.eqb id) (cowrite_at st x))).
      { apply (proj2 (histogram_count_pos Pos.eqb Pos.eqb_eq id _)); rewrite Hbucket; now left. }
      rewrite Hcounts in Hpositive.
      destruct (snapshot_get id st) as [ss|] eqn:Hget; [|lia].
      destruct (snapshot_live ss) eqn:Hss; [|lia].
      apply (proj1 (histogram_count_pos S.key_eqb Inventory.key_eqb_true x _)) in Hpositive.
      destruct (Hlive id ss Hget Hss x Hpositive) as [v Hvalue].
      rewrite Hnone in Hvalue; discriminate Hvalue.
    Qed.

    (** This proof abbreviation is the existing preparation performed by finish_demand. *)
    Definition prepared_state (st : state) xs m : state :=
      clear_new_buckets xs (merge_discovered (normalize_values st) xs m).

    Lemma prepared_value : forall st xs m x,
      value (prepared_state st xs m) x =
        if Bindings.mem x xs then Some (Checker.look m x) else value st x.
    Proof.
      intros st xs m x; unfold prepared_state.
      rewrite clear_buckets_value; unfold value, merge_discovered; cbn [inc_values].
      rewrite fill_lookup; destruct (Bindings.mem x xs); [reflexivity|].
      exact (normalize_values_value st x).
    Qed.

    Lemma prepared_dom : forall st xs m x,
      dom (prepared_state st xs m) x <-> dom st x \/ In x xs.
    Proof.
      intros st xs m x; rewrite <- (merge_dom st xs m x).
      unfold dom; rewrite prepared_value.
      unfold value, merge_discovered; cbn [inc_values]; rewrite fill_lookup; reflexivity.
    Qed.

    Lemma prepared_snapshot_get : forall st xs m id,
      snapshot_get id (prepared_state st xs m) = snapshot_get id st.
    Proof.
      reflexivity.
    Qed.

    Lemma prepared_infl : forall st xs m x,
      infl_at (prepared_state st xs m) x =
        if Inventory.Bindings.mem x xs then [] else infl_at st x.
    Proof.
      intros st xs m x; unfold infl_at, prepared_state, clear_new_buckets,
        merge_discovered, normalize_values; cbn [inc_influence].
      change (match PTrieCode.get (S.key_code x)
        (Inventory.Bindings.remove_keys xs (inc_influence st)) with
        | Some ids => ids | None => [] end =
        if Inventory.Bindings.mem x xs then [] else infl_at st x).
      rewrite Inventory.raw_get_remove_keys; destruct (Inventory.Bindings.mem x xs); reflexivity.
    Qed.

    Lemma prepared_cowrite : forall st xs m x,
      cowrite_at (prepared_state st xs m) x =
        if Inventory.Bindings.mem x xs then [] else cowrite_at st x.
    Proof.
      intros st xs m x; unfold cowrite_at, prepared_state, clear_new_buckets,
        merge_discovered, normalize_values; cbn [inc_cowrites].
      change (match PTrieCode.get (S.key_code x)
        (Inventory.Bindings.remove_keys xs (inc_cowrites st)) with
        | Some ids => ids | None => [] end =
        if Inventory.Bindings.mem x xs then [] else cowrite_at st x).
      rewrite Inventory.raw_get_remove_keys; destruct (Inventory.Bindings.mem x xs); reflexivity.
    Qed.

    Lemma prepared_core : forall st xs m, Core.state_core st ->
      (forall x, In x xs -> value st x = None) -> Core.state_core (prepared_state st xs m).
    Proof.
      intros st xs m Hcore Hfresh.
      pose proof Hcore as [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]].
      split.
      - apply Inventory.fill_canonical; apply Inventory.prune_values_canonical.
      - split.
        + intros id ss Hget; rewrite prepared_snapshot_get in Hget; now apply Howner.
        + split.
          * intros x id Hin; rewrite prepared_infl in Hin.
            destruct (Inventory.Bindings.mem x xs); [contradiction|].
            destruct (Hrefs x id Hin) as [ss Hss]; exists ss; now rewrite prepared_snapshot_get.
          * split.
            -- intros id ss Hget Hss x Hx; rewrite prepared_snapshot_get in Hget.
               apply (proj2 (prepared_dom st xs m x)); left; exact (Hlive id ss Hget Hss x Hx).
            -- intros x id; rewrite prepared_cowrite, prepared_snapshot_get.
               destruct (Inventory.Bindings.mem x xs) eqn:Hmem; [|exact (Hcounts x id)].
               pose proof (core_cowrite_absent st x Hcore
                 (Hfresh x (proj1 (Inventory.mem_spec x xs) Hmem))) as Hempty.
               rewrite <- (Hcounts x id), Hempty; reflexivity.
    Qed.

    Definition previous_writes (st : state) id : list S.key :=
      match snapshot_get id st with
      | Some ss => if snapshot_live ss then snapshot_writes ss else []
      | None => []
      end.

    Definition recorded_snapshot (st : state) owner writes : incremental_snapshot S.key :=
      {| snapshot_owner := owner;
         snapshot_writes := writes ++ previous_writes st (S.key_code owner);
         snapshot_live := true |}.

    Lemma record_row_snapshot_get : forall p r st q,
      snapshot_get q (record_row p r st) =
        if Pos.eqb q (S.key_code (S.target p r))
        then Some (recorded_snapshot st (S.target p r) (row_writes p r))
        else snapshot_get q st.
    Proof.
      intros p r st q; unfold snapshot_get, record_row, snapshot_record, snapshot_set.
      cbn [inc_snapshots]; destruct (Pos.eqb q (S.key_code (S.target p r))) eqn:Hq.
      - apply Pos.eqb_eq in Hq; subst q; rewrite PTrie.get_set_same; reflexivity.
      - apply Pos.eqb_neq in Hq; rewrite PTrie.get_set_other by exact Hq; reflexivity.
    Qed.

    Lemma previous_writes_dom : forall st id, Core.state_core st ->
      forall x, In x (previous_writes st id) -> dom st x.
    Proof.
      intros st id [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]] x Hin.
      unfold previous_writes in Hin; destruct (snapshot_get id st) as [ss|] eqn:Hget;
        [|contradiction].
      destruct (snapshot_live ss) eqn:Hss; [|contradiction].
      exact (Hlive id ss Hget Hss x Hin).
    Qed.

    Lemma previous_writes_count : forall st, Core.state_core st -> forall x id,
      length (filter (Pos.eqb id) (cowrite_at st x)) =
        length (filter (S.key_eqb x) (previous_writes st id)).
    Proof.
      intros st [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]] x id.
      rewrite Hcounts; unfold previous_writes; destruct (snapshot_get id st) as [ss|];
        [destruct (snapshot_live ss)|]; reflexivity.
    Qed.

    (** Recording one row preserves all independent representation fields. *)
    Lemma record_row_core : forall p r st, Core.state_core st ->
      (forall x, In x (row_writes p r) -> dom st x) ->
      Core.state_core (record_row p r st).
    Proof.
      intros p r st Hcore Hwrites.
      pose proof Hcore as [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]].
      split; [rewrite Buckets.record_row_values; exact Hcanonical|].
      split.
      - intros id ss Hget; rewrite record_row_snapshot_get in Hget.
        destruct (Pos.eqb id (S.key_code (S.target p r))) eqn:Hid.
        + apply Pos.eqb_eq in Hid; inversion Hget; subst ss; cbn [recorded_snapshot].
          split; [exact Hid|apply in_or_app; left; unfold row_writes; now left].
        + exact (Howner id ss Hget).
      - split.
        + intros x id Hin.
          change (In id (Buckets.bucket_at
            (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
              (S.deps p r) (inc_influence st)) x)) in Hin.
          apply push_entries_members in Hin as [Heq|Hin].
          * subst id; exists (recorded_snapshot st (S.target p r) (row_writes p r)).
            rewrite record_row_snapshot_get, Pos.eqb_refl; reflexivity.
          * destruct (Hrefs x id Hin) as [ss Hss].
            destruct (Pos.eqb id (S.key_code (S.target p r))) eqn:Hid.
            -- exists (recorded_snapshot st (S.target p r) (row_writes p r)).
               now rewrite record_row_snapshot_get, Hid.
            -- exists ss; now rewrite record_row_snapshot_get, Hid.
        + split.
          * intros id ss Hget Hss x Hx.
            unfold dom; rewrite record_row_value; rewrite record_row_snapshot_get in Hget.
            destruct (Pos.eqb id (S.key_code (S.target p r))) eqn:Hid.
            -- inversion Hget; subst ss; cbn [recorded_snapshot] in Hx.
               apply in_app_iff in Hx as [Hx|Hx].
               ++ exact (Hwrites x Hx).
               ++ exact (previous_writes_dom st _ Hcore x Hx).
            -- exact (Hlive id ss Hget Hss x Hx).
          * intros x id.
            change (length (filter (Pos.eqb id) (Buckets.bucket_at
              (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
                (row_writes p r) (inc_cowrites st)) x)) =
              match snapshot_get id (record_row p r st) with
              | Some ss => if snapshot_live ss
                  then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0
              | None => 0
              end).
            rewrite push_entries_count, record_row_snapshot_get.
            change (Buckets.bucket_at (inc_cowrites st) x) with (cowrite_at st x).
            destruct (Pos.eqb id (S.key_code (S.target p r))) eqn:Hid.
            -- apply Pos.eqb_eq in Hid; subst id;
                 cbn [recorded_snapshot snapshot_live snapshot_writes].
               rewrite filter_app, length_app, (previous_writes_count st Hcore).
               lia.
            -- cbn; rewrite Hcounts; lia.
    Qed.

    Lemma record_rows_core : forall p rs st, Core.state_core st ->
      (forall r, In r rs -> forall x, In x (row_writes p r) -> dom st x) ->
      Core.state_core (record_rows p rs st).
    Proof.
      intros p rs; induction rs as [|r rest IH]; intros st Hcore Hwrites.
      - exact Hcore.
      - change (Core.state_core (record_rows p rest (record_row p r st))).
        apply IH.
        + apply record_row_core; [exact Hcore|].
          intros x Hx; apply (Hwrites r); [now left|exact Hx].
        + intros q Hq x Hx; unfold dom; rewrite record_row_value.
          apply (Hwrites q); [now right|exact Hx].
    Qed.

    (** Finite discovery supplies every newly recorded row write without semantic premises. *)
    Lemma finish_demand_core : forall p roots st m, Core.state_core st ->
      Core.state_core (finish_demand p st (discovery_keys p roots st)
        (discovery_region p roots st) m).
    Proof.
      intros p roots st m Hcore.
      change (Core.state_core (record_rows p (discovery_region p roots st)
        (prepared_state st (discovery_keys p roots st) m))).
      apply record_rows_core.
      - apply prepared_core; [exact Hcore|].
        intros x Hx; exact (discovery_keys_missing p roots st x Hx).
      - intros r Hr x Hx; apply (proj2 (prepared_dom st _ m x)).
        apply (discovery_region_support p roots st r x Hr).
        apply in_or_app; now left.
    Qed.

    (** Every demand outcome preserves the exact released representation invariant. *)
    Lemma state_ok_demand : forall p pol roots fuel st o st', state_ok st ->
      demand p pol roots fuel st = (o, st') -> state_ok st'.
    Proof.
      intros p pol roots fuel st o st' Hstate Hrun; unfold demand in Hrun.
      destruct (forallb (present st) roots); [inversion Hrun; subst; exact Hstate|].
      cbv zeta in Hrun; fold (discovery_region p roots st) in Hrun.
      fold (frozen_pairs p roots st) in Hrun.
      destruct (Sol.run (R.mk p (frozen_pairs p roots st) (discovery_region p roots st))
        pol fuel) as [m|m|why] eqn:Hsolver.
      - destruct (Checker.check_rows p (discovery_region p roots st)
          (restore (frozen_pairs p roots st) m)) eqn:Hcheck.
        + inversion Hrun; subst; apply Core.state_core_ok, finish_demand_core.
          now apply Core.state_ok_core.
        + inversion Hrun; subst; exact Hstate.
      - inversion Hrun; subst; exact Hstate.
      - inversion Hrun; subst; exact Hstate.
    Qed.
  End DemandState.

  Module EditMetadata.
    Module InvFacts := Inventory.

    (** Editing removes exactly the influence buckets of invalidated keys. *)
    Lemma edit_infl_eq : forall p p' ch st x,
      infl_at (edit p p' ch st) x =
        if mem x (invalidate_keys p p' ch st) then [] else infl_at st x.
    Proof.
      intros p p' ch st x; unfold edit.
      destruct (invalidate_keys p p' ch st) as [|y bad]; [reflexivity|].
      unfold infl_at; cbn [inc_influence]; rewrite InvFacts.raw_get_remove_keys.
      change (InvFacts.Bindings.mem x (y :: bad)) with (mem x (y :: bad)).
      destruct (mem x (y :: bad)); reflexivity.
    Qed.

    (** Editing removes exactly the co-write buckets of invalidated keys. *)
    Lemma edit_cowrite_eq : forall p p' ch st x,
      cowrite_at (edit p p' ch st) x =
        if mem x (invalidate_keys p p' ch st) then [] else cowrite_at st x.
    Proof.
      intros p p' ch st x; unfold edit.
      destruct (invalidate_keys p p' ch st) as [|y bad]; [reflexivity|].
      unfold cowrite_at; cbn [inc_cowrites]; rewrite InvFacts.raw_get_remove_keys.
      change (InvFacts.Bindings.mem x (y :: bad)) with (mem x (y :: bad)).
      destruct (mem x (y :: bad)); reflexivity.
    Qed.

    (** No snapshot is touched by the empty invalidation list. *)
    Lemma retire_snapshot_nil : forall ss, retire_snapshot [] ss = ss.
    Proof.
      intros [owner writes live]; unfold retire_snapshot; cbn [snapshot_owner snapshot_writes].
      assert (Htouch : existsb (fun x => mem x []) writes = false).
      { induction writes; cbn [existsb mem]; assumption || reflexivity. }
      rewrite Htouch; destruct live; reflexivity.
    Qed.

    (** Every snapshot remains present at its identifier, with its live bit updated. *)
    Lemma snapshot_get_edit : forall p p' ch st id,
      snapshot_get id (edit p p' ch st) =
        option_map (retire_snapshot (invalidate_keys p p' ch st)) (snapshot_get id st).
    Proof.
      intros p p' ch st id; unfold edit.
      destruct (invalidate_keys p p' ch st) as [|x bad].
      - destruct (snapshot_get id st) as [ss|]; cbn [option_map];
          [now rewrite retire_snapshot_nil|reflexivity].
      - unfold snapshot_get; cbn [inc_snapshots]; apply PTrie.get_map.
    Qed.

    (** An edited snapshot has one original payload at the same identifier. *)
    Lemma snapshot_get_edit_inv : forall p p' ch st id ss',
      snapshot_get id (edit p p' ch st) = Some ss' ->
      exists ss, snapshot_get id st = Some ss /\
        ss' = retire_snapshot (invalidate_keys p p' ch st) ss.
    Proof.
      intros p p' ch st id ss' Hget; rewrite snapshot_get_edit in Hget.
      destruct (snapshot_get id st) as [ss|] eqn:Hbefore in Hget; cbn [option_map] in Hget;
        [|discriminate Hget].
      injection Hget as <-; exists ss; split; [exact Hbefore|reflexivity].
    Qed.

    (** The snapshot inventory is mapped without adding or deleting identifiers. *)
    Lemma snapshots_edit_perm : forall p p' ch st,
      Permutation (snapshots (edit p p' ch st))
        (map (fun entry => (fst entry, retire_snapshot (invalidate_keys p p' ch st) (snd entry)))
          (snapshots st)).
    Proof.
      intros p p' ch st; unfold edit.
      destruct (invalidate_keys p p' ch st) as [|x bad].
      - assert (Hmap : map (fun entry => (fst entry, retire_snapshot [] (snd entry)))
          (snapshots st) = snapshots st).
        { transitivity (map (fun entry => entry) (snapshots st)).
          - apply map_ext; intros [id ss]; cbn [fst snd]; now rewrite retire_snapshot_nil.
          - apply map_id. }
        rewrite Hmap; reflexivity.
      - unfold snapshots; cbn [inc_snapshots]; apply trie_map_elements_perm.
    Qed.

    (** Raw stored-key inventory can only shrink, even for malformed input values. *)
    Lemma stored_edit_subset : forall p p' ch st x,
      In x (stored (edit p p' ch st)) -> In x (stored st).
    Proof.
      intros p p' ch st x; unfold edit.
      destruct (invalidate_keys p p' ch st) as [|y bad]; [tauto|].
      unfold stored; cbn [inc_values]; apply InvFacts.raw_keys_remove_subset.
    Qed.

    (** Retirement preserves every recorded write key. *)
    Lemma snapshot_keys_edit_subset : forall p p' ch st x,
      In x (snapshot_keys (edit p p' ch st)) -> In x (snapshot_keys st).
    Proof.
      intros p p' ch st x Hin; unfold snapshot_keys in *.
      apply in_flat_map in Hin as [[id ss'] [Hin Hx]].
      apply (proj1 (PTrie.elements_spec _ _ id ss')) in Hin.
      change (snapshot_get id (edit p p' ch st) = Some ss') in Hin.
      apply snapshot_get_edit_inv in Hin as [ss [Hget ->]].
      apply in_flat_map; exists (id, ss); split; [|exact Hx].
      unfold snapshots; apply (proj2 (PTrie.elements_spec _ _ id ss)); exact Hget.
    Qed.

    (** Edits retain read entries of every retained key, including changed-row entries. *)
    Lemma edit_infl_keeps : forall p p' ch st x, dom (edit p p' ch st) x ->
      infl_at (edit p p' ch st) x = infl_at st x.
    Proof.
      intros p p' ch st x Hdom; rewrite edit_infl_eq.
      apply (proj1 (edit_dom_keys p p' ch st x)) in Hdom as [_ Hkeep].
      destruct (mem x (invalidate_keys p p' ch st)) eqn:Hmem; [|reflexivity].
      exfalso; apply Hkeep; apply (proj1 (mem_spec x _)); exact Hmem.
    Qed.

    (** A live snapshot propagates invalidation to each of its stored write keys. *)
    Lemma invalidate_snapshot : forall p p' ch st id ss x y,
      snapshot_get id st = Some ss -> snapshot_live ss = true ->
      In x (snapshot_writes ss) -> In x (invalidate_keys p p' ch st) ->
      In y (snapshot_writes ss) -> dom st y -> In y (invalidate_keys p p' ch st).
    Proof.
      intros p p' ch st id ss x y Hget Hlive Hx Hbad Hy Hdom.
      eapply (invalidate_keys_footprint p p' ch st (snapshot_footprint ss) x y).
      - unfold edit_footprints; apply in_or_app; right; apply in_or_app; right.
        apply in_map_iff; exists (id, ss); split; [reflexivity|].
        apply filter_In; split; [|exact Hlive].
        apply (proj2 (PTrie.elements_spec _ _ id ss)); exact Hget.
      - exact Hx.
      - exact Hbad.
      - exact Hy.
      - exact Hdom.
    Qed.

    (** A touched live snapshot has all its writes in the invalidation closure. *)
    Lemma snapshot_touch_all : forall p p' ch st id ss, Core.state_core st ->
      snapshot_get id st = Some ss -> snapshot_live ss = true ->
      existsb (fun x => mem x (invalidate_keys p p' ch st)) (snapshot_writes ss) = true ->
      forall x, In x (snapshot_writes ss) -> mem x (invalidate_keys p p' ch st) = true.
    Proof.
      intros p p' ch st id ss [_ [_ [_ [Hstored Hcounts]]]] Hget Hlive Htouch x Hx.
      apply existsb_exists in Htouch as [y [Hy Hmem]].
      apply (proj2 (mem_spec x _)).
      eapply invalidate_snapshot; [exact Hget|exact Hlive|exact Hy| |exact Hx|].
      - apply (proj1 (mem_spec y _)); exact Hmem.
      - exact (Hstored id ss Hget Hlive x Hx).
    Qed.

    (** The retained per-key count agrees with retiring its whole shared snapshot. *)
    Lemma retire_snapshot_count : forall p p' ch st id ss x, Core.state_core st ->
      snapshot_get id st = Some ss ->
      (if mem x (invalidate_keys p p' ch st) then 0 else
        if snapshot_live ss then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0) =
      (if snapshot_live (retire_snapshot (invalidate_keys p p' ch st) ss)
        then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0).
    Proof.
      intros p p' ch st id ss x Hcore Hget.
      unfold retire_snapshot; cbn [snapshot_live].
      destruct (snapshot_live ss) eqn:Hlive;
        [|destruct (mem x (invalidate_keys p p' ch st)); reflexivity].
      destruct (mem x (invalidate_keys p p' ch st)) eqn:Hmem;
        destruct (existsb (fun y => mem y (invalidate_keys p p' ch st))
          (snapshot_writes ss)) eqn:Htouch; cbn; try reflexivity.
      - symmetry; apply (histogram_count_zero S.key_eqb key_eqb_true); intro Hx.
        assert (Htrue : existsb (fun y => mem y (invalidate_keys p p' ch st))
          (snapshot_writes ss) = true).
        { apply existsb_exists; exists x; split; assumption. }
        congruence.
      - apply (histogram_count_zero S.key_eqb key_eqb_true); intro Hx.
        pose proof (snapshot_touch_all p p' ch st id ss Hcore Hget Hlive Htouch x Hx).
        congruence.
    Qed.

    (** Editing preserves the five independent representation fields. *)
    Lemma state_core_edit : forall p p' ch st,
      Core.state_core st -> Core.state_core (edit p p' ch st).
    Proof.
      intros p p' ch st Hcore.
      pose proof Hcore as [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]].
      unfold Core.state_core; split.
      - unfold edit; destruct (invalidate_keys p p' ch st) as [|x bad]; cbn [inc_values].
        + exact Hcanonical.
        + apply InvFacts.remove_keys_canonical; exact Hcanonical.
      - split.
        + intros id ss' Hget.
          apply snapshot_get_edit_inv in Hget as [ss [Hget ->]]; exact (Howner id ss Hget).
        + split.
          * intros x id Hin; rewrite edit_infl_eq in Hin.
            destruct (mem x (invalidate_keys p p' ch st)); [contradiction|].
            destruct (Hrefs x id Hin) as [ss Hget].
            exists (retire_snapshot (invalidate_keys p p' ch st) ss).
            rewrite snapshot_get_edit, Hget; reflexivity.
          * split.
            -- intros id ss' Hget Hactive x Hx.
               apply snapshot_get_edit_inv in Hget as [ss [Hget ->]].
               cbn [retire_snapshot snapshot_live] in Hactive.
               apply andb_true_iff in Hactive as [Hactive Htouch].
               apply negb_true_iff in Htouch.
               apply (proj2 (edit_dom_keys p p' ch st x)); split.
               ++ exact (Hlive id ss Hget Hactive x Hx).
               ++ intro Hbad.
                  assert (Htrue : existsb (fun y => mem y (invalidate_keys p p' ch st))
                    (snapshot_writes ss) = true).
                  { apply existsb_exists; exists x; split; [exact Hx|].
                    apply (proj2 (mem_spec x _)); exact Hbad. }
                  congruence.
            -- intros x id; rewrite edit_cowrite_eq, snapshot_get_edit.
               destruct (snapshot_get id st) as [ss|] eqn:Hget; cbn [option_map].
               ++ change (length (filter (Pos.eqb id)
                    (if mem x (invalidate_keys p p' ch st) then [] else cowrite_at st x)) =
                    if snapshot_live (retire_snapshot (invalidate_keys p p' ch st) ss)
                    then length (filter (S.key_eqb x) (snapshot_writes ss)) else 0).
                  rewrite <- (retire_snapshot_count p p' ch st id ss x Hcore Hget).
                  destruct (mem x (invalidate_keys p p' ch st)); [reflexivity|].
                  pose proof (Hcounts x id) as Hcount; now rewrite Hget in Hcount.
               ++ destruct (mem x (invalidate_keys p p' ch st)); [reflexivity|].
                  pose proof (Hcounts x id) as Hcount; now rewrite Hget in Hcount.
    Qed.

    (** Editing preserves the complete released representation invariant. *)
    Lemma state_ok_edit : forall p p' ch st, state_ok st -> state_ok (edit p p' ch st).
    Proof.
      intros p p' ch st Hstate; apply Core.state_core_ok; apply state_core_edit.
      apply Core.state_ok_core; exact Hstate.
    Qed.

    (** Visiting a snapshot removes its writes, memberships and live status. *)
    Lemma edit_snapshot_visit : forall p p' ch st id ss, state_ok st ->
      In (id, ss) (snapshots st) -> snapshot_live ss = true ->
      (exists x, In x (snapshot_writes ss) /\ In x (invalidated p p' ch st)) ->
      (forall x, In x (snapshot_writes ss) -> ~ dom (edit p p' ch st) x) /\
      (forall x, ~ In id (cowrite_at (edit p p' ch st) x)) /\
      (forall ss', In (id, ss') (snapshots (edit p p' ch st)) -> snapshot_live ss' = false).
    Proof.
      intros p p' ch st id ss Hstate Hin Hlive [x [Hx Hbad]].
      pose proof (Core.state_ok_core st Hstate) as Hcore.
      pose proof (proj2 (Core.snapshot_get_elements st id ss) Hin) as Hget.
      assert (Htouch : existsb (fun y => mem y (invalidate_keys p p' ch st))
        (snapshot_writes ss) = true).
      { apply existsb_exists; exists x; split; [exact Hx|].
        apply (proj2 (mem_spec x _)); exact Hbad. }
      pose proof (snapshot_touch_all p p' ch st id ss Hcore Hget Hlive Htouch) as Hall.
      split.
      - intros y Hy Hdom; apply (proj1 (edit_dom_keys p p' ch st y)) in Hdom as [_ Hkeep].
        apply Hkeep; apply (proj1 (mem_spec y _)); apply Hall; exact Hy.
      - split.
        + intro y; rewrite edit_cowrite_eq.
          destruct (mem y (invalidate_keys p p' ch st)) eqn:Hmem;
            [intros Hmember; contradiction|].
          intro Hmember.
          pose proof (proj2 (histogram_count_pos Pos.eqb Pos.eqb_eq id (cowrite_at st y))
            Hmember) as Hpositive.
          destruct Hcore as [_ [_ [_ [_ Hcounts]]]].
          rewrite (Hcounts y id), Hget, Hlive in Hpositive.
          apply (proj1 (histogram_count_pos S.key_eqb key_eqb_true y (snapshot_writes ss)))
            in Hpositive.
          pose proof (Hall y Hpositive); congruence.
        + intros ss' Hnew.
          apply (proj2 (Core.snapshot_get_elements (edit p p' ch st) id ss')) in Hnew.
          rewrite snapshot_get_edit, Hget in Hnew; cbn [option_map] in Hnew.
          injection Hnew as <-; cbn [retire_snapshot snapshot_live].
          rewrite Hlive, Htouch; reflexivity.
    Qed.

    (** Snapshot retirement never increases the live occurrence total. *)
    Lemma snapshot_mass_edit_le : forall p p' ch st,
      snapshot_mass (edit p p' ch st) <= snapshot_mass st.
    Proof.
      intros p p' ch st; unfold snapshot_mass; rewrite !finite_fold_choice.
      rewrite (finite_sum_perm _ _ _ _ (snapshots_edit_perm p p' ch st)), finite_sum_map.
      apply finite_sum_mono; intros [id [owner writes live]] Hin.
      cbn [fst snd retire_snapshot snapshot_live snapshot_writes].
      destruct live;
        destruct (existsb (fun x => mem x (invalidate_keys p p' ch st)) writes); cbn; lia.
    Qed.

    (** Editing never widens the stored or recorded key inventories. *)
    Lemma kwidth_edit : forall p p' ch st, kwidth (edit p p' ch st) <= kwidth st.
    Proof.
      intros p p' ch st; unfold kwidth; apply finite_max_bound.
      intros x Hin; apply finite_max_member; apply in_app_iff.
      apply in_app_iff in Hin as [Hin|Hin].
      - left; eapply stored_edit_subset; exact Hin.
      - right; eapply snapshot_keys_edit_subset; exact Hin.
    Qed.

    (** Editing releases each invalidated key and all its counted read entries. *)
    Lemma infl_mass_edit : forall p p' ch st, state_ok st ->
      infl_mass (edit p p' ch st) +
        fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (invalidated p p' ch st)) <=
      infl_mass st.
    Proof.
      intros p p' ch st Hstate.
      pose proof Hstate as [Hstored [Hnodup Hrest]].
      pose proof (state_ok_edit p p' ch st Hstate) as [Hstored' [Hnodup' Hrest']].
      assert (Hboth : NoDup (stored (edit p p' ch st) ++ invalidate_keys p p' ch st)).
      { apply NoDup_app; [exact Hnodup'|apply invalidate_keys_nodup|].
        intros x Hin Hbad; apply (proj1 (Hstored' x)) in Hin.
        apply (proj1 (edit_dom_keys p p' ch st x)) in Hin as [_ Hkeep]; contradiction. }
      assert (Hsub : incl (stored (edit p p' ch st) ++ invalidate_keys p p' ch st) (stored st)).
      { intros x Hin; apply in_app_iff in Hin as [Hin|Hin].
        - eapply stored_edit_subset; exact Hin.
        - apply (proj2 (Hstored x)); eapply invalidate_keys_dom; exact Hin. }
      pose proof (finite_sum_incl_nodup _ (fun x => infl_deg st x + 1) _ _ Hboth Hsub) as Hsum.
      rewrite finite_sum_app in Hsum.
      assert (Hretained :
        finite_sum (fun x => infl_deg (edit p p' ch st) x + 1) (stored (edit p p' ch st)) =
        finite_sum (fun x => infl_deg st x + 1) (stored (edit p p' ch st))).
      { apply finite_sum_ext; intros x Hin; unfold infl_deg.
        rewrite edit_infl_keeps; [reflexivity|apply (proj1 (Hstored' x)); exact Hin]. }
      pose proof (snapshot_mass_edit_le p p' ch st) as Hsnap.
      change (finite_sum (fun x => infl_deg (edit p p' ch st) x + 1)
        (stored (edit p p' ch st)) + snapshot_mass (edit p p' ch st) +
        finite_sum (fun x => infl_deg st x + 1) (invalidate_keys p p' ch st) <=
        finite_sum (fun x => infl_deg st x + 1) (stored st) + snapshot_mass st).
      rewrite Hretained; lia.
    Qed.
  End EditMetadata.

  Lemma state_ok_init : state_ok init.
  Proof.
    apply Core.state_core_ok; exact Core.state_core_init.
  Qed.
  Lemma state_ok_demand : forall p pol roots fuel st o st', state_ok st ->
    demand p pol roots fuel st = (o, st') -> state_ok st'.
  Proof.
    exact DemandState.state_ok_demand.
  Qed.
  Lemma state_ok_edit : forall p p' ch st, state_ok st -> state_ok (edit p p' ch st).
  Proof.
    exact EditMetadata.state_ok_edit.
  Qed.

  Definition width (p : S.prog) (_ : state) : nat :=
    S.kw p + N.to_nat (S.row_work p 0).
  Definition c_inc : N := (32 * (S.c_sys + PTrieT.c_trie + 1))%N.
  (** The initial state is a constant. *)
  Lemma T_init_le : (T_init <= c_inc)%N.
  Proof.
    unfold T_init, c_inc; time_cbn; lia.
  Qed.

  (** Reading a value pays for the key code. *)
  Lemma T_value_le : forall st x,
    (T_value st x <= c_inc * N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros st x.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (S.key * L.t) (S.key_code x) (inc_values st)) as Hget.
    assert (Hguard :
      (match PTrieCode.get (S.key_code x) (inc_values st) with
       | Some (stored_key, _) => S.T_key_eqb x stored_key
       | None => 0
       end <= S.c_sys * N.of_nat (S.key_bits x + 1))%N).
    { destruct (PTrieCode.get (S.key_code x) (inc_values st)) as [[stored_key v]|].
      - apply S.T_key_eqb_le.
      - lia. }
    unfold PTrieT.T_get in Hget.
    unfold S.key_bits in Hcode, Hguard.
    unfold T_value, T_lookup, PTrieCode.T_get, c_inc, S.key_bits.
    time_simpl; time_cbn; nia.
  Qed.

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
  Proof. Admitted. (* OPEN: Global discovery and value scans exceed the regional time budget. *)

  (** Invalidation lists each removed stored key once. *)
  Lemma invalidated_nodup : forall p p' ch st, NoDup (invalidated p p' ch st).
  Proof.
    intros p p' ch st; apply invalidate_nodup.
  Qed.
  (** The empty state stores no key and no influence entry. *)
  Lemma infl_mass_init : infl_mass init = 0.
  Proof.
    reflexivity.
  Qed.
  Lemma kwidth_init : kwidth init = 0.
  Proof.
    reflexivity.
  Qed.
  (** Every stored key fits the key width of the state. *)
  Lemma kwidth_dom : forall st x, state_ok st -> dom st x -> S.key_bits x <= kwidth st.
  Proof.
    intros st x [Hstored Hrest] Hdom; unfold kwidth.
    change (S.key_bits x <= finite_max S.key_bits (stored st ++ snapshot_keys st)).
    apply finite_max_member; apply in_or_app; left.
    apply (proj2 (Hstored x)); exact Hdom.
  Qed.
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
  Lemma infl_mass_edit : forall p p' ch st, state_ok st ->
    infl_mass (edit p p' ch st) +
      fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (invalidated p p' ch st)) <=
    infl_mass st.
  Proof.
    exact EditMetadata.infl_mass_edit.
  Qed.
  (** Editing never widens the state. *)
  Lemma kwidth_edit : forall p p' ch st, kwidth (edit p p' ch st) <= kwidth st.
  Proof.
    exact EditMetadata.kwidth_edit.
  Qed.
  (** Editing pays for the influence mass that it releases and for the changed rows. *)
  Lemma T_edit_le : forall p p' ch st, S.wf p -> S.wf p' -> state_ok st ->
    (forall r, In r ch -> In r (S.rows p) \/ In r (S.rows p')) ->
    (T_edit p p' ch st <= c_inc *
      N.of_nat (((infl_mass st - infl_mass (edit p p' ch st)) +
        fold_right Nat.add 0%nat (map (fun r => length (S.writes p r) + length (S.writes p' r) +
          length (S.deps p r) + length (S.deps p' r) + 1) ch) + 1)%nat) *
      N.of_nat (width p st + width p' st + kwidth st + 1))%N.
  Proof. Admitted. (* OPEN: Whole-program and snapshot scans exceed released influence credit. *)

  TimeFun discover.
  (** Snapshot access walks the identifier once. *)
  Lemma T_snapshot_get_le : forall id st,
    (T_snapshot_get id st <= c_inc * N.of_nat (Pos.size_nat id + 1))%N.
  Proof.
    intros id st.
    pose proof (PTrieT.T_get_le (incremental_snapshot S.key) id (inc_snapshots st)) as Hget.
    unfold PTrieT.T_get in Hget.
    unfold T_snapshot_get, PTrieCode.T_get, c_inc; time_simpl; time_cbn; nia.
  Qed.
  Lemma T_snapshot_set_le : forall id ss st,
    (T_snapshot_set id ss st <= c_inc * N.of_nat (Pos.size_nat id + 1))%N.
  Proof.
    intros id ss st.
    pose proof (PTrieT.T_set_le (incremental_snapshot S.key) id ss (inc_snapshots st)) as Hset.
    unfold PTrieT.T_set in Hset.
    unfold T_snapshot_set, PTrieCode.T_set, c_inc; time_simpl; time_cbn; nia.
  Qed.
  (** Recording pays for the owner code and the new write occurrences. *)
  Lemma T_snapshot_record_le : forall owner writes st,
    (T_snapshot_record owner writes st <=
      c_inc * N.of_nat (S.key_bits owner + length writes + 1))%N.
  Proof.
    intros owner writes st.
    pose proof (S.T_key_code_le owner) as Hcode.
    pose proof (PTrieT.T_get_le (incremental_snapshot S.key)
      (S.key_code owner) (inc_snapshots st)) as Hget.
    pose proof (Datatypes.T_app_le writes
      (match snapshot_get (S.key_code owner) st with
       | Some ss => if snapshot_live ss then snapshot_writes ss else []
       | None => []
       end)) as Happ.
    pose proof (PTrieT.T_set_le (incremental_snapshot S.key) (S.key_code owner)
      {| snapshot_owner := owner;
         snapshot_writes := writes ++
           match snapshot_get (S.key_code owner) st with
           | Some ss => if snapshot_live ss then snapshot_writes ss else []
           | None => []
           end;
         snapshot_live := true |} (inc_snapshots st)) as Hset.
    unfold PTrieT.T_get in Hget; unfold PTrieT.T_set in Hset.
    unfold S.key_bits in Hcode.
    unfold T_snapshot_record, T_snapshot_get, T_snapshot_set,
      PTrieCode.T_get, PTrieCode.T_set, c_inc, S.key_bits.
    time_simpl; time_cbn.
    destruct (snapshot_get (S.key_code owner) st) as [ss|] eqn:Hsnapshot in *;
      [destruct (snapshot_live ss) eqn:Hlive in *|]; cbn beta iota zeta in *;
      rewrite !Nat2N.inj_add in *; change (N.of_nat 1) with 1%N in *; nia.
  Qed.
  (** Trie lookup reads precisely the recorded snapshot inventory. *)
  Lemma snapshot_get_pin : forall st id ss,
    snapshot_get id st = Some ss <-> In (id, ss) (snapshots st).
  Proof.
    intros st id ss; unfold snapshot_get, snapshots; symmetry; apply PTrie.elements_spec.
  Qed.
  (** Trie update changes precisely one shared snapshot. *)
  Lemma snapshot_set_pin : forall st id ss q,
    snapshot_get q (snapshot_set id ss st) =
      if Pos.eqb q id then Some ss else snapshot_get q st.
  Proof.
    intros st id ss q; unfold snapshot_get, snapshot_set; cbn [inc_snapshots].
    destruct (Pos.eqb q id) eqn:Hcode.
    - apply Pos.eqb_eq in Hcode; subst q; apply PTrie.get_set_same.
    - apply Pos.eqb_neq in Hcode; apply PTrie.get_set_other; exact Hcode.
  Qed.
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
  Proof.
    intros st owner writes; unfold snapshot_record.
    rewrite snapshot_set_pin, Pos.eqb_refl; reflexivity.
  Qed.
  (** Snapshot mass counts each unvisited write occurrence once. *)
  Lemma snapshot_mass_pin : forall st, snapshot_mass st =
    fold_right (fun ss n =>
      if snapshot_live (snd ss) then length (snapshot_writes (snd ss)) + n else n)
      0 (snapshots st).
  Proof.
    reflexivity.
  Qed.
  (** The recorded key inventory includes visited snapshots for identifier width accounting. *)
  Lemma snapshot_keys_pin : forall st, snapshot_keys st =
    flat_map (fun ss => snapshot_writes (snd ss)) (snapshots st).
  Proof.
    reflexivity.
  Qed.
  (** Every snapshot identifier is the code of an owner among its writes. *)
  Lemma snapshot_owner_pin : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    id = S.key_code (snapshot_owner ss) /\ In (snapshot_owner ss) (snapshot_writes ss).
  Proof.
    intros st id ss [_ [_ [Howner Hrest]]] Hin; apply Howner; exact Hin.
  Qed.
  (** Snapshot identifiers occur once in the inventory. *)
  Lemma snapshots_nodup : forall st, NoDup (map fst (snapshots st)).
  Proof.
    intro st; unfold snapshots; apply PTrie.elements_nodup.
  Qed.
  (** Read entries resolve to a retained shared snapshot, including stale entries. *)
  Lemma infl_snapshot_pin : forall st x id, state_ok st -> In id (infl_at st x) ->
    exists ss, In (id, ss) (snapshots st).
  Proof.
    intros st x id [_ [_ [_ [Hrefs Hrest]]]] Hin; apply Hrefs with (x := x); exact Hin.
  Qed.
  (** Unvisited snapshots contain stored keys. *)
  Lemma snapshot_stored_pin : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    snapshot_live ss = true -> forall x, In x (snapshot_writes ss) -> dom st x.
  Proof.
    intros st id ss [_ [_ [_ [_ [Hlive Hrest]]]]] Hin Hactive x Hx.
    exact (Hlive id ss Hin Hactive x Hx).
  Qed.
  (** Co-write memberships are precisely the unvisited snapshot key occurrences. *)
  Lemma cowrite_count_pin : forall st x id, state_ok st ->
    length (filter (Pos.eqb id) (cowrite_at st x)) =
    fold_right (fun iss n =>
      if (Pos.eqb id (fst iss) && snapshot_live (snd iss))%bool then
        length (filter (S.key_eqb x) (snapshot_writes (snd iss))) + n else n)
      0 (snapshots st).
  Proof.
    intros st x id [_ [_ [_ [_ [_ [Hcounts Hrest]]]]]]; exact (Hcounts x id).
  Qed.
  (** Shared snapshot mass pays the co-write memberships without a second inventory charge. *)
  Lemma cowrite_mass_pin : forall st, state_ok st -> snapshot_mass st =
    fold_right Nat.add 0 (map (fun x => length (cowrite_at st x)) (stored st)).
  Proof.
    intros st [_ [_ [_ [_ [_ [_ [Hmass Hwidth]]]]]]]; exact Hmass.
  Qed.
  (** Every retained snapshot identifier fits the stored key width. *)
  Lemma snapshot_id_width : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    Pos.size_nat id <= kwidth st.
  Proof.
    intros st id ss [_ [_ [_ [_ [_ [_ [_ Hwidth]]]]]]] Hin; exact (Hwidth id ss Hin).
  Qed.
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
  Proof.
    exact EditMetadata.edit_infl_keeps.
  Qed.
  (** Visiting a snapshot removes all its writes and retires every co-write membership. *)
  Lemma edit_snapshot_visit : forall p p' ch st id ss, state_ok st ->
    In (id, ss) (snapshots st) -> snapshot_live ss = true ->
    (exists x, In x (snapshot_writes ss) /\ In x (invalidated p p' ch st)) ->
    (forall x, In x (snapshot_writes ss) -> ~ dom (edit p p' ch st) x) /\
    (forall x, ~ In id (cowrite_at (edit p p' ch st) x)) /\
    (forall ss', In (id, ss') (snapshots (edit p p' ch st)) -> snapshot_live ss' = false).
  Proof.
    exact EditMetadata.edit_snapshot_visit.
  Qed.

  (** The stored key list enumerates the domain once. *)
  Lemma stored_spec : forall st x, state_ok st -> (In x (stored st) <-> dom st x).
  Proof.
    intros st x [Hstored Hrest]; exact (Hstored x).
  Qed.
  Lemma stored_nodup : forall st, state_ok st -> NoDup (stored st).
  Proof.
    intros st [_ [Hnodup Hrest]]; exact Hnodup.
  Qed.
  (** The influence degree counts the recorded entries of a key, stale ones included. *)
  Lemma infl_deg_spec : forall st x, infl_deg st x = length (infl_at st x).
  Proof.
    reflexivity.
  Qed.
  (** Influence mass counts stored keys, their entries and the unvisited snapshot keys. *)
  Lemma infl_mass_spec : forall st, infl_mass st =
    fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (stored st)) + snapshot_mass st.
  Proof.
    reflexivity.
  Qed.
  (** The key width covers the stored keys and every key of a recorded snapshot. *)
  Lemma kwidth_spec : forall st, kwidth st =
    fold_right Nat.max 0 (map S.key_bits (stored st ++ snapshot_keys st)).
  Proof.
    reflexivity.
  Qed.
  (** The public invalidation list is the plan's closure. *)
  Lemma invalidated_pin : forall p p' ch st,
    invalidated p p' ch st = invalidate p p' ch st.
  Proof.
    reflexivity.
  Qed.
  TimeFun merge_region.

  Lemma region_closed : forall p roots st r x, inv p st ->
    In r (region p roots st) -> In x (S.writes p r ++ S.deps p r) ->
    dom st x \/ In x (discover p roots st).
  Proof.
    intros p roots st r x Hinv Hr Hx; exact (discovery_region_support p roots st r x Hr Hx).
  Qed.

  Lemma frame_post : forall p st s, S.wf p -> inv p st ->
    (forall x, dom st x -> s x = look st x) ->
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  Proof.
    intros p st s Hwf [Hclosed Hpost] Hagree r y Hr Hy Hdom.
    assert (Hrow : row_ok L.leb s (S.target p r) (S.eval p r s) =
      row_ok L.leb (look st) (S.target p r) (S.eval p r (look st))).
    { apply row_look_transport; [exact Hwf|exact Hr|].
      intros x Hx; apply Hagree; exact (Hclosed r y x Hr Hy Hdom Hx). }
    rewrite Hrow; exact (Hpost r y Hr Hy Hdom).
  Qed.

  Lemma merge_inv : forall p roots st m, S.wf p -> inv p st ->
    Checker.check_rows p (region p roots st) m = true ->
    (forall x, dom st x -> Checker.look m x = look st x) ->
    inv p (merge_region st (discover p roots st) m).
  Proof.
    intros p roots st m Hwf Hinv Hcheck Hagree.
    apply merge_checked_inv; [exact Hwf|exact Hinv|exact Hcheck|].
    intros r x Hr Hx Hdom; apply Hagree; exact Hdom.
  Qed.

  Lemma demand_certificate : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') ->
    exists m, Checker.check_rows p (region p roots st) m = true.
  Proof. Admitted. (* STUB *)

  Lemma region_least_restricted : forall p pol roots fuel st m,
    S.wf p -> S.monotone p -> Least.widening_free pol -> inv p st -> least_on p st ->
    Sol.run (R.mk p (frozen p roots st) (region p roots st)) pol fuel = Solved m ->
    forall s, S.post_solution p s -> forall x,
      L.leb (look_or S.key_code L.bot m x) (s x) = true.
  Proof.
    intros p pol roots fuel st m Hwf Hmono Hfree Hinv Hleast Hrun.
    exact (regional_run_below p pol roots fuel st m Hwf Hmono Hfree Hleast Hrun).
  Qed.

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
  Proof.
    intros p roots st x v Hin; exact (frozen_for_rows_sound p (region p roots st) st x v Hin).
  Qed.
  (** Frozen pairs have distinct keys read or written by region rows. *)
  Lemma frozen_region : forall p roots st x v, In (x, v) (frozen p roots st) ->
    exists r, In r (region p roots st) /\ In x (S.writes p r ++ S.deps p r).
  Proof.
    intros p roots st x v Hin; unfold frozen, frozen_pairs, frozen_for_rows in Hin.
    apply freeze_values_spec in Hin as [Hin Hvalue].
    apply (proj1 (unique_spec (flat_map (row_keys p) (discovery_region p roots st)) x)) in Hin.
    apply in_flat_map in Hin as [r [Hr Hx]].
    exists r; split; assumption.
  Qed.
  Lemma frozen_nodup : forall p roots st, NoDup (map fst (frozen p roots st)).
  Proof. Admitted. (* STUB *)

End IncrementalT.
