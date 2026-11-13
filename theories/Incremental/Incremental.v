(** * Checked incremental solving

    Incremental states retain values between demands and edits.
    For example, an initial state has no stored values.
    Builds on: IncrementalSig. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Code MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig CheckSig PolicySig.
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

  Definition lookup (m : kmap S.key L.t) (x : S.key) : option L.t :=
    match PTrieCode.get (S.key_code x) m with
    | Some (stored_key, v) => if S.key_eqb x stored_key then Some v else None
    | None => None
    end.

  Definition value (st : state) (x : S.key) : option L.t :=
    lookup (inc_values st) x.

  Definition present (st : state) (x : S.key) : bool :=
    match value st x with Some _ => true | None => false end.

  Definition missing (st : state) (x : S.key) : bool := negb (present st x).
  Definition mem (x : S.key) (xs : list S.key) : bool := existsb (S.key_eqb x) xs.
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

  Fixpoint unique (xs : list S.key) : list S.key :=
    match xs with
    | [] => []
    | x :: rest => if mem x rest then unique rest else x :: unique rest
    end.

  Definition freeze_values (st : state) (xs : list S.key) : list (S.key * L.t) :=
    flat_map (fun x =>
      match value st x with Some v => [(x, v)] | None => [] end) xs.

  Definition frozen_for_rows (p : S.prog) (rs : list S.row) (st : state)
      : list (S.key * L.t) :=
    freeze_values st (unique (flat_map (row_keys p) rs)).

  Definition frozen_pairs (p : S.prog) (roots : list S.key) (st : state)
      : list (S.key * L.t) :=
    frozen_for_rows p (discovery_region p roots st) st.

  (** This is exactly the released [checked] fold when [fz = frozen p roots st]. *)
  Definition restore (fz : list (S.key * L.t)) (m : kmap S.key L.t)
      : kmap S.key L.t :=
    fold_left (fun acc xv => PTrieCode.set (S.key_code (fst xv)) xv acc) fz m.

  (** Inserting bottom is intentional: it makes an otherwise unknown root present. *)
  Fixpoint fill (xs : list S.key) (m base : kmap S.key L.t) : kmap S.key L.t :=
    match xs with
    | [] => base
    | x :: rest =>
        PTrieCode.set (S.key_code x) (x, Checker.look m x) (fill rest m base)
    end.

  Definition merge_discovered (st : state) (xs : list S.key) (m : kmap S.key L.t) : state :=
    {| inc_values := fill xs m (inc_values st);
       inc_influence := inc_influence st;
       inc_cowrites := inc_cowrites st;
       inc_snapshots := inc_snapshots st |}.

  Fixpoint prune_values (cells : list (positive * (S.key * L.t)))
      (m : kmap S.key L.t) : kmap S.key L.t :=
    match cells with
    | [] => m
    | (path, (x, v)) :: rest =>
        let remaining := if Pos.eqb path (S.key_code x) then m else PTrieCode.remove path m in
        prune_values rest remaining
    end.

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
  (* STUB-CODE *)
  Definition edit (_ _ : S.prog) (_ : list S.row) (st : state) : state := st.
End IncrementalCode.

Module Incremental (L : WLATTICE) (LB : LUB L) (Top : HAS_TOP L) (S : LOCAL_SYSTEM L)
    (RS : SYSTEM L with Definition key := S.key
      with Definition key_code := S.key_code)
    (R : RESTRICT L S RS) (Sol : SOLVER_OPS L RS) (Checker : CHECK L S)
    (Least : SOLVER_LEAST L LB RS Sol) <: INCREMENTAL L LB Top S RS R Sol Checker Least.
  Include IncrementalCode L S RS R Sol Checker.
  Include INCREMENTAL_SPEC L S RS R Sol Checker.

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

  Lemma mem_spec : forall x xs, mem x xs = true <-> In x xs.
  Proof.
    intros x xs; unfold mem; rewrite existsb_exists; split.
    - intros [y [Hy Heq]].
      destruct (S.key_eqb_spec x y) as [->|Hneq]; [exact Hy|discriminate Heq].
    - intro Hx; exists x; split; [exact Hx|].
      destruct (S.key_eqb_spec x x); congruence.
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

  Lemma key_eqb_true : forall x y, S.key_eqb x y = true <-> x = y.
  Proof.
    intros x y; destruct (S.key_eqb_spec x y); split; intro H; congruence.
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

  Lemma discovery_region_rows : forall p roots st r,
    In r (discovery_region p roots st) -> In r (S.rows p).
  Proof.
    intros p roots st r Hr; apply region_for_spec in Hr; tauto.
  Qed.

  Lemma discovery_region_new : forall p roots st r,
    In r (discovery_region p roots st) ->
    exists x, In x (S.writes p r) /\ ~ dom st x.
  Proof.
    intros p roots st r Hr; apply region_for_spec in Hr.
    destruct Hr as [_ [x [Hx [Hnone _]]]].
    exists x; split; [exact Hx|].
    intros [v Hvalue]; rewrite Hnone in Hvalue; discriminate Hvalue.
  Qed.

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

  Lemma discovery_closed : forall p roots st, inv p st ->
    closed p (fun x => dom st x \/ In x (discovery_keys p roots st)).
  Proof.
    intros p roots st [Hclosed Hpost] r y x Hr Hy [Hold|Hnew] Hx.
    - left; eapply Hclosed; eauto.
    - apply (discovery_region_support p roots st r x); [|exact Hx].
      apply region_for_spec; split; [exact Hr|].
      exists y; repeat split; [exact Hy| |exact Hnew].
      apply (discovery_keys_missing p roots st y Hnew).
  Qed.

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

  Lemma lookup_set : forall m x y v,
    lookup (PTrieCode.set (S.key_code y) (y, v) m) x =
      if S.key_eqb x y then Some v else lookup m x.
  Proof.
    intros m x y v; destruct (S.key_eqb_spec x y) as [->|Hneq].
    - unfold lookup; rewrite PTrie.get_set_same.
      destruct (S.key_eqb_spec y y); congruence.
    - unfold lookup; rewrite PTrie.get_set_other; [reflexivity|].
      intro Hcode; apply Hneq, S.key_code_inj, Hcode.
  Qed.

  Lemma lookup_remove : forall m path x,
    lookup (PTrieCode.remove path m) x =
      if Pos.eqb (S.key_code x) path then None else lookup m x.
  Proof.
    intros m path x; destruct (Pos.eqb (S.key_code x) path) eqn:Hpath.
    - apply Pos.eqb_eq in Hpath; unfold lookup.
      rewrite Hpath, PTrie.get_remove_same; reflexivity.
    - apply Pos.eqb_neq in Hpath; unfold lookup.
      rewrite PTrie.get_remove_other by exact Hpath; reflexivity.
  Qed.

  Lemma malformed_lookup : forall original path y v x,
    PTrieCode.get path original = Some (y, v) ->
    Pos.eqb path (S.key_code y) = false -> S.key_code x = path ->
    lookup original x = None.
  Proof.
    intros original path y v x Hget Hbad Hpath; subst path.
    unfold lookup; rewrite Hget.
    destruct (S.key_eqb_spec x y) as [->|Hneq]; [|reflexivity].
    rewrite Pos.eqb_refl in Hbad; discriminate Hbad.
  Qed.

  Lemma prune_values_lookup : forall cells original current,
    (forall path y v, In (path, (y, v)) cells ->
      PTrieCode.get path original = Some (y, v)) ->
    (forall x, lookup current x = lookup original x) ->
    forall x, lookup (prune_values cells current) x = lookup original x.
  Proof.
    induction cells as [|[path [y v]] rest IH]; intros original current Hcells Hagree x.
    - exact (Hagree x).
    - cbn [prune_values].
      destruct (Pos.eqb path (S.key_code y)) eqn:Hvalid.
      + apply (IH original current).
        * intros q z w Hin; apply Hcells; now right.
        * exact Hagree.
      + apply (IH original (PTrieCode.remove path current)).
        * intros q z w Hin; apply Hcells; now right.
        * intro z; rewrite lookup_remove.
          destruct (Pos.eqb (S.key_code z) path) eqn:Hpath.
          -- symmetry; eapply malformed_lookup.
             ++ apply Hcells; now left.
             ++ exact Hvalid.
             ++ now apply Pos.eqb_eq.
          -- exact (Hagree z).
  Qed.

  Lemma normalize_values_value : forall st x,
    value (normalize_values st) x = value st x.
  Proof.
    intros st x; unfold value, normalize_values, canonical_values; cbn [inc_values].
    apply prune_values_lookup.
    - intros path y v Hin; now apply PTrie.elements_spec in Hin.
    - intro y; reflexivity.
  Qed.

  Lemma fill_lookup : forall xs m base x,
    lookup (fill xs m base) x =
      if mem x xs then Some (Checker.look m x) else lookup base x.
  Proof.
    induction xs as [|y rest IH]; intros m base x; cbn [fill mem].
    - reflexivity.
    - rewrite lookup_set, IH.
      change (mem x (y :: rest)) with (S.key_eqb x y || mem x rest)%bool.
      destruct (S.key_eqb_spec x y) as [->|Hneq]; reflexivity.
  Qed.

  Lemma merge_old_value : forall st xs m x v,
    (forall y, In y xs -> value st y = None) -> value st x = Some v ->
    value (merge_discovered st xs m) x = Some v.
  Proof.
    intros st xs m x v Hmissing Hvalue.
    unfold value, merge_discovered; cbn [inc_values]; rewrite fill_lookup.
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
    destruct (mem x xs) eqn:Hmem.
    - split.
      + intros _; right; now apply mem_spec.
      + intros _; exists (Checker.look m x); reflexivity.
    - split.
      + intros [v Hv]; left; exists v; exact Hv.
      + intros [[v Hv]|Hin]; [exists v; exact Hv|].
        apply mem_spec in Hin; congruence.
  Qed.

  Lemma merge_new_look : forall st xs m x,
    In x xs -> look (merge_discovered st xs m) x = Checker.look m x.
  Proof.
    intros st xs m x Hin; unfold look, value, merge_discovered; cbn [inc_values].
    rewrite fill_lookup, (proj2 (mem_spec x xs) Hin); reflexivity.
  Qed.

  Lemma unique_spec : forall xs x, In x (unique xs) <-> In x xs.
  Proof.
    induction xs as [|y rest IH]; intro x; cbn [unique].
    - reflexivity.
    - destruct (mem y rest) eqn:Hmem.
      + rewrite IH; cbn [In]; split; [now right|].
        intros [->|Hin]; [now apply mem_spec in Hmem|exact Hin].
      + cbn [In]; rewrite IH; reflexivity.
  Qed.

  Lemma unique_nodup : forall xs, NoDup (unique xs).
  Proof.
    induction xs as [|x rest IH]; cbn [unique].
    - constructor.
    - destruct (mem x rest) eqn:Hmem; [exact IH|].
      constructor; [|exact IH].
      intro Hin.
      pose proof (proj1 (unique_spec rest x) Hin) as Hrest.
      pose proof (proj2 (mem_spec x rest) Hrest) as Htrue.
      congruence.
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

  Lemma raw_set : forall m x y v,
    look_or S.key_code L.bot (PTrieCode.set (S.key_code y) (y, v) m) x =
      if S.key_eqb x y then v else look_or S.key_code L.bot m x.
  Proof.
    intros m x y v; destruct (S.key_eqb_spec x y) as [->|Hneq].
    - unfold look_or; rewrite PTrie.get_set_same; reflexivity.
    - unfold look_or; rewrite PTrie.get_set_other; [reflexivity|].
      intro Hcode; apply Hneq, S.key_code_inj, Hcode.
  Qed.

  (** Coherent later seed updates cannot disturb a value already restored. *)
  Lemma restore_preserves : forall fz m x v,
    (forall y w, In (y, w) fz -> y = x -> w = v) ->
    look_or S.key_code L.bot m x = v ->
    look_or S.key_code L.bot (restore fz m) x = v.
  Proof.
    induction fz as [|[y w] rest IH]; intros m x v Hcoherent Hlook.
    - exact Hlook.
    - cbn [restore fold_left fst].
      apply IH.
      + intros z a Hin Heq; apply (Hcoherent z a); [now right|exact Heq].
      + rewrite raw_set.
        destruct (S.key_eqb_spec x y) as [->|Hneq]; [|exact Hlook].
        apply (Hcoherent y w); [now left|reflexivity].
  Qed.

  Lemma restore_hit : forall fz m x v,
    (forall w, In (x, w) fz -> w = v) -> In (x, v) fz ->
    look_or S.key_code L.bot (restore fz m) x = v.
  Proof.
    induction fz as [|[y w] rest IH]; intros m x v Hcoherent Hin.
    - contradiction.
    - cbn [restore fold_left fst].
      destruct Hin as [Heq|Hin].
      + inversion Heq; subst y w.
        apply restore_preserves.
        * intros z a Hz ->; apply Hcoherent; now right.
        * rewrite raw_set; destruct (S.key_eqb_spec x x); congruence.
      + apply IH.
        * intros a Ha; apply Hcoherent; now right.
        * exact Hin.
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

  Lemma forallb_same : forall A (xs : list A) f g,
    (forall x, In x xs -> f x = g x) -> forallb f xs = forallb g xs.
  Proof.
    intros A xs; induction xs as [|x rest IH]; intros f g Hagree; cbn [forallb].
    - reflexivity.
    - rewrite (Hagree x (or_introl eq_refl)); f_equal.
      apply IH; intros y Hy; apply Hagree; now right.
  Qed.

  (** Row checking only observes the row's declared read and write support. *)
  Lemma row_look_transport : forall p r a b,
    S.wf p -> In r (S.rows p) ->
    (forall x, In x (row_keys p r) -> a x = b x) ->
    row_ok L.leb a (S.target p r) (S.eval p r a) =
      row_ok L.leb b (S.target p r) (S.eval p r b).
  Proof.
    intros p r a b Hwf Hr Hagree.
    assert (Heval : S.eval p r a = S.eval p r b).
    { apply S.reads_within; [exact Hwf|exact Hr|].
      intros x Hx; apply Hagree; unfold row_keys; apply in_or_app; now right. }
    rewrite Heval.
    destruct (S.eval p r b) as [[v ss]|] eqn:Hout; cbn [row_ok]; [|reflexivity].
    assert (Htarget : a (S.target p r) = b (S.target p r)).
    { apply Hagree; unfold row_keys, row_writes; apply in_or_app; left; now left. }
    rewrite Htarget; f_equal; apply forallb_same.
    intros [x w] Hside; cbn [fst snd]; rewrite Hagree; [reflexivity|].
    unfold row_keys, row_writes; apply in_or_app; left; right.
    eapply S.sides_within; eauto.
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
    rewrite !fill_lookup; destruct (mem x xs); [reflexivity|].
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
  Proof. Admitted. (* STUB *)

  Lemma demand_rejected : forall p pol roots fuel st why st',
    demand p pol roots fuel st = (DemandRejected why, st') -> st' = st.
  Proof. Admitted. (* STUB *)

  Lemma edit_inv : forall p p' ch st, S.wf p' -> edit_covers p p' ch -> inv p st ->
    inv p' (edit p p' ch st).
  Proof. Admitted. (* STUB *)

  Lemma edit_keeps : forall p p' ch st x v,
    value (edit p p' ch st) x = Some v -> value st x = Some v.
  Proof. Admitted. (* STUB *)

  Lemma demand_least : forall p pol roots fuel st o st', S.wf p -> S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  Proof. Admitted. (* STUB *)

  Lemma edit_least : forall p p' ch st, S.wf p -> edit_covers p p' ch ->
    inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  Proof. Admitted. (* STUB *)

  Lemma from_scratch_agrees : forall p st s x v, S.wf p -> S.monotone p ->
    inv p st -> least_on p st -> least_solution p s -> value st x = Some v ->
    L.leb (s x) v = true /\ L.leb v (s x) = true.
  Proof. Admitted. (* STUB *)

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
  TimeFun remove_buckets.
  TimeFun clear_new_buckets.
  TimeFun push_entry.
  TimeFun record_row.
  TimeFun record_rows.
  TimeFun finish_demand.
  TimeFun demand.
  TimeFun edit.
  Definition region := discovery_region.
  Definition invalidated (_ _ : S.prog) (_ : list S.row) (_ : state) : list S.key := [].
  Definition frozen := frozen_pairs.
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

  Lemma state_ok_init : state_ok init.
  Proof. Admitted. (* STUB *)
  Lemma state_ok_demand : forall p pol roots fuel st o st', state_ok st ->
    demand p pol roots fuel st = (o, st') -> state_ok st'.
  Proof. Admitted. (* STUB *)
  Lemma state_ok_edit : forall p p' ch st, state_ok st -> state_ok (edit p p' ch st).
  Proof. Admitted. (* STUB *)

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
  Lemma kwidth_dom : forall st x, state_ok st -> dom st x -> S.key_bits x <= kwidth st.
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
  Lemma infl_mass_edit : forall p p' ch st, state_ok st ->
    infl_mass (edit p p' ch st) +
      fold_right Nat.add 0%nat (map (fun x => infl_deg st x + 1) (invalidated p p' ch st)) <=
    infl_mass st.
  Proof. Admitted. (* STUB *)
  (** Editing never widens the state. *)
  Lemma kwidth_edit : forall p p' ch st, kwidth (edit p p' ch st) <= kwidth st.
  Proof. Admitted. (* STUB *)
  (** Editing pays for the influence mass that it releases and for the changed rows. *)
  Lemma T_edit_le : forall p p' ch st, S.wf p -> S.wf p' -> state_ok st ->
    (forall r, In r ch -> In r (S.rows p) \/ In r (S.rows p')) ->
    (T_edit p p' ch st <= c_inc *
      N.of_nat (((infl_mass st - infl_mass (edit p p' ch st)) +
        fold_right Nat.add 0%nat (map (fun r => length (S.writes p r) + length (S.writes p' r) +
          length (S.deps p r) + length (S.deps p' r) + 1) ch) + 1)%nat) *
      N.of_nat (width p st + width p' st + kwidth st + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition discover := discovery_keys.
  TimeFun discover.
  (* STUB-CODE *)
  Definition invalidate (_ _ : S.prog) (_ : list S.row) (_ : state) : list S.key := [].
  TimeFun invalidate.
  (** Snapshot access walks the identifier once. *)
  Lemma T_snapshot_get_le : forall id st,
    (T_snapshot_get id st <= c_inc * N.of_nat (Pos.size_nat id + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_snapshot_set_le : forall id ss st,
    (T_snapshot_set id ss st <= c_inc * N.of_nat (Pos.size_nat id + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Recording pays for the owner code and the new write occurrences. *)
  Lemma T_snapshot_record_le : forall owner writes st,
    (T_snapshot_record owner writes st <=
      c_inc * N.of_nat (S.key_bits owner + length writes + 1))%N.
  Proof. Admitted. (* STUB *)
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
  Lemma snapshot_owner_pin : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    id = S.key_code (snapshot_owner ss) /\ In (snapshot_owner ss) (snapshot_writes ss).
  Proof. Admitted. (* STUB *)
  (** Snapshot identifiers occur once in the inventory. *)
  Lemma snapshots_nodup : forall st, NoDup (map fst (snapshots st)).
  Proof. Admitted. (* STUB *)
  (** Read entries resolve to a retained shared snapshot, including stale entries. *)
  Lemma infl_snapshot_pin : forall st x id, state_ok st -> In id (infl_at st x) ->
    exists ss, In (id, ss) (snapshots st).
  Proof. Admitted. (* STUB *)
  (** Unvisited snapshots contain stored keys. *)
  Lemma snapshot_stored_pin : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
    snapshot_live ss = true -> forall x, In x (snapshot_writes ss) -> dom st x.
  Proof. Admitted. (* STUB *)
  (** Co-write memberships are precisely the unvisited snapshot key occurrences. *)
  Lemma cowrite_count_pin : forall st x id, state_ok st ->
    length (filter (Pos.eqb id) (cowrite_at st x)) =
    fold_right (fun iss n =>
      if (Pos.eqb id (fst iss) && snapshot_live (snd iss))%bool then
        length (filter (S.key_eqb x) (snapshot_writes (snd iss))) + n else n)
      0 (snapshots st).
  Proof. Admitted. (* STUB *)
  (** Shared snapshot mass pays the co-write memberships without a second inventory charge. *)
  Lemma cowrite_mass_pin : forall st, state_ok st -> snapshot_mass st =
    fold_right Nat.add 0 (map (fun x => length (cowrite_at st x)) (stored st)).
  Proof. Admitted. (* STUB *)
  (** Every retained snapshot identifier fits the stored key width. *)
  Lemma snapshot_id_width : forall st id ss, state_ok st -> In (id, ss) (snapshots st) ->
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
  Lemma edit_snapshot_visit : forall p p' ch st id ss, state_ok st ->
    In (id, ss) (snapshots st) -> snapshot_live ss = true ->
    (exists x, In x (snapshot_writes ss) /\ In x (invalidated p p' ch st)) ->
    (forall x, In x (snapshot_writes ss) -> ~ dom (edit p p' ch st) x) /\
    (forall x, ~ In id (cowrite_at (edit p p' ch st) x)) /\
    (forall ss', In (id, ss') (snapshots (edit p p' ch st)) -> snapshot_live ss' = false).
  Proof. Admitted. (* STUB *)

  (** The stored key list enumerates the domain once. *)
  Lemma stored_spec : forall st x, state_ok st -> (In x (stored st) <-> dom st x).
  Proof. Admitted. (* STUB *)
  Lemma stored_nodup : forall st, state_ok st -> NoDup (stored st).
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
  Definition merge_region := merge_discovered.
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
  (** Frozen pairs have distinct keys read or written by region rows. *)
  Lemma frozen_region : forall p roots st x v, In (x, v) (frozen p roots st) ->
    exists r, In r (region p roots st) /\ In x (S.writes p r ++ S.deps p r).
  Proof. Admitted. (* STUB *)
  Lemma frozen_nodup : forall p roots st, NoDup (map fst (frozen p roots st)).
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
