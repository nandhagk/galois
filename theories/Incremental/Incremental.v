(** * Checked incremental solving

    Incremental states retain values between demands and edits.
    For example, an initial state has no stored values.
    Builds on: IncrementalSig. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Code MapSig Trie Loop.
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

Record incremental_discovery (K R A : Type) := {
  discovery_pending : list K;
  discovery_seen : PTrieCode.t unit;
  discovery_missing : list K;
  discovery_done : list K;
  discovery_rows : list R;
  discovery_frozen : list (K * A)
}.

Arguments discovery_pending {K R A}.
Arguments discovery_seen {K R A}.
Arguments discovery_missing {K R A}.
Arguments discovery_done {K R A}.
Arguments discovery_rows {K R A}.
Arguments discovery_frozen {K R A}.

TimeFun discovery_pending.
TimeFun discovery_seen.
TimeFun discovery_missing.
TimeFun discovery_done.
TimeFun discovery_rows.
TimeFun discovery_frozen.

Record incremental_invalidation (K : Type) := {
  invalid_pending : list K;
  invalid_seen : PTrieCode.t unit;
  invalid_bad : list K;
  invalid_done : list K;
  invalid_snapshots : PTrieCode.t (incremental_snapshot K)
}.

Arguments invalid_pending {K}.
Arguments invalid_seen {K}.
Arguments invalid_bad {K}.
Arguments invalid_done {K}.
Arguments invalid_snapshots {K}.

TimeFun invalid_pending.
TimeFun invalid_seen.
TimeFun invalid_bad.
TimeFun invalid_done.
TimeFun invalid_snapshots.

(** Accessibility iteration carries an invariant into the stopping result. *)
Lemma incremental_loop_preserves {A R : Type} (lt : A -> A -> Prop)
    (step : forall s, {s1 : A | lt s1 s} + R) (Inv : A -> Prop) (Post : R -> Prop) :
  (forall s, Inv s ->
    match step s with inl (exist _ s1 _) => Inv s1 | inr r => Post r end) ->
  forall s (H : Acc lt s), Inv s -> Post (loop lt step s H).
Proof.
  intros Hstep s H; induction H as [s Hnext IH] using Acc_ind_dep; intro Hinv.
  cbn [loop Acc_inv]; destruct (step s) as [[s1 Hlt]|r] eqn:Hcall.
  - apply IH; specialize (Hstep s Hinv); rewrite Hcall in Hstep; exact Hstep.
  - specialize (Hstep s Hinv); rewrite Hcall in Hstep; exact Hstep.
Qed.

(** Binary loop results inherit an invariant of every callback step. *)
Lemma incremental_loopN_preserves {A R : Type} (step : A -> A + R)
    (Inv : A -> Prop) (Post : R -> Prop) :
  (forall s, Inv s -> match step s with inl s1 => Inv s1 | inr r => Post r end) ->
  forall fuel s, Inv s ->
    match loopN step fuel s with inl s1 => Inv s1 | inr r => Post r end.
Proof.
  intros Hstep fuel s Hinv; unfold loopN.
  apply (incremental_loop_preserves loopN_lt (loopN_step step)
    (fun fs => Inv (snd fs))
    (fun result => match result with inl s1 => Inv s1 | inr r => Post r end)).
  - intros [remaining current] Hcurrent; destruct remaining as [|p].
    + exact Hcurrent.
    + cbn [loopN_step]; specialize (Hstep current Hcurrent).
      destruct (step current) as [next|r] eqn:Hcall; exact Hstep.
  - exact Hinv.
Qed.

(** Binary fuel and unary fuel produce the same outcome for every accessibility proof. *)
Lemma incremental_loopN_acc_fuel {A R : Type} (step : A -> A + R) :
  forall fs (H : Acc (@loopN_lt A) fs),
    loop loopN_lt (loopN_step step) fs H =
      loop_fuel step (N.to_nat (fst fs)) (snd fs).
Proof.
  intros fs H; induction H as [[fuel s] Hnext IH] using Acc_ind_dep.
  destruct fuel as [|p].
  - reflexivity.
  - assert (Hpos : 0 < N.to_nat (N.pos p)) by apply Pos2Nat.is_pos.
    assert (Hfuel : N.to_nat (N.pos p) = S (N.to_nat (N.pred (N.pos p)))).
    { rewrite N2Nat.inj_pred; lia. }
    cbn [fst snd]; rewrite Hfuel.
    cbn [loop loopN_step loop_fuel].
    destruct (step s) as [next|result] eqn:Hstep; [apply IH|reflexivity].
Qed.

(** A binary-fuel loop has the corresponding unary-fuel outcome. *)
Lemma incremental_loopN_fuel {A R : Type} (step : A -> A + R) :
  forall fuel s, loopN step fuel s = loop_fuel step (N.to_nat fuel) s.
Proof.
  intros fuel s; unfold loopN; apply incremental_loopN_acc_fuel.
Qed.

(** Two completed runs of a deterministic binary-fuel loop return the same result. *)
Lemma incremental_loopN_agree {A R : Type} (step : A -> A + R) :
  forall fuel1 fuel2 s r1 r2,
    loopN step fuel1 s = inr r1 ->
    loopN step fuel2 s = inr r2 -> r1 = r2.
Proof.
  assert (Hagree : forall n1 n2 s r1 r2,
    loop_fuel step n1 s = inr r1 ->
    loop_fuel step n2 s = inr r2 -> r1 = r2).
  { intro n1; induction n1 as [|n1 IH]; intros [|n2] s r1 r2 Hrun1 Hrun2;
      cbn [loop_fuel] in Hrun1, Hrun2; try discriminate.
    destruct (step s) as [next|result] eqn:Hstep.
    - eapply IH; eassumption.
    - now injection Hrun1 as <-; injection Hrun2 as <-. }
  intros fuel1 fuel2 s r1 r2 Hrun1 Hrun2.
  rewrite incremental_loopN_fuel in Hrun1, Hrun2.
  eapply Hagree; eassumption.
Qed.

(** A completed unary loop replays under any fuel above its number of continuing steps. *)
Lemma incremental_loop_fuel_replay {A : Type} (step : A -> A + A) (count : A -> nat) :
  (forall s s', step s = inl s' -> count s' = S (count s)) ->
  (forall s r, step s = inr r -> count r = count s) ->
  forall fuel s r, loop_fuel step fuel s = inr r ->
    exists steps, steps < fuel /\ count r = count s + steps /\
      forall more, steps < more -> loop_fuel step more s = inr r.
Proof.
  intros Hcount Hstop fuel; induction fuel as [|fuel IH]; intros s r Hrun;
    [discriminate Hrun|].
  cbn [loop_fuel] in Hrun; destruct (step s) as [next|result] eqn:Hstep.
  - destruct (IH next r Hrun) as [steps [Hsteps [Hfinal Hreplay]]].
    exists (S steps); split; [lia|]; split.
    + rewrite (Hcount s next Hstep) in Hfinal; lia.
    + intros [|more] Hmore; [lia|].
      cbn [loop_fuel]; rewrite Hstep; apply Hreplay; lia.
  - inversion Hrun; subst r.
    exists 0; split; [lia|]; split; [rewrite Nat.add_0_r; now apply Hstop|].
    intros [|more] Hmore; [lia|].
    cbn [loop_fuel]; now rewrite Hstep.
Qed.

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

  Definition empty_discovery : incremental_discovery S.key S.row L.t :=
    {| discovery_pending := []; discovery_seen := PTrieCode.empty;
       discovery_missing := []; discovery_done := [];
       discovery_rows := []; discovery_frozen := [] |}.

  Definition discovery_visit (st : state) (x : S.key)
      (acc : incremental_discovery S.key S.row L.t)
      : incremental_discovery S.key S.row L.t :=
    let code := S.key_code x in
    match PTrieCode.get code (discovery_seen acc) with
    | Some _ => acc
    | None =>
      let seen := PTrieCode.set code tt (discovery_seen acc) in
      match value st x with
      | Some v =>
        {| discovery_pending := discovery_pending acc; discovery_seen := seen;
           discovery_missing := discovery_missing acc; discovery_done := discovery_done acc;
           discovery_rows := discovery_rows acc;
           discovery_frozen := (x, v) :: discovery_frozen acc |}
      | None =>
        {| discovery_pending := x :: discovery_pending acc; discovery_seen := seen;
           discovery_missing := x :: discovery_missing acc; discovery_done := discovery_done acc;
           discovery_rows := discovery_rows acc;
           discovery_frozen := discovery_frozen acc |}
      end
    end.

  Definition discovery_seed_one (st : state) (acc : incremental_discovery S.key S.row L.t)
      (x : S.key) : incremental_discovery S.key S.row L.t :=
    if missing st x then discovery_visit st x acc else acc.

  Definition discovery_row (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) (r : S.row)
      : incremental_discovery S.key S.row L.t :=
    let next := fold_left (fun current x => discovery_visit st x current) (row_keys p r) acc in
    {| discovery_pending := discovery_pending next; discovery_seen := discovery_seen next;
       discovery_missing := discovery_missing next; discovery_done := discovery_done next;
       discovery_rows := r :: discovery_rows next;
       discovery_frozen := discovery_frozen next |}.

  Definition discovery_step (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t)
      : incremental_discovery S.key S.row L.t + incremental_discovery S.key S.row L.t :=
    match discovery_pending acc with
    | [] => inr acc
    | x :: pending =>
      let rest :=
        {| discovery_pending := pending; discovery_seen := discovery_seen acc;
           discovery_missing := discovery_missing acc; discovery_done := x :: discovery_done acc;
           discovery_rows := discovery_rows acc;
           discovery_frozen := discovery_frozen acc |} in
      inl (fold_left (discovery_row p st) (S.rows_of p x) rest)
    end.

  Definition discovery (p : S.prog) (roots : list S.key) (fuel : N) (st : state)
      : option (list S.key * list S.row * list (S.key * L.t)) :=
    let initial := fold_left (discovery_seed_one st) roots empty_discovery in
    match loopN (discovery_step p st) fuel initial with
    | inl _ => None
    | inr result => Some (rev_append (discovery_missing result) [],
        rev_append (discovery_rows result) [],
        rev_append (discovery_frozen result) [])
    end.

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

  Fixpoint fill_local (xs : list S.key) (m base : kmap S.key L.t)
      : kmap S.key L.t :=
    match xs with
    | [] => base
    | x :: rest =>
      PTrieCode.set (S.key_code x) (x, look_or S.key_code L.bot m x)
        (fill_local rest m base)
    end.

  Definition merge_discovered (st : state) (xs : list S.key) (m : kmap S.key L.t) : state :=
    {| inc_values := fill_local xs m (inc_values st);
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
      (clear_new_buckets xs (merge_discovered st xs m)).

  Definition demand (p : S.prog) (pol : policy L.wparam) (roots : list S.key)
      (fuel : N) (st : state) : demand_status * state :=
    if forallb (present st) roots then (Done, st)
    else
      match discovery p roots fuel st with
      | None => (DemandOutOfFuel, st)
      | Some (xs, rs, fz) =>
        match Sol.run (R.mk p fz rs) pol fuel with
        | OutOfFuel _ => (DemandOutOfFuel, st)
        | Rejected why => (DemandRejected why, st)
        | Solved m =>
            let candidate := restore fz m in
            if Checker.check_rows p rs candidate
            then (Done, finish_demand p st xs rs candidate)
            else (DemandRejected Check_failed, st)
        end
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

  Definition invalid_seed_one (st : state) (acc : incremental_invalidation S.key)
      (x : S.key) : incremental_invalidation S.key :=
    if present st x then
      match PTrieCode.get (S.key_code x) (invalid_seen acc) with
      | Some _ => acc
      | None =>
        {| invalid_pending := x :: invalid_pending acc;
           invalid_seen := PTrieCode.set (S.key_code x) tt (invalid_seen acc);
           invalid_bad := x :: invalid_bad acc;
           invalid_done := invalid_done acc;
           invalid_snapshots := invalid_snapshots acc |}
      end
    else acc.

  Definition invalid_visit_snapshot (st : state) (acc : incremental_invalidation S.key)
      (id : positive) : incremental_invalidation S.key :=
    match PTrieCode.get id (invalid_snapshots acc) with
    | Some ss =>
      if snapshot_live ss then
        let next := fold_left (invalid_seed_one st) (snapshot_writes ss) acc in
        {| invalid_pending := invalid_pending next;
           invalid_seen := invalid_seen next;
           invalid_bad := invalid_bad next;
           invalid_done := invalid_done next;
           invalid_snapshots := PTrieCode.set id
             {| snapshot_owner := snapshot_owner ss;
                snapshot_writes := snapshot_writes ss;
                snapshot_live := false |} (invalid_snapshots next) |}
      else acc
    | None => acc
    end.

  Definition invalid_next (st : state) (x : S.key) (pending : list S.key)
      (seen : PTrieCode.t unit) (bad done : list S.key)
      (snapshots : PTrieCode.t (incremental_snapshot S.key))
      : incremental_invalidation S.key :=
    let rest :=
      {| invalid_pending := pending; invalid_seen := seen;
         invalid_bad := bad; invalid_done := x :: done;
         invalid_snapshots := snapshots |} in
    let readers := match PTrieCode.get (S.key_code x) (inc_influence st) with
      | Some ids => ids | None => [] end in
    let cowriters := match PTrieCode.get (S.key_code x) (inc_cowrites st) with
      | Some ids => ids | None => [] end in
    fold_left (invalid_visit_snapshot st) (readers ++ cowriters) rest.

  Definition invalid_step (st : state) (acc : incremental_invalidation S.key)
      : incremental_invalidation S.key + incremental_invalidation S.key :=
    match acc with
    | {| invalid_pending := []; invalid_seen := seen; invalid_bad := bad;
         invalid_done := done; invalid_snapshots := snapshots |} =>
      inr {| invalid_pending := []; invalid_seen := seen; invalid_bad := bad;
             invalid_done := done; invalid_snapshots := snapshots |}
    | {| invalid_pending := x :: pending; invalid_seen := seen; invalid_bad := bad;
         invalid_done := done; invalid_snapshots := snapshots |} =>
      inl (invalid_next st x pending seen bad done snapshots)
    end.

  Definition invalid_initial (p p' : S.prog) (ch : list S.row) (st : state)
      : incremental_invalidation S.key :=
    fold_left (invalid_seed_one st) (changed_keys p p' ch)
      {| invalid_pending := []; invalid_seen := PTrieCode.empty;
         invalid_bad := []; invalid_done := [];
         invalid_snapshots := inc_snapshots st |}.

  Definition invalid_codes (st : state) : list positive :=
    map fst (PTrieCode.elements (inc_values st)).

  Definition invalid_unseen (st : state) (acc : incremental_invalidation S.key) : nat :=
    length (filter (fun id =>
      match PTrieCode.get id (invalid_seen acc) with Some _ => false | None => true end)
      (invalid_codes st)).

  Definition invalid_measure (st : state) (acc : incremental_invalidation S.key) : nat :=
    invalid_unseen st acc + length (invalid_pending acc).

  Lemma invalid_codes_nodup : forall st, NoDup (invalid_codes st).
  Proof.
    intros st; unfold invalid_codes; apply PTrie.elements_nodup.
  Qed.

  Lemma invalid_code_present : forall st x, present st x = true ->
    In (S.key_code x) (invalid_codes st).
  Proof.
    intros st x Hpresent; unfold present, value, lookup in Hpresent.
    destruct (PTrieCode.get (S.key_code x) (inc_values st)) as [[y v]|]
      eqn:Hget; [|discriminate Hpresent].
    unfold invalid_codes; apply in_map_iff.
    exists (S.key_code x, (y, v)); split; [reflexivity|].
    apply (proj2 (PTrie.elements_spec _ _ _ _)); exact Hget.
  Qed.

  Lemma invalid_unseen_set : forall codes seen code,
    NoDup codes -> In code codes -> PTrieCode.get code seen = None ->
    length (filter (fun id =>
      match PTrieCode.get id (PTrieCode.set code tt seen) with
      | Some _ => false | None => true end) codes) + 1 =
    length (filter (fun id =>
      match PTrieCode.get id seen with Some _ => false | None => true end) codes).
  Proof.
    intros codes; induction codes as [|head rest IH]; intros seen code Hnodup Hin Hnone;
      [contradiction|].
    inversion Hnodup as [|? ? Habsent Hrest]; subst.
    destruct Hin as [Heq|Hin]; [subst head|].
    - cbn [filter]; rewrite PTrie.get_set_same, Hnone; cbn [length].
      assert (Htail : filter (fun id =>
          match PTrieCode.get id (PTrieCode.set code tt seen) with
          | Some _ => false | None => true end) rest =
        filter (fun id =>
          match PTrieCode.get id seen with Some _ => false | None => true end) rest).
      { apply filter_ext_in; intros id Hid.
        assert (Hneq : id <> code) by (intro Heq; subst; contradiction).
        rewrite PTrie.get_set_other by exact Hneq; reflexivity. }
      rewrite Htail; lia.
    - cbn [filter].
      assert (Hneq : head <> code) by (intro Heq; subst; contradiction).
      rewrite PTrie.get_set_other by exact Hneq.
      destruct (PTrieCode.get head seen); cbn [length];
        pose proof (IH seen code Hrest Hin Hnone) as Hrest_count; lia.
  Qed.

  Lemma invalid_seed_measure : forall st acc x,
    invalid_measure st (invalid_seed_one st acc x) = invalid_measure st acc.
  Proof.
    intros st acc x; unfold invalid_seed_one.
    destruct (present st x) eqn:Hpresent; [|reflexivity].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)) as [[]|]
      eqn:Hseen; [reflexivity|].
    unfold invalid_measure, invalid_unseen; cbn [invalid_pending invalid_seen length].
    pose proof (invalid_unseen_set (invalid_codes st) (invalid_seen acc)
      (S.key_code x) (invalid_codes_nodup st)
      (invalid_code_present st x Hpresent) Hseen) as Hcount.
    lia.
  Qed.

  Lemma invalid_seed_fold_measure : forall st xs acc,
    invalid_measure st (fold_left (invalid_seed_one st) xs acc) = invalid_measure st acc.
  Proof.
    intros st xs; induction xs as [|x rest IH]; intro acc; [reflexivity|].
    cbn [fold_left]; rewrite IH, invalid_seed_measure; reflexivity.
  Qed.

  Lemma invalid_snapshot_measure : forall st acc id,
    invalid_measure st (invalid_visit_snapshot st acc id) = invalid_measure st acc.
  Proof.
    intros st acc id; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|reflexivity].
    destruct (snapshot_live ss); [|reflexivity].
    unfold invalid_measure, invalid_unseen; cbn [invalid_pending invalid_seen].
    exact (invalid_seed_fold_measure st (snapshot_writes ss) acc).
  Qed.

  Lemma invalid_snapshot_fold_measure : forall st ids acc,
    invalid_measure st (fold_left (invalid_visit_snapshot st) ids acc) =
      invalid_measure st acc.
  Proof.
    intros st ids; induction ids as [|id rest IH]; intro acc; [reflexivity|].
    cbn [fold_left]; rewrite IH, invalid_snapshot_measure; reflexivity.
  Qed.

  Lemma invalid_step_measure : forall st acc next,
    invalid_step st acc = inl next ->
    invalid_measure st next < invalid_measure st acc.
  Proof.
    intros st [pending0 seen bad done snapshots] next Hstep.
    destruct pending0 as [|x pending]; cbn [invalid_step] in Hstep;
      [discriminate Hstep|].
    inversion Hstep; subst next; clear Hstep.
    unfold invalid_next.
    rewrite invalid_snapshot_fold_measure.
    unfold invalid_measure, invalid_unseen; cbn [invalid_pending invalid_seen length].
    lia.
  Qed.

  Definition invalid_lt (st : state) (next acc : incremental_invalidation S.key) : Prop :=
    (N.of_nat (invalid_measure st next) < N.of_nat (invalid_measure st acc))%N.

  Lemma invalid_step_lt : forall st acc next,
    invalid_step st acc = inl next -> invalid_lt st next acc.
  Proof.
    intros st acc next Hstep; unfold invalid_lt.
    pose proof (invalid_step_measure st acc next Hstep); lia.
  Qed.

  Lemma invalid_next_lt : forall st x pending seen bad done snapshots,
    invalid_lt st
      (invalid_next st x pending seen bad done snapshots)
      {| invalid_pending := x :: pending; invalid_seen := seen;
         invalid_bad := bad; invalid_done := done; invalid_snapshots := snapshots |}.
  Proof.
    intros st x pending seen bad done snapshots.
    eapply invalid_step_lt; reflexivity.
  Qed.

  Definition invalid_checked_step (st : state) (acc : incremental_invalidation S.key) :
      {next : incremental_invalidation S.key | invalid_lt st next acc} +
        incremental_invalidation S.key :=
    match acc with
    | {| invalid_pending := []; invalid_seen := seen; invalid_bad := bad;
         invalid_done := done; invalid_snapshots := snapshots |} =>
      inr {| invalid_pending := []; invalid_seen := seen; invalid_bad := bad;
             invalid_done := done; invalid_snapshots := snapshots |}
    | {| invalid_pending := x :: pending; invalid_seen := seen; invalid_bad := bad;
         invalid_done := done; invalid_snapshots := snapshots |} =>
      inl (exist _ (invalid_next st x pending seen bad done snapshots)
        (invalid_next_lt st x pending seen bad done snapshots))
    end.

  Definition invalid_accessible (st : state) (acc : incremental_invalidation S.key) :
      Acc (invalid_lt st) acc :=
    Acc_intro_generator 32
      (Wellfounded.Inverse_Image.wf_inverse_image _ N N.lt
        (fun current => N.of_nat (invalid_measure st current)) N.lt_wf_0) acc.

  Definition invalid_walk (p p' : S.prog) (ch : list S.row) (st : state)
      : incremental_invalidation S.key :=
    let initial := invalid_initial p p' ch st in
    Argent.Loop.loop (invalid_lt st) (invalid_checked_step st)
      initial (invalid_accessible st initial).

  Definition changed_seeds (p p' : S.prog) (ch : list S.row) (st : state) : list S.key :=
    footprint_adds S.key_eqb (present st) (changed_keys p p' ch) [].

  Definition invalidate_keys (p p' : S.prog) (ch : list S.row) (st : state) : list S.key :=
    invalid_bad (invalid_walk p p' ch st).

  Definition retire_snapshot (bad : list S.key) (ss : incremental_snapshot S.key)
      : incremental_snapshot S.key :=
    {| snapshot_owner := snapshot_owner ss;
       snapshot_writes := snapshot_writes ss;
       snapshot_live := snapshot_live ss &&
         negb (existsb (fun x => mem x bad) (snapshot_writes ss)) |}.

  Definition edit (p p' : S.prog) (ch : list S.row) (st : state) : state :=
    let result := invalid_walk p p' ch st in
    let bad := invalid_bad result in
    match bad with
    | [] => st
    | _ :: _ =>
      {| inc_values := remove_keys bad (inc_values st);
         inc_influence := remove_keys bad (inc_influence st);
         inc_cowrites := remove_keys bad (inc_cowrites st);
         inc_snapshots := invalid_snapshots result |}
    end.

  (** View fuel covers roots and every key occurrence of a listed row. *)
  Definition view_fuel (p : S.prog) (roots : list S.key) : N :=
    N.of_nat (Nat.succ (length roots +
      fold_right Nat.add 0%nat (map (fun r => length (row_keys p r)) (S.rows p)))).

  Definition discovery_view (p : S.prog) (roots : list S.key) (st : state)
      : list S.key * list S.row * list (S.key * L.t) :=
    match discovery p roots (view_fuel p roots) st with
    | Some result => result
    | None => ([], [], [])
    end.

  Definition discover (p : S.prog) (roots : list S.key) (st : state) : list S.key :=
    let '(ks, _, _) := discovery_view p roots st in ks.
  Definition region (p : S.prog) (roots : list S.key) (st : state) : list S.row :=
    let '(_, rs, _) := discovery_view p roots st in rs.
  Definition frozen (p : S.prog) (roots : list S.key) (st : state)
      : list (S.key * L.t) :=
    let '(_, _, fz) := discovery_view p roots st in fz.
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
  Module InvFacts := SourceBindingInventory L S Checker.
  Local Opaque loopN.
  Local Opaque invalid_accessible.

  Lemma discovery_rev_equation : forall p roots fuel st,
    discovery p roots fuel st =
      match loopN (discovery_step p st) fuel
        (fold_left (discovery_seed_one st) roots empty_discovery) with
      | inl _ => None
      | inr result => Some (rev (discovery_missing result),
          rev (discovery_rows result), rev (discovery_frozen result))
      end.
  Proof.
    intros p roots fuel st; unfold discovery.
    destruct (loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery));
      [reflexivity|].
    now rewrite <- !rev_alt.
  Qed.

  Lemma fill_local_eq_fill : forall xs m base,
    fill_local xs m base = fill xs m base.
  Proof.
    intros xs; induction xs as [|x rest IH]; intros m base; [reflexivity|].
    cbn [fill_local fill]; rewrite IH, Checker.look_spec; reflexivity.
  Qed.

  Definition invalid_buckets (st : state) (x : S.key) : list positive :=
    (match PTrieCode.get (S.key_code x) (inc_influence st) with
      | Some ids => ids | None => [] end) ++
    (match PTrieCode.get (S.key_code x) (inc_cowrites st) with
      | Some ids => ids | None => [] end).

  Definition row_snapshot_recorded (p : S.prog) (st : state)
      (r : S.row) (y : S.key) : Prop :=
    exists ss, snapshot_get (S.key_code (S.target p r)) st = Some ss /\
      snapshot_live ss = true /\
      (forall w, In w (S.writes p r) ->
        In w (snapshot_writes ss) /\
        In (S.key_code (S.target p r))
          (match PTrieCode.get (S.key_code w) (inc_cowrites st) with
            | Some ids => ids | None => [] end)) /\
      (forall x, In x (S.deps p r) ->
        In (S.key_code (S.target p r))
          (match PTrieCode.get (S.key_code x) (inc_influence st) with
            | Some ids => ids | None => [] end)).

  (** Tracked states carry the row metadata needed for local invalidation. *)
  Definition tracks (p : S.prog) (st : state) : Prop :=
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_snapshot_recorded p st r y.

  Lemma tracks_init : forall p, tracks p init.
  Proof.
    intros p r y Hr Hy [v Hvalue].
    unfold value, lookup, init in Hvalue; cbn [inc_values] in Hvalue.
    rewrite PTrie.get_empty in Hvalue; discriminate.
  Qed.

  Definition metadata_bucket_at (buckets : PTrieCode.t (list positive))
      (x : S.key) : list positive :=
    match PTrieCode.get (S.key_code x) buckets with
    | Some entries => entries | None => [] end.

  Lemma metadata_push_at : forall y id buckets x,
    metadata_bucket_at (push_entry y id buckets) x =
      if S.key_eqb x y then id :: metadata_bucket_at buckets x
      else metadata_bucket_at buckets x.
  Proof.
    intros y id buckets x; unfold push_entry, metadata_bucket_at.
    destruct (S.key_eqb_spec x y) as [->|Hneq].
    - rewrite PTrie.get_set_same; reflexivity.
    - rewrite PTrie.get_set_other; [reflexivity|].
      intro Heq; apply Hneq; now apply S.key_code_inj.
  Qed.

  Lemma metadata_push_keeps : forall ys id buckets x q,
    In q (metadata_bucket_at buckets x) ->
    In q (metadata_bucket_at
      (fold_left (fun acc y => push_entry y id acc) ys buckets) x).
  Proof.
    induction ys as [|y rest IH]; intros id buckets x q Hin; [exact Hin|].
    cbn [fold_left]; apply IH; rewrite metadata_push_at.
    destruct (S.key_eqb x y); [now right|exact Hin].
  Qed.

  Lemma metadata_push_add : forall ys id buckets x,
    In x ys -> In id (metadata_bucket_at
      (fold_left (fun acc y => push_entry y id acc) ys buckets) x).
  Proof.
    induction ys as [|y rest IH]; intros id buckets x Hin; [contradiction|].
    cbn [fold_left]; destruct Hin as [->|Hin].
    - apply metadata_push_keeps; rewrite metadata_push_at.
      destruct (S.key_eqb_spec x x); [now left|congruence].
    - apply IH; exact Hin.
  Qed.

  Definition metadata_previous_writes (st : state) id : list S.key :=
    match snapshot_get id st with
    | Some ss => if snapshot_live ss then snapshot_writes ss else []
    | None => [] end.

  Definition metadata_recorded_snapshot (st : state) owner writes
      : incremental_snapshot S.key :=
    {| snapshot_owner := owner;
       snapshot_writes := writes ++ metadata_previous_writes st (S.key_code owner);
       snapshot_live := true |}.

  Lemma metadata_record_row_get : forall p r st q,
    snapshot_get q (record_row p r st) =
      if Pos.eqb q (S.key_code (S.target p r))
      then Some (metadata_recorded_snapshot st (S.target p r) (row_writes p r))
      else snapshot_get q st.
  Proof.
    intros p r st q; unfold snapshot_get, record_row, snapshot_record, snapshot_set.
    cbn [inc_snapshots]; destruct (Pos.eqb q (S.key_code (S.target p r))) eqn:Hq.
    - apply Pos.eqb_eq in Hq; subst q; rewrite PTrie.get_set_same; reflexivity.
    - apply Pos.eqb_neq in Hq; rewrite PTrie.get_set_other by exact Hq; reflexivity.
  Qed.

  Lemma metadata_record_row_own : forall p r st,
    exists ss, snapshot_get (S.key_code (S.target p r)) (record_row p r st) = Some ss /\
      snapshot_live ss = true /\
      (forall w, In w (S.writes p r) -> In w (snapshot_writes ss) /\
        In (S.key_code (S.target p r))
          (metadata_bucket_at (inc_cowrites (record_row p r st)) w)) /\
      (forall x, In x (S.deps p r) ->
        In (S.key_code (S.target p r))
          (metadata_bucket_at (inc_influence (record_row p r st)) x)).
  Proof.
    intros p r st.
    exists (metadata_recorded_snapshot st (S.target p r) (row_writes p r)).
    split.
    - rewrite metadata_record_row_get, Pos.eqb_refl; reflexivity.
    - split; [reflexivity|split].
      + intros w Hw; split.
        * cbn [snapshot_writes]; apply in_or_app; now left.
        * change (In (S.key_code (S.target p r))
            (metadata_bucket_at
              (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
                (row_writes p r) (inc_cowrites st)) w)).
          apply metadata_push_add; exact Hw.
      + intros x Hx.
        change (In (S.key_code (S.target p r))
          (metadata_bucket_at
            (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
              (S.deps p r) (inc_influence st)) x)).
        apply metadata_push_add; exact Hx.
  Qed.

  Lemma metadata_record_row_preserves : forall p r st id ss ws ds,
    snapshot_get id st = Some ss -> snapshot_live ss = true ->
    (forall w, In w ws -> In w (snapshot_writes ss) /\
      In id (metadata_bucket_at (inc_cowrites st) w)) ->
    (forall x, In x ds -> In id (metadata_bucket_at (inc_influence st) x)) ->
    exists ss', snapshot_get id (record_row p r st) = Some ss' /\
      snapshot_live ss' = true /\
      (forall w, In w ws -> In w (snapshot_writes ss') /\
        In id (metadata_bucket_at (inc_cowrites (record_row p r st)) w)) /\
      (forall x, In x ds ->
        In id (metadata_bucket_at (inc_influence (record_row p r st)) x)).
  Proof.
    intros p r st id ss ws ds Hget Hlive Hwrites Hdeps.
    destruct (Pos.eqb id (S.key_code (S.target p r))) eqn:Hsame.
    - apply Pos.eqb_eq in Hsame; subst id.
      exists (metadata_recorded_snapshot st (S.target p r) (row_writes p r)).
      split; [now rewrite metadata_record_row_get, Pos.eqb_refl|].
      split; [reflexivity|split].
      + intros w Hw; destruct (Hwrites w Hw) as [Hwrite Hcowrite]; split.
        * cbn [metadata_recorded_snapshot snapshot_writes]; apply in_or_app; right.
          unfold metadata_previous_writes; rewrite Hget, Hlive; exact Hwrite.
        * change (In (S.key_code (S.target p r)) (metadata_bucket_at
            (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
              (row_writes p r) (inc_cowrites st)) w)).
          apply metadata_push_keeps; exact Hcowrite.
      + intros x Hx.
        change (In (S.key_code (S.target p r)) (metadata_bucket_at
          (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
            (S.deps p r) (inc_influence st)) x)).
        apply metadata_push_keeps; now apply Hdeps.
    - exists ss; split; [now rewrite metadata_record_row_get, Hsame|].
      split; [exact Hlive|split].
      + intros w Hw; destruct (Hwrites w Hw) as [Hwrite Hcowrite]; split;
          [exact Hwrite|].
        change (In id (metadata_bucket_at
          (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
            (row_writes p r) (inc_cowrites st)) w)).
        apply metadata_push_keeps; exact Hcowrite.
      + intros x Hx.
        change (In id (metadata_bucket_at
          (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
            (S.deps p r) (inc_influence st)) x)).
        apply metadata_push_keeps; now apply Hdeps.
  Qed.

  Lemma metadata_record_rows_preserves : forall p rs st id ss ws ds,
    snapshot_get id st = Some ss -> snapshot_live ss = true ->
    (forall w, In w ws -> In w (snapshot_writes ss) /\
      In id (metadata_bucket_at (inc_cowrites st) w)) ->
    (forall x, In x ds -> In id (metadata_bucket_at (inc_influence st) x)) ->
    exists ss', snapshot_get id (record_rows p rs st) = Some ss' /\
      snapshot_live ss' = true /\
      (forall w, In w ws -> In w (snapshot_writes ss') /\
        In id (metadata_bucket_at (inc_cowrites (record_rows p rs st)) w)) /\
      (forall x, In x ds ->
        In id (metadata_bucket_at (inc_influence (record_rows p rs st)) x)).
  Proof.
    intros p rs; induction rs as [|r rest IH]; intros st id ss ws ds
      Hget Hlive Hwrites Hdeps.
    - cbn [record_rows fold_left]; exists ss.
      split; [exact Hget|]; split; [exact Hlive|].
      split; [exact Hwrites|exact Hdeps].
    - cbn [record_rows fold_left].
      destruct (metadata_record_row_preserves p r st id ss ws ds
        Hget Hlive Hwrites Hdeps)
        as [ss' [Hget' [Hlive' [Hwrites' Hdeps']]]].
      exact (IH _ _ _ _ _ Hget' Hlive' Hwrites' Hdeps').
  Qed.

  Lemma metadata_record_rows_own : forall p rs st r, In r rs ->
    exists ss, snapshot_get (S.key_code (S.target p r)) (record_rows p rs st) = Some ss /\
      snapshot_live ss = true /\
      (forall w, In w (S.writes p r) -> In w (snapshot_writes ss) /\
        In (S.key_code (S.target p r))
          (metadata_bucket_at (inc_cowrites (record_rows p rs st)) w)) /\
      (forall x, In x (S.deps p r) ->
        In (S.key_code (S.target p r))
          (metadata_bucket_at (inc_influence (record_rows p rs st)) x)).
  Proof.
    intros p rs; induction rs as [|q rest IH]; intros st r Hr; [contradiction|].
    cbn [record_rows fold_left].
    destruct Hr as [->|Hr].
    - destruct (metadata_record_row_own p r st)
        as [ss [Hget [Hlive [Hwrites Hdeps]]]].
      exact (metadata_record_rows_preserves p rest (record_row p r st)
        (S.key_code (S.target p r)) ss (S.writes p r) (S.deps p r)
        Hget Hlive Hwrites Hdeps).
    - apply IH; exact Hr.
  Qed.

  Definition metadata_prepared_state (st : state) xs m : state :=
    clear_new_buckets xs (merge_discovered st xs m).

  Lemma metadata_prepared_snapshot : forall st xs m id,
    snapshot_get id (metadata_prepared_state st xs m) = snapshot_get id st.
  Proof.
    reflexivity.
  Qed.

  Lemma metadata_prepared_infl : forall st xs m x,
    metadata_bucket_at (inc_influence (metadata_prepared_state st xs m)) x =
      if InvFacts.Bindings.mem x xs then []
      else metadata_bucket_at (inc_influence st) x.
  Proof.
    intros st xs m x; unfold metadata_bucket_at, metadata_prepared_state,
      clear_new_buckets, merge_discovered; cbn [inc_influence].
    change (match PTrieCode.get (S.key_code x)
      (InvFacts.Bindings.remove_keys xs (inc_influence st)) with
      | Some ids => ids | None => [] end =
      if InvFacts.Bindings.mem x xs then []
      else metadata_bucket_at (inc_influence st) x).
    rewrite InvFacts.raw_get_remove_keys.
    destruct (InvFacts.Bindings.mem x xs); reflexivity.
  Qed.

  Lemma metadata_prepared_cowrite : forall st xs m x,
    metadata_bucket_at (inc_cowrites (metadata_prepared_state st xs m)) x =
      if InvFacts.Bindings.mem x xs then []
      else metadata_bucket_at (inc_cowrites st) x.
  Proof.
    intros st xs m x; unfold metadata_bucket_at, metadata_prepared_state,
      clear_new_buckets, merge_discovered; cbn [inc_cowrites].
    change (match PTrieCode.get (S.key_code x)
      (InvFacts.Bindings.remove_keys xs (inc_cowrites st)) with
      | Some ids => ids | None => [] end =
      if InvFacts.Bindings.mem x xs then []
      else metadata_bucket_at (inc_cowrites st) x).
    rewrite InvFacts.raw_get_remove_keys.
    destruct (InvFacts.Bindings.mem x xs); reflexivity.
  Qed.

  Lemma metadata_finish_preserves : forall p st xs rs m id ss ws ds,
    (forall x, In x xs -> value st x = None) ->
    (forall x, In x (ws ++ ds) -> dom st x) ->
    snapshot_get id st = Some ss -> snapshot_live ss = true ->
    (forall w, In w ws -> In w (snapshot_writes ss) /\
      In id (metadata_bucket_at (inc_cowrites st) w)) ->
    (forall x, In x ds -> In id (metadata_bucket_at (inc_influence st) x)) ->
    exists ss', snapshot_get id (finish_demand p st xs rs m) = Some ss' /\
      snapshot_live ss' = true /\
      (forall w, In w ws -> In w (snapshot_writes ss') /\
        In id (metadata_bucket_at (inc_cowrites (finish_demand p st xs rs m)) w)) /\
      (forall x, In x ds ->
        In id (metadata_bucket_at (inc_influence (finish_demand p st xs rs m)) x)).
  Proof.
    intros p st xs rs m id ss ws ds Hfresh Hdom Hget Hlive Hwrites Hdeps.
    assert (Houtside : forall x, dom st x -> InvFacts.Bindings.mem x xs = false).
    { intros x [v Hv]; destruct (InvFacts.Bindings.mem x xs) eqn:Hmem;
        [|reflexivity].
      apply (proj1 (InvFacts.mem_spec x xs)) in Hmem.
      rewrite (Hfresh x Hmem) in Hv; discriminate Hv. }
    unfold finish_demand.
    eapply (metadata_record_rows_preserves p rs
      (metadata_prepared_state st xs m) id ss ws ds).
    - change (snapshot_get id (metadata_prepared_state st xs m) = Some ss).
      now rewrite metadata_prepared_snapshot.
    - exact Hlive.
    - intros w Hw; destruct (Hwrites w Hw) as [Hwrite Hcowrite]; split;
        [exact Hwrite|].
      change (In id (metadata_bucket_at
        (inc_cowrites (metadata_prepared_state st xs m)) w)).
      rewrite metadata_prepared_cowrite,
        (Houtside w (Hdom w (in_or_app _ _ _ (or_introl Hw)))).
      exact Hcowrite.
    - intros x Hx.
      change (In id (metadata_bucket_at
        (inc_influence (metadata_prepared_state st xs m)) x)).
      rewrite metadata_prepared_infl,
        (Houtside x (Hdom x (in_or_app _ _ _ (or_intror Hx)))).
      now apply Hdeps.
  Qed.

  Definition discovery_balanced (acc : incremental_discovery S.key S.row L.t) : Prop :=
    length (discovery_missing acc) =
      length (discovery_pending acc) + length (discovery_done acc).

  Lemma discovery_visit_balanced : forall st x acc,
    discovery_balanced acc -> discovery_balanced (discovery_visit st x acc).
  Proof.
    intros st x acc Hbalance; unfold discovery_visit, discovery_balanced in *.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)); [exact Hbalance|].
    destruct (value st x); cbn [discovery_missing discovery_pending discovery_done length];
      lia.
  Qed.

  Lemma discovery_seed_balanced : forall st roots acc,
    discovery_balanced acc ->
    discovery_balanced (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hbalance;
      [exact Hbalance|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_balanced|exact Hbalance].
  Qed.

  Lemma discovery_row_balanced : forall p st r acc,
    discovery_balanced acc -> discovery_balanced (discovery_row p st acc r).
  Proof.
    intros p st r acc Hbalance; unfold discovery_row, discovery_balanced in *.
    cbn [discovery_pending discovery_missing discovery_done].
    assert (Hfold : forall xs current,
      discovery_balanced current ->
      discovery_balanced
        (fold_left (fun current x => discovery_visit st x current) xs current)).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_visit_balanced. }
    apply Hfold; exact Hbalance.
  Qed.

  Lemma discovery_step_balanced : forall p st acc next,
    discovery_balanced acc -> discovery_step p st acc = inl next ->
    discovery_balanced next.
  Proof.
    intros p st acc next Hbalance Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_balanced current ->
      discovery_balanced (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_balanced. }
    apply Hfold.
    unfold discovery_balanced in *; cbn [discovery_missing discovery_pending discovery_done].
    rewrite Hpending in Hbalance; cbn [length] in *; lia.
  Qed.

  Lemma discovery_visit_keeps_seen : forall st x acc y,
    PTrieCode.get (S.key_code y) (discovery_seen acc) = Some tt ->
    PTrieCode.get (S.key_code y) (discovery_seen (discovery_visit st x acc)) = Some tt.
  Proof.
    intros st x acc y Hseen; unfold discovery_visit.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|] eqn:Hx;
      [exact Hseen|].
    destruct (value st x); cbn [discovery_seen].
    all: destruct (Pos.eq_dec (S.key_code y) (S.key_code x)) as [Heq|Hneq].
    all: try (rewrite Heq, PTrie.get_set_same; reflexivity).
    all: rewrite PTrie.get_set_other by exact Hneq; exact Hseen.
  Qed.

  Lemma discovery_visit_marks : forall st x acc,
    PTrieCode.get (S.key_code x) (discovery_seen (discovery_visit st x acc)) = Some tt.
  Proof.
    intros st x acc; unfold discovery_visit.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|] eqn:Hx;
      [exact Hx|].
    destruct (value st x); cbn [discovery_seen]; now rewrite PTrie.get_set_same.
  Qed.

  Definition discovery_missing_valid (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    NoDup (discovery_missing acc) /\
    forall x, In x (discovery_missing acc) ->
      value st x = None /\
      PTrieCode.get (S.key_code x) (discovery_seen acc) = Some tt.

  Lemma discovery_visit_missing_valid : forall st x acc,
    discovery_missing_valid st acc ->
    discovery_missing_valid st (discovery_visit st x acc).
  Proof.
    intros st x acc [Hnodup Hmissing]; unfold discovery_visit.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|] eqn:Hx.
    - split; assumption.
    - destruct (value st x) as [v|] eqn:Hvalue.
      + split; [exact Hnodup|].
        intros y Hy; destruct (Hmissing y Hy) as [Hnone Hseen]; split;
          [exact Hnone|].
        cbn [discovery_seen].
        assert (Hneq : S.key_code y <> S.key_code x).
        { intro Heq; rewrite Heq in Hseen; congruence. }
        rewrite PTrie.get_set_other by exact Hneq; exact Hseen.
      + split.
        * constructor; [|exact Hnodup].
          intro Hin; destruct (Hmissing x Hin) as [_ Hseen]; congruence.
        * intros y [->|Hy]; [split; [exact Hvalue|]|].
          -- cbn [discovery_seen]; now rewrite PTrie.get_set_same.
          -- destruct (Hmissing y Hy) as [Hnone Hseen]; split;
               [exact Hnone|].
             cbn [discovery_seen].
             assert (Hneq : S.key_code y <> S.key_code x).
             { intro Heq; rewrite Heq in Hseen; congruence. }
             rewrite PTrie.get_set_other by exact Hneq; exact Hseen.
  Qed.

  Lemma discovery_seed_missing_valid : forall st roots acc,
    discovery_missing_valid st acc ->
    discovery_missing_valid st (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_missing_valid|exact Hvalid].
  Qed.

  Lemma discovery_row_missing_valid : forall p st r acc,
    discovery_missing_valid st acc -> discovery_missing_valid st (discovery_row p st acc r).
  Proof.
    intros p st r acc Hvalid; unfold discovery_row.
    cbn [discovery_missing discovery_seen].
    assert (Hfold : forall xs current, discovery_missing_valid st current ->
      discovery_missing_valid st
        (fold_left (fun current x => discovery_visit st x current) xs current)).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_visit_missing_valid. }
    apply Hfold; exact Hvalid.
  Qed.

  Lemma discovery_step_missing_valid : forall p st acc next,
    discovery_missing_valid st acc -> discovery_step p st acc = inl next ->
    discovery_missing_valid st next.
  Proof.
    intros p st acc next Hvalid Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_missing_valid st current ->
      discovery_missing_valid st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_missing_valid. }
    apply Hfold; unfold discovery_missing_valid in *.
    cbn [discovery_missing discovery_seen]; exact Hvalid.
  Qed.

  Lemma discovery_result_missing : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    NoDup ks /\ (forall x, In x ks -> value st x = None).
  Proof.
    intros p roots fuel st ks rs fz Hrun.
    rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_missing_valid st initial).
    { unfold initial; apply discovery_seed_missing_valid.
      unfold discovery_missing_valid, empty_discovery;
        cbn [discovery_missing discovery_seen]; split; [constructor|].
      intros x Hx; contradiction. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_missing_valid st) (discovery_missing_valid st)) as Hpreserve.
    assert (Hstep : forall acc, discovery_missing_valid st acc ->
      match discovery_step p st acc with
      | inl next => discovery_missing_valid st next
      | inr finished => discovery_missing_valid st finished
      end).
    { intros acc Hvalid; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_missing_valid; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hvalid|].
      discriminate Hnext. }
    specialize (Hpreserve Hstep fuel initial Hinitial).
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as <- <- <-.
    destruct Hpreserve as [Hnodup Hmissing]; split.
    - apply NoDup_rev; exact Hnodup.
    - intros x Hx; apply in_rev in Hx; exact (proj1 (Hmissing x Hx)).
  Qed.

  Lemma discovery_result_balanced : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    exists finished, loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished /\
      ks = rev (discovery_missing finished) /\
      discovery_balanced finished.
  Proof.
    intros p roots fuel st ks rs fz Hrun; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_balanced initial).
    { unfold initial; apply discovery_seed_balanced.
      unfold discovery_balanced, empty_discovery;
        cbn [discovery_missing discovery_pending discovery_done length]; lia. }
    assert (Hstep : forall acc, discovery_balanced acc ->
      match discovery_step p st acc with
      | inl next => discovery_balanced next
      | inr finished => discovery_balanced finished
      end).
    { intros acc Hbalance; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_balanced; eauto|].
      unfold discovery_step in Hnext; destruct (discovery_pending acc);
        [inversion Hnext; subst; exact Hbalance|discriminate Hnext]. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      discovery_balanced discovery_balanced Hstep fuel initial Hinitial) as Hbalance.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as <- <- <-.
    exists finished; split; [reflexivity|].
    split; [reflexivity|exact Hbalance].
  Qed.

  Lemma discovery_result_done : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    exists finished, loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished /\
      discovery_pending finished = [] /\
      length ks = length (discovery_done finished).
  Proof.
    intros p roots fuel st ks rs fz Hrun.
    destruct (discovery_result_balanced p roots fuel st ks rs fz Hrun)
      as [finished [Hloop [Hks Hbalanced]]].
    assert (Hstop : forall acc, True ->
      match discovery_step p st acc with
      | inl _ => True
      | inr result => discovery_pending result = []
      end).
    { intros acc _; unfold discovery_step.
      destruct (discovery_pending acc) as [|x pending] eqn:Hpending.
      - exact Hpending.
      - exact I. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (fun _ => True) (fun result => discovery_pending result = [])
      Hstop fuel (fold_left (discovery_seed_one st) roots empty_discovery) I) as Hresult.
    rewrite Hloop in Hresult.
    exists finished; split; [exact Hloop|].
    split; [exact Hresult|].
    rewrite Hks, length_rev.
    unfold discovery_balanced in Hbalanced; rewrite Hresult in Hbalanced.
    cbn [length] in Hbalanced; lia.
  Qed.

  Definition discovery_rows_listed (p : S.prog)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall r, In r (discovery_rows acc) -> In r (S.rows p).

  Lemma discovery_row_listed : forall p st acc r,
    discovery_rows_listed p acc -> In r (S.rows p) ->
    discovery_rows_listed p (discovery_row p st acc r).
  Proof.
    intros p st acc r Hlisted Hr r' Hin.
    unfold discovery_row in Hin; cbn [discovery_rows] in Hin.
    destruct Hin as [<-|Hin]; [exact Hr|].
    assert (Hrows : forall xs current,
      discovery_rows current = discovery_rows acc ->
      discovery_rows (fold_left (fun current x => discovery_visit st x current) xs current)
        = discovery_rows acc).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; unfold discovery_visit.
      destruct (PTrieCode.get (S.key_code x) (discovery_seen current));
        [exact Hcurrent|].
      destruct (value st x); cbn [discovery_rows]; exact Hcurrent. }
    rewrite (Hrows (row_keys p r) acc eq_refl) in Hin.
    now apply Hlisted.
  Qed.

  Lemma discovery_step_listed : forall p st acc next, S.wf p ->
    discovery_rows_listed p acc -> discovery_step p st acc = inl next ->
    discovery_rows_listed p next.
  Proof.
    intros p st acc next Hwf Hlisted Hstep.
    unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current,
      (forall r, In r rs -> In r (S.rows p)) ->
      discovery_rows_listed p current ->
      discovery_rows_listed p (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hrs Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH.
      - intros r' Hr'; apply Hrs; now right.
      - apply discovery_row_listed; [exact Hcurrent|].
        apply Hrs; now left. }
    apply Hfold.
    - intros r Hr; apply (proj1 (S.rows_of_spec p x r Hwf)) in Hr; exact (proj1 Hr).
    - unfold discovery_rows_listed in *; cbn [discovery_rows]; exact Hlisted.
  Qed.

  Lemma discovery_result_rows : forall p roots fuel st ks rs fz, S.wf p ->
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall r, In r rs -> In r (S.rows p).
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun.
    rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_rows_listed p initial).
    { unfold initial, discovery_rows_listed.
      intros r Hr.
      assert (Hseed : forall xs current,
        discovery_rows current = [] ->
        discovery_rows (fold_left (discovery_seed_one st) xs current) = []).
      { intros xs; induction xs as [|x rest IH]; intros current Hrows;
          [exact Hrows|].
        cbn [fold_left]; apply IH; unfold discovery_seed_one.
        destruct (missing st x); [|exact Hrows].
        unfold discovery_visit.
        destruct (PTrieCode.get (S.key_code x) (discovery_seen current));
          [exact Hrows|].
        destruct (value st x); cbn [discovery_rows]; exact Hrows. }
      rewrite (Hseed roots empty_discovery eq_refl) in Hr; contradiction. }
    assert (Hstep : forall acc, discovery_rows_listed p acc ->
      match discovery_step p st acc with
      | inl next => discovery_rows_listed p next
      | inr finished => discovery_rows_listed p finished
      end).
    { intros acc Hlisted; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_listed; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hlisted|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_rows_listed p) (discovery_rows_listed p)
      Hstep fuel initial Hinitial) as Hlisted.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as <- <- <-.
    intros r Hr; apply Hlisted; apply in_rev; exact Hr.
  Qed.

  Definition discovery_pending_missing (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x, In x (discovery_pending acc) -> value st x = None.

  Lemma discovery_visit_pending_missing : forall st x acc,
    discovery_pending_missing st acc ->
    discovery_pending_missing st (discovery_visit st x acc).
  Proof.
    intros st x acc Hvalid y Hin; unfold discovery_visit in Hin.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc));
      [now apply Hvalid|].
    destruct (value st x) as [old|] eqn:Hold;
      cbn [discovery_pending] in Hin.
    - now apply Hvalid.
    - destruct Hin as [<-|Hin]; [exact Hold|now apply Hvalid].
  Qed.

  Lemma discovery_seed_pending_missing : forall st roots acc,
    discovery_pending_missing st acc ->
    discovery_pending_missing st (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_pending_missing|exact Hvalid].
  Qed.

  Lemma discovery_row_pending_missing : forall p st r acc,
    discovery_pending_missing st acc ->
    discovery_pending_missing st (discovery_row p st acc r).
  Proof.
    intros p st r acc Hvalid; unfold discovery_row.
    cbn [discovery_pending].
    assert (Hfold : forall xs current, discovery_pending_missing st current ->
      discovery_pending_missing st
        (fold_left (fun current x => discovery_visit st x current) xs current)).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_visit_pending_missing. }
    apply Hfold; exact Hvalid.
  Qed.

  Lemma discovery_step_pending_missing : forall p st acc next,
    discovery_pending_missing st acc -> discovery_step p st acc = inl next ->
    discovery_pending_missing st next.
  Proof.
    intros p st acc next Hvalid Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_pending_missing st current ->
      discovery_pending_missing st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_pending_missing. }
    apply Hfold; unfold discovery_pending_missing in *.
    cbn [discovery_pending]; intros y Hy; apply Hvalid.
    rewrite Hpending; now right.
  Qed.

  Definition discovery_rows_new (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall r, In r (discovery_rows acc) ->
      exists y, In y (S.writes p r) /\ value st y = None.

  Lemma discovery_row_new : forall p st acc r,
    discovery_rows_new p st acc ->
    (exists y, In y (S.writes p r) /\ value st y = None) ->
    discovery_rows_new p st (discovery_row p st acc r).
  Proof.
    intros p st acc r Hnew Hr r' Hin.
    unfold discovery_row in Hin; cbn [discovery_rows] in Hin.
    destruct Hin as [<-|Hin]; [exact Hr|].
    assert (Hrows : forall xs current,
      discovery_rows current = discovery_rows acc ->
      discovery_rows (fold_left (fun current x => discovery_visit st x current) xs current)
        = discovery_rows acc).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; unfold discovery_visit.
      destruct (PTrieCode.get (S.key_code x) (discovery_seen current));
        [exact Hcurrent|].
      destruct (value st x); cbn [discovery_rows]; exact Hcurrent. }
    rewrite (Hrows (row_keys p r) acc eq_refl) in Hin.
    now apply Hnew.
  Qed.

  Definition discovery_state_new (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    discovery_pending_missing st acc /\ discovery_rows_new p st acc.

  Lemma discovery_step_new : forall p st acc next, S.wf p ->
    discovery_state_new p st acc -> discovery_step p st acc = inl next ->
    discovery_state_new p st next.
  Proof.
    intros p st acc next Hwf [Hpending Hrows] Hstep.
    unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending_eq;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hx : value st x = None).
    { apply Hpending; rewrite Hpending_eq; now left. }
    assert (Hfold : forall rs current,
      (forall r, In r rs -> In x (S.writes p r)) ->
      discovery_state_new p st current ->
      discovery_state_new p st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hwrites Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH.
      - intros r' Hr'; apply Hwrites; now right.
      - destruct Hcurrent as [Hcurrent_pending Hcurrent_rows]; split.
        + now apply discovery_row_pending_missing.
        + apply discovery_row_new; [exact Hcurrent_rows|].
          exists x; split; [apply Hwrites; now left|exact Hx]. }
    apply Hfold.
    - intros r Hr; apply (proj1 (S.rows_of_spec p x r Hwf)) in Hr; exact (proj2 Hr).
    - split.
      + intros y Hy; apply Hpending; rewrite Hpending_eq; now right.
      + exact Hrows.
  Qed.

  Lemma discovery_result_rows_new : forall p roots fuel st ks rs fz, S.wf p ->
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall r, In r rs -> exists y, In y (S.writes p r) /\ value st y = None.
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_state_new p st initial).
    { unfold initial, discovery_state_new; split.
      - apply discovery_seed_pending_missing.
        unfold discovery_pending_missing, empty_discovery;
          cbn [discovery_pending].
        intros x Hin; contradiction.
      - unfold discovery_rows_new.
        intros r Hr.
        assert (Hseed : forall xs current,
          discovery_rows current = [] ->
          discovery_rows (fold_left (discovery_seed_one st) xs current) = []).
        { intros xs; induction xs as [|x rest IH]; intros current Hrows;
            [exact Hrows|].
          cbn [fold_left]; apply IH; unfold discovery_seed_one.
          destruct (missing st x); [|exact Hrows].
          unfold discovery_visit.
          destruct (PTrieCode.get (S.key_code x) (discovery_seen current));
            [exact Hrows|].
          destruct (value st x); cbn [discovery_rows]; exact Hrows. }
        rewrite (Hseed roots empty_discovery eq_refl) in Hr; contradiction. }
    assert (Hstep : forall acc, discovery_state_new p st acc ->
      match discovery_step p st acc with
      | inl next => discovery_state_new p st next
      | inr finished => discovery_state_new p st finished
      end).
    { intros acc Hvalid; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_new; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hvalid|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_state_new p st) (discovery_state_new p st)
      Hstep fuel initial Hinitial) as Hvalid.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as <- <- <-.
    intros r Hr; apply (proj2 Hvalid); apply in_rev; exact Hr.
  Qed.

  Definition discovery_seen_missing (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x, value st x = None ->
      PTrieCode.get (S.key_code x) (discovery_seen acc) = Some tt ->
      In x (discovery_missing acc).

  Lemma discovery_visit_seen_missing : forall st x acc,
    discovery_seen_missing st acc ->
    discovery_seen_missing st (discovery_visit st x acc).
  Proof.
    intros st x acc Hvalid y Hnone Hseen.
    unfold discovery_visit in Hseen |- *.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|]
      eqn:Hx; [now apply Hvalid|].
    destruct (value st x) as [v|] eqn:Hvalue;
      cbn [discovery_seen discovery_missing] in Hseen |- *.
    all: destruct (Pos.eq_dec (S.key_code y) (S.key_code x)) as [Heq|Hneq].
    - pose proof (S.key_code_inj y x Heq) as ->; congruence.
    - rewrite PTrie.get_set_other in Hseen by exact Hneq.
      now apply Hvalid.
    - pose proof (S.key_code_inj y x Heq) as ->; now left.
    - rewrite PTrie.get_set_other in Hseen by exact Hneq.
      right; now apply Hvalid.
  Qed.

  Lemma discovery_seed_seen_missing : forall st roots acc,
    discovery_seen_missing st acc ->
    discovery_seen_missing st (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_seen_missing|exact Hvalid].
  Qed.

  Lemma discovery_row_seen_missing : forall p st r acc,
    discovery_seen_missing st acc ->
    discovery_seen_missing st (discovery_row p st acc r).
  Proof.
    intros p st r acc Hvalid; unfold discovery_row.
    cbn [discovery_seen discovery_missing].
    assert (Hfold : forall xs current, discovery_seen_missing st current ->
      discovery_seen_missing st
        (fold_left (fun current x => discovery_visit st x current) xs current)).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_visit_seen_missing. }
    apply Hfold; exact Hvalid.
  Qed.

  Lemma discovery_step_seen_missing : forall p st acc next,
    discovery_seen_missing st acc -> discovery_step p st acc = inl next ->
    discovery_seen_missing st next.
  Proof.
    intros p st acc next Hvalid Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_seen_missing st current ->
      discovery_seen_missing st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_seen_missing. }
    apply Hfold; unfold discovery_seen_missing in *.
    cbn [discovery_seen discovery_missing]; exact Hvalid.
  Qed.

  Lemma discovery_visit_missing_keeps : forall st x acc y,
    In y (discovery_missing acc) ->
    In y (discovery_missing (discovery_visit st x acc)).
  Proof.
    intros st x acc y Hy; unfold discovery_visit.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc));
      [exact Hy|].
    destruct (value st x); cbn [discovery_missing]; [exact Hy|now right].
  Qed.

  Lemma discovery_fold_visit_missing_keeps : forall st xs acc y,
    In y (discovery_missing acc) ->
    In y (discovery_missing
      (fold_left (fun current x => discovery_visit st x current) xs acc)).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc y Hy;
      [exact Hy|].
    cbn [fold_left]; apply IH; now apply discovery_visit_missing_keeps.
  Qed.

  Lemma discovery_fold_visit_seen_keeps : forall st xs acc y,
    PTrieCode.get (S.key_code y) (discovery_seen acc) = Some tt ->
    PTrieCode.get (S.key_code y)
      (discovery_seen
        (fold_left (fun current x => discovery_visit st x current) xs acc)) = Some tt.
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc y Hy;
      [exact Hy|].
    cbn [fold_left]; apply IH; now apply discovery_visit_keeps_seen.
  Qed.

  Lemma discovery_fold_visit_marks : forall st xs acc y, In y xs ->
    PTrieCode.get (S.key_code y)
      (discovery_seen
        (fold_left (fun current x => discovery_visit st x current) xs acc)) = Some tt.
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc y Hy;
      [contradiction|].
    cbn [fold_left]; destruct Hy as [<-|Hy].
    - apply discovery_fold_visit_seen_keeps; apply discovery_visit_marks.
    - now apply IH.
  Qed.

  Definition discovery_rows_support (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall r x, In r (discovery_rows acc) -> In x (row_keys p r) ->
      value st x = None -> In x (discovery_missing acc).

  Lemma discovery_row_support : forall p st r acc,
    discovery_seen_missing st acc -> discovery_rows_support p st acc ->
    discovery_rows_support p st (discovery_row p st acc r).
  Proof.
    intros p st r acc Hseen Hsupport r' x Hr Hx Hnone.
    unfold discovery_row in Hr |- *; cbn [discovery_rows discovery_missing] in Hr |- *.
    destruct Hr as [<-|Hr].
    - apply (discovery_row_seen_missing p st r acc Hseen x Hnone).
      unfold discovery_row; cbn [discovery_seen].
      now apply discovery_fold_visit_marks.
    - assert (Hrows : forall xs current,
        discovery_rows current = discovery_rows acc ->
        discovery_rows
          (fold_left (fun current y => discovery_visit st y current) xs current) =
          discovery_rows acc).
      { intros xs; induction xs as [|y rest IH]; intros current Hcurrent;
          [exact Hcurrent|].
        cbn [fold_left]; apply IH; unfold discovery_visit.
        destruct (PTrieCode.get (S.key_code y) (discovery_seen current));
          [exact Hcurrent|].
        destruct (value st y); cbn [discovery_rows]; exact Hcurrent. }
      rewrite (Hrows (row_keys p r) acc eq_refl) in Hr.
      apply discovery_fold_visit_missing_keeps.
      now apply (Hsupport r' x Hr Hx Hnone).
  Qed.

  Definition discovery_support_state (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    discovery_seen_missing st acc /\ discovery_rows_support p st acc.

  Lemma discovery_seed_support_state : forall p st roots acc,
    discovery_support_state p st acc ->
    discovery_support_state p st (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros p st roots; induction roots as [|x rest IH]; intros acc [Hseen Hsupport];
      [now split|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [|now split].
    split; [now apply discovery_visit_seen_missing|].
    intros r y Hr Hy Hnone; unfold discovery_visit in Hr |- *.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc));
      [eapply Hsupport; eauto|].
    destruct (value st x); cbn [discovery_rows discovery_missing] in Hr |- *.
    - eapply Hsupport; eauto.
    - right; eapply Hsupport; eauto.
  Qed.

  Lemma discovery_step_support_state : forall p st acc next,
    discovery_support_state p st acc -> discovery_step p st acc = inl next ->
    discovery_support_state p st next.
  Proof.
    intros p st acc next [Hseen Hsupport] Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_support_state p st current ->
      discovery_support_state p st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; destruct Hcurrent as [Hcurrent_seen Hcurrent_support].
      split.
      - now apply discovery_row_seen_missing.
      - now apply discovery_row_support. }
    apply Hfold; split.
    - unfold discovery_seen_missing in *;
        cbn [discovery_seen discovery_missing]; exact Hseen.
    - unfold discovery_rows_support in *;
        cbn [discovery_rows discovery_missing]; exact Hsupport.
  Qed.

  Lemma discovery_result_support : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall r x, In r rs -> In x (row_keys p r) ->
      dom st x \/ In x ks.
  Proof.
    intros p roots fuel st ks rs fz Hrun; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_support_state p st initial).
    { unfold initial; apply discovery_seed_support_state.
      split.
      - unfold discovery_seen_missing, empty_discovery;
          cbn [discovery_seen discovery_missing].
        intros x Hnone Hseen; rewrite PTrie.get_empty in Hseen; discriminate Hseen.
      - unfold discovery_rows_support, empty_discovery;
          cbn [discovery_rows].
        intros r x Hr; contradiction. }
    assert (Hstep : forall acc, discovery_support_state p st acc ->
      match discovery_step p st acc with
      | inl next => discovery_support_state p st next
      | inr finished => discovery_support_state p st finished
      end).
    { intros acc Hvalid; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_support_state; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hvalid|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_support_state p st) (discovery_support_state p st)
      Hstep fuel initial Hinitial) as Hvalid.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as <- <- <-.
    intros r x Hr Hx; destruct (value st x) as [v|] eqn:Hvalue.
    - left; exists v; exact Hvalue.
    - right.
      apply in_rev in Hr.
      assert (Hraw : In x (discovery_missing finished)).
      { eapply (proj2 Hvalid); eauto. }
      apply in_rev in Hraw; exact Hraw.
  Qed.

  Definition discovery_missing_queued
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x, In x (discovery_missing acc) ->
      In x (discovery_pending acc) \/ In x (discovery_done acc).

  Lemma discovery_visit_missing_queued : forall st x acc,
    discovery_missing_queued acc -> discovery_missing_queued (discovery_visit st x acc).
  Proof.
    intros st x acc Hqueued y Hy; unfold discovery_visit in Hy |- *.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc));
      [now apply Hqueued|].
    destruct (value st x); cbn [discovery_missing discovery_pending discovery_done] in Hy |- *.
    - now apply Hqueued.
    - destruct Hy as [<-|Hy]; [left; now left|].
      destruct (Hqueued y Hy) as [Hpending|Hdone].
      + left; now right.
      + right; exact Hdone.
  Qed.

  Lemma discovery_seed_missing_queued : forall st roots acc,
    discovery_missing_queued acc ->
    discovery_missing_queued (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hqueued;
      [exact Hqueued|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_missing_queued|exact Hqueued].
  Qed.

  Lemma discovery_row_missing_queued : forall p st r acc,
    discovery_missing_queued acc -> discovery_missing_queued (discovery_row p st acc r).
  Proof.
    intros p st r acc Hqueued; unfold discovery_row.
    cbn [discovery_missing discovery_pending discovery_done].
    assert (Hfold : forall xs current, discovery_missing_queued current ->
      discovery_missing_queued
        (fold_left (fun current x => discovery_visit st x current) xs current)).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_visit_missing_queued. }
    apply Hfold; exact Hqueued.
  Qed.

  Lemma discovery_step_missing_queued : forall p st acc next,
    discovery_missing_queued acc -> discovery_step p st acc = inl next ->
    discovery_missing_queued next.
  Proof.
    intros p st acc next Hqueued Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_missing_queued current ->
      discovery_missing_queued (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_missing_queued. }
    apply Hfold; intros y Hy.
    destruct (Hqueued y Hy) as [Hbefore|Hdone].
    - rewrite Hpending in Hbefore; destruct Hbefore as [<-|Htail].
      + right; now left.
      + left; exact Htail.
    - right; now right.
  Qed.

  Lemma discovery_result_processed : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    exists finished, loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished /\
      (forall x, In x ks -> In x (discovery_done finished)).
  Proof.
    intros p roots fuel st ks rs fz Hrun.
    destruct (discovery_result_done p roots fuel st ks rs fz Hrun)
      as [finished [Hloop [Hpending _]]].
    assert (Hinitial : discovery_missing_queued
      (fold_left (discovery_seed_one st) roots empty_discovery)).
    { apply discovery_seed_missing_queued.
      unfold discovery_missing_queued, empty_discovery;
        cbn [discovery_missing].
      intros x Hin; contradiction. }
    assert (Hstep : forall acc, discovery_missing_queued acc ->
      match discovery_step p st acc with
      | inl next => discovery_missing_queued next
      | inr result => discovery_missing_queued result
      end).
    { intros acc Hqueued; destruct (discovery_step p st acc) as [next|result]
        eqn:Hnext; [eapply discovery_step_missing_queued; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hqueued|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      discovery_missing_queued discovery_missing_queued Hstep fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) Hinitial) as Hqueued.
    rewrite Hloop in Hqueued.
    exists finished; split; [exact Hloop|].
    intros x Hx.
    rewrite discovery_rev_equation in Hrun; rewrite Hloop in Hrun; cbn in Hrun.
    injection Hrun as Hks _ _; subst ks.
    apply in_rev in Hx.
    destruct (Hqueued x Hx) as [Hbad|Hdone];
      [rewrite Hpending in Hbad; contradiction|exact Hdone].
  Qed.

  Lemma discovery_row_rows : forall p st acc r,
    discovery_rows (discovery_row p st acc r) = r :: discovery_rows acc.
  Proof.
    intros p st acc r; unfold discovery_row; cbn [discovery_rows].
    assert (Hfold : forall xs current,
      discovery_rows (fold_left (fun current x => discovery_visit st x current) xs current) =
      discovery_rows current).
    { intros xs; induction xs as [|x rest IH]; intros current; [reflexivity|].
      cbn [fold_left]; rewrite IH; unfold discovery_visit.
      destruct (PTrieCode.get (S.key_code x) (discovery_seen current));
        [reflexivity|].
      destruct (value st x); reflexivity. }
    now rewrite Hfold.
  Qed.

  Lemma discovery_row_done : forall p st acc r,
    discovery_done (discovery_row p st acc r) = discovery_done acc.
  Proof.
    intros p st acc r; unfold discovery_row; cbn [discovery_done].
    assert (Hfold : forall xs current,
      discovery_done (fold_left (fun current x => discovery_visit st x current) xs current) =
      discovery_done current).
    { intros xs; induction xs as [|x rest IH]; intros current; [reflexivity|].
      cbn [fold_left]; rewrite IH; unfold discovery_visit.
      destruct (PTrieCode.get (S.key_code x) (discovery_seen current));
        [reflexivity|].
      destruct (value st x); reflexivity. }
    now rewrite Hfold.
  Qed.

  Lemma discovery_step_done_count : forall p st acc next,
    discovery_step p st acc = inl next ->
    length (discovery_done next) = S (length (discovery_done acc)).
  Proof.
    intros p st acc next Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current,
      discovery_done (fold_left (discovery_row p st) rs current) = discovery_done current).
    { intros rs; induction rs as [|r rest IH]; intros current;
        [reflexivity|].
      cbn [fold_left]; rewrite IH, discovery_row_done; reflexivity. }
    rewrite Hfold; cbn [discovery_done length]; reflexivity.
  Qed.

  Lemma discovery_seed_done_empty : forall st roots,
    discovery_done (fold_left (discovery_seed_one st) roots empty_discovery) = [].
  Proof.
    intros st roots.
    assert (Hseed_one : forall acc y,
      discovery_done (discovery_seed_one st acc y) = discovery_done acc).
    { intros acc y; unfold discovery_seed_one.
      destruct (missing st y); [|reflexivity].
      unfold discovery_visit.
      destruct (PTrieCode.get (S.key_code y) (discovery_seen acc));
        [reflexivity|].
      destruct (value st y); reflexivity. }
    assert (Hseed : forall xs acc,
      discovery_done (fold_left (discovery_seed_one st) xs acc) = discovery_done acc).
    { intros xs; induction xs as [|y rest IH]; intro acc; [reflexivity|].
      cbn [fold_left]; rewrite IH, Hseed_one; reflexivity. }
    rewrite Hseed; reflexivity.
  Qed.

  Lemma discovery_finished_replay : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall more, (N.of_nat (length ks) < more)%N ->
      discovery p roots more st = Some (ks, rs, fz).
  Proof.
    intros p roots fuel st ks rs fz Hrun more Hmore.
    destruct (discovery_result_done p roots fuel st ks rs fz Hrun)
      as [finished [Hloop [_ Hlen]]].
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hcount : forall acc next,
      discovery_step p st acc = inl next ->
      length (discovery_done next) = S (length (discovery_done acc))).
    { intros acc next Hstep; now apply discovery_step_done_count with (p := p) (st := st). }
    assert (Hstop : forall acc result,
      discovery_step p st acc = inr result ->
      length (discovery_done result) = length (discovery_done acc)).
    { intros acc result Hstep; unfold discovery_step in Hstep.
      destruct (discovery_pending acc); [inversion Hstep; reflexivity|discriminate]. }
    rewrite incremental_loopN_fuel in Hloop.
    destruct (incremental_loop_fuel_replay (discovery_step p st)
      (fun acc => length (discovery_done acc)) Hcount Hstop
      (N.to_nat fuel) initial finished Hloop)
      as [steps [_ [Hsteps Hreplay]]].
    assert (Hinitial : length (discovery_done initial) = 0).
    { unfold initial; rewrite discovery_seed_done_empty; reflexivity. }
    assert (Hsteps_len : steps = length ks) by lia.
    assert (Hmore_nat : steps < N.to_nat more).
    { rewrite Hsteps_len; lia. }
    pose proof (Hreplay (N.to_nat more) Hmore_nat) as Hloop_more.
    unfold initial in Hloop, Hloop_more.
    unfold discovery in Hrun |- *; rewrite incremental_loopN_fuel, Hloop_more.
    rewrite incremental_loopN_fuel, Hloop in Hrun.
    exact Hrun.
  Qed.

  Lemma discovery_fold_rows_old : forall p st rs acc r,
    In r (discovery_rows acc) ->
    In r (discovery_rows (fold_left (discovery_row p st) rs acc)).
  Proof.
    intros p st rs; induction rs as [|next rest IH]; intros acc r Hr;
      [exact Hr|].
    cbn [fold_left]; apply IH; rewrite discovery_row_rows; now right.
  Qed.

  Lemma discovery_fold_rows_new : forall p st rs acc r,
    In r rs -> In r (discovery_rows (fold_left (discovery_row p st) rs acc)).
  Proof.
    intros p st rs; induction rs as [|next rest IH]; intros acc r Hr;
      [contradiction|].
    cbn [fold_left]; destruct Hr as [<-|Hr].
    - apply discovery_fold_rows_old; rewrite discovery_row_rows; now left.
    - now apply IH.
  Qed.

  Lemma discovery_fold_done : forall p st rs acc,
    discovery_done (fold_left (discovery_row p st) rs acc) = discovery_done acc.
  Proof.
    intros p st rs; induction rs as [|r rest IH]; intro acc;
      [reflexivity|].
    cbn [fold_left]; rewrite IH, discovery_row_done; reflexivity.
  Qed.

  Definition discovery_done_rows (p : S.prog)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x, In x (discovery_done acc) ->
      forall r, In r (S.rows_of p x) -> In r (discovery_rows acc).

  Lemma discovery_step_done_rows : forall p st acc next,
    discovery_done_rows p acc -> discovery_step p st acc = inl next ->
    discovery_done_rows p next.
  Proof.
    intros p st acc next Hdone Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    unfold discovery_done_rows in *.
    intros y Hy r Hr.
    rewrite discovery_fold_done in Hy.
    cbn [discovery_done] in Hy.
    destruct Hy as [<-|Hy].
    - now apply discovery_fold_rows_new.
    - apply discovery_fold_rows_old; now apply (Hdone y Hy).
  Qed.

  Lemma discovery_result_done_rows : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall x r, In x ks -> In r (S.rows_of p x) -> In r rs.
  Proof.
    intros p roots fuel st ks rs fz Hrun x r Hx Hr.
    destruct (discovery_result_processed p roots fuel st ks rs fz Hrun)
      as [finished [Hloop Hprocessed]].
    assert (Hinitial : discovery_done_rows p
      (fold_left (discovery_seed_one st) roots empty_discovery)).
    { unfold discovery_done_rows.
      assert (Hseed : forall xs current,
        discovery_done current = [] ->
        discovery_done (fold_left (discovery_seed_one st) xs current) = []).
      { intros xs; induction xs as [|y rest IH]; intros current Hdone;
          [exact Hdone|].
        cbn [fold_left]; apply IH; unfold discovery_seed_one.
        destruct (missing st y); [|exact Hdone].
        unfold discovery_visit.
        destruct (PTrieCode.get (S.key_code y) (discovery_seen current));
          [exact Hdone|].
        destruct (value st y); cbn [discovery_done]; exact Hdone. }
      intros y Hy; rewrite (Hseed roots empty_discovery eq_refl) in Hy;
        contradiction. }
    assert (Hstep : forall acc, discovery_done_rows p acc ->
      match discovery_step p st acc with
      | inl next => discovery_done_rows p next
      | inr result => discovery_done_rows p result
      end).
    { intros acc Hdone; destruct (discovery_step p st acc) as [next|result]
        eqn:Hnext; [eapply discovery_step_done_rows; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hdone|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_done_rows p) (discovery_done_rows p) Hstep fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) Hinitial) as Hdone.
    rewrite Hloop in Hdone.
    rewrite discovery_rev_equation in Hrun; rewrite Hloop in Hrun; cbn in Hrun.
    injection Hrun as _ Hrs _; subst rs.
    assert (Hraw : In r (discovery_rows finished)).
    { apply (Hdone x); [exact (Hprocessed x Hx)|exact Hr]. }
    apply in_rev in Hraw; exact Hraw.
  Qed.

  Definition discovery_frozen_valid (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x v, In (x, v) (discovery_frozen acc) -> value st x = Some v.

  Lemma discovery_visit_frozen_valid : forall st x acc,
    discovery_frozen_valid st acc ->
    discovery_frozen_valid st (discovery_visit st x acc).
  Proof.
    intros st x acc Hvalid y v Hin; unfold discovery_visit in Hin.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc));
      [now apply Hvalid|].
    destruct (value st x) as [old|] eqn:Hold;
      cbn [discovery_frozen] in Hin.
    - destruct Hin as [Heq|Hin]; [injection Heq as <- <-; exact Hold|].
      now apply Hvalid.
    - now apply Hvalid.
  Qed.

  Lemma discovery_seed_frozen_valid : forall st roots acc,
    discovery_frozen_valid st acc ->
    discovery_frozen_valid st (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_frozen_valid|exact Hvalid].
  Qed.

  Lemma discovery_row_frozen_valid : forall p st r acc,
    discovery_frozen_valid st acc ->
    discovery_frozen_valid st (discovery_row p st acc r).
  Proof.
    intros p st r acc Hvalid; unfold discovery_row.
    cbn [discovery_frozen].
    assert (Hfold : forall xs current, discovery_frozen_valid st current ->
      discovery_frozen_valid st
        (fold_left (fun current x => discovery_visit st x current) xs current)).
    { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_visit_frozen_valid. }
    apply Hfold; exact Hvalid.
  Qed.

  Lemma discovery_step_frozen_valid : forall p st acc next,
    discovery_frozen_valid st acc -> discovery_step p st acc = inl next ->
    discovery_frozen_valid st next.
  Proof.
    intros p st acc next Hvalid Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_frozen_valid st current ->
      discovery_frozen_valid st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_frozen_valid. }
    apply Hfold; unfold discovery_frozen_valid in *.
    cbn [discovery_frozen]; exact Hvalid.
  Qed.

  Lemma discovery_result_frozen : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall x v, In (x, v) fz -> value st x = Some v.
  Proof.
    intros p roots fuel st ks rs fz Hrun; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_frozen_valid st initial).
    { unfold initial; apply discovery_seed_frozen_valid.
      unfold discovery_frozen_valid, empty_discovery;
        cbn [discovery_frozen].
      intros x v Hin; contradiction. }
    assert (Hstep : forall acc, discovery_frozen_valid st acc ->
      match discovery_step p st acc with
      | inl next => discovery_frozen_valid st next
      | inr finished => discovery_frozen_valid st finished
      end).
    { intros acc Hvalid; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_frozen_valid; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hvalid|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_frozen_valid st) (discovery_frozen_valid st)
      Hstep fuel initial Hinitial) as Hvalid.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as <- <- <-.
    intros x v Hin; apply Hvalid; apply in_rev; exact Hin.
  Qed.

  Definition discovery_seen_frozen (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x v, value st x = Some v ->
      PTrieCode.get (S.key_code x) (discovery_seen acc) = Some tt ->
      In (x, v) (discovery_frozen acc).

  Lemma discovery_visit_seen_frozen : forall st x acc,
    discovery_seen_frozen st acc ->
    discovery_seen_frozen st (discovery_visit st x acc).
  Proof.
    intros st x acc Hvalid y v Hvalue Hseen.
    unfold discovery_visit in Hseen |- *.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|]
      eqn:Hx; [now apply Hvalid|].
    destruct (value st x) as [old|] eqn:Hold;
      cbn [discovery_seen discovery_frozen] in Hseen |- *.
    - destruct (Pos.eq_dec (S.key_code y) (S.key_code x)) as [Heq|Hneq].
      + pose proof (S.key_code_inj y x Heq) as ->.
        rewrite Hold in Hvalue; injection Hvalue as <-; now left.
      + rewrite PTrie.get_set_other in Hseen by exact Hneq.
        right; now apply Hvalid.
    - destruct (Pos.eq_dec (S.key_code y) (S.key_code x)) as [Heq|Hneq].
      + pose proof (S.key_code_inj y x Heq) as ->; congruence.
      + rewrite PTrie.get_set_other in Hseen by exact Hneq.
        now apply Hvalid.
  Qed.

  Lemma discovery_seed_seen_frozen : forall st roots acc,
    discovery_seen_frozen st acc ->
    discovery_seen_frozen st (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_seen_frozen|exact Hvalid].
  Qed.

  Lemma discovery_row_seen_frozen : forall p st r acc,
    discovery_seen_frozen st acc ->
    discovery_seen_frozen st (discovery_row p st acc r).
  Proof.
    intros p st r acc Hvalid; unfold discovery_row.
    cbn [discovery_seen discovery_frozen].
    induction (row_keys p r) as [|x xs IH] in acc, Hvalid |- *;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply discovery_visit_seen_frozen.
  Qed.

  Lemma discovery_step_seen_frozen : forall p st acc next,
    discovery_seen_frozen st acc -> discovery_step p st acc = inl next ->
    discovery_seen_frozen st next.
  Proof.
    intros p st acc next Hvalid Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_seen_frozen st current ->
      discovery_seen_frozen st (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_seen_frozen. }
    apply Hfold; unfold discovery_seen_frozen in *.
    cbn [discovery_seen discovery_frozen]; exact Hvalid.
  Qed.

  Definition discovery_rows_marked (p : S.prog)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall r x, In r (discovery_rows acc) -> In x (row_keys p r) ->
      PTrieCode.get (S.key_code x) (discovery_seen acc) = Some tt.

  Lemma discovery_row_marked : forall p st acc r,
    discovery_rows_marked p acc ->
    discovery_rows_marked p (discovery_row p st acc r).
  Proof.
    intros p st acc r Hmarked q x Hq Hx.
    rewrite discovery_row_rows in Hq.
    unfold discovery_row; cbn [discovery_seen].
    destruct Hq as [<-|Hq].
    - now apply discovery_fold_visit_marks.
    - apply discovery_fold_visit_seen_keeps; exact (Hmarked q x Hq Hx).
  Qed.

  Lemma discovery_step_marked : forall p st acc next,
    discovery_rows_marked p acc -> discovery_step p st acc = inl next ->
    discovery_rows_marked p next.
  Proof.
    intros p st acc next Hmarked Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, discovery_rows_marked p current ->
      discovery_rows_marked p (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_marked. }
    apply Hfold; unfold discovery_rows_marked in *.
    cbn [discovery_rows discovery_seen]; exact Hmarked.
  Qed.

  Lemma discovery_result_marked : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall r x, In r rs -> In x (row_keys p r) ->
      exists finished, loopN (discovery_step p st) fuel
        (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished /\
        PTrieCode.get (S.key_code x) (discovery_seen finished) = Some tt.
  Proof.
    intros p roots fuel st ks rs fz Hrun r x Hr Hx; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_rows_marked p initial).
    { unfold initial, discovery_rows_marked.
      assert (Hseed : forall xs acc, discovery_rows acc = [] ->
        discovery_rows (fold_left (discovery_seed_one st) xs acc) = []).
      { intros xs; induction xs as [|y ys IH]; intros acc Hrows;
          [exact Hrows|].
        cbn [fold_left]; apply IH; unfold discovery_seed_one.
        destruct (missing st y); [|exact Hrows].
        unfold discovery_visit.
        destruct (PTrieCode.get (S.key_code y) (discovery_seen acc));
          [exact Hrows|].
        destruct (value st y); cbn [discovery_rows]; exact Hrows. }
      intros q y Hq; rewrite (Hseed roots empty_discovery eq_refl) in Hq;
        contradiction. }
    assert (Hstep : forall acc, discovery_rows_marked p acc ->
      match discovery_step p st acc with
      | inl next => discovery_rows_marked p next
      | inr finished => discovery_rows_marked p finished
      end).
    { intros acc Hvalid; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_marked; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hvalid|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_rows_marked p) (discovery_rows_marked p)
      Hstep fuel initial Hinitial) as Hvalid.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as _ <- _.
    exists finished; split; [reflexivity|].
    apply in_rev in Hr; exact (Hvalid r x Hr Hx).
  Qed.

  Lemma discovery_result_frozen_complete : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    forall r x v, In r rs -> In x (row_keys p r) -> value st x = Some v ->
      In (x, v) fz.
  Proof.
    intros p roots fuel st ks rs fz Hrun.
    pose proof Hrun as Hdiscovery; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_seen_frozen st initial).
    { unfold initial; apply discovery_seed_seen_frozen.
      unfold discovery_seen_frozen, empty_discovery;
        cbn [discovery_seen discovery_frozen].
      intros x v Hvalue Hseen; rewrite PTrie.get_empty in Hseen; discriminate Hseen. }
    assert (Hstep : forall acc, discovery_seen_frozen st acc ->
      match discovery_step p st acc with
      | inl next => discovery_seen_frozen st next
      | inr finished => discovery_seen_frozen st finished
      end).
    { intros acc Hvalid; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_seen_frozen; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [inversion Hnext; subst; exact Hvalid|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_seen_frozen st) (discovery_seen_frozen st)
      Hstep fuel initial Hinitial) as Hvalid.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as _ Hrs Hfz.
    intros r x v Hr Hx Hvalue.
    assert (Hmarked : PTrieCode.get (S.key_code x) (discovery_seen finished) = Some tt).
    { destruct (discovery_result_marked p roots fuel st ks rs fz Hdiscovery r x)
        as [result [Hresult Hmarked]]; [exact Hr|exact Hx|].
      change (loopN (discovery_step p st) fuel initial = inr result) in Hresult.
      rewrite Hloop in Hresult; injection Hresult as <-; exact Hmarked. }
    rewrite <- Hfz.
    apply (proj1 (in_rev (discovery_frozen finished) (x, v))).
    exact (Hvalid x v Hvalue Hmarked).
  Qed.

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

  Lemma region_rows : forall p roots st r, S.wf p ->
    In r (region p roots st) -> In r (S.rows p).
  Proof.
    intros p roots st r Hwf Hr; unfold region, discovery_view in Hr.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; cbn in Hr; [|contradiction].
    eapply discovery_result_rows; eauto.
  Qed.

  Definition discovery_region_rows := region_rows.

  Lemma region_new : forall p roots st r, S.wf p ->
    In r (region p roots st) -> exists y, In y (S.writes p r) /\ ~ dom st y.
  Proof.
    intros p roots st r Hwf Hr; unfold region, discovery_view in Hr.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; cbn in Hr; [|contradiction].
    destruct (discovery_result_rows_new p roots (view_fuel p roots)
      st ks rs fz Hwf Hrun r Hr) as [y [Hy Hnone]].
    exists y; split; [exact Hy|].
    intros [v Hv]; rewrite Hnone in Hv; discriminate Hv.
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

  Lemma discover_closed : forall p roots st, S.wf p -> inv p st ->
    closed p (fun x => dom st x \/ In x (discover p roots st)).
  Proof.
    intros p roots st Hwf [Hclosed Hpost] r y x Hr Hy [Hold|Hnew] Hx.
    - left; eapply Hclosed; eauto.
    - unfold discover, discovery_view in Hnew |- *.
      destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
        eqn:Hrun; cbn in Hnew |- *; [|contradiction].
      apply (discovery_result_support p roots (view_fuel p roots) st ks rs fz Hrun
        r x).
      + eapply discovery_result_done_rows; [exact Hrun|exact Hnew|].
        apply (proj2 (S.rows_of_spec p y r Hwf)); split; assumption.
      + exact Hx.
  Qed.

  Definition discovery_closed := discover_closed.

  Lemma legacy_discovery_closed : forall p roots st, S.wf p -> inv p st ->
    closed p (fun x => dom st x \/ In x (discovery_keys p roots st)).
  Proof.
    intros p roots st Hwf [Hclosed Hpost] r y x Hr Hy [Hold|Hnew] Hx.
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
    unfold value, merge_discovered; cbn [inc_values].
    rewrite fill_local_eq_fill, fill_lookup.
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
    rewrite fill_local_eq_fill.
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
    rewrite fill_local_eq_fill.
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
    reflexivity.
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
      eapply (legacy_discovery_closed p roots st Hwf (conj Hclosed Hpost));
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

  Lemma discovery_result_closed : forall p roots fuel st ks rs fz,
    S.wf p -> inv p st -> discovery p roots fuel st = Some (ks, rs, fz) ->
    closed p (fun x => dom st x \/ In x ks).
  Proof.
    intros p roots fuel st ks rs fz Hwf [Hclosed Hpost] Hrun r y x Hr Hy Hdy Hx.
    destruct Hdy as [Hold|Hnew].
    - left; eapply Hclosed; eauto.
    - eapply discovery_result_support; [exact Hrun| |exact Hx].
      eapply discovery_result_done_rows; [exact Hrun|exact Hnew|].
      apply (proj2 (S.rows_of_spec p y r Hwf)); split; assumption.
  Qed.

  Lemma restored_result_old_support : forall p roots fuel st ks rs fz m r x v,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    In r rs -> In x (row_keys p r) -> value st x = Some v ->
    Checker.look (restore fz m) x = v.
  Proof.
    intros p roots fuel st ks rs fz m r x v Hrun Hr Hx Hvalue.
    rewrite Checker.look_spec; apply restore_hit.
    - intros w Hw; apply (discovery_result_frozen p roots fuel st ks rs fz Hrun) in Hw.
      rewrite Hvalue in Hw; injection Hw as Heq; symmetry; exact Heq.
    - eapply discovery_result_frozen_complete; eauto.
  Qed.

  Lemma merge_checked_inv_result : forall p roots fuel st ks rs fz m,
    S.wf p -> inv p st -> discovery p roots fuel st = Some (ks, rs, fz) ->
    Checker.check_rows p rs (restore fz m) = true ->
    inv p (merge_discovered st ks (restore fz m)).
  Proof.
    intros p roots fuel st ks rs fz m Hwf Hinv Hrun Hcheck.
    destruct Hinv as [Hclosed Hpost].
    pose proof (proj2 (discovery_result_missing p roots fuel st ks rs fz Hrun)) as Hmissing.
    split.
    - intros r y x Hr Hy Hdom Hx.
      apply (proj2 (merge_dom st ks (restore fz m) x)).
      eapply (discovery_result_closed p roots fuel st ks rs fz Hwf
        (conj Hclosed Hpost) Hrun); [exact Hr|exact Hy| |exact Hx].
      apply (proj1 (merge_dom st ks (restore fz m) y)); exact Hdom.
    - intros r y Hr Hy Hdom.
      destruct (value st y) as [v|] eqn:Hvalue.
      + assert (Hold : dom st y) by (exists v; exact Hvalue).
        assert (Hrow :
          row_ok L.leb (look (merge_discovered st ks (restore fz m)))
            (S.target p r) (S.eval p r (look (merge_discovered st ks (restore fz m)))) =
          row_ok L.leb (look st) (S.target p r) (S.eval p r (look st))).
        { apply row_look_transport; [exact Hwf|exact Hr|].
          intros x Hx; apply merge_old_look; [exact Hmissing|].
          eapply Hclosed; eauto. }
        rewrite Hrow; eapply Hpost; eauto.
      + assert (Hnew : In y ks).
        { apply (proj1 (merge_dom st ks (restore fz m) y)) in Hdom.
          destruct Hdom as [[w Hw]|Hin]; [rewrite Hvalue in Hw; discriminate Hw|exact Hin]. }
        assert (Hregion : In r rs).
        { eapply discovery_result_done_rows; [exact Hrun|exact Hnew|].
          apply (proj2 (S.rows_of_spec p y r Hwf)); split; assumption. }
        assert (Hrow :
          row_ok L.leb (look (merge_discovered st ks (restore fz m)))
            (S.target p r) (S.eval p r (look (merge_discovered st ks (restore fz m)))) =
          row_ok L.leb (Checker.look (restore fz m))
            (S.target p r) (S.eval p r (Checker.look (restore fz m)))).
        { apply row_look_transport; [exact Hwf|exact Hr|].
          intros x Hx; destruct (discovery_result_support p roots fuel st ks rs fz
            Hrun r x Hregion Hx) as [Hold|Hin].
          - rewrite (merge_old_look st ks (restore fz m) x Hmissing Hold).
            destruct Hold as [w Hw]; unfold look; rewrite Hw.
            symmetry; eapply restored_result_old_support; eauto.
          - apply merge_new_look; exact Hin. }
        rewrite Hrow; apply (proj1 (Checker.check_rows_iff p _ _)
          Hcheck r Hregion).
  Qed.

  Lemma finish_checked_inv_result : forall p roots fuel st ks rs fz m,
    S.wf p -> inv p st -> discovery p roots fuel st = Some (ks, rs, fz) ->
    Checker.check_rows p rs (restore fz m) = true ->
    inv p (finish_demand p st ks rs (restore fz m)).
  Proof.
    intros p roots fuel st ks rs fz m Hwf Hinv Hrun Hcheck.
    eapply inv_same_values with (left := merge_discovered st ks (restore fz m)).
    - exact Hwf.
    - intro x; symmetry; apply finish_demand_value.
    - eapply merge_checked_inv_result; eauto.
  Qed.

  Lemma demand_inv : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') -> inv p st'.
  Proof.
    intros p pol roots fuel st o st' Hwf Hinv Hrun; unfold demand in Hrun.
    destruct (forallb (present st) roots); [inversion Hrun; subst; exact Hinv|].
    destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
      [|inversion Hrun; subst; exact Hinv].
    destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why] eqn:Hsolver.
    - destruct (Checker.check_rows p rs (restore fz m)) eqn:Hcheck.
      + inversion Hrun; subst; eapply finish_checked_inv_result; eauto.
      + inversion Hrun; subst; exact Hinv.
    - inversion Hrun; subst; exact Hinv.
    - inversion Hrun; subst; exact Hinv.
  Qed.

  Lemma discovery_seed_one_keeps_missing : forall st acc x y,
    In y (discovery_missing acc) ->
    In y (discovery_missing (discovery_seed_one st acc x)).
  Proof.
    intros st acc x y Hy; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_missing_keeps|exact Hy].
  Qed.

  Lemma discovery_seed_keeps_missing : forall st roots acc y,
    In y (discovery_missing acc) ->
    In y (discovery_missing (fold_left (discovery_seed_one st) roots acc)).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc y Hy;
      [exact Hy|].
    cbn [fold_left]; apply IH; now apply discovery_seed_one_keeps_missing.
  Qed.

  Lemma discovery_seed_roots : forall st roots x,
    In x roots -> value st x = None ->
    In x (discovery_missing (fold_left (discovery_seed_one st) roots empty_discovery)).
  Proof.
    assert (Hseed : forall st roots acc x,
      discovery_seen_missing st acc -> In x roots -> value st x = None ->
      In x (discovery_missing (fold_left (discovery_seed_one st) roots acc))).
    { intros st roots; induction roots as [|y rest IH]; intros acc x Hseen Hin Hnone;
        [contradiction|].
      cbn [fold_left]; destruct Hin as [<-|Hin].
      - apply discovery_seed_keeps_missing.
        unfold discovery_seed_one; rewrite (proj2 (missing_spec st y) Hnone).
        unfold discovery_visit.
        destruct (PTrieCode.get (S.key_code y) (discovery_seen acc)) as [[]|]
          eqn:Hget; [now apply Hseen|].
        rewrite Hnone; cbn [discovery_missing]; now left.
      - apply IH; [|exact Hin|exact Hnone].
        unfold discovery_seed_one; destruct (missing st y);
          [now apply discovery_visit_seen_missing|exact Hseen]. }
    intros st roots x Hin Hnone; apply Hseed; [|exact Hin|exact Hnone].
    unfold discovery_seen_missing, empty_discovery; cbn [discovery_seen].
    intros y Hvalue Hget; rewrite PTrie.get_empty in Hget; discriminate Hget.
  Qed.

  Lemma discovery_row_keeps_missing : forall p st acc r x,
    In x (discovery_missing acc) ->
    In x (discovery_missing (discovery_row p st acc r)).
  Proof.
    intros p st acc r x Hx; unfold discovery_row; cbn [discovery_missing].
    now apply discovery_fold_visit_missing_keeps.
  Qed.

  Lemma discovery_step_keeps_missing : forall p st acc x,
    In x (discovery_missing acc) ->
    match discovery_step p st acc with
    | inl next => In x (discovery_missing next)
    | inr result => In x (discovery_missing result)
    end.
  Proof.
    intros p st acc x Hx; unfold discovery_step.
    destruct (discovery_pending acc) as [|y pending]; [exact Hx|].
    assert (Hfold : forall rs current,
      In x (discovery_missing current) ->
      In x (discovery_missing (fold_left (discovery_row p st) rs current))).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_keeps_missing. }
    apply Hfold; cbn [discovery_missing]; exact Hx.
  Qed.

  Lemma discovery_result_roots : forall p roots fuel st ks rs fz x,
    discovery p roots fuel st = Some (ks, rs, fz) -> In x roots ->
    dom st x \/ In x ks.
  Proof.
    intros p roots fuel st ks rs fz x Hrun Hin.
    destruct (value st x) as [v|] eqn:Hvalue;
      [left; exists v; exact Hvalue|right].
    rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : In x (discovery_missing initial)).
    { unfold initial; now apply discovery_seed_roots. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (fun acc => In x (discovery_missing acc))
      (fun acc => In x (discovery_missing acc))
      (fun acc => discovery_step_keeps_missing p st acc x)
      fuel initial Hinitial) as Hresult.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as Hks _ _; subst ks.
    apply (proj1 (in_rev (discovery_missing finished) x)); exact Hresult.
  Qed.

  Definition discovery_source_state (p : S.prog) (roots : list S.key)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x, In x (discovery_missing acc) -> In x roots \/
      exists r, In r (discovery_rows acc) /\ In x (row_keys p r).

  Lemma discovery_visit_missing_origin : forall st acc x y,
    In y (discovery_missing (discovery_visit st x acc)) ->
    y = x \/ In y (discovery_missing acc).
  Proof.
    intros st acc x y Hin; unfold discovery_visit in Hin.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)); [now right|].
    destruct (value st x); cbn [discovery_missing] in Hin;
      [now right|].
    destruct Hin as [<-|Hin]; [now left|now right].
  Qed.

  Lemma discovery_visit_rows_eq : forall st acc x,
    discovery_rows (discovery_visit st x acc) = discovery_rows acc.
  Proof.
    intros st acc x; unfold discovery_visit.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc));
      [reflexivity|].
    destruct (value st x); reflexivity.
  Qed.

  Lemma discovery_seed_source : forall p roots st,
    discovery_source_state p roots
      (fold_left (discovery_seed_one st) roots empty_discovery).
  Proof.
    intros p roots st.
    assert (Hfold : forall xs acc,
      discovery_source_state p roots acc ->
      (forall x, In x xs -> In x roots) ->
      discovery_source_state p roots (fold_left (discovery_seed_one st) xs acc)).
    { intros xs; induction xs as [|y rest IH]; intros acc Hsource Hsubset;
        [exact Hsource|].
      cbn [fold_left]; apply IH.
      - unfold discovery_seed_one; destruct (missing st y); [|exact Hsource].
        intros x Hx; apply discovery_visit_missing_origin in Hx as [->|Hold].
        + left; apply Hsubset; now left.
        + destruct (Hsource x Hold) as [Hroot|[r [Hr Hkey]]]; [now left|].
          right; exists r; split; [rewrite discovery_visit_rows_eq; exact Hr|exact Hkey].
      - intros x Hx; apply Hsubset; now right. }
    apply Hfold.
    - intros x Hx; unfold empty_discovery in Hx; cbn [discovery_missing] in Hx;
        contradiction.
    - intros x Hx; exact Hx.
  Qed.

  Lemma discovery_row_source : forall p roots st acc r,
    discovery_source_state p roots acc ->
    discovery_source_state p roots (discovery_row p st acc r).
  Proof.
    intros p roots st acc r Hsource.
    assert (Hfold : forall xs current,
      (forall y, In y xs -> In y (row_keys p r)) ->
      discovery_rows current = discovery_rows acc ->
      (forall x, In x (discovery_missing current) ->
        In x roots \/ (exists q, In q (discovery_rows acc) /\ In x (row_keys p q)) \/
        In x (row_keys p r)) ->
      (forall x, In x (discovery_missing
        (fold_left (fun current y => discovery_visit st y current) xs current)) ->
        In x roots \/ (exists q, In q (discovery_rows acc) /\ In x (row_keys p q)) \/
        In x (row_keys p r))).
    { intros xs; induction xs as [|y rest IH];
        intros current Hsubset Hrows Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH.
      - intros z Hz; apply Hsubset; now right.
      - rewrite discovery_visit_rows_eq; exact Hrows.
      - intros x Hx; apply discovery_visit_missing_origin in Hx as [->|Hold].
        + right; right; apply Hsubset; now left.
        + exact (Hcurrent x Hold). }
    intros x Hx; unfold discovery_row in Hx; cbn [discovery_missing] in Hx.
    pose proof (Hfold (row_keys p r) acc (fun y Hy => Hy) eq_refl) as Hresult.
    specialize (Hresult (fun y Hy =>
      match Hsource y Hy with
      | or_introl Hroot => or_introl Hroot
      | or_intror Hrow => or_intror (or_introl Hrow)
      end) x Hx).
    destruct Hresult as [Hroot|[[q [Hq Hkey]]|Hkey]]; [now left| |].
    - right; exists q; split; [rewrite discovery_row_rows; now right|exact Hkey].
    - right; exists r; split; [rewrite discovery_row_rows; now left|exact Hkey].
  Qed.

  Lemma discovery_step_source : forall p roots st acc next,
    discovery_source_state p roots acc -> discovery_step p st acc = inl next ->
    discovery_source_state p roots next.
  Proof.
    intros p roots st acc next Hsource Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current,
      discovery_source_state p roots current ->
      discovery_source_state p roots (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_source. }
    apply Hfold; unfold discovery_source_state in *;
      cbn [discovery_missing discovery_rows]; exact Hsource.
  Qed.

  Lemma discovery_result_source : forall p roots fuel st ks rs fz x,
    discovery p roots fuel st = Some (ks, rs, fz) -> In x ks ->
    In x roots \/ exists r, In r rs /\ In x (row_keys p r).
  Proof.
    intros p roots fuel st ks rs fz x Hrun Hx; rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : discovery_source_state p roots initial).
    { unfold initial; apply discovery_seed_source. }
    assert (Hstep : forall acc, discovery_source_state p roots acc ->
      match discovery_step p st acc with
      | inl next => discovery_source_state p roots next
      | inr result => discovery_source_state p roots result
      end).
    { intros acc Hsource; destruct (discovery_step p st acc) as [next|result]
        eqn:Hnext; [eapply discovery_step_source; eauto|].
      unfold discovery_step in Hnext; destruct (discovery_pending acc);
        [inversion Hnext; subst; exact Hsource|discriminate Hnext]. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (discovery_source_state p roots) (discovery_source_state p roots)
      Hstep fuel initial Hinitial) as Hsource.
    destruct (loopN (discovery_step p st) fuel initial) as [remaining|finished]
      eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as Hks Hrs _.
    rewrite <- Hks in Hx.
    apply (proj2 (in_rev (discovery_missing finished) x)) in Hx.
    destruct (Hsource x Hx) as [Hroot|[r [Hr Hkey]]]; [now left|].
    right; exists r; split; [|exact Hkey].
    rewrite <- Hrs; apply (proj1 (in_rev (discovery_rows finished) r)); exact Hr.
  Qed.

  Lemma discovery_result_length : forall p roots fuel st ks rs fz,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    length ks <= length roots +
      fold_right Nat.add 0 (map (fun r => length (row_keys p r)) (S.rows p)).
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun.
    assert (Hincl : incl ks (roots ++ flat_map (row_keys p) (S.rows p))).
    { intros x Hx; apply in_app_iff.
      destruct (discovery_result_source p roots fuel st ks rs fz x Hrun Hx)
        as [Hroot|[r [Hr Hkey]]]; [now left|right].
      apply in_flat_map; exists r; split; [|exact Hkey].
      eapply discovery_result_rows; eauto. }
    pose proof (NoDup_incl_length
      (proj1 (discovery_result_missing p roots fuel st ks rs fz Hrun)) Hincl)
      as Hlength.
    rewrite length_app, finite_flat_map_length in Hlength.
    exact Hlength.
  Qed.

  Lemma discovery_result_keys_length : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    length ks <= length roots +
      fold_right Nat.add 0 (map (fun r => length (S.deps p r)) rs) +
      fold_right Nat.add 0 (map (fun r => length (S.writes p r)) rs).
  Proof.
    intros p roots fuel st ks rs fz Hrun.
    assert (Hincl : incl ks (roots ++ flat_map (row_keys p) rs)).
    { intros x Hx; apply in_app_iff.
      destruct (discovery_result_source p roots fuel st ks rs fz x Hrun Hx)
        as [Hroot|[r [Hr Hkey]]]; [now left|right].
      apply in_flat_map; exists r; auto. }
    pose proof (NoDup_incl_length
      (proj1 (discovery_result_missing p roots fuel st ks rs fz Hrun)) Hincl)
      as Hlength.
    rewrite length_app, finite_flat_map_length in Hlength.
    assert (Hrows : finite_sum (fun r => length (row_keys p r)) rs =
      finite_sum (fun r => length (S.deps p r)) rs +
      finite_sum (fun r => length (S.writes p r)) rs).
    { rewrite <- finite_sum_plus; apply finite_sum_ext; intros r Hr.
      change (length (S.writes p r ++ S.deps p r) =
        length (S.deps p r) + length (S.writes p r)).
      rewrite length_app; lia. }
    rewrite Hrows in Hlength.
    change (length ks <= length roots +
      finite_sum (fun r => length (S.deps p r)) rs +
      finite_sum (fun r => length (S.writes p r)) rs).
    rewrite <- Nat.add_assoc; exact Hlength.
  Qed.

  Lemma discovery_result_view : forall p roots fuel st ks rs fz,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    discovery p roots (view_fuel p roots) st = Some (ks, rs, fz).
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun.
    apply discovery_finished_replay with (fuel := fuel); [exact Hrun|].
    pose proof (discovery_result_length p roots fuel st ks rs fz Hwf Hrun) as Hlength.
    unfold view_fuel, N.lt.
    rewrite <- Nat2N.inj_compare.
    apply Nat.compare_lt_iff.
    apply Nat.lt_succ_r; exact Hlength.
  Qed.

  Lemma discovery_result_view_keys : forall p roots fuel st ks rs fz,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    ks = discover p roots st.
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun.
    pose proof (discovery_result_view p roots fuel st ks rs fz Hwf Hrun) as Hview.
    unfold discover, discovery_view; now rewrite Hview.
  Qed.

  Lemma discovery_result_view_rows : forall p roots fuel st ks rs fz,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    rs = region p roots st.
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun.
    pose proof (discovery_result_view p roots fuel st ks rs fz Hwf Hrun) as Hview.
    unfold region, discovery_view; now rewrite Hview.
  Qed.

  Lemma discovery_result_view_frozen : forall p roots fuel st ks rs fz,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    fz = frozen p roots st.
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun.
    pose proof (discovery_result_view p roots fuel st ks rs fz Hwf Hrun) as Hview.
    unfold frozen, discovery_view; now rewrite Hview.
  Qed.

  Lemma discovery_result_view_projection : forall p roots fuel st ks rs fz,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    ks = discover p roots st /\ rs = region p roots st /\ fz = frozen p roots st.
  Proof.
    intros p roots fuel st ks rs fz Hwf Hrun; repeat split.
    - eapply discovery_result_view_keys; eauto.
    - eapply discovery_result_view_rows; eauto.
    - eapply discovery_result_view_frozen; eauto.
  Qed.

  Lemma demand_covers : forall p pol roots fuel st st', inv p st ->
    demand p pol roots fuel st = (Done, st') -> forall x, In x roots -> dom st' x.
  Proof.
    intros p pol roots fuel st st' Hinv Hrun x Hx; unfold demand in Hrun.
    destruct (forallb (present st) roots) eqn:Hready.
    - inversion Hrun; subst; apply present_spec.
      exact ((proj1 (@forallb_forall _ _ _) Hready) x Hx).
    - destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
        [|discriminate Hrun].
      destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why] eqn:Hsolver;
        [|discriminate Hrun|discriminate Hrun].
      destruct (Checker.check_rows p rs (restore fz m)) eqn:Hcheck;
        [|discriminate Hrun].
      inversion Hrun; subst; apply (proj2 (finish_demand_dom p st _ _ _ x)).
      eapply discovery_result_roots; eauto.
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
    destruct (discovery p roots fuel st) as [[[xs rs] fz]|]; [|discriminate].
    destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|reason].
    - destruct (Checker.check_rows p rs (restore fz m));
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

  Definition invalid_seen_bad (acc : incremental_invalidation S.key) : Prop :=
    forall x, PTrieCode.get (S.key_code x) (invalid_seen acc) = Some tt ->
      In x (invalid_bad acc).

  Lemma invalid_seed_seen_bad : forall st acc x,
    invalid_seen_bad acc -> invalid_seen_bad (invalid_seed_one st acc x).
  Proof.
    intros st acc x Hvalid y Hseen; unfold invalid_seed_one in Hseen |- *.
    destruct (present st x); [|now apply Hvalid].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)) as [[]|]
      eqn:Hx; [now apply Hvalid|].
    cbn [invalid_seen invalid_bad] in Hseen |- *.
    destruct (Pos.eq_dec (S.key_code y) (S.key_code x)) as [Heq|Hneq].
    - pose proof (S.key_code_inj y x Heq) as ->; now left.
    - rewrite PTrie.get_set_other in Hseen by exact Hneq.
      right; now apply Hvalid.
  Qed.

  Lemma invalid_seed_bad_keeps : forall st acc x y,
    In y (invalid_bad acc) -> In y (invalid_bad (invalid_seed_one st acc x)).
  Proof.
    intros st acc x y Hy; unfold invalid_seed_one.
    destruct (present st x); [|exact Hy].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      [exact Hy|now right].
  Qed.

  Lemma invalid_seed_fold_seen_bad : forall st xs acc,
    invalid_seen_bad acc ->
    invalid_seen_bad (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply invalid_seed_seen_bad.
  Qed.

  Lemma invalid_seed_fold_bad_keeps : forall st xs acc y,
    In y (invalid_bad acc) ->
    In y (invalid_bad (fold_left (invalid_seed_one st) xs acc)).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc y Hy;
      [exact Hy|].
    cbn [fold_left]; apply IH; now apply invalid_seed_bad_keeps.
  Qed.

  Lemma invalid_seed_fold_contains : forall st xs acc x,
    invalid_seen_bad acc -> In x xs -> present st x = true ->
    In x (invalid_bad (fold_left (invalid_seed_one st) xs acc)).
  Proof.
    intros st xs; induction xs as [|y rest IH]; intros acc x Hvalid Hin Hpresent;
      [contradiction|].
    cbn [fold_left]; destruct Hin as [Heq|Hin]; [subst y|].
    - apply invalid_seed_fold_bad_keeps.
      unfold invalid_seed_one; rewrite Hpresent.
      destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)) as [[]|]
        eqn:Hseen; [now apply Hvalid|now left].
    - apply IH; [now apply invalid_seed_seen_bad|exact Hin|exact Hpresent].
  Qed.

  Lemma invalid_snapshot_bad_keeps : forall st acc id y,
    In y (invalid_bad acc) -> In y (invalid_bad (invalid_visit_snapshot st acc id)).
  Proof.
    intros st acc id y Hy; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|exact Hy].
    destruct (snapshot_live ss); [|exact Hy].
    cbn [invalid_bad]; now apply invalid_seed_fold_bad_keeps.
  Qed.

  Lemma invalid_snapshot_seen_bad : forall st acc id,
    invalid_seen_bad acc -> invalid_seen_bad (invalid_visit_snapshot st acc id).
  Proof.
    intros st acc id Hvalid; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|exact Hvalid].
    destruct (snapshot_live ss); [|exact Hvalid].
    cbn [invalid_seen invalid_bad]; now apply invalid_seed_fold_seen_bad.
  Qed.

  Lemma invalid_snapshot_contains : forall st acc id ss y,
    invalid_seen_bad acc ->
    PTrieCode.get id (invalid_snapshots acc) = Some ss ->
    snapshot_live ss = true -> In y (snapshot_writes ss) -> present st y = true ->
    In y (invalid_bad (invalid_visit_snapshot st acc id)).
  Proof.
    intros st acc id ss y Hvalid Hget Hlive Hy Hpresent.
    unfold invalid_visit_snapshot; rewrite Hget, Hlive.
    cbn [invalid_bad]; now apply invalid_seed_fold_contains.
  Qed.

  Lemma invalid_snapshot_fold_seen_bad : forall st ids acc,
    invalid_seen_bad acc ->
    invalid_seen_bad (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply invalid_snapshot_seen_bad.
  Qed.

  Lemma invalid_snapshot_fold_bad_keeps : forall st ids acc y,
    In y (invalid_bad acc) ->
    In y (invalid_bad (fold_left (invalid_visit_snapshot st) ids acc)).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc y Hy;
      [exact Hy|].
    cbn [fold_left]; apply IH; now apply invalid_snapshot_bad_keeps.
  Qed.

  Lemma invalid_step_bad_keeps : forall st acc next y,
    invalid_step st acc = inl next -> In y (invalid_bad acc) -> In y (invalid_bad next).
  Proof.
    intros st [pending0 seen bad done snapshots] next y Hstep Hy.
    destruct pending0 as [|x pending]; cbn [invalid_step] in Hstep;
      [discriminate Hstep|].
    inversion Hstep; subst next; clear Hstep.
    unfold invalid_next.
    apply invalid_snapshot_fold_bad_keeps; exact Hy.
  Qed.

  Lemma invalid_walk_seen_bad : forall p p' ch st,
    invalid_seen_bad (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_seen_bad) (Post := invalid_seen_bad).
    - intros [pending0 seen bad done snapshots] Hvalid.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hvalid|].
      unfold invalid_next; apply invalid_snapshot_fold_seen_bad; exact Hvalid.
    - unfold invalid_initial; apply invalid_seed_fold_seen_bad.
      intros x Hseen; cbn [invalid_seen] in Hseen.
      rewrite PTrie.get_empty in Hseen; discriminate.
  Qed.

  Lemma invalid_walk_bad_keeps : forall p p' ch st x,
    In x (invalid_bad (invalid_initial p p' ch st)) ->
    In x (invalid_bad (invalid_walk p p' ch st)).
  Proof.
    intros p p' ch st x Hbad; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := fun acc => In x (invalid_bad acc))
      (Post := fun result => In x (invalid_bad result)); [|exact Hbad].
    intros [pending0 seen bad done snapshots] Hacc.
    destruct pending0 as [|y pending]; cbn [invalid_checked_step].
    - exact Hacc.
    - unfold invalid_next; apply invalid_snapshot_fold_bad_keeps; exact Hacc.
  Qed.

  Lemma invalid_initial_seed : forall p p' ch st x,
    In x (changed_keys p p' ch) -> present st x = true ->
    In x (invalid_bad (invalid_initial p p' ch st)).
  Proof.
    intros p p' ch st x Hx Hpresent; unfold invalid_initial.
    eapply invalid_seed_fold_contains; [|exact Hx|exact Hpresent].
    unfold invalid_seen_bad; cbn [invalid_seen invalid_bad].
    intros y Hseen; rewrite PTrie.get_empty in Hseen; discriminate.
  Qed.

  (** Every seed remains in the saturated invalidation list. *)
  Lemma invalidate_keys_seed : forall p p' ch st,
    incl (changed_seeds p p' ch st) (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st x Hseed; unfold invalidate_keys.
    apply invalid_walk_bad_keeps, invalid_initial_seed.
    - apply (proj1 (changed_seeds_spec p p' ch st x)) in Hseed.
      destruct Hseed as [_ [r [Hr Hx]]].
      unfold changed_keys; apply in_flat_map; exists r; split; assumption.
    - apply (proj1 (changed_seeds_spec p p' ch st x)) in Hseed.
      destruct Hseed as [Hdom _]; now apply (proj2 (present_spec st x)).
  Qed.

  Definition invalid_bad_present (st : state) (acc : incremental_invalidation S.key) : Prop :=
    forall x, In x (invalid_bad acc) -> present st x = true.

  Lemma invalid_seed_bad_present : forall st acc x,
    invalid_bad_present st acc -> invalid_bad_present st (invalid_seed_one st acc x).
  Proof.
    intros st acc x Hvalid y Hy; unfold invalid_seed_one in Hy.
    destruct (present st x) eqn:Hpresent; [|now apply Hvalid].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      [now apply Hvalid|].
    cbn [invalid_bad] in Hy; destruct Hy as [<-|Hy];
      [exact Hpresent|now apply Hvalid].
  Qed.

  Lemma invalid_seed_fold_bad_present : forall st xs acc,
    invalid_bad_present st acc ->
    invalid_bad_present st (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply invalid_seed_bad_present.
  Qed.

  Lemma invalid_snapshot_bad_present : forall st acc id,
    invalid_bad_present st acc -> invalid_bad_present st (invalid_visit_snapshot st acc id).
  Proof.
    intros st acc id Hvalid; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|exact Hvalid].
    destruct (snapshot_live ss); [|exact Hvalid].
    unfold invalid_bad_present in *; cbn [invalid_bad].
    now apply invalid_seed_fold_bad_present.
  Qed.

  Lemma invalid_snapshot_fold_bad_present : forall st ids acc,
    invalid_bad_present st acc ->
    invalid_bad_present st (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply invalid_snapshot_bad_present.
  Qed.

  Lemma invalid_walk_bad_present : forall p p' ch st,
    invalid_bad_present st (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_bad_present st) (Post := invalid_bad_present st).
    - intros [pending0 seen bad done snapshots] Hvalid.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hvalid|].
      unfold invalid_next; apply invalid_snapshot_fold_bad_present; exact Hvalid.
    - unfold invalid_initial; apply invalid_seed_fold_bad_present.
      unfold invalid_bad_present; cbn [invalid_bad]; intros x Hx; contradiction.
  Qed.

  (** Invalidation can only remove keys that were actually present. *)
  Lemma invalidate_dom : forall p p' ch st x,
    In x (invalidate p p' ch st) -> dom st x.
  Proof.
    unfold invalidate, invalidate_keys.
    intros p p' ch st x Hin; apply (proj1 (present_spec st x)).
    exact (invalid_walk_bad_present p p' ch st x Hin).
  Qed.

  Definition invalidate_keys_dom := invalidate_dom.

  Definition invalid_bad_unique (acc : incremental_invalidation S.key) : Prop :=
    NoDup (invalid_bad acc) /\
    forall x, In x (invalid_bad acc) ->
      PTrieCode.get (S.key_code x) (invalid_seen acc) = Some tt.

  Lemma invalid_seed_bad_unique : forall st acc x,
    invalid_bad_unique acc -> invalid_bad_unique (invalid_seed_one st acc x).
  Proof.
    intros st acc x [Hnodup Hmarked]; unfold invalid_seed_one.
    destruct (present st x); [|now split].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)) as [[]|]
      eqn:Hseen; [now split|].
    cbn [invalid_bad invalid_seen]; split.
    - constructor; [|exact Hnodup].
      intro Hin; rewrite (Hmarked x Hin) in Hseen; discriminate.
    - intros y [<-|Hy]; [apply PTrie.get_set_same|].
      assert (Hneq : S.key_code y <> S.key_code x).
      { intro Heq; pose proof (Hmarked y Hy) as Hget.
        rewrite Heq in Hget; congruence. }
      cbn [invalid_seen]; rewrite PTrie.get_set_other by exact Hneq.
      now apply Hmarked.
  Qed.

  Lemma invalid_seed_fold_bad_unique : forall st xs acc,
    invalid_bad_unique acc -> invalid_bad_unique (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply invalid_seed_bad_unique.
  Qed.

  Lemma invalid_snapshot_bad_unique : forall st acc id,
    invalid_bad_unique acc -> invalid_bad_unique (invalid_visit_snapshot st acc id).
  Proof.
    intros st acc id Hvalid; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|exact Hvalid].
    destruct (snapshot_live ss); [|exact Hvalid].
    cbn [invalid_bad invalid_seen]; now apply invalid_seed_fold_bad_unique.
  Qed.

  Lemma invalid_snapshot_fold_bad_unique : forall st ids acc,
    invalid_bad_unique acc ->
    invalid_bad_unique (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hvalid;
      [exact Hvalid|].
    cbn [fold_left]; apply IH; now apply invalid_snapshot_bad_unique.
  Qed.

  Lemma invalid_walk_bad_unique : forall p p' ch st,
    invalid_bad_unique (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_bad_unique) (Post := invalid_bad_unique).
    - intros [pending0 seen bad done snapshots] Hvalid.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hvalid|].
      unfold invalid_next; apply invalid_snapshot_fold_bad_unique; exact Hvalid.
    - unfold invalid_initial; apply invalid_seed_fold_bad_unique.
      unfold invalid_bad_unique; cbn [invalid_bad invalid_seen].
      split; [constructor|intros x Hx; contradiction].
  Qed.

  (** Invalidation lists each removed key once. *)
  Lemma invalidate_nodup : forall p p' ch st, NoDup (invalidate p p' ch st).
  Proof.
    intros p p' ch st; unfold invalidate, invalidate_keys.
    exact (proj1 (invalid_walk_bad_unique p p' ch st)).
  Qed.

  Definition invalidate_keys_nodup := invalidate_nodup.

  Definition invalid_queued (acc : incremental_invalidation S.key) : Prop :=
    forall x, In x (invalid_bad acc) ->
      In x (invalid_pending acc) \/ In x (invalid_done acc).

  Lemma invalid_seed_queued : forall st acc x,
    invalid_queued acc -> invalid_queued (invalid_seed_one st acc x).
  Proof.
    intros st acc x Hqueued; unfold invalid_seed_one.
    destruct (present st x); [|exact Hqueued].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      [exact Hqueued|].
    intros y [<-|Hy]; [now left; left|].
    destruct (Hqueued y Hy) as [Hpending|Hdone];
      [left; now right|now right].
  Qed.

  Lemma invalid_seed_fold_queued : forall st xs acc,
    invalid_queued acc -> invalid_queued (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hqueued;
      [exact Hqueued|].
    cbn [fold_left]; apply IH; now apply invalid_seed_queued.
  Qed.

  Lemma invalid_snapshot_queued : forall st acc id,
    invalid_queued acc -> invalid_queued (invalid_visit_snapshot st acc id).
  Proof.
    intros st acc id Hqueued; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|exact Hqueued].
    destruct (snapshot_live ss); [|exact Hqueued].
    cbn [invalid_bad invalid_pending invalid_done].
    now apply invalid_seed_fold_queued.
  Qed.

  Lemma invalid_snapshot_fold_queued : forall st ids acc,
    invalid_queued acc ->
    invalid_queued (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hqueued;
      [exact Hqueued|].
    cbn [fold_left]; apply IH; now apply invalid_snapshot_queued.
  Qed.

  Lemma invalid_walk_queued : forall p p' ch st,
    invalid_queued (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_queued) (Post := invalid_queued).
    - intros [pending0 seen bad done snapshots] Hqueued.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hqueued|].
      unfold invalid_next; apply invalid_snapshot_fold_queued.
      intros y Hy; destruct (Hqueued y Hy) as [Hpending|Hdone].
      + destruct Hpending as [<-|Hpending];
          [right; now left|left; exact Hpending].
      + right; now right.
    - unfold invalid_initial; apply invalid_seed_fold_queued.
      intros x Hx; contradiction.
  Qed.

  Lemma invalid_walk_pending_empty : forall p p' ch st,
    invalid_pending (invalid_walk p p' ch st) = [].
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := fun _ => True)
      (Post := fun acc => invalid_pending acc = []); [|exact I].
    intros [pending0 seen bad done snapshots] _.
    destruct pending0 as [|x pending]; cbn [invalid_checked_step];
      [reflexivity|exact I].
  Qed.

  Lemma invalid_walk_bad_done : forall p p' ch st x,
    In x (invalidate_keys p p' ch st) ->
    In x (invalid_done (invalid_walk p p' ch st)).
  Proof.
    intros p p' ch st x Hbad; unfold invalidate_keys in Hbad.
    pose proof (invalid_walk_queued p p' ch st x Hbad) as [Hpending|Hdone];
      [|exact Hdone].
    rewrite invalid_walk_pending_empty in Hpending; contradiction.
  Qed.

  Definition invalid_snapshot_view (st : state)
      (acc : incremental_invalidation S.key) : Prop :=
    forall id ss, PTrieCode.get id (inc_snapshots st) = Some ss ->
      snapshot_live ss = true ->
      exists current, PTrieCode.get id (invalid_snapshots acc) = Some current /\
        snapshot_writes current = snapshot_writes ss /\
        (snapshot_live current = false ->
          forall y, In y (snapshot_writes ss) -> present st y = true ->
            In y (invalid_bad acc)).

  Lemma invalid_seed_snapshot_view : forall st acc x,
    invalid_snapshot_view st acc -> invalid_snapshot_view st (invalid_seed_one st acc x).
  Proof.
    intros st acc x Hview; unfold invalid_seed_one.
    destruct (present st x); [|exact Hview].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      [exact Hview|].
    intros id ss Hget Hlive.
    destruct (Hview id ss Hget Hlive) as [current [Hcurrent [Hwrites Hbad]]].
    exists current; cbn [invalid_snapshots invalid_bad]; split; [exact Hcurrent|].
    split; [exact Hwrites|].
    intros Hretired y Hy Hpresent; right; now apply Hbad.
  Qed.

  Lemma invalid_seed_fold_snapshot_view : forall st xs acc,
    invalid_snapshot_view st acc ->
    invalid_snapshot_view st (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hview;
      [exact Hview|].
    cbn [fold_left]; apply IH; now apply invalid_seed_snapshot_view.
  Qed.

  Lemma invalid_seed_fold_snapshots : forall st xs acc,
    invalid_snapshots (fold_left (invalid_seed_one st) xs acc) = invalid_snapshots acc.
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc; [reflexivity|].
    cbn [fold_left]; rewrite IH; unfold invalid_seed_one.
    destruct (present st x); [|reflexivity].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)); reflexivity.
  Qed.

  Lemma invalid_visit_snapshot_view : forall st acc visit,
    invalid_seen_bad acc -> invalid_snapshot_view st acc ->
    invalid_snapshot_view st (invalid_visit_snapshot st acc visit).
  Proof.
    intros st acc visit Hseen Hview; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get visit (invalid_snapshots acc)) as [visited|]
      eqn:Hvisit; [|exact Hview].
    destruct (snapshot_live visited) eqn:Hlive; [|exact Hview].
    set (next := fold_left (invalid_seed_one st) (snapshot_writes visited) acc).
    intros id ss Horig Horiglive.
    destruct (Hview id ss Horig Horiglive) as
      [current [Hcurrent [Hwrites Hbad]]].
    destruct (Pos.eq_dec id visit) as [->|Hneq].
    - rewrite Hvisit in Hcurrent; inversion Hcurrent; subst current.
      exists {| snapshot_owner := snapshot_owner visited;
                snapshot_writes := snapshot_writes visited;
                snapshot_live := false |}.
      cbn [invalid_snapshots invalid_bad snapshot_writes snapshot_live].
      split; [apply PTrie.get_set_same|].
      split; [exact Hwrites|].
      intros _ y Hy Hpresent.
      unfold next; eapply invalid_seed_fold_contains;
        [exact Hseen|rewrite Hwrites; exact Hy|exact Hpresent].
    - exists current; cbn [invalid_snapshots invalid_bad].
      rewrite PTrie.get_set_other by exact Hneq.
      unfold next; rewrite invalid_seed_fold_snapshots; split; [exact Hcurrent|].
      split; [exact Hwrites|].
      intros Hretired y Hy Hpresent; unfold next.
      apply invalid_seed_fold_bad_keeps.
      now apply Hbad.
  Qed.

  Lemma invalid_snapshot_fold_view : forall st ids acc,
    invalid_seen_bad acc -> invalid_snapshot_view st acc ->
    invalid_snapshot_view st (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hseen Hview;
      [exact Hview|].
    cbn [fold_left]; apply IH.
    - now apply invalid_snapshot_seen_bad.
    - now apply invalid_visit_snapshot_view.
  Qed.

  Lemma invalid_walk_snapshot_view : forall p p' ch st,
    invalid_snapshot_view st (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := fun acc => invalid_seen_bad acc /\ invalid_snapshot_view st acc)
      (Post := invalid_snapshot_view st).
    - intros [pending0 seen bad done snapshots] [Hseen Hview].
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hview|].
      unfold invalid_next; split.
      + apply invalid_snapshot_fold_seen_bad; exact Hseen.
      + apply invalid_snapshot_fold_view; assumption.
    - unfold invalid_initial; split.
      + apply invalid_seed_fold_seen_bad.
        intros x Hseen; cbn [invalid_seen] in Hseen.
        rewrite PTrie.get_empty in Hseen; discriminate.
      + apply invalid_seed_fold_snapshot_view.
        intros id ss Hget Hlive; exists ss.
        cbn [invalid_snapshots snapshot_writes snapshot_live].
        split; [exact Hget|].
        split; [reflexivity|congruence].
  Qed.

  Definition invalid_snapshot_origin (st : state)
      (acc : incremental_invalidation S.key) : Prop :=
    forall id current, PTrieCode.get id (invalid_snapshots acc) = Some current ->
      exists original, PTrieCode.get id (inc_snapshots st) = Some original /\
        snapshot_owner current = snapshot_owner original /\
        snapshot_writes current = snapshot_writes original /\
        (snapshot_live current = true -> snapshot_live original = true).

  Lemma invalid_seed_origin : forall st acc x,
    invalid_snapshot_origin st acc -> invalid_snapshot_origin st (invalid_seed_one st acc x).
  Proof.
    intros st acc x Horigin; unfold invalid_seed_one.
    destruct (present st x); [|exact Horigin].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      exact Horigin.
  Qed.

  Lemma invalid_seed_fold_origin : forall st xs acc,
    invalid_snapshot_origin st acc ->
    invalid_snapshot_origin st (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Horigin;
      [exact Horigin|].
    cbn [fold_left]; apply IH; now apply invalid_seed_origin.
  Qed.

  Lemma invalid_visit_origin : forall st acc visit,
    invalid_snapshot_origin st acc ->
    invalid_snapshot_origin st (invalid_visit_snapshot st acc visit).
  Proof.
    intros st acc visit Horigin; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get visit (invalid_snapshots acc)) as [visited|]
      eqn:Hvisit; [|exact Horigin].
    destruct (snapshot_live visited) eqn:Hlive; [|exact Horigin].
    intros id current Hget; cbn [invalid_snapshots] in Hget.
    destruct (Pos.eq_dec id visit) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget; inversion Hget; subst current.
      destruct (Horigin visit visited Hvisit) as
        [original [Horig [Howner [Hwrites Hactive]]]].
      exists original; split; [exact Horig|].
      split; [exact Howner|].
      split; [exact Hwrites|discriminate].
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      rewrite invalid_seed_fold_snapshots in Hget.
      now apply Horigin in Hget.
  Qed.

  Lemma invalid_snapshot_fold_origin : forall st ids acc,
    invalid_snapshot_origin st acc ->
    invalid_snapshot_origin st (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Horigin;
      [exact Horigin|].
    cbn [fold_left]; apply IH; now apply invalid_visit_origin.
  Qed.

  Lemma invalid_walk_snapshot_origin : forall p p' ch st,
    invalid_snapshot_origin st (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_snapshot_origin st) (Post := invalid_snapshot_origin st).
    - intros [pending0 seen bad done snapshots] Horigin.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Horigin|].
      unfold invalid_next; apply invalid_snapshot_fold_origin; exact Horigin.
    - unfold invalid_initial; apply invalid_seed_fold_origin.
      intros id current Hget; exists current.
      cbn [invalid_snapshots] in Hget.
      split; [exact Hget|].
      split; [reflexivity|].
      split; [reflexivity|].
      intros Hlive; exact Hlive.
  Qed.

  Definition invalid_snapshot_support (st : state)
      (acc : incremental_invalidation S.key) : Prop :=
    forall id original, PTrieCode.get id (inc_snapshots st) = Some original ->
      exists current, PTrieCode.get id (invalid_snapshots acc) = Some current.

  Lemma invalid_seed_support : forall st acc x,
    invalid_snapshot_support st acc -> invalid_snapshot_support st (invalid_seed_one st acc x).
  Proof.
    intros st acc x Hsupport; unfold invalid_seed_one.
    destruct (present st x); [|exact Hsupport].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      exact Hsupport.
  Qed.

  Lemma invalid_seed_fold_support : forall st xs acc,
    invalid_snapshot_support st acc ->
    invalid_snapshot_support st (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hsupport;
      [exact Hsupport|].
    cbn [fold_left]; apply IH; now apply invalid_seed_support.
  Qed.

  Lemma invalid_visit_support : forall st acc visit,
    invalid_snapshot_support st acc ->
    invalid_snapshot_support st (invalid_visit_snapshot st acc visit).
  Proof.
    intros st acc visit Hsupport id original Horig.
    destruct (Hsupport id original Horig) as [current Hcurrent].
    unfold invalid_visit_snapshot.
    destruct (PTrieCode.get visit (invalid_snapshots acc)) as [visited|]
      eqn:Hvisit; [|now exists current].
    destruct (snapshot_live visited); [|now exists current].
    destruct (Pos.eq_dec id visit) as [->|Hneq].
    - eexists; cbn [invalid_snapshots]; apply PTrie.get_set_same.
    - exists current; cbn [invalid_snapshots].
      rewrite PTrie.get_set_other by exact Hneq.
      now rewrite invalid_seed_fold_snapshots.
  Qed.

  Lemma invalid_snapshot_fold_support : forall st ids acc,
    invalid_snapshot_support st acc ->
    invalid_snapshot_support st (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hsupport;
      [exact Hsupport|].
    cbn [fold_left]; apply IH; now apply invalid_visit_support.
  Qed.

  Lemma invalid_walk_snapshot_support : forall p p' ch st,
    invalid_snapshot_support st (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_snapshot_support st) (Post := invalid_snapshot_support st).
    - intros [pending0 seen bad done snapshots] Hsupport.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hsupport|].
      unfold invalid_next; apply invalid_snapshot_fold_support; exact Hsupport.
    - unfold invalid_initial; apply invalid_seed_fold_support.
      intros id original Hget; exists original.
      cbn [invalid_snapshots]; exact Hget.
  Qed.

  Definition invalid_retired (acc : incremental_invalidation S.key) (id : positive) : Prop :=
    forall ss, PTrieCode.get id (invalid_snapshots acc) = Some ss ->
      snapshot_live ss = false.

  Lemma invalid_seed_retired : forall st acc x id,
    invalid_retired acc id -> invalid_retired (invalid_seed_one st acc x) id.
  Proof.
    intros st acc x id Hretired; unfold invalid_seed_one.
    destruct (present st x); [|exact Hretired].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      exact Hretired.
  Qed.

  Lemma invalid_seed_fold_retired : forall st xs acc id,
    invalid_retired acc id ->
    invalid_retired (fold_left (invalid_seed_one st) xs acc) id.
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc id Hretired;
      [exact Hretired|].
    cbn [fold_left]; apply IH; now apply invalid_seed_retired.
  Qed.

  Lemma invalid_visit_retired : forall st acc visit id,
    invalid_retired acc id -> invalid_retired (invalid_visit_snapshot st acc visit) id.
  Proof.
    intros st acc visit id Hretired; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get visit (invalid_snapshots acc)) as [visited|]
      eqn:Hvisit; [|exact Hretired].
    destruct (snapshot_live visited) eqn:Hlive; [|exact Hretired].
    intros ss Hget; cbn [invalid_snapshots] in Hget.
    destruct (Pos.eq_dec id visit) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget; inversion Hget; reflexivity.
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      rewrite invalid_seed_fold_snapshots in Hget.
      now apply Hretired in Hget.
  Qed.

  Lemma invalid_visit_retired_target : forall st acc id,
    invalid_retired (invalid_visit_snapshot st acc id) id.
  Proof.
    intros st acc id; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [visited|]
      eqn:Hvisit.
    - destruct (snapshot_live visited) eqn:Hlive.
      + intros ss Hget; cbn [invalid_snapshots] in Hget.
        rewrite PTrie.get_set_same in Hget; inversion Hget; reflexivity.
      + intros ss Hget; rewrite Hvisit in Hget; inversion Hget; subst; exact Hlive.
    - intros ss Hget; rewrite Hvisit in Hget; discriminate.
  Qed.

  Lemma invalid_snapshot_fold_retired : forall st ids acc id,
    invalid_retired acc id ->
    invalid_retired (fold_left (invalid_visit_snapshot st) ids acc) id.
  Proof.
    intros st ids; induction ids as [|visit rest IH]; intros acc id Hretired;
      [exact Hretired|].
    cbn [fold_left]; apply IH; now apply invalid_visit_retired.
  Qed.

  Lemma invalid_snapshot_fold_retired_member : forall st ids acc id,
    In id ids -> invalid_retired (fold_left (invalid_visit_snapshot st) ids acc) id.
  Proof.
    intros st ids; induction ids as [|visit rest IH]; intros acc id Hin;
      [contradiction|].
    cbn [fold_left]; destruct Hin as [<-|Hin].
    - apply invalid_snapshot_fold_retired, invalid_visit_retired_target.
    - now apply IH.
  Qed.

  Definition invalid_processed (st : state)
      (acc : incremental_invalidation S.key) : Prop :=
    forall x, In x (invalid_done acc) ->
      forall id, In id (invalid_buckets st x) -> invalid_retired acc id.

  Lemma invalid_seed_fold_done : forall st xs acc,
    invalid_done (fold_left (invalid_seed_one st) xs acc) = invalid_done acc.
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc; [reflexivity|].
    cbn [fold_left]; rewrite IH; unfold invalid_seed_one.
    destruct (present st x); [|reflexivity].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)); reflexivity.
  Qed.

  Lemma invalid_snapshot_fold_done : forall st ids acc,
    invalid_done (fold_left (invalid_visit_snapshot st) ids acc) = invalid_done acc.
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc; [reflexivity|].
    cbn [fold_left]; rewrite IH; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|];
      [|reflexivity].
    destruct (snapshot_live ss); [|reflexivity].
    cbn [invalid_done]; apply invalid_seed_fold_done.
  Qed.

  Lemma invalid_seed_processed : forall st acc x,
    invalid_processed st acc -> invalid_processed st (invalid_seed_one st acc x).
  Proof.
    intros st acc x Hprocessed; unfold invalid_seed_one.
    destruct (present st x); [|exact Hprocessed].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      [exact Hprocessed|exact Hprocessed].
  Qed.

  Lemma invalid_seed_fold_processed : forall st xs acc,
    invalid_processed st acc ->
    invalid_processed st (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st xs; induction xs as [|x rest IH]; intros acc Hprocessed;
      [exact Hprocessed|].
    cbn [fold_left]; apply IH; now apply invalid_seed_processed.
  Qed.

  Lemma invalid_visit_processed : forall st acc visit,
    invalid_processed st acc ->
    invalid_processed st (invalid_visit_snapshot st acc visit).
  Proof.
    intros st acc visit Hprocessed; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get visit (invalid_snapshots acc)) as [ss|];
      [|exact Hprocessed].
    destruct (snapshot_live ss); [|exact Hprocessed].
    pose proof (invalid_seed_fold_processed st (snapshot_writes ss) acc Hprocessed)
      as Hfold.
    intros x Hdone id Hid current Hget.
    cbn [invalid_done invalid_snapshots] in Hdone, Hget.
    destruct (Pos.eq_dec id visit) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget; inversion Hget; reflexivity.
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      exact (Hfold x Hdone id Hid current Hget).
  Qed.

  Lemma invalid_snapshot_fold_processed : forall st ids acc,
    invalid_processed st acc ->
    invalid_processed st (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st ids; induction ids as [|id rest IH]; intros acc Hprocessed;
      [exact Hprocessed|].
    cbn [fold_left]; apply IH; now apply invalid_visit_processed.
  Qed.

  Lemma invalid_walk_processed : forall p p' ch st,
    invalid_processed st (invalid_walk p p' ch st).
  Proof.
    intros p p' ch st; unfold invalid_walk.
    eapply incremental_loop_preserves with
      (Inv := invalid_processed st) (Post := invalid_processed st).
    - intros [pending0 seen bad done snapshots] Hprocessed.
      destruct pending0 as [|x pending]; cbn [invalid_checked_step];
        [exact Hprocessed|].
      unfold invalid_next; intros y Hy id Hid.
      rewrite invalid_snapshot_fold_done in Hy.
      cbn [invalid_done] in Hy.
      destruct Hy as [<-|Hy].
      + apply invalid_snapshot_fold_retired_member.
        exact Hid.
      + apply invalid_snapshot_fold_retired.
        exact (Hprocessed y Hy id Hid).
    - unfold invalid_initial; apply invalid_seed_fold_processed.
      intros x Hx; contradiction.
  Qed.

  Lemma invalidate_bucket_snapshot : forall p p' ch st id ss x y,
    PTrieCode.get id (inc_snapshots st) = Some ss ->
    snapshot_live ss = true ->
    In id (invalid_buckets st x) ->
    In x (invalidate_keys p p' ch st) ->
    In y (snapshot_writes ss) -> present st y = true ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st id ss x y Hget Hlive Hbucket Hbad Hy Hpresent.
    pose proof (invalid_walk_bad_done p p' ch st x Hbad) as Hdone.
    pose proof (invalid_walk_processed p p' ch st x Hdone id Hbucket) as Hretired.
    destruct (invalid_walk_snapshot_view p p' ch st id ss Hget Hlive) as
      [current [Hcurrent [Hwrites Hwrites_bad]]].
    unfold invalidate_keys; apply (Hwrites_bad (Hretired current Hcurrent) y Hy Hpresent).
  Qed.

  Lemma invalidate_keys_row : forall p p' ch st q r x y,
    row_snapshot_recorded q st r y ->
    In x (S.writes q r ++ S.deps q r) ->
    In x (invalidate_keys p p' ch st) -> In y (S.writes q r) -> dom st y ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st q r x y [ss [Hget [Hlive [Hwrites Hdeps]]]]
      Hx Hbad Hy Hdom.
    destruct (Hwrites y Hy) as [Hss _].
    eapply invalidate_bucket_snapshot;
      [exact Hget|exact Hlive| |exact Hbad|exact Hss|].
    - apply in_app_iff in Hx as [Hx|Hx].
      + unfold invalid_buckets; apply in_or_app; right.
        exact (proj2 (Hwrites x Hx)).
      + unfold invalid_buckets; apply in_or_app; left.
        exact (Hdeps x Hx).
    - now apply (proj2 (present_spec st y)).
  Qed.

  (** Old rows propagate invalidation from reads and co-writes to every stored write. *)
  Lemma invalidate_keys_old : forall p p' ch st r x y,
    row_snapshot_recorded p st r y -> In x (S.writes p r ++ S.deps p r) ->
    In x (invalidate_keys p p' ch st) -> In y (S.writes p r) -> dom st y ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st r x y Hrecorded Hx Hbad Hy Hdom.
    exact (invalidate_keys_row p p' ch st p r x y Hrecorded Hx Hbad Hy Hdom).
  Qed.

  (** New rows propagate invalidation from reads and co-writes to every stored write. *)
  Lemma invalidate_keys_new : forall p p' ch st r x y,
    row_snapshot_recorded p' st r y -> In x (S.writes p' r ++ S.deps p' r) ->
    In x (invalidate_keys p p' ch st) -> In y (S.writes p' r) -> dom st y ->
    In y (invalidate_keys p p' ch st).
  Proof.
    intros p p' ch st r x y Hrecorded Hx Hbad Hy Hdom.
    exact (invalidate_keys_row p p' ch st p' r x y Hrecorded Hx Hbad Hy Hdom).
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
    (forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      row_snapshot_recorded p st r y) ->
    closed p (fun x => dom st x /\ ~ In x (invalidate_keys p p' ch st)).
  Proof.
    intros p p' ch st [Hclosed Hpost] Hrecorded r y x Hr Hy [Hdom Hkeep] Hx; split.
    - exact (Hclosed r y x Hr Hy Hdom Hx).
    - intro Hbad; apply Hkeep.
      exact (invalidate_keys_old p p' ch st r x y
        (Hrecorded r y Hr Hy Hdom) Hx Hbad Hy Hdom).
  Qed.

  (** Removing the closure leaves a closed domain in the new program. *)
  Lemma invalidate_closed : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    tracks p st ->
    closed p' (fun x => dom st x /\ ~ In x (invalidate p p' ch st)).
  Proof.
    unfold invalidate.
    intros p p' ch st Hcovers [Hclosed Hpost] Htracks r y x Hr' Hy' [Hdom Hkeep] Hx'.
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
      exact (invalidate_keys_old p p' ch st r x y
        (Htracks r y Hr Hy Hdom) Hx Hbad Hy Hdom).
  Qed.

  Definition invalidate_keys_closed := invalidate_closed.

  (** Metadata retirement does not alter exact value deletion. *)
  Lemma edit_value : forall p p' ch st x,
    value (edit p p' ch st) x =
      if existsb (S.key_eqb x) (invalidate p p' ch st) then None else value st x.
  Proof.
    unfold invalidate, invalidate_keys.
    intros p p' ch st x; unfold edit.
    destruct (invalid_walk p p' ch st) as [pending seen bad done snapshots].
    destruct bad as [|y bad]; [reflexivity|].
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
    tracks p st -> post_on p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hwf Hcovers Hinv Htracks r y Hr' Hy' Hnew.
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
      exact (proj2 (invalidate_keys_closed p p' ch st Hcovers Hinv Htracks r y x
        Hr' Hy' (conj Hdom Hkeep) Hx)). }
    rewrite (row_look_transport p' r (look st) (look (edit p p' ch st))
      Hwf Hr' Hagree) in Hrow.
    exact Hrow.
  Qed.

  Definition edit_frame_keys := edit_frame.

  Lemma edit_inv : forall p p' ch st,
    S.wf p' -> edit_covers p p' ch -> inv p st -> tracks p st ->
    inv p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hwf Hcovers Hinv Htracks; split.
    - intros r y x Hr Hy Hnew Hx; apply (proj2 (edit_dom_keys p p' ch st x)).
      apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew.
      exact (invalidate_keys_closed p p' ch st Hcovers Hinv Htracks r y x Hr Hy Hnew Hx).
    - exact (edit_frame_keys p p' ch st Hwf Hcovers Hinv Htracks).
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
    assert (Hrows : forall r, In r (discovery_region p roots st) -> In r (S.rows p)).
    { intros r Hr; apply region_for_spec in Hr; tauto. }
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
    rewrite fill_local_eq_fill, fill_lookup in Hvalue.
    destruct (Bindings.mem x (discovery_keys p roots st)) eqn:Hmem.
    - injection Hvalue as <-; rewrite Checker.look_spec.
      apply restore_below.
      + exact (Hcandidate upper Hpost).
      + intros y w Hin; apply (Hleast upper Hpost y w).
        exact (frozen_for_rows_sound p (discovery_region p roots st) st y w Hin).
    - exact (Hleast upper Hpost x v Hvalue).
  Qed.

  Lemma regional_run_below_result : forall p pol roots fuel st ks rs fz m,
    S.wf p -> S.monotone p -> Least.widening_free pol -> least_on p st ->
    discovery p roots fuel st = Some (ks, rs, fz) ->
    Sol.run (R.mk p fz rs) pol fuel = Solved m ->
    forall upper, S.post_solution p upper -> forall x,
      L.leb (look_or S.key_code L.bot m x) (upper x) = true.
  Proof.
    intros p pol roots fuel st ks rs fz m Hwf Hmono Hfree Hleast Hdiscovery Hrun
      upper Hpost x.
    assert (Hrows : forall r, In r rs -> In r (S.rows p)).
    { intros r Hr; eapply discovery_result_rows; eauto. }
    assert (Hseeds : forall y v, In (y, v) fz -> L.leb v (upper y) = true).
    { intros y v Hin; apply (Hleast upper Hpost y v).
      eapply discovery_result_frozen; eauto. }
    eapply (Least.run_least (R.mk p fz rs) pol fuel m upper).
    - apply R.mk_wf; [exact Hwf|exact Hrows].
    - apply R.mk_monotone; [exact Hmono|exact Hrows].
    - exact Hfree.
    - exact Hrun.
    - apply R.restrict_complete; [exact Hpost|exact Hrows|exact Hseeds].
  Qed.

  Lemma finish_demand_least_result : forall p roots fuel st ks rs fz m,
    discovery p roots fuel st = Some (ks, rs, fz) -> least_on p st ->
    (forall upper, S.post_solution p upper -> forall x,
      L.leb (look_or S.key_code L.bot m x) (upper x) = true) ->
    least_on p (finish_demand p st ks rs (restore fz m)).
  Proof.
    intros p roots fuel st ks rs fz m Hdiscovery Hleast Hcandidate upper Hpost x v Hvalue.
    rewrite finish_demand_value in Hvalue.
    unfold value, merge_discovered in Hvalue; cbn [inc_values] in Hvalue.
    rewrite fill_local_eq_fill, fill_lookup in Hvalue.
    destruct (Bindings.mem x ks) eqn:Hmem.
    - injection Hvalue as <-; rewrite Checker.look_spec.
      apply restore_below.
      + exact (Hcandidate upper Hpost).
      + intros y w Hin; apply (Hleast upper Hpost y w).
        eapply discovery_result_frozen; eauto.
    - exact (Hleast upper Hpost x v Hvalue).
  Qed.

  Lemma demand_least : forall p pol roots fuel st o st', S.wf p -> S.monotone p ->
    Least.widening_free pol -> inv p st -> least_on p st ->
    demand p pol roots fuel st = (o, st') -> least_on p st'.
  Proof.
    intros p pol roots fuel st o st' Hwf Hmono Hfree Hinv Hleast Hrun.
    unfold demand in Hrun.
    destruct (forallb (present st) roots); [inversion Hrun; subst; exact Hleast|].
    destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
      [|inversion Hrun; subst; exact Hleast].
    destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why] eqn:Hsolver.
    - destruct (Checker.check_rows p rs (restore fz m)) eqn:Hcheck.
      + inversion Hrun; subst; eapply finish_demand_least_result;
          [exact Hdiscovery|exact Hleast|].
        eapply regional_run_below_result; eauto.
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
  Lemma edit_closed_old : forall p p' ch st, inv p st -> tracks p st ->
    closed p (dom (edit p p' ch st)).
  Proof.
    intros p p' ch st Hinv Htracks r y x Hr Hy Hnew Hx.
    apply (proj2 (edit_dom_keys p p' ch st x)).
    apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew.
    exact (invalidate_keys_closed_old p p' ch st Hinv Htracks
      r y x Hr Hy Hnew Hx).
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
    inv p st -> tracks p st -> least_on p st -> least_on p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hwf Hcovers Hinv Htracks Hleast s Hpost x v Hvalue.
    assert (Hpatched : S.post_solution p
      (TopFacts.top_extend (present (edit p p' ch st)) s)).
    { apply top_extend_state_post;
        [exact Hwf|apply edit_closed_old; assumption|].
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

  Lemma tracks_finish : forall p st xs rs m,
    inv p st -> tracks p st ->
    (forall x, In x xs -> value st x = None) ->
    (forall r y, In r (S.rows p) -> In y (S.writes p r) -> In y xs -> In r rs) ->
    tracks p (finish_demand p st xs rs m).
  Proof.
    intros p st xs rs m [Hclosed Hpost] Htracks Hfresh Hselected r y Hr Hy Hdom.
    apply (proj1 (finish_demand_dom p st xs rs m y)) in Hdom as [Hold|Hnew].
    - destruct (Htracks r y Hr Hy Hold) as
        [ss [Hget [Hlive [Hwrites Hdeps]]]].
      destruct (metadata_finish_preserves p st xs rs m
        (S.key_code (S.target p r)) ss (S.writes p r) (S.deps p r))
        as [ss' [Hget' [Hlive' [Hwrites' Hdeps']]]];
        try assumption.
      + intros x Hx; exact (Hclosed r y x Hr Hy Hold Hx).
      + exists ss'; split; [exact Hget'|].
        split; [exact Hlive'|].
        split; [exact Hwrites'|exact Hdeps'].
    - unfold finish_demand.
      destruct (metadata_record_rows_own p rs
        (metadata_prepared_state st xs m) r (Hselected r y Hr Hy Hnew))
        as [ss [Hget [Hlive [Hwrites Hdeps]]]].
      exists ss; split; [exact Hget|].
      split; [exact Hlive|].
      split; [exact Hwrites|exact Hdeps].
  Qed.

  Lemma tracks_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    tracks p st -> demand p pol roots fuel st = (o, st') -> tracks p st'.
  Proof.
    intros p pol roots fuel st o st' Hwf Hinv Htracks Hrun.
    unfold demand in Hrun.
    destruct (forallb (present st) roots); [inversion Hrun; subst; exact Htracks|].
    destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
      [|inversion Hrun; subst; exact Htracks].
    destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why] eqn:Hsolver.
    - destruct (Checker.check_rows p rs (restore fz m)) eqn:Hcheck;
        [|inversion Hrun; subst; exact Htracks].
      inversion Hrun; subst; clear Hrun.
      apply tracks_finish; [exact Hinv|exact Htracks| |].
      + exact (proj2 (discovery_result_missing p roots fuel st ks rs fz Hdiscovery)).
      + intros r y Hr Hy Hnew.
        eapply discovery_result_done_rows; [exact Hdiscovery|exact Hnew|].
        apply (proj2 (S.rows_of_spec p y r Hwf)); split; assumption.
    - inversion Hrun; subst; exact Htracks.
    - inversion Hrun; subst; exact Htracks.
  Qed.

  Lemma metadata_edit_snapshot : forall p p' ch st id ss y,
    snapshot_get id st = Some ss -> snapshot_live ss = true ->
    In y (snapshot_writes ss) -> dom st y ->
    ~ In y (invalidate_keys p p' ch st) ->
    exists current, snapshot_get id (edit p p' ch st) = Some current /\
      snapshot_live current = true /\
      snapshot_writes current = snapshot_writes ss.
  Proof.
    intros p p' ch st id ss y Hget Hlive Hy Hdom Hkeep.
    unfold edit; destruct (invalid_walk p p' ch st)
      as [pending seen bad done snapshots] eqn:Hwalk.
    destruct bad as [|z bad].
    - exists ss; split; [exact Hget|]; split; [exact Hlive|reflexivity].
    - pose proof (invalid_walk_snapshot_view p p' ch st id ss Hget Hlive)
        as Hview.
      rewrite Hwalk in Hview.
      destruct Hview as [current [Hcurrent [Hwrites Hbad]]].
      exists current; split; [exact Hcurrent|]; split; [|exact Hwrites].
      destruct (snapshot_live current) eqn:Hcurrent_live; [reflexivity|].
      exfalso; apply Hkeep.
      unfold invalidate_keys; rewrite Hwalk.
      apply (Hbad eq_refl y Hy).
      now apply (proj2 (present_spec st y)).
  Qed.

  Lemma metadata_edit_infl : forall p p' ch st x,
    ~ In x (invalidate_keys p p' ch st) ->
    metadata_bucket_at (inc_influence (edit p p' ch st)) x =
      metadata_bucket_at (inc_influence st) x.
  Proof.
    intros p p' ch st x Hkeep; unfold edit.
    destruct (invalid_walk p p' ch st) as [pending seen bad done snapshots]
      eqn:Hwalk; destruct bad as [|z bad]; [reflexivity|].
    unfold metadata_bucket_at; cbn [inc_influence].
    change (match PTrieCode.get (S.key_code x)
      (InvFacts.Bindings.remove_keys (z :: bad) (inc_influence st)) with
      | Some ids => ids | None => [] end =
      metadata_bucket_at (inc_influence st) x).
    rewrite InvFacts.raw_get_remove_keys.
    assert (Hmem : InvFacts.Bindings.mem x (z :: bad) = false).
    { destruct (InvFacts.Bindings.mem x (z :: bad)) eqn:Htest;
        [|reflexivity].
      exfalso; apply Hkeep; unfold invalidate_keys; rewrite Hwalk.
      now apply (proj1 (InvFacts.mem_spec x (z :: bad))). }
    rewrite Hmem; reflexivity.
  Qed.

  Lemma metadata_edit_cowrite : forall p p' ch st x,
    ~ In x (invalidate_keys p p' ch st) ->
    metadata_bucket_at (inc_cowrites (edit p p' ch st)) x =
      metadata_bucket_at (inc_cowrites st) x.
  Proof.
    intros p p' ch st x Hkeep; unfold edit.
    destruct (invalid_walk p p' ch st) as [pending seen bad done snapshots]
      eqn:Hwalk; destruct bad as [|z bad]; [reflexivity|].
    unfold metadata_bucket_at; cbn [inc_cowrites].
    change (match PTrieCode.get (S.key_code x)
      (InvFacts.Bindings.remove_keys (z :: bad) (inc_cowrites st)) with
      | Some ids => ids | None => [] end =
      metadata_bucket_at (inc_cowrites st) x).
    rewrite InvFacts.raw_get_remove_keys.
    assert (Hmem : InvFacts.Bindings.mem x (z :: bad) = false).
    { destruct (InvFacts.Bindings.mem x (z :: bad)) eqn:Htest;
        [|reflexivity].
      exfalso; apply Hkeep; unfold invalidate_keys; rewrite Hwalk.
      now apply (proj1 (InvFacts.mem_spec x (z :: bad))). }
    rewrite Hmem; reflexivity.
  Qed.

  Lemma tracks_edit : forall p p' ch st, edit_covers p p' ch -> inv p st ->
    tracks p st -> tracks p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hcovers Hinv Htracks r y Hr' Hy' Hnew.
    apply (proj1 (edit_dom_keys p p' ch st y)) in Hnew as [Hold Hkeep].
    pose proof (retained_row_unchanged p p' ch st r y Hr' Hy' Hold Hkeep)
      as Hunchanged.
    destruct (Hcovers r Hunchanged) as [Hrows Hbody].
    pose proof (proj2 Hrows Hr') as Hr.
    destruct (Hbody Hr) as [Htarget [Hdeps [Hsides Heval]]].
    assert (Hwrites_eq : S.writes p r = S.writes p' r).
    { unfold S.writes; now rewrite Htarget, Hsides. }
    assert (Hy : In y (S.writes p r)) by (rewrite Hwrites_eq; exact Hy').
    pose proof (Htracks r y Hr Hy Hold) as Hrecorded.
    destruct Hrecorded as [ss [Hget [Hlive [Hwrites Hreads]]]].
    destruct (Hwrites y Hy) as [Hss_y Hcow_y].
    destruct (metadata_edit_snapshot p p' ch st
      (S.key_code (S.target p r)) ss y Hget Hlive Hss_y Hold Hkeep)
      as [current [Hcurrent [Hcurrent_live Hcurrent_writes]]].
    assert (Hrecorded' : row_snapshot_recorded p (edit p p' ch st) r y).
    { exists current; split; [exact Hcurrent|].
      split; [exact Hcurrent_live|].
      split.
      - intros w Hw; destruct (Hwrites w Hw) as [Hss_w Hcow_w]; split.
        + rewrite Hcurrent_writes; exact Hss_w.
        + assert (Hkeep_w : ~ In w (invalidate_keys p p' ch st)).
          { intro Hbad; apply Hkeep.
            eapply invalidate_keys_old; [| |exact Hbad|exact Hy|exact Hold].
            - exists ss; split; [exact Hget|].
              split; [exact Hlive|].
              split; [exact Hwrites|exact Hreads].
            - apply in_or_app; now left. }
          change (In (S.key_code (S.target p r))
            (metadata_bucket_at (inc_cowrites (edit p p' ch st)) w)).
          rewrite metadata_edit_cowrite by exact Hkeep_w; exact Hcow_w.
      - intros x Hx.
        assert (Hkeep_x : ~ In x (invalidate_keys p p' ch st)).
        { intro Hbad; apply Hkeep.
          eapply invalidate_keys_old; [| |exact Hbad|exact Hy|exact Hold].
          - exists ss; split; [exact Hget|].
            split; [exact Hlive|].
            split; [exact Hwrites|exact Hreads].
          - apply in_or_app; now right. }
        change (In (S.key_code (S.target p r))
          (metadata_bucket_at (inc_influence (edit p p' ch st)) x)).
        rewrite metadata_edit_infl by exact Hkeep_x; now apply Hreads. }
    unfold row_snapshot_recorded in *.
    rewrite <- Htarget, <- Hdeps, <- Hwrites_eq.
    exact Hrecorded'.
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
  TimeFun empty_discovery.
  TimeFun discovery_visit.
  TimeFun discovery_seed_one.
  TimeFun discovery_row.
  TimeFun discovery_step.
  TimeFun discovery.
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
  TimeFun fill_local.
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
  TimeFun invalid_seed_one.
  TimeFun invalid_visit_snapshot.
  TimeFun invalid_next.
  TimeFun invalid_step.
  TimeFun invalid_initial.
  TimeFun invalid_checked_step.
  TimeFun invalid_walk.
  TimeFun changed_seeds.
  TimeFun invalidate_keys.
  TimeFun retire_snapshot.
  TimeFun edit.
  TimeFun invalidate.
  Local Opaque loopN.
  Local Opaque invalid_accessible.
  Module Inventory := SourceBindingInventory L S Checker.
  Definition stored (st : state) : list S.key :=
    Inventory.valid_keys (inc_values st).
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
    Pos.size_nat id <= kwidth st) /\
    Inventory.canonical (inc_values st).

  (** The independent representation fields determine mass and identifier widths. *)
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
      intros st [Hstored [Hnodup [Howner [Hrefs [Hlive
        [Hcounts [Hmass [Hwidth Hcanonical]]]]]]]].
      split; [exact Hcanonical|].
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
          * apply Inventory.valid_keys_nodup.
          * intros x Hx; apply (proj2 (Inventory.valid_keys_dom _ x)).
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
      split; [intro x; apply Inventory.valid_keys_dom|].
      split; [apply Inventory.valid_keys_nodup|].
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
            -- split; [now apply state_core_mass|].
               split; [now apply state_core_width|exact Hcanonical].
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

    Lemma push_entries_keeps : forall ys id buckets x q,
      In q (bucket_at buckets x) ->
      In q (bucket_at (fold_left (fun acc y => push_entry y id acc) ys buckets) x).
    Proof.
      induction ys as [|y rest IH]; intros id buckets x q Hin.
      - exact Hin.
      - cbn [fold_left]; apply IH; rewrite push_entry_at.
        destruct (S.key_eqb x y); [now right|exact Hin].
    Qed.

    Lemma push_entries_add : forall ys id buckets x,
      In x ys ->
      In id (bucket_at (fold_left (fun acc y => push_entry y id acc) ys buckets) x).
    Proof.
      induction ys as [|y rest IH]; intros id buckets x Hin; [contradiction|].
      cbn [fold_left]; destruct Hin as [->|Hin].
      - apply push_entries_keeps; rewrite push_entry_at.
        destruct (S.key_eqb_spec x x); [now left|congruence].
      - apply IH; exact Hin.
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

    (** Preparation fills new values and clears their previously hidden buckets. *)
    Definition prepared_state (st : state) xs m : state :=
      clear_new_buckets xs (merge_discovered st xs m).

    Lemma prepared_values : forall st xs m,
      inc_values (prepared_state st xs m) = fill xs m (inc_values st).
    Proof.
      intros st xs m; unfold prepared_state, clear_new_buckets, merge_discovered.
      cbn [inc_values]; apply fill_local_eq_fill.
    Qed.

    Lemma prepared_value : forall st xs m x,
      value (prepared_state st xs m) x =
        if Bindings.mem x xs then Some (Checker.look m x) else value st x.
    Proof.
      intros st xs m x; unfold prepared_state.
      rewrite clear_buckets_value; unfold value, merge_discovered; cbn [inc_values].
      rewrite fill_local_eq_fill, fill_lookup; reflexivity.
    Qed.

    Lemma prepared_dom : forall st xs m x,
      dom (prepared_state st xs m) x <-> dom st x \/ In x xs.
    Proof.
      intros st xs m x; rewrite <- (merge_dom st xs m x).
      unfold dom; rewrite prepared_value.
      unfold value, merge_discovered; cbn [inc_values].
      rewrite fill_local_eq_fill, fill_lookup; reflexivity.
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
        merge_discovered; cbn [inc_influence].
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
        merge_discovered; cbn [inc_cowrites].
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
      - rewrite prepared_values; apply Inventory.fill_canonical; exact Hcanonical.
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

    Lemma record_row_own : forall p r st,
      exists ss, snapshot_get (S.key_code (S.target p r)) (record_row p r st) = Some ss /\
        snapshot_live ss = true /\
        (forall w, In w (S.writes p r) -> In w (snapshot_writes ss) /\
          In (S.key_code (S.target p r)) (cowrite_at (record_row p r st) w)) /\
        (forall x, In x (S.deps p r) ->
          In (S.key_code (S.target p r)) (infl_at (record_row p r st) x)).
    Proof.
      intros p r st.
      exists (recorded_snapshot st (S.target p r) (row_writes p r)).
      split.
      - rewrite record_row_snapshot_get, Pos.eqb_refl; reflexivity.
      - split; [reflexivity|split].
        + intros w Hw; split.
          * cbn [snapshot_writes]; apply in_or_app; now left.
          * change (In (S.key_code (S.target p r))
              (Buckets.bucket_at
                (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
                  (row_writes p r) (inc_cowrites st)) w)).
            apply Buckets.push_entries_add; exact Hw.
        + intros x Hx.
          change (In (S.key_code (S.target p r))
            (Buckets.bucket_at
              (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
                (S.deps p r) (inc_influence st)) x)).
          apply Buckets.push_entries_add; exact Hx.
    Qed.

    Lemma record_row_preserves : forall p r st id ss ws ds,
      snapshot_get id st = Some ss -> snapshot_live ss = true ->
      (forall w, In w ws -> In w (snapshot_writes ss) /\ In id (cowrite_at st w)) ->
      (forall x, In x ds -> In id (infl_at st x)) ->
      exists ss', snapshot_get id (record_row p r st) = Some ss' /\
        snapshot_live ss' = true /\
        (forall w, In w ws -> In w (snapshot_writes ss') /\
          In id (cowrite_at (record_row p r st) w)) /\
        (forall x, In x ds -> In id (infl_at (record_row p r st) x)).
    Proof.
      intros p r st id ss ws ds Hget Hlive Hwrites Hdeps.
      destruct (Pos.eqb id (S.key_code (S.target p r))) eqn:Hsame.
      - apply Pos.eqb_eq in Hsame; subst id.
        exists (recorded_snapshot st (S.target p r) (row_writes p r)).
        split; [now rewrite record_row_snapshot_get, Pos.eqb_refl|].
        split; [reflexivity|split].
        + intros w Hw; destruct (Hwrites w Hw) as [Hwrite Hcowrite]; split.
          * cbn [recorded_snapshot snapshot_writes]; apply in_or_app; right.
            unfold previous_writes; rewrite Hget, Hlive; exact Hwrite.
          * change (In (S.key_code (S.target p r)) (Buckets.bucket_at
              (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
                (row_writes p r) (inc_cowrites st)) w)).
            apply Buckets.push_entries_keeps; exact Hcowrite.
        + intros x Hx.
          change (In (S.key_code (S.target p r)) (Buckets.bucket_at
            (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
              (S.deps p r) (inc_influence st)) x)).
          apply Buckets.push_entries_keeps; now apply Hdeps.
      - exists ss; split; [now rewrite record_row_snapshot_get, Hsame|].
        split; [exact Hlive|split].
        + intros w Hw; destruct (Hwrites w Hw) as [Hwrite Hcowrite]; split;
            [exact Hwrite|].
          change (In id (Buckets.bucket_at
            (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
              (row_writes p r) (inc_cowrites st)) w)).
          apply Buckets.push_entries_keeps; exact Hcowrite.
        + intros x Hx.
          change (In id (Buckets.bucket_at
            (fold_left (fun acc y => push_entry y (S.key_code (S.target p r)) acc)
              (S.deps p r) (inc_influence st)) x)).
          apply Buckets.push_entries_keeps; now apply Hdeps.
    Qed.

    Lemma record_rows_preserves : forall p rs st id ss ws ds,
      snapshot_get id st = Some ss -> snapshot_live ss = true ->
      (forall w, In w ws -> In w (snapshot_writes ss) /\ In id (cowrite_at st w)) ->
      (forall x, In x ds -> In id (infl_at st x)) ->
      exists ss', snapshot_get id (record_rows p rs st) = Some ss' /\
        snapshot_live ss' = true /\
        (forall w, In w ws -> In w (snapshot_writes ss') /\
          In id (cowrite_at (record_rows p rs st) w)) /\
        (forall x, In x ds -> In id (infl_at (record_rows p rs st) x)).
    Proof.
      intros p rs; induction rs as [|r rest IH]; intros st id ss ws ds
        Hget Hlive Hwrites Hdeps.
      - cbn [record_rows fold_left]; exists ss.
        split; [exact Hget|]; split; [exact Hlive|].
        split; [exact Hwrites|exact Hdeps].
      - cbn [record_rows fold_left].
        destruct (record_row_preserves p r st id ss ws ds Hget Hlive Hwrites Hdeps)
          as [ss' [Hget' [Hlive' [Hwrites' Hdeps']]]].
        exact (IH _ _ _ _ _ Hget' Hlive' Hwrites' Hdeps').
    Qed.

    Lemma record_rows_own : forall p rs st r, In r rs ->
      exists ss, snapshot_get (S.key_code (S.target p r)) (record_rows p rs st) = Some ss /\
        snapshot_live ss = true /\
        (forall w, In w (S.writes p r) -> In w (snapshot_writes ss) /\
          In (S.key_code (S.target p r)) (cowrite_at (record_rows p rs st) w)) /\
        (forall x, In x (S.deps p r) ->
          In (S.key_code (S.target p r)) (infl_at (record_rows p rs st) x)).
    Proof.
      intros p rs; induction rs as [|q rest IH]; intros st r Hr; [contradiction|].
      cbn [record_rows fold_left].
      destruct Hr as [->|Hr].
      - destruct (record_row_own p r st) as [ss [Hget [Hlive [Hwrites Hdeps]]]].
        exact (record_rows_preserves p rest (record_row p r st)
          (S.key_code (S.target p r)) ss (S.writes p r) (S.deps p r)
          Hget Hlive Hwrites Hdeps).
      - apply IH; exact Hr.
    Qed.

    Lemma prepared_group_preserves : forall st xs m id ss ws ds,
      (forall x, In x xs -> value st x = None) ->
      (forall x, In x (ws ++ ds) -> dom st x) ->
      snapshot_get id st = Some ss -> snapshot_live ss = true ->
      (forall w, In w ws -> In w (snapshot_writes ss) /\ In id (cowrite_at st w)) ->
      (forall x, In x ds -> In id (infl_at st x)) ->
      snapshot_get id (prepared_state st xs m) = Some ss /\
      snapshot_live ss = true /\
      (forall w, In w ws -> In w (snapshot_writes ss) /\
        In id (cowrite_at (prepared_state st xs m) w)) /\
      (forall x, In x ds -> In id (infl_at (prepared_state st xs m) x)).
    Proof.
      intros st xs m id ss ws ds Hfresh Hdom Hget Hlive Hwrites Hdeps.
      assert (Houtside : forall x, dom st x -> Inventory.Bindings.mem x xs = false).
      { intros x [v Hv]; destruct (Inventory.Bindings.mem x xs) eqn:Hmem;
          [|reflexivity].
        apply (proj1 (Inventory.mem_spec x xs)) in Hmem.
        rewrite (Hfresh x Hmem) in Hv; discriminate Hv. }
      split; [now rewrite prepared_snapshot_get|].
      split; [exact Hlive|split].
      - intros w Hw; destruct (Hwrites w Hw) as [Hwrite Hcowrite]; split;
          [exact Hwrite|].
        rewrite prepared_cowrite, (Houtside w (Hdom w (in_or_app _ _ _ (or_introl Hw)))).
        exact Hcowrite.
      - intros x Hx.
        rewrite prepared_infl, (Houtside x (Hdom x (in_or_app _ _ _ (or_intror Hx)))).
        now apply Hdeps.
    Qed.

    Lemma finish_group_preserves : forall p st xs rs m id ss ws ds,
      (forall x, In x xs -> value st x = None) ->
      (forall x, In x (ws ++ ds) -> dom st x) ->
      snapshot_get id st = Some ss -> snapshot_live ss = true ->
      (forall w, In w ws -> In w (snapshot_writes ss) /\ In id (cowrite_at st w)) ->
      (forall x, In x ds -> In id (infl_at st x)) ->
      exists ss', snapshot_get id (finish_demand p st xs rs m) = Some ss' /\
        snapshot_live ss' = true /\
        (forall w, In w ws -> In w (snapshot_writes ss') /\
          In id (cowrite_at (finish_demand p st xs rs m) w)) /\
        (forall x, In x ds -> In id (infl_at (finish_demand p st xs rs m) x)).
    Proof.
      intros p st xs rs m id ss ws ds Hfresh Hdom Hget Hlive Hwrites Hdeps.
      destruct (prepared_group_preserves st xs m id ss ws ds Hfresh Hdom
        Hget Hlive Hwrites Hdeps) as [Hget' [Hlive' [Hwrites' Hdeps']]].
      unfold finish_demand.
      exact (record_rows_preserves p rs (prepared_state st xs m)
        id ss ws ds Hget' Hlive' Hwrites' Hdeps').
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

    Lemma finish_demand_core_result : forall p roots fuel st ks rs fz m,
      Core.state_core st -> discovery p roots fuel st = Some (ks, rs, fz) ->
      Core.state_core (finish_demand p st ks rs m).
    Proof.
      intros p roots fuel st ks rs fz m Hcore Hrun.
      change (Core.state_core (record_rows p rs (prepared_state st ks m))).
      apply record_rows_core.
      - apply prepared_core; [exact Hcore|].
        intros x Hx; exact (proj2 (discovery_result_missing p roots fuel st ks rs fz
          Hrun) x Hx).
      - intros r Hr x Hx; apply (proj2 (prepared_dom st ks m x)).
        eapply discovery_result_support; [exact Hrun|exact Hr|].
        apply in_or_app; now left.
    Qed.

    (** Every demand outcome preserves the exact released representation invariant. *)
    Lemma state_ok_demand : forall p pol roots fuel st o st', state_ok st ->
      demand p pol roots fuel st = (o, st') -> state_ok st'.
    Proof.
      intros p pol roots fuel st o st' Hstate Hrun; unfold demand in Hrun.
      destruct (forallb (present st) roots); [inversion Hrun; subst; exact Hstate|].
      destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
        [|inversion Hrun; subst; exact Hstate].
      destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why] eqn:Hsolver.
      - destruct (Checker.check_rows p rs (restore fz m)) eqn:Hcheck.
        + inversion Hrun; subst; apply Core.state_core_ok.
          eapply finish_demand_core_result; [now apply Core.state_ok_core|exact Hdiscovery].
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
      intros p p' ch st x; unfold edit, invalidate_keys.
      destruct (invalid_walk p p' ch st) as [pending seen bad0 done snapshots].
      destruct bad0 as [|y bad]; [reflexivity|].
      change (match PTrieCode.get (S.key_code x)
        (InvFacts.Bindings.remove_keys (y :: bad) (inc_influence st)) with
        | Some ids => ids | None => [] end =
        if mem x (y :: bad) then [] else infl_at st x).
      rewrite InvFacts.raw_get_remove_keys.
      change (InvFacts.Bindings.mem x (y :: bad)) with (mem x (y :: bad)).
      destruct (mem x (y :: bad)); reflexivity.
    Qed.

    (** Editing removes exactly the co-write buckets of invalidated keys. *)
    Lemma edit_cowrite_eq : forall p p' ch st x,
      cowrite_at (edit p p' ch st) x =
        if mem x (invalidate_keys p p' ch st) then [] else cowrite_at st x.
    Proof.
      intros p p' ch st x; unfold edit, invalidate_keys.
      destruct (invalid_walk p p' ch st) as [pending seen bad0 done snapshots].
      destruct bad0 as [|y bad]; [reflexivity|].
      change (match PTrieCode.get (S.key_code x)
        (InvFacts.Bindings.remove_keys (y :: bad) (inc_cowrites st)) with
        | Some ids => ids | None => [] end =
        if mem x (y :: bad) then [] else cowrite_at st x).
      rewrite InvFacts.raw_get_remove_keys.
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

    (** Edits use the snapshot trie returned by the local invalidation walk. *)
    Lemma snapshot_get_edit : forall p p' ch st id,
      snapshot_get id (edit p p' ch st) =
        match invalid_bad (invalid_walk p p' ch st) with
        | [] => snapshot_get id st
        | _ :: _ => PTrieCode.get id (invalid_snapshots (invalid_walk p p' ch st))
        end.
    Proof.
      intros p p' ch st id; unfold edit, snapshot_get.
      destruct (invalid_walk p p' ch st)
        as [pending seen bad done snapshots].
      destruct bad; reflexivity.
    Qed.

    (** An edited snapshot has one original payload at the same identifier. *)
    Lemma snapshot_get_edit_inv : forall p p' ch st id ss',
      snapshot_get id (edit p p' ch st) = Some ss' ->
      exists ss, snapshot_get id st = Some ss /\
        snapshot_owner ss' = snapshot_owner ss /\
        snapshot_writes ss' = snapshot_writes ss /\
        (snapshot_live ss' = true -> snapshot_live ss = true).
    Proof.
      intros p p' ch st id ss' Hget; rewrite snapshot_get_edit in Hget.
      destruct (invalid_walk p p' ch st) as [pending seen bad done snapshots]
        eqn:Hwalk; destruct bad as [|x bad].
      - exists ss'; split; [exact Hget|].
        split; [reflexivity|].
        split; [reflexivity|tauto].
      - pose proof (invalid_walk_snapshot_origin p p' ch st id ss') as Horigin.
        rewrite Hwalk in Horigin.
        exact (Horigin Hget).
    Qed.

    Lemma snapshot_get_edit_support : forall p p' ch st id ss,
      snapshot_get id st = Some ss ->
      exists current, snapshot_get id (edit p p' ch st) = Some current.
    Proof.
      intros p p' ch st id ss Hget; rewrite snapshot_get_edit.
      destruct (invalid_walk p p' ch st) as [pending seen bad done snapshots]
        eqn:Hwalk; destruct bad as [|x bad]; [now exists ss|].
      pose proof (invalid_walk_snapshot_support p p' ch st id ss Hget)
        as Hsupport.
      rewrite Hwalk in Hsupport; exact Hsupport.
    Qed.

    (** Raw stored-key inventory can only shrink, even for malformed input values. *)
    Lemma stored_edit_subset : forall p p' ch st x,
      In x (stored (edit p p' ch st)) -> In x (stored st).
    Proof.
      intros p p' ch st x; unfold edit.
      destruct (invalid_walk p p' ch st) as [pending seen bad0 done snapshots].
      destruct bad0 as [|y bad]; [tauto|].
      unfold stored; cbn [inc_values]; apply Inventory.valid_keys_remove_subset.
    Qed.

    (** Retirement preserves every recorded write key. *)
    Lemma snapshot_keys_edit_subset : forall p p' ch st x,
      In x (snapshot_keys (edit p p' ch st)) -> In x (snapshot_keys st).
    Proof.
      intros p p' ch st x Hin; unfold snapshot_keys in *.
      apply in_flat_map in Hin as [[id ss'] [Hin Hx]].
      apply (proj1 (PTrie.elements_spec _ _ id ss')) in Hin.
      change (snapshot_get id (edit p p' ch st) = Some ss') in Hin.
      apply snapshot_get_edit_inv in Hin as [ss [Hget [_ [Hwrites _]]]].
      cbn [snd] in Hx.
      rewrite Hwrites in Hx.
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
      In id (invalid_buckets st x) ->
      In x (snapshot_writes ss) -> In x (invalidate_keys p p' ch st) ->
      In y (snapshot_writes ss) -> dom st y -> In y (invalidate_keys p p' ch st).
    Proof.
      intros p p' ch st id ss x y Hget Hlive Hbucket Hx Hbad Hy Hdom.
      eapply invalidate_bucket_snapshot;
        [exact Hget|exact Hlive|exact Hbucket|exact Hbad|exact Hy|].
      now apply (proj2 (present_spec st y)).
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
      eapply invalidate_snapshot; [exact Hget|exact Hlive| |exact Hy| |exact Hx|].
      - unfold invalid_buckets; apply in_or_app; right.
        change (In id (cowrite_at st y)).
        apply (proj1 (histogram_count_pos Pos.eqb Pos.eqb_eq id _)).
        pose proof (Hcounts y id) as Hcount.
        rewrite Hget, Hlive in Hcount.
        rewrite Hcount.
        apply (proj2 (histogram_count_pos S.key_eqb key_eqb_true y _)); exact Hy.
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

    Lemma live_edit_write_kept : forall p p' ch st id ss' x,
      Core.state_core st ->
      snapshot_get id (edit p p' ch st) = Some ss' ->
      snapshot_live ss' = true -> In x (snapshot_writes ss') ->
      ~ In x (invalidate_keys p p' ch st).
    Proof.
      intros p p' ch st id ss' x Hcore Hget Hactive Hx Hbad.
      destruct Hcore as [_ [_ [_ [_ Hcounts]]]].
      destruct (snapshot_get_edit_inv p p' ch st id ss' Hget) as
        [ss [Horig [_ [Hwrites Horiglive]]]].
      pose proof (Horiglive Hactive) as Hlive.
      rewrite Hwrites in Hx.
      assert (Hbucket : In id (invalid_buckets st x)).
      { unfold invalid_buckets; apply in_or_app; right.
        change (In id (cowrite_at st x)).
        apply (proj1 (histogram_count_pos Pos.eqb Pos.eqb_eq id _)).
        pose proof (Hcounts x id) as Hcount.
        rewrite Horig, Hlive in Hcount; rewrite Hcount.
        apply (proj2 (histogram_count_pos S.key_eqb key_eqb_true x _)); exact Hx. }
      pose proof (invalid_walk_bad_done p p' ch st x Hbad) as Hdone.
      pose proof (invalid_walk_processed p p' ch st x Hdone id Hbucket) as Hretired.
      rewrite snapshot_get_edit in Hget.
      destruct (invalid_bad (invalid_walk p p' ch st)) as [|y bad]
        eqn:Hbadlist; [unfold invalidate_keys in Hbad; rewrite Hbadlist in Hbad;
          contradiction|].
      pose proof (Hretired ss' Hget) as Hfalse; congruence.
    Qed.

    Lemma retired_edit_write_bad : forall p p' ch st id ss current x,
      Core.state_core st -> snapshot_get id st = Some ss ->
      snapshot_live ss = true ->
      snapshot_get id (edit p p' ch st) = Some current ->
      snapshot_live current = false -> In x (snapshot_writes ss) ->
      In x (invalidate_keys p p' ch st).
    Proof.
      intros p p' ch st id ss current x Hcore Horig Hlive Hget Hretired Hx.
      destruct Hcore as [_ [_ [_ [Hstored _]]]].
      rewrite snapshot_get_edit in Hget.
      destruct (invalid_walk p p' ch st) as [pending seen bad done snapshots]
        eqn:Hwalk; destruct bad as [|y bad].
      - rewrite Horig in Hget; inversion Hget; subst; congruence.
      - pose proof (invalid_walk_snapshot_view p p' ch st id ss Horig Hlive)
          as Hview.
        rewrite Hwalk in Hview.
        destruct Hview as [view [Hview [Hwrites Hbad]]].
        cbn [invalid_bad invalid_snapshots] in Hget, Hview.
        rewrite Hget in Hview; inversion Hview; subst view.
        unfold invalidate_keys; rewrite Hwalk.
        apply (Hbad Hretired x Hx).
        now apply (proj2 (present_spec st x)), (Hstored id ss Horig Hlive x Hx).
    Qed.

    Lemma snapshot_get_edit_core : forall p p' ch st id,
      Core.state_core st ->
      snapshot_get id (edit p p' ch st) =
        option_map (retire_snapshot (invalidate_keys p p' ch st)) (snapshot_get id st).
    Proof.
      intros p p' ch st id Hcore.
      destruct (snapshot_get id st) as [ss|] eqn:Horig.
      - destruct (snapshot_get_edit_support p p' ch st id ss Horig)
          as [current Hget].
        destruct (snapshot_get_edit_inv p p' ch st id current Hget) as
          [original [Hbefore [Howner [Hwrites Horiglive]]]].
        rewrite Horig in Hbefore; inversion Hbefore; subst original.
        rewrite Hget; cbn [option_map].
        destruct ss as [owner writes live], current as [owner' writes' live'];
          cbn [snapshot_owner snapshot_writes snapshot_live] in *.
        subst owner' writes'.
        unfold retire_snapshot; cbn [snapshot_owner snapshot_writes snapshot_live].
        destruct live eqn:Hold, live' eqn:Hnew; cbn.
        + assert (Hnone : existsb
            (fun x => mem x (invalidate_keys p p' ch st)) writes = false).
          { apply Bool.not_true_iff_false; intro Htouch.
            apply existsb_exists in Htouch as [x [Hx Hbad]].
            apply (live_edit_write_kept p p' ch st id
              {| snapshot_owner := owner; snapshot_writes := writes;
                 snapshot_live := true |} x Hcore Hget eq_refl Hx).
            now apply (proj1 (mem_spec x _)) in Hbad. }
          rewrite Hnone; reflexivity.
        + assert (Htouch : existsb
            (fun x => mem x (invalidate_keys p p' ch st)) writes = true).
          { apply existsb_exists.
          assert (Hin : In owner writes).
          { destruct Hcore as [_ [Howner_core _]].
            exact (proj2 (Howner_core id
              {| snapshot_owner := owner; snapshot_writes := writes;
                 snapshot_live := true |} Horig)). }
            exists owner; split; [exact Hin|].
            apply (proj2 (mem_spec owner _)).
            eapply retired_edit_write_bad;
              [exact Hcore|exact Horig|reflexivity|exact Hget|reflexivity|exact Hin]. }
          rewrite Htouch; reflexivity.
        + exfalso; specialize (Horiglive eq_refl); discriminate.
        + reflexivity.
      - destruct (snapshot_get id (edit p p' ch st)) as [current|] eqn:Hget;
          [|reflexivity].
        destruct (snapshot_get_edit_inv p p' ch st id current Hget)
          as [ss [Hbefore _]].
        rewrite Horig in Hbefore; discriminate.
    Qed.

    Lemma snapshots_edit_perm : forall p p' ch st, Core.state_core st ->
      Permutation (snapshots (edit p p' ch st))
        (map (fun entry =>
          (fst entry, retire_snapshot (invalidate_keys p p' ch st) (snd entry)))
          (snapshots st)).
    Proof.
      intros p p' ch st Hcore.
      assert (Hmap : inc_snapshots (edit p p' ch st) =
        PTrieCode.map (retire_snapshot (invalidate_keys p p' ch st))
          (inc_snapshots st)).
      { apply PTrie.ext; intro id.
        change (snapshot_get id (edit p p' ch st) =
          PTrieCode.get id (PTrieCode.map
            (retire_snapshot (invalidate_keys p p' ch st)) (inc_snapshots st))).
        rewrite PTrie.get_map.
        apply snapshot_get_edit_core; exact Hcore. }
      unfold snapshots; rewrite Hmap; apply trie_map_elements_perm.
    Qed.

    (** Editing preserves the five independent representation fields. *)
    Lemma state_core_edit : forall p p' ch st,
      Core.state_core st -> Core.state_core (edit p p' ch st).
    Proof.
      intros p p' ch st Hcore.
      pose proof Hcore as [Hcanonical [Howner [Hrefs [Hlive Hcounts]]]].
      unfold Core.state_core; split.
      - unfold edit; destruct (invalid_walk p p' ch st)
          as [pending seen bad0 done snapshots].
        destruct bad0 as [|x bad]; cbn [inc_values].
        + exact Hcanonical.
        + apply InvFacts.remove_keys_canonical; exact Hcanonical.
      - split.
        + intros id ss' Hget.
          apply snapshot_get_edit_inv in Hget as
            [ss [Hget [Howner_eq [Hwrites_eq Hlive_eq]]]].
          destruct (Howner id ss Hget) as [Hid Hin]; split.
          * now rewrite Howner_eq.
          * now rewrite Howner_eq, Hwrites_eq.
        + split.
          * intros x id Hin; rewrite edit_infl_eq in Hin.
            destruct (mem x (invalidate_keys p p' ch st)); [contradiction|].
            destruct (Hrefs x id Hin) as [ss Hget].
            exact (snapshot_get_edit_support p p' ch st id ss Hget).
          * split.
            -- intros id ss' Hget Hactive x Hx.
               destruct (snapshot_get_edit_inv p p' ch st id ss' Hget) as
                 [ss [Horig [_ [Hwrites Horiglive]]]].
               apply (proj2 (edit_dom_keys p p' ch st x)); split.
               ++ rewrite Hwrites in Hx.
                  exact (Hlive id ss Horig (Horiglive Hactive) x Hx).
               ++ exact (live_edit_write_kept p p' ch st id ss' x
                    Hcore Hget Hactive Hx).
            -- intros x id; rewrite edit_cowrite_eq,
                 (snapshot_get_edit_core p p' ch st id Hcore).
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
          rewrite (snapshot_get_edit_core p p' ch st id Hcore), Hget in Hnew;
            cbn [option_map] in Hnew.
          injection Hnew as <-; cbn [retire_snapshot snapshot_live].
          rewrite Hlive, Htouch; reflexivity.
    Qed.

    (** Snapshot retirement never increases the live occurrence total. *)
    Lemma snapshot_mass_edit_le : forall p p' ch st, Core.state_core st ->
      snapshot_mass (edit p p' ch st) <= snapshot_mass st.
    Proof.
      intros p p' ch st Hcore; unfold snapshot_mass; rewrite !finite_fold_choice.
      rewrite (finite_sum_perm _ _ _ _ (snapshots_edit_perm p p' ch st Hcore)), finite_sum_map.
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
      pose proof (snapshot_mass_edit_le p p' ch st (Core.state_ok_core st Hstate))
        as Hsnap.
      change (finite_sum (fun x => infl_deg (edit p p' ch st) x + 1)
        (stored (edit p p' ch st)) + snapshot_mass (edit p p' ch st) +
        finite_sum (fun x => infl_deg st x + 1) (invalidate_keys p p' ch st) <=
        finite_sum (fun x => infl_deg st x + 1) (stored st) + snapshot_mass st).
      rewrite Hretained; lia.
    Qed.
  End EditMetadata.

  Module DemandAccounting.
    Definition snapshot_weight (ss : incremental_snapshot S.key) : nat :=
      if snapshot_live ss then length (snapshot_writes ss) else 0.

    (** The public live snapshot mass is the weighted raw trie inventory. *)
    Lemma snapshot_mass_sum : forall st,
      snapshot_mass st = trie_sum snapshot_weight (inc_snapshots st).
    Proof.
      intro st; unfold snapshot_mass, snapshots, trie_sum, finite_sum.
      induction (PTrieCode.elements (inc_snapshots st)) as [|[id ss] rest IH].
      - reflexivity.
      - cbn [map fold_right snd]; rewrite IH; unfold snapshot_weight.
        destruct (snapshot_live ss); reflexivity.
    Qed.

    (** Recording a snapshot adds exactly its new write occurrences to the live mass. *)
    Lemma snapshot_record_mass : forall owner writes st,
      snapshot_mass (snapshot_record owner writes st) =
        snapshot_mass st + length writes.
    Proof.
      intros owner writes st; rewrite !snapshot_mass_sum.
      unfold snapshot_record, snapshot_set, snapshot_get; cbn [inc_snapshots].
      pose proof (trie_sum_set _ snapshot_weight (S.key_code owner)
        {| snapshot_owner := owner;
           snapshot_writes := writes ++
             match PTrieCode.get (S.key_code owner) (inc_snapshots st) with
             | Some ss => if snapshot_live ss then snapshot_writes ss else []
             | None => []
             end;
           snapshot_live := true |} (inc_snapshots st)) as Hsum.
      cbn [snapshot_weight snapshot_live snapshot_writes] in Hsum.
      rewrite length_app in Hsum.
      destruct (PTrieCode.get (S.key_code owner) (inc_snapshots st)) as [ss|] eqn:Hget.
      - destruct (snapshot_live ss) eqn:Hlive.
        all: change (snapshot_weight ss) with
          (if snapshot_live ss then length (snapshot_writes ss) else 0) in Hsum.
        all: rewrite Hlive in Hsum; cbn [length] in Hsum; lia.
      - cbn [length] in Hsum; lia.
    Qed.

    (** A recorded snapshot retains only old keys and its newly supplied writes. *)
    Lemma snapshot_record_keys : forall owner writes st x,
      In x (snapshot_keys (snapshot_record owner writes st)) ->
        In x (snapshot_keys st) \/ In x writes.
    Proof.
      intros owner writes st x Hin; unfold snapshot_keys, snapshots in *.
      apply in_flat_map in Hin as [[id ss] [Hentry Hx]]; cbn [snd] in Hx.
      apply PTrie.elements_spec in Hentry.
      unfold snapshot_record, snapshot_set, snapshot_get in Hentry.
      cbn [inc_snapshots] in Hentry.
      destruct (Pos.eq_dec id (S.key_code owner)) as [->|Hneq].
      - rewrite PTrie.get_set_same in Hentry; injection Hentry as <-.
        cbn [snapshot_writes] in Hx; apply in_app_iff in Hx as [Hx|Hx]; [now right|].
        destruct (PTrieCode.get (S.key_code owner) (inc_snapshots st)) as [old|] eqn:Hold;
          [|contradiction].
        destruct (snapshot_live old); [|contradiction].
        left; apply in_flat_map; exists (S.key_code owner, old); split; [|exact Hx].
        now apply PTrie.elements_spec.
      - rewrite PTrie.get_set_other in Hentry by exact Hneq.
        left; apply in_flat_map; exists (id, ss); split; [|exact Hx].
        now apply PTrie.elements_spec.
    Qed.

    (** Recording a row adds precisely its declared write occurrences to snapshot mass. *)
    Lemma record_row_mass : forall p r st,
      snapshot_mass (record_row p r st) = snapshot_mass st + length (S.writes p r).
    Proof.
      intros p r st; change (snapshot_mass
        (snapshot_record (S.target p r) (row_writes p r) st) =
        snapshot_mass st + length (S.writes p r)).
      rewrite snapshot_record_mass; reflexivity.
    Qed.

    (** Recording rows adds their declared write lengths without duplicating prior mass. *)
    Lemma record_rows_mass : forall p rs st,
      snapshot_mass (record_rows p rs st) = snapshot_mass st +
        finite_sum (fun r => length (S.writes p r)) rs.
    Proof.
      intros p rs; induction rs as [|r rest IH]; intro st.
      - cbn [record_rows fold_left finite_sum map fold_right]; lia.
      - change (snapshot_mass (record_rows p rest (record_row p r st)) =
          snapshot_mass st +
            (length (S.writes p r) + finite_sum (fun row => length (S.writes p row)) rest)).
        rewrite IH, record_row_mass; lia.
    Qed.

    (** Every snapshot key newly retained by a row list occurs in one of its declared writes. *)
    Lemma record_rows_keys : forall p rs st x,
      In x (snapshot_keys (record_rows p rs st)) ->
      In x (snapshot_keys st) \/ exists r, In r rs /\ In x (S.writes p r).
    Proof.
      intros p rs; induction rs as [|r rest IH]; intros st x Hin.
      - now left.
      - change (In x (snapshot_keys (record_rows p rest (record_row p r st)))) in Hin.
        apply IH in Hin as [Hin|[row [Hrow Hx]]].
        + change (In x (snapshot_keys
            (snapshot_record (S.target p r) (row_writes p r) st))) in Hin.
          apply snapshot_record_keys in Hin as [Hin|Hin]; [now left|].
          right; exists r; split; [now left|exact Hin].
        + right; exists row; split; [now right|exact Hx].
    Qed.

    (** Every demand returns its old state or the checked finalization of its discovered region. *)
    Lemma demand_state_cases : forall p pol roots fuel st o st',
      demand p pol roots fuel st = (o, st') -> st' = st \/
      exists ks rs fz m, discovery p roots fuel st = Some (ks, rs, fz) /\
        st' = finish_demand p st ks rs m.
    Proof.
      intros p pol roots fuel st o st' Hrun; unfold demand in Hrun.
      destruct (forallb (present st) roots); [inversion Hrun; subst; now left|].
      destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
        [|inversion Hrun; subst; now left].
      destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why].
      - destruct (Checker.check_rows p rs (restore fz m)).
        + inversion Hrun; subst; right.
          exists ks, rs, fz, (restore fz m); split; reflexivity.
        + inversion Hrun; subst; now left.
      - inversion Hrun; subst; now left.
      - inversion Hrun; subst; now left.
    Qed.

    (** Finalization changes the raw value map only by filling. *)
    Lemma finish_values : forall p st xs rs m,
      inc_values (finish_demand p st xs rs m) = fill xs m (inc_values st).
    Proof.
      intros p st xs rs m; unfold finish_demand; rewrite Buckets.record_rows_values.
      exact (DemandState.prepared_values st xs m).
    Qed.

    (** Every final stored key is new or survives canonicalization of the old map. *)
    Lemma finish_stored_keys : forall p st xs rs m x,
      In x (stored (finish_demand p st xs rs m)) <->
        In x xs \/ In x (stored st).
    Proof.
      intros p st xs rs m x; unfold stored; rewrite finish_values.
      apply Inventory.valid_keys_fill.
    Qed.

    (** The repaired and filled value map has a duplicate-free key inventory. *)
    Lemma finish_stored_nodup : forall p st xs rs m,
      NoDup (stored (finish_demand p st xs rs m)).
    Proof.
      intros p st xs rs m; unfold stored; rewrite finish_values.
      apply Inventory.valid_keys_nodup.
    Qed.

    (** Canonicalization keeps only payload keys already counted in the old inventory. *)
    Lemma canonical_keys_old : forall st x,
      In x (stored st) -> In x (stored st).
    Proof.
      auto.
    Qed.

    (** Finalization adds at most one stored key per supplied key occurrence. *)
    Lemma finish_stored_length : forall p st xs rs m,
      length (stored (finish_demand p st xs rs m)) <= length (stored st) + length xs.
    Proof.
      intros p st xs rs m.
      assert (Hincl : incl (stored (finish_demand p st xs rs m)) (xs ++ stored st)).
      { intros x Hx; apply finish_stored_keys in Hx; apply in_app_iff.
        destruct Hx as [Hx|Hx]; [now left|now right]. }
      pose proof (finite_sum_incl_nodup _ (fun _ => 1) _ _
        (finish_stored_nodup p st xs rs m) Hincl) as Hsum.
      rewrite !finite_sum_one, length_app in Hsum; lia.
    Qed.

    Definition bucket_mass (keys : list S.key) (buckets : PTrieCode.t (list positive)) : nat :=
      finite_sum (fun x => length (Buckets.bucket_at buckets x)) keys.

    Definition influence_sum (st : state) : nat :=
      bucket_mass (stored st) (inc_influence st).

    (** One bucket push increases a duplicate-free support's mass by at most one. *)
    Lemma push_entry_mass : forall keys y id buckets, NoDup keys ->
      bucket_mass keys (push_entry y id buckets) <= bucket_mass keys buckets + 1.
    Proof.
      intros keys y id buckets Hnodup.
      assert (Hunit : finite_sum (fun x => if S.key_eqb x y then 1 else 0) keys <= 1).
      { destruct (mem y keys) eqn:Hmem.
        - apply mem_spec in Hmem.
          rewrite (histogram_unit_once S.key_eqb key_eqb_true keys y Hnodup Hmem); lia.
        - rewrite (histogram_unit_absent S.key_eqb key_eqb_true keys y); [lia|].
          intro Hin; pose proof (proj2 (mem_spec y keys) Hin) as Htrue.
          change (mem y keys = true) in Htrue; congruence. }
      unfold bucket_mass.
      eapply Nat.le_trans with (m := finite_sum
        (fun x => length (Buckets.bucket_at buckets x) + if S.key_eqb x y then 1 else 0) keys).
      - apply finite_sum_mono; intros x Hx; rewrite Buckets.push_entry_at.
        destruct (S.key_eqb x y); cbn [length]; lia.
      - rewrite finite_sum_plus; lia.
    Qed.

    (** A list of bucket pushes increases supported mass by at most its occurrence length. *)
    Lemma push_entries_mass : forall keys ys id buckets, NoDup keys ->
      bucket_mass keys (fold_left (fun acc x => push_entry x id acc) ys buckets) <=
        bucket_mass keys buckets + length ys.
    Proof.
      intros keys ys; induction ys as [|y rest IH]; intros id buckets Hnodup.
      - cbn [fold_left length]; lia.
      - cbn [fold_left length].
        pose proof (IH id (push_entry y id buckets) Hnodup) as Hrest.
        pose proof (push_entry_mass keys y id buckets Hnodup) as Hhead; lia.
    Qed.

    (** Recording rows charges at most one influence entry for each dependency occurrence. *)
    Lemma record_rows_influence : forall p rs st keys, NoDup keys ->
      bucket_mass keys (inc_influence (record_rows p rs st)) <=
        bucket_mass keys (inc_influence st) + finite_sum (fun r => length (S.deps p r)) rs.
    Proof.
      intros p rs; induction rs as [|r rest IH]; intros st keys Hnodup.
      - cbn [record_rows fold_left finite_sum map fold_right]; lia.
      - change (bucket_mass keys (inc_influence (record_rows p rest (record_row p r st))) <=
          bucket_mass keys (inc_influence st) +
            (length (S.deps p r) + finite_sum (fun row => length (S.deps p row)) rest)).
        pose proof (IH (record_row p r st) keys Hnodup) as Hrest.
        pose proof (push_entries_mass keys (S.deps p r) (S.key_code (S.target p r))
          (inc_influence st) Hnodup) as Hhead.
        change (bucket_mass keys (inc_influence (record_row p r st)) <=
          bucket_mass keys (inc_influence st) + length (S.deps p r)) in Hhead.
        lia.
    Qed.

    (** Clearing new buckets zeros precisely the selected key buckets. *)
    Lemma bucket_at_remove : forall xs buckets x,
      Buckets.bucket_at (remove_buckets xs buckets) x =
        if mem x xs then [] else Buckets.bucket_at buckets x.
    Proof.
      intros xs buckets x; unfold Buckets.bucket_at.
      change (match PTrieCode.get (S.key_code x) (Inventory.Bindings.remove_keys xs buckets) with
        | Some entries => entries | None => [] end =
        if mem x xs then [] else
          match PTrieCode.get (S.key_code x) buckets with Some entries => entries | None => [] end).
      rewrite Inventory.raw_get_remove_keys.
      change (Inventory.Bindings.mem x xs) with (mem x xs).
      destruct (mem x xs); reflexivity.
    Qed.

    (** Clearing new keys cannot increase old counted bucket mass. *)
    Lemma prepared_influence : forall st xs m,
      bucket_mass (Inventory.valid_keys (fill xs m (inc_values st)))
        (remove_buckets xs (inc_influence st)) <= influence_sum st.
    Proof.
      intros st xs m.
      set (keys := Inventory.valid_keys (fill xs m (inc_values st))).
      assert (Hnodup : NoDup keys).
      { apply Inventory.valid_keys_nodup. }
      assert (Hclear : bucket_mass keys (remove_buckets xs (inc_influence st)) =
        finite_sum (fun x => if mem x xs then 0
          else length (Buckets.bucket_at (inc_influence st) x)) keys).
      { unfold bucket_mass; apply finite_sum_ext; intros x Hx; rewrite bucket_at_remove.
        destruct (mem x xs); reflexivity. }
      rewrite Hclear, finite_sum_filter_indicator; unfold influence_sum, bucket_mass.
      apply finite_sum_incl_nodup; [now apply NoDup_filter|].
      intros x Hx; apply filter_In in Hx as [Hx Hnot]; apply negb_true_iff in Hnot.
      unfold keys in Hx; apply (proj1 (Inventory.valid_keys_fill xs m _ x)) in Hx.
      destruct Hx as [Hx|Hx].
      - pose proof (proj2 (mem_spec x xs) Hx) as Htrue.
        change (mem x xs = true) in Htrue; congruence.
      - exact Hx.
    Qed.

    (** Recording metadata does not change the public raw stored-key inventory. *)
    Lemma record_rows_stored : forall p rs st,
      stored (record_rows p rs st) = stored st.
    Proof.
      intros p rs st; unfold stored; rewrite Buckets.record_rows_values; reflexivity.
    Qed.

    (** Finalization charges all influence growth to its dependency occurrences. *)
    Lemma finish_influence : forall p st xs rs m,
      influence_sum (finish_demand p st xs rs m) <= influence_sum st +
        finite_sum (fun r => length (S.deps p r)) rs.
    Proof.
      intros p st xs rs m; unfold finish_demand, influence_sum at 1.
      rewrite record_rows_stored.
      eapply Nat.le_trans.
      - apply record_rows_influence.
        change (NoDup (Inventory.valid_keys (fill_local xs m (inc_values st)))).
        rewrite fill_local_eq_fill.
        apply Inventory.valid_keys_nodup.
      - pose proof (prepared_influence st xs m) as Hbase.
        change (bucket_mass (Inventory.valid_keys (fill_local xs m (inc_values st)))
          (remove_buckets xs (inc_influence st)) +
          finite_sum (fun r => length (S.deps p r)) rs <=
          influence_sum st + finite_sum (fun r => length (S.deps p r)) rs).
        rewrite fill_local_eq_fill.
        lia.
    Qed.

    (** Every footprint selected during discovery appears in the final filtered region. *)
    Lemma discovery_selected_region : forall p roots st r,
      In r (footprint_selected (plan p roots st)) -> In r (discovery_region p roots st).
    Proof.
      intros p roots st r Hr; apply region_for_spec; split.
      - pose proof (footprint_close_partition S.key_eqb (row_writes p) (row_keys p)
          (missing st) (length (S.rows p)) (discovery_seed st roots)
          (S.rows p)) as Hpartition.
        change (Permutation (S.rows p) (footprint_selected (plan p roots st) ++
          footprint_pending (plan p roots st))) in Hpartition.
        eapply Permutation_in; [apply Permutation_sym; exact Hpartition|].
        apply in_app_iff; now left.
      - pose proof (footprint_close_selected S.key_eqb (row_writes p) (row_keys p)
          (missing st) key_eqb_true (length (S.rows p)) (discovery_seed st roots)
          (S.rows p) r Hr) as Hactive.
        apply (footprint_active_spec S.key_eqb (row_writes p) key_eqb_true) in Hactive.
        destruct Hactive as [x [Hx Hseen]]; exists x; repeat split; [exact Hx| |exact Hseen].
        eapply discovery_keys_missing; exact Hseen.
    Qed.

    (** Every discovered key is a root or a declared read or write of a discovered row. *)
    Lemma discovery_keys_provenance : forall p roots st x,
      In x (discovery_keys p roots st) -> In x roots \/
        exists r, In r (discovery_region p roots st) /\ In x (row_keys p r).
    Proof.
      intros p roots st x Hx.
      apply (footprint_close_provenance S.key_eqb (row_writes p) (row_keys p)
        (missing st) key_eqb_true (length (S.rows p)) (discovery_seed st roots)
        (S.rows p)) in Hx.
      destruct Hx as [Hx|[r [Hr [Hx Hmissing]]]].
      - left; apply discovery_seed_spec in Hx; tauto.
      - right; exists r; split; [now apply discovery_selected_region|exact Hx].
    Qed.

    (** Discovery accumulates each key at most once. *)
    Lemma discovery_keys_nodup : forall p roots st, NoDup (discovery_keys p roots st).
    Proof.
      intros p roots st; unfold discovery_keys, plan, footprint_run.
      apply (footprint_close_nodup S.key_eqb (row_writes p) (row_keys p)
        (missing st) key_eqb_true).
      unfold discovery_seed; apply (footprint_adds_nodup S.key_eqb (missing st)
        key_eqb_true); constructor.
    Qed.

    (** Roots and discovered row occurrences pay for every accumulated key. *)
    Lemma discovery_keys_length : forall p roots st,
      length (discovery_keys p roots st) <= length roots +
        finite_sum (fun r => length (S.deps p r)) (discovery_region p roots st) +
        finite_sum (fun r => length (S.writes p r)) (discovery_region p roots st).
    Proof.
      intros p roots st.
      assert (Hincl : incl (discovery_keys p roots st)
        (roots ++ flat_map (row_keys p) (discovery_region p roots st))).
      { intros x Hx; apply discovery_keys_provenance in Hx; apply in_app_iff.
        destruct Hx as [Hx|[r [Hr Hx]]]; [now left|].
        right; apply in_flat_map; exists r; auto. }
      pose proof (finite_sum_incl_nodup _ (fun _ => 1) _ _
        (discovery_keys_nodup p roots st) Hincl) as Hlength.
      rewrite !finite_sum_one, length_app, finite_flat_map_length in Hlength.
      assert (Hrows : finite_sum (fun r => length (row_keys p r))
          (discovery_region p roots st) =
        finite_sum (fun r => length (S.deps p r)) (discovery_region p roots st) +
        finite_sum (fun r => length (S.writes p r)) (discovery_region p roots st)).
      { rewrite <- finite_sum_plus; apply finite_sum_ext; intros r Hr.
        change (length (S.writes p r ++ S.deps p r) =
          length (S.deps p r) + length (S.writes p r)).
        rewrite length_app; lia. }
      lia.
    Qed.

    (** A demand records snapshot keys only from its discovered rows. *)
    Lemma snapshot_keys_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
      demand p pol roots fuel st = (o, st') -> forall x, In x (snapshot_keys st') ->
      In x (snapshot_keys st) \/ exists r, In r (region p roots st) /\ In x (S.writes p r).
    Proof.
      intros p pol roots fuel st o st' Hwf Hinv Hrun x Hx.
      apply demand_state_cases in Hrun as [->|[ks [rs [fz [m [Hdiscovery ->]]]]]];
        [now left|].
      pose proof (proj1 (proj2
        (discovery_result_view_projection p roots fuel st ks rs fz Hwf Hdiscovery)))
        as Hregion.
      unfold finish_demand in Hx; apply record_rows_keys in Hx as [Hold|[r [Hr Hwrite]]].
      - now left.
      - right; exists r; split; [now rewrite <- Hregion|exact Hwrite].
    Qed.

    (** Demand counts stay within roots, dependency occurrences and shared write occurrences. *)
    Lemma demand_record_counts : forall p pol roots fuel st o st', S.wf p -> inv p st ->
      demand p pol roots fuel st = (o, st') ->
      let reads := fold_right Nat.add 0 (map (fun r => length (S.deps p r)) (region p roots st)) in
      let writes := fold_right Nat.add 0
        (map (fun r => length (S.writes p r)) (region p roots st)) in
      length (stored st') <= length (stored st) + length roots + reads + writes /\
      fold_right Nat.add 0 (map (fun x => length (infl_at st' x)) (stored st')) <=
        fold_right Nat.add 0 (map (fun x => length (infl_at st x)) (stored st)) + reads /\
      snapshot_mass st' <= snapshot_mass st + writes.
    Proof.
      intros p pol roots fuel st o st' Hwf Hinv Hrun; cbv zeta.
      change (length (stored st') <= length (stored st) + length roots +
        finite_sum (fun r => length (S.deps p r)) (region p roots st) +
        finite_sum (fun r => length (S.writes p r)) (region p roots st) /\
        influence_sum st' <= influence_sum st +
          finite_sum (fun r => length (S.deps p r)) (region p roots st) /\
        snapshot_mass st' <= snapshot_mass st +
          finite_sum (fun r => length (S.writes p r)) (region p roots st)).
      apply demand_state_cases in Hrun as [->|[ks [rs [fz [m [Hdiscovery ->]]]]]];
        [repeat split; lia|].
      pose proof (discovery_result_view_rows p roots fuel st ks rs fz Hwf Hdiscovery)
        as Hregion.
      split.
      - pose proof (finish_stored_length p st ks rs m) as Hstored.
        pose proof (discovery_result_keys_length p roots fuel st ks rs fz Hdiscovery)
          as Hkeys.
        rewrite Hregion in Hkeys.
        eapply Nat.le_trans; [exact Hstored|].
        unfold finite_sum; lia.
      - split.
        + pose proof (finish_influence p st ks rs m) as Hinfluence.
          rewrite <- Hregion; exact Hinfluence.
        + unfold finish_demand; rewrite record_rows_mass.
          rewrite <- Hregion; apply Nat.le_refl.
    Qed.

    (** Stored demand keys come from the previous inventory, roots, or discovered row supports. *)
    Lemma demand_stored_provenance : forall p pol roots fuel st o st',
      S.wf p -> demand p pol roots fuel st = (o, st') ->
      forall x, In x (stored st') ->
      In x (stored st) \/ In x roots \/
        exists r, In r (region p roots st) /\ In x (row_keys p r).
    Proof.
      intros p pol roots fuel st o st' Hwf Hrun x Hx.
      apply demand_state_cases in Hrun as [->|[ks [rs [fz [m [Hdiscovery ->]]]]]];
        [now left|].
      apply finish_stored_keys in Hx as [Hx|Hx].
      - right.
        destruct (discovery_result_source p roots fuel st ks rs fz x Hdiscovery Hx)
          as [Hroot|[r [Hr Hkey]]]; [now left|right].
        exists r; split; [|exact Hkey].
        rewrite <- (discovery_result_view_rows p roots fuel st ks rs fz Hwf Hdiscovery).
        exact Hr.
      - left; now apply canonical_keys_old.
    Qed.

    (** The root width budget includes its program seed. *)
    Lemma roots_budget_base : forall p roots,
      S.kw p <= fold_right Nat.max (S.kw p) (map S.key_bits roots).
    Proof.
      intros p roots; induction roots as [|x roots IH]; cbn [map fold_right]; [lia|].
      eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
    Qed.

    (** Each root fits the root width budget. *)
    Lemma roots_budget_member : forall p roots x, In x roots ->
      S.key_bits x <= fold_right Nat.max (S.kw p) (map S.key_bits roots).
    Proof.
      intros p roots; induction roots as [|y roots IH]; intros x Hx; [contradiction|].
      cbn [map fold_right]; destruct Hx as [->|Hx]; [apply Nat.le_max_l|].
      eapply Nat.le_trans; [apply IH; exact Hx|apply Nat.le_max_r].
    Qed.

    (** Old inventory keys, roots and declared region keys fit the next width bound. *)
    Lemma demand_key_bound : forall p roots st x, S.wf p ->
      (In x (stored st ++ snapshot_keys st) \/ In x roots \/
        exists r, In r (region p roots st) /\ In x (row_keys p r)) ->
      S.key_bits x <= Nat.max (kwidth st)
        (fold_right Nat.max (S.kw p) (map S.key_bits roots)).
    Proof.
      intros p roots st x Hwf [Hold|[Hroot|[r [Hr Hx]]]].
      - eapply Nat.le_trans; [apply finite_max_member; exact Hold|apply Nat.le_max_l].
      - eapply Nat.le_trans; [apply roots_budget_member; exact Hroot|apply Nat.le_max_r].
      - eapply Nat.le_trans; [eapply S.key_bits_le; [exact Hwf| |exact Hx]|].
        + now apply region_rows in Hr.
        + eapply Nat.le_trans; [apply roots_budget_base|apply Nat.le_max_r].
    Qed.

    (** Demand widens the raw inventory only to program keys and explicit roots. *)
    Lemma kwidth_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
      demand p pol roots fuel st = (o, st') ->
      kwidth st' <= Nat.max (kwidth st)
        (fold_right Nat.max (S.kw p) (map S.key_bits roots)).
    Proof.
      intros p pol roots fuel st o st' Hwf Hinv Hrun.
      apply finite_max_bound; intros x Hx; apply demand_key_bound; [exact Hwf|].
      apply in_app_iff in Hx as [Hx|Hx].
      - apply (demand_stored_provenance p pol roots fuel st o st' Hwf Hrun) in Hx.
        destruct Hx as [Hx|Hx]; [left; apply in_app_iff; now left|now right].
      - apply (snapshot_keys_demand p pol roots fuel st o st' Hwf Hinv Hrun) in Hx.
        destruct Hx as [Hx|[r [Hr Hx]]].
        + left; apply in_app_iff; now right.
        + right; right; exists r; split; [exact Hr|].
          apply in_app_iff; now left.
    Qed.

    (** The three demand counters imply the public influence-mass growth bound. *)
    Lemma infl_mass_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
      demand p pol roots fuel st = (o, st') ->
      infl_mass st' <= infl_mass st + 2 * (length roots + fold_right Nat.add 0
        (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st))).
    Proof.
      intros p pol roots fuel st o st' Hwf Hinv Hrun.
      pose proof (demand_record_counts p pol roots fuel st o st' Hwf Hinv Hrun) as Hcounts.
      cbv zeta in Hcounts; destruct Hcounts as [Hstored [Hreads Hwrites]].
      assert (Hcharge : finite_sum
        (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st) =
        finite_sum (fun r => length (S.deps p r)) (region p roots st) +
        finite_sum (fun r => length (S.writes p r)) (region p roots st)).
      { rewrite <- finite_sum_plus; apply finite_sum_ext; intros r Hr.
        change (length (S.deps p r) + length (S.sides p r) + 1 =
          length (S.deps p r) + S (length (S.sides p r))); lia. }
      unfold infl_mass.
      change (finite_sum (fun x => infl_deg st' x + 1) (stored st') + snapshot_mass st' <=
        finite_sum (fun x => infl_deg st x + 1) (stored st) + snapshot_mass st +
        2 * (length roots + finite_sum
          (fun r => length (S.deps p r) + length (S.sides p r) + 1) (region p roots st))).
      rewrite Hcharge, !finite_sum_plus, !finite_sum_one.
      unfold finite_sum, infl_deg in *; lia.
    Qed.
  End DemandAccounting.

  Module DemandPlanProof.
    (** Covered roots contribute no missing discovery seed. *)
    Lemma covered_seed_empty : forall st roots,
      forallb (present st) roots = true -> discovery_seed st roots = [].
    Proof.
      intros st roots Hcovered.
      destruct (discovery_seed st roots) as [|x rest] eqn:Hseed; [reflexivity|].
      exfalso; assert (Hx : In x (discovery_seed st roots)).
      { rewrite Hseed; now left. }
      apply discovery_seed_spec in Hx as [Hroot Hmissing].
      pose proof (proj1 (forallb_forall (present st) roots) Hcovered x Hroot) as Hpresent.
      unfold present in Hpresent; rewrite Hmissing in Hpresent; discriminate Hpresent.
    Qed.

    (** Covered roots discover no additional key. *)
    Lemma covered_keys_empty : forall p st roots,
      forallb (present st) roots = true -> discovery_keys p roots st = [].
    Proof.
      intros p st roots Hcovered; unfold discovery_keys, plan, footprint_run.
      rewrite covered_seed_empty by exact Hcovered; apply footprint_close_empty.
    Qed.

    (** Covered roots leave the selected region empty. *)
    Lemma covered_region_empty : forall p st roots,
      forallb (present st) roots = true -> region p roots st = [].
    Proof.
      intros p st roots Hcovered.
      assert (Hinitial : forall xs acc, forallb (present st) xs = true ->
        fold_left (discovery_seed_one st) xs acc = acc).
      { intros xs; induction xs as [|x rest IH]; intros acc Hxs; [reflexivity|].
        cbn [forallb fold_left] in *; apply andb_true_iff in Hxs as [Hx Hrest].
        unfold discovery_seed_one, missing; rewrite Hx; cbn [negb].
        apply IH; exact Hrest. }
      unfold region, discovery_view, discovery.
      rewrite (Hinitial roots empty_discovery Hcovered), incremental_loopN_fuel.
      unfold view_fuel; rewrite Nat2N.id.
      reflexivity.
    Qed.

    (** Completed demands expose a checked candidate for their discovered region. *)
    Lemma demand_certificate : forall p pol roots fuel st st', S.wf p -> inv p st ->
      demand p pol roots fuel st = (Done, st') ->
      exists m, Checker.check_rows p (region p roots st) m = true.
    Proof.
      intros p pol roots fuel st st' Hwf Hinv Hrun; unfold demand in Hrun.
      destruct (forallb (present st) roots) eqn:Hcovered.
      - rewrite (covered_region_empty p st roots Hcovered).
        exists (@PTrieCode.empty (S.key * L.t)).
        apply (proj2 (Checker.check_rows_iff p [] _)); intros r Hr; contradiction.
      - destruct (discovery p roots fuel st) as [[[ks rs] fz]|] eqn:Hdiscovery;
          [|discriminate Hrun].
        destruct (Sol.run (R.mk p fz rs) pol fuel) as [m|m|why];
          [|discriminate Hrun|discriminate Hrun].
        destruct (Checker.check_rows p rs (restore fz m)) eqn:Hcheck;
          [|discriminate Hrun].
        rewrite (discovery_result_view_rows p roots fuel st ks rs fz Hwf Hdiscovery)
          in Hcheck.
        exists (restore fz m); exact Hcheck.
    Qed.

    (** Freezing a duplicate-free source list preserves distinct payload keys. *)
    Lemma freeze_values_nodup : forall st xs, NoDup xs ->
      NoDup (map fst (freeze_values st xs)).
    Proof.
      intros st xs Hnodup; induction Hnodup as [|x xs Habsent Hnodup IH].
      - cbn [freeze_values flat_map map]; constructor.
      - cbn [freeze_values flat_map].
        destruct (value st x) as [v|]; cbn [app map fst]; [|exact IH].
        constructor; [|exact IH].
        intro Hin; apply in_map_iff in Hin as [[y w] [Heq Hin]]; cbn [fst] in Heq; subst y.
        apply Habsent; apply freeze_values_spec in Hin; tauto.
    Qed.

    (** Frozen keys are unique and each has a seen mark. *)
    Definition frozen_unique (acc : incremental_discovery S.key S.row L.t) : Prop :=
      NoDup (map fst (discovery_frozen acc)) /\
      forall x, In x (map fst (discovery_frozen acc)) ->
        PTrieCode.get (S.key_code x) (discovery_seen acc) = Some tt.

    Lemma discovery_visit_frozen_unique : forall st x acc,
      frozen_unique acc -> frozen_unique (discovery_visit st x acc).
    Proof.
      intros st x acc [Hnodup Hseen]; unfold discovery_visit.
      destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|]
        eqn:Hx; [now split|].
      destruct (value st x) as [v|]; cbn [discovery_frozen discovery_seen map].
      - split.
        + constructor; [|exact Hnodup].
          intro Hin; rewrite (Hseen x Hin) in Hx; discriminate.
        + intros y [<-|Hy]; [apply PTrie.get_set_same|].
          assert (Hneq : S.key_code y <> S.key_code x).
          { intro Heq; pose proof (Hseen y Hy) as Hget.
            rewrite Heq in Hget; congruence. }
          cbn [discovery_seen]; rewrite PTrie.get_set_other by exact Hneq.
          now apply Hseen.
      - split; [exact Hnodup|].
        intros y Hy.
        assert (Hneq : S.key_code y <> S.key_code x).
        { intro Heq; pose proof (Hseen y Hy) as Hget.
          rewrite Heq in Hget; congruence. }
        cbn [discovery_seen]; rewrite PTrie.get_set_other by exact Hneq.
        now apply Hseen.
    Qed.

    Lemma discovery_seed_frozen_unique : forall st roots acc,
      frozen_unique acc ->
      frozen_unique (fold_left (discovery_seed_one st) roots acc).
    Proof.
      intros st roots; induction roots as [|x rest IH]; intros acc Hunique;
        [exact Hunique|].
      cbn [fold_left]; apply IH; unfold discovery_seed_one.
      destruct (missing st x); [now apply discovery_visit_frozen_unique|exact Hunique].
    Qed.

    Lemma discovery_row_frozen_unique : forall p st r acc,
      frozen_unique acc -> frozen_unique (discovery_row p st acc r).
    Proof.
      intros p st r acc Hunique; unfold discovery_row.
      cbn [discovery_frozen discovery_seen].
      assert (Hfold : forall xs current, frozen_unique current ->
        frozen_unique
          (fold_left (fun current x => discovery_visit st x current) xs current)).
      { intros xs; induction xs as [|x rest IH]; intros current Hcurrent;
          [exact Hcurrent|].
        cbn [fold_left]; apply IH; now apply discovery_visit_frozen_unique. }
      apply Hfold; exact Hunique.
    Qed.

    Lemma discovery_step_frozen_unique : forall p st acc next,
      frozen_unique acc -> discovery_step p st acc = inl next -> frozen_unique next.
    Proof.
      intros p st acc next Hunique Hstep; unfold discovery_step in Hstep.
      destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
        [discriminate Hstep|].
      inversion Hstep; subst next.
      assert (Hfold : forall rs current, frozen_unique current ->
        frozen_unique (fold_left (discovery_row p st) rs current)).
      { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
          [exact Hcurrent|].
        cbn [fold_left]; apply IH; now apply discovery_row_frozen_unique. }
      apply Hfold; unfold frozen_unique in *.
      cbn [discovery_frozen discovery_seen]; exact Hunique.
    Qed.

    (** The frozen boundary lists each key at most once. *)
    Lemma frozen_nodup : forall p roots st, NoDup (map fst (frozen p roots st)).
    Proof.
      intros p roots st; unfold frozen, discovery_view.
      rewrite discovery_rev_equation.
      set (initial := fold_left (discovery_seed_one st) roots empty_discovery).
      assert (Hinitial : frozen_unique initial).
      { unfold initial; apply discovery_seed_frozen_unique.
        unfold frozen_unique, empty_discovery; cbn [discovery_frozen map].
        split; [constructor|intros x Hx; contradiction]. }
      assert (Hstep : forall acc, frozen_unique acc ->
        match discovery_step p st acc with
        | inl next => frozen_unique next
        | inr finished => frozen_unique finished
        end).
      { intros acc Hunique; destruct (discovery_step p st acc) as [next|finished]
          eqn:Hnext; [eapply discovery_step_frozen_unique; eauto|].
        unfold discovery_step in Hnext.
        destruct (discovery_pending acc); [inversion Hnext; subst; exact Hunique|].
        discriminate Hnext. }
      pose proof (incremental_loopN_preserves (discovery_step p st)
        frozen_unique frozen_unique Hstep (view_fuel p roots) initial Hinitial) as Hunique.
      destruct (loopN (discovery_step p st) (view_fuel p roots) initial)
        as [remaining|finished]; [constructor|].
      cbn; rewrite map_rev; apply NoDup_rev; exact (proj1 Hunique).
    Qed.
  End DemandPlanProof.

  Definition row_recorded (p : S.prog) (st : state) : Prop :=
    forall r y, In r (S.rows p) -> In y (S.writes p r) -> dom st y ->
      exists ss, snapshot_get (S.key_code (S.target p r)) st = Some ss /\
        snapshot_live ss = true /\
        (forall w, In w (S.writes p r) -> In w (snapshot_writes ss) /\
          In (S.key_code (S.target p r)) (cowrite_at st w)) /\
        (forall x, In x (S.deps p r) ->
          In (S.key_code (S.target p r)) (infl_at st x)).

  Lemma row_recorded_init : forall p, row_recorded p init.
  Proof.
    intros p r y Hr Hy [v Hvalue]; rewrite value_init in Hvalue; discriminate Hvalue.
  Qed.

  Lemma row_recorded_finish : forall p st xs rs m,
    inv p st -> row_recorded p st ->
    (forall x, In x xs -> value st x = None) ->
    (forall r y, In r (S.rows p) -> In y (S.writes p r) -> In y xs -> In r rs) ->
    row_recorded p (finish_demand p st xs rs m).
  Proof.
    intros p st xs rs m [Hclosed Hpost] Hrecorded Hfresh Hselected r y Hr Hy Hdom.
    apply (proj1 (finish_demand_dom p st xs rs m y)) in Hdom as [Hold|Hnew].
    - destruct (Hrecorded r y Hr Hy Hold) as [ss [Hget [Hlive [Hwrites Hdeps]]]].
      apply DemandState.finish_group_preserves with (ss := ss); try assumption.
      intros x Hx; exact (Hclosed r y x Hr Hy Hold Hx).
    - unfold finish_demand.
      apply DemandState.record_rows_own.
      exact (Hselected r y Hr Hy Hnew).
  Qed.

  Lemma row_recorded_demand : forall p pol roots fuel st o st',
    S.wf p -> inv p st -> row_recorded p st ->
    demand p pol roots fuel st = (o, st') -> row_recorded p st'.
  Proof.
    intros p pol roots fuel st o st' Hwf Hinv Hrecorded Hrun.
    apply DemandAccounting.demand_state_cases in Hrun as
      [->|[ks [rs [fz [m [Hdiscovery ->]]]]]];
      [exact Hrecorded|].
    apply row_recorded_finish; [exact Hinv|exact Hrecorded| |].
    - exact (proj2 (discovery_result_missing p roots fuel st ks rs fz Hdiscovery)).
    - intros r y Hr Hy Hnew.
      eapply discovery_result_done_rows; [exact Hdiscovery|exact Hnew|].
      apply (proj2 (S.rows_of_spec p y r Hwf)); split; assumption.
  Qed.

  Lemma row_recorded_tracks : forall p st, row_recorded p st <-> tracks p st.
  Proof.
    intros p st; split; intros Hrecorded r y Hr Hy Hdom;
      exact (Hrecorded r y Hr Hy Hdom).
  Qed.

  Lemma row_recorded_edit : forall p p' ch st,
    edit_covers p p' ch -> inv p st -> row_recorded p st ->
    row_recorded p' (edit p p' ch st).
  Proof.
    intros p p' ch st Hcovers Hinv Hrecorded.
    apply row_recorded_tracks.
    eapply tracks_edit; [exact Hcovers|exact Hinv|].
    now apply row_recorded_tracks.
  Qed.

  Lemma tracks_row : forall p st r y, tracks p st -> In r (S.rows p) ->
    In y (S.writes p r) -> dom st y ->
    exists ss, In (S.key_code (S.target p r), ss) (snapshots st) /\
      snapshot_live ss = true /\
      (forall w, In w (S.writes p r) -> In w (snapshot_writes ss) /\
        In (S.key_code (S.target p r)) (cowrite_at st w)) /\
      (forall x, In x (S.deps p r) -> In (S.key_code (S.target p r)) (infl_at st x)).
  Proof.
    intros p st r y Htracks Hr Hy Hdom.
    destruct (Htracks r y Hr Hy Hdom) as [ss [Hget [Hlive [Hwrites Hdeps]]]].
    exists ss; split; [now apply Core.snapshot_get_elements|].
    split; [exact Hlive|]; split; [exact Hwrites|exact Hdeps].
  Qed.

  Lemma discover_nodup : forall p roots st, NoDup (discover p roots st).
  Proof.
    intros p roots st; unfold discover, discovery_view.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; [|constructor].
    cbn; exact (proj1 (discovery_result_missing p roots (view_fuel p roots)
      st ks rs fz Hrun)).
  Qed.

  Lemma discover_source : forall p roots st x, In x (discover p roots st) ->
    ~ dom st x /\
    (In x roots \/ exists r, In r (region p roots st) /\
      In x (S.writes p r ++ S.deps p r)).
  Proof.
    intros p roots st x Hx; unfold discover, discovery_view in Hx.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; cbn in Hx; [|contradiction].
    split.
    - intros [v Hv].
      pose proof (proj2 (discovery_result_missing p roots (view_fuel p roots)
        st ks rs fz Hrun) x Hx) as Hnone.
      rewrite Hnone in Hv; discriminate.
    - destruct (discovery_result_source p roots (view_fuel p roots)
        st ks rs fz x Hrun Hx) as [Hroot|[r [Hr Hkey]]];
        [now left|right].
      exists r; split; [|exact Hkey].
      unfold region, discovery_view; now rewrite Hrun.
  Qed.

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
  Definition c_inc : N := (1024 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1))%N.
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

  Lemma T_local_look_le : forall m x,
    (T_look_or S.key_code S.T_key_code L.bot m x <=
      (S.c_sys + PTrieT.c_trie + 2) * N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros m x.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (S.key * L.t) (S.key_code x) m) as Hget.
    unfold T_look_or, PTrieCode.T_get, S.key_bits in *.
    time_simpl; time_cbn; nia.
  Qed.

  Lemma T_fill_local_le : forall xs m base,
    (T_fill_local xs m base <= c_inc * N.of_nat
      (fold_right Nat.add 0%nat (map (fun x => S.key_bits x + 1)%nat xs)) + 1)%N.
  Proof.
    intros xs; induction xs as [|x rest IH]; intros m base.
    - time_unfold @T_fill_local; unfold c_inc; time_simpl; lia.
    - pose proof (S.T_key_code_le x) as Hcode.
      pose proof (T_local_look_le m x) as Hlook.
      pose proof (PTrieT.T_set_le (S.key * L.t) (S.key_code x)
        (x, look_or S.key_code L.bot m x) (fill_local rest m base)) as Hset.
      specialize (IH m base).
      time_unfold @T_fill_local; cbn [map fold_right].
      change (PTrieCode.T_set (S.key_code x)
        (x, look_or S.key_code L.bot m x) (fill_local rest m base)) with
        (PTrieT.T_set (S.key_code x)
          (x, look_or S.key_code L.bot m x) (fill_local rest m base)).
      change (T_look_or S.key_code (fun y : S.key => S.T_key_code y) L.bot m x) with
        (T_look_or S.key_code S.T_key_code L.bot m x).
      unfold c_inc, S.key_bits in *; time_simpl; time_cbn.
      rewrite !Nat2N.inj_add in *.
      nia.
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
      c_inc * N.of_nat (N.size_nat fuel) +
      c_inc * demand_solver_work p pol roots fuel st)%N.
  Proof.
    (* OPEN: the discovery and local finish clocks still need an amortized bound. *)
  Admitted.

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
  Proof.
    exact DemandAccounting.infl_mass_demand.
  Qed.
  (** Demand widens the state only to program keys and roots. *)
  Lemma kwidth_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    kwidth st' <= Nat.max (kwidth st) (fold_right Nat.max (S.kw p) (map S.key_bits roots)).
  Proof.
    exact DemandAccounting.kwidth_demand.
  Qed.
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
    (forall r, In r ch -> In r (S.rows p) /\ In r (S.rows p')) ->
    (T_edit p p' ch st <= c_inc *
      N.of_nat (((infl_mass st - infl_mass (edit p p' ch st)) +
        fold_right Nat.add 0%nat (map (fun r => length (S.writes p r) + length (S.writes p' r) +
          length (S.deps p r) + length (S.deps p' r) + 1) ch) + 1)%nat) *
      N.of_nat (width p st + width p' st + kwidth st + 1))%N.
  Proof.
    (* OPEN: the local edit clock still needs the released influence credit bound. *)
  Admitted.

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
    intros st id ss [_ [_ [_ [_ [_ [_ [_ [Hwidth Hcanonical]]]]]]]] Hin.
    exact (Hwidth id ss Hin).
  Qed.
  (** Demands record write occurrences only from their discovered rows. *)
  Lemma snapshot_keys_demand : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') -> forall x, In x (snapshot_keys st') ->
    In x (snapshot_keys st) \/ exists r, In r (region p roots st) /\ In x (S.writes p r).
  Proof.
    exact DemandAccounting.snapshot_keys_demand.
  Qed.
  (** Demand records keys, read entries and shared write occurrences within their exact charges. *)
  Lemma demand_record_counts : forall p pol roots fuel st o st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (o, st') ->
    let reads := fold_right Nat.add 0 (map (fun r => length (S.deps p r)) (region p roots st)) in
    let writes := fold_right Nat.add 0 (map (fun r => length (S.writes p r)) (region p roots st)) in
    length (stored st') <= length (stored st) + length roots + reads + writes /\
    fold_right Nat.add 0 (map (fun x => length (infl_at st' x)) (stored st')) <=
      fold_right Nat.add 0 (map (fun x => length (infl_at st x)) (stored st)) + reads /\
    snapshot_mass st' <= snapshot_mass st + writes.
  Proof.
    exact DemandAccounting.demand_record_counts.
  Qed.
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
    intros p roots st r x Hinv Hr Hx.
    unfold region, discovery_view in Hr.
    unfold discover, discovery_view.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; cbn in Hr |- *; [|contradiction].
    eapply discovery_result_support; eauto.
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
    intros p roots st m Hwf [Hclosed Hpost] Hcheck Hagree.
    unfold merge_region.
    assert (Hmissing : forall x, In x (discover p roots st) -> value st x = None).
    { intros x Hx; destruct (value st x) as [v|] eqn:Hvalue; [|reflexivity].
      exfalso; apply (proj1 (discover_source p roots st x Hx)); exists v; exact Hvalue. }
    split.
    - intros r y x Hr Hy Hdom Hx.
      apply (proj2 (merge_dom st _ m x)).
      eapply (discover_closed p roots st Hwf (conj Hclosed Hpost));
        [exact Hr|exact Hy| |exact Hx].
      apply (proj1 (merge_dom st _ m y)); exact Hdom.
    - intros r y Hr Hy Hdom.
      destruct (value st y) as [v|] eqn:Hvalue.
      + assert (Hold : dom st y) by (exists v; exact Hvalue).
        assert (Hrow :
          row_ok L.leb (look (merge_discovered st (discover p roots st) m))
            (S.target p r)
            (S.eval p r (look (merge_discovered st (discover p roots st) m))) =
          row_ok L.leb (look st) (S.target p r) (S.eval p r (look st))).
        { apply row_look_transport; [exact Hwf|exact Hr|].
          intros x Hx; apply merge_old_look; [exact Hmissing|].
          eapply Hclosed; eauto. }
        rewrite Hrow; eapply Hpost; eauto.
      + assert (Hnew : In y (discover p roots st)).
        { apply (proj1 (merge_dom st _ m y)) in Hdom.
          destruct Hdom as [[w Hw]|Hin]; [rewrite Hvalue in Hw; discriminate Hw|exact Hin]. }
        assert (Hregion : In r (region p roots st)).
        { unfold discover, discovery_view in Hnew.
          unfold region, discovery_view.
          destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
            eqn:Hrun; cbn in Hnew |- *; [|contradiction].
          eapply discovery_result_done_rows; [exact Hrun|exact Hnew|].
          apply (proj2 (S.rows_of_spec p y r Hwf)); split; assumption. }
        assert (Hrow :
          row_ok L.leb (look (merge_discovered st (discover p roots st) m))
            (S.target p r)
            (S.eval p r (look (merge_discovered st (discover p roots st) m))) =
          row_ok L.leb (Checker.look m)
            (S.target p r) (S.eval p r (Checker.look m))).
        { apply row_look_transport; [exact Hwf|exact Hr|].
          intros x Hx; destruct (region_closed p roots st r x
            (conj Hclosed Hpost) Hregion Hx) as [Hold|Hin].
          - rewrite (merge_old_look st _ m x Hmissing Hold).
            symmetry; apply Hagree; exact Hold.
          - apply merge_new_look; exact Hin. }
        rewrite Hrow; apply (proj1 (Checker.check_rows_iff p _ m) Hcheck r Hregion).
  Qed.

  Lemma demand_certificate : forall p pol roots fuel st st', S.wf p -> inv p st ->
    demand p pol roots fuel st = (Done, st') ->
    exists m, Checker.check_rows p (region p roots st) m = true.
  Proof.
    intros p pol roots fuel st st' Hwf Hinv Hrun.
    exact (DemandPlanProof.demand_certificate p pol roots fuel st st' Hwf Hinv Hrun).
  Qed.

  Lemma region_least_restricted : forall p pol roots fuel st m,
    S.wf p -> S.monotone p -> Least.widening_free pol -> inv p st -> least_on p st ->
    Sol.run (R.mk p (frozen p roots st) (region p roots st)) pol fuel = Solved m ->
    forall s, S.post_solution p s -> forall x,
      L.leb (look_or S.key_code L.bot m x) (s x) = true.
  Proof.
    intros p pol roots fuel st m Hwf Hmono Hfree Hinv Hleast Hrun upper Hpost x.
    assert (Hrows : forall r, In r (region p roots st) -> In r (S.rows p)).
    { intros r Hr; eapply region_rows; eauto. }
    assert (Hseeds : forall y v, In (y, v) (frozen p roots st) ->
      L.leb v (upper y) = true).
    { intros y v Hin; apply (Hleast upper Hpost y v).
      unfold frozen, discovery_view in Hin.
      destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
        eqn:Hdiscovery; cbn in Hin; [|contradiction].
      eapply discovery_result_frozen; eauto. }
    eapply (Least.run_least (R.mk p (frozen p roots st) (region p roots st))
      pol fuel m upper).
    - apply R.mk_wf; [exact Hwf|exact Hrows].
    - apply R.mk_monotone; [exact Hmono|exact Hrows].
    - exact Hfree.
    - exact Hrun.
    - apply R.restrict_complete; [exact Hpost|exact Hrows|exact Hseeds].
  Qed.

  Lemma region_least : forall p (E : S.key -> Prop) rs small global,
    S.wf p -> S.monotone p -> closed p E ->
    (forall r, In r rs <-> In r (S.rows p) /\ exists x, E x /\ In x (S.writes p r)) ->
    S.post_on p rs small ->
    (forall s, S.post_on p rs s -> S.below small s) ->
    least_solution p global ->
    forall x, E x -> L.leb (small x) (global x) = true /\
      L.leb (global x) (small x) = true.
  Proof.
    intros p E rs small global Hwf Hmono Hclosed Hrows Hsmall Hregional
      [Hglobal Hleast] x HEx; split.
    - apply (Hregional global); intros r Hr; apply Hglobal.
      exact (proj1 (proj1 (Hrows r) Hr)).
    - set (support := x :: flat_map (fun r => S.writes p r ++ S.deps p r) rs).
      set (member := fun y => existsb (S.key_eqb y) support).
      assert (Hmember : forall y, member y = true <-> In y support).
      { intro y; unfold member; rewrite existsb_exists; split.
        - intros [z [Hz Heq]].
          destruct (S.key_eqb_spec y z) as [->|Hneq]; [exact Hz|discriminate Heq].
        - intro Hy; exists y; split; [exact Hy|].
          destruct (S.key_eqb_spec y y); congruence. }
      assert (Hsupport : forall y, In y support -> E y).
      { intros y Hy; unfold support in Hy; destruct Hy as [<-|Hy]; [exact HEx|].
        apply in_flat_map in Hy as [r [Hr Hy]].
        destruct (proj1 (Hrows r) Hr) as [Hlisted [z [HEz Hwrite]]].
        exact (Hclosed r z y Hlisted Hwrite HEz Hy). }
      assert (Hselected : forall r y, In r (S.rows p) -> In y (S.writes p r) ->
        member y = true -> In r rs).
      { intros r y Hr Hy Hmem; apply (proj2 (Hrows r)); split; [exact Hr|].
        exists y; split; [apply Hsupport; apply (proj1 (Hmember y)); exact Hmem|exact Hy]. }
      assert (Hclosed_member : TopFacts.support_closed p member).
      { intros r y z Hr Hy Hmem Hz; apply (proj2 (Hmember z)); unfold support; right.
        apply in_flat_map; exists r; split; [exact (Hselected r y Hr Hy Hmem)|exact Hz]. }
      assert (Hextended : S.post_solution p (TopFacts.top_extend member small)).
      { apply TopFacts.top_extend_post; [exact Hwf|exact Hclosed_member|].
        intros r y Hr Hy Hmem; apply Hsmall; exact (Hselected r y Hr Hy Hmem). }
      pose proof (Hleast (TopFacts.top_extend member small) Hextended x) as Hbound.
      assert (Hmember_x : member x = true).
      { apply (proj2 (Hmember x)); unfold support; now left. }
      rewrite (TopFacts.top_extend_on member small x Hmember_x) in Hbound; exact Hbound.
  Qed.

  (** Frozen pairs are stored checked values. *)
  Lemma frozen_spec : forall p roots st x v,
    In (x, v) (frozen p roots st) -> value st x = Some v.
  Proof.
    intros p roots st x v Hin; unfold frozen, discovery_view in Hin.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; cbn in Hin; [|contradiction].
    eapply discovery_result_frozen; eauto.
  Qed.

  Definition frozen_source_state (p : S.prog)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    forall x v, In (x, v) (discovery_frozen acc) ->
      exists r, In r (discovery_rows acc) /\ In x (row_keys p r).

  Lemma discovery_visit_frozen_origin : forall st acc x y v,
    In (y, v) (discovery_frozen (discovery_visit st x acc)) ->
    In (y, v) (discovery_frozen acc) \/ y = x.
  Proof.
    intros st acc x y v Hin; unfold discovery_visit in Hin.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)); [now left|].
    destruct (value st x); cbn [discovery_frozen] in Hin;
      [|now left].
    destruct Hin as [Heq|Hin]; [injection Heq as <- <-; now right|now left].
  Qed.

  Lemma discovery_seed_frozen_empty : forall st roots,
    discovery_frozen (fold_left (discovery_seed_one st) roots empty_discovery) = [].
  Proof.
    intros st roots.
    assert (Hseed : forall xs acc,
      discovery_frozen (fold_left (discovery_seed_one st) xs acc) =
        discovery_frozen acc).
    { intros xs; induction xs as [|x rest IH]; intro acc; [reflexivity|].
      cbn [fold_left]; rewrite IH; unfold discovery_seed_one.
      destruct (missing st x) eqn:Hmissing; [|reflexivity].
      apply (proj1 (missing_spec st x)) in Hmissing.
      unfold discovery_visit; destruct (PTrieCode.get (S.key_code x)
        (discovery_seen acc)); [reflexivity|].
      rewrite Hmissing; reflexivity. }
    rewrite Hseed; reflexivity.
  Qed.

  Lemma discovery_row_frozen_source : forall p st r acc,
    frozen_source_state p acc -> frozen_source_state p (discovery_row p st acc r).
  Proof.
    intros p st r acc Hsource; unfold discovery_row.
    cbn [discovery_frozen discovery_rows].
    assert (Hfold : forall xs current,
      (forall y, In y xs -> In y (row_keys p r)) ->
      discovery_rows current = discovery_rows acc ->
      (forall y v, In (y, v) (discovery_frozen current) ->
        (exists q, In q (discovery_rows acc) /\ In y (row_keys p q)) \/
        In y (row_keys p r)) ->
      forall y v,
        In (y, v) (discovery_frozen
          (fold_left (fun current x => discovery_visit st x current) xs current)) ->
        (exists q, In q (discovery_rows acc) /\ In y (row_keys p q)) \/
        In y (row_keys p r)).
    { intros xs; induction xs as [|x rest IH];
        intros current Hsubset Hrows Hcurrent y v Hin;
        [exact (Hcurrent y v Hin)|].
      cbn [fold_left] in Hin; eapply IH; [| | |exact Hin].
      - intros z Hz; apply Hsubset; now right.
      - rewrite discovery_visit_rows_eq; exact Hrows.
      - intros z w Hnew; apply discovery_visit_frozen_origin in Hnew as [Hold|<-].
        + exact (Hcurrent z w Hold).
        + right; apply Hsubset; now left. }
    intros y v Hin.
    pose proof (Hfold (row_keys p r) acc (fun x Hx => Hx) eq_refl
      (fun x w Hw => or_introl (Hsource x w Hw)) y v Hin) as Horigin.
    destruct Horigin as [[q [Hq Hkey]]|Hkey].
    - exists q; split; [change (In q (discovery_rows (discovery_row p st acc r)));
        rewrite discovery_row_rows; now right|exact Hkey].
    - exists r; split; [now left|exact Hkey].
  Qed.

  Lemma discovery_step_frozen_source : forall p st acc next,
    frozen_source_state p acc -> discovery_step p st acc = inl next ->
    frozen_source_state p next.
  Proof.
    intros p st acc next Hsource Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    inversion Hstep; subst next.
    assert (Hfold : forall rs current, frozen_source_state p current ->
      frozen_source_state p (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_frozen_source. }
    apply Hfold; unfold frozen_source_state in *.
    cbn [discovery_frozen discovery_rows]; exact Hsource.
  Qed.

  (** Frozen pairs have distinct keys read or written by region rows. *)
  Lemma frozen_region : forall p roots st x v, In (x, v) (frozen p roots st) ->
    exists r, In r (region p roots st) /\ In x (S.writes p r ++ S.deps p r).
  Proof.
    intros p roots st x v Hin; unfold frozen, discovery_view in Hin.
    unfold region, discovery_view.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hrun; cbn in Hin |- *; [|contradiction].
    rewrite discovery_rev_equation in Hrun.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery) in *.
    assert (Hinitial : frozen_source_state p initial).
    { unfold initial, frozen_source_state; rewrite discovery_seed_frozen_empty.
      intros y w Hy; contradiction. }
    assert (Hstep : forall acc, frozen_source_state p acc ->
      match discovery_step p st acc with
      | inl next => frozen_source_state p next
      | inr finished => frozen_source_state p finished
      end).
    { intros acc Hsource; destruct (discovery_step p st acc) as [next|finished]
        eqn:Hnext; [eapply discovery_step_frozen_source; eauto|].
      unfold discovery_step in Hnext; destruct (discovery_pending acc);
        [inversion Hnext; subst; exact Hsource|discriminate Hnext]. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      (frozen_source_state p) (frozen_source_state p)
      Hstep (view_fuel p roots) initial Hinitial) as Hsource.
    destruct (loopN (discovery_step p st) (view_fuel p roots) initial)
      as [remaining|finished] eqn:Hloop; [discriminate Hrun|].
    cbn in Hrun; injection Hrun as _ Hrs Hfz; subst rs fz.
    apply in_rev in Hin.
    destruct (Hsource x v Hin) as [r [Hr Hkey]].
    exists r; split; [|exact Hkey].
    apply in_rev in Hr; exact Hr.
  Qed.
  Lemma frozen_nodup : forall p roots st, NoDup (map fst (frozen p roots st)).
  Proof.
    exact DemandPlanProof.frozen_nodup.
  Qed.

  Lemma discovery_views : forall p roots fuel st ks rs fz, S.wf p ->
    discovery p roots fuel st = Some (ks, rs, fz) ->
    ks = discover p roots st /\ rs = region p roots st /\ fz = frozen p roots st.
  Proof.
    exact discovery_result_view_projection.
  Qed.

  Definition discovery_bounded (p : S.prog) (roots : list S.key) (st : state)
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    discovery_missing_valid st acc /\ discovery_balanced acc /\
    discovery_rows_listed p acc /\ discovery_source_state p roots acc.

  Lemma discovery_bounded_length : forall p roots st acc,
    discovery_bounded p roots st acc ->
    length (discovery_done acc) <= length roots +
      fold_right Nat.add 0 (map (fun r => length (row_keys p r)) (S.rows p)).
  Proof.
    intros p roots st acc [Hmissing [Hbalanced [Hlisted Hsource]]].
    assert (Hincl : incl (discovery_missing acc)
      (roots ++ flat_map (row_keys p) (S.rows p))).
    { intros x Hx; apply in_app_iff.
      destruct (Hsource x Hx) as [Hroot|[r [Hr Hkey]]]; [now left|right].
      apply in_flat_map; exists r; split; [now apply Hlisted|exact Hkey]. }
    pose proof (NoDup_incl_length (proj1 Hmissing) Hincl) as Hlength.
    rewrite length_app, finite_flat_map_length in Hlength.
    unfold discovery_balanced in Hbalanced.
    unfold finite_sum in Hlength; lia.
  Qed.

  Lemma discovery_seed_rows_empty : forall st roots,
    discovery_rows (fold_left (discovery_seed_one st) roots empty_discovery) = [].
  Proof.
    intros st roots.
    assert (Hseed : forall xs acc,
      discovery_rows (fold_left (discovery_seed_one st) xs acc) =
        discovery_rows acc).
    { intros xs; induction xs as [|x rest IH]; intro acc; [reflexivity|].
      cbn [fold_left]; rewrite IH; unfold discovery_seed_one.
      destruct (missing st x); [apply discovery_visit_rows_eq|reflexivity]. }
    rewrite Hseed; reflexivity.
  Qed.

  Lemma discovery_bounded_initial : forall p roots st,
    discovery_bounded p roots st
      (fold_left (discovery_seed_one st) roots empty_discovery).
  Proof.
    intros p roots st; unfold discovery_bounded.
    split; [|split; [|split]].
    - apply discovery_seed_missing_valid.
      unfold discovery_missing_valid, empty_discovery;
        cbn [discovery_missing]; split; [constructor|].
      intros x Hx; contradiction.
    - apply discovery_seed_balanced.
      unfold discovery_balanced, empty_discovery;
        cbn [discovery_missing discovery_pending discovery_done]; reflexivity.
    - unfold discovery_rows_listed; rewrite discovery_seed_rows_empty.
      intros r Hr; contradiction.
    - apply discovery_seed_source.
  Qed.

  Lemma discovery_bounded_step : forall p roots st acc next,
    S.wf p -> discovery_bounded p roots st acc ->
    discovery_step p st acc = inl next -> discovery_bounded p roots st next.
  Proof.
    intros p roots st acc next Hwf [Hmissing [Hbalanced [Hlisted Hsource]]] Hstep.
    unfold discovery_bounded; split; [|split; [|split]].
    - eapply discovery_step_missing_valid; eauto.
    - eapply discovery_step_balanced; eauto.
    - eapply discovery_step_listed; eauto.
    - eapply discovery_step_source; eauto.
  Qed.

  Lemma discovery_fuel_bound : forall {A : Type} (step : A -> A + A)
      (Inv : A -> Prop) (count : A -> nat) bound start fuel,
    Inv start ->
    (forall s, Inv s -> count s <= bound) ->
    (forall s next, Inv s -> step s = inl next ->
      Inv next /\ count next = S (count s)) ->
    bound - count start < fuel ->
    exists result, loop_fuel step fuel start = inr result.
  Proof.
    intros A step Inv count bound start fuel Hinitial Hbound Hstep.
    revert start Hinitial; induction fuel as [|fuel IH]; intros start Hinitial Hfuel;
      [lia|].
    cbn [loop_fuel]; destruct (step start) as [next|result] eqn:Hcall;
      [|eexists; reflexivity].
    destruct (Hstep start next Hinitial Hcall) as [Hnext Hcount].
    apply IH; [exact Hnext|].
    pose proof (Hbound next Hnext) as Hnext_bound.
    rewrite Hcount in Hnext_bound |- *; lia.
  Qed.

  Lemma discovery_view_finishes : forall p roots st, S.wf p ->
    discovery p roots (view_fuel p roots) st <> None.
  Proof.
    intros p roots st Hwf; unfold discovery.
    set (initial := fold_left (discovery_seed_one st) roots empty_discovery).
    set (bound := length roots +
      fold_right Nat.add 0 (map (fun r => length (row_keys p r)) (S.rows p))).
    assert (Hinitial : discovery_bounded p roots st initial).
    { unfold initial; apply discovery_bounded_initial. }
    assert (Hstep : forall acc next,
      discovery_bounded p roots st acc -> discovery_step p st acc = inl next ->
      discovery_bounded p roots st next /\
        length (discovery_done next) = S (length (discovery_done acc))).
    { intros acc next Hacc Hcall; split.
      - eapply discovery_bounded_step; eauto.
      - eapply discovery_step_done_count; eauto. }
    rewrite incremental_loopN_fuel.
    destruct (discovery_fuel_bound (discovery_step p st)
      (discovery_bounded p roots st) (fun acc => length (discovery_done acc))
      bound initial (N.to_nat (view_fuel p roots)) Hinitial
      (discovery_bounded_length p roots st) Hstep) as [result Hresult].
    - unfold bound, initial, view_fuel.
      rewrite discovery_seed_done_empty, Nat2N.id; cbn [length].
      rewrite Nat.sub_0_r; apply Nat.lt_succ_diag_r.
    - rewrite Hresult; discriminate.
  Qed.

  Lemma discovery_enough : forall p roots fuel st, S.wf p ->
    (N.of_nat (length (discover p roots st)) < fuel)%N ->
    discovery p roots fuel st <> None.
  Proof.
    intros p roots fuel st Hwf Hfuel.
    destruct (discovery p roots (view_fuel p roots) st) as [[[ks rs] fz]|]
      eqn:Hview; [|exfalso; eapply discovery_view_finishes; eauto].
    pose proof (discovery_result_view_keys p roots (view_fuel p roots)
      st ks rs fz Hwf Hview) as Hkeys.
    rewrite <- Hkeys in Hfuel.
    rewrite (discovery_finished_replay p roots (view_fuel p roots)
      st ks rs fz Hview fuel Hfuel); discriminate.
  Qed.

  Lemma T_merge_region_le : forall st xs m,
    (T_merge_region st xs m <= c_inc * N.of_nat
      (fold_right Nat.add 0%nat
        (map (fun x => S.key_bits x + 1)%nat xs) + 1)%nat)%N.
  Proof.
    intros st xs m.
    pose proof (T_fill_local_le xs m (inc_values st)) as Hfill.
    unfold T_merge_region, T_merge_discovered, c_inc in *.
    time_simpl; time_cbn; nia.
  Qed.

  Lemma T_value_small_le : forall st x,
    (T_value st x <= 4 * (S.c_sys + PTrieT.c_trie + 1) *
      N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros st x.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (S.key * L.t) (S.key_code x) (inc_values st)) as Hget.
    assert (Hguard :
      (match PTrieCode.get (S.key_code x) (inc_values st) with
       | Some (stored_key, _) => S.T_key_eqb x stored_key
       | None => 0 end <= S.c_sys * N.of_nat (S.key_bits x + 1))%N).
    { destruct (PTrieCode.get (S.key_code x) (inc_values st)) as [[key v]|];
        [apply S.T_key_eqb_le|lia]. }
    unfold PTrieT.T_get in Hget.
    unfold T_value, T_lookup, PTrieCode.T_get, S.key_bits in *.
    time_simpl; time_cbn; nia.
  Qed.

  Lemma T_discovery_visit_le : forall st x acc,
    (T_discovery_visit st x acc <=
      12 * (S.c_sys + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros st x acc.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le unit (S.key_code x) (discovery_seen acc)) as Hget.
    pose proof (PTrieT.T_set_le unit (S.key_code x) tt (discovery_seen acc)) as Hset.
    pose proof (T_value_small_le st x) as Hvalue.
    unfold T_discovery_visit, PTrieCode.T_get, PTrieCode.T_set,
      PTrieT.T_get, PTrieT.T_set, S.key_bits in *.
    change (1 + PTrieCode.T_replace (S.key_code x) (Some tt)
      (discovery_seen acc) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (S.key_code x) + 1))%N in Hset.
    assert (Hbits : (1 <= N.of_nat (Pos.size_nat (S.key_code x) + 1))%N) by lia.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|];
      destruct (value st x); time_simpl; time_cbn; nia.
  Qed.

  Lemma T_discovery_seed_one_le : forall st x acc,
    (T_discovery_seed_one st acc x <=
      20 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros st x acc.
    pose proof (T_value_small_le st x) as Hvalue.
    pose proof (T_discovery_visit_le st x acc) as Hvisit.
    unfold T_discovery_seed_one, T_missing, T_present, c_inc, S.key_bits in *.
    destruct (missing st x); time_simpl; time_cbn; nia.
  Qed.

  Lemma T_local_fold_in : forall A B (f : A -> B -> A) Tf xs acc k,
    (forall state x, In x xs -> (Tf state x <= k)%N) ->
    (List.T_fold_left f Tf xs acc <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f Tf xs; induction xs as [|x xs IH]; intros acc k Hcallback.
    - time_step.
    - pose proof (Hcallback acc x (or_introl eq_refl)) as Hhead.
      pose proof (IH (f acc x) k
        (fun state y Hy => Hcallback state y (or_intror Hy))) as Htail.
      time_step.
  Qed.

  Lemma T_row_keys_le : forall p st r, S.wf p -> In r (S.rows p) ->
    (T_row_keys p r <= 4 * (S.c_sys + 1) *
      N.of_nat (length (row_keys p r)) * N.of_nat (width p st + 1))%N.
  Proof.
    intros p st r Hwf Hr.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (S.T_sides_le p r Hwf Hr) as Hsides.
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (Datatypes.T_app_le (S.target p r :: S.sides p r)
      (S.deps p r)) as Happ.
    unfold T_row_keys, T_row_writes, row_keys, row_writes, width.
    time_simpl; time_cbn.
    rewrite length_app in *.
    rewrite !Nat2N.inj_add in *.
    rewrite N2Nat.id in *.
    cbn [length] in Happ.
    rewrite !Nat2N.inj_succ in Happ.
    cbn [N.of_nat] in *.
    nia.
  Qed.

  Lemma T_discovery_row_le : forall p st r acc, S.wf p -> In r (S.rows p) ->
    (T_discovery_row p st acc r <=
      26 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
      N.of_nat (length (row_keys p r)) * N.of_nat (width p st + 1))%N.
  Proof.
    intros p st r acc Hwf Hr.
    assert (Hbits : forall x, In x (row_keys p r) -> S.key_bits x <= width p st).
    { intros x Hx; unfold width.
      pose proof (S.key_bits_le p r x Hwf Hr Hx); lia. }
    pose proof (T_row_keys_le p st r Hwf Hr) as Hkeys.
    pose proof (T_local_fold_in _ _ (fun current x => discovery_visit st x current)
      (fun current x => (1 + T_discovery_visit st x current)%N) (row_keys p r) acc
      (12 * (S.c_sys + PTrieT.c_trie + 1) * N.of_nat (width p st + 1) + 1)%N)
      as Hfold.
    assert (Hcallback : forall current x, In x (row_keys p r) ->
      (1 + T_discovery_visit st x current <=
        12 * (S.c_sys + PTrieT.c_trie + 1) * N.of_nat (width p st + 1) + 1)%N).
    { intros current x Hx.
      pose proof (T_discovery_visit_le st x current) as Hvisit.
      assert (Hwidth : (N.of_nat (S.key_bits x + 1) <=
        N.of_nat (width p st + 1))%N) by (pose proof (Hbits x Hx); lia).
      assert (Hsmall : (12 * (S.c_sys + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1) <=
        12 * (S.c_sys + PTrieT.c_trie + 1) *
        N.of_nat (width p st + 1))%N).
      { apply N.mul_le_mono_l; exact Hwidth. }
      lia. }
    specialize (Hfold Hcallback).
    unfold T_discovery_row.
    time_simpl; time_cbn.
    unfold row_keys, row_writes in Hfold, Hkeys.
    rewrite length_app in *.
    rewrite !Nat2N.inj_add in *.
    cbn [length] in *.
    set (n := (N.of_nat (S (length (S.sides p r))) +
      N.of_nat (length (S.deps p r)))%N) in *.
    set (u := (N.of_nat (width p st) + 1)%N) in *.
    set (a := S.c_sys) in *.
    set (b := S.c_loc) in *.
    set (c := PTrieT.c_trie) in *.
    change (N.of_nat 1) with 1%N in *.
    fold n u in Hkeys, Hfold.
    replace (N.of_nat (length (S.sides p r)) +
      N.of_nat (length (S.deps p r)) + 1)%N with n.
    2: { unfold n; rewrite Nat2N.inj_succ; lia. }
    fold u.
    clear Hwf Hr Hbits Hcallback.
    assert (Hunit : (1 <= u)%N) by (unfold u; lia).
    assert (Hnonempty : (1 <= n)%N) by (unfold n; lia).
    assert (Hscale : (4 * (a + 1) + 12 * (a + c + 1) + 10 <=
      26 * (a + b + c + 1))%N) by lia.
    assert (Hproduct : ((4 * (a + 1) + 12 * (a + c + 1) + 10) * n * u <=
      26 * (a + b + c + 1) * n * u)%N).
    { apply N.mul_le_mono_r, N.mul_le_mono_r; exact Hscale. }
    assert (Hoverhead : (2 * n + 8 <= 10 * n * u)%N).
    { assert (Hn : (n <= n * u)%N) by nia.
      nia. }
    replace ((12 * (a + c + 1) * u + 1 + 1) * n + 1)%N with
      (12 * (a + c + 1) * u * n + 2 * n + 1)%N in Hfold by ring.
    assert (Hbudget : (4 * (a + 1) * n * u +
      12 * (a + c + 1) * u * n + 2 * n + 8 <=
      (4 * (a + 1) + 12 * (a + c + 1) + 10) * n * u)%N).
    { replace ((4 * (a + 1) + 12 * (a + c + 1) + 10) * n * u)%N with
        (4 * (a + 1) * n * u + 12 * (a + c + 1) * u * n + 10 * n * u)%N
        by ring.
      lia. }
    assert (Hclock : (1 + (T_row_keys p r +
      List.T_fold_left (fun current x => discovery_visit st x current)
        (fun current x => (1 + T_discovery_visit st x current)%N)
        (row_keys p r) acc + 6) <=
      4 * (a + 1) * n * u +
      12 * (a + c + 1) * u * n + 2 * n + 8)%N).
    { unfold row_keys, row_writes; lia. }
    unfold row_keys, row_writes in Hclock.
    replace (S.target p r :: S.sides p r ++ S.deps p r) with
      ((S.target p r :: S.sides p r) ++ S.deps p r) by reflexivity.
    eapply N.le_trans; [exact Hclock|].
    eapply N.le_trans; [exact Hbudget|exact Hproduct].
  Qed.

  Lemma T_discovery_rows_fold_le : forall p st rs acc, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (List.T_fold_left (discovery_row p st)
      (fun current r => T_discovery_row p st current r) rs acc <=
      26 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (fold_right Nat.add 0%nat (map (fun r => length (row_keys p r)) rs)) *
        N.of_nat (width p st + 1) + 2 * N.of_nat (length rs) + 1)%N.
  Proof.
    intros p st rs acc Hwf Hlisted.
    destruct (fold_left_inv_time (discovery_row p st)
      (fun current r => T_discovery_row p st current r)
      (fun _ => True)
      (fun r => (26 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (length (row_keys p r)) * N.of_nat (width p st + 1))%N)
      rs acc I) as [_ Hfold].
    { intros current r _ Hr; split; [exact I|].
      apply T_discovery_row_le; [exact Hwf|now apply Hlisted]. }
    assert (Hsum : forall xs,
      (fold_right (fun r total =>
        26 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (length (row_keys p r)) * N.of_nat (width p st + 1) + 2 + total)%N
        1%N xs <=
        26 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (fold_right Nat.add 0%nat
            (map (fun r => length (row_keys p r)) xs)) *
          N.of_nat (width p st + 1) + 2 * N.of_nat (length xs) + 1)%N).
    { induction xs as [|r rest IH]; [cbn; lia|].
      cbn [map fold_right length].
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
      change (N.succ (N.of_nat 0)) with 1%N in *.
      change (N.of_nat 1) with 1%N in *.
      nia. }
    eapply N.le_trans; [exact Hfold|apply Hsum].
  Qed.

  Lemma discovery_step_arithmetic : forall c base n q k u,
    (n <= q)%N -> (c <= base)%N -> (4 <= base)%N ->
    (1 <= k)%N -> (1 <= u)%N ->
    (9 + c * (n + k) + 26 * base * q * u + 2 * n <=
      64 * base * q * u + 64 * base * k + 64 * base * u)%N.
  Proof.
    intros c base n q k u Hn Hc Hb Hk Hu.
    assert (Hbu : (1 <= base * u)%N) by nia.
    assert (Hqu : (q <= base * q * u)%N).
    { replace q with (q * 1)%N at 1 by ring.
      replace (base * q * u)%N with (q * (base * u))%N by ring.
      apply N.mul_le_mono_l; exact Hbu. }
    assert (Hnu : (n <= base * q * u)%N) by lia.
    assert (Hcn : (c * n <= base * q * u)%N).
    { eapply N.le_trans; [apply N.mul_le_mono_l; exact Hn|].
      eapply N.le_trans; [apply N.mul_le_mono_r; exact Hc|].
      replace (base * q * u)%N with ((base * q) * u)%N by ring.
      replace (base * q)%N with ((base * q) * 1)%N at 1 by ring.
      apply N.mul_le_mono_l; exact Hu. }
    assert (Hck : (c * k <= base * k)%N) by (apply N.mul_le_mono_r; exact Hc).
    assert (Hnine : (9 <= 9 * base * u)%N).
    { replace (9 * base * u)%N with (9 * (base * u))%N by ring.
      replace 9%N with (9 * 1)%N at 1 by ring.
      apply N.mul_le_mono_l; exact Hbu. }
    rewrite N.mul_add_distr_l.
    set (v := (base * q * u)%N).
    set (w := (base * k)%N).
    set (z := (base * u)%N).
    change (n <= v)%N in Hnu.
    change (c * n <= v)%N in Hcn.
    change (c * k <= w)%N in Hck.
    replace (9 * base * u)%N with (9 * z)%N in Hnine by (unfold z; ring).
    assert (Hsum : (9 + c * n + c * k + 26 * v + 2 * n <=
      64 * v + 64 * w + 64 * z)%N) by lia.
    unfold v, w, z in Hsum.
    replace (64 * base * q * u + 64 * base * k + 64 * base * u)%N with
      (64 * (base * q * u) + 64 * (base * k) + 64 * (base * u))%N by ring.
    replace (26 * base * q * u)%N with (26 * (base * q * u))%N by ring.
    replace (9 + (c * n + c * k) + 26 * (base * q * u) + 2 * n)%N with
      (9 + c * n + c * k + 26 * (base * q * u) + 2 * n)%N by ring.
    exact Hsum.
  Qed.

  Lemma T_discovery_step_le : forall p st acc, S.wf p ->
    (T_discovery_step p st acc <=
      match discovery_pending acc with
      | [] => 64 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (width p st + 1)
      | x :: _ =>
        64 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (fold_right Nat.add 0%nat (map (fun r => length (row_keys p r))
            (S.rows_of p x))) * N.of_nat (width p st + 1) +
        64 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (S.key_bits x + 1) +
        64 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (width p st + 1)
      end)%N.
  Proof.
    intros p st acc Hwf.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending.
    - unfold T_discovery_step, c_inc, width.
      rewrite Hpending; time_simpl; time_cbn; nia.
    - assert (Hlisted : forall r, In r (S.rows_of p x) -> In r (S.rows p)).
      { intros r Hr; apply (proj1 (S.rows_of_spec p x r Hwf)) in Hr; tauto. }
      pose proof (S.T_rows_of_le p x Hwf) as Hrows_of.
      set (rest := {| discovery_pending := pending; discovery_seen := discovery_seen acc;
        discovery_missing := discovery_missing acc; discovery_done := x :: discovery_done acc;
        discovery_rows := discovery_rows acc; discovery_frozen := discovery_frozen acc |}).
      pose proof (T_discovery_rows_fold_le p st (S.rows_of p x) rest Hwf Hlisted)
        as Hfold.
      unfold T_discovery_step.
      rewrite Hpending.
      time_simpl; time_cbn.
      assert (Hlen : length (S.rows_of p x) <=
        fold_right Nat.add 0%nat
          (map (fun r => length (row_keys p r)) (S.rows_of p x))).
      { generalize (S.rows_of p x) as rs; clear; intros rs.
        induction rs as [|r rest IH]; [cbn; lia|].
        cbn [map fold_right length].
        unfold row_keys, row_writes in *; cbn [length] in *.
        rewrite length_app; cbn [length]; lia. }
      assert (Hbase : (4 <= S.c_sys + S.c_loc + PTrieT.c_trie + 1)%N).
      { unfold PTrieT.c_trie; lia. }
      unfold row_keys, row_writes in Hfold.
      cbn [length] in Hfold.
      rewrite !Nat2N.inj_add in Hrows_of, Hfold |- *.
      set (base := (S.c_sys + S.c_loc + PTrieT.c_trie + 1)%N).
      set (n := N.of_nat (length (S.rows_of p x))).
      set (q := N.of_nat (fold_right Nat.add 0%nat
        (map (fun r => S (length (S.sides p r ++ S.deps p r))) (S.rows_of p x)))).
      set (k := N.of_nat (S.key_bits x + 1)).
      set (u := (N.of_nat (width p st) + 1)%N).
      assert (Hnq : (n <= q)%N).
      { unfold row_keys, row_writes in Hlen.
        change (map (fun r => length ((S.target p r :: S.sides p r) ++ S.deps p r))
          (S.rows_of p x)) with
          (map (fun r => S (length (S.sides p r ++ S.deps p r)))
            (S.rows_of p x)) in Hlen.
        unfold n, q; lia. }
      assert (Hc : (S.c_loc <= base)%N) by (unfold base; lia).
      assert (Hb : (4 <= base)%N) by (unfold base; exact Hbase).
      assert (Hk : (1 <= k)%N) by (unfold k; lia).
      assert (Hu : (1 <= u)%N) by (unfold u; lia).
      assert (Hrows' : (S.T_rows_of p x <= S.c_loc * (n + k))%N).
      { unfold n, k; rewrite !Nat2N.inj_add.
        rewrite Nat2N.inj_add in Hrows_of; lia. }
      assert (Hfold' : (List.T_fold_left (discovery_row p st)
        (fun current r => T_discovery_row p st current r)
        (S.rows_of p x) rest <= 26 * base * q * u + 2 * n + 1)%N).
      { unfold base, q, u, n.
        change (map (fun r => length ((S.target p r :: S.sides p r) ++ S.deps p r))
          (S.rows_of p x)) with
          (map (fun r => S (length (S.sides p r ++ S.deps p r)))
            (S.rows_of p x)) in Hfold.
        change (N.of_nat 1) with 1%N in Hfold.
        exact Hfold. }
      pose proof (discovery_step_arithmetic S.c_loc base n q k u
        Hnq Hc Hb Hk Hu) as Hbudget.
      eapply N.le_trans; [|exact Hbudget].
      change (N.of_nat 1) with 1%N.
      fold base q k u rest.
      lia.
  Qed.

  Lemma T_discovery_seed_fold_le : forall st roots acc,
    (List.T_fold_left (discovery_seed_one st)
      (fun current x => T_discovery_seed_one st current x) roots acc <=
      24 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (fold_right Nat.add 0%nat
          (map (fun x => S.key_bits x + 1)%nat roots)) + 1)%N.
  Proof.
    intros st roots acc.
    destruct (fold_left_inv_time (discovery_seed_one st)
      (fun current x => T_discovery_seed_one st current x)
      (fun _ => True)
      (fun x => (20 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1))%N) roots acc I) as [_ Hfold].
    { intros current x _ _; split; [exact I|apply T_discovery_seed_one_le]. }
    assert (Hsum : forall xs,
      (fold_right (fun x total =>
        20 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (S.key_bits x + 1) + 2 + total)%N 1%N xs <=
        24 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (fold_right Nat.add 0%nat
            (map (fun x => S.key_bits x + 1)%nat xs)) + 1)%N).
    { induction xs as [|x rest IH]; [cbn; lia|].
      cbn [map fold_right]; rewrite Nat2N.inj_add.
      pose proof (Pos2Nat.is_pos (S.key_code x)) as Hpositive.
      unfold S.key_bits in *; nia. }
    eapply N.le_trans; [exact Hfold|apply Hsum].
  Qed.

  Lemma discovery_rows_weight_fold : forall p st rs acc,
    finite_sum (fun r => length (row_keys p r))
      (discovery_rows (fold_left (discovery_row p st) rs acc)) =
    finite_sum (fun r => length (row_keys p r)) rs +
      finite_sum (fun r => length (row_keys p r)) (discovery_rows acc).
  Proof.
    intros p st rs; induction rs as [|r rest IH]; intro acc.
    - reflexivity.
    - cbn [fold_left finite_sum]; rewrite IH, discovery_row_rows.
      unfold finite_sum; cbn [map fold_right]; lia.
  Qed.

  Lemma discovery_step_weight : forall p st acc next x pending,
    discovery_pending acc = x :: pending -> discovery_step p st acc = inl next ->
    finite_sum (fun r => length (row_keys p r)) (discovery_rows next) =
      finite_sum (fun r => length (row_keys p r)) (S.rows_of p x) +
      finite_sum (fun r => length (row_keys p r)) (discovery_rows acc) /\
    discovery_done next = x :: discovery_done acc.
  Proof.
    intros p st acc next x pending Hpending Hstep.
    unfold discovery_step in Hstep; rewrite Hpending in Hstep.
    injection Hstep as <-; split.
    - rewrite discovery_rows_weight_fold; reflexivity.
    - rewrite discovery_fold_done; reflexivity.
  Qed.

  Definition discovery_spent (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) : N :=
    let base := (S.c_sys + S.c_loc + PTrieT.c_trie + 1)%N in
    let unit := N.of_nat (width p st + 1) in
    (128 * base * N.of_nat (finite_sum (fun r => length (row_keys p r))
      (discovery_rows acc)) * unit +
     128 * base * N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat)
       (discovery_done acc)) +
     128 * base * N.of_nat (length (discovery_done acc)) * unit)%N.

  Lemma discovery_spent_step : forall p st acc next x pending,
    discovery_pending acc = x :: pending -> discovery_step p st acc = inl next ->
    discovery_spent p st next =
      (discovery_spent p st acc +
       128 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
         N.of_nat (finite_sum (fun r => length (row_keys p r)) (S.rows_of p x)) *
         N.of_nat (width p st + 1) +
       128 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
         N.of_nat (S.key_bits x + 1) +
       128 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
         N.of_nat (width p st + 1))%N.
  Proof.
    intros p st acc next x pending Hpending Hstep.
    destruct (discovery_step_weight p st acc next x pending Hpending Hstep)
      as [Hrows Hdone].
    unfold discovery_spent; rewrite Hrows, Hdone.
    unfold finite_sum; cbn [map fold_right length].
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ.
    change (N.succ (N.of_nat 0)) with 1%N.
    replace (N.succ (N.of_nat (length (discovery_done acc)))) with
      (N.of_nat (length (discovery_done acc)) + 1)%N by lia.
    ring.
  Qed.

  Definition discovery_queue_perm
      (acc : incremental_discovery S.key S.row L.t) : Prop :=
    Permutation (discovery_pending acc ++ discovery_done acc) (discovery_missing acc).

  Lemma discovery_visit_queue_perm : forall st x acc,
    discovery_queue_perm acc -> discovery_queue_perm (discovery_visit st x acc).
  Proof.
    intros st x acc Hperm; unfold discovery_visit, discovery_queue_perm in *.
    destruct (PTrieCode.get (S.key_code x) (discovery_seen acc)) as [[]|];
      [exact Hperm|].
    destruct (value st x); cbn [discovery_pending discovery_done discovery_missing];
      [exact Hperm|now constructor].
  Qed.

  Lemma discovery_seed_queue_perm : forall st roots acc,
    discovery_queue_perm acc ->
    discovery_queue_perm (fold_left (discovery_seed_one st) roots acc).
  Proof.
    intros st roots; induction roots as [|x rest IH]; intros acc Hperm;
      [exact Hperm|].
    cbn [fold_left]; apply IH; unfold discovery_seed_one.
    destruct (missing st x); [now apply discovery_visit_queue_perm|exact Hperm].
  Qed.

  Lemma discovery_row_queue_perm : forall p st r acc,
    discovery_queue_perm acc -> discovery_queue_perm (discovery_row p st acc r).
  Proof.
    intros p st r acc Hperm; unfold discovery_row, discovery_queue_perm in *.
    cbn [discovery_pending discovery_done discovery_missing].
    induction (row_keys p r) as [|x rest IH] in acc, Hperm |- *;
      [exact Hperm|].
    cbn [fold_left]; apply IH; now apply discovery_visit_queue_perm.
  Qed.

  Lemma discovery_step_queue_perm : forall p st acc next,
    discovery_queue_perm acc -> discovery_step p st acc = inl next ->
    discovery_queue_perm next.
  Proof.
    intros p st acc next Hperm Hstep; unfold discovery_step in Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending;
      [discriminate Hstep|].
    injection Hstep as <-.
    assert (Hmove : discovery_queue_perm
      {| discovery_pending := pending; discovery_seen := discovery_seen acc;
         discovery_missing := discovery_missing acc; discovery_done := x :: discovery_done acc;
         discovery_rows := discovery_rows acc; discovery_frozen := discovery_frozen acc |}).
    { unfold discovery_queue_perm; cbn [discovery_pending discovery_done discovery_missing].
      eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
      unfold discovery_queue_perm in Hperm; rewrite Hpending in Hperm; exact Hperm. }
    assert (Hfold : forall rs current, discovery_queue_perm current ->
      discovery_queue_perm (fold_left (discovery_row p st) rs current)).
    { intros rs; induction rs as [|r rest IH]; intros current Hcurrent;
        [exact Hcurrent|].
      cbn [fold_left]; apply IH; now apply discovery_row_queue_perm. }
    apply Hfold; exact Hmove.
  Qed.

  Lemma discovery_result_done_perm : forall p roots fuel st ks rs fz,
    discovery p roots fuel st = Some (ks, rs, fz) ->
    exists finished, loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished /\
      Permutation (discovery_done finished) (rev ks) /\
      NoDup (discovery_done finished).
  Proof.
    intros p roots fuel st ks rs fz Hrun.
    destruct (discovery_result_done p roots fuel st ks rs fz Hrun)
      as [finished [Hloop [Hpending _]]].
    assert (Hinitial : discovery_queue_perm
      (fold_left (discovery_seed_one st) roots empty_discovery)).
    { apply discovery_seed_queue_perm; unfold discovery_queue_perm, empty_discovery;
        cbn [discovery_pending discovery_done discovery_missing]; reflexivity. }
    assert (Hstep : forall acc, discovery_queue_perm acc ->
      match discovery_step p st acc with
      | inl next => discovery_queue_perm next
      | inr result => discovery_queue_perm result
      end).
    { intros acc Hperm; destruct (discovery_step p st acc) as [next|result]
        eqn:Hnext; [eapply discovery_step_queue_perm; eauto|].
      unfold discovery_step in Hnext.
      destruct (discovery_pending acc); [injection Hnext as <-; exact Hperm|].
      discriminate Hnext. }
    pose proof (incremental_loopN_preserves (discovery_step p st)
      discovery_queue_perm discovery_queue_perm Hstep fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) Hinitial) as Hperm.
    rewrite Hloop in Hperm; cbn in Hperm.
    assert (Hmissing : discovery_missing finished = rev ks).
    { rewrite discovery_rev_equation in Hrun; rewrite Hloop in Hrun.
      cbn in Hrun; injection Hrun as Hks _ _; subst ks.
      now rewrite rev_involutive. }
    unfold discovery_queue_perm in Hperm.
    rewrite Hmissing in Hperm.
    rewrite Hpending in Hperm.
    cbn [app] in Hperm.
    pose proof (proj1 (discovery_result_missing p roots fuel st ks rs fz Hrun))
      as Hnodup.
    apply NoDup_rev in Hnodup.
    exists finished; split; [exact Hloop|].
    split; [exact Hperm|].
    eapply Permutation_NoDup; [apply Permutation_sym; exact Hperm|exact Hnodup].
  Qed.

  Lemma finite_sum_flat_map_local : forall A B (f : B -> nat) (g : A -> list B) xs,
    finite_sum f (flat_map g xs) = finite_sum (fun x => finite_sum f (g x)) xs.
  Proof.
    intros A B f g xs; induction xs as [|x rest IH]; [reflexivity|].
    cbn [flat_map].
    rewrite finite_sum_app, IH; reflexivity.
  Qed.

  Lemma finite_sum_rev_local : forall A (f : A -> nat) xs,
    finite_sum f (rev xs) = finite_sum f xs.
  Proof.
    intros A f xs; induction xs as [|x rest IH]; [reflexivity|].
    cbn [rev]; rewrite finite_sum_app.
    change (finite_sum f (x :: rest)) with (f x + finite_sum f rest).
    rewrite IH; unfold finite_sum; cbn [map fold_right]; lia.
  Qed.

  Lemma discovery_row_bits_le : forall p st r, S.wf p -> In r (S.rows p) ->
    finite_sum (fun x => S.key_bits x + 1) (row_keys p r) <=
      length (row_keys p r) * (width p st + 1).
  Proof.
    intros p st r Hwf Hr.
    assert (Hbits : forall x, In x (row_keys p r) -> S.key_bits x <= width p st).
    { intros x Hx; unfold width.
      pose proof (S.key_bits_le p r x Hwf Hr Hx); lia. }
    assert (Hlist : forall xs,
      (forall x, In x xs -> S.key_bits x <= width p st) ->
      finite_sum (fun x => S.key_bits x + 1) xs <= length xs * (width p st + 1)).
    { intros xs; induction xs as [|x rest IH]; intros Hmembers; [reflexivity|].
      change (finite_sum (fun y => S.key_bits y + 1) (x :: rest)) with
        (S.key_bits x + 1 + finite_sum (fun y => S.key_bits y + 1) rest).
      cbn [length].
      assert (Hhead : S.key_bits x <= width p st) by (apply Hmembers; now left).
      assert (Htail : forall y, In y rest -> S.key_bits y <= width p st).
      { intros y Hy; apply Hmembers; now right. }
      specialize (IH Htail).
      replace (S (length rest) * (width p st + 1)) with
        (length rest * (width p st + 1) + (width p st + 1)) by nia.
      lia. }
    apply Hlist; exact Hbits.
  Qed.

  Lemma discovery_region_bits_le : forall p roots st, S.wf p ->
    finite_sum (fun x => S.key_bits x + 1)
      (flat_map (row_keys p) (region p roots st)) <=
    finite_sum (fun r => length (row_keys p r)) (region p roots st) *
      (width p st + 1).
  Proof.
    intros p roots st Hwf.
    rewrite finite_sum_flat_map_local.
    assert (Hlist : forall rs,
      (forall r, In r rs -> In r (S.rows p)) ->
      finite_sum (fun r => finite_sum (fun x => S.key_bits x + 1) (row_keys p r)) rs
        <= finite_sum (fun r => length (row_keys p r)) rs * (width p st + 1)).
    { intros rs; induction rs as [|r rest IH]; intros Hlisted; [reflexivity|].
      change (finite_sum
        (fun q => finite_sum (fun x => S.key_bits x + 1) (row_keys p q)) (r :: rest))
        with (finite_sum (fun x => S.key_bits x + 1) (row_keys p r) +
          finite_sum (fun q => finite_sum (fun x => S.key_bits x + 1)
            (row_keys p q)) rest).
      change (finite_sum (fun q => length (row_keys p q)) (r :: rest)) with
        (length (row_keys p r) + finite_sum (fun q => length (row_keys p q)) rest).
      pose proof (discovery_row_bits_le p st r Hwf (Hlisted r (or_introl eq_refl)))
        as Hrow.
      specialize (IH (fun q Hq => Hlisted q (or_intror Hq))).
      rewrite Nat.mul_add_distr_r; lia. }
    apply Hlist; intros r Hr; eapply region_rows; eauto.
  Qed.

  Lemma discovery_done_charge : forall p roots fuel st ks rs fz
      (finished : incremental_discovery S.key S.row L.t),
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    Permutation (discovery_done finished) (rev ks) ->
    NoDup (discovery_done finished) ->
    finite_sum (fun x => S.key_bits x + 1) (discovery_done finished) <=
      finite_sum (fun x => S.key_bits x + 1) roots +
      finite_sum (fun r => length (row_keys p r)) (region p roots st) *
        (width p st + 1) /\
    length (discovery_done finished) <= length roots +
      finite_sum (fun r => length (row_keys p r)) (region p roots st).
  Proof.
    intros p roots fuel st ks rs fz finished Hwf Hrun Hperm Hnodup.
    assert (Hincl : incl (discovery_done finished)
      (roots ++ flat_map (row_keys p) (region p roots st))).
    { intros x Hx; apply in_app_iff.
      apply (Permutation_in x Hperm) in Hx.
      apply in_rev in Hx.
      destruct (discovery_result_source p roots fuel st ks rs fz x Hrun Hx)
        as [Hroot|[r [Hr Hkey]]]; [now left|right].
      apply in_flat_map; exists r; split.
      - rewrite <- (discovery_result_view_rows p roots fuel st ks rs fz Hwf Hrun).
        exact Hr.
      - exact Hkey. }
    pose proof (finite_sum_incl_nodup _ (fun x => S.key_bits x + 1)
      _ _ Hnodup Hincl) as Hbits.
    rewrite finite_sum_app, finite_sum_flat_map_local in Hbits.
    pose proof (discovery_region_bits_le p roots st Hwf) as Hregion.
    rewrite finite_sum_flat_map_local in Hregion.
    pose proof (finite_sum_incl_nodup _ (fun _ => 1) _ _ Hnodup Hincl) as Hlen.
    rewrite !finite_sum_one, length_app, finite_flat_map_length in Hlen.
    split; lia.
  Qed.

  Lemma discovery_rows_length_charge : forall p rs,
    length rs <= finite_sum (fun r => length (row_keys p r)) rs.
  Proof.
    intros p rs; induction rs as [|r rest IH]; [reflexivity|].
    change (finite_sum (fun q => length (row_keys p q)) (r :: rest)) with
      (length (row_keys p r) + finite_sum (fun q => length (row_keys p q)) rest).
    assert (Hnonempty : 1 <= length (row_keys p r)).
    { unfold row_keys, row_writes; rewrite length_app; cbn [length]; lia. }
    cbn [length]; lia.
  Qed.

  Lemma discovery_frozen_length_charge : forall p roots st,
    length (frozen p roots st) <=
      finite_sum (fun r => length (row_keys p r)) (region p roots st).
  Proof.
    intros p roots st.
    assert (Hincl : incl (map fst (frozen p roots st))
      (flat_map (row_keys p) (region p roots st))).
    { intros x Hx; apply in_map_iff in Hx as [[y v] [Heq Hin]].
      cbn [fst] in Heq; subst y.
      destruct (frozen_region p roots st x v Hin) as [r [Hr Hkey]].
      apply in_flat_map; exists r; split; [exact Hr|exact Hkey]. }
    pose proof (finite_sum_incl_nodup _ (fun _ => 1) _ _
      (frozen_nodup p roots st) Hincl) as Hlength.
    rewrite !finite_sum_one, length_map, finite_flat_map_length in Hlength.
    exact Hlength.
  Qed.

  Lemma discovery_finish_lengths : forall p roots fuel st ks rs fz finished,
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished ->
    length (discovery_missing finished) + length (discovery_rows finished) +
      length (discovery_frozen finished) <=
      length roots + 3 * finite_sum (fun r => length (row_keys p r))
        (region p roots st).
  Proof.
    intros p roots fuel st ks rs fz finished Hwf Hrun Hloop.
    destruct (discovery_result_done_perm p roots fuel st ks rs fz Hrun)
      as [final [Hfinal [Hperm Hnodup]]].
    rewrite Hloop in Hfinal; injection Hfinal as <-.
    destruct (discovery_done_charge p roots fuel st ks rs fz finished
      Hwf Hrun Hperm Hnodup) as [_ Hdone].
    pose proof (discovery_frozen_length_charge p roots st) as Hfrozen.
    pose proof (discovery_rows_length_charge p (region p roots st)) as Hrows.
    assert (Hparts : ks = rev (discovery_missing finished) /\
      rs = rev (discovery_rows finished) /\
      fz = rev (discovery_frozen finished)).
    { rewrite discovery_rev_equation in Hrun; rewrite Hloop in Hrun.
      cbn in Hrun; injection Hrun as <- <- <-; repeat split; reflexivity. }
    destruct Hparts as [Hks [Hrs Hfz]].
    destruct (discovery_views p roots fuel st ks rs fz Hwf Hrun)
      as [_ [Hregion Hfrozen_view]].
    rewrite Hrs in Hregion; rewrite Hfz in Hfrozen_view.
    assert (Hmissing_len : length (discovery_missing finished) =
      length (discovery_done finished)).
    { pose proof (Permutation_length Hperm) as Hlen.
      rewrite length_rev in Hlen; rewrite Hks in Hlen; rewrite length_rev in Hlen.
      exact (eq_sym Hlen). }
    rewrite <- Hmissing_len in Hdone.
    rewrite <- Hregion in Hrows; rewrite length_rev in Hrows.
    rewrite Hregion in Hrows.
    rewrite <- Hfrozen_view in Hfrozen; rewrite length_rev in Hfrozen.
    lia.
  Qed.

  Lemma discovery_spent_arithmetic : forall base q d t l r u,
    (d <= t + q * u)%N -> (l <= r + q)%N ->
    (128 * base * q * u + 128 * base * d + 128 * base * l * u <=
      512 * base * (q + r + 1) * u + 512 * base * t)%N.
  Proof.
    intros base q d t l r u Hd Hl.
    assert (Hd' : (128 * base * d <= 128 * base * (t + q * u))%N).
    { apply N.mul_le_mono_l; exact Hd. }
    assert (Hl' : (128 * base * l * u <= 128 * base * (r + q) * u)%N).
    { apply N.mul_le_mono_r, N.mul_le_mono_l; exact Hl. }
    eapply N.le_trans with
      (m := (128 * base * q * u + 128 * base * (t + q * u) +
        128 * base * (r + q) * u)%N); [lia|].
    replace (128 * base * q * u + 128 * base * (t + q * u) +
      128 * base * (r + q) * u)%N with
      (384 * base * q * u + 128 * base * r * u + 128 * base * t)%N by ring.
    replace (512 * base * (q + r + 1) * u + 512 * base * t)%N with
      (512 * base * q * u + 512 * base * r * u +
       512 * base * u + 512 * base * t)%N by ring.
    nia.
  Qed.

  Lemma discovery_spent_view_le : forall p roots fuel st ks rs fz
      (finished : incremental_discovery S.key S.row L.t),
    S.wf p -> discovery p roots fuel st = Some (ks, rs, fz) ->
    loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished ->
    Permutation (discovery_done finished) (rev ks) ->
    NoDup (discovery_done finished) ->
    (discovery_spent p st finished <=
      512 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (finite_sum (fun r => length (row_keys p r))
          (region p roots st) + length roots + 1) *
        N.of_nat (width p st + 1) +
      512 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat) roots))%N.
  Proof.
    intros p roots fuel st ks rs fz finished Hwf Hrun Hloop Hperm Hnodup.
    destruct (discovery_done_charge p roots fuel st ks rs fz finished
      Hwf Hrun Hperm Hnodup) as [Hbits Hlen].
    assert (Hraw : rs = rev (discovery_rows finished)).
    { rewrite discovery_rev_equation in Hrun; rewrite Hloop in Hrun.
      cbn in Hrun; now injection Hrun as _ <- _. }
    assert (Hregion : finite_sum (fun r => length (row_keys p r))
      (discovery_rows finished) =
      finite_sum (fun r => length (row_keys p r)) (region p roots st)).
    { rewrite <- (discovery_result_view_rows p roots fuel st ks rs fz Hwf Hrun).
      rewrite Hraw; symmetry; apply finite_sum_rev_local. }
    unfold discovery_spent; rewrite Hregion.
    set (base := (S.c_sys + S.c_loc + PTrieT.c_trie + 1)%N).
    set (q := N.of_nat (finite_sum (fun r => length (row_keys p r))
      (region p roots st))).
    set (d := N.of_nat (finite_sum (fun x => S.key_bits x + 1)
      (discovery_done finished))).
    set (t := N.of_nat (finite_sum (fun x => S.key_bits x + 1) roots)).
    set (l := N.of_nat (length (discovery_done finished))).
    set (r := N.of_nat (length roots)).
    set (u := N.of_nat (width p st + 1)).
    assert (Hd : (d <= t + q * u)%N).
    { unfold d, t, q, u; rewrite <- Nat2N.inj_mul, <- Nat2N.inj_add; lia. }
    assert (Hl : (l <= r + q)%N).
    { unfold l, r, q; rewrite <- Nat2N.inj_add; lia. }
    pose proof (discovery_spent_arithmetic base q d t l r u Hd Hl) as Hbudget.
    rewrite !Nat2N.inj_add.
    change (N.of_nat 1) with 1%N.
    exact Hbudget.
  Qed.

  Lemma discovery_spent_monotone : forall p st acc next,
    discovery_step p st acc = inl next ->
    (discovery_spent p st acc <= discovery_spent p st next)%N.
  Proof.
    intros p st acc next Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending.
    - unfold discovery_step in Hstep; rewrite Hpending in Hstep; discriminate.
    - rewrite (discovery_spent_step p st acc next x pending Hpending Hstep); lia.
  Qed.

  Lemma discovery_completion_spent : forall p st n acc finished,
    loop_fuel (discovery_step p st) n acc = inr finished ->
    (discovery_spent p st acc <= discovery_spent p st finished)%N.
  Proof.
    intros p st n; induction n as [|n IH]; intros acc finished Hrun;
      [discriminate Hrun|].
    cbn [loop_fuel] in Hrun.
    destruct (discovery_step p st acc) as [next|result] eqn:Hstep.
    - eapply N.le_trans; [apply discovery_spent_monotone; exact Hstep|].
      eapply IH; exact Hrun.
    - injection Hrun as <-.
      unfold discovery_step in Hstep.
      destruct (discovery_pending acc); [injection Hstep as <-; apply N.le_refl|].
      discriminate Hstep.
  Qed.

  Lemma discovery_completion_tail : forall p st n acc finished next,
    loop_fuel (discovery_step p st) n acc = inr finished ->
    discovery_step p st acc = inl next ->
    exists m, loop_fuel (discovery_step p st) m next = inr finished.
  Proof.
    intros p st [|n] acc finished next Hrun Hstep; [discriminate Hrun|].
    cbn [loop_fuel] in Hrun; rewrite Hstep in Hrun.
    exists n; exact Hrun.
  Qed.

  Definition discovery_potential (p : S.prog) (st : state)
      (finished acc : incremental_discovery S.key S.row L.t) : N :=
    (discovery_spent p st finished - discovery_spent p st acc +
      128 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (width p st + 1))%N.

  Lemma discovery_step_credit : forall p st acc next,
    S.wf p -> discovery_step p st acc = inl next ->
    (T_discovery_step p st acc + c_loopN + discovery_spent p st acc <=
      discovery_spent p st next)%N.
  Proof.
    intros p st acc next Hwf Hstep.
    destruct (discovery_pending acc) as [|x pending] eqn:Hpending.
    - unfold discovery_step in Hstep; rewrite Hpending in Hstep; discriminate.
    - pose proof (T_discovery_step_le p st acc Hwf) as Htime.
      rewrite Hpending in Htime.
      rewrite (discovery_spent_step p st acc next x pending Hpending Hstep).
      unfold c_loopN.
      set (base := (S.c_sys + S.c_loc + PTrieT.c_trie + 1)%N).
      set (u := N.of_nat (width p st + 1)).
      assert (Hunit : (8 <= 64 * base * u)%N).
      { unfold base, u, PTrieT.c_trie; nia. }
      unfold finite_sum in Htime.
      fold base u in Htime.
      pose (q := N.of_nat (fold_right Nat.add 0%nat
        (map (fun r => length (row_keys p r)) (S.rows_of p x)))).
      pose (k := N.of_nat (S.key_bits x + 1)).
      fold q k in Htime.
      unfold finite_sum.
      fold q k.
      assert (Hallow : (64 * base * q * u + 64 * base * k + 64 * base * u + 8 <=
        128 * base * q * u + 128 * base * k + 128 * base * u)%N).
      { replace (128 * base * q * u + 128 * base * k + 128 * base * u)%N with
          (64 * base * q * u + 64 * base * k + 64 * base * u +
           64 * base * q * u + 64 * base * k + 64 * base * u)%N by ring.
        lia. }
      lia.
  Qed.

  Lemma discovery_loop_clock : forall p st initial finished fuel, S.wf p ->
    (exists n, loop_fuel (discovery_step p st) n initial = inr finished) ->
    (T_loopN (discovery_step p st)
      (fun current => T_discovery_step p st current) fuel initial <=
      discovery_potential p st finished initial +
        c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
  Proof.
    intros p st initial finished fuel Hwf Hfinished.
    pose proof (T_loopN_amort _ _ (discovery_step p st)
      (fun current => T_discovery_step p st current)
      (fun acc => exists n, loop_fuel (discovery_step p st) n acc = inr finished)
      (discovery_potential p st finished) (fun _ => 0%N) fuel initial)
      as Hamort.
    assert (Hgo : forall acc next,
      (exists n, loop_fuel (discovery_step p st) n acc = inr finished) ->
      discovery_step p st acc = inl next ->
      (exists n, loop_fuel (discovery_step p st) n next = inr finished) /\
      (T_discovery_step p st acc + c_loopN +
        discovery_potential p st finished next <=
        discovery_potential p st finished acc)%N).
    { intros acc next [n Hcomplete] Hstep.
      destruct (discovery_completion_tail p st n acc finished next Hcomplete Hstep)
        as [m Htail].
      split; [now exists m|].
      pose proof (discovery_completion_spent p st n acc finished Hcomplete) as Hacc.
      pose proof (discovery_completion_spent p st m next finished Htail) as Hnext.
      pose proof (discovery_step_credit p st acc next Hwf Hstep) as Hcredit.
      unfold discovery_potential; lia. }
    assert (Hstop : forall acc result,
      (exists n, loop_fuel (discovery_step p st) n acc = inr finished) ->
      discovery_step p st acc = inr result ->
      (T_discovery_step p st acc + c_loopN + 0 <=
        discovery_potential p st finished acc)%N).
    { intros acc result [n Hcomplete] Hstep.
      pose proof (discovery_completion_spent p st n acc finished Hcomplete) as Hspent.
      pose proof (T_discovery_step_le p st acc Hwf) as Htime.
      unfold discovery_step in Hstep.
      destruct (discovery_pending acc) as [|x rest] eqn:Hpending;
        [|discriminate Hstep].
      unfold discovery_potential, c_loopN in *.
      assert (Hunit : (8 <= 64 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (width p st + 1))%N).
      { unfold PTrieT.c_trie; nia. }
      lia. }
    specialize (Hamort Hgo Hstop Hfinished).
    assert (Hzero : (match loopN (discovery_step p st) fuel initial with
      | inl _ => 0%N
      | inr r => (fun _ : incremental_discovery S.key S.row L.t => 0%N) r
      end) = 0%N).
    { destruct (loopN (discovery_step p st) fuel initial); reflexivity. }
    cbn beta in Hamort.
    rewrite Hzero in Hamort; lia.
  Qed.

  Lemma discovery_clock_arithmetic : forall Q T U F BF seed loop spent,
    (U <= Q)%N -> (1 <= U)%N -> (F <= BF)%N ->
    (seed <= 24 * T + 1)%N ->
    (spent <= 512 * Q + 512 * T)%N ->
    (loop <= spent + 128 * U + 8 * (F + 1))%N ->
    (1 + seed + loop <= 1024 * Q + 1024 * T + 1024 * BF)%N.
  Proof.
    intros Q T U F BF seed loop spent Hsub Hunit Hfuel Hseed Hspent Hloop.
    lia.
  Qed.

  Lemma discovery_clock_with_output : forall Q T U F BF seed loop spent output,
    (U <= Q)%N -> (1 <= U)%N -> (F <= BF)%N ->
    (seed <= 24 * T + 1)%N ->
    (spent <= 512 * Q + 512 * T)%N ->
    (loop <= spent + 128 * U + 8 * (F + 1))%N ->
    (output <= 16 * Q)%N ->
    (1 + seed + loop + output <= 1024 * Q + 1024 * T + 1024 * BF)%N.
  Proof.
    intros Q T U F BF seed loop spent output Hsub Hunit Hfuel Hseed Hspent
      Hloop Houtput.
    lia.
  Qed.

  Lemma discovery_output_clock_le : forall p roots fuel st result,
    S.wf p ->
    loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr result ->
    (1 + List.T_rev_append (discovery_missing result) [] +
      (1 + List.T_rev_append (discovery_rows result) []) +
      (1 + List.T_rev_append (discovery_frozen result) []) <=
      16 * N.of_nat (finite_sum (fun r => length (row_keys p r))
        (region p roots st) + length roots + 1))%N.
  Proof.
    intros p roots fuel st result Hwf Hloop.
    pose proof (List.T_rev_append_le (discovery_missing result) []) as Hkeys.
    pose proof (List.T_rev_append_le (discovery_rows result) []) as Hrows.
    pose proof (List.T_rev_append_le (discovery_frozen result) []) as Hfrozen.
    assert (Hrun : discovery p roots fuel st =
      Some (rev (discovery_missing result), rev (discovery_rows result),
        rev (discovery_frozen result))).
    { rewrite discovery_rev_equation; now rewrite Hloop. }
    pose proof (discovery_finish_lengths p roots fuel st
      (rev (discovery_missing result)) (rev (discovery_rows result))
      (rev (discovery_frozen result)) result Hwf Hrun Hloop) as Hlength.
    set (r := finite_sum (fun row => length (row_keys p row))
      (region p roots st)) in Hlength |- *.
    set (a := length (discovery_missing result)) in Hlength |- *.
    fold a in Hkeys.
    set (b := length (discovery_rows result)) in Hlength |- *.
    fold b in Hrows.
    set (c := length (discovery_frozen result)) in Hlength |- *.
    fold c in Hfrozen.
    assert (HlengthN : (N.of_nat (a + b + c) <=
      N.of_nat (length roots + 3 * r))%N) by lia.
    rewrite !Nat2N.inj_add in HlengthN |- *.
    cbn [N.of_nat] in HlengthN |- *.
    lia.
  Qed.

  Lemma discovery_row_sum_equation : forall p rs,
    finite_sum (fun r => length (row_keys p r)) rs =
    fold_right Nat.add 0%nat
      (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) rs).
  Proof.
    intros p rs; induction rs as [|r rest IH]; [reflexivity|].
    change (finite_sum (fun q => length (row_keys p q)) (r :: rest)) with
      (length (row_keys p r) + finite_sum
        (fun q => length (row_keys p q)) rest).
    cbn [fold_right map]; rewrite IH.
    unfold row_keys, row_writes; rewrite length_app; cbn [length]; lia.
  Qed.

  Local Opaque T_loopN.

  Lemma discovery_loop_total_le : forall p roots fuel st, S.wf p ->
    (T_loopN (discovery_step p st)
      (fun current => T_discovery_step p st current) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) <=
      512 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat ((fold_right Nat.add 0%nat
          (map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
            (region p roots st)) + length roots + 1)%nat) *
        N.of_nat (width p st + 1) +
      512 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat) roots) +
      128 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (width p st + 1) +
      c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
  Proof.
    intros p roots fuel st Hwf.
    destruct (discovery p roots (view_fuel p roots) st) as [[[vk vr] vf]|]
      eqn:Hview.
    2: { exfalso; exact (discovery_view_finishes p roots st Hwf Hview). }
    destruct (discovery_result_done_perm p roots (view_fuel p roots) st vk vr vf
      Hview) as [finished [Hfinish [Hperm Hnodup]]].
    pose proof (discovery_spent_view_le p roots (view_fuel p roots) st
      vk vr vf finished Hwf Hview Hfinish Hperm Hnodup) as Hspent.
    rewrite (discovery_row_sum_equation p (region p roots st)) in Hspent.
    pose proof (discovery_loop_clock p st
      (fold_left (discovery_seed_one st) roots empty_discovery)
      finished fuel Hwf) as Hclock.
    assert (Hcomplete : exists n, loop_fuel (discovery_step p st) n
      (fold_left (discovery_seed_one st) roots empty_discovery) = inr finished).
    { exists (N.to_nat (view_fuel p roots)).
      rewrite <- incremental_loopN_fuel; exact Hfinish. }
    specialize (Hclock Hcomplete).
    unfold discovery_potential in Hclock; lia.
  Qed.

  Lemma T_discovery_le : forall p roots fuel st, S.wf p ->
    (T_discovery p roots fuel st <=
      c_inc * N.of_nat ((fold_right Nat.add 0%nat
        (map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
          (region p roots st)) + length roots + 1)%nat) *
        N.of_nat (width p st + 1) +
      c_inc * N.of_nat (fold_right Nat.add 0%nat
        (map (fun x => S.key_bits x + 1)%nat roots)) +
      c_inc * N.of_nat (N.size_nat fuel))%N.
  Proof.
    intros p roots fuel st Hwf.
    pose proof (T_discovery_seed_fold_le st roots empty_discovery) as Hseed.
    pose proof (discovery_loop_total_le p roots fuel st Hwf) as Hclock.
    unfold T_discovery; time_simpl; time_cbn.
    set (output := match loopN (discovery_step p st) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery) with
      | inl _ => 0%N
      | inr result => (1 + List.T_rev_append (discovery_missing result) [] +
          (1 + List.T_rev_append (discovery_rows result) []) +
          (1 + List.T_rev_append (discovery_frozen result) []))%N
      end).
    assert (Hout : (output <= 16 * N.of_nat
      (finite_sum (fun r => length (row_keys p r)) (region p roots st) +
        length roots + 1))%N).
    { unfold output.
      destruct (loopN (discovery_step p st) fuel
        (fold_left (discovery_seed_one st) roots empty_discovery))
        as [partial|result] eqn:Hresult; [lia|].
      eapply discovery_output_clock_le; eauto. }
    rewrite (discovery_row_sum_equation p (region p roots st)) in Hout.
    assert (Hrootsum : finite_sum (fun x => (S.key_bits x + 1)%nat) roots =
      fold_right Nat.add 0%nat
        (map (fun x => (S.key_bits x + 1)%nat) roots)) by reflexivity.
    rewrite Hrootsum in Hclock.
    set (base := (S.c_sys + S.c_loc + PTrieT.c_trie + 1)%N) in *.
    set (q := N.of_nat (fold_right Nat.add 0%nat
      (map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
        (region p roots st)) + length roots + 1)) in *.
    set (t := N.of_nat (fold_right Nat.add 0%nat
      (map (fun x => (S.key_bits x + 1)%nat) roots))) in *.
    set (u := N.of_nat (width p st + 1)) in *.
    set (f := N.of_nat (N.size_nat fuel)) in *.
    assert (Hbase : (1 <= base)%N) by (unfold base; lia).
    assert (Hq : (1 <= q)%N) by (unfold q; lia).
    assert (Hu : (1 <= u)%N) by (unfold u; lia).
    assert (Hqu : (base * u <= base * q * u)%N).
    { replace (base * q * u)%N with (base * u * q)%N by ring.
      set (w := (base * u)%N); nia. }
    assert (Hunit : (1 <= base * u)%N) by nia.
    assert (Hfuel : (f <= base * f)%N) by nia.
    assert (HqQ : (q <= base * q * u)%N).
    { replace (base * q * u)%N with (q * (base * u))%N by ring.
      set (w := (base * u)%N) in Hunit |- *; nia. }
    assert (HoutQ : (output <= 16 * (base * q * u))%N).
    { eapply N.le_trans; [exact Hout|].
      apply N.mul_le_mono_l; exact HqQ. }
    replace (512 * base * q * u)%N with
      (512 * (base * q * u))%N in Hclock by ring.
    replace (512 * base * t)%N with (512 * (base * t))%N in Hclock by ring.
    replace (128 * base * u)%N with (128 * (base * u))%N in Hclock by ring.
    replace (24 * base * t)%N with (24 * (base * t))%N in Hseed by ring.
    unfold c_loopN in Hclock.
    replace (N.of_nat (N.size_nat fuel + 1)) with (f + 1)%N in Hclock.
    2: { unfold f; rewrite Nat2N.inj_add; reflexivity. }
    set (seed := List.T_fold_left (discovery_seed_one st)
      (fun current x => T_discovery_seed_one st current x)
      roots empty_discovery) in Hseed |- *.
    set (clock := T_loopN (discovery_step p st)
      (fun current => T_discovery_step p st current) fuel
      (fold_left (discovery_seed_one st) roots empty_discovery)) in Hclock |- *.
    clearbody seed clock output.
    replace (1 + (seed + (clock + output)))%N with
      (1 + seed + clock + output)%N by ring.
    pose proof (discovery_clock_with_output (base * q * u)%N (base * t)%N
      (base * u)%N f (base * f)%N seed clock
      (512 * (base * q * u) + 512 * (base * t))%N output) as Hbudget.
    specialize (Hbudget Hqu).
    specialize (Hbudget Hunit).
    specialize (Hbudget Hfuel).
    specialize (Hbudget Hseed).
    specialize (Hbudget (N.le_refl _)).
    specialize (Hbudget Hclock).
    specialize (Hbudget HoutQ).
    clearbody q t u f.
    eapply N.le_trans; [exact Hbudget|].
    unfold c_inc, base.
    match goal with
    | |- (?lhs <= ?rhs)%N => replace rhs with lhs by ring; apply N.le_refl
    end.
  Qed.

  Lemma T_invalid_seed_one_le : forall st acc x,
    (T_invalid_seed_one st acc x <=
      20 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros st acc x.
    pose proof (T_value_small_le st x) as Hvalue.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le unit (S.key_code x) (invalid_seen acc)) as Hget.
    pose proof (PTrieT.T_set_le unit (S.key_code x) tt (invalid_seen acc)) as Hset.
    unfold PTrieT.T_get in Hget; unfold PTrieT.T_set in Hset.
    unfold T_invalid_seed_one, T_present, PTrieCode.T_get, PTrieCode.T_set,
      S.key_bits in *.
    destruct (present st x);
      destruct (PTrieCode.get (S.key_code x) (invalid_seen acc)) as [[]|];
      time_simpl; time_cbn; nia.
  Qed.

  Lemma T_invalid_seed_fold_le : forall st xs acc,
    (List.T_fold_left (invalid_seed_one st)
      (fun current x => T_invalid_seed_one st current x) xs acc <=
      24 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat) xs) + 1)%N.
  Proof.
    intros st xs acc.
    destruct (fold_left_inv_time (invalid_seed_one st)
      (fun current x => T_invalid_seed_one st current x)
      (fun _ => True)
      (fun x => (20 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1))%N) xs acc I) as [_ Hfold].
    { intros current x _ _; split; [exact I|apply T_invalid_seed_one_le]. }
    assert (Hsum : forall ys,
      (fold_right (fun x total =>
        20 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (S.key_bits x + 1) + 2 + total)%N 1%N ys <=
        24 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
          N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat) ys) + 1)%N).
    { induction ys as [|x rest IH]; [cbn; lia|].
      unfold finite_sum in *; cbn [map fold_right].
      rewrite Nat2N.inj_add.
      pose proof (Pos2Nat.is_pos (S.key_code x)) as Hpositive.
      unfold S.key_bits in *; nia. }
    eapply N.le_trans; [exact Hfold|apply Hsum].
  Qed.

  Lemma invalid_snapshot_get_budget : forall base bits cost,
    (1 + cost <= 1024 * bits)%N -> (1 <= bits)%N ->
    (1027 <= 64 * base)%N -> (4 + cost <= 64 * base * bits)%N.
  Proof.
    intros base bits cost Hget Hbits Hcoef.
    assert (Hsmall : (4 + cost <= 1027 * bits)%N) by lia.
    assert (Hscale : (1027 * bits <= 64 * base * bits)%N).
    { apply N.mul_le_mono_r; exact Hcoef. }
    exact (N.le_trans _ _ _ Hsmall Hscale).
  Qed.

  Lemma invalid_snapshot_live_budget : forall base bits work get set fold,
    (1 + get <= 1024 * bits)%N -> (1 + set <= 1024 * bits)%N ->
    (fold <= 24 * base * work + 1)%N -> (1 <= bits)%N ->
    (1025 <= base)%N ->
    (16 + get + fold + set <= 64 * base * (bits + work))%N.
  Proof.
    intros base bits work get set fold Hget Hset Hfold Hbits Hbase.
    assert (Hscale : (1024 * bits <= base * bits)%N).
    { apply N.mul_le_mono_r; lia. }
    assert (Hunit : (1 <= base * bits)%N) by nia.
    replace (64 * base * (bits + work))%N with
      (64 * (base * bits) + 64 * (base * work))%N by ring.
    set (q := (base * bits)%N) in Hscale, Hunit |- *.
    set (w := (base * work)%N) in Hfold |- *.
    lia.
  Qed.

  Lemma T_invalid_visit_snapshot_le : forall st acc id,
    (T_invalid_visit_snapshot st acc id <=
      64 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        (N.of_nat (Pos.size_nat id + 1) +
          match PTrieCode.get id (invalid_snapshots acc) with
          | Some ss => if snapshot_live ss then
              N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat)
                (snapshot_writes ss))
            else 0%N
          | None => 0%N
          end))%N.
  Proof.
    intros st acc id.
    pose proof (PTrieT.T_get_le (incremental_snapshot S.key) id
      (invalid_snapshots acc)) as Hget.
    unfold PTrieT.T_get in Hget.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|] eqn:Hsnapshot.
    2: { unfold T_invalid_visit_snapshot, PTrieCode.T_get.
         rewrite Hsnapshot; time_simpl; time_cbn.
         set (bits := N.of_nat (Pos.size_nat id + 1)) in *.
         assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
         unfold PTrieT.c_trie in Hget |- *.
         replace (1 + (1 + (1 + T_trie_get id (invalid_snapshots acc)) + 0))%N
           with (3 + T_trie_get id (invalid_snapshots acc))%N by ring.
         rewrite N.add_0_r.
         eapply N.le_trans with
           (m := (4 + T_trie_get id (invalid_snapshots acc))%N); [lia|].
         apply invalid_snapshot_get_budget; [exact Hget|exact Hbits|lia]. }
    destruct (snapshot_live ss) eqn:Hlive.
    2: { unfold T_invalid_visit_snapshot, PTrieCode.T_get.
         rewrite Hsnapshot, Hlive; time_simpl; time_cbn.
         set (bits := N.of_nat (Pos.size_nat id + 1)) in *.
         assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
         unfold PTrieT.c_trie in Hget |- *.
         eapply N.le_trans with
           (m := (4 + T_trie_get id (invalid_snapshots acc))%N).
         1: lia.
         rewrite N.add_0_r.
         apply invalid_snapshot_get_budget; [exact Hget|exact Hbits|lia]. }
    pose proof (T_invalid_seed_fold_le st (snapshot_writes ss) acc) as Hfold.
    pose proof (PTrieT.T_set_le (incremental_snapshot S.key) id
      {| snapshot_owner := snapshot_owner ss;
         snapshot_writes := snapshot_writes ss;
         snapshot_live := false |}
      (invalid_snapshots
        (fold_left (invalid_seed_one st) (snapshot_writes ss) acc))) as Hset.
    unfold PTrieT.T_set in Hset.
    unfold T_invalid_visit_snapshot, PTrieCode.T_get, PTrieCode.T_set.
    rewrite Hsnapshot, Hlive; time_simpl; time_cbn.
    unfold PTrieT.c_trie in Hget, Hset, Hfold |- *.
    set (bits := N.of_nat (Pos.size_nat id + 1)) in Hget, Hset |- *.
    set (work := N.of_nat (finite_sum (fun x => (S.key_bits x + 1)%nat)
      (snapshot_writes ss))) in Hfold |- *.
    set (base := (S.c_sys + S.c_loc + 1024 + 1)%N) in Hfold |- *.
    set (tg := T_trie_get id (invalid_snapshots acc)) in Hget |- *.
    set (tf := List.T_fold_left (invalid_seed_one st)
      (fun current x => T_invalid_seed_one st current x)
      (snapshot_writes ss) acc) in Hfold |- *.
    set (next := fold_left (invalid_seed_one st) (snapshot_writes ss) acc)
      in Hset |- *.
    set (ts := PTrieCode.T_replace id
      (Some {| snapshot_owner := snapshot_owner ss;
               snapshot_writes := snapshot_writes ss;
               snapshot_live := false |}) (invalid_snapshots next)) in Hset |- *.
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hbase : (1025 <= base)%N) by (unfold base; lia).
    match goal with
    | |- (?clock <= ?budget)%N =>
      assert (Hclock : (clock <= 16 + tg + tf + ts)%N)
        by (clear Hget Hset Hfold; lia);
      eapply N.le_trans; [exact Hclock|]
    end.
    eapply invalid_snapshot_live_budget;
      [exact Hget|exact Hset|exact Hfold|exact Hbits|exact Hbase].
  Qed.

  Lemma invalid_next_budget : forall a b c bits n code read write app fold,
    (code <= a * bits)%N -> (read <= c * bits)%N ->
    (write <= c * bits)%N -> (app <= n)%N -> (1 <= bits)%N ->
    (1 + (code + 1 + read + (code + 1 + write + (app + fold))) <=
      16 * (a + b + c + 1) * bits + 4 * n + fold)%N.
  Proof.
    intros a b c bits n code read write app fold Hcode Hread Hwrite Happ Hbits.
    replace (16 * (a + b + c + 1) * bits)%N with
      (16 * (a * bits) + 16 * (b * bits) +
        16 * (c * bits) + 16 * bits)%N by ring.
    nia.
  Qed.

  Lemma T_invalid_next_le : forall st x pending seen bad done snapshots,
    let readers := match PTrieCode.get (S.key_code x) (inc_influence st) with
      | Some ids => ids | None => [] end in
    let cowriters := match PTrieCode.get (S.key_code x) (inc_cowrites st) with
      | Some ids => ids | None => [] end in
    let rest := {| invalid_pending := pending; invalid_seen := seen;
      invalid_bad := bad; invalid_done := x :: done;
      invalid_snapshots := snapshots |} in
    (T_invalid_next st x pending seen bad done snapshots <=
      16 * (S.c_sys + S.c_loc + PTrieT.c_trie + 1) *
        N.of_nat (S.key_bits x + 1) +
      4 * N.of_nat (length readers + 1) +
      List.T_fold_left (invalid_visit_snapshot st)
        (fun current id => T_invalid_visit_snapshot st current id)
        (readers ++ cowriters) rest)%N.
  Proof.
    intros st x pending seen bad done snapshots.
    cbn beta zeta.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (list positive) (S.key_code x)
      (inc_influence st)) as Hread.
    pose proof (PTrieT.T_get_le (list positive) (S.key_code x)
      (inc_cowrites st)) as Hwrite.
    unfold PTrieT.T_get in Hread, Hwrite.
    destruct (PTrieCode.get (S.key_code x) (inc_influence st)) as [readers|]
      eqn:Hreaders;
      destruct (PTrieCode.get (S.key_code x) (inc_cowrites st)) as [cowriters|]
      eqn:Hcowriters.
    all: pose proof (Datatypes.T_app_le
      (match PTrieCode.get (S.key_code x) (inc_influence st) with
       | Some ids => ids | None => [] end)
      (match PTrieCode.get (S.key_code x) (inc_cowrites st) with
       | Some ids => ids | None => [] end)) as Happ.
    all: unfold T_invalid_next, PTrieCode.T_get, S.key_bits in *;
      rewrite Hreaders, Hcowriters in *; time_simpl; time_cbn.
    all: assert (HappN : (Datatypes.T_app
      (match PTrieCode.get (S.key_code x) (inc_influence st) with
       | Some ids => ids | None => [] end)
      (match PTrieCode.get (S.key_code x) (inc_cowrites st) with
       | Some ids => ids | None => [] end) <=
      N.of_nat (length (match PTrieCode.get (S.key_code x) (inc_influence st) with
        | Some ids => ids | None => [] end) + 1))%N)
      by (rewrite Hreaders, Hcowriters in *;
        rewrite Nat2N.inj_add; cbn [N.of_nat]; exact Happ).
    all: rewrite Hreaders, Hcowriters in HappN;
      assert (Hbits : (1 <= N.of_nat (Pos.size_nat (S.key_code x) + 1))%N)
        by lia;
      eapply invalid_next_budget;
        [exact Hcode|exact Hread|exact Hwrite|exact HappN|exact Hbits].
  Qed.

  Definition invalid_snapshot_mass (acc : incremental_invalidation S.key) : nat :=
    trie_sum DemandAccounting.snapshot_weight (invalid_snapshots acc).

  Lemma invalid_visit_snapshot_mass : forall st acc id,
    invalid_snapshot_mass (invalid_visit_snapshot st acc id) +
      match PTrieCode.get id (invalid_snapshots acc) with
      | Some ss => DemandAccounting.snapshot_weight ss
      | None => 0
      end = invalid_snapshot_mass acc.
  Proof.
    intros st acc id; unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|] eqn:Hget;
      [|lia].
    destruct (snapshot_live ss) eqn:Hlive.
    2: { unfold DemandAccounting.snapshot_weight; rewrite Hlive; lia. }
    unfold invalid_snapshot_mass; cbn [invalid_snapshots].
    rewrite invalid_seed_fold_snapshots.
    pose proof (trie_sum_set _ DemandAccounting.snapshot_weight id
      {| snapshot_owner := snapshot_owner ss;
         snapshot_writes := snapshot_writes ss;
         snapshot_live := false |} (invalid_snapshots acc)) as Hsum.
    rewrite Hget in Hsum.
    unfold DemandAccounting.snapshot_weight in *.
    rewrite Hlive in Hsum |- *; cbn [snapshot_live] in Hsum |- *; lia.
  Qed.

  Lemma invalid_snapshot_width : forall st acc id ss,
    state_ok st -> invalid_snapshot_origin st acc ->
    PTrieCode.get id (invalid_snapshots acc) = Some ss ->
    Pos.size_nat id <= kwidth st /\
      (forall x, In x (snapshot_writes ss) -> S.key_bits x <= kwidth st).
  Proof.
    intros st acc id ss Hstate Horigin Hget.
    destruct (Horigin id ss Hget) as [original [Horiginal [_ [Hwrites _]]]].
    assert (Hin : In (id, original) (snapshots st)).
    { apply Core.snapshot_get_elements; exact Horiginal. }
    split.
    - exact (snapshot_id_width st id original Hstate Hin).
    - intros x Hx; rewrite Hwrites in Hx.
      unfold kwidth; apply finite_max_member; apply in_or_app; right.
      unfold snapshot_keys; apply in_flat_map.
      exists (id, original); split; [exact Hin|exact Hx].
  Qed.

  Lemma finite_sum_key_bits_width : forall xs w,
    (forall x, In x xs -> S.key_bits x <= w) ->
    finite_sum (fun x => S.key_bits x + 1) xs <= length xs * (w + 1).
  Proof.
    intros xs; induction xs as [|x rest IH]; intros w Hwidth; [reflexivity|].
    change (finite_sum (fun y => S.key_bits y + 1) (x :: rest)) with
      (S.key_bits x + 1 + finite_sum (fun y => S.key_bits y + 1) rest).
    cbn [length].
    assert (Hhead : S.key_bits x <= w) by (apply Hwidth; now left).
    assert (Htail : forall y, In y rest -> S.key_bits y <= w).
    { intros y Hy; apply Hwidth; now right. }
    specialize (IH w Htail).
    nia.
  Qed.

  Lemma invalid_snapshot_bits_le : forall st acc id ss,
    state_ok st -> invalid_snapshot_origin st acc ->
    PTrieCode.get id (invalid_snapshots acc) = Some ss ->
    finite_sum (fun x => S.key_bits x + 1) (snapshot_writes ss) <=
      length (snapshot_writes ss) * (kwidth st + 1).
  Proof.
    intros st acc id ss Hstate Horigin Hget.
    apply finite_sum_key_bits_width.
    exact (proj2 (invalid_snapshot_width st acc id ss Hstate Horigin Hget)).
  Qed.

  Lemma infl_mass_weight : forall st, state_ok st ->
    infl_mass st = finite_sum (fun x =>
      infl_deg st x + length (cowrite_at st x) + 1) (stored st).
  Proof.
    intros st Hstate; unfold infl_mass.
    rewrite (cowrite_mass_pin st Hstate).
    change (finite_sum (fun x => infl_deg st x + 1) (stored st) +
      finite_sum (fun x => length (cowrite_at st x)) (stored st) =
      finite_sum (fun x => infl_deg st x + length (cowrite_at st x) + 1)
        (stored st)).
    rewrite <- finite_sum_plus.
    apply finite_sum_ext; intros x Hx; lia.
  Qed.

  Lemma infl_mass_release : forall p p' ch st, state_ok st ->
    infl_mass (edit p p' ch st) +
      fold_right Nat.add 0%nat (map (fun x =>
        infl_deg st x + length (cowrite_at st x) + 1) (invalidate p p' ch st)) <=
    infl_mass st.
  Proof.
    intros p p' ch st Hstate.
    pose proof (state_ok_edit p p' ch st Hstate) as Hstate'.
    assert (Hboth : NoDup (stored (edit p p' ch st) ++ invalidate p p' ch st)).
    { apply NoDup_app; [exact (stored_nodup _ Hstate')|apply invalidate_nodup|].
      intros x Hin Hbad.
      apply (proj1 (stored_spec (edit p p' ch st) x Hstate')) in Hin.
      apply (proj1 (edit_dom_keys p p' ch st x)) in Hin as [_ Hkeep].
      exact (Hkeep Hbad). }
    assert (Hsub : incl (stored (edit p p' ch st) ++ invalidate p p' ch st)
      (stored st)).
    { intros x Hin; apply in_app_iff in Hin as [Hin|Hin].
      - eapply EditMetadata.stored_edit_subset; exact Hin.
      - apply (proj2 (stored_spec st x Hstate)).
        eapply invalidate_dom; exact Hin. }
    pose proof (finite_sum_incl_nodup _
      (fun x => infl_deg st x + length (cowrite_at st x) + 1)
      _ _ Hboth Hsub) as Hsum.
    rewrite finite_sum_app in Hsum.
    assert (Hretained : finite_sum (fun x =>
        infl_deg (edit p p' ch st) x +
        length (cowrite_at (edit p p' ch st) x) + 1)
        (stored (edit p p' ch st)) =
      finite_sum (fun x => infl_deg st x + length (cowrite_at st x) + 1)
        (stored (edit p p' ch st))).
    { apply finite_sum_ext; intros x Hin.
      assert (Hdom : dom (edit p p' ch st) x).
      { apply (proj1 (stored_spec (edit p p' ch st) x Hstate')); exact Hin. }
      apply (proj1 (edit_dom_keys p p' ch st x)) in Hdom as [_ Hkeep].
      unfold infl_deg; rewrite EditMetadata.edit_infl_keeps.
      - pose proof (metadata_edit_cowrite p p' ch st x Hkeep) as Hcowrite.
        change (cowrite_at (edit p p' ch st) x = cowrite_at st x) in Hcowrite.
        now rewrite Hcowrite.
      - apply (proj1 (stored_spec (edit p p' ch st) x Hstate')); exact Hin. }
    rewrite (infl_mass_weight (edit p p' ch st) Hstate'),
      (infl_mass_weight st Hstate).
    unfold invalidate.
    change (finite_sum (fun x =>
      infl_deg (edit p p' ch st) x +
      length (cowrite_at (edit p p' ch st) x) + 1)
      (stored (edit p p' ch st)) +
      finite_sum (fun x => infl_deg st x + length (cowrite_at st x) + 1)
        (invalidate_keys p p' ch st) <=
      finite_sum (fun x => infl_deg st x + length (cowrite_at st x) + 1)
        (stored st)).
    rewrite Hretained; exact Hsum.
  Qed.

  Definition invalid_respects (P : S.key -> Prop)
      (acc : incremental_invalidation S.key) : Prop :=
    forall x, In x (invalid_bad acc ++ invalid_pending acc) -> P x.

  Lemma invalid_seed_respects : forall st P acc x,
    invalid_respects P acc -> (present st x = true -> P x) ->
    invalid_respects P (invalid_seed_one st acc x).
  Proof.
    intros st P acc x Hres Hnew; unfold invalid_seed_one.
    destruct (present st x) eqn:Hpresent; [|exact Hres].
    destruct (PTrieCode.get (S.key_code x) (invalid_seen acc));
      [exact Hres|].
    intros y Hy; cbn [invalid_bad invalid_pending] in Hy.
    apply in_app_iff in Hy as [[<-|Hy]|[<-|Hy]].
    - now apply Hnew.
    - apply Hres; apply in_app_iff; now left.
    - now apply Hnew.
    - apply Hres; apply in_app_iff; now right.
  Qed.

  Lemma invalid_seed_fold_respects : forall st P xs acc,
    invalid_respects P acc ->
    (forall x, In x xs -> present st x = true -> P x) ->
    invalid_respects P (fold_left (invalid_seed_one st) xs acc).
  Proof.
    intros st P xs; induction xs as [|x rest IH]; intros acc Hres Hnew;
      [exact Hres|].
    cbn [fold_left]; apply IH.
    - apply invalid_seed_respects; [exact Hres|].
      apply Hnew; now left.
    - intros y Hy; apply Hnew; now right.
  Qed.

  Lemma invalid_visit_respects : forall st P x id acc,
    invalid_snapshot_origin st acc -> invalid_respects P acc -> P x ->
    In id (invalid_buckets st x) ->
    (forall key ident ss y, P key -> In ident (invalid_buckets st key) ->
      In (ident, ss) (snapshots st) -> snapshot_live ss = true ->
      In y (snapshot_writes ss) -> dom st y -> P y) ->
    invalid_respects P (invalid_visit_snapshot st acc id).
  Proof.
    intros st P x id acc Horigin Hres Hx Hbucket Hclosed.
    unfold invalid_visit_snapshot.
    destruct (PTrieCode.get id (invalid_snapshots acc)) as [ss|]
      eqn:Hget; [|exact Hres].
    destruct (snapshot_live ss) eqn:Hlive; [|exact Hres].
    destruct (Horigin id ss Hget) as [original [Horig [_ [Hwrites Horiglive]]]].
    cbn [invalid_bad invalid_pending].
    apply invalid_seed_fold_respects; [exact Hres|].
    intros y Hy Hpresent.
    apply (Hclosed x id original y Hx Hbucket).
    - unfold snapshots; now apply PTrie.elements_spec.
    - exact (Horiglive Hlive).
    - rewrite <- Hwrites; exact Hy.
    - now apply (proj1 (present_spec st y)).
  Qed.

  Lemma invalid_snapshot_fold_respects : forall st P x ids acc,
    invalid_snapshot_origin st acc -> invalid_respects P acc -> P x ->
    (forall id, In id ids -> In id (invalid_buckets st x)) ->
    (forall key ident ss y, P key -> In ident (invalid_buckets st key) ->
      In (ident, ss) (snapshots st) -> snapshot_live ss = true ->
      In y (snapshot_writes ss) -> dom st y -> P y) ->
    invalid_respects P (fold_left (invalid_visit_snapshot st) ids acc).
  Proof.
    intros st P x ids; induction ids as [|id rest IH];
      intros acc Horigin Hres Hx Hids Hclosed; [exact Hres|].
    cbn [fold_left]; apply IH.
    - now apply invalid_visit_origin.
    - eapply invalid_visit_respects;
        [exact Horigin|exact Hres|exact Hx|apply Hids; now left|exact Hclosed].
    - exact Hx.
    - intros q Hq; apply Hids; now right.
    - exact Hclosed.
  Qed.

  Lemma invalidate_least : forall p p' ch st (P : S.key -> Prop),
    (forall r y, In r ch -> In y (S.writes p r ++ S.writes p' r) -> dom st y -> P y) ->
    (forall x id ss y, P x -> In id (infl_at st x ++ cowrite_at st x) ->
      In (id, ss) (snapshots st) -> snapshot_live ss = true ->
      In y (snapshot_writes ss) -> dom st y -> P y) ->
    forall x, In x (invalidate p p' ch st) -> P x.
  Proof.
    intros p p' ch st P Hseed Hclosed x Hbad.
    assert (Hclosure : forall key ident ss y, P key ->
      In ident (invalid_buckets st key) ->
      In (ident, ss) (snapshots st) -> snapshot_live ss = true ->
      In y (snapshot_writes ss) -> dom st y -> P y).
    { intros key ident ss y Hkey Hids Hss Hlive Hy Hdom.
      apply (Hclosed key ident ss y Hkey); assumption. }
    assert (Hinitial : invalid_respects P (invalid_initial p p' ch st) /\
      invalid_snapshot_origin st (invalid_initial p p' ch st)).
    { unfold invalid_initial; split.
      - apply invalid_seed_fold_respects.
        + intros y Hy; cbn [invalid_bad invalid_pending] in Hy; contradiction.
        + intros y Hy Hpresent.
          unfold changed_keys in Hy; apply in_flat_map in Hy as [r [Hr Hy]].
          apply (Hseed r y Hr Hy).
          now apply (proj1 (present_spec st y)).
      - apply invalid_seed_fold_origin.
        intros id current Hget; exists current.
        cbn [invalid_snapshots] in Hget; split; [exact Hget|].
        split; [reflexivity|].
        split; [reflexivity|tauto]. }
    assert (Hresult : invalid_respects P (invalid_walk p p' ch st)).
    { unfold invalid_walk.
      eapply incremental_loop_preserves with
        (Inv := fun acc => invalid_respects P acc /\ invalid_snapshot_origin st acc)
        (Post := invalid_respects P); [|exact Hinitial].
      intros [pending0 seen bad done snapshots] [Hres Horigin].
      destruct pending0 as [|key pending]; cbn [invalid_checked_step];
        [exact Hres|].
      unfold invalid_next; split.
      - eapply invalid_snapshot_fold_respects.
        + exact Horigin.
        + intros y Hy; apply Hres.
          apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff;
            [now left|right; now right].
        + apply Hres; apply in_app_iff; right; now left.
        + intros id Hid; exact Hid.
        + exact Hclosure.
      - apply invalid_snapshot_fold_origin; exact Horigin. }
    apply Hresult; apply in_app_iff; left.
    exact Hbad.
  Qed.

End IncrementalT.
