(** * Tarjan invariants on the actual search trace

    Every shared-search trace prefix preserves Tarjan's low-link and ownership invariants.
    For example, each complete root invocation leaves its pending Tarjan stack empty.
    Builds on: GraphTarjanLowStep and the public Search trace and numbering guarantees. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchExact GraphSearchOrder GraphTarjan GraphTarjanState
  GraphTarjanBookkeeping GraphTarjanLow GraphTarjanLowStep.
Import List.ListNotations.

Module TarjanTrace.

(** Shared search maintains its own storage, numbering history and scoped frame validity. *)
Record search_state {V E} (p : Prepared.t V E) scope roots (w : SearchRun.work E) : Prop :=
  SearchState {
    representation : SearchInvariant.representation (snd w);
    history : SearchInvariant.history w;
    sound : SearchInvariant.sound_work p scope roots w
  }.

(** Adjacent open vertices retain the actual parent-to-child arc selected by their entry. *)
Fixpoint tree_edges {V E} (p : Prepared.t V E) (open : list positive) : Prop :=
  match open with
  | [] => True
  | v :: rest =>
    (match rest with
    | [] => True
    | u :: _ => exists e, Prepared.arc p u e v
    end) /\ tree_edges p rest
  end.

(** Every emitted block is mutually reachable through admitted valid scoped paths. *)
Definition strong_output {V E} (p : Prepared.t V E) scope (s : Tarjan.state) :=
  forall c, In c (Tarjan.emitted_rev s) ->
    forall u v, In u c -> In v c ->
      TarjanLow.reaches p scope u v /\ TarjanLow.reaches p scope v u.

(** Prefix invariants couple the same search core, open vertices and visitor state. *)
Record invariant {V E} (p : Prepared.t V E) scope roots (w : SearchRun.work E)
    (s : Tarjan.state) : Prop := Invariant {
  search : search_state p scope roots w;
  discovery : TarjanStateFacts.discovery_agrees (snd w) s;
  low : TarjanLow.invariant p scope (map fst (fst w)) s;
  tree : tree_edges p (map fst (fst w));
  output : strong_output p scope s
}.

(** The initial actual core and visitor state satisfy the coupled prefix invariant. *)
Theorem initial_invariant {V E} (p : Prepared.t V E) scope roots :
  invariant p scope roots ([], @SearchRun.initial E) Tarjan.initial.
Proof.
  constructor.
  - constructor.
    + apply SearchInvariant.initial_representation.
    + apply SearchInvariant.initial_history.
    + constructor.
      * intros v Hfalse.
        change (FinSet.mem positive_encoding v FinSet.empty = true) in Hfalse.
        rewrite FinSet.mem_empty in Hfalse. discriminate.
      * intros u es Hfalse. contradiction.
  - split; reflexivity.
  - apply TarjanLow.initial_invariant.
  - exact I.
  - intros c Hfalse. contradiction.
Qed.

(** Actual trace blocks preserve the public search invariants without duplicating its driver. *)
Theorem step_search {V E} (p : Prepared.t V E) scope roots w here next :
  Prepared.ready p -> search_state p scope roots w ->
  SearchRun.trace_step p scope w here next -> search_state p scope roots next.
Proof.
  intros Hready [Hrep Hhistory Hsound] Htrace.
  pose proof (SearchOrder.trace_step_equation p scope w here next Htrace) as Hstep.
  pose proof (SearchInvariant.transition_representation p scope w Hrep) as Hrep'.
  pose proof (SearchInvariant.transition_history p scope w Hrep Hhistory) as Hhistory'.
  pose proof (SearchInvariant.transition_sound p scope roots w Hready Hrep Hsound) as Hsound'.
  rewrite Hstep in Hrep', Hhistory', Hsound'. constructor; assumption.
Qed.

(** A white actual target has no Tarjan discovery number in the synchronized prefix. *)
Theorem fresh_discovery {V E} (p : Prepared.t V E) scope roots w s v :
  invariant p scope roots w s ->
  FinSet.mem positive_encoding v (SearchRun.seen (snd w)) = false ->
    Map.get positive_encoding v (Tarjan.disc s) = None.
Proof.
  intros HI Hfresh. rewrite (proj1 (discovery _ _ _ _ _ HI)).
  destruct (Map.get positive_encoding v (SearchRun.pre_index (snd w))) as [n|] eqn:Hnumber;
    [|reflexivity].
  assert (Hin : In v (SearchRun.pre_rev (snd w))).
  { apply (SearchInvariant.numbering_domain _ _ _
      (SearchInvariant.pre_numbering _ (history _ _ _ _ (search _ _ _ _ _ HI)))).
    now exists n. }
  apply (SearchInvariant.seen_discovered _ (representation _ _ _ _ (search _ _ _ _ _ HI))) in Hin.
  congruence.
Qed.

(** A discovered open vertex is valid and admitted in the current scoped prefix. *)
Theorem open_domain {V E} (p : Prepared.t V E) scope roots w s v :
  invariant p scope roots w s -> In v (map fst (fst w)) ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intros HI Hv.
  pose proof (TarjanLow.book _ _ _ _ (low _ _ _ _ _ HI)) as Hbook.
  assert (Hpending : In v (Tarjan.stack s)) by
    exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) v Hv).
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook v) ltac:(apply in_or_app; now left))
    as [d Hvd].
  exact (TarjanLow.domain _ _ _ _ (low _ _ _ _ _ HI) v d Hvd).
Qed.

(** An admitted valid target turns an actual arc from an open source into a scoped path. *)
Theorem arc_reaches {V E} (p : Prepared.t V E) scope roots w s u e v :
  invariant p scope roots w s -> In u (map fst (fst w)) ->
  Prepared.arc p u e v -> Prepared.valid_id p v -> Scope.admits scope v = true ->
    TarjanLow.reaches p scope u v.
Proof.
  intros HI Hu Harc Hv Ha. destruct (open_domain p scope roots w s u HI Hu) as [Hvalid Hallowed].
  exists [e]. eapply Search.scoped_cons; [exact Hvalid|exact Hallowed|exact Harc|].
  now apply Search.scoped_nil.
Qed.

(** An exit uses the actual adjacent parent arc of the same open search stack. *)
Theorem exit_parent_path {V E} (p : Prepared.t V E) scope roots v rest c s :
  invariant p scope roots ((v, []) :: rest, c) s ->
  match rest with
  | [] => True
  | (u, es) :: _ => In u (map fst rest) /\ TarjanLow.reaches p scope u v
  end.
Proof.
  intro HI. destruct rest as [|[u es] rest]; [exact I|].
  split; [now left|].
  destruct (proj1 (tree _ _ _ _ _ HI)) as [e Harc].
  destruct (open_domain p scope roots _ s v HI (or_introl eq_refl)) as [Hv Ha].
  apply (arc_reaches p scope roots _ s u e v HI); [right; now left|exact Harc|exact Hv|exact Ha].
Qed.

Local Lemma lower_output {V E} (p : Prepared.t V E) scope s v n :
  strong_output p scope s -> strong_output p scope (Tarjan.lower v n s).
Proof.
  intro Houtput. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); exact Houtput.
Qed.

Local Lemma edge_output {V E} (p : Prepared.t V E) scope s u v k :
  strong_output p scope s -> strong_output p scope (Tarjan.edge u v k s).
Proof.
  intro Houtput. rewrite Tarjan.edge_equation. destruct k; try exact Houtput.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Houtput.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Houtput.
  all: now apply lower_output.
Qed.

(** Emission appends one block whose mutual reachability is proved from the local low-link invariant. *)
Theorem emit_output {V E} (p : Prepared.t V E) scope v open s :
  TarjanLow.invariant p scope (v :: open) s -> strong_output p scope s ->
    strong_output p scope (Tarjan.emit v s).
Proof.
  intros HI Houtput. rewrite Tarjan.emit_equation.
  intros c [<-|Hc] u w Hu Hw; [|exact (Houtput c Hc u w Hu Hw)].
  exact (TarjanLow.emission_strong p scope v open s HI u w Hu Hw).
Qed.

(** Exit preserves mutual scoped reachability of every emitted block. *)
Theorem exit_output {V E} (p : Prepared.t V E) scope v open s parent :
  TarjanLow.invariant p scope (v :: open) s -> strong_output p scope s ->
    strong_output p scope (Tarjan.exit v parent s).
Proof.
  intros HI Houtput. rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|]; try exact Houtput.
  destruct (Pos.eqb l d); [now apply emit_output with (open := open)|].
  destruct parent; [now apply lower_output|exact Houtput].
Qed.

(** Every real event block preserves the coupled low-link, ownership and strong-output invariant. *)
Theorem step_invariant {V E} (p : Prepared.t V E) scope roots w here next s :
  Prepared.ready p -> invariant p scope roots w s ->
  SearchRun.trace_step p scope w here next ->
    invariant p scope roots next (SearchRun.apply_events Tarjan.visitor here s).
Proof.
  intros Hready HI Htrace.
  pose proof (step_search p scope roots w here next Hready (search _ _ _ _ _ HI) Htrace)
    as Hsearch.
  destruct Htrace as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot].
  - change (invariant p scope roots (rest, SearchRun.finish u c)
      (Tarjan.exit u (match rest with [] => None | (parent, _) :: _ => Some parent end) s)).
    constructor; [exact Hsearch| | | |].
    + apply (TarjanStateFacts.apply_discovery
        (Search.Exit u (match rest with [] => None | (parent, _) :: _ => Some parent end))).
      exact (discovery _ _ _ _ _ HI).
    + apply TarjanLowStep.exit_invariant; [exact (low _ _ _ _ _ HI)|].
      destruct rest as [|[parent es] rest]; [exact I|].
      exact (exit_parent_path p scope roots u ((parent, es) :: rest) c s HI).
    + exact (proj2 (tree _ _ _ _ _ HI)).
    + apply exit_output with (open := map fst rest);
        [exact (low _ _ _ _ _ HI)|exact (output _ _ _ _ _ HI)].
  - constructor; [exact Hsearch|exact (discovery _ _ _ _ _ HI)|exact (low _ _ _ _ _ HI)|
      exact (tree _ _ _ _ _ HI)|exact (output _ _ _ _ _ HI)].
  - constructor; [exact Hsearch|exact (discovery _ _ _ _ _ HI)|exact (low _ _ _ _ _ HI)|
      exact (tree _ _ _ _ _ HI)|exact (output _ _ _ _ _ HI)].
  - assert (Hvalid : Prepared.valid_id p v).
    { apply SearchInvariant.vertices_spec.
      exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
    destruct (SearchInvariant.valid_frames _ _ _ _ (sound _ _ _ _ (search _ _ _ _ _ HI))
      u ((e, v) :: pending) (or_introl eq_refl)) as [_ [Hu [_ Hedges]]].
    destruct (SearchInvariant.successor_arc p u e v Hready Hu (Hedges _ (or_introl eq_refl)))
      as [Harc _].
    assert (Hreach : TarjanLow.reaches p scope u v).
    { eapply arc_reaches; [exact HI|now left|exact Harc|exact Hvalid|exact Hscope]. }
    assert (Hwhite : FinSet.mem positive_encoding v (SearchRun.seen c) = false).
    { apply (proj1 (SearchInvariant.tree_is_white c u v)).
      now apply SearchRun.color_edge_kind. }
    assert (Hfresh : Map.get positive_encoding v (Tarjan.disc s) = None) by
      exact (fresh_discovery p scope roots _ s v HI Hwhite).
    change (invariant p scope roots
      ((v, Prepared.succ_edges p v) :: (u, pending) :: rest,
        SearchRun.discover v (Some (e, u)) c) (Tarjan.enter v s)).
    constructor; [exact Hsearch| | | |].
    + apply (TarjanStateFacts.apply_discovery (Search.Enter v (Some (e, u)))).
      exact (discovery _ _ _ _ _ HI).
    + apply TarjanLowStep.enter_invariant; [exact (low _ _ _ _ _ HI)|exact Hfresh|
        exact Hvalid|exact Hscope|].
      intros w Hw. eapply TarjanLow.reaches_trans; [|exact Hreach].
      exact (TarjanLow.pending_current p scope u (map fst rest) s
        (TarjanLow.book _ _ _ _ (low _ _ _ _ _ HI))
        (TarjanLow.numbers _ _ _ _ (low _ _ _ _ _ HI))
        (TarjanLow.domain _ _ _ _ (low _ _ _ _ _ HI))
        (TarjanLow.links _ _ _ _ (low _ _ _ _ _ HI))
        (TarjanLow.closed _ _ _ _ (low _ _ _ _ _ HI))
        (TarjanLow.paths _ _ _ _ (low _ _ _ _ _ HI)) w Hw).
    + split; [now exists e|exact (tree _ _ _ _ _ HI)].
    + exact (output _ _ _ _ _ HI).
  - destruct (SearchInvariant.valid_frames _ _ _ _ (sound _ _ _ _ (search _ _ _ _ _ HI))
      u ((e, v) :: pending) (or_introl eq_refl)) as [_ [Hu [_ Hedges]]].
    destruct (SearchInvariant.successor_arc p u e v Hready Hu (Hedges _ (or_introl eq_refl)))
      as [Harc Hv].
    assert (Hreach : TarjanLow.reaches p scope u v).
    { eapply arc_reaches; [exact HI|now left|exact Harc|exact Hv|exact Hscope]. }
    change (invariant p scope roots ((u, pending) :: rest, c) (Tarjan.edge u v k s)).
    constructor; [exact Hsearch| | | |].
    + apply (TarjanStateFacts.apply_discovery (Search.Edge e u v k)).
      exact (discovery _ _ _ _ _ HI).
    + apply TarjanLowStep.edge_invariant; [exact (low _ _ _ _ _ HI)|exact Hreach].
    + exact (tree _ _ _ _ _ HI).
    + apply edge_output, (output _ _ _ _ _ HI).
Qed.

(** Actual event segments compose their prefix invariants in the emitted event order. *)
Theorem segment_invariant {V E} (p : Prepared.t V E) scope roots w evs final s :
  Prepared.ready p -> SearchRun.trace_segment p scope w evs final ->
  invariant p scope roots w s ->
    invariant p scope roots final (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intros Hready Htrace. revert s.
  induction Htrace as [w|w here next later final Hstep Htail IH]; intros s HI; [exact HI|].
  rewrite SearchRun.apply_events_app. apply IH.
  exact (step_invariant p scope roots w here next s Hready HI Hstep).
Qed.

(** Root entry starts one scoped DFS tree from an actually drained pending Tarjan boundary. *)
Theorem root_start {V E} (p : Prepared.t V E) scope roots c s v name :
  Prepared.ready p -> invariant p scope roots ([], c) s -> In v roots ->
  Scope.admits scope v = true -> FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name ->
    invariant p scope roots ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)
      (Tarjan.enter v s).
Proof.
  intros Hready HI Hroot Hallowed Hwhite Hname.
  assert (Hvalid : Prepared.valid_id p v).
  { apply SearchInvariant.vertices_spec.
    exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
  assert (Hfresh : Map.get positive_encoding v (Tarjan.disc s) = None) by
    exact (fresh_discovery p scope roots _ s v HI Hwhite).
  assert (Hpre : ~ In v (SearchRun.pre_rev c)).
  { intro Hin. apply (SearchInvariant.seen_discovered _ (representation _ _ _ _
      (search _ _ _ _ _ HI))) in Hin.
    change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin. congruence. }
  constructor.
  - constructor.
    + apply SearchInvariant.discover_representation;
        [exact (representation _ _ _ _ (search _ _ _ _ _ HI))|exact Hwhite].
    + apply SearchInvariant.discover_history;
        [exact (history _ _ _ _ (search _ _ _ _ _ HI))|exact Hpre].
    + apply SearchInvariant.sound_push;
        [exact (representation _ _ _ _ (search _ _ _ _ _ HI))|
        exact (sound _ _ _ _ (search _ _ _ _ _ HI))| |exact Hvalid|exact Hallowed].
      exists v, []. split; [exact Hroot|now apply Search.scoped_nil].
  - apply (TarjanStateFacts.apply_discovery (Search.Enter v None)).
    exact (discovery _ _ _ _ _ HI).
  - apply TarjanLowStep.enter_invariant; [exact (low _ _ _ _ _ HI)|exact Hfresh|
      exact Hvalid|exact Hallowed|].
    intros w Hw.
    pose proof (low _ _ _ _ _ HI) as Hlow.
    pose proof (TarjanLow.pending_empty p scope s (TarjanLow.book _ _ _ _ Hlow)
      (TarjanLow.domain _ _ _ _ Hlow) (TarjanLow.links _ _ _ _ Hlow)
      (TarjanLow.closed _ _ _ _ Hlow)) as Hempty.
    rewrite Hempty in Hw. contradiction.
  - split; exact I.
  - exact (output _ _ _ _ _ HI).
Qed.

(** Each complete root invocation returns the coupled invariant with an empty open search stack. *)
Theorem root_invariant {V E} (p : Prepared.t V E) scope roots c v evs final s :
  Prepared.ready p -> SearchRun.trace_root p scope c v evs final ->
  invariant p scope roots ([], c) s -> In v roots ->
    invariant p scope roots ([], final) (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intros Hready Htrace HI Hroot.
  destruct Htrace as [c v Hscope|c v Hscope Hseen|c v Hscope Hseen Hname|
    c v name evs final Hscope Hseen Hname Hsegment]; try exact HI.
  change (invariant p scope roots ([], final)
    (SearchRun.apply_events Tarjan.visitor evs (Tarjan.enter v s))).
  apply (segment_invariant p scope roots _ _ _ _ Hready Hsegment).
  exact (root_start p scope roots c s v name Hready HI Hroot Hscope Hseen Hname).
Qed.

(** Supplied root occurrences compose complete actual tree traces without sharing pending stacks. *)
Theorem roots_invariant {V E} (p : Prepared.t V E) scope roots todo c evs final s :
  Prepared.ready p -> SearchRun.trace_roots p scope todo c evs final ->
  invariant p scope roots ([], c) s -> incl todo roots ->
    invariant p scope roots ([], final) (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intros Hready Htrace. revert s.
  induction Htrace as [c|v rest c here next later final Hroot Htail IH];
    intros s HI Hincl; [exact HI|].
  rewrite SearchRun.apply_events_app. apply IH.
  - exact (root_invariant p scope roots c v here next s Hready Hroot HI
      (Hincl v (or_introl eq_refl))).
  - intros x Hx. apply Hincl. now right.
Qed.

(** One actual final core and the actual complete event list carry the coupled Tarjan invariant. *)
Theorem actual_invariant {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  exists final,
    SearchRun.dfs p scope roots = SearchRun.result final /\
    invariant p scope roots ([], final)
      (snd (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))).
Proof.
  intro Hready. destruct (SearchExact.events_wf p scope roots Hready)
    as [final [Hresult Htrace]].
  exists final. split; [exact Hresult|].
  rewrite SearchRun.run_events.
  apply (roots_invariant p scope roots roots SearchRun.initial _ final Tarjan.initial
    Hready Htrace).
  - apply initial_invariant.
  - intros x Hx. exact Hx.
Qed.

(** Completing all actual root invocations leaves the actual pending Tarjan stack empty. *)
Theorem actual_stack_empty {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  Tarjan.stack (snd (Cost.value
    (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))) = [].
Proof.
  intro Hready. destruct (actual_invariant p scope roots Hready) as [final [_ HI]].
  pose proof (low _ _ _ _ _ HI) as Hlow.
  exact (TarjanLow.pending_empty p scope _ (TarjanLow.book _ _ _ _ Hlow)
    (TarjanLow.domain _ _ _ _ Hlow) (TarjanLow.links _ _ _ _ Hlow)
    (TarjanLow.closed _ _ _ _ Hlow)).
Qed.

End TarjanTrace.
