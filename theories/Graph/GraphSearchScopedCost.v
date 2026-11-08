(** * Local visitor and scoped search credit

    Local visitor laws are applied only to genuine emitted events and maintained visitor states.
    For example, a restricted diamond still pays for an outgoing edge to its rejected branch.
    Builds on: GraphSearchCost, GraphSearchInvariant and GraphVisitor. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchExact GraphSearchCost.
Import List.ListNotations Cost.Notations.

Module ScopedSearchCost.
Local Open Scope N_scope.

(** Event IDs name admitted vertices, including each recorded source or parent ID. *)
Definition event_domain {V E} (p : Prepared.t V E) scope (ev : Search.event E) : Prop :=
  match ev with
  | Search.Enter v via =>
    Prepared.valid_id p v /\ Scope.admits scope v = true /\
      match via with
      | None => True
      | Some (e, u) =>
        Prepared.valid_id p u /\ Scope.admits scope u = true /\ Prepared.arc p u e v
      end
  | Search.Edge e u v _ =>
    Prepared.valid_id p u /\ Prepared.valid_id p v /\
      Scope.admits scope u = true /\ Scope.admits scope v = true /\ Prepared.arc p u e v
  | Search.Exit v parent =>
    Prepared.valid_id p v /\ Scope.admits scope v = true /\
      match parent with
      | None => True
      | Some u => Prepared.valid_id p u /\ Scope.admits scope u = true
      end
  end.

(** Scoped support contains admitted valid IDs and retains their original global dense identities. *)
Definition vertices {V E} (p : Prepared.t V E) scope :=
  filter (Scope.admits scope) (SearchInvariant.vertices p).

Definition node_count {V E} (p : Prepared.t V E) scope := length (vertices p scope).

(** Outgoing support counts every cached occurrence at admitted sources, even rejected targets. *)
Definition edge_count {V E} (p : Prepared.t V E) scope :=
  fold_right (fun v n => (length (Prepared.succ_edges p v) + n)%nat) 0%nat (vertices p scope).

Definition capacity {V E} (p : Prepared.t V E) scope :=
  fold_right (fun v n => (SearchInvariant.vertex_work p v + n)%nat) 0%nat (vertices p scope).

Definition work_measure {V E} (p : Prepared.t V E) scope (w : SearchRun.work E) :=
  (SearchInvariant.pending_work (fst w) +
    SearchInvariant.white_work p (vertices p scope) (SearchRun.seen (snd w)))%nat.

(** Scoped support is exactly admitted validity, independently of the supplied root list. *)
Theorem vertices_spec {V E} (p : Prepared.t V E) scope v :
  In v (vertices p scope) <-> Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  unfold vertices. rewrite filter_In, SearchInvariant.vertices_spec. reflexivity.
Qed.

(** Ready scoped support has no repeated global ID. *)
Theorem vertices_nodup {V E} (p : Prepared.t V E) scope :
  Prepared.ready p -> NoDup (vertices p scope).
Proof.
  intro Hready. apply NoDup_filter. now apply SearchInvariant.vertices_nodup.
Qed.

(** The scoped initial capacity is one frame per admitted vertex plus all its outgoing occurrences. *)
Theorem capacity_equation {V E} (p : Prepared.t V E) scope :
  capacity p scope = (node_count p scope + edge_count p scope)%nat.
Proof.
  unfold capacity, node_count, edge_count, SearchInvariant.vertex_work.
  induction (vertices p scope) as [|v rest IH]; cbn [fold_right length]; lia.
Qed.

(** Every emitted transition event has valid admitted endpoints and genuine labelled entry arcs. *)
Theorem transition_events_domain {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchInvariant.sound_work p scope roots w ->
    Forall (event_domain p scope) (snd (SearchRun.transition p scope w)).
Proof.
  intros Hready. destruct w as [stack c]. intro Hsound. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; cbn [snd]; [constructor| |].
  - destruct (SearchInvariant.valid_frames _ _ _ _ Hsound u [] (or_introl eq_refl))
      as [_ [Hu [Hallowed Hedges]]].
    constructor; [|constructor]. cbn [event_domain].
    destruct rest as [|[parent es] rest]; [tauto|].
    destruct (SearchInvariant.valid_frames _ _ _ _ Hsound parent es
      (or_intror (or_introl eq_refl))) as [_ [Hp [Hparent Hrest]]]. tauto.
  - destruct (Scope.admits scope v) eqn:Hscope; [|constructor].
    destruct (Prepared.name_of p v); [|constructor].
    destruct (SearchInvariant.valid_frames _ _ _ _ Hsound u ((e, v) :: pending)
      (or_introl eq_refl)) as [_ [Hu [Hallowed Hedges]]].
    destruct (SearchInvariant.successor_arc p u e v Hready Hu (Hedges _ (or_introl eq_refl)))
      as [Harc Hv].
    assert (Hedge : forall k, event_domain p scope (Search.Edge e u v k)).
    { intro k. cbn [event_domain]. tauto. }
    destruct (SearchRun.edge_kind c u v); constructor; [apply Hedge| |apply Hedge|
      constructor|apply Hedge|constructor|apply Hedge|constructor].
    constructor; [cbn [event_domain]; tauto|constructor].
Qed.

(** Scoped work decreases for every continuing step, including every rejected occurrence. *)
Theorem transition_decreases {V E} (p : Prepared.t V E) scope w next evs :
  Prepared.ready p -> SearchInvariant.representation (snd w) ->
  SearchRun.transition p scope w = (inl next, evs) ->
    (work_measure p scope next < work_measure p scope w)%nat.
Proof.
  intros Hready Hrep Htransition. destruct w as [stack c].
  rewrite SearchRun.step_equation in Htransition.
  destruct stack as [|[u [|[e v] pending]] rest]; [discriminate| |].
  - inversion Htransition; subst next evs.
    unfold work_measure. rewrite SearchRun.finish_equation.
    cbn [fst snd SearchInvariant.pending_work SearchRun.seen]. lia.
  - destruct (Scope.admits scope v) eqn:Hallowed.
    + destruct (Prepared.name_of p v) as [name|] eqn:Hname.
      * destruct (SearchRun.edge_kind c u v) eqn:Hkind;
          inversion Htransition; subst next evs; unfold work_measure;
          cbn [fst snd SearchInvariant.pending_work length]; try lia.
        rewrite SearchRun.discover_equation. cbn [SearchRun.seen].
        assert (Hin : In v (vertices p scope)).
        { apply vertices_spec. split; [|exact Hallowed].
          apply SearchInvariant.vertices_spec.
          exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
        pose proof (SearchInvariant.white_add_present p (vertices p scope) (SearchRun.seen c) v
          (SearchInvariant.seen_wf _ Hrep) (vertices_nodup p scope Hready) Hin
          (proj1 (SearchInvariant.tree_is_white c u v) Hkind)) as Hwhite.
        unfold SearchInvariant.vertex_work in Hwhite. lia.
      * inversion Htransition; subst next evs.
        unfold work_measure. cbn [fst snd SearchInvariant.pending_work length]. lia.
    + inversion Htransition; subst next evs.
      unfold work_measure. cbn [fst snd SearchInvariant.pending_work length]. lia.
Qed.

(** Starting a named admitted root transfers exactly its scoped white credit to the stack. *)
Theorem root_work {V E} (p : Prepared.t V E) scope (c : SearchRun.core E) v name :
  Prepared.ready p -> SearchInvariant.representation c ->
  Scope.admits scope v = true -> Prepared.name_of p v = Some name ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
    work_measure p scope ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) =
      SearchInvariant.white_work p (vertices p scope) (SearchRun.seen c).
Proof.
  intros Hready Hrep Hallowed Hname Hfresh.
  assert (Hin : In v (vertices p scope)).
  { apply vertices_spec. split; [|exact Hallowed]. apply SearchInvariant.vertices_spec.
    exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
  pose proof (SearchInvariant.white_add_present p (vertices p scope) (SearchRun.seen c) v
    (SearchInvariant.seen_wf _ Hrep) (vertices_nodup p scope Hready) Hin Hfresh) as Hwhite.
  unfold work_measure. rewrite SearchRun.discover_equation.
  cbn [fst snd SearchInvariant.pending_work SearchRun.seen].
  unfold SearchInvariant.vertex_work in Hwhite. lia.
Qed.

Local Lemma apply_events_preserved {E S} (vis : Visitor.t E S) I D Phi kv evs s :
  Visitor.amortised_on vis I D Phi kv -> Forall D evs -> I s ->
    I (SearchRun.apply_events vis evs s).
Proof.
  intros Hlocal HD. unfold SearchRun.apply_events.
  revert s. induction HD as [|ev rest Hev Hrest IH]; intros s HI; [exact HI|].
  cbn [fold_left]. apply IH. exact (proj1 (Hlocal ev s HI Hev)).
Qed.

(** Local state preservation and full visitor credit telescope over an admissible event list. *)
Theorem apply_events_cost_on {E S} (vis : Visitor.t E S) I D Phi kv evs s :
  Visitor.amortised_on vis I D Phi kv -> Forall D evs -> I s ->
    I (SearchRun.apply_events vis evs s) /\
    (Cost.ticks (SearchRun.apply_events_c vis evs s) +
      Phi (SearchRun.apply_events vis evs s) <=
      N.of_nat (length evs) * (kv + 1) + Phi s)%N.
Proof.
  intros Hlocal HD HI. split; [eapply apply_events_preserved; eassumption|].
  pose proof (ticks_fold_left_c_potential
    (fun state ev => Visitor.apply_c vis ev state) I Phi kv evs s) as Hfold.
  assert (Hstep : forall state ev, I state -> In ev evs ->
    I (Visitor.apply vis ev state) /\
    Cost.ticks (Visitor.apply_c vis ev state) + Phi (Visitor.apply vis ev state) <= kv + Phi state).
  { intros state ev Hstate Hin. apply Hlocal; [exact Hstate|].
    exact (proj1 (Forall_forall D evs) HD ev Hin). }
  specialize (Hfold Hstep HI).
  fold (SearchRun.apply_events_c vis evs s) in Hfold.
  now rewrite SearchRun.apply_events_value in Hfold.
Qed.

Definition state_invariant {V E S} (p : Prepared.t V E) scope roots (I : S -> Prop)
    (state : SearchRun.work E * S) :=
  SearchCost.state_invariant p scope roots state /\ I (snd state).

Definition state_credit {V E S} (p : Prepared.t V E) scope (Phi : S -> N) w kv
    (state : SearchRun.work E * S) :=
  SearchCost.step_k w kv * N.of_nat (work_measure p scope (fst state)) + Phi (snd state).

Local Lemma step_visitor_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w s :
  Prepared.ready p -> SearchInvariant.sound_work p scope roots w ->
  Visitor.amortised_on vis I D Phi kv ->
  (forall ev, event_domain p scope ev -> D ev) -> I s ->
  I (snd (SearchRun.unwrap (Cost.value (SearchRun.step_c p vis scope (w, s))))) /\
  (Cost.ticks (SearchRun.step_c p vis scope (w, s)) +
    Phi (snd (SearchRun.unwrap (Cost.value (SearchRun.step_c p vis scope (w, s))))) <=
    Cost.ticks (SearchRun.transition_c p scope w) + 2 * (kv + 1) + Phi s)%N.
Proof.
  intros Hready Hsound Hlocal Hdomain HI.
  assert (HD : Forall D (snd (SearchRun.transition p scope w))).
  { eapply Forall_impl; [exact Hdomain|].
    exact (transition_events_domain p scope roots w Hready Hsound). }
  destruct (apply_events_cost_on vis I D Phi kv _ s Hlocal HD HI) as [HI' Hvisitor].
  pose proof (SearchCost.transition_events_bound p scope w) as Hlength.
  unfold SearchRun.step_c. rewrite Cost.ticks_bind, Cost.value_bind.
  fold (SearchRun.transition p scope w).
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd] in HI', Hvisitor, Hlength |- *;
    rewrite Cost.ticks_bind, Cost.value_bind, SearchRun.apply_events_value, Cost.value_ret;
    cbn [SearchRun.unwrap snd]; rewrite Cost.ticks_ret, N.add_0_r;
    split; [exact HI'| |exact HI'|].
  all: assert (HlengthN : (N.of_nat (length evs) <= 2)%N).
  all: try (destruct (length evs) as [|[|n]]; [cbn; lia|cbn; lia|];
    assert (Hn : n = 0%nat) by lia; subst n; reflexivity).
  all: nia.
Qed.

Local Lemma stop_same {V E} (p : Prepared.t V E) scope state final evs :
  SearchRun.transition p scope state = (inr final, evs) ->
    final = state /\ evs = [] /\ fst state = [].
Proof.
  destruct state as [stack c]. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest].
  - intro H. inversion H. auto.
  - discriminate.
  - destruct (Scope.admits scope v); [|discriminate].
    destruct (Prepared.name_of p v); [|discriminate].
    destruct (SearchRun.edge_kind c u v); discriminate.
Qed.

(** Actual step credit uses only local visitor duties on events established by the search owner. *)
Theorem step_credit_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w state :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv ->
  (forall ev, event_domain p scope ev -> D ev) ->
  state_invariant p scope roots I state ->
  match Cost.value (SearchRun.step_c p vis scope state) with
  | inl next =>
    state_invariant p scope roots I next /\
    Cost.ticks (SearchRun.step_c p vis scope state) + state_credit p scope Phi w kv next + 3 <=
      state_credit p scope Phi w kv state
  | inr final =>
    state_invariant p scope roots I final /\
    Cost.ticks (SearchRun.step_c p vis scope state) + state_credit p scope Phi w kv final <=
      state_credit p scope Phi w kv state + 1
  end.
Proof.
  intros Hready Hwidth Hlocal Hdomain. destruct state as [work s]. intros [[Hrep Hsound] HI].
  destruct (step_visitor_cost_on p vis I D Phi kv scope roots work s
    Hready Hsound Hlocal Hdomain HI) as [HI' Hvisitor].
  pose proof (SearchCost.transition_cost p scope roots w work Hready Hwidth Hsound) as Hprimitive.
  pose proof (SearchInvariant.transition_representation p scope work Hrep) as Hrep'.
  pose proof (SearchInvariant.transition_sound p scope roots work Hready Hrep Hsound) as Hsound'.
  rewrite SearchRun.step_erases in HI', Hvisitor |- *.
  destruct (SearchRun.transition p scope work) as [[next|final] evs] eqn:Htransition.
  - split; [split; [split; assumption|exact HI']|].
    pose proof (transition_decreases p scope work next evs Hready Hrep Htransition) as Hdecrease.
    cbn [SearchRun.unwrap fst snd] in Hvisitor.
    unfold state_credit. cbn [fst snd].
    assert (HdecreaseN : N.of_nat (work_measure p scope next) + 1 <=
      N.of_nat (work_measure p scope work)) by lia.
    unfold SearchCost.step_k. nia.
  - destruct (stop_same p scope work final evs Htransition) as [-> [-> Hempty]].
    destruct work as [stack c]. cbn [fst] in Hempty. subst stack.
    unfold SearchRun.step_c, SearchRun.transition_c, SearchRun.apply_events_c.
    autorewrite with galois_cost.
    cbn [SearchRun.apply_events fold_left].
    autorewrite with galois_cost.
    split; [split; [split; assumption|exact HI]|lia].
Qed.

(** Both stopping and exhaustion retain the actual visitor invariant and all residual credit. *)
Theorem loop_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w fuel state :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv ->
  (forall ev, event_domain p scope ev -> D ev) ->
  state_invariant p scope roots I state ->
    state_invariant p scope roots I
      (SearchRun.unwrap (Cost.value (iterate (SearchRun.step_c p vis scope) fuel state))) /\
    Cost.ticks (iterate (SearchRun.step_c p vis scope) fuel state) +
      state_credit p scope Phi w kv
        (SearchRun.unwrap (Cost.value (iterate (SearchRun.step_c p vis scope) fuel state))) <=
      state_credit p scope Phi w kv state + (1 + N.pos (Pos.size fuel)).
Proof.
  intros Hready Hwidth Hlocal Hdomain HI.
  pose proof (SearchCost.iterate_credit (SearchRun.step_c p vis scope)
    (state_invariant p scope roots I) (state_credit p scope Phi w kv) fuel state
    (fun st Hst => step_credit_on p vis I D Phi kv scope roots w st
      Hready Hwidth Hlocal Hdomain Hst) HI) as Hcredit.
  destruct (Cost.value (iterate (SearchRun.step_c p vis scope) fuel state)) as [next|final];
    cbn [SearchRun.unwrap]; destruct Hcredit; split; try assumption; nia.
Qed.

Definition core_credit {V E S} (p : Prepared.t V E) scope (Phi : S -> N) w kv
    (state : SearchRun.core E * S) :=
  SearchCost.step_k w kv *
    N.of_nat (SearchInvariant.white_work p (vertices p scope) (SearchRun.seen (fst state))) +
      Phi (snd state).

Definition core_invariant {V E S} (p : Prepared.t V E) scope roots (I : S -> Prop)
    (state : SearchRun.core E * S) :=
  SearchCost.core_invariant p scope roots state /\ I (snd state).

(** A named admitted root belongs to the callback event domain regardless of root multiplicity. *)
Theorem root_event_domain {V E} (p : Prepared.t V E) scope v name :
  Prepared.ready p -> Scope.admits scope v = true -> Prepared.name_of p v = Some name ->
    event_domain p scope (Search.Enter v None).
Proof.
  intros Hready Hallowed Hname. cbn [event_domain]. split.
  - apply SearchInvariant.vertices_spec.
    exact (SearchInvariant.named_in_vertices p v name Hready Hname).
  - auto.
Qed.

Local Lemma launch_invariant {V E S} (p : Prepared.t V E) scope roots c v name (s : S) :
  Prepared.ready p -> SearchInvariant.representation c ->
  SearchInvariant.sound_work p scope roots ([], c) ->
  In v roots -> Scope.admits scope v = true ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name ->
    SearchCost.state_invariant p scope roots
      (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c), s).
Proof.
  intros Hready Hrep Hsound Hroot Hallowed Hfresh Hname.
  assert (Hvalid : Prepared.valid_id p v).
  { apply SearchInvariant.vertices_spec.
    exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
  split; [now apply SearchInvariant.discover_representation|].
  apply SearchInvariant.sound_push; try assumption.
  exists v, []. split; [exact Hroot|now apply Search.scoped_nil].
Qed.

(** Root launch transfers scoped graph credit and preserves locally admissible visitor state. *)
Theorem launch_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w c v name s :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv -> (forall ev, event_domain p scope ev -> D ev) ->
  SearchInvariant.representation c -> SearchInvariant.sound_work p scope roots ([], c) ->
  In v roots -> Scope.admits scope v = true ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name -> I s ->
  I (snd (Cost.value (SearchRun.launch_c p vis scope c v s))) /\
  Cost.ticks (SearchRun.launch_c p vis scope c v s) +
    core_credit p scope Phi w kv (Cost.value (SearchRun.launch_c p vis scope c v s)) <=
    core_credit p scope Phi w kv (c, s) +
      (2 + 4 * SearchCost.id_cost w + kv + N.pos (Pos.size (Prepared.fuel p))).
Proof.
  intros Hready Hwidth Hlocal Hdomain Hrep Hsound Hroot Hallowed Hfresh Hname HI.
  destruct (Hlocal (Search.Enter v None) s HI
    (Hdomain _ (root_event_domain p scope v name Hready Hallowed Hname))) as [HI' Hvisitor].
  destruct (loop_cost_on p vis I D Phi kv scope roots w (Prepared.fuel p)
    (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c),
      Visitor.apply vis (Search.Enter v None) s) Hready Hwidth Hlocal Hdomain
    (conj (launch_invariant p scope roots c v name _ Hready Hrep Hsound Hroot
      Hallowed Hfresh Hname) HI')) as [HIloop Hloop].
  set (loop := iterate (SearchRun.step_c p vis scope) (Prepared.fuel p)
    (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c),
      Visitor.apply vis (Search.Enter v None) s)) in *.
  pose proof (SearchCost.discover_cost w v None c (Hwidth v (or_intror Hroot))) as Hdiscover.
  pose proof (SearchCost.successors_cost p w v (Hwidth v (or_intror Hroot))) as Hsuccessors.
  unfold SearchRun.launch_c. autorewrite with galois_cost.
  fold (SearchRun.discover v None c).
  fold (Visitor.apply vis (Search.Enter v None) s).
  fold (Prepared.succ_edges p v). fold loop.
  destruct (SearchRun.unwrap (Cost.value loop)) as [[stack final] sv] eqn:Hanswer.
  cbn [fst snd]. autorewrite with galois_cost. split; [exact (proj2 HIloop)|].
  unfold state_credit in Hloop. cbn [fst snd] in Hloop.
  rewrite (root_work p scope c v name Hready Hrep Hallowed Hname Hfresh) in Hloop.
  unfold core_credit. cbn [fst snd].
  unfold work_measure in Hloop. cbn [fst snd] in Hloop.
  rewrite Nat2N.inj_add in Hloop. nia.
Qed.

(** Every root occurrence preserves local visitor state and telescopes the same scoped credit. *)
Theorem root_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w c v s :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv -> (forall ev, event_domain p scope ev -> D ev) ->
  SearchInvariant.representation c -> SearchInvariant.sound_work p scope roots ([], c) ->
  In v roots -> I s ->
  I (snd (Cost.value (SearchRun.root_c p vis scope (c, s) v))) /\
  Cost.ticks (SearchRun.root_c p vis scope (c, s) v) +
    core_credit p scope Phi w kv (Cost.value (SearchRun.root_c p vis scope (c, s) v)) <=
    core_credit p scope Phi w kv (c, s) +
      (SearchCost.root_k w kv + N.pos (Pos.size (Prepared.fuel p))).
Proof.
  intros Hready Hwidth Hlocal Hdomain Hrep Hsound Hroot HI.
  pose proof (SearchCost.admits_cost w scope v (Hwidth v (or_intror Hroot))) as Hscope.
  pose proof (SearchCost.id_membership_cost w v (SearchRun.seen c)
    (Hwidth v (or_intror Hroot))) as Hmem.
  pose proof (SearchCost.name_cost p w v (Hwidth v (or_intror Hroot))) as Hname.
  unfold SearchRun.root_c. autorewrite with galois_cost.
  fold (Scope.admits scope v). destruct (Scope.admits scope v) eqn:Hallowed;
    autorewrite with galois_cost; [|split; [exact HI|unfold SearchCost.root_k; nia]].
  fold (FinSet.mem positive_encoding v (SearchRun.seen c)).
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh;
    autorewrite with galois_cost; [split; [exact HI|unfold SearchCost.root_k; nia]|].
  fold (Prepared.name_of p v).
  destruct (Prepared.name_of p v) as [name|] eqn:Hnamed;
    autorewrite with galois_cost; [|split; [exact HI|unfold SearchCost.root_k; nia]].
  destruct (launch_cost_on p vis I D Phi kv scope roots w c v name s Hready Hwidth
    Hlocal Hdomain Hrep Hsound Hroot Hallowed Hfresh Hnamed HI) as [HI' Hlaunch].
  split; [exact HI'|]. unfold SearchCost.root_k. nia.
Qed.

Local Lemma root_core_preserved {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    scope roots state v :
  Prepared.ready p -> SearchCost.core_invariant p scope roots state -> In v roots ->
    SearchCost.core_invariant p scope roots
      (Cost.value (SearchRun.root_c p vis scope state v)).
Proof.
  intros Hready. destruct state as [c s]. intros [Hrep Hsound] Hroot.
  pose proof (SearchInvariant.root_representation p scope c v Hrep) as Hrep'.
  pose proof (SearchInvariant.root_sound p scope roots c v Hready Hrep Hsound Hroot) as Hsound'.
  rewrite SearchRun.root_erases.
  destruct (SearchRun.reference_root p scope c v) as [final evs]. split; assumption.
Qed.

Local Lemma fold_left_preserves {A B} (f : B -> A -> B) (J : B -> Prop) xs start :
  (forall state x, J state -> In x xs -> J (f state x)) ->
  J start -> J (fold_left f xs start).
Proof.
  revert start. induction xs as [|x rest IH]; intros start Hstep Hstart; [exact Hstart|].
  cbn [fold_left]. apply IH.
  - intros state y Hstate Hy. apply Hstep; [exact Hstate|now right].
  - apply Hstep; [exact Hstart|now left].
Qed.

(** Root folding preserves the local invariant and the full final visitor potential. *)
Theorem roots_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w c s :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv -> (forall ev, event_domain p scope ev -> D ev) ->
  core_invariant p scope roots I (c, s) ->
  core_invariant p scope roots I
    (Cost.value (fold_left_c (SearchRun.root_c p vis scope) roots (c, s))) /\
  Cost.ticks (fold_left_c (SearchRun.root_c p vis scope) roots (c, s)) +
    core_credit p scope Phi w kv
      (Cost.value (fold_left_c (SearchRun.root_c p vis scope) roots (c, s))) <=
    N.of_nat (length roots) *
      (SearchCost.root_k w kv + N.pos (Pos.size (Prepared.fuel p)) + 1) +
      core_credit p scope Phi w kv (c, s).
Proof.
  intros Hready Hwidth Hlocal Hdomain HI.
  assert (Hstep : forall state v, core_invariant p scope roots I state -> In v roots ->
    core_invariant p scope roots I (Cost.value (SearchRun.root_c p vis scope state v)) /\
    Cost.ticks (SearchRun.root_c p vis scope state v) +
      core_credit p scope Phi w kv (Cost.value (SearchRun.root_c p vis scope state v)) <=
      SearchCost.root_k w kv + N.pos (Pos.size (Prepared.fuel p)) +
        core_credit p scope Phi w kv state).
  { intros [c' s'] v [[Hrep Hsound] Hstate] Hroot.
    destruct (root_cost_on p vis I D Phi kv scope roots w c' v s'
      Hready Hwidth Hlocal Hdomain Hrep Hsound Hroot Hstate) as [HI' Hcredit].
    split.
    - split; [apply root_core_preserved; [exact Hready|split; assumption|exact Hroot]|exact HI'].
    - nia. }
  split.
  - rewrite value_fold_left_c. apply fold_left_preserves; [|exact HI].
    intros state v Hstate Hroot. exact (proj1 (Hstep state v Hstate Hroot)).
  - exact (ticks_fold_left_c_potential (SearchRun.root_c p vis scope)
      (core_invariant p scope roots I) (core_credit p scope Phi w kv)
      (SearchCost.root_k w kv + N.pos (Pos.size (Prepared.fuel p))) roots (c, s) Hstep HI).
Qed.

(** The admitted support bounds the actual result size without scanning that support at runtime. *)
Theorem preorder_length {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
    (length (Search.preorder (SearchRun.dfs p scope roots)) <= node_count p scope)%nat.
Proof.
  intro Hready.
  destruct (SearchExact.run_representation p scope roots) as [_ [_ [_ [_ [Hnodup Hseen]]]]].
  apply NoDup_incl_length; [exact Hnodup|].
  intros v Hv. apply vertices_spec.
  apply (proj1 (SearchExact.run_reachable p scope roots v Hready)) in Hv.
  destruct Hv as [root [es [_ Hpath]]]. induction Hpath; auto.
Qed.

Local Lemma result_cost {E} (c : SearchRun.core E) :
  Cost.ticks (SearchRun.result_c c) =
    N.of_nat (length (Search.preorder (SearchRun.result c))) +
      N.of_nat (length (Search.postorder (SearchRun.result c))).
Proof.
  unfold SearchRun.result, SearchRun.result_c. autorewrite with galois_cost.
  cbn [Search.preorder Search.postorder]. rewrite !length_rev. lia.
Qed.

Local Lemma initial_core_invariant {V E S} (p : Prepared.t V E) scope roots (I : S -> Prop) s :
  I s -> core_invariant p scope roots I (SearchRun.initial, s).
Proof.
  intro HI. split; [split; [apply SearchInvariant.initial_representation|]|exact HI].
  constructor.
  - intros v Hv. change (FinSet.mem positive_encoding v FinSet.empty = true) in Hv.
    rewrite FinSet.mem_empty in Hv. discriminate.
  - intros u es Hin. contradiction.
Qed.

Local Lemma initial_credit {V E S} (p : Prepared.t V E) scope (Phi : S -> N) w kv s :
  core_credit p scope Phi w kv (SearchRun.initial, s) =
    SearchCost.step_k w kv *
      (N.of_nat (node_count p scope) + N.of_nat (edge_count p scope)) + Phi s.
Proof.
  unfold core_credit. cbn [fst snd SearchRun.initial SearchRun.seen].
  assert (Hwhite : forall todo, SearchInvariant.white_work p todo FinSet.empty =
    fold_right (fun v n => (SearchInvariant.vertex_work p v + n)%nat) 0%nat todo).
  { induction todo as [|v rest IH]; [reflexivity|].
    cbn [SearchInvariant.white_work fold_right]. rewrite FinSet.mem_empty, IH. reflexivity. }
  rewrite Hwhite. fold (capacity p scope).
  rewrite capacity_equation, Nat2N.inj_add. reflexivity.
Qed.

(** Actual run cost telescopes scoped structural work and returns its local state invariant. *)
Theorem search_scoped_credit_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w s :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv -> (forall ev, event_domain p scope ev -> D ev) ->
  I s ->
  I (snd (Cost.value (SearchRun.run_c p vis scope roots s))) /\
  Cost.ticks (SearchRun.run_c p vis scope roots s) +
    Phi (snd (Cost.value (SearchRun.run_c p vis scope roots s))) <=
    SearchCost.step_k w kv * (N.of_nat (node_count p scope) + N.of_nat (edge_count p scope)) +
    N.of_nat (length roots) *
      (SearchCost.root_k w kv + N.pos (Pos.size (Prepared.fuel p)) + 1) +
    2 * N.of_nat (node_count p scope) + Phi s.
Proof.
  intros Hready Hwidth Hlocal Hdomain HI.
  destruct (roots_cost_on p vis I D Phi kv scope roots w SearchRun.initial s
    Hready Hwidth Hlocal Hdomain (initial_core_invariant p scope roots I s HI))
    as [Hfinal Hroots].
  rewrite initial_credit in Hroots.
  pose proof (SearchRun.run_result p vis scope roots s) as Hresult.
  pose proof (preorder_length p scope roots Hready) as Hlength.
  destruct (SearchExact.run_numbering p scope roots Hready) as [Hperm _].
  pose proof (Permutation_length Hperm) as Hpost.
  unfold SearchRun.run_c in Hresult |- *.
  set (fold_m := fold_left_c (SearchRun.root_c p vis scope) roots (SearchRun.initial, s)) in *.
  rewrite Cost.value_bind in Hresult |- *. rewrite Cost.ticks_bind.
  destruct (Cost.value fold_m) as [c final] eqn:Hfold.
  cbn [fst snd] in Hfinal, Hroots, Hresult |- *.
  autorewrite with galois_cost in Hresult |- *.
  change (SearchRun.result c = SearchRun.dfs p scope roots) in Hresult.
  split; [exact (proj2 Hfinal)|].
  rewrite result_cost, Hresult.
  unfold core_credit in Hroots. cbn [fst snd] in Hroots.
  cbn [snd]. nia.
Qed.

(** Scoped size retains global ID widths, root multiplicity and the actual prepared-fuel overhead. *)
Definition search_size {V E} (p : Prepared.t V E) scope (roots : list positive) w kv :=
  (N.of_nat (node_count p scope) + N.of_nat (edge_count p scope) + N.of_nat (length roots)) *
    (1 + w + kv) + N.of_nat (length roots) * N.pos (Pos.size (Prepared.fuel p)).

(** Local callback duties give the component-sensitive bound with full final visitor potential. *)
Theorem search_scoped_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w s :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv -> (forall ev, event_domain p scope ev -> D ev) ->
  I s ->
  I (snd (Cost.value (SearchRun.run_c p vis scope roots s))) /\
  Cost.ticks (SearchRun.run_c p vis scope roots s) +
    Phi (snd (Cost.value (SearchRun.run_c p vis scope roots s))) <=
    SearchCost.search_k * search_size p scope roots w kv + Phi s.
Proof.
  intros Hready Hwidth Hlocal Hdomain HI.
  destruct (search_scoped_credit_cost_on p vis I D Phi kv scope roots w s
    Hready Hwidth Hlocal Hdomain HI) as [HI' Hcost]. split; [exact HI'|].
  pose proof (SearchCost.search_coefficients (N.of_nat (node_count p scope))
    (N.of_nat (edge_count p scope)) (N.of_nat (length roots))
    (N.pos (Pos.size (Prepared.fuel p))) w kv).
  unfold search_size. nia.
Qed.

Local Lemma loop_events_domain {V E} (p : Prepared.t V E) scope roots n w :
  Prepared.ready p -> SearchInvariant.representation (snd w) ->
  SearchInvariant.sound_work p scope roots w ->
    Forall (event_domain p scope) (snd (SearchRun.reference_loop p scope n w)).
Proof.
  intro Hready. revert w. induction n as [|n IH]; intros w Hrep Hsound; [constructor|].
  pose proof (transition_events_domain p scope roots w Hready Hsound) as Hhere.
  pose proof (SearchInvariant.transition_representation p scope w Hrep) as Hrep'.
  pose proof (SearchInvariant.transition_sound p scope roots w Hready Hrep Hsound) as Hsound'.
  cbn [SearchRun.reference_loop].
  destruct (SearchRun.transition p scope w) as [[next|final] here];
    cbn [fst snd SearchRun.unwrap] in Hhere, Hrep', Hsound'.
  - pose proof (IH next Hrep' Hsound') as Hlater.
    destruct (SearchRun.reference_loop p scope n next) as [last later].
    cbn [snd] in Hlater |- *. apply Forall_app. auto.
  - exact Hhere.
Qed.

Local Lemma root_events_domain {V E} (p : Prepared.t V E) scope roots c v :
  Prepared.ready p -> SearchInvariant.representation c ->
  SearchInvariant.sound_work p scope roots ([], c) -> In v roots ->
    Forall (event_domain p scope) (snd (SearchRun.reference_root p scope c v)).
Proof.
  intros Hready Hrep Hsound Hroot. unfold SearchRun.reference_root.
  destruct (Scope.admits scope v) eqn:Hallowed; [|constructor].
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh; [constructor|].
  destruct (Prepared.name_of p v) as [name|] eqn:Hname; [|constructor].
  destruct (launch_invariant p scope roots c v name tt Hready Hrep Hsound Hroot
    Hallowed Hfresh Hname) as [Hrep' Hsound'].
  pose proof (loop_events_domain p scope roots (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) Hready Hrep' Hsound')
    as Hloop.
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [final evs].
  constructor; [exact (root_event_domain p scope v name Hready Hallowed Hname)|exact Hloop].
Qed.

Local Lemma roots_events_domain {V E} (p : Prepared.t V E) scope roots todo c :
  Prepared.ready p -> incl todo roots -> SearchInvariant.representation c ->
  SearchInvariant.sound_work p scope roots ([], c) ->
    Forall (event_domain p scope) (snd (SearchRun.reference_roots p scope todo c)).
Proof.
  intro Hready. revert c. induction todo as [|v rest IH]; intros c Htodo Hrep Hsound;
    [constructor|].
  pose proof (root_events_domain p scope roots c v Hready Hrep Hsound
    (Htodo v (or_introl eq_refl))) as Hhere.
  pose proof (SearchInvariant.root_representation p scope c v Hrep) as Hrep'.
  pose proof (SearchInvariant.root_sound p scope roots c v Hready Hrep Hsound
    (Htodo v (or_introl eq_refl))) as Hsound'.
  cbn [SearchRun.reference_roots].
  destruct (SearchRun.reference_root p scope c v) as [next here].
  pose proof (IH next ltac:(intros x Hx; apply Htodo; now right) Hrep' Hsound') as Hlater.
  destruct (SearchRun.reference_roots p scope rest next) as [final later].
  apply Forall_app. auto.
Qed.

(** Ready search emits only valid admitted event IDs and parent IDs from its actual trace. *)
Theorem events_domain {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> Forall (event_domain p scope) (SearchRun.events p scope roots).
Proof.
  intro Hready.
  destruct (initial_core_invariant p scope roots (fun _ : unit => True) tt I)
    as [[Hrep Hsound] Hvisitor].
  unfold SearchRun.events.
  exact (roots_events_domain p scope roots roots _ Hready ltac:(intros x Hx; exact Hx)
    Hrep Hsound).
Qed.

Local Lemma filter_work_bound {V E} (p : Prepared.t V E) scope todo :
  (fold_right (fun v n => SearchInvariant.vertex_work p v + n) 0
    (filter (Scope.admits scope) todo) <=
   fold_right (fun v n => SearchInvariant.vertex_work p v + n) 0 todo)%nat.
Proof.
  induction todo as [|v rest IH]; [reflexivity|].
  cbn [filter fold_right]. destruct (Scope.admits scope v); cbn [fold_right]; lia.
Qed.

(** Scoped work is a genuine sub-credit of the full graph rather than a renamed global size. *)
Theorem capacity_bound {V E} (p : Prepared.t V E) scope :
  Prepared.ready p ->
    (node_count p scope + edge_count p scope <=
      length (Graph.nodes (Prepared.graph p)) + GraphModel.edge_count (Prepared.graph p))%nat.
Proof.
  intro Hready. rewrite <- capacity_equation, <- (SearchInvariant.capacity_equation p Hready).
  unfold capacity, vertices, SearchInvariant.capacity. apply filter_work_bound.
Qed.

Local Lemma scoped_size_bound {V E} (p : Prepared.t V E) scope roots w kv :
  Prepared.ready p -> search_size p scope roots w kv <= SearchCost.search_size p roots w kv.
Proof.
  intro Hready. pose proof (capacity_bound p scope Hready) as Hcapacity.
  unfold search_size, SearchCost.search_size.
  assert (HcapacityN : N.of_nat (node_count p scope) + N.of_nat (edge_count p scope) <=
    N.of_nat (length (Graph.nodes (Prepared.graph p))) +
      N.of_nat (GraphModel.edge_count (Prepared.graph p))) by lia.
  nia.
Qed.

(** Local visitor duties also give the old global size bound while retaining final potential. *)
Theorem search_cost_on {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    I D Phi kv scope roots w s :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  Visitor.amortised_on vis I D Phi kv -> (forall ev, event_domain p scope ev -> D ev) ->
  I s ->
  I (snd (Cost.value (SearchRun.run_c p vis scope roots s))) /\
  Cost.ticks (SearchRun.run_c p vis scope roots s) +
    Phi (snd (Cost.value (SearchRun.run_c p vis scope roots s))) <=
    SearchCost.search_k * SearchCost.search_size p roots w kv + Phi s.
Proof.
  intros Hready Hwidth Hlocal Hdomain HI.
  destruct (search_scoped_cost_on p vis I D Phi kv scope roots w s
    Hready Hwidth Hlocal Hdomain HI) as [HI' Hcost]. split; [exact HI'|].
  pose proof (scoped_size_bound p scope roots w kv Hready). nia.
Qed.

(** The existing global visitor law specializes to the new component-sensitive size bound. *)
Theorem search_scoped_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w s :
  Prepared.ready p -> SearchCost.width_bound p roots w -> Visitor.amortised vis Phi kv ->
  Cost.ticks (SearchRun.run_c p vis scope roots s) +
    Phi (snd (Cost.value (SearchRun.run_c p vis scope roots s))) <=
    SearchCost.search_k * search_size p scope roots w kv + Phi s.
Proof.
  intros Hready Hwidth Hglobal.
  assert (Hlocal : Visitor.amortised_on vis (fun _ => True) (fun _ => True) Phi kv).
  { apply Visitor.amortised_on_of_global; [exact Hglobal|intros; exact I]. }
  exact (proj2 (search_scoped_cost_on p vis (fun _ => True) (fun _ => True)
    Phi kv scope roots w s Hready Hwidth Hlocal ltac:(intros; exact I) I)).
Qed.

End ScopedSearchCost.
