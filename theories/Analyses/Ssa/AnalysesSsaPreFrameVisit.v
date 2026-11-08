(** * Coverage of the actual indexed dominator walk

    Roots remain scheduled and visiting a parent schedules each indexed child.
    For example, a completed diamond walk cannot omit its right arm even without a real occurrence.
    Builds on: AnalysesSsaPreRename, GraphCheckDom and the public map/index observations. *)

From Stdlib Require Import List Bool Relations.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreFrameCache AnalysesSsaPreFrameStep AnalysesSsaPreFrameEnd.
Import List.ListNotations.

Module PreFrameVisit.

Section Coverage.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Hypothesis Hlaw : Pre.laws c.
Let index := PreRename.prepare c data.

(** Scheduled block IDs have already been visited or occur in the pending task list. *)
Definition scheduled (current : PreRename.work B BE E U) id : Prop :=
  FinSet.mem positive_encoding id (PreRename.visited current) = true \/
    exists frames, In (id, frames) (PreRename.pending current).

(** Root and parent-edge obligations remain represented by visited or pending tasks. *)
Record visit_laws (current : PreRename.work B BE E U) : Prop := VisitLaws {
  visit_seen_wf : FinSet.wf positive_encoding (PreRename.visited current);
  visit_roots : forall id, In id (PreRename.root_ids index) -> scheduled current id;
  visit_children : forall child parent,
    Map.get positive_encoding child (Dom.idom (Pre.dom c)) = Some parent ->
    FinSet.mem positive_encoding parent (PreRename.visited current) = true ->
      scheduled current child
}.

Local Lemma children_exact {child parent} :
  In (child, parent) (Index.find positive_encoding parent (PreRename.children index)) <->
    Map.get positive_encoding child (Dom.idom (Pre.dom c)) = Some parent.
Proof.
  unfold index; destruct (PreRename.prepare_walk_equations c data)
    as [Hroots [Hparents [Hchildren Hbudget]]].
  rewrite Hchildren, Index.find_group_by, filter_In; cbn [snd]; rewrite eqb_refl.
  rewrite (Map.elements_spec positive_encoding positive_encoding_laws)
    by exact (proj1 (Dom.maps_wf _ _ (Pre.tree_exact c (Pre.graphs c Hlaw)))).
  tauto.
Qed.

Local Lemma initial_visit_laws : visit_laws (PreRename.initial index).
Proof.
  constructor; rewrite PreRename.initial_equation; cbn [PreRename.visited].
  - apply FinSet.wf_empty.
  - intros id Hid; right; exists (PreRename.entry_scope index).
    cbn [PreRename.pending]; apply in_map_iff; exists id; auto.
  - intros child parent Hparent Hseen; rewrite FinSet.mem_empty in Hseen; discriminate.
Qed.

Local Lemma scheduled_advance :
  forall current next id frames rest,
    PreRename.pending current = (id, frames) :: rest ->
    (forall x, FinSet.mem positive_encoding x (PreRename.visited current) = true ->
      FinSet.mem positive_encoding x (PreRename.visited next) = true) ->
    FinSet.mem positive_encoding id (PreRename.visited next) = true ->
    incl rest (PreRename.pending next) ->
    forall x, scheduled current x -> scheduled next x.
Proof.
  intros current next id frames rest Hpending Hseen Hid Hrest x [Hx|[scope Hx]].
  - left; apply Hseen; exact Hx.
  - rewrite Hpending in Hx; destruct Hx as [Heq|Hx].
    + inversion Heq; subst x; now left.
    + right; exists scope; apply Hrest; exact Hx.
Qed.

Local Lemma skip_visit_laws current id frames rest :
  visit_laws current -> PreRename.pending current = (id, frames) :: rest ->
  FinSet.mem positive_encoding id (PreRename.visited current) = true ->
  visit_laws (PreRename.Work rest (PreRename.visited current) (PreRename.output current)).
Proof.
  intros Hvisit Hpending Hseen.
  assert (Hadvance : forall x, scheduled current x ->
    scheduled (PreRename.Work rest (PreRename.visited current) (PreRename.output current)) x).
  { apply (scheduled_advance current _ id frames rest Hpending); cbn [PreRename.visited].
    - auto.
    - exact Hseen.
    - intros pair Hpair; exact Hpair. }
  constructor; [exact (visit_seen_wf _ Hvisit)| |].
  - intros root Hroot; apply Hadvance; exact (visit_roots _ Hvisit root Hroot).
  - intros child parent Hparent Hparent_seen.
    apply Hadvance; exact (visit_children _ Hvisit child parent Hparent Hparent_seen).
Qed.

Local Lemma add_visit_laws current id frames rest b :
  visit_laws current -> PreRename.pending current = (id, frames) :: rest ->
  visit_laws (PreRename.Work
    (map (fun pair => (fst pair, fst (PreRename.block c index b frames (PreRename.output current))))
      (Index.find positive_encoding id (PreRename.children index)) ++ rest)
    (FinSet.add positive_encoding id (PreRename.visited current))
    (snd (PreRename.block c index b frames (PreRename.output current)))).
Proof.
  intros Hvisit Hpending.
  set (next := PreRename.Work
    (map (fun pair => (fst pair, fst (PreRename.block c index b frames (PreRename.output current))))
      (Index.find positive_encoding id (PreRename.children index)) ++ rest)
    (FinSet.add positive_encoding id (PreRename.visited current))
    (snd (PreRename.block c index b frames (PreRename.output current)))).
  assert (Hadvance : forall x, scheduled current x -> scheduled next x).
  { apply (scheduled_advance current next id frames rest Hpending); unfold next;
      cbn [PreRename.visited PreRename.pending].
    - intros x Hx; rewrite FinSet.mem_add by exact (visit_seen_wf _ Hvisit).
      rewrite Hx, orb_true_r; reflexivity.
    - rewrite FinSet.mem_add by exact (visit_seen_wf _ Hvisit).
      rewrite eqb_refl; reflexivity.
    - intros pair Hpair; apply in_or_app; now right. }
  constructor.
  - apply FinSet.wf_add; exact (visit_seen_wf _ Hvisit).
  - intros root Hroot; apply Hadvance; exact (visit_roots _ Hvisit root Hroot).
  - intros child parent Hparent Hseen.
    unfold next in Hseen |- *.
    cbn [PreRename.visited] in Hseen.
    rewrite FinSet.mem_add in Hseen by exact (visit_seen_wf _ Hvisit).
    apply orb_true_iff in Hseen; destruct Hseen as [Hsame|Hseen].
    + apply (eqb_true_iff _ positive_encoding_laws) in Hsame; subst parent.
      right; exists (fst (PreRename.block c index b frames (PreRename.output current))).
      apply in_or_app; left; apply in_map_iff; exists (child, id); split; [reflexivity|].
      apply children_exact; exact Hparent.
    + apply Hadvance; exact (visit_children _ Hvisit child parent Hparent Hseen).
Qed.

Local Lemma step_visit_laws current next :
  visit_laws current -> PreRename.step c index current = inl next -> visit_laws next.
Proof.
  intros Hvisit Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)) eqn:Hseen.
  - inversion Hstep; subst next; eapply skip_visit_laws; eassumption.
  - destruct (Prepared.name_of (Pre.blocks c) id) as [b|]; [|discriminate].
    inversion Hstep; subst next; eapply add_visit_laws; eassumption.
Qed.

(** Every continuing actual driver history retains root and child coverage. *)
Theorem runs_visit_laws :
  forall budget current final, runs (PreRename.step_c c index) budget current (inl final) ->
    visit_laws current -> visit_laws final.
Proof.
  intros budget current final Hrun; remember (inl final) as result eqn:Hresult.
  revert final Hresult.
  induction Hrun as [current|budget current stopped Hstop|
    budget current next result Hstep Hrun IH]; intros final Hresult Hvisit.
  - inversion Hresult; subst final; exact Hvisit.
  - discriminate.
  - apply (IH final Hresult); eapply step_visit_laws; eassumption.
Qed.

Local Lemma all_scheduled_seen current :
  visit_laws current -> PreRename.pending current = [] ->
  forall id, In id (PreRename.root_ids index) ->
  forall other, idom_ancestor (Dom.idom (Pre.dom c)) id other ->
    FinSet.mem positive_encoding other (PreRename.visited current) = true.
Proof.
  intros Hvisit Hempty root Hroot other Hancestor.
  assert (Hscheduled : forall id, scheduled current id ->
    FinSet.mem positive_encoding id (PreRename.visited current) = true).
  { intros id [Hseen|[frames Hin]]; [exact Hseen|rewrite Hempty in Hin; contradiction]. }
  assert (Hroot_seen := Hscheduled root (visit_roots _ Hvisit root Hroot)).
  clear Hroot.
  revert Hroot_seen; induction Hancestor as [parent child Hparent|id|start mid finish Hfirst IHfirst
    Hlast IHlast]; intro Hseen.
  - apply Hscheduled; exact (visit_children _ Hvisit child parent Hparent Hseen).
  - exact Hseen.
  - apply IHlast; apply IHfirst; exact Hseen.
Qed.

(** Unique-entry dominance places every named block below an actually scheduled root. *)
Theorem block_below_root :
  forall b id, In b (Graph.nodes (Pre.bg c)) -> Prepared.id_of (Pre.blocks c) b = Some id ->
    exists root, In root (PreRename.root_ids index) /\
      idom_ancestor (Dom.idom (Pre.dom c)) root id.
Proof.
  intros b id Hb Hid.
  pose proof (Pre.blocks_ready c (Pre.graphs c Hlaw)) as Hready.
  pose proof (proj2 (proj2 Hready)) as Hp.
  destruct (Pre.entry_position c (Pre.graphs c Hlaw)) as [entry [point [Hentry Hrest]]].
  assert (Hentry_listed : In entry (Graph.nodes (Prepared.graph (Pre.blocks c)))).
  { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)).
    apply (entries_in (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))).
    change (In entry (Graph.entries (Pre.bg c))).
    rewrite Hentry; now left. }
  destruct (proj1 (Prepared.ids_domain _ Hp entry) Hentry_listed) as [root Hroot].
  exists root; split.
  - unfold index; rewrite (proj1 (PreRename.prepare_walk_equations c data)).
    apply (Prepared.entry_ids_spec _ _ Hp); exists entry; split; [|exact Hroot].
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)), Hentry; now left.
  - assert (Hreach : reachable (Prepared.graph (Pre.blocks c)) b).
    { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)).
      exact (Pre.reachable_blocks c (Pre.graphs c Hlaw) b Hb). }
    apply (proj2 (DomCheck.ancestry_spec _ _ _ _ _ _ Hready
      (Pre.tree_exact c (Pre.graphs c Hlaw)) Hreach Hid Hroot)).
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)).
    intros start es Hstart Hpath; rewrite Hentry in Hstart; destruct Hstart as [<-|[]]; now left.
Qed.

Local Lemma completed_stop_empty current final :
  PreRename.step c index current = inr final ->
  PreRename.stop_status final = PreFrg.Completed ->
    PreRename.pending current = [] /\ PreRename.stop_output final = PreRename.output current.
Proof.
  intros Hstop Hcompleted; rewrite PreRename.step_equation in Hstop.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending.
  - inversion Hstop; auto.
  - destruct (FinSet.mem positive_encoding id (PreRename.visited current)); [discriminate|].
    destruct (Prepared.name_of (Pre.blocks c) id); [discriminate|].
    inversion Hstop; subst final; discriminate.
Qed.

(** The actual lawful run has a completed empty-worklist prefix, not just a completion flag. *)
Theorem run_finished_state :
  exists budget last,
    runs (PreRename.step_c c index) budget (PreRename.initial index) (inl last) /\
    PreRename.pending last = [] /\
    PreRename.stop_output (PreRename.run c index) = PreRename.output last /\
    visit_laws last.
Proof.
  pose proof (iterate_value (PreRename.step_c c index) (PreRename.walk_budget index)
    (PreRename.initial index)) as Hrun.
  pose proof (PreRename.run_completed c index (PreRename.prepare_walk_domain c data Hlaw))
    as Hcompleted.
  rewrite PreRename.run_equation in Hcompleted |- *.
  destruct (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
    (PreRename.initial index))) as [remaining|final] eqn:Hresult; [discriminate|].
  destruct (runs_inr_stop (PreRename.step_c c index) _ _ _ Hrun)
    as [used [last [Hused [Hprefix Hstop]]]].
  destruct (completed_stop_empty last final Hstop Hcompleted) as [Hempty Houtput].
  exists used, last; split; [exact Hprefix|]; split; [exact Hempty|].
  split; [exact Houtput|].
  exact (runs_visit_laws used _ _ Hprefix initial_visit_laws).
Qed.

(** In the completed prefix every named source block was actually processed by the indexed walk. *)
Theorem completed_blocks_seen current :
  visit_laws current -> PreRename.pending current = [] ->
  forall b id, In b (Graph.nodes (Pre.bg c)) -> Prepared.id_of (Pre.blocks c) b = Some id ->
    FinSet.mem positive_encoding id (PreRename.visited current) = true.
Proof.
  intros Hvisit Hempty b id Hb Hid.
  destruct (block_below_root b id Hb Hid) as [root [Hroot Hancestor]].
  exact (all_scheduled_seen current Hvisit Hempty root Hroot id Hancestor).
Qed.

Hypothesis Hdata : PreFrameCache.placement_laws c data.

(** Presence observes occurrence-map domain, independently of which reusable version was selected. *)
Definition present (acc : PreRename.accumulator B BE E U) e : Prop :=
  exists d, Map.get (Pre.ee (Pre.keys c)) e (PreRename.occurrence_index acc) = Some d.

Local Lemma mark_occurrences frames acc key :
  PreRename.occurrence_index (PreRename.mark c frames acc key) =
    PreRename.occurrence_index acc.
Proof.
  rewrite PreRename.mark_equation.
  destruct (PreRename.selected (PreRename.top_id frames (fst key) (snd key))) as [d real].
  destruct d, real; reflexivity.
Qed.

Local Lemma fold_mark_occurrences frames :
  forall keys acc, PreRename.occurrence_index (fold_left (PreRename.mark c frames) keys acc) =
    PreRename.occurrence_index acc.
Proof.
  intro keys; induction keys as [|key rest IH]; intro acc; cbn [fold_left]; [reflexivity|].
  rewrite IH; apply mark_occurrences.
Qed.

Local Lemma mark_exit_occurrences n work :
  PreRename.occurrence_index (snd (PreRename.mark_exit c index n work)) =
    PreRename.occurrence_index (snd work).
Proof.
  rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index));
    [apply fold_mark_occurrences|reflexivity].
Qed.

Local Lemma alter_occurrences instance work key :
  PreRename.occurrence_index (snd (PreRename.alter c instance work key)) =
    PreRename.occurrence_index (snd work).
Proof.
  rewrite PreRename.alter_equation; destruct work as [frames acc]; cbn [snd].
  destruct instance as [current|].
  - destruct (eqb positive_encoding (fst current) (fst key));
      [reflexivity|apply mark_occurrences].
  - apply mark_occurrences.
Qed.

Local Lemma fold_alter_occurrences instance :
  forall keys work,
    PreRename.occurrence_index (snd (fold_left (PreRename.alter c instance) keys work)) =
      PreRename.occurrence_index (snd work).
Proof.
  intro keys; induction keys as [|key rest IH]; intro work; cbn [fold_left]; [reflexivity|].
  rewrite IH; apply alter_occurrences.
Qed.

Local Lemma instruction_occurrences b parameter work e :
  PreRename.occurrence_index (snd (PreRename.instruction c index b parameter work e)) =
    match Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index) with
    | None => PreRename.occurrence_index (snd work)
    | Some info => PreRename.occurrence_index
        (snd (fst (PreRename.occurrence c e (PreRename.evaluation info) work)))
    end.
Proof.
  rewrite PreRename.instruction_equation.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index)) as [info|]; [|reflexivity].
  rewrite mark_exit_occurrences; cbn [snd]; apply fold_alter_occurrences.
Qed.

Local Lemma occurrence_keeps e instance work :
  Map.wf (Pre.ee (Pre.keys c)) (PreRename.occurrence_index (snd work)) ->
  forall query, present (snd work) query ->
    present (snd (fst (PreRename.occurrence c e instance work))) query.
Proof.
  intros Hwf query [d Hget]; rewrite PreRename.occurrence_equation.
  destruct instance as [[id u]|]; [|now exists d].
  destruct work as [frames acc]; cbn zeta.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u);
    cbn [fst snd]; unfold present; cbn [PreRename.occurrence_index].
  all: rewrite Map.get_set by exact Hwf.
  all: destruct (eqb (Pre.ee (Pre.keys c)) query e); eauto.
Qed.

Local Lemma instruction_keeps b parameter work e :
  PreFrameEnd.accumulator_wf c (snd work) ->
  forall query, present (snd work) query ->
    present (snd (PreRename.instruction c index b parameter work e)) query.
Proof.
  intros Hwf query Hpresent; unfold present; rewrite instruction_occurrences.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index)) as [info|];
    [|exact Hpresent].
  apply occurrence_keeps; [exact (proj1 Hwf)|exact Hpresent].
Qed.

Local Lemma instruction_sets b parameter work e u :
  PreFrameEnd.accumulator_wf c (snd work) ->
  In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    present (snd (PreRename.instruction c index b parameter work e)) e.
Proof.
  intros Hwf He Hcomputed Hpure; unfold present; rewrite instruction_occurrences.
  pose proof (PreFrameCache.event_lookup c data Hlaw e He) as Hlookup.
  fold index in Hlookup; rewrite Hlookup.
  destruct (PreFrameCache.evaluation_available c data Hlaw Hdata e u Hcomputed Hpure)
    as [id [Hevaluation Hid]].
  rewrite PreRename.occurrence_equation, Hevaluation.
  destruct work as [frames acc]; cbn zeta.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u); cbn [fst snd];
    cbn [PreRename.occurrence_index]; rewrite Map.get_set_same by exact (proj1 Hwf); eauto.
Qed.

Local Lemma fold_instructions_keeps b parameter :
  forall es work, PreFrameEnd.accumulator_wf c (snd work) ->
  forall query, present (snd work) query ->
    present (snd (fold_left (PreRename.instruction c index b parameter) es work)) query.
Proof.
  intro es; induction es as [|e rest IH]; intros work Hwf query Hpresent; cbn [fold_left].
  - exact Hpresent.
  - apply IH; [apply PreFrameEnd.instruction_wf; exact Hwf|].
    apply instruction_keeps; assumption.
Qed.

Local Lemma fold_instructions_total b parameter :
  forall es work, PreFrameEnd.accumulator_wf c (snd work) ->
  forall e u, In e es -> In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
      present (snd (fold_left (PreRename.instruction c index b parameter) es work)) e.
Proof.
  intro es; induction es as [|head rest IH]; intros work Hwf e u Hin He Hcomputed Hpure;
    [contradiction|]; cbn [fold_left]; destruct Hin as [<-|Hin].
  - apply fold_instructions_keeps; [apply PreFrameEnd.instruction_wf; exact Hwf|].
    exact (instruction_sets b parameter work head u Hwf He Hcomputed Hpure).
  - apply (IH _ (PreFrameEnd.instruction_wf c Hwf) e u Hin He Hcomputed Hpure).
Qed.

Local Lemma argument_occurrences frames acc arg :
  PreRename.occurrence_index (PreRename.select_argument c frames acc arg) =
    PreRename.occurrence_index acc.
Proof.
  rewrite PreRename.select_argument_equation; reflexivity.
Qed.

Local Lemma fold_argument_occurrences frames :
  forall (args : list (B * PreRename.argument B BE U)) acc,
    PreRename.occurrence_index
      (fold_left (fun current pair => PreRename.select_argument c frames current (snd pair))
        args acc) = PreRename.occurrence_index acc.
Proof.
  intro args; induction args as [|pair rest IH]; intro acc; cbn [fold_left]; [reflexivity|].
  rewrite IH; apply argument_occurrences.
Qed.

Local Lemma block_keeps b frames acc :
  PreFrameEnd.accumulator_wf c acc ->
  forall e, present acc e -> present (snd (PreRename.block c index b frames acc)) e.
Proof.
  intros Hwf e Hpresent; rewrite PreRename.block_equation.
  unfold present; cbn [snd]; rewrite fold_argument_occurrences; fold (present).
  apply fold_instructions_keeps.
  - destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hwf|].
    apply PreFrameEnd.mark_exit_wf; exact Hwf.
  - unfold present; destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hpresent|rewrite mark_exit_occurrences; exact Hpresent].
Qed.

Local Lemma block_sets b frames acc e u :
  PreFrameEnd.accumulator_wf c acc ->
  In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
  In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    present (snd (PreRename.block c index b frames acc)) e.
Proof.
  intros Hwf Hin He Hcomputed Hpure; rewrite PreRename.block_equation.
  unfold present; cbn [snd]; rewrite fold_argument_occurrences; fold present.
  eapply fold_instructions_total.
  - destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hwf|apply PreFrameEnd.mark_exit_wf; exact Hwf].
  - exact Hin.
  - exact He.
  - exact Hcomputed.
  - exact Hpure.
Qed.

(** Every visited named block has already installed all eligible occurrences in its ordered body. *)
Record processed_laws (current : PreRename.work B BE E U) : Prop := ProcessedLaws {
  processed_visit : visit_laws current;
  processed_output_wf : PreFrameEnd.accumulator_wf c (PreRename.output current);
  processed_occurrences : forall id b e u,
    FinSet.mem positive_encoding id (PreRename.visited current) = true ->
    Prepared.name_of (Pre.blocks c) id = Some b ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u -> Pre.pure c u = true ->
      present (PreRename.output current) e
}.

Local Lemma initial_processed_laws : processed_laws (PreRename.initial index).
Proof.
  constructor; [exact initial_visit_laws| |].
  - rewrite PreRename.initial_equation; exact (PreFrameEnd.empty_accumulator_wf c).
  - intros id b e u Hseen; rewrite PreRename.initial_equation in Hseen.
    cbn [PreRename.visited] in Hseen; rewrite FinSet.mem_empty in Hseen; discriminate.
Qed.

Local Lemma added_processed current id frames rest b :
  processed_laws current ->
  PreRename.pending current = (id, frames) :: rest ->
  Prepared.name_of (Pre.blocks c) id = Some b ->
  forall query owner e u,
    FinSet.mem positive_encoding query
      (FinSet.add positive_encoding id (PreRename.visited current)) = true ->
    Prepared.name_of (Pre.blocks c) query = Some owner ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) owner) ->
    In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    present (snd (PreRename.block c index b frames (PreRename.output current))) e.
Proof.
  intros Hprocessed Hpending Hname query owner e u Hseen Howner Hin He Hcomputed Hpure.
  rewrite FinSet.mem_add in Hseen by
    exact (visit_seen_wf _ (processed_visit _ Hprocessed)).
  apply orb_true_iff in Hseen; destruct Hseen as [Hsame|Hseen].
  - apply (eqb_true_iff _ positive_encoding_laws) in Hsame; subst query.
    assert (owner = b) by congruence; subst owner.
    apply (block_sets b frames _ e u); try assumption; exact (processed_output_wf _ Hprocessed).
  - apply block_keeps; [exact (processed_output_wf _ Hprocessed)|].
    exact (processed_occurrences _ Hprocessed query owner e u
      Hseen Howner Hin He Hcomputed Hpure).
Qed.

Local Lemma step_processed_laws current next :
  processed_laws current -> PreRename.step c index current = inl next -> processed_laws next.
Proof.
  intros Hprocessed Hstep.
  pose proof (step_visit_laws current next (processed_visit _ Hprocessed) Hstep) as Hvisit.
  rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)).
  - inversion Hstep; subst next; constructor; [exact Hvisit| |].
    + exact (processed_output_wf _ Hprocessed).
    + exact (processed_occurrences _ Hprocessed).
  - destruct (Prepared.name_of (Pre.blocks c) id) as [b|] eqn:Hname; [|discriminate].
    inversion Hstep; subst next; constructor; [exact Hvisit| |].
    + apply PreFrameEnd.block_wf; exact (processed_output_wf _ Hprocessed).
    + cbn [PreRename.visited PreRename.output].
      exact (added_processed current id frames rest b Hprocessed Hpending Hname).
Qed.

Local Lemma runs_processed_laws :
  forall budget current final, runs (PreRename.step_c c index) budget current (inl final) ->
    processed_laws current -> processed_laws final.
Proof.
  intros budget current final Hrun; remember (inl final) as result eqn:Hresult.
  revert final Hresult.
  induction Hrun as [current|budget current stopped Hstop|
    budget current next result Hstep Hrun IH]; intros final Hresult Hprocessed.
  - inversion Hresult; subst final; exact Hprocessed.
  - discriminate.
  - apply (IH final Hresult); eapply step_processed_laws; eassumption.
Qed.

(** Every listed pure recomputation is actually installed before the completed walk stops. *)
Theorem run_occurrence_total :
  forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
      present (PreRename.stop_output (PreRename.run c index)) e.
Proof.
  intros e u He Hcomputed Hpure.
  destruct (run_finished_state) as [budget [last [Hprefix [Hempty [Houtput Hvisit]]]]].
  pose proof (runs_processed_laws budget _ _ Hprefix initial_processed_laws) as Hprocessed.
  destruct (PreFrg.internal_edge_block c Hlaw He
    (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)))
    as [b [Hb [Hin Htarget]]].
  pose proof (Pre.blocks_ready c (Pre.graphs c Hlaw)) as Hready.
  assert (Hb' : In b (Graph.nodes (Prepared.graph (Pre.blocks c)))).
  { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)); exact Hb. }
  destruct (proj1 (Prepared.ids_domain _ (proj2 (proj2 Hready)) b) Hb') as [id Hid].
  rewrite Houtput; apply (processed_occurrences _ Hprocessed id b e u).
  - exact (completed_blocks_seen last Hvisit Hempty b id Hb Hid).
  - exact (Prepared.name_of_id_of _ _ _ (proj2 (proj2 Hready)) Hid).
  - exact Hin.
  - exact He.
  - exact Hcomputed.
  - exact Hpure.
Qed.

End Coverage.

End PreFrameVisit.
