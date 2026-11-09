(** * Total incoming selections from processed source blocks

    Visiting a block writes each prepared outgoing argument and later visits retain its key.
    For example, both incoming edge identities of a join acquire separate operand entries.
    Builds on: AnalysesSsaPreFrameVisit, AnalysesSsaPreFrameInvariant and BaseMap. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreFrameCache AnalysesSsaPreFrameStep AnalysesSsaPreFrameEnd
  AnalysesSsaPreCoverage AnalysesSsaPreFrameInvariant AnalysesSsaPreFrameVisit
  AnalysesSsaPreFrameDominance AnalysesSsaPreFrameTables AnalysesSsaPreFrameWalk
  AnalysesSsaPreFrameHistory AnalysesSsaPreFrameOccurrence AnalysesSsaPreFrameEdges.
Import List.ListNotations.

Module PreFrameIncoming.

Section Total.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Hypothesis Hlaw : Pre.laws c.
Let index := PreRename.prepare c data.

Definition present (acc : PreRename.accumulator B BE E U) key : Prop :=
  exists op, Map.get (PreFrg.link_encoding c) key (PreRename.link_index acc) = Some op.

Local Lemma argument_keeps frames acc arg :
  Map.wf (PreFrg.link_encoding c) (PreRename.link_index acc) ->
  forall key, present acc key -> present (PreRename.select_argument c frames acc arg) key.
Proof.
  intros Hwf key [op Hget]; unfold present; rewrite PreRename.select_argument_equation.
  cbn zeta; cbn [PreRename.link_index]; rewrite Map.get_set by exact Hwf.
  destruct (eqb (PreFrg.link_encoding c) key
    (PreRename.argument_phi arg, PreRename.argument_edge arg)); eauto.
Qed.

Local Lemma argument_sets frames acc arg :
  Map.wf (PreFrg.link_encoding c) (PreRename.link_index acc) ->
    present (PreRename.select_argument c frames acc arg)
      (PreRename.argument_phi arg, PreRename.argument_edge arg).
Proof.
  intro Hwf; unfold present; rewrite PreRename.select_argument_equation.
  cbn zeta; cbn [PreRename.link_index]; rewrite Map.get_set_same by exact Hwf; eauto.
Qed.

Local Lemma arguments_keep frames :
  forall (args : list (B * PreRename.argument B BE U)) acc, PreFrameEnd.accumulator_wf c acc ->
  forall key, present acc key ->
    present (fold_left (fun acc pair => PreRename.select_argument c frames acc (snd pair))
      args acc) key.
Proof.
  intro args; induction args as [|pair rest IH]; intros acc Hwf key Hpresent; [exact Hpresent|].
  cbn [fold_left]; apply IH.
  - apply PreFrameEnd.argument_wf; exact Hwf.
  - apply argument_keeps; [exact (proj1 (proj2 (proj2 Hwf)))|exact Hpresent].
Qed.

Local Lemma arguments_set frames :
  forall (args : list (B * PreRename.argument B BE U)) acc, PreFrameEnd.accumulator_wf c acc ->
  forall pair, In pair args ->
    present (fold_left (fun acc pair => PreRename.select_argument c frames acc (snd pair))
      args acc) (PreRename.argument_phi (snd pair), PreRename.argument_edge (snd pair)).
Proof.
  intro args; induction args as [|pair rest IH]; intros acc Hwf query Hin; [contradiction|].
  cbn [fold_left]; destruct Hin as [<-|Hin].
  - apply arguments_keep.
    + apply PreFrameEnd.argument_wf; exact Hwf.
    + apply argument_sets; exact (proj1 (proj2 (proj2 Hwf))).
  - apply IH; [apply PreFrameEnd.argument_wf; exact Hwf|exact Hin].
Qed.

(** The instruction body leaves incoming operands unchanged before its outgoing argument fold. *)
Theorem block_body_links b frames acc :
  let entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
  | [] => (frames, acc)
  | point :: _ => PreRename.mark_exit c index point (frames, acc)
  end in
  let body := fold_left (PreRename.instruction c index b
    (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
    (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered in
  PreRename.link_index (snd body) = PreRename.link_index acc.
Proof.
  intros entered body; unfold body.
  rewrite (PreFrameStep.fold_observation _ (fun work => PreRename.link_index (snd work))
    (fun work edge => PreFrameInvariant.instruction_links c data b)).
  unfold entered; destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
    [reflexivity|apply PreFrameInvariant.mark_exit_links].
Qed.

Local Lemma body_wf b frames acc :
  PreFrameEnd.accumulator_wf c acc ->
    PreFrameEnd.accumulator_wf c
      (snd (fold_left (PreRename.instruction c index b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
        (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b)
        (match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
        | [] => (frames, acc)
        | point :: _ => PreRename.mark_exit c index point (frames, acc)
        end))).
Proof.
  intro Hwf; apply (PreFrameStep.fold_preserves _
    (fun work => PreFrameEnd.accumulator_wf c (snd work))).
  - intros work edge Hwork; apply PreFrameEnd.instruction_wf; exact Hwork.
  - destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hwf|apply PreFrameEnd.mark_exit_wf; exact Hwf].
Qed.

Local Lemma block_keeps b frames acc :
  PreFrameEnd.accumulator_wf c acc ->
  forall key, present acc key -> present (snd (PreRename.block c index b frames acc)) key.
Proof.
  intros Hwf key Hpresent; rewrite PreRename.block_equation; cbn [snd].
  apply arguments_keep; [exact (body_wf b frames acc Hwf)|].
  unfold present; rewrite block_body_links; exact Hpresent.
Qed.

Local Lemma block_sets b frames acc :
  PreFrameEnd.accumulator_wf c acc ->
  forall pair, In pair (Index.find (Pre.eb (Pre.keys c)) b (PreRename.arguments index)) ->
    present (snd (PreRename.block c index b frames acc))
      (PreRename.argument_phi (snd pair), PreRename.argument_edge (snd pair)).
Proof.
  intros Hwf pair Hin; rewrite PreRename.block_equation; cbn [snd].
  apply arguments_set; [exact (body_wf b frames acc Hwf)|exact Hin].
Qed.

(** Every visited source block has written all of its prepared outgoing argument keys. *)
Definition seen_total (current : PreRename.work B BE E U) : Prop :=
  FinSet.wf positive_encoding (PreRename.visited current) /\
  PreFrameEnd.accumulator_wf c (PreRename.output current) /\
  forall id b, Prepared.name_of (Pre.blocks c) id = Some b ->
    FinSet.mem positive_encoding id (PreRename.visited current) = true ->
  forall pair, In pair (Index.find (Pre.eb (Pre.keys c)) b (PreRename.arguments index)) ->
    present (PreRename.output current)
      (PreRename.argument_phi (snd pair), PreRename.argument_edge (snd pair)).

Local Lemma initial_total : seen_total (PreRename.initial index).
Proof.
  rewrite PreRename.initial_equation; split; [apply FinSet.wf_empty|].
  split; [apply PreFrameEnd.empty_accumulator_wf|].
  intros id b Hname Hseen; cbn [PreRename.visited] in Hseen.
  rewrite FinSet.mem_empty in Hseen; discriminate.
Qed.

Local Lemma step_total {current next} :
  seen_total current -> PreRename.step c index current = inl next -> seen_total next.
Proof.
  intros [Hseen_wf [Hwf Htotal]] Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest]; [discriminate|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)) eqn:Hseen.
  - inversion Hstep; subst next; split; [exact Hseen_wf|]; split; [exact Hwf|exact Htotal].
  - destruct (Prepared.name_of (Pre.blocks c) id) as [b|] eqn:Hname; [|discriminate].
    inversion Hstep; subst next; split; [apply FinSet.wf_add; exact Hseen_wf|].
    split; [apply PreFrameEnd.block_wf; exact Hwf|].
    intros other owner Howner Hvisited pair Hpair.
    cbn [PreRename.visited] in Hvisited.
    rewrite FinSet.mem_add in Hvisited by exact Hseen_wf.
    apply orb_true_iff in Hvisited; destruct Hvisited as [Hsame|Hold].
    + apply (eqb_true_iff _ positive_encoding_laws) in Hsame; subst other.
      assert (Hblock : owner = b) by congruence; subst owner.
      apply block_sets; assumption.
    + apply block_keeps; [exact Hwf|exact (Htotal other owner Howner Hold pair Hpair)].
Qed.

Local Lemma runs_total :
  forall budget current last, runs (PreRename.step_c c index) budget current (inl last) ->
    seen_total current -> seen_total last.
Proof.
  intros budget current last Hrun; remember (inl last) as result eqn:Hresult.
  revert last Hresult; induction Hrun as [current|budget current stopped Hstop|
    budget current next result Hstep Hrun IH]; intros last Hresult Htotal.
  - inversion Hresult; subst last; exact Htotal.
  - discriminate.
  - apply (IH last Hresult); exact (step_total Htotal Hstep).
Qed.

(** Every required incoming phi edge is present after the actual lawful indexed run completes. *)
Theorem run_total :
  PreFrameCache.placement_laws c data ->
  forall b u be, PreFrg.phi_needed c u b -> Pre.pure c u = true ->
    In be (Cfg.edges (Pre.block_cfg c)) -> Graph.target (Pre.bg c) be = b ->
    present (PreRename.stop_output (PreRename.run c index)) ((b, u), be).
Proof.
  intros Hdata b u be Hphi Hpure Hbe Htarget.
  destruct (PreFrameCache.arguments_total c data Hlaw Hdata u b be Hphi Hpure Hbe Htarget)
    as [v [id [Htranslate [Hid Harg]]]].
  destruct (PreFrameVisit.run_finished_state c data Hlaw)
    as [budget [last [Hprefix [Hempty [Houtput Hvisit]]]]].
  pose proof (runs_total _ _ _ Hprefix initial_total) as [_ [Hwf Htotal]].
  pose proof Hbe as Hlisted; apply Cfg.edges_spec in Hlisted.
  destruct Hlisted as [source [Hsource Hout]].
  pose proof (out_source (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
    source be Hout) as Howner.
  change (Graph.source (Pre.bg c) be = source) in Howner; subst source.
  pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
  assert (Hsource' : In (Graph.source (Pre.bg c) be) (Graph.nodes (Prepared.graph (Pre.blocks c)))).
  { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)); exact Hsource. }
  destruct (proj1 (Prepared.ids_domain _ Hp _) Hsource') as [source_id Hsource_id].
  fold index in Houtput; rewrite Houtput.
  exact (Htotal source_id _ (Prepared.name_of_id_of _ _ _ Hp Hsource_id)
    (PreFrameVisit.completed_blocks_seen c data Hlaw last Hvisit Hempty _ source_id
      Hsource Hsource_id) _ Harg).
Qed.

End Total.

Section Meaning.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Context {g : PreFrg.frg B BE E U}.
Variable final : PreRename.accumulator B BE E U.
Hypothesis Hlaw : Pre.laws c.
Hypothesis Hdata : PreFrameCache.placement_laws c data.
Let index := PreRename.prepare c data.
Let points := Pre.points (Pre.input c).

(** Incoming meaning retains the selected source frame at the indexed crossing point. *)
Definition link_meaning (key : (B * U) * BE) (op : PreFrg.operand B E U) : Prop :=
  exists pe v frame,
    Map.get (Pre.ebe (Pre.keys c)) (snd key) (PreFrameEdges.point_edge_index c) = Some pe /\
    Pre.translate c (snd key) (snd (fst key)) = Some v /\
    PreFamily.in_family c v /\ Pre.pure c v = true /\
    PreCoverage.frame_laws c g v (Graph.source (Pre.pg c) pe) frame /\
    op = if PreRename.available frame then PreRename.selected frame
      else PreFrg.Operand (PreFrg.Unavailable v) false.

Definition output_meaning (acc : PreRename.accumulator B BE E U) : Prop :=
  forall key op, Map.get (PreFrg.link_encoding c) key (PreRename.link_index acc) = Some op ->
    link_meaning key op.

Local Definition argument_value (frames : PreRename.scope B E U) (arg : PreRename.argument B BE U) :=
  let v := PreRename.argument_input arg in
  let frame := match PreRename.argument_id arg with
  | None => PreRename.missing v
  | Some id => PreRename.top_id frames id v
  end in
  if (if PreRename.available frame then
    eqb (Pre.eu (Pre.keys c)) (PreFrg.version_expr
      (PreFrg.operand_version (PreRename.selected frame))) v else false)
  then PreRename.selected frame else PreFrg.Operand (PreFrg.Unavailable v) false.

Local Lemma argument_links frames acc arg :
  PreRename.link_index (PreRename.select_argument c frames acc arg) =
    Map.set (PreFrg.link_encoding c) (PreRename.argument_phi arg, PreRename.argument_edge arg)
      (argument_value frames arg) (PreRename.link_index acc).
Proof.
  rewrite PreRename.select_argument_equation; reflexivity.
Qed.

Local Lemma argument_meaning source default frames pair :
  In source (Graph.nodes (Pre.bg c)) ->
  PreFrameInvariant.scope_source c data frames ->
  PreCoverage.scope_laws c g (last (SsaPoints.points_in_block points source) default) frames ->
  In pair (Index.find (Pre.eb (Pre.keys c)) source (PreRename.arguments index)) ->
    link_meaning (PreRename.argument_phi (snd pair), PreRename.argument_edge (snd pair))
      (argument_value frames (snd pair)).
Proof.
  intros Hsource Hframes Hscope Hpair.
  destruct (PreFrameCache.argument_bucket c data Hlaw Hdata source pair Hpair) as [Howner Harg].
  destruct pair as [owner [[b u] be v id]]; cbn [fst] in Howner; subst owner.
  cbn [fst snd PreRename.argument_phi PreRename.argument_edge PreRename.argument_input
    PreRename.argument_id] in Harg.
  destruct Harg as [Hphi [Hpure [Hbe [Htarget [Htranslate [Hfamily [Hvpure
    [found [Hid Hfind]]]]]]]]].
  assert (Hedge_source : Graph.source (Pre.bg c) be = source).
  { apply (PreFrameCache.arguments_exact c data Hlaw Hdata) in Hpair; tauto. }
  destruct (PreFrameEdges.point_edge_index_total c Hlaw be Hbe) as [pe Hpe].
  pose proof (proj1 (PreFrameEdges.point_edge_boundary c Hlaw be pe Hpe)) as Hlast.
  rewrite Hedge_source in Hlast.
  assert (Hpoint : last (SsaPoints.points_in_block points source) default =
    Graph.source (Pre.pg c) pe).
  { rewrite <- Hlast; apply PreFrameDominance.last_default.
    exact (blocks_nonempty (Pre.point_laws c (Pre.graphs c Hlaw)) source Hsource). }
  rewrite Hpoint in Hscope.
  pose proof (Hscope v Hfamily Hvpure) as Hframe.
  exists pe, v, (PreRename.top c frames v).
  split; [exact Hpe|]; split; [exact Htranslate|]; split; [exact Hfamily|].
  split; [exact Hvpure|]; split; [exact Hframe|].
  cbn [snd]; unfold argument_value; cbn [PreRename.argument_input PreRename.argument_id].
  rewrite Hid.
  rewrite <- (PreFrameCache.top_id_agrees c (frames := frames) (u := v) (id := found)).
  2: { rewrite (PreFrameInvariant.scope_symbols c data frames Hframes); exact Hfind. }
  rewrite (proj1 Hframe), eqb_refl.
  destruct (PreRename.available (PreRename.top c frames v)); reflexivity.
Qed.

Local Lemma argument_preserves source default frames pair acc :
  In source (Graph.nodes (Pre.bg c)) ->
  PreFrameInvariant.scope_source c data frames ->
  PreCoverage.scope_laws c g (last (SsaPoints.points_in_block points source) default) frames ->
  In pair (Index.find (Pre.eb (Pre.keys c)) source (PreRename.arguments index)) ->
  PreFrameEnd.accumulator_wf c acc -> output_meaning acc ->
    output_meaning (PreRename.select_argument c frames acc (snd pair)).
Proof.
  intros Hsource Hframes Hscope Hpair Hwf Hmeaning key op Hget.
  rewrite argument_links, Map.get_set in Hget by exact (proj1 (proj2 (proj2 Hwf))).
  destruct (eqb (PreFrg.link_encoding c) key
    (PreRename.argument_phi (snd pair), PreRename.argument_edge (snd pair))) eqn:Hsame.
  - apply (eqb_true_iff _ (PreFrg.link_encoding_laws c Hlaw)) in Hsame; subst key.
    inversion Hget; subst op; exact (argument_meaning source default frames pair
      Hsource Hframes Hscope Hpair).
  - exact (Hmeaning key op Hget).
Qed.

Local Lemma block_meaning b first frames acc :
  In b (Graph.nodes (Pre.bg c)) ->
  PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
  PreCoverage.scope_laws c g (last (SsaPoints.points_in_block points b) first)
    (fst (PreRename.block c index b frames acc)) ->
  output_meaning acc -> output_meaning (snd (PreRename.block c index b frames acc)).
Proof.
  intros Hb Hframes Hwf Hscope Hmeaning.
  pose proof (PreFrameInvariant.block_source c data Hlaw Hdata b frames acc Hframes) as Hbody_source.
  rewrite PreRename.block_equation in Hscope, Hbody_source |- *.
  set (entered := match SsaPoints.points_in_block points b with
  | [] => (frames, acc)
  | point :: _ => PreRename.mark_exit c index point (frames, acc)
  end) in *.
  set (body := fold_left (PreRename.instruction c index b (SsaPoints.parameter_edge points b))
    (SsaPoints.instruction_edges points b) entered) in *.
  cbn [fst snd] in Hscope, Hbody_source |- *.
  assert (Hbody_wf : PreFrameEnd.accumulator_wf c (snd body)) by
    exact (body_wf c data b frames acc Hwf).
  assert (Hbody_meaning : output_meaning (snd body)).
  { intros key op Hget; apply (Hmeaning key op).
    pose proof (block_body_links c data b frames acc) as Hlinks.
    change (PreRename.link_index (snd body) = PreRename.link_index acc) in Hlinks.
    rewrite Hlinks in Hget; exact Hget. }
  assert (Hfold : forall args current,
    Forall (fun pair => In pair (Index.find (Pre.eb (Pre.keys c)) b (PreRename.arguments index))) args ->
    PreFrameEnd.accumulator_wf c current -> output_meaning current ->
    output_meaning (fold_left (fun acc pair => PreRename.select_argument c (fst body) acc (snd pair))
      args current)).
  { intros args current Hargs; revert current; induction Hargs as [|pair rest Hpair Hrest IH];
      intros current Hcurrent Hcurrent_meaning; [exact Hcurrent_meaning|].
    cbn [fold_left]; apply IH.
    - apply PreFrameEnd.argument_wf; exact Hcurrent.
    - exact (argument_preserves b first (fst body) pair current
        Hb Hbody_source Hscope Hpair Hcurrent Hcurrent_meaning). }
  apply Hfold; [apply Forall_forall; auto|exact Hbody_wf|exact Hbody_meaning].
Qed.

Hypothesis Htransfer :
  forall frames acc b e, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges points b) ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreFrameTables.stamp c e acc = (None, false) ->
    PreFrameTables.stamp c e final = PreFrameTables.stamp c e
      (snd (PreRename.instruction c index b (SsaPoints.parameter_edge points b) (frames, acc) e)) ->
    PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) frames ->
    PreCoverage.scope_laws c g (Graph.target (Pre.pg c) e)
      (fst (PreRename.instruction c index b (SsaPoints.parameter_edge points b) (frames, acc) e)).

Local Lemma executed_block_meaning {current next result budget} :
  PreFrameWalk.walk_scope c data (g := g) current ->
  PreRename.step c index current = inl next ->
  runs (PreRename.step_c c index) budget next result ->
  final = PreFrameTables.output_of result ->
  output_meaning (PreRename.output current) -> output_meaning (PreRename.output next).
Proof.
  intros [Hdomains [Howned Htasks]] Hstep Hsuffix Hfinal Hmeaning.
  pose proof Hstep as Hraw; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)) eqn:Hseen.
  - inversion Hstep; subst next; exact Hmeaning.
  - pose proof (proj2 Hdomains) as Hpending_domains; rewrite Hpending in Hpending_domains.
    inversion Hpending_domains as [|pair tail Hdomain Htail]; subst pair tail.
    destruct Hdomain as [b [first [Hname [Hb [Hfirst [Hsource Hpoint]]]]]].
    cbn [fst snd] in Hname, Hsource.
    rewrite Hname in Hstep; inversion Hstep; subst next.
    apply (block_meaning b first frames (PreRename.output current)
      Hb Hsource (PreFrameTables.owned_output_wf c current Howned)); [|exact Hmeaning].
    apply (PreFrameWalk.block_scope c data final Hlaw Hdata Htransfer
      b first frames (PreRename.output current) Hb Hfirst Hsource
      (PreFrameTables.owned_output_wf c current Howned)).
    + inversion Htasks as [|pair tail Htask Hrest]; subst pair tail.
      exact (Htask b first Hname Hb Hfirst).
    + intros e He; exact (PreFrameTables.unvisited_unwritten c Hlaw Howned Hname Hseen e He).
    + intros e He; rewrite Hfinal.
      exact (PreFrameTables.block_table_final c Hlaw index current Howned _ result budget
        id frames rest b Hpending Hseen Hname Hraw Hsuffix e He).
Qed.

Local Lemma terminal_links {current stopped} :
  PreRename.step c index current = inr stopped ->
    PreRename.stop_output stopped = PreRename.output current.
Proof.
  intro Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest].
  - inversion Hstep; reflexivity.
  - destruct (FinSet.mem positive_encoding id (PreRename.visited current)); [discriminate|].
    destruct (Prepared.name_of (Pre.blocks c) id); [discriminate|].
    inversion Hstep; reflexivity.
Qed.

(** Checked histories propagate incoming selections from full source scopes to the same final table. *)
Theorem history_meaning :
  forall source labels target,
    PreFrameStep.history (PreFrameWalk.checked_step c data (g := g)) source labels target ->
    final = PreFrameTables.output_of target ->
    output_meaning (PreFrameTables.output_of source) ->
    output_meaning (PreFrameTables.output_of target).
Proof.
  intros source labels target Hhistory; induction Hhistory as
    [source|source label next rest target Hstep Hhistory IH]; intros Hfinal Hmeaning;
    [exact Hmeaning|].
  apply (IH Hfinal).
  destruct Hstep as [current [Hsource [Hscope Hstep]]]; subst source.
  destruct next as [next|stopped].
  - exact (executed_block_meaning Hscope Hstep
      (PreFrameHistory.checked_runs c data _ _ _ Hhistory next eq_refl) Hfinal Hmeaning).
  - cbn [PreFrameTables.output_of].
    rewrite (terminal_links Hstep); exact Hmeaning.
Qed.

(** The actual checked walk starts with no incoming entries and certifies every final operand. *)
Theorem run_meaning {labels target} :
  PreFrameStep.history (PreFrameWalk.checked_step c data (g := g))
    (inl (PreRename.initial index)) labels target ->
  final = PreFrameTables.output_of target -> output_meaning final.
Proof.
  intros Hhistory Hfinal; rewrite Hfinal.
  apply (history_meaning _ _ _ Hhistory Hfinal).
  intros key op Hget; rewrite PreRename.initial_equation in Hget.
  cbn [PreFrameTables.output_of PreRename.output PreRename.empty_accumulator
    PreRename.link_index] in Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

End Meaning.

End PreFrameIncoming.
