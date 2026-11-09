(** * Full semantic frames through the actual indexed walk

    Checked local instruction packets propagate nearest, availability and real-use meaning.
    For example, a child scope inherits the full meaning of its parent's final frame.
    Builds on: AnalysesSsaPreFrameTables, AnalysesSsaPreFrameMeaning and the shared Rel histories. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameCache AnalysesSsaPreFrameInvariant
  AnalysesSsaPreFrameStep AnalysesSsaPreFrameEnd AnalysesSsaPreFrameTables AnalysesSsaPreFrameMeaning
  AnalysesSsaPreFrameDominance.
Import List.ListNotations.

Module PreFrameWalk.

Section SemanticWalk.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Context {g : PreFrg.frg B BE E U}.
Variable final : PreRename.accumulator B BE E U.
Hypothesis Hlaw : Pre.laws c.
Hypothesis Hdata : PreFrameCache.placement_laws c data.
Let index := PreRename.prepare c data.
Let points := Pre.points (Pre.input c).

Hypothesis Hdefinitions :
  forall d, In d (PreFrg.versions g) -> PreFrg.definition_domain c d.
Hypothesis Hoccurrences :
  forall e d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d ->
    In e (Cfg.edges (Pre.point_cfg c)) /\ exists u, Pre.recomputed c e = Some u.
Hypothesis Hinitial :
  forall u, PreFamily.in_family c u -> Pre.pure c u = true ->
    (In (PreFrg.Initial u) (PreFrg.versions g) <-> Pre.initial c u = true).

(** The local transfer proof consumes literal packets from the same final table. *)
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

(** A certified instruction step retains its actual input frame and literal final-table packet. *)
Definition instruction_step b
    (work : PreRename.scope B E U * PreRename.accumulator B BE E U) e target : Prop :=
  PreFrameInvariant.scope_source c data (fst work) /\
  PreFrameEnd.accumulator_wf c (snd work) /\
  PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) (fst work) /\
  PreFrameTables.instruction_packet c index b (SsaPoints.parameter_edge points b) final work e /\
  target = PreRename.instruction c index b (SsaPoints.parameter_edge points b) work e.

Local Lemma chain_scope b :
  forall ns es, point_chain (Pre.pg c) ns es ->
  forall first default work, In b (Graph.nodes (Pre.bg c)) ->
    nth_error ns 0 = Some first -> incl es (SsaPoints.instruction_edges points b) ->
    PreFrameInvariant.scope_source c data (fst work) ->
    PreFrameEnd.accumulator_wf c (snd work) ->
    PreCoverage.scope_laws c g first (fst work) ->
    PreFrameStep.fold_enabled (PreRename.instruction c index b (SsaPoints.parameter_edge points b))
      (PreFrameTables.instruction_packet c index b (SsaPoints.parameter_edge points b) final) es work ->
    PreFrameStep.history (instruction_step b) work es
      (fold_left (PreRename.instruction c index b (SsaPoints.parameter_edge points b)) es work) /\
    PreCoverage.scope_laws c g (last ns default)
      (fst (fold_left (PreRename.instruction c index b (SsaPoints.parameter_edge points b)) es work)).
Proof.
  intros ns es Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intros first default [frames acc] Hb Hfirst Hedges Hsource Hwf Hscope Henabled.
  - cbn [nth_error] in Hfirst; inversion Hfirst; subst first.
    split; [constructor|exact Hscope].
  - cbn [nth_error] in Hfirst; inversion Hfirst; subst first.
    destruct Henabled as [[Hbefore Hpacket] Hrest].
    assert (Hin : In edge (SsaPoints.instruction_edges points b)) by (apply Hedges; now left).
    pose proof (out_source (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      n edge Hedge) as Hstart; change (Graph.source (Pre.pg c) edge = n) in Hstart.
    assert (Hinput : PreCoverage.scope_laws c g (Graph.source (Pre.pg c) edge) frames).
    { rewrite Hstart; exact Hscope. }
    assert (Htail := IH next default
      (PreRename.instruction c index b (SsaPoints.parameter_edge points b) (frames, acc) edge)).
    specialize (Htail Hb eq_refl (fun e He => Hedges e (or_intror He))
      (PreFrameInvariant.instruction_source c data Hlaw Hdata b _ _ edge Hsource)
      (PreFrameEnd.instruction_wf c Hwf)).
    assert (Hnext_scope : PreCoverage.scope_laws c g next
      (fst (PreRename.instruction c index b (SsaPoints.parameter_edge points b) (frames, acc) edge))).
    { rewrite <- Htarget; exact (Htransfer frames acc b edge Hb Hin Hsource Hwf Hbefore Hpacket Hinput). }
    destruct (Htail Hnext_scope Hrest) as [Hhistory Hlast].
    cbn [fold_left last]; split; [|exact Hlast].
    econstructor; [|exact Hhistory].
    split; [exact Hsource|]; split; [exact Hwf|]; split; [exact Hinput|].
    split; [exact (conj Hbefore Hpacket)|reflexivity].
Qed.

Local Lemma block_certificate :
  forall b first frames acc, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreCoverage.scope_laws c g first frames ->
    PreFrameTables.unwritten c (SsaPoints.instruction_edges points b) acc ->
    (forall e, In e (SsaPoints.instruction_edges points b) ->
      PreFrameTables.stamp c e final = PreFrameTables.stamp c e
        (snd (PreRename.block c index b frames acc))) ->
    let entered := match SsaPoints.points_in_block points b with
    | [] => (frames, acc)
    | point :: _ => PreRename.mark_exit c index point (frames, acc)
    end in
    PreFrameStep.history (instruction_step b) entered (SsaPoints.instruction_edges points b)
      (fold_left (PreRename.instruction c index b (SsaPoints.parameter_edge points b))
        (SsaPoints.instruction_edges points b) entered) /\
    PreCoverage.scope_laws c g (last (SsaPoints.points_in_block points b) first)
      (fst (PreRename.block c index b frames acc)).
Proof.
  intros b first frames acc Hb Hfirst Hsource Hwf Hscope Hunwritten Htable.
  pose proof (PreFrameTables.block_packets c Hlaw index b frames acc final
    Hb Hwf Hunwritten Htable) as Hhistory.
  set (entered := match SsaPoints.points_in_block points b with
    | [] => (frames, acc)
    | point :: _ => PreRename.mark_exit c index point (frames, acc)
    end) in *.
  pose proof (proj1 (PreFrameStep.checked_history_fold _ _) Hhistory) as [Henabled Heq].
  assert (Hentered_scope : PreCoverage.scope_laws c g first (fst entered)).
  { unfold entered; destruct (SsaPoints.points_in_block points b); [exact Hscope|].
    unfold index; rewrite PreFrameInvariant.mark_exit_scope; exact Hscope. }
  assert (Hentered_source : PreFrameInvariant.scope_source c data (fst entered)).
  { unfold entered; destruct (SsaPoints.points_in_block points b); [exact Hsource|].
    unfold index; rewrite PreFrameInvariant.mark_exit_scope; exact Hsource. }
  assert (Hentered_wf : PreFrameEnd.accumulator_wf c (snd entered)).
  { unfold entered; destruct (SsaPoints.points_in_block points b);
      [exact Hwf|apply PreFrameEnd.mark_exit_wf; exact Hwf]. }
  pose proof (chain_scope b _ _ (points_ordered (Pre.point_laws c (Pre.graphs c Hlaw)) b Hb)
    first first entered Hb Hfirst (fun e He => He)
    Hentered_source Hentered_wf Hentered_scope Henabled) as [Hchecked Hlast].
  split; [exact Hchecked|]; rewrite PreRename.block_equation; exact Hlast.
Qed.

(** Ordered block processing preserves full scope meaning when its actual final packets agree. *)
Theorem block_scope :
  forall b first frames acc, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreCoverage.scope_laws c g first frames ->
    PreFrameTables.unwritten c (SsaPoints.instruction_edges points b) acc ->
    (forall e, In e (SsaPoints.instruction_edges points b) ->
      PreFrameTables.stamp c e final = PreFrameTables.stamp c e
        (snd (PreRename.block c index b frames acc))) ->
    PreCoverage.scope_laws c g (last (SsaPoints.points_in_block points b) first)
      (fst (PreRename.block c index b frames acc)).
Proof.
  intros b first frames acc Hb Hfirst Hsource Hwf Hscope Hunwritten Htable.
  exact (proj2 (block_certificate b first frames acc Hb Hfirst Hsource Hwf Hscope Hunwritten Htable)).
Qed.

(** Actual body histories certify full input-frame meaning for every individual instruction occurrence. *)
Theorem block_history :
  forall b first frames acc, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreCoverage.scope_laws c g first frames ->
    PreFrameTables.unwritten c (SsaPoints.instruction_edges points b) acc ->
    (forall e, In e (SsaPoints.instruction_edges points b) ->
      PreFrameTables.stamp c e final = PreFrameTables.stamp c e
        (snd (PreRename.block c index b frames acc))) ->
    let entered := match SsaPoints.points_in_block points b with
    | [] => (frames, acc)
    | point :: _ => PreRename.mark_exit c index point (frames, acc)
    end in
    PreFrameStep.history (instruction_step b) entered (SsaPoints.instruction_edges points b)
      (fold_left (PreRename.instruction c index b (SsaPoints.parameter_edge points b))
        (SsaPoints.instruction_edges points b) entered).
Proof.
  intros b first frames acc Hb Hfirst Hsource Hwf Hscope Hunwritten Htable.
  exact (proj1 (block_certificate b first frames acc Hb Hfirst Hsource Hwf Hscope Hunwritten Htable)).
Qed.

(** Full task meaning is attached to the actual named first point supplied by the existing domain. *)
Definition task_scope (pair : positive * PreRename.scope B E U) : Prop :=
  forall b first, Prepared.name_of (Pre.blocks c) (fst pair) = Some b ->
    In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    PreCoverage.scope_laws c g first (snd pair).

(** The semantic invariant reuses maintained point domains and table ownership without new caches. *)
Definition walk_scope (current : PreRename.work B BE E U) : Prop :=
  PreFrameDominance.walk_dominance c data current /\ PreFrameTables.owned c current /\
    Forall task_scope (PreRename.pending current).

Local Lemma initial_scope : walk_scope (PreRename.initial index).
Proof.
  split; [exact (PreFrameDominance.initial_dominance c data Hlaw Hdata)|]; split.
  - exact (PreFrameTables.initial_owned c index).
  - rewrite PreRename.initial_equation; cbn [PreRename.pending].
    apply Forall_forall; intros [id frames] Hin; apply in_map_iff in Hin.
    destruct Hin as [root [Heq Hroot]]; inversion Heq; subst frames root.
    intros b first Hname Hb Hfirst.
    unfold index in Hroot; rewrite (proj1 (PreRename.prepare_walk_equations c data)) in Hroot.
    pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
    apply (Prepared.entry_ids_spec _ _ Hp) in Hroot; destruct Hroot as [entry [Hentry Hid]].
    pose proof (Prepared.name_of_id_of _ _ _ Hp Hid) as Hentry_name.
    cbn [fst] in Hname; assert (Howner : entry = b) by congruence; subst entry.
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hentry.
    destruct (Pre.entry_position c (Pre.graphs c Hlaw)) as
      [root [point [Hentries [Hpoints Hposition]]]].
    rewrite Hentries in Hentry; destruct Hentry as [<-|[]].
    fold points in Hposition.
    assert (Hpoint : first = point) by congruence; subst point.
    exact (PreFrameMeaning.entry_scope_laws c g Hlaw Hdefinitions Hoccurrences
      data Hdata root first Hb Hfirst Hpoints Hinitial).
Qed.

Local Lemma step_scope {current next result budget} :
  walk_scope current -> PreRename.step c index current = inl next ->
  runs (PreRename.step_c c index) budget next result ->
  final = PreFrameTables.output_of result ->
    walk_scope next.
Proof.
  intros [Hdomains [Howned Htasks]] Hstep Hsuffix Hfinal.
  pose proof (PreFrameDominance.step_dominance c data Hlaw Hdata current Hdomains) as Hnext_domains.
  fold index in Hnext_domains.
  rewrite Hstep in Hnext_domains.
  split; [exact Hnext_domains|]; split.
  - exact (PreFrameTables.step_owned c Hlaw Howned Hstep).
  - pose proof Hstep as Hraw; rewrite PreRename.step_equation in Hstep.
    destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
    inversion Htasks as [|pair tail Htask Hrest]; subst pair tail.
    destruct (FinSet.mem positive_encoding id (PreRename.visited current)) eqn:Hseen.
    + inversion Hstep; subst next; exact Hrest.
    + pose proof (proj2 Hdomains) as Hpending_domains; rewrite Hpending in Hpending_domains.
      inversion Hpending_domains as [|pair tail Hdomain Hdomain_rest]; subst pair tail.
      destruct Hdomain as [b [first [Hname [Hb [Hfirst [Hsource Hpoint]]]]]].
      cbn [fst snd] in Hname, Hsource, Hpoint.
      rewrite Hname in Hstep; inversion Hstep; subst next.
      assert (Hscope : PreCoverage.scope_laws c g
        (last (SsaPoints.points_in_block points b) first)
        (fst (PreRename.block c index b frames (PreRename.output current)))).
      { apply (block_scope b first frames (PreRename.output current) Hb Hfirst Hsource).
        - exact (PreFrameTables.owned_output_wf c current Howned).
        - exact (Htask b first Hname Hb Hfirst).
        - intros e He; exact (PreFrameTables.unvisited_unwritten c Hlaw Howned Hname Hseen e He).
        - intros e He; rewrite Hfinal.
          exact (PreFrameTables.block_table_final c Hlaw index current Howned
            _ result budget id frames rest b Hpending Hseen Hname Hraw Hsuffix e He). }
      apply Forall_app; split; [|exact Hrest].
      apply Forall_forall; intros [child scope] Hin; apply in_map_iff in Hin.
      destruct Hin as [[key parent] [Heq Hpair]]; inversion Heq; subst child scope.
      intros owner start Hchild_name Howner Hstart.
      destruct (PreFrameCache.child_parent c data Hlaw id key parent Hpair) as [Hparent Hmap].
      pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
      apply (PreFrameMeaning.scope_parent_laws c g Hlaw Hdefinitions Hoccurrences
        b owner start id key _ Hb Howner
        (Prepared.id_of_name_of _ _ _ Hp Hname)
        (Prepared.id_of_name_of _ _ _ Hp Hchild_name) Hmap Hstart).
      fold points.
      rewrite (PreFrameDominance.last_default (SsaPoints.points_in_block points b) start first
        (blocks_nonempty (Pre.point_laws c (Pre.graphs c Hlaw)) b Hb)).
      exact Hscope.
Qed.

(** Checked driver steps use the shared labelled closure and retain full input-frame meaning. *)
Definition checked_step
    (source : PreRename.work B BE E U + PreRename.stopped B BE E U) (_ : unit)
    (target : PreRename.work B BE E U + PreRename.stopped B BE E U) : Prop :=
  exists current, source = inl current /\ walk_scope current /\
    PreRename.step c index current = target.

Local Lemma runs_scope_history :
  forall budget current result, runs (PreRename.step_c c index) budget current result ->
    final = PreFrameTables.output_of result -> walk_scope current ->
    exists labels, PreFrameStep.history checked_step (inl current) labels result.
Proof.
  intros budget current result Hrun; induction Hrun as [current|budget current stopped Hstop|
    budget current next result Hstep Hrun IH]; intros Hfinal Hscope.
  - exists []; constructor.
  - exists [tt]; econstructor.
    + exists current; split; [reflexivity|]; split; [exact Hscope|exact Hstop].
    + constructor.
  - pose proof (step_scope Hscope Hstep Hrun Hfinal) as Hnext.
    destruct (IH Hfinal Hnext) as [labels Hhistory]; exists (tt :: labels).
    econstructor.
    + exists current; split; [reflexivity|]; split; [exact Hscope|exact Hstep].
    + exact Hhistory.
Qed.

(** The same actual binary-driver execution carries full semantic frames at every processed block. *)
Theorem run_scope_history :
  final = PreFrameTables.output_of
    (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
      (PreRename.initial index))) ->
  exists labels, PreFrameStep.history checked_step (inl (PreRename.initial index)) labels
    (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
      (PreRename.initial index))).
Proof.
  intro Hfinal.
  exact (runs_scope_history _ _ _ (iterate_value (PreRename.step_c c index)
    (PreRename.walk_budget index) (PreRename.initial index)) Hfinal initial_scope).
Qed.

End SemanticWalk.

End PreFrameWalk.
