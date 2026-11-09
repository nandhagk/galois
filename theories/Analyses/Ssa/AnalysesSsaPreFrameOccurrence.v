(** * Executed writers and occurrence selection

    A final occurrence supplies a processed block and an instruction input from the same history.
    For example, a reused occurrence reads its nearest frame before its own instruction runs.
    Builds on: AnalysesSsaPreFrameHistory, AnalysesSsaPreFrameTables and AnalysesSsaPreCoverage. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep
  AnalysesSsaPreFrameEnd AnalysesSsaPreFrameCache AnalysesSsaPreFrameInvariant
  AnalysesSsaPreFrameDominance AnalysesSsaPreFrameTables AnalysesSsaPreFrameWalk
  AnalysesSsaPreFrameHistory.
Import List.ListNotations.

Module PreFrameOccurrence.

Section Writers.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Context {g : PreFrg.frg B BE E U}.
Hypothesis Hlaw : Pre.laws c.
Let index := PreRename.prepare c data.
Let points := Pre.points (Pre.input c).

Local Definition written e result :=
  match PreFrameTables.stamp c e (PreFrameTables.output_of result) with
  | (None, false) => false
  | _ => true
  end.

Local Lemma written_false e result :
  written e result = false <->
    PreFrameTables.stamp c e (PreFrameTables.output_of result) = (None, false).
Proof.
  unfold written; destruct (PreFrameTables.stamp c e (PreFrameTables.output_of result))
    as [[d|] flag]; destruct flag; split; intros H; try discriminate; reflexivity.
Qed.

Local Lemma changed_block {current result e} :
  PreFrameTables.owned c current ->
  PreFrameTables.stamp c e (PreRename.output current) = (None, false) ->
  PreFrameTables.stamp c e (PreFrameTables.output_of result) <> (None, false) ->
  PreRename.step c index current = result ->
    exists id frames rest b next,
      PreRename.pending current = (id, frames) :: rest /\
      FinSet.mem positive_encoding id (PreRename.visited current) = false /\
      Prepared.name_of (Pre.blocks c) id = Some b /\ result = inl next /\
      In e (SsaPoints.instruction_edges points b).
Proof.
  intros Howned Hbefore Hafter Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending.
  - subst result; cbn [PreFrameTables.output_of PreRename.stop_output] in Hafter; contradiction.
  - destruct (FinSet.mem positive_encoding id (PreRename.visited current)) eqn:Hseen.
    + subst result; cbn [PreFrameTables.output_of PreRename.output] in Hafter; contradiction.
    + destruct (Prepared.name_of (Pre.blocks c) id) as [b|] eqn:Hname.
      * destruct (in_dec (eqb_dec _ (Pre.ee_laws c (Pre.graphs c Hlaw))) e
          (SsaPoints.instruction_edges points b)) as [Hin|Hnone].
        -- exists id, frames, rest, b.
           subst result; eexists; repeat split; eassumption || reflexivity.
        -- exfalso; apply Hafter; subst result.
           cbn [PreFrameTables.output_of PreRename.output].
           rewrite (PreFrameTables.block_other c Hlaw e
             (PreFrameTables.owned_output_wf c current Howned) Hnone); exact Hbefore.
      * subst result; cbn [PreFrameTables.output_of PreRename.stop_output] in Hafter; contradiction.
Qed.

Local Lemma executed_writer {labels target e} :
  PreFrameStep.history (PreFrameWalk.checked_step c data (g := g))
    (inl (PreRename.initial index)) labels target ->
  PreFrameTables.stamp c e (PreFrameTables.output_of target) <> (None, false) ->
    exists current next id frames rest b budget,
      PreFrameWalk.walk_scope c data (g := g) current /\
      PreRename.pending current = (id, frames) :: rest /\
      FinSet.mem positive_encoding id (PreRename.visited current) = false /\
      Prepared.name_of (Pre.blocks c) id = Some b /\
      PreRename.step c index current = inl next /\
      runs (PreRename.step_c c index) budget next target /\
      In e (SsaPoints.instruction_edges points b).
Proof.
  intros Hhistory Hwritten.
  assert (Hstart : written e (inl (PreRename.initial index)) = false).
  { apply written_false; rewrite PreRename.initial_equation.
    unfold PreFrameTables.stamp; cbn [PreFrameTables.output_of PreRename.output
      PreRename.empty_accumulator PreRename.occurrence_index PreRename.fresh_index].
    rewrite Map.get_empty, FinSet.mem_empty; reflexivity. }
  assert (Hfinish : written e target = true).
  { destruct (written e target) eqn:Hflag; [reflexivity|].
    exfalso; apply Hwritten; apply written_false; exact Hflag. }
  destruct (PreFrameHistory.becomes_true _ (written e) _ _ _ Hhistory Hstart Hfinish)
    as [prefix [before [label [after [suffix [Hlabels [Hprefix
      [[current [Hbefore [Hscope Hstep]]] [Hempty [Hnonempty Hsuffix]]]]]]]]]].
  subst before; apply written_false in Hempty.
  assert (Hafter : PreFrameTables.stamp c e (PreFrameTables.output_of after) <> (None, false)).
  { intro Heq; apply (proj2 (written_false e after)) in Heq; congruence. }
  destruct (changed_block (proj1 (proj2 Hscope)) Hempty Hafter Hstep)
    as [id [frames [rest [b [next [Hpending [Hseen [Hname [Hafter' Hin]]]]]]]]].
  subst after; exists current, next, id, frames, rest, b, (length suffix).
  split; [exact Hscope|]; split; [exact Hpending|]; split; [exact Hseen|].
  split; [exact Hname|]; split; [exact Hafter'|]; split; [|exact Hin].
  exact (PreFrameHistory.checked_runs c data _ _ _ Hsuffix next Hafter').
Qed.

(** Every final written occurrence has a full source scope and literal final-table block packet. *)
Theorem writing_block {labels target e} :
  PreFrameStep.history (PreFrameWalk.checked_step c data (g := g))
    (inl (PreRename.initial index)) labels target ->
  PreFrameTables.stamp c e (PreFrameTables.output_of target) <> (None, false) ->
    exists b first frames acc,
      In b (Graph.nodes (Pre.bg c)) /\
      nth_error (SsaPoints.points_in_block points b) 0 = Some first /\
      In e (SsaPoints.instruction_edges points b) /\
      PreFrameInvariant.scope_source c data frames /\
      PreFrameEnd.accumulator_wf c acc /\
      PreCoverage.scope_laws c g first frames /\
      PreFrameTables.unwritten c (SsaPoints.instruction_edges points b) acc /\
      (forall edge, In edge (SsaPoints.instruction_edges points b) ->
        PreFrameTables.stamp c edge (PreFrameTables.output_of target) =
          PreFrameTables.stamp c edge (snd (PreRename.block c index b frames acc))).
Proof.
  intros Hhistory Hwritten.
  destruct (executed_writer Hhistory Hwritten) as [current [next [id [frames [rest [b
    [budget [[Hdomains [Howned Htasks]] [Hpending [Hseen [Hname [Hstep [Hsuffix Hin]]]]]]]]]]]]].
  pose proof (proj2 Hdomains) as Hpending_domains; rewrite Hpending in Hpending_domains, Htasks.
  inversion Hpending_domains as [|pair tail Hdomain Htail]; subst pair tail.
  destruct Hdomain as [owner [first [Howner [Hb [Hfirst [Hsource Hpoint]]]]]].
  cbn [fst snd] in Howner, Hsource.
  assert (Hsame : owner = b) by congruence; subst owner.
  inversion Htasks as [|pair tail Htask Hrest]; subst pair tail.
  exists b, first, frames, (PreRename.output current).
  split; [exact Hb|]; split; [exact Hfirst|]; split; [exact Hin|].
  split; [exact Hsource|]; split; [exact (PreFrameTables.owned_output_wf c current Howned)|].
  split; [exact (Htask b first Hname Hb Hfirst)|]; split.
  - intros edge Hedge.
    exact (PreFrameTables.unvisited_unwritten c Hlaw Howned Hname Hseen edge Hedge).
  - intros edge Hedge.
    exact (PreFrameTables.block_table_final c Hlaw index current Howned next target budget
      id frames rest b Hpending Hseen Hname Hstep Hsuffix edge Hedge).
Qed.

(** An instruction history exposes its full source-frame meaning and its own final-table packet. *)
Theorem instruction_input {final b source labels target e} :
  PreFrameStep.history
    (PreFrameWalk.instruction_step c data (g := g) final b) source labels target ->
  In e labels ->
    exists frames acc,
      PreFrameInvariant.scope_source c data frames /\
      PreFrameEnd.accumulator_wf c acc /\
      PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) frames /\
      PreFrameTables.instruction_packet c index b (SsaPoints.parameter_edge points b)
        final (frames, acc) e.
Proof.
  intros Hhistory Hin.
  destruct (PreFrameHistory.member _ _ _ _ Hhistory e Hin)
    as [prefix [[frames acc] [after [suffix [Hlabels [Hprefix [Hstep Hsuffix]]]]]]].
  exists frames, acc; destruct Hstep as [Hsource [Hwf [Hscope [Hpacket Heq]]]].
  exact (conj Hsource (conj Hwf (conj Hscope Hpacket))).
Qed.

End Writers.

Section Selection.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Full frame meaning makes the executable reuse guard equal the availability bit. *)
Theorem frame_reuse_available {g u n frame} :
  PreCoverage.frame_laws c g u n frame ->
    PreRename.frame_reuse c frame u = PreRename.available frame.
Proof.
  destruct frame as [[d real] available]; intros [Hexpr [Hreal Hmeaning]].
  unfold PreRename.frame_reuse; cbn [PreRename.available PreRename.selected
    PreFrg.operand_version] in *.
  destruct d as [v|v|e v|b v]; cbn [PreFrg.version_expr] in Hexpr; subst v.
  - rewrite PreFrg.version_point_equation in Hmeaning.
    destruct Hmeaning as [_ [Hfalse Hnone]]; subst available; reflexivity.
  - destruct available; [apply eqb_refl|reflexivity].
  - destruct available; [apply eqb_refl|reflexivity].
  - destruct available; [apply eqb_refl|reflexivity].
Qed.

(** A real instruction packet selects its full input frame or creates its own fresh version. *)
Theorem packet_selection {data g b frames acc final e u} :
  Pre.laws c -> PreFrameCache.placement_laws c data ->
  In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u -> Pre.pure c u = true ->
  PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
  PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) frames ->
  PreFrameTables.instruction_packet c (PreRename.prepare c data) b
    (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) final (frames, acc) e ->
    let frame := PreRename.top c frames u in
    PreCoverage.frame_laws c g u (Graph.source (Pre.pg c) e) frame /\
    PreFrameTables.stamp c e final =
      (Some (if PreRename.available frame
        then PreFrg.operand_version (PreRename.selected frame) else PreFrg.Fresh e u),
        negb (PreRename.available frame)).
Proof.
  intros Hlaw Hdata He Hcomputed Hpure Hsource Hwf Hscope [Hbefore Hpacket] frame.
  assert (Hfamily : PreFamily.in_family c u).
  { apply Pre.family_seed; exact (Pre.occurrences_seeded c (Pre.shapes c Hlaw) e u Hcomputed). }
  pose proof (Hscope u Hfamily Hpure) as Hframe; split; [exact Hframe|].
  destruct (PreFrameCache.evaluation_available c data Hlaw Hdata e u Hcomputed Hpure)
    as [id [Hevaluation Hid]].
  rewrite (PreFrameTables.real_packet_stamp c (work := (frames, acc)) Hwf
    (PreFrameCache.event_lookup c data Hlaw e He) Hevaluation Hbefore) in Hpacket.
  cbn [fst] in Hpacket.
  rewrite <- (PreFrameCache.top_id_agrees c (frames := frames) (u := u) (id := id)) in Hpacket.
  2: { rewrite (PreFrameInvariant.scope_symbols c data frames Hsource); exact Hid. }
  cbn zeta in Hpacket.
  fold frame in Hpacket.
  rewrite (frame_reuse_available (frame := frame) Hframe) in Hpacket; exact Hpacket.
Qed.

(** A recomputation's new definition cannot already be reusable at that instruction's source. *)
Theorem current_not_reusable {g e u} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u ->
    ~ PreRename.reusable c g u (Graph.source (Pre.pg c) e) (PreFrg.Fresh e u).
Proof.
  intros Hlaw He Hcomputed [[Hd [Hexpr [q [Hpoint [Hback Hnearest]]]]] Hsafe].
  rewrite PreFrg.version_point_equation in Hpoint; inversion Hpoint; subst q.
  pose proof (PreCoverage.internal_immediate c Hlaw He
    (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed))) as [[Hforward Hne] Hminimal].
  destruct (PreCoverage.listed_edge_out c Hlaw He) as [Hsource Hout].
  pose proof (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
    _ e Hsource Hout) as Htarget.
  apply Hne; exact (dominates_antisym_reachable (Pre.en (Pre.keys c))
    (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c) _ _
    (Pre.reachable_points c (Pre.graphs c Hlaw) _ Hsource)
    (Pre.reachable_points c (Pre.graphs c Hlaw) _ Htarget) Hforward Hback).
Qed.

End Selection.

End PreFrameOccurrence.
