(** * Entry and dominator-boundary frame meaning

    Static source domains exclude definitions and real uses at the wrong block boundary.
    For example, an initial entry frame crosses a child boundary without inventing a phi definition.
    Builds on: AnalysesSsaPreCoverage, AnalysesSsaPreFrameStep and the supplied exact block tree. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep AnalysesSsaPreFrameCache.
Import List.ListNotations.

Module PreFrameMeaning.

Section Boundaries.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable g : PreFrg.frg B BE E U.
Hypothesis Hlaw : Pre.laws c.
Let points := Pre.points (Pre.input c).

(** At a first point the only possible static definition is an initial version. *)
Theorem definition_first_initial :
  forall b first, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
  forall d, PreFrg.definition_domain c d -> PreFrg.version_point c d = Some first ->
    d = PreFrg.Initial (PreFrg.version_expr d).
Proof.
  intros b first Hb Hfirst d Hdomain Hpoint; destruct d as [u|u|e u|owner u].
  - rewrite PreFrg.version_point_equation in Hpoint; discriminate.
  - reflexivity.
  - destruct Hdomain as [He Hcomputed]; exfalso.
    apply (PreCoverage.internal_target_not_first c Hlaw He
      (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)) Hb Hfirst).
    rewrite PreFrg.version_point_equation in Hpoint; congruence.
  - pose proof (PreFrg.phi_needed_nodes c Hlaw Hdomain) as Howner.
    destruct (PreFrg.parameter_edge_listed c Hlaw Howner) as [He Hi]; exfalso.
    apply (PreCoverage.internal_target_not_first c Hlaw He Hi Hb Hfirst).
    rewrite PreFrg.version_point_equation in Hpoint; congruence.
Qed.

Local Lemma entry_dominator first q :
  In first (Graph.entries (Pre.pg c)) -> dominates (Pre.pg c) q first -> q = first.
Proof.
  intros Hentry Hdom; destruct (Hdom first [] Hentry (path_nil first)) as [Heq|[e [[] _]]].
  exact Heq.
Qed.

Hypothesis Hdefinitions :
  forall d, In d (PreFrg.versions g) -> PreFrg.definition_domain c d.
Hypothesis Hoccurrences :
  forall e d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d ->
    In e (Cfg.edges (Pre.point_cfg c)) /\ exists u, Pre.recomputed c e = Some u.

(** A first point has no completed real occurrence, independent of the selected graph version. *)
Theorem no_occurrence_first :
  forall b first, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
  forall e d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d ->
    Graph.target (Pre.pg c) e <> first.
Proof.
  intros b first Hb Hfirst e d Hget.
  destruct (Hoccurrences e d Hget) as [He [u Hcomputed]].
  exact (PreCoverage.internal_target_not_first c Hlaw He
    (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)) Hb Hfirst).
Qed.

(** No selected real occurrence dominates an entry first point. *)
Theorem no_real_use_entry :
  forall b first, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    In first (Graph.entries (Pre.pg c)) ->
  forall d, ~ PreCoverage.real_use_at c g first d.
Proof.
  intros b first Hb Hfirst Hentry d [e [Hget Hdom]].
  apply (no_occurrence_first b first Hb Hfirst e d Hget).
  exact (entry_dominator first _ Hentry Hdom).
Qed.

(** A family's initial-availability callback establishes the full initial frame meaning at entry. *)
Theorem initial_frame_laws :
  forall b first, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    Graph.entries (Pre.pg c) = [first] ->
  forall u, (In (PreFrg.Initial u) (PreFrg.versions g) <-> Pre.initial c u = true) ->
    PreCoverage.frame_laws c g u first (PreRename.initial_frame c u).
Proof.
  intros b first Hb Hfirst Hentry u Hinitial.
  assert (Hentry_in : In first (Graph.entries (Pre.pg c))) by (rewrite Hentry; now left).
  assert (Hreachable : reachable (Pre.pg c) first) by (apply reachable_entry; exact Hentry_in).
  rewrite PreRename.initial_frame_equation; destruct (Pre.initial c u) eqn:Ha.
  - apply (PreFrameStep.definition_frame c g Hlaw u first (PreFrg.Initial u) false).
    + exact Hreachable.
    + apply Hinitial; reflexivity.
    + reflexivity.
    + rewrite PreFrg.version_point_equation, Hentry; reflexivity.
    + split; [discriminate|intro Hreal; exfalso].
      exact (no_real_use_entry b first Hb Hfirst Hentry_in _ Hreal).
  - split; [reflexivity|]; split.
    + split; [discriminate|intro Hreal; exfalso].
      exact (no_real_use_entry b first Hb Hfirst Hentry_in _ Hreal).
    + rewrite PreFrg.version_point_equation; split; [reflexivity|]; split; [reflexivity|].
      intros d q Hd Hu Hpoint Hdom.
      assert (Hq : q = first) by exact (entry_dominator first q Hentry_in Hdom); subst q.
      pose proof (definition_first_initial b first Hb Hfirst d (Hdefinitions d Hd) Hpoint) as Heq.
      rewrite Hu in Heq; subst d; apply Hinitial in Hd; congruence.
Qed.

(** A nonentry first point has no graph version completing at that boundary. *)
Theorem no_definition_nonentry_first :
  forall b first, In b (Graph.nodes (Pre.bg c)) -> ~ In b (Graph.entries (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
  forall d, In d (PreFrg.versions g) -> PreFrg.version_point c d <> Some first.
Proof.
  intros b first Hb Hnonentry Hfirst d Hd Hpoint.
  pose proof (definition_first_initial b first Hb Hfirst d (Hdefinitions d Hd) Hpoint) as Heq.
  rewrite Heq, PreFrg.version_point_equation in Hpoint.
  destruct (Pre.entry_position c (Pre.graphs c Hlaw)) as [entry [point [Hentries [Hpoints Hposition]]]].
  rewrite Hpoints in Hpoint; cbn [nth_error] in Hpoint; inversion Hpoint; subst point.
  assert (Hentry : In entry (Graph.nodes (Pre.bg c))).
  { apply (entries_in (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))).
    change (In entry (Graph.entries (Pre.bg c))); rewrite Hentries; now left. }
  pose proof (points_owner (Pre.point_laws c (Pre.graphs c Hlaw)) b first Hb
    (nth_error_In _ _ Hfirst)) as Howner.
  pose proof (points_owner (Pre.point_laws c (Pre.graphs c Hlaw)) entry first Hentry
    (nth_error_In _ _ Hposition)) as Howner'.
  apply Hnonentry; rewrite Hentries; left; congruence.
Qed.

(** A family's kill callback cannot complete at a block's first point. *)
Theorem no_kill_first :
  forall b first u, PreFamily.in_family c u -> In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
  forall e, In e (Cfg.edges (Pre.point_cfg c)) -> Graph.target (Pre.pg c) e = first ->
    Pre.killed c e u = false.
Proof.
  intros b first u Hfamily Hb Hfirst e He Htarget.
  destruct (Pre.killed c e u) eqn:Hkill; [|reflexivity].
  exfalso; exact (PreCoverage.internal_target_not_first c Hlaw He
    (PreCoverage.kill_internal c Hlaw Hfamily He Hkill) Hb Hfirst Htarget).
Qed.

Local Lemma parent_nonentry {parent child parent_id child_id} :
  Prepared.id_of (Pre.blocks c) parent = Some parent_id ->
  Prepared.id_of (Pre.blocks c) child = Some child_id ->
  Map.get positive_encoding child_id (Dom.idom (Pre.dom c)) = Some parent_id ->
    ~ In child (Graph.entries (Pre.bg c)).
Proof.
  intros Hp Hc Hparent Hentry.
  pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hready.
  pose proof (Dom.idom_sound _ _ (Pre.tree_exact c (Pre.graphs c Hlaw))
    _ _ _ _ Hparent (Prepared.name_of_id_of _ _ _ Hready Hc)
    (Prepared.name_of_id_of _ _ _ Hready Hp)) as Hdom.
  rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hdom.
  destruct Hdom as [[Hdom Hne] Hminimal].
  destruct (Hdom child [] Hentry (path_nil child)) as [Heq|[edge [[] Htarget]]].
  exact (Hne Heq).
Qed.

(** Full frame meaning crosses the supplied dominator-parent boundary without a point-tree premise. *)
Theorem scope_parent_laws :
  forall parent child first parent_id child_id frames,
    In parent (Graph.nodes (Pre.bg c)) -> In child (Graph.nodes (Pre.bg c)) ->
    Prepared.id_of (Pre.blocks c) parent = Some parent_id ->
    Prepared.id_of (Pre.blocks c) child = Some child_id ->
    Map.get positive_encoding child_id (Dom.idom (Pre.dom c)) = Some parent_id ->
    nth_error (SsaPoints.points_in_block points child) 0 = Some first ->
    PreCoverage.scope_laws c g
      (last (SsaPoints.points_in_block points parent) first) frames ->
    PreCoverage.scope_laws c g first frames.
Proof.
  intros parent child first parent_id child_id frames Hp Hc Hip Hic Hparent Hfirst Hscope
    u Hfamily Hpure.
  eapply (PreFrameStep.frame_gap c g Hlaw).
  - exact (PreCoverage.block_parent_immediate c Hlaw parent child first
      parent_id child_id Hp Hc Hip Hic Hparent Hfirst).
  - intros d Hd Hu; exact (no_definition_nonentry_first child first Hc
      (parent_nonentry Hip Hic Hparent) Hfirst d Hd).
  - intros e Hget; eapply no_occurrence_first; eassumption.
  - intros e He Htarget; exact (no_kill_first child first u Hfamily Hc Hfirst e He Htarget).
  - exact (Hscope u Hfamily Hpure).
Qed.

(** Actual prepared entry bindings establish full scope meaning from source-domain graph facts. *)
Theorem entry_scope_laws :
  forall data, PreFrameCache.placement_laws c data ->
  forall b first, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    Graph.entries (Pre.pg c) = [first] ->
    (forall u, PreFamily.in_family c u -> Pre.pure c u = true ->
      (In (PreFrg.Initial u) (PreFrg.versions g) <-> Pre.initial c u = true)) ->
    PreCoverage.scope_laws c g first (PreRename.entry_scope (PreRename.prepare c data)).
Proof.
  intros data Hdata b first Hb Hfirst Hentry Hinitial u Hfamily Hpure.
  rewrite (PreFrameCache.cached_entry c data _ (PreFrameCache.prepare_laws c data)),
    PreFrameCache.initial_top; [|exact Hlaw|].
  - exact (initial_frame_laws b first Hb Hfirst Hentry u (Hinitial u Hfamily Hpure)).
  - apply (PreFrameCache.eligible_exact c data Hdata); auto.
Qed.

End Boundaries.

End PreFrameMeaning.
