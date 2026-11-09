(** * Ordered transfer histories through one relation closure

    A single labelled closure represents ordinary walks and precondition-checked folds.
    For example, a checked instruction history erases to the same ordinary transfer history.
    Builds on: BaseRel and Stdlib lists. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseRel.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage.
Import List.ListNotations.

Module PreFrameStep.

(** Histories use the shared relation closure for any chosen local transfer relation. *)
Definition history {S E} (step : S -> E -> S -> Prop) := Rel.lpath step.

Section Histories.
Context {S E : Type}.
Variable transfer : S -> E -> S.

Definition transfer_step s e target : Prop := transfer s e = target.

(** Folding ordered instructions constructs a history of exactly those local transfers. *)
Theorem fold_history es s :
  history transfer_step s es (fold_left transfer es s).
Proof.
  revert s; induction es as [|e rest IH]; intro s; cbn [fold_left].
  - constructor.
  - econstructor; [reflexivity|apply IH].
Qed.

(** Functional local transfers determine the endpoint of every ordinary history. *)
Theorem history_fold {s es target} :
  history transfer_step s es target -> fold_left transfer es s = target.
Proof.
  intro Hpath; induction Hpath as [s|s e mid rest target Hstep Hpath IH].
  - reflexivity.
  - cbn [fold_left]; unfold transfer_step in Hstep; rewrite Hstep; exact IH.
Qed.

Variable enabled : S -> E -> Prop.

(** Checked transfer keeps the local precondition on the same state and edge occurrence. *)
Definition checked_step s e target : Prop :=
  enabled s e /\ transfer_step s e target.

Fixpoint fold_enabled (es : list E) s : Prop :=
  match es with
  | [] => True
  | e :: rest => enabled s e /\ fold_enabled rest (transfer s e)
  end.

(** A checked history erases its local guards without changing its edges or endpoint. *)
Theorem checked_history_erases {s es target} :
  history checked_step s es target -> history transfer_step s es target.
Proof.
  apply Rel.lpath_mono; intros source e finish [_ Hstep]; exact Hstep.
Qed.

Local Lemma checked_history_enabled {s es target} :
  history checked_step s es target -> fold_enabled es s.
Proof.
  intro Hpath; induction Hpath as [s|s e mid rest target [Hen Hstep] Hpath IH].
  - exact I.
  - cbn [fold_enabled]; split; [exact Hen|].
    unfold transfer_step in Hstep; rewrite Hstep; exact IH.
Qed.

Local Lemma enabled_fold_history es s :
  fold_enabled es s -> history checked_step s es (fold_left transfer es s).
Proof.
  revert s; induction es as [|e rest IH]; intros s Henabled.
  - constructor.
  - destruct Henabled as [Hen Htail]; cbn [fold_left].
    econstructor; [split; [exact Hen|reflexivity]|apply IH; exact Htail].
Qed.

(** Checked folding and checked histories describe the same enabled instruction sequence. *)
Theorem checked_history_fold {s es target} :
  history checked_step s es target <->
    fold_enabled es s /\ fold_left transfer es s = target.
Proof.
  split.
  - intro Hpath; split.
    + exact (checked_history_enabled Hpath).
    + apply history_fold; exact (checked_history_erases Hpath).
  - intros [Henabled <-]; exact (enabled_fold_history es s Henabled).
Qed.

End Histories.

(** A local invariant propagates through any history relation, including checked transfers. *)
Theorem history_invariant {S E} (step : S -> E -> S -> Prop) (P : S -> Prop) :
  (forall s e target, P s -> step s e target -> P target) ->
  forall s es target, history step s es target -> P s -> P target.
Proof.
  apply Rel.lpath_invariant.
Qed.

(** A history prefix and suffix compose without changing any ordered instruction occurrence. *)
Theorem history_app {S E} (step : S -> E -> S -> Prop) :
  forall s es mid tail target, history step s es mid ->
    history step mid tail target -> history step s (es ++ tail) target.
Proof.
  intros s es mid tail target; apply Rel.lpath_app.
Qed.

(** A local transfer invariant covers the endpoint of the same ordered fold history. *)
Theorem fold_preserves {S E} (transfer : S -> E -> S) (P : S -> Prop) :
  (forall s e, P s -> P (transfer s e)) ->
  forall es s, P s -> P (fold_left transfer es s).
Proof.
  intros Hstep es s HP.
  eapply (history_invariant (transfer_step transfer) P).
  - intros source e target Hsource Htransfer.
    unfold transfer_step in Htransfer; subst target; apply Hstep; exact Hsource.
  - apply fold_history.
  - exact HP.
Qed.

(** An observation unchanged by every local transfer is unchanged by its ordered fold. *)
Theorem fold_observation {S E X} (transfer : S -> E -> S) (observe : S -> X) :
  (forall s e, observe (transfer s e) = observe s) ->
  forall es s, observe (fold_left transfer es s) = observe s.
Proof.
  intros Hstep es s.
  apply (fold_preserves transfer (fun target => observe target = observe s)).
  - intros current e Hcurrent; rewrite Hstep; exact Hcurrent.
  - reflexivity.
Qed.

(** Concatenating ordered graph paths preserves the shared intermediate point. *)
Lemma path_app {N E} (g : Graph.t N E) :
  forall start es mid tail finish, path g start es mid -> path g mid tail finish ->
    path g start (es ++ tail) finish.
Proof.
  apply PreRename.path_app.
Qed.

(** A strict dominator of an edge's target already dominates the edge's source. *)
Theorem strict_target_dominates_source {N E} (g : Graph.t N E) :
  forall e q, In e (Graph.out g (Graph.source g e)) ->
    strictly_dominates g q (Graph.target g e) -> dominates g q (Graph.source g e).
Proof.
  apply PreRename.strict_target_dominates_source.
Qed.

Section Advance.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable g : PreFrg.frg B BE E U.

(** A nearest definition advances through an immediate-dominance gap
    containing no new definition. *)
Theorem nearest_advance :
  forall u n target d, immediately_dominates (Pre.pg c) n target ->
    (forall other, In other (PreFrg.versions g) -> PreFrg.version_expr other = u ->
      PreFrg.version_point c other <> Some target) ->
    PreRename.nearest_version c g u n d -> PreRename.nearest_version c g u target d.
Proof.
  intros u n target d [[Hdom Hne] Hminimal] Hnone
    [Hd [Hexpr [q [Hpoint [Hreach Hnearest]]]]].
  split; [exact Hd|]; split; [exact Hexpr|]; exists q; split; [exact Hpoint|]; split.
  - eapply dominates_trans; [exact Hreach|exact Hdom].
  - intros other p Hother Hu Hp Hdom'.
    apply (Hnearest other p Hother Hu Hp); apply Hminimal; split; [exact Hdom'|].
    intro Heq; subst p; exact (Hnone other Hother Hu Hp).
Qed.

(** Absence of a reaching definition advances across the same definition-free dominance gap. *)
Theorem no_reaching_advance :
  forall u n target, immediately_dominates (Pre.pg c) n target ->
    (forall d, In d (PreFrg.versions g) -> PreFrg.version_expr d = u ->
      PreFrg.version_point c d <> Some target) ->
    PreCoverage.no_reaching_version c g u n ->
    PreCoverage.no_reaching_version c g u target.
Proof.
  intros u n target [[Hdom Hne] Hminimal] Hnone Hold d q Hd Hu Hq Hreach.
  apply (Hold d q Hd Hu Hq); apply Hminimal; split; [exact Hreach|].
  intro Heq; subst q; exact (Hnone d Hd Hu Hq).
Qed.

(** A real-use witness is unchanged across a gap with no newly completed selected occurrence. *)
Theorem real_use_advance :
  forall n target d, immediately_dominates (Pre.pg c) n target ->
    (forall e, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d ->
      Graph.target (Pre.pg c) e <> target) ->
    (PreCoverage.real_use_at c g target d <-> PreCoverage.real_use_at c g n d).
Proof.
  intros n target d [[Hdom Hne] Hminimal] Hnone; split; intros [e [Hget Hreach]];
    exists e; split; [exact Hget| |exact Hget|].
  - apply Hminimal; split; [exact Hreach|exact (Hnone e Hget)].
  - eapply dominates_trans; [exact Hreach|exact Hdom].
Qed.

Hypothesis Hlaw : Pre.laws c.

(** A dominance gap without a new killing target preserves every earlier kill obligation. *)
Theorem kills_gap :
  forall u q n target, immediately_dominates (Pre.pg c) n target ->
    (forall e, In e (Cfg.edges (Pre.point_cfg c)) -> Graph.target (Pre.pg c) e = target ->
      Pre.killed c e u = false) ->
    (PreCoverage.no_dominating_kill c u q target <->
      PreCoverage.no_dominating_kill c u q n).
Proof.
  intros u q n target [[Hdom Hne] Hminimal] Hnone; split; intros Hsafe e He Hstrict Hreach.
  - apply (Hsafe e He Hstrict); eapply dominates_trans; [exact Hreach|exact Hdom].
  - destruct (eqb (Pre.en (Pre.keys c)) (Graph.target (Pre.pg c) e) target) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.en_laws c (Pre.graphs c Hlaw))) in Hsame.
      exact (Hnone e He Hsame).
    + apply (Hsafe e He Hstrict); apply Hminimal; split; [exact Hreach|].
      intro Heq; subst target; rewrite eqb_refl in Hsame; discriminate.
Qed.

(** Full nearest, availability and real-use frame meaning advances across an empty dominance gap. *)
Theorem frame_gap :
  forall u n target frame, immediately_dominates (Pre.pg c) n target ->
    (forall d, In d (PreFrg.versions g) -> PreFrg.version_expr d = u ->
      PreFrg.version_point c d <> Some target) ->
    (forall e, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) =
      Some (PreFrg.operand_version (PreRename.selected frame)) ->
      Graph.target (Pre.pg c) e <> target) ->
    (forall e, In e (Cfg.edges (Pre.point_cfg c)) -> Graph.target (Pre.pg c) e = target ->
      Pre.killed c e u = false) ->
    PreCoverage.frame_laws c g u n frame -> PreCoverage.frame_laws c g u target frame.
Proof.
  intros u n target frame Himmediate Hdefinitions Hoccurrences Hkills
    [Hexpr [Hreal Hdefinition]].
  split; [exact Hexpr|]; split.
  - rewrite (real_use_advance n target _ Himmediate Hoccurrences); exact Hreal.
  - destruct (PreFrg.version_point c
      (PreFrg.operand_version (PreRename.selected frame))) as [q|] eqn:Hpoint.
    + destruct Hdefinition as [Hnearest Havailable]; split.
      * exact (nearest_advance u n target _ Himmediate Hdefinitions Hnearest).
      * rewrite (kills_gap u q n target Himmediate Hkills); exact Havailable.
    + destruct Hdefinition as [Hunavailable [Hfalse Hnone]].
      split; [exact Hunavailable|]; split; [exact Hfalse|].
      exact (no_reaching_advance u n target Himmediate Hdefinitions Hnone).
Qed.

Local Lemma definition_strictly_before_target {q e} :
  In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of (Pre.points (Pre.input c)) e = None ->
  dominates (Pre.pg c) q (Graph.source (Pre.pg c) e) ->
    strictly_dominates (Pre.pg c) q (Graph.target (Pre.pg c) e).
Proof.
  intros He Hi Hq.
  pose proof (PreCoverage.internal_immediate c Hlaw He Hi) as [[Hdom Hne] Hminimal].
  pose proof (PreCoverage.listed_edge_out c Hlaw He) as [Hsource Hedge].
  pose proof (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
    _ e Hsource Hedge) as Htarget.
  pose proof (Pre.reachable_points c (Pre.graphs c Hlaw) _ Hsource) as Hsource_reachable.
  pose proof (Pre.reachable_points c (Pre.graphs c Hlaw) _ Htarget) as Htarget_reachable.
  split; [eapply dominates_trans; eassumption|].
  intro Heq; subst q; apply Hne.
  exact (dominates_antisym_reachable (Pre.en (Pre.keys c))
    (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c) _ _
    Hsource_reachable Htarget_reachable Hdom Hq).
Qed.

(** An internal instruction adds exactly its own killing Boolean to the prior dominating kills. *)
Theorem kills_instruction :
  forall u q e, In e (Cfg.edges (Pre.point_cfg c)) ->
    SsaPoints.block_edge_of (Pre.points (Pre.input c)) e = None ->
    dominates (Pre.pg c) q (Graph.source (Pre.pg c) e) ->
    (PreCoverage.no_dominating_kill c u q (Graph.target (Pre.pg c) e) <->
      PreCoverage.no_dominating_kill c u q (Graph.source (Pre.pg c) e) /\
      Pre.killed c e u = false).
Proof.
  intros u q e He Hi Hq.
  pose proof (PreCoverage.internal_immediate c Hlaw He Hi) as [[Hdom Hne] Hminimal].
  pose proof (definition_strictly_before_target He Hi Hq) as Hstrict.
  split.
  - intro Hsafe; split.
    + intros edge Hedge Hbefore Hreach; apply (Hsafe edge Hedge Hbefore).
      eapply dominates_trans; [exact Hreach|exact Hdom].
    + apply (Hsafe e He Hstrict); apply dominates_refl.
  - intros [Hsafe Hkill] edge Hedge Hbefore Hreach.
    destruct (eqb (Pre.en (Pre.keys c)) (Graph.target (Pre.pg c) edge)
      (Graph.target (Pre.pg c) e)) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.en_laws c (Pre.graphs c Hlaw))) in Hsame.
      pose proof (PreCoverage.internal_incoming_unique c Hlaw He Hi Hedge Hsame) as Heq.
      subst edge; exact Hkill.
    + apply (Hsafe edge Hedge Hbefore); apply Hminimal; split; [exact Hreach|].
      intro Heq; rewrite Heq, eqb_refl in Hsame; discriminate.
Qed.

(** An internal target adds precisely its own selected occurrence to the dominating real uses. *)
Theorem real_use_instruction :
  (forall edge d, Map.get (Pre.ee (Pre.keys c)) edge (PreFrg.occurrences g) = Some d ->
    In edge (Cfg.edges (Pre.point_cfg c))) ->
  forall e d, In e (Cfg.edges (Pre.point_cfg c)) ->
    SsaPoints.block_edge_of (Pre.points (Pre.input c)) e = None ->
    (PreCoverage.real_use_at c g (Graph.target (Pre.pg c) e) d <->
      PreCoverage.real_use_at c g (Graph.source (Pre.pg c) e) d \/
      Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d).
Proof.
  intros Hdomain e d He Hi.
  pose proof (PreCoverage.internal_immediate c Hlaw He Hi) as [[Hdom Hne] Hminimal].
  split.
  - intros [other [Hget Hreach]].
    destruct (eqb (Pre.en (Pre.keys c)) (Graph.target (Pre.pg c) other)
      (Graph.target (Pre.pg c) e)) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.en_laws c (Pre.graphs c Hlaw))) in Hsame.
      pose proof (PreCoverage.internal_incoming_unique c Hlaw He Hi
        (Hdomain other d Hget) Hsame) as Heq; subst other; now right.
    + left; exists other; split; [exact Hget|]; apply Hminimal; split; [exact Hreach|].
      intro Heq; rewrite Heq, eqb_refl in Hsame; discriminate.
  - intros [[other [Hget Hreach]]|Hget].
    + exists other; split; [exact Hget|]; eapply dominates_trans; eassumption.
    + exists e; split; [exact Hget|apply dominates_refl].
Qed.

(** An ordinary instruction advances full frame meaning using its exact selection and kill bits. *)
Theorem frame_instruction :
  (forall edge d, Map.get (Pre.ee (Pre.keys c)) edge (PreFrg.occurrences g) = Some d ->
    In edge (Cfg.edges (Pre.point_cfg c))) ->
  forall u e d real available used_here,
    In e (Cfg.edges (Pre.point_cfg c)) ->
    SsaPoints.block_edge_of (Pre.points (Pre.input c)) e = None ->
    (forall other, In other (PreFrg.versions g) -> PreFrg.version_expr other = u ->
      PreFrg.version_point c other <> Some (Graph.target (Pre.pg c) e)) ->
    (used_here = true <-> Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d) ->
    PreCoverage.frame_laws c g u (Graph.source (Pre.pg c) e)
      (PreRename.Frame (PreFrg.Operand d real) available) ->
    PreCoverage.frame_laws c g u (Graph.target (Pre.pg c) e)
      (PreRename.Frame (PreFrg.Operand d (real || used_here))
        (available && negb (Pre.killed c e u))).
Proof.
  intros Hdomain u e d real available used_here He Hi Hnone Hused
    [Hexpr [Hreal Hdefinition]].
  pose proof (PreCoverage.internal_immediate c Hlaw He Hi) as Himmediate.
  split; [exact Hexpr|]; split.
  - cbn [PreRename.selected PreFrg.real_use]; rewrite orb_true_iff, Hreal, Hused.
    symmetry; exact (real_use_instruction Hdomain e d He Hi).
  - cbn [PreRename.selected PreFrg.operand_version] in Hdefinition |- *.
    destruct (PreFrg.version_point c d) as [q|] eqn:Hpoint.
    + destruct Hdefinition as [Hnearest Havailable]; split.
      * exact (nearest_advance u _ _ d Himmediate Hnone Hnearest).
      * cbn [PreRename.available] in Havailable |- *.
        rewrite andb_true_iff, negb_true_iff, Havailable.
        symmetry; apply kills_instruction; [exact He|exact Hi|].
        destruct Hnearest as [_ [_ [point [Hp [Hdom Hminimal]]]]].
        assert (point = q) by congruence; subst point; exact Hdom.
    + destruct Hdefinition as [Hunavailable [Hfalse Hreaching]].
      split; [exact Hunavailable|]; split.
      * cbn [PreRename.available] in Hfalse |- *; rewrite Hfalse; reflexivity.
      * exact (no_reaching_advance u _ _ Himmediate Hnone Hreaching).
Qed.

(** A newly completed definition has no strictly later killing target dominating that same point. *)
Theorem kills_at_definition :
  forall u q, reachable (Pre.pg c) q -> PreCoverage.no_dominating_kill c u q q.
Proof.
  intros u q Hq e He [Hbefore Hneq] Hafter.
  pose proof (PreCoverage.listed_edge_out c Hlaw He) as [Hsource Hedge].
  pose proof (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
    _ e Hsource Hedge) as Htarget.
  exfalso; apply Hneq.
  exact (dominates_antisym_reachable (Pre.en (Pre.keys c))
    (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c) _ _ Hq
    (Pre.reachable_points c (Pre.graphs c Hlaw) _ Htarget) Hbefore Hafter).
Qed.

(** A completed graph definition establishes nearest and available frame meaning at its own point. *)
Theorem definition_frame :
  forall u q d real, reachable (Pre.pg c) q ->
    In d (PreFrg.versions g) -> PreFrg.version_expr d = u ->
    PreFrg.version_point c d = Some q ->
    (real = true <-> PreCoverage.real_use_at c g q d) ->
    PreCoverage.frame_laws c g u q (PreRename.Frame (PreFrg.Operand d real) true).
Proof.
  intros u q d real Hq Hd Hu Hpoint Hreal.
  split; [exact Hu|]; split; [exact Hreal|].
  cbn [PreRename.selected PreFrg.operand_version]; rewrite Hpoint; split.
  - subst u; exact (PreRename.nearest_at_definition c g d Hd Hpoint).
  - split; [intros _; apply kills_at_definition; exact Hq|intros _; reflexivity].
Qed.
End Advance.

End PreFrameStep.
