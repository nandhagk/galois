(** * Ordered transfer histories through one relation closure

    A single labelled closure represents ordinary walks and precondition-checked folds.
    For example, a checked instruction history erases to the same ordinary transfer history.
    Builds on: BaseRel and Stdlib lists. *)

From Stdlib Require Import List.
From Galois.Base Require Import BaseMap BaseRel.
From Galois.Graph Require Import GraphModel GraphDomSpec.
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

(** Concatenating ordered graph paths preserves the shared intermediate point. *)
Lemma path_app {N E} (g : Graph.t N E) :
  forall start es mid tail finish, path g start es mid -> path g mid tail finish ->
    path g start (es ++ tail) finish.
Proof.
  intros start es mid tail finish Hprefix Htail.
  induction Hprefix as [n|e rest mid Hedge Hpath IH]; [exact Htail|].
  cbn [app]; constructor; [exact Hedge|apply IH; exact Htail].
Qed.

(** A strict dominator of an edge's target already dominates the edge's source. *)
Theorem strict_target_dominates_source {N E} (g : Graph.t N E) :
  forall e q, In e (Graph.out g (Graph.source g e)) ->
    strictly_dominates g q (Graph.target g e) -> dominates g q (Graph.source g e).
Proof.
  intros e q Hedge [Hdom Hne] start es Hentry Hpath.
  assert (Hsingle : path g (Graph.source g e) [e] (Graph.target g e)).
  { constructor; [exact Hedge|constructor]. }
  destruct (Hdom start (es ++ [e]) Hentry (path_app g _ _ _ _ _ Hpath Hsingle))
    as [Heq|[edge [Hin Htarget]]]; [now left|].
  apply in_app_iff in Hin; destruct Hin as [Hin|[<-|[]]].
  - right; exists edge; auto.
  - exfalso; apply Hne; symmetry; exact Htarget.
Qed.

Section Advance.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable g : PreFrg.frg B BE E U.

(** A nearest definition advances through an immediate-dominance gap containing no new definition. *)
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

End Advance.

End PreFrameStep.
