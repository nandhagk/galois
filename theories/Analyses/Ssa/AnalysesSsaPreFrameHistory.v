(** * Elimination of executed PRE histories

    History elimination retains the states on both sides of an executed step and its suffix.
    For example, a newly written occurrence has a writing step in the same checked run.
    Builds on: AnalysesSsaPreFrameStep, AnalysesSsaPreFrameWalk and CostLoop. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseRel.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreFrameStep AnalysesSsaPreFrameWalk.
Import List.ListNotations.

Module PreFrameHistory.

(** Every labelled occurrence exposes its executed step and the same prefix and suffix. *)
Theorem member {S L} (step : S -> L -> S -> Prop) :
  forall source labels target, PreFrameStep.history step source labels target ->
  forall label, In label labels ->
    exists prefix before after suffix, labels = prefix ++ label :: suffix /\
      PreFrameStep.history step source prefix before /\ step before label after /\
      PreFrameStep.history step after suffix target.
Proof.
  intros source labels target Hhistory; induction Hhistory as
    [source|source first next rest target Hstep Hhistory IH]; intros label Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists [], source, next, rest; split; [reflexivity|].
      split; [constructor|]; split; assumption.
    + destruct (IH label Hin) as [prefix [before [after [suffix [Hlabels
        [Hprefix [Hexecuted Hsuffix]]]]]]].
      exists (first :: prefix), before, after, suffix.
      split; [cbn [app]; now rewrite Hlabels|]; split.
      * econstructor; eassumption.
      * exact (conj Hexecuted Hsuffix).
Qed.

(** A Boolean observation that changes from false to true crosses an executed step. *)
Theorem becomes_true {S L} (step : S -> L -> S -> Prop) (observe : S -> bool) :
  forall source labels target, PreFrameStep.history step source labels target ->
    observe source = false -> observe target = true ->
    exists prefix before label after suffix, labels = prefix ++ label :: suffix /\
      PreFrameStep.history step source prefix before /\ step before label after /\
      observe before = false /\ observe after = true /\
      PreFrameStep.history step after suffix target.
Proof.
  intros source labels target Hhistory; induction Hhistory as
    [source|source label next rest target Hstep Hhistory IH]; intros Hbefore Hafter.
  - congruence.
  - destruct (observe next) eqn:Hnext.
    + exists [], source, label, next, rest; split; [reflexivity|].
      split; [constructor|]; split; [exact Hstep|]; auto.
    + destruct (IH eq_refl Hafter) as [prefix [before [edge [after [suffix
        [Hlabels [Hprefix [Hexecuted Hcross]]]]]]]].
      exists (label :: prefix), before, edge, after, suffix.
      split; [cbn [app]; now rewrite Hlabels|]; split.
      * econstructor; eassumption.
      * exact (conj Hexecuted Hcross).
Qed.

Section Checked.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Context {g : PreFrg.frg B BE E U}.
Let index := PreRename.prepare c data.

Local Lemma stopped_history {stopped labels target} :
  PreFrameStep.history (PreFrameWalk.checked_step c data (g := g))
    (inr stopped) labels target -> labels = [] /\ target = inr stopped.
Proof.
  intro Hhistory; inversion Hhistory as [|source label next rest finish Hstep Htail]; subst.
  - auto.
  - destruct Hstep as [current [Hsource Hrest]]; discriminate.
Qed.

(** Erasing checked history evidence yields a raw suffix run on the same states and result. *)
Theorem checked_runs :
  forall source labels target,
    PreFrameStep.history (PreFrameWalk.checked_step c data (g := g)) source labels target ->
  forall current, source = inl current ->
    runs (PreRename.step_c c index) (length labels) current target.
Proof.
  intros source labels target Hhistory; induction Hhistory as
    [source|source label next rest target Hstep Hhistory IH]; intros current Hsource.
  - subst source; constructor.
  - destruct Hstep as [executed [Hexecuted [Hscope Hstep]]].
    assert (Hsame : executed = current) by congruence; subst executed.
    destruct next as [next|stopped].
    + eapply runs_next; [exact Hstep|exact (IH next eq_refl)].
    + destruct (stopped_history Hhistory) as [Hlabels ->]; subst rest.
      apply runs_stop; exact Hstep.
Qed.

End Checked.

End PreFrameHistory.
