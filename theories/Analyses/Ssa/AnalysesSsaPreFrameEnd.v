(** * Canonical output through complete scoped transfer histories

    Local transfer facts propagate through the same instruction folds and actual fuel-driver runs.
    For example, even an exhausted raw run retains canonical occurrence
    and incoming-operand indexes.
    Builds on: AnalysesSsaPreFrameStep, AnalysesSsaPreRename and CostLoop. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared.
From Galois.Program Require Import ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreFrameStep.

Module PreFrameEnd.

Section Canonical.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Accumulated output keys are stored at canonical encoded trie positions. *)
Definition accumulator_wf (acc : PreRename.accumulator B BE E U) : Prop :=
  Map.wf (Pre.ee (Pre.keys c)) (PreRename.occurrence_index acc) /\
  FinSet.wf (Pre.ee (Pre.keys c)) (PreRename.fresh_index acc) /\
  Map.wf (PreFrg.link_encoding c) (PreRename.link_index acc) /\
  FinSet.wf (PreFrg.phi_encoding c) (PreRename.unsafe_index acc).

(** Empty scoped output starts with canonical indexes. *)
Theorem empty_accumulator_wf : accumulator_wf PreRename.empty_accumulator.
Proof.
  repeat split; first [apply Map.wf_empty|apply FinSet.wf_empty].
Qed.

Local Lemma mark_wf {frames acc key} :
  accumulator_wf acc -> accumulator_wf (PreRename.mark c frames acc key).
Proof.
  intro Hwf; rewrite PreRename.mark_equation.
  destruct (PreRename.top_id frames (fst key) (snd key)) as [[d real] yes].
  destruct d, real; try exact Hwf.
  destruct Hwf as [Hocc [Hfresh [Hlinks Hunsafe]]].
  repeat split; try assumption; apply FinSet.wf_add; exact Hunsafe.
Qed.

Local Lemma mark_exit_wf {index n work} :
  accumulator_wf (snd work) -> accumulator_wf (snd (PreRename.mark_exit c index n work)).
Proof.
  intro Hwf; rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index)); [|exact Hwf].
  cbn [snd]; apply (PreFrameStep.fold_preserves _ accumulator_wf); [|exact Hwf].
  intros acc key Hacc; apply mark_wf; exact Hacc.
Qed.

Local Lemma occurrence_wf {e instance work} :
  accumulator_wf (snd work) ->
  accumulator_wf (snd (fst (PreRename.occurrence c e instance work))).
Proof.
  intro Hwf; rewrite PreRename.occurrence_equation.
  destruct instance as [[id u]|]; [|exact Hwf].
  destruct work as [frames acc]; cbn [snd] in Hwf.
  cbn zeta.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u).
  all: cbn [fst snd]; destruct Hwf as [Hocc [Hfresh [Hlinks Hunsafe]]];
    repeat split; try assumption.
  all: first [apply Map.wf_set; exact Hocc|apply FinSet.wf_add; exact Hfresh].
Qed.

Local Lemma alter_wf {instance work key} :
  accumulator_wf (snd work) -> accumulator_wf (snd (PreRename.alter c instance work key)).
Proof.
  intro Hwf; rewrite PreRename.alter_equation; destruct work as [frames acc].
  destruct instance as [current|]; cbn [snd].
  - destruct (eqb positive_encoding (fst current) (fst key));
      [exact Hwf|apply mark_wf; exact Hwf].
  - apply mark_wf; exact Hwf.
Qed.

Local Lemma instruction_wf {index b parameter work e} :
  accumulator_wf (snd work) ->
  accumulator_wf (snd (PreRename.instruction c index b parameter work e)).
Proof.
  intro Hwf; rewrite PreRename.instruction_equation.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index)) as [info|]; [|exact Hwf].
  pose proof (occurrence_wf (e := e) (instance := PreRename.evaluation info) (work := work) Hwf)
    as Hobserved.
  set (observed := PreRename.occurrence c e (PreRename.evaluation info) work) in *.
  assert (Haltered : accumulator_wf (snd (fold_left (PreRename.alter c (PreRename.evaluation info))
    (PreRename.alterations info) (fst observed)))).
  { apply (PreFrameStep.fold_preserves _ (fun work => accumulator_wf (snd work)));
      [|exact Hobserved].
    intros current key Hcurrent; apply alter_wf; exact Hcurrent. }
  apply mark_exit_wf; exact Haltered.
Qed.

Local Lemma argument_wf {frames acc arg} :
  accumulator_wf acc -> accumulator_wf (PreRename.select_argument c frames acc arg).
Proof.
  intros [Hocc [Hfresh [Hlinks Hunsafe]]]; rewrite PreRename.select_argument_equation.
  repeat split; try assumption; apply Map.wf_set; exact Hlinks.
Qed.

(** Every ordered block transfer retains canonical output, including all outgoing operands. *)
Theorem block_wf {index b frames acc} :
  accumulator_wf acc -> accumulator_wf (snd (PreRename.block c index b frames acc)).
Proof.
  intro Hwf; rewrite PreRename.block_equation.
  set (entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
    | nil => (frames, acc)
    | cons first _ => PreRename.mark_exit c index first (frames, acc)
    end).
  assert (Hentered : accumulator_wf (snd entered)).
  { unfold entered; destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hwf|apply mark_exit_wf; exact Hwf]. }
  assert (Hbody : accumulator_wf (snd (fold_left (PreRename.instruction c index b
    (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
    (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered))).
  { apply (PreFrameStep.fold_preserves _ (fun work => accumulator_wf (snd work)));
      [|exact Hentered].
    intros current e Hcurrent; apply instruction_wf; exact Hcurrent. }
  cbn [snd]; apply (PreFrameStep.fold_preserves _ accumulator_wf); [|exact Hbody].
  intros current pair Hcurrent; apply argument_wf; exact Hcurrent.
Qed.

Definition result_acc (result : PreRename.work B BE E U + PreRename.stopped B BE E U) :=
  match result with
  | inl current => PreRename.output current
  | inr final => PreRename.stop_output final
  end.

Local Lemma step_wf {index current} :
  accumulator_wf (PreRename.output current) ->
  accumulator_wf (result_acc (PreRename.step c index current)).
Proof.
  intro Hwf; rewrite PreRename.step_equation.
  destruct (PreRename.pending current) as [|[id frames] rest]; [exact Hwf|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)); [exact Hwf|].
  destruct (Prepared.name_of (Pre.blocks c) id) as [b|]; [|exact Hwf].
  exact (block_wf (index := index) (b := b) (frames := frames) Hwf).
Qed.

Local Lemma runs_wf {index budget current result} :
  runs (PreRename.step_c c index) budget current result ->
  accumulator_wf (PreRename.output current) -> accumulator_wf (result_acc result).
Proof.
  intro Hrun; induction Hrun as [current|budget current final Hstop|
    budget current next result Hstep Hrun IH]; intro Hwf.
  - exact Hwf.
  - pose proof (step_wf (index := index) (current := current) Hwf) as Hfinal.
    unfold PreRename.step in Hfinal; rewrite Hstop in Hfinal; exact Hfinal.
  - apply IH.
    pose proof (step_wf (index := index) (current := current) Hwf) as Hnext.
    unfold PreRename.step in Hnext; rewrite Hstep in Hnext; exact Hnext.
Qed.

(** Every actual binary-driver outcome retains canonical output independently of context laws. *)
Theorem run_wf index : accumulator_wf (PreRename.stop_output (PreRename.run c index)).
Proof.
  pose proof (runs_wf (iterate_value (PreRename.step_c c index)
    (PreRename.walk_budget index) (PreRename.initial index))) as Hrun.
  assert (Hinitial : accumulator_wf (PreRename.output (PreRename.initial index))).
  { rewrite PreRename.initial_equation; exact empty_accumulator_wf. }
  specialize (Hrun Hinitial).
  rewrite PreRename.run_equation.
  destruct (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
    (PreRename.initial index))); exact Hrun.
Qed.

End Canonical.

End PreFrameEnd.
