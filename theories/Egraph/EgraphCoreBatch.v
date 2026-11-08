(** * Preservation through deferred parent batches

    The unvisited fold suffix supplies the temporary coverage used by each parent repair.
    For example, a dirty dequeue transfers its entire bucket before the first parent is processed.
    Builds on: EgraphCoreRepairStep, EgraphRebuild and the public Cost loop relation. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphCoreIndex EgraphCoreInvariant EgraphCoreTransition
  EgraphCoreRepair EgraphCoreRepairStep EgraphRebuild.
Import List.ListNotations.

Module EggRepairBatch.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).
Context (Hcodes : forall first second,
  Egraph.node_code a first = Egraph.node_code a second -> first = second).

(** A completed parent fold discharges the entire initial batch and keeps all stored productions. *)
Theorem fold_correct parents g visits :
  Egraph.kernel_inv_on a g parents -> EggTransition.layout a g ->
  let result := fold_left (fun state i =>
    (Egraph.repair_node a (fst state) i, N.succ (snd state))) parents (g, visits) in
  Egraph.kernel_inv a (fst result) /\
  EggTransition.layout a (fst result) /\
  Egraph.nodes (fst result) = Egraph.nodes g /\
  Egraph.next (fst result) = Egraph.next g.
Proof.
  revert g visits; induction parents as [|i parents IH]; intros g visits Hinv Hlayout.
  - cbn [fold_left fst]; split; [exact Hinv|]; split; [exact Hlayout|]; split; reflexivity.
  - destruct (EggRepairStep.repair_node_correct a g i parents Hinv Hlayout Hcodes)
      as [Hnext Hnext_layout].
    pose proof (IH (Egraph.repair_node a g i) (N.succ visits) Hnext Hnext_layout)
      as [Hfinal [Hfinal_layout [Hnodes Hbound]]].
    cbn [fold_left fst snd]; split; [exact Hfinal|]; split; [exact Hfinal_layout|]; split.
    + rewrite Hnodes; apply EggRepairStep.repair_node_nodes.
    + rewrite Hbound; apply EggRepairStep.repair_node_next.
Qed.

(** The actual counted repair fold restores the invariant without any remaining active suffix. *)
Theorem repair_correct g loser :
  Egraph.kernel_inv_on a g (EggParent.get (Egraph.parents g) loser) ->
  EggTransition.layout a g ->
  Egraph.kernel_inv a (fst (EggRebuild.repair a g loser)) /\
  EggTransition.layout a (fst (EggRebuild.repair a g loser)) /\
  Egraph.nodes (fst (EggRebuild.repair a g loser)) = Egraph.nodes g /\
  Egraph.next (fst (EggRebuild.repair a g loser)) = Egraph.next g.
Proof.
  intros Hinv Hlayout; rewrite EggRebuild.repair_equation.
  exact (fold_correct _ g 0%N Hinv Hlayout).
Qed.

(** Every actual dirty callback preserves maintained data and stopping certifies an empty queue. *)
Theorem dirty_step_correct g visits :
  Egraph.kernel_inv a g -> EggTransition.layout a g ->
  match Cost.value (Egraph.dirty_step_c a (g, visits)) with
  | inl (h, _) =>
    Egraph.kernel_inv a h /\ EggTransition.layout a h /\
    Egraph.nodes h = Egraph.nodes g /\ Egraph.next h = Egraph.next g
  | inr (h, _) =>
    Egraph.kernel_inv a h /\ EggTransition.layout a h /\
    Egraph.nodes h = Egraph.nodes g /\ Egraph.next h = Egraph.next g /\
    Egraph.dirty h = []
  end.
Proof.
  intros Hinv Hlayout; rewrite EggRebuild.dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g))) as [[loser queue]|] eqn:Hpop.
  - cbv zeta; fold (Egraph.with_queue g queue).
    pose proof (EggRepairInv.pop_kernel_inv a g loser queue Hinv Hpop) as Hactive.
    pose proof (EggTransition.queue_layout a g queue Hlayout) as Hpopped.
    pose proof (repair_correct (Egraph.with_queue g queue) loser Hactive Hpopped) as Hbatch.
    destruct (EggRebuild.repair a (Egraph.with_queue g queue) loser) as [h count].
    exact Hbatch.
  - split; [exact Hinv|]; split; [exact Hlayout|]; split; [reflexivity|].
    split; [reflexivity|].
    rewrite EggPending.pop_equation in Hpop.
    unfold Egraph.dirty.
    destruct (EggPending.entries (Egraph.pending (Egraph.private g))); congruence.
Qed.

(** The loop invariant fixes the stored node universe and allocation bound of its initial graph. *)
Definition execution_inv (initial : Egraph.t K Sort V) (state : Egraph.t K Sort V * N) : Prop :=
  Egraph.kernel_inv a (fst state) /\ EggTransition.layout a (fst state) /\
  Egraph.nodes (fst state) = Egraph.nodes initial /\ Egraph.next (fst state) = Egraph.next initial.

(** One actual callback maintains the fixed allocation universe of the whole run. *)
Theorem step_execution_inv initial g visits :
  execution_inv initial (g, visits) ->
  match Cost.value (Egraph.dirty_step_c a (g, visits)) with
  | inl state => execution_inv initial state
  | inr state => execution_inv initial state /\ Egraph.dirty (fst state) = []
  end.
Proof.
  intros [Hinv [Hlayout [Hnodes Hnext]]].
  cbn [fst] in Hinv, Hlayout, Hnodes, Hnext.
  pose proof (dirty_step_correct g visits Hinv Hlayout) as Hstep.
  destruct (Cost.value (Egraph.dirty_step_c a (g, visits))) as [[h count]|[h count]].
  - destruct Hstep as [Hh [Hl [Hn Hb]]]; unfold execution_inv; cbn [fst].
    split; [exact Hh|]; split; [exact Hl|]; split; congruence.
  - destruct Hstep as [Hh [Hl [Hn [Hb Hempty]]]]; split; [|exact Hempty].
    unfold execution_inv; cbn [fst].
    split; [exact Hh|]; split; [exact Hl|]; split; congruence.
Qed.

(** Every actual run retains the invariant, and its stopping branch has no dirty class left. *)
Theorem run_preserved initial fuel state result :
  runs (Egraph.dirty_step_c a) fuel state result -> execution_inv initial state ->
  match result with
  | inl final => execution_inv initial final
  | inr final => execution_inv initial final /\ Egraph.dirty (fst final) = []
  end.
Proof.
  intro Hrun; induction Hrun as
    [state|n state final Hstop|n state next result Hnext Hrun IH]; intro Hinv.
  - exact Hinv.
  - destruct state as [g visits].
    pose proof (step_execution_inv initial g visits Hinv) as Hstep.
    rewrite Hstop in Hstep; exact Hstep.
  - apply IH; destruct state as [g visits].
    pose proof (step_execution_inv initial g visits Hinv) as Hstep.
    rewrite Hnext in Hstep; exact Hstep.
Qed.

(** The Cost iterator inherits preservation from the same counted dirty callbacks. *)
Theorem iterate_preserved fuel g visits :
  Egraph.kernel_inv a g -> EggTransition.layout a g ->
  match Cost.value (iterate (Egraph.dirty_step_c a) fuel (g, visits)) with
  | inl state => execution_inv g state
  | inr state => execution_inv g state /\ Egraph.dirty (fst state) = []
  end.
Proof.
  intros Hinv Hlayout.
  apply (run_preserved g _ _ _ (iterate_value (Egraph.dirty_step_c a) fuel (g, visits))).
  unfold execution_inv; cbn [fst].
  split; [exact Hinv|]; split; [exact Hlayout|]; split; reflexivity.
Qed.

Section Property.
Context (P : Egraph.t K Sort V -> Prop).
Context (Hparent : forall h i tail,
  Egraph.kernel_inv_on a h (i :: tail) -> EggTransition.layout a h ->
  P h -> P (Egraph.repair_node a h i)).
Context (Hqueue : forall h queue, P h -> P (Egraph.with_queue h queue)).

Local Lemma fold_property parents g visits :
  Egraph.kernel_inv_on a g parents -> EggTransition.layout a g -> P g ->
  P (fst (fold_left (fun state i =>
    (Egraph.repair_node a (fst state) i, N.succ (snd state))) parents (g, visits))).
Proof.
  revert g visits; induction parents as [|i parents IH]; intros g visits Hinv Hlayout HP.
  - exact HP.
  - destruct (EggRepairStep.repair_node_correct a g i parents Hinv Hlayout Hcodes)
      as [Hnext Hnext_layout].
    cbn [fold_left fst snd].
    exact (IH _ _ Hnext Hnext_layout (Hparent g i parents Hinv Hlayout HP)).
Qed.

(** A callback property composes through the actual dequeue and complete parent batch. *)
Theorem dirty_step_property g visits :
  Egraph.kernel_inv a g -> EggTransition.layout a g -> P g ->
  match Cost.value (Egraph.dirty_step_c a (g, visits)) with
  | inl state | inr state => P (fst state)
  end.
Proof.
  intros Hinv Hlayout HP; rewrite EggRebuild.dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g))) as [[loser queue]|] eqn:Hpop;
    [|exact HP].
  cbv zeta; fold (Egraph.with_queue g queue).
  pose proof (fold_property
    (EggParent.get (Egraph.parents (Egraph.with_queue g queue)) loser)
    (Egraph.with_queue g queue) 0%N
    (EggRepairInv.pop_kernel_inv a g loser queue Hinv Hpop)
    (EggTransition.queue_layout a g queue Hlayout) (Hqueue g queue HP)) as Hfold.
  rewrite <- EggRebuild.repair_equation in Hfold.
  destruct (EggRebuild.repair a (Egraph.with_queue g queue) loser) as [h count].
  exact Hfold.
Qed.

Local Lemma run_property fuel state result :
  runs (Egraph.dirty_step_c a) fuel state result ->
  Egraph.kernel_inv a (fst state) -> EggTransition.layout a (fst state) -> P (fst state) ->
  match result with inl final | inr final => P (fst final) end.
Proof.
  intro Hrun; induction Hrun as
    [state|n state final Hstop|n state next result Hnext Hrun IH];
    intros Hinv Hlayout HP; [exact HP| |].
  - destruct state as [g visits].
    pose proof (dirty_step_property g visits Hinv Hlayout HP) as Hproperty.
    rewrite Hstop in Hproperty; exact Hproperty.
  - destruct state as [g visits].
    pose proof (dirty_step_property g visits Hinv Hlayout HP) as Hproperty.
    pose proof (dirty_step_correct g visits Hinv Hlayout) as Hpreserved.
    rewrite Hnext in Hproperty, Hpreserved; destruct next as [h count].
    destruct Hpreserved as [Hh [Hl Hrest]]; exact (IH Hh Hl Hproperty).
Qed.

(** Any proved parent and metadata property holds on both outcomes of the actual binary driver. *)
Theorem iterate_property fuel g visits :
  Egraph.kernel_inv a g -> EggTransition.layout a g -> P g ->
  match Cost.value (iterate (Egraph.dirty_step_c a) fuel (g, visits)) with
  | inl state | inr state => P (fst state)
  end.
Proof.
  intros Hinv Hlayout HP.
  exact (run_property _ _ _ (iterate_value (Egraph.dirty_step_c a) fuel (g, visits))
    Hinv Hlayout HP).
Qed.

End Property.

End Graph.

End EggRepairBatch.
