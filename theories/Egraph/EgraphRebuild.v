(** * Deferred repair batches and their actual visit counts

    A repair count is the second projection of the fold that updates the graph.
    For example, a losing bucket of two parents records two visits even if both are in one class.
    Builds on: EgraphGraph, EgraphCoreIndex and the public Cost loop semantics. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Egraph Require Import EgraphSyntax EgraphCoreIndex EgraphGraph.
Import List.ListNotations Cost.Notations.

Module EggRebuild.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

Definition repair_c (g : Egraph.t K Sort V) loser := Egraph.repair_c a g loser.
Definition repair g loser := Cost.value (repair_c g loser).

(** Repair's pure equation traverses exactly the selected loser's stored parent snapshot. *)
Theorem repair_equation g loser :
  repair g loser =
    fold_left (fun result i =>
      (Egraph.repair_node a (fst result) i, N.succ (snd result)))
      (EggParent.get (Egraph.parents g) loser) (g, 0%N).
Proof.
  unfold repair, repair_c, Egraph.repair_c; rewrite Cost.value_bind.
  fold (EggParent.get (Egraph.parents g) loser).
  rewrite value_fold_left_c; reflexivity.
Qed.

Local Lemma repair_fold_count parents (state : Egraph.t K Sort V * N) :
  snd (fold_left (fun result i =>
    (Egraph.repair_node a (fst result) i, N.succ (snd result))) parents state) =
    (snd state + N.of_nat (length parents))%N.
Proof.
  revert state; induction parents as [|i parents IH]; intros [g visits].
  - cbn [fold_left snd length]; lia.
  - cbn [fold_left fst snd]; rewrite IH.
    cbn [length snd]; rewrite Nat2N.inj_succ; lia.
Qed.

(** The repair counter counts the actual fold's parent visits without a second traversal runner. *)
Theorem repair_count g loser :
  snd (repair g loser) =
    N.of_nat (length (EggParent.get (Egraph.parents g) loser)).
Proof.
  rewrite repair_equation, repair_fold_count; reflexivity.
Qed.

(** A dirty step's value keeps its instrumented count on both continuation and stopping branches. *)
Theorem dirty_step_equation (g : Egraph.t K Sort V) visits :
  Cost.value (Egraph.dirty_step_c a (g, visits)) =
    match EggPending.pop (Egraph.pending (Egraph.private g)) with
    | None => inr (g, visits)
    | Some (loser, queue) =>
      let kernel := Egraph.Kernel_data K Sort V (Egraph.parents g) queue
        (Egraph.cached g) (Egraph.edges g) in
      let popped := Egraph.Make K Sort V (Egraph.uf g) (Egraph.nodes g) (Egraph.memo g)
        (Egraph.next g) kernel in
      let result := repair popped loser in
      inl (fst result, N.add visits (snd result))
    end.
Proof.
  unfold Egraph.dirty_step_c; rewrite Cost.value_bind.
  fold (EggPending.pop (Egraph.pending (Egraph.private g))).
  destruct (EggPending.pop (Egraph.pending (Egraph.private g))) as [[loser queue]|].
  - rewrite Cost.value_bind; reflexivity.
  - reflexivity.
Qed.

(** Every continuing dirty step adds the number of parents in its actual dequeued snapshot. *)
Theorem dirty_step_count g visits h total :
  Cost.value (Egraph.dirty_step_c a (g, visits)) = inl (h, total) ->
  exists loser queue,
    EggPending.pop (Egraph.pending (Egraph.private g)) = Some (loser, queue) /\
    total = (visits + N.of_nat (length (EggParent.get (Egraph.parents g) loser)))%N.
Proof.
  rewrite dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g)))
    as [[loser queue]|] eqn:Hpop; [|discriminate].
  set (kernel := Egraph.Kernel_data K Sort V (Egraph.parents g) queue
    (Egraph.cached g) (Egraph.edges g)).
  set (popped := Egraph.Make K Sort V (Egraph.uf g) (Egraph.nodes g) (Egraph.memo g)
    (Egraph.next g) kernel).
  intro Hresult; injection Hresult as Hgraph <-.
  exists loser, queue; split; [reflexivity|].
  rewrite repair_count; reflexivity.
Qed.

(** Stopping preserves the instrumented state and certifies an empty dirty-class queue. *)
Theorem dirty_step_stops g visits h total :
  Cost.value (Egraph.dirty_step_c a (g, visits)) = inr (h, total) ->
  h = g /\ total = visits /\ Egraph.dirty g = [].
Proof.
  rewrite dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g)))
    as [[loser queue]|] eqn:Hpop; [discriminate|].
  intro Hresult; injection Hresult as <- <-.
  split; [reflexivity|]; split; [reflexivity|].
  rewrite EggPending.pop_equation in Hpop.
  unfold Egraph.dirty.
  destruct (EggPending.entries (Egraph.pending (Egraph.private g))); congruence.
Qed.

Local Definition visits_of (result : (Egraph.t K Sort V * N) + (Egraph.t K Sort V * N)) :=
  match result with inl state | inr state => snd state end.

(** Count instrumentation is monotone along the actual Cost loop's run relation. *)
Theorem run_count_monotone fuel state result :
  runs (Egraph.dirty_step_c a) fuel state result ->
  (snd state <= visits_of result)%N.
Proof.
  intro Hrun; induction Hrun as
    [state|n state final Hstop|n state next result Hnext Hrun IH].
  - reflexivity.
  - destruct state as [g visits], final as [h total].
    destruct (dirty_step_stops g visits h total Hstop) as [Hgraph [Hcount Hempty]].
    cbn [visits_of snd]; lia.
  - destruct state as [g visits], next as [h total].
    destruct (dirty_step_count g visits h total Hnext) as [loser [queue [Hpop Hcount]]].
    cbn [snd] in *; lia.
Qed.

(** Binary iteration observes the counter of its actual repair steps on every fuel outcome. *)
Theorem iterate_count_monotone fuel g visits :
  (visits <= visits_of (Cost.value (iterate (Egraph.dirty_step_c a) fuel (g, visits))))%N.
Proof.
  exact (run_count_monotone _ _ _ (iterate_value (Egraph.dirty_step_c a) fuel (g, visits))).
Qed.

End Graph.

End EggRebuild.
