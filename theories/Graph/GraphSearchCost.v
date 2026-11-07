(** * Search visitor credit

    Visitor potential bounds retain arbitrary callee charges along the actual event sequence.
    For example, a step that enters a child dispatches both its edge and its entry callback.
    Builds on: GraphSearch, GraphSearchExact and the costed list potential theorem. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact.
Import List.ListNotations Cost.Notations.

Module SearchCost.
Local Open Scope N_scope.

(** Visitor credits telescope over the actual events and retain each dispatch-list traversal tick. *)
Theorem apply_events_cost {E S} (vis : Visitor.t E S) Phi kv evs s :
  Visitor.amortised vis Phi kv ->
  (Cost.ticks (SearchRun.apply_events_c vis evs s) +
    Phi (SearchRun.apply_events vis evs s) <=
    N.of_nat (length evs) * (kv + 1) + Phi s)%N.
Proof.
  intro Hamortised.
  pose proof (ticks_fold_left_c_potential
    (fun s ev => Visitor.apply_c vis ev s) (fun _ => True) Phi kv evs s) as Hfold.
  assert (Hstep : forall s ev, True -> In ev evs ->
    True /\ (Cost.ticks (Visitor.apply_c vis ev s) +
      Phi (Visitor.apply vis ev s) <= kv + Phi s)%N).
  { intros state ev _ _. split; [exact I|apply Hamortised]. }
  specialize (Hfold Hstep I).
  fold (SearchRun.apply_events_c vis evs s) in Hfold.
  rewrite SearchRun.apply_events_value in Hfold. exact Hfold.
Qed.

(** Every transition emits at most two eligible events, regardless of rejected adjacency work. *)
Theorem transition_events_bound {V E} (p : Prepared.t V E) scope w :
  (length (snd (SearchRun.transition p scope w)) <= 2)%nat.
Proof.
  destruct w as [stack c]. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; [cbn; lia|cbn; lia|].
  destruct (Scope.admits scope v); [|cbn; lia].
  destruct (Prepared.name_of p v); [|cbn; lia].
  destruct (SearchRun.edge_kind c u v); cbn; lia.
Qed.

(** Each actual step spends its primitive work and at most two amortised visitor dispatches. *)
Theorem step_visitor_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope w s :
  Visitor.amortised vis Phi kv ->
  (Cost.ticks (SearchRun.step_c p vis scope (w, s)) +
    Phi (snd (SearchRun.unwrap (Cost.value (SearchRun.step_c p vis scope (w, s))))) <=
    Cost.ticks (SearchRun.transition_c p scope w) + 2 * (kv + 1) + Phi s)%N.
Proof.
  intro Hamortised.
  pose proof (apply_events_cost vis Phi kv
    (snd (SearchRun.transition p scope w)) s Hamortised) as Hvisitor.
  pose proof (transition_events_bound p scope w) as Hlength.
  unfold SearchRun.step_c. rewrite Cost.ticks_bind, Cost.value_bind.
  fold (SearchRun.transition p scope w).
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd] in Hvisitor, Hlength |- *;
    rewrite Cost.ticks_bind, Cost.value_bind, SearchRun.apply_events_value;
    rewrite Cost.value_ret;
    cbn [SearchRun.unwrap snd]; rewrite Cost.ticks_ret, N.add_0_r.
  all: assert (HlengthN : (N.of_nat (length evs) <= 2)%N).
  all: try (destruct (length evs) as [|[|n]]; [cbn; lia|cbn; lia|];
    assert (Hn : n = 0%nat) by lia; subst n; reflexivity).
  all: nia.
Qed.

End SearchCost.
