(** * Tarjan producer guarantees

    Producer theorems concern the visitor state returned by the actual shared search.
    For example, an unknown supplied root has no component owner.
    Builds on: GraphTarjanState and the public search guarantees. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSccSpec GraphTarjan GraphTarjanState.
Import List.ListNotations.

Module TarjanExact.

(** Popping splits the actual stack into precisely its consumed prefix and surviving suffix. *)
Theorem pop_split root i xs lows active own :
  let answer := Tarjan.pop root i xs lows active own in
  xs = Tarjan.members answer ++ Tarjan.tail answer /\
    (In root xs -> In root (Tarjan.members answer)).
Proof.
  apply TarjanStateFacts.pop_split.
Qed.

(** Every actual owner map has canonical storage even without preparation readiness. *)
Theorem compute_owners_wf {V E} (p : Prepared.t V E) scope roots :
  Map.wf positive_encoding (Scc.comp_of (Tarjan.compute p scope roots)).
Proof.
  apply TarjanStateFacts.compute_owners_wf.
Qed.

(** Discovery ranks agree with the same actual visitor run's preorder. *)
Theorem discovery_index {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  (Map.get positive_encoding v
    (Tarjan.disc (snd (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))) = Some i <->
    nth_error (Search.preorder (fst (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))))
      (Nat.pred (Pos.to_nat i)) = Some v).
Proof.
  apply TarjanStateFacts.discovery_index.
Qed.

(** Every owner binding belongs to the admitted reachable region for arbitrary roots. *)
Theorem owners_reachable {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
    Search.scoped_reachable p scope roots v.
Proof.
  apply TarjanStateFacts.owners_reachable.
Qed.

(** Every emitted member belongs to the admitted reachable region for arbitrary roots. *)
Theorem components_reachable {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> In v (concat (Scc.components (Tarjan.compute p scope roots))) ->
    Search.scoped_reachable p scope roots v.
Proof.
  apply TarjanStateFacts.components_reachable.
Qed.

(** Scope-rejected vertices have no owner in the actual computation. *)
Theorem rejected_unowned {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> Scope.admits scope v = false ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = None.
Proof.
  apply TarjanStateFacts.rejected_unowned.
Qed.

(** Unknown IDs have no owner even when the scope admits them. *)
Theorem unknown_unowned {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> ~ Prepared.valid_id p v ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = None.
Proof.
  apply TarjanStateFacts.unknown_unowned.
Qed.

(** The actual visitor state is the fold of the same actual Search event list. *)
Theorem compute_events {V E} (p : Prepared.t V E) scope roots :
  Tarjan.compute p scope roots =
    Tarjan.result (SearchRun.apply_events Tarjan.visitor
      (SearchRun.events p scope roots) Tarjan.initial).
Proof.
  apply TarjanStateFacts.compute_events.
Qed.

(** Empty supplied roots produce the empty component partition and owner map. *)
Theorem compute_empty {V E} (p : Prepared.t V E) scope :
  Tarjan.compute p scope [] = Scc.Result [] Map.empty.
Proof.
  apply TarjanStateFacts.compute_empty.
Qed.

(** The full SCC specification holds for empty roots without readiness. *)
Theorem empty_roots_exact {V E} (p : Prepared.t V E) scope :
  Scc.exact p scope [] (Tarjan.compute p scope []).
Proof.
  apply TarjanStateFacts.empty_roots_exact.
Qed.

(** One final Search core witnesses the actual visitor result and complete temporal trace. *)
Theorem compute_trace {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  exists final,
    fst (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)) =
      SearchRun.result final /\
    SearchRun.trace_roots p scope roots SearchRun.initial
      (SearchRun.events p scope roots) final /\
    Tarjan.compute p scope roots =
      Tarjan.result (SearchRun.apply_events Tarjan.visitor
        (SearchRun.events p scope roots) Tarjan.initial).
Proof.
  apply TarjanStateFacts.compute_trace.
Qed.

End TarjanExact.
