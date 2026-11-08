(** * Public hierarchy exactness guarantees

    The public owner connects exact forests to scoped weak orders through the structural proof helper.
    For example, readiness supplies the endpoint closure needed by the weak-order edge condition.
    Builds on: GraphHierFacts. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphHierSpec GraphHier GraphHierFacts GraphHierProducer.

Module HierExact.

(** The actual recursive producer is exact for arbitrary scopes and supplied roots from readiness alone. *)
Theorem compute_exact {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> Hier.exact p scope roots (HierRun.compute p scope roots).
Proof.
  apply HierProducer.compute_exact.
Qed.

(** Every scoped path ends at a valid admitted ID. *)
Theorem path_target {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  apply HierFacts.path_target.
Qed.

(** Closed client graph endpoints give every interpreted arc a valid target ID. *)
Theorem arc_target_valid {V E} (p : Prepared.t V E) u e v :
  graph_wf (Prepared.graph p) -> Prepared.arc p u e v -> Prepared.valid_id p v.
Proof.
  apply HierFacts.arc_target_valid.
Qed.

(** Arcs to allowed targets preserve rooted scoped reachability over closed graph endpoints. *)
Theorem reachable_step {V E} (p : Prepared.t V E) scope roots u e v :
  graph_wf (Prepared.graph p) -> Search.scoped_reachable p scope roots u ->
  Prepared.arc p u e v -> Scope.admits scope v = true ->
    Search.scoped_reachable p scope roots v.
Proof.
  apply HierFacts.reachable_step.
Qed.

(** Exact forests over closed graph endpoints flatten to valid scoped weak orders. *)
Theorem exact_wto_valid {V E} (p : Prepared.t V E) scope roots f :
  graph_wf (Prepared.graph p) -> Hier.exact p scope roots f ->
    Wto.valid_within p scope roots (Wto.of_forest f).
Proof.
  apply HierFacts.exact_wto_valid.
Qed.

(** Ready preparation discharges the endpoint-closure duty of hierarchy flattening. *)
Theorem exact_wto_valid_ready {V E} (p : Prepared.t V E) scope roots f :
  Prepared.ready p -> Hier.exact p scope roots f ->
    Wto.valid_within p scope roots (Wto.of_forest f).
Proof.
  apply HierFacts.exact_wto_valid_ready.
Qed.

(** Empty roots have an exact empty hierarchy for every scope and prepared record. *)
Theorem empty_roots_exact {V E} (p : Prepared.t V E) scope :
  Hier.exact p scope nil Hier.Nil.
Proof.
  apply HierFacts.empty_roots_exact.
Qed.

End HierExact.
