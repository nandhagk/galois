(** * Reverse-view dominator parents

    Post-dominator parent construction binds the checked prepared reversal before the backend.
    For example, a node with paths to two exits need not have a strict post-dominator.
    Builds on: GraphDomBackend, GraphPrepared and the public reverse-dominance transport. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphDomBackend
  GraphFrontierControl.
Import Cost.Notations.

Module DomPost.

(** Reverse-view construction retains every duplicate and unknown exit-conversion charge. *)
Definition parents_c {V E} b (p : Prepared.t V E) exits :=
  let* reversed := Prepared.reverse_c p exits in
  DomBackend.parents_c b reversed.

Definition parents {V E} b (p : Prepared.t V E) exits :=
  Cost.value (parents_c b p exits).

(** Parent construction runs the selected backend on the actual public reversed prepared value. *)
Theorem parents_equation {V E} b (p : Prepared.t V E) exits :
  parents b p exits = DomBackend.parents b (Prepared.reverse p exits).
Proof.
  reflexivity.
Qed.

(** Exact callee accounting includes reversal work before any selected backend work. *)
Theorem parents_cost_equation {V E} b (p : Prepared.t V E) exits :
  Cost.ticks (parents_c b p exits) =
    (Cost.ticks (Prepared.reverse_c p exits) +
      Cost.ticks (DomBackend.parents_c b (Prepared.reverse p exits)))%N.
Proof.
  unfold parents_c. rewrite Cost.ticks_bind. reflexivity.
Qed.

(** Every post-dominance query at a listed node is the same query on the reversed view. *)
Theorem post_dominates_iff_reverse {V E} (p : Prepared.t V E) exits d n :
  Prepared.ready p -> In n (Graph.nodes (Prepared.graph p)) ->
  (post_dominates (Prepared.graph p) (Prepared.present (Prepared.name_of p) exits) d n <->
    dominates (Prepared.graph (Prepared.reverse p exits)) d n).
Proof.
  apply FrontierControl.post_is_reverse.
Qed.

(** Full reverse-view construction binds the actual checked reversal before tree computation. *)
Definition post_c {V E} b (p : Prepared.t V E) exits :=
  let* reversed := Prepared.reverse_c p exits in
  DomBackend.compute_c b reversed.

Definition post {V E} b (p : Prepared.t V E) exits := Cost.value (post_c b p exits).

(** Full post-tree construction uses the same selected backend on the reversed view. *)
Theorem post_equation {V E} b (p : Prepared.t V E) exits :
  post b p exits = DomBackend.compute b (Prepared.reverse p exits).
Proof.
  reflexivity.
Qed.

(** A lawful backend's actual reversed-view result is exact when the supplied exits denote valid IDs. *)
Theorem post_exact {V E} b (p : Prepared.t V E) exits :
  DomBackend.backend_laws b -> Prepared.ready p ->
  (forall i, In i exits -> Prepared.valid_id p i) ->
  Dom.exact (Prepared.reverse p exits) (post b p exits).
Proof.
  intros Hlaws Hready Hexits. rewrite post_equation.
  exact (DomBackend.compute_exact b _ Hlaws (Prepared.reverse_ready p exits Hready Hexits)).
Qed.

End DomPost.
