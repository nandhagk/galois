(** * Producer bounds derived from original input counts

    Original nodes, edge occurrences and raw entries supply every augmented graph-size budget.
    For example, repeated entries retain their occurrence price after root-edge deduplication.
    Builds on: GraphDomSize and complete GraphDomGlobalCost contracts. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphDomBackend
  GraphDomSize GraphDomGlobalCost.

Module DomInputCost.
Local Open Scope N_scope.

Definition nodes {V E} (p : Prepared.t V E) := (1 + length (Graph.nodes (Prepared.graph p)))%nat.
Definition roots {V E} (p : Prepared.t V E) := length (Graph.entries (Prepared.graph p)).
Definition augmented_edges {V E} (p : Prepared.t V E) :=
  (1 + edge_count (Prepared.graph p) + roots p)%nat.

(** Primitive callbacks and explicit binary widths refer exclusively to original input sizes. *)
Record bounds {V E} (p : Prepared.t V E) w : Prop := {
  callbacks : PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) w w w w w;
  allocation_width : N.pos (Pos.size (Pos.of_succ_nat (nodes p))) <= w;
  input_fuel_width :
    N.pos (Pos.size (Pos.of_succ_nat (2 * nodes p + augmented_edges p))) <= w;
  output_fuel_width :
    N.pos (Pos.size (Pos.of_succ_nat (2 * nodes p + nodes p * nodes p + 1))) <= w
}.
Arguments callbacks {V E p w} _.
Arguments allocation_width {V E p w} _.
Arguments input_fuel_width {V E p w} _.
Arguments output_fuel_width {V E p w} _.

(** Augmented-edge and root budgets follow from original counts and ready encoder laws. *)
Theorem global_bounds {V E} (p : Prepared.t V E) w :
  Prepared.ready p -> bounds p w ->
  DomGlobalCost.bounds p (nodes p) (augmented_edges p) (roots p) w.
Proof.
  intros Hready Hb. constructor.
  - reflexivity.
  - unfold augmented_edges. lia.
  - pose proof (DomSize.virtual_edges_bound (Prepared.node_enc p) (Prepared.graph p)
      (Prepared.encoding_valid p (proj2 (proj2 Hready)))) as Hedge.
    unfold augmented_edges, roots. lia.
  - reflexivity.
  - exact (callbacks Hb).
  - exact (allocation_width Hb).
  - exact (input_fuel_width Hb).
  - exact (output_fuel_width Hb).
Qed.

(** Complete LT costs have an input-only bound without a produced virtual-graph size premise. *)
Theorem lt_cost {V E} (p : Prepared.t V E) w :
  Prepared.ready p -> bounds p w ->
  Cost.ticks (DomBackend.compute_c DomBackend.lt p) <=
    DomGlobalCost.lt_k * DomGlobalCost.work (nodes p) (augmented_edges p) (roots p) w.
Proof.
  intros Hready Hb. apply DomGlobalCost.lt_cost; [exact Hready|now apply global_bounds].
Qed.

(** Complete NCA costs retain all actual quadratic work in the original-input-derived budget. *)
Theorem semi_nca_cost {V E} (p : Prepared.t V E) w :
  Prepared.ready p -> bounds p w ->
  Cost.ticks (DomBackend.compute_c DomBackend.semi_nca p) <=
    DomGlobalCost.lt_k * DomGlobalCost.work (nodes p) (augmented_edges p) (roots p) w.
Proof.
  intros Hready Hb. apply DomGlobalCost.semi_nca_cost; [exact Hready|now apply global_bounds].
Qed.

(** Input-derived LT bounds lift to families with primitive and numeric-width duties. *)
Theorem lt_bigO {X V E} (p : X -> Prepared.t V E) (w : X -> N) :
  (forall x, Prepared.ready (p x)) -> (forall x, bounds (p x) (w x)) ->
  bigO (fun x => DomGlobalCost.work (nodes (p x)) (augmented_edges (p x)) (roots (p x)) (w x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.lt (p x))).
Proof.
  intros Hready Hb. apply DomGlobalCost.lt_bigO; [exact Hready|].
  intro x. exact (global_bounds (p x) (w x) (Hready x) (Hb x)).
Qed.

(** Original-input-derived NCA families include every preparation, finisher and annotation phase. *)
Theorem semi_nca_bigO {X V E} (p : X -> Prepared.t V E) (w : X -> N) :
  (forall x, Prepared.ready (p x)) -> (forall x, bounds (p x) (w x)) ->
  bigO (fun x => DomGlobalCost.work (nodes (p x)) (augmented_edges (p x)) (roots (p x)) (w x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (p x))).
Proof.
  intros Hready Hb. apply DomGlobalCost.semi_nca_bigO; [exact Hready|].
  intro x. exact (global_bounds (p x) (w x) (Hready x) (Hb x)).
Qed.

End DomInputCost.
