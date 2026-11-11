(** * Global costs of actual dominance trees

    Actual prologue, selected finisher, inverse erasure and single-search numbering are composed.
    For example, selecting NCA changes only its actual finisher price in the complete tree bound.
    Builds on: complete primitive phase bounds and proved builtin backend laws. *)

From Stdlib Require Import PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphDomSpec
  GraphDomSemi GraphDomLt GraphDomNca GraphDomBackend GraphDomNumber GraphDomPrologueCost
  GraphDomLtCost GraphDomNcaCost GraphDomOutputCost.
Import Cost.Notations.

Module DomPipelineCost.
Local Open Scope N_scope.

Local Lemma compute_cost_equation {V E} b (p : Prepared.t V E) :
  DomBackend.backend_laws b -> Prepared.ready p ->
  Cost.ticks (DomBackend.compute_c b p) =
    Cost.ticks (DomSemi.semi_c p) +
      (1 + (Cost.ticks (DomBackend.finish_c b (DomSemi.compute p)) +
        Cost.ticks
          (let* parents := DomSemi.erase_c (DomSemi.compute p) (DomLt.finish (DomSemi.compute p)) in
           let* ranks := rev_c (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) in
           let* live := Prepared.present_c
             (fun rank => Map.get_c positive_encoding rank
               (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p)))) ranks in
           DomNumber.of_parents_c live parents))).
Proof.
  intros Hlaws Hready.
  unfold DomBackend.compute_c.
  rewrite (Cost.ticks_bind (DomSemi.semi_c p)). fold (DomSemi.compute p).
  rewrite (Cost.ticks_bind Cost.step), Cost.ticks_step.
  rewrite (Cost.ticks_bind (DomBackend.finish_c b (DomSemi.compute p))).
  rewrite (DomBackend.finish_agrees_lt b p Hlaws Hready). reflexivity.
Qed.

(** The LT budget includes the entire actual producer and every output construction phase. *)
Definition lt_bound {V E} (p : Prepared.t V E) e b ko ks kt :=
  DomPrologueCost.prologue_bound p e b ko ks kt + 1 +
    DomLtCost.finish_bound p + DomOutputCost.output_bound p.

(** The NCA budget retains complete setup/output and its actual numeric finisher work. *)
Definition nca_bound {V E} (p : Prepared.t V E) e b ko ks kt :=
  DomPrologueCost.prologue_bound p e b ko ks kt + 1 +
    16 * DomNcaCost.actual_work p + DomOutputCost.output_bound p.

(** Actual LT tree computation has a global numeric bound from original primitive callbacks. *)
Theorem lt_cost {V E} (p : Prepared.t V E) e b ko ks kt :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  Cost.ticks (DomBackend.compute_c DomBackend.lt p) <= lt_bound p e b ko ks kt.
Proof.
  intros Hready Hcallbacks.
  pose proof (DomPrologueCost.semi_cost p e b ko ks kt Hready Hcallbacks) as Hsetup.
  pose proof (DomLtCost.actual_finish_cost p Hready) as Hfinish.
  pose proof (DomOutputCost.output_cost p Hready) as Houtput.
  rewrite (compute_cost_equation DomBackend.lt p DomBackend.lt_laws Hready).
  eapply N.le_trans with (m := DomPrologueCost.prologue_bound p e b ko ks kt +
    (1 + (DomLtCost.finish_bound p + DomOutputCost.output_bound p))).
  - apply N.add_le_mono; [exact Hsetup|].
    apply N.add_le_mono; [reflexivity|]. now apply N.add_le_mono.
  - unfold lt_bound. lia.
Qed.

(** Actual NCA computation has a global numeric bound without an owned phase-price premise. *)
Theorem semi_nca_cost {V E} (p : Prepared.t V E) e b ko ks kt :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  Cost.ticks (DomBackend.compute_c DomBackend.semi_nca p) <= nca_bound p e b ko ks kt.
Proof.
  intros Hready Hcallbacks.
  pose proof (DomPrologueCost.semi_cost p e b ko ks kt Hready Hcallbacks) as Hsetup.
  pose proof (DomNcaCost.actual_finish_numeric_cost p Hready) as Hfinish.
  pose proof (DomOutputCost.output_cost p Hready) as Houtput.
  rewrite (compute_cost_equation DomBackend.semi_nca p DomBackend.semi_nca_laws Hready).
  eapply N.le_trans with (m := DomPrologueCost.prologue_bound p e b ko ks kt +
    (1 + (16 * DomNcaCost.actual_work p + DomOutputCost.output_bound p))).
  - apply N.add_le_mono; [exact Hsetup|].
    apply N.add_le_mono; [reflexivity|]. now apply N.add_le_mono.
  - unfold nca_bound. lia.
Qed.

(** Complete LT budgets lift over families satisfying original primitive contracts. *)
Theorem lt_bigO {X V E} (p : X -> Prepared.t V E) (e b ko ks kt : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, PreparedCost.prepare_bounds (Prepared.node_enc (p x)) (Prepared.graph (p x))
    (e x) (b x) (ko x) (ks x) (kt x)) ->
  bigO (fun x => lt_bound (p x) (e x) (b x) (ko x) (ks x) (kt x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.lt (p x))).
Proof.
  intros Hready Hcallbacks. exists 1. intro x.
  pose proof (lt_cost (p x) (e x) (b x) (ko x) (ks x) (kt x) (Hready x) (Hcallbacks x)).
  lia.
Qed.

(** Complete NCA budgets lift over primitive callback domains without result premises. *)
Theorem semi_nca_bigO {X V E} (p : X -> Prepared.t V E) (e b ko ks kt : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, PreparedCost.prepare_bounds (Prepared.node_enc (p x)) (Prepared.graph (p x))
    (e x) (b x) (ko x) (ks x) (kt x)) ->
  bigO (fun x => nca_bound (p x) (e x) (b x) (ko x) (ks x) (kt x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (p x))).
Proof.
  intros Hready Hcallbacks. exists 1. intro x.
  pose proof (semi_nca_cost (p x) (e x) (b x) (ko x) (ks x) (kt x) (Hready x) (Hcallbacks x)).
  lia.
Qed.

End DomPipelineCost.
