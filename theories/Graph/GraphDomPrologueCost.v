(** * Complete shared dominance prologue costs

    One virtual preparation, one search, one rank layout and one settlement are composed.
    For example, all incoming-row filtering and real-name conversion charges precede settlement.
    Builds on: GraphDomVirtualCost, GraphDomLayoutCost and the proved actual incoming inventory. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphVisitor
  GraphSearchSpec GraphSearch GraphSearchCost GraphReach GraphDomVirtual GraphDomSemi GraphDomDfs
  GraphDomSemiCost
  GraphDomVirtualCost GraphDomLayoutCost GraphDomPredSize.
Import Cost.Notations.

Module DomPrologueCost.
Local Open Scope N_scope.

Section Prologue.
Context {V E : Type} (p : Prepared.t V E).
Local Abbreviation q := (DomVirtual.virtual p).
Local Abbreviation g := (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)).
Local Abbreviation result := (DomSemi.search (DomSemi.compute p)).
Local Abbreviation ranked := (DomSemi.ranked (DomSemi.compute p)).

Local Lemma width_bound :
  Prepared.ready p -> SearchCost.width_bound q (Prepared.entry_ids q) (DomLayoutCost.raw_width p).
Proof.
  intros Hready i [Hvalid|Hroot].
  - exact (DomLayoutCost.valid_width p i Hready Hvalid).
  - apply (Prepared.entry_ids_spec q i
      (proj2 (proj2 (DomVirtual.virtual_ready p Hready)))) in Hroot.
    destruct Hroot as [name [Hname Hid]].
    exact (DomLayoutCost.virtual_id_width p name i Hready Hid).
Qed.

Definition search_bound :=
  SearchCost.search_k *
    SearchCost.search_size q (Prepared.entry_ids q) (DomLayoutCost.raw_width p) 1.

(** The one actual input search has its public primitive graph/root/fuel bound. *)
Theorem search_cost :
  Prepared.ready p ->
  Cost.ticks (SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt) <=
    search_bound.
Proof.
  intro Hready.
  pose proof (SearchCost.search_cost q Visitor.noop (fun _ : unit => 0) 1
    Reach.unrestricted (Prepared.entry_ids q) (DomLayoutCost.raw_width p) tt
    (DomVirtual.virtual_ready p Hready) (width_bound Hready)
    (Visitor.noop_amortised (fun _ : unit => 0))) as Hsearch.
  cbn beta in Hsearch. rewrite N.add_0_r in Hsearch. exact Hsearch.
Qed.

Definition settlement_bound :=
  N.of_nat (length (Search.preorder result)) * (13 + 6 * DomLayoutCost.rank_width p) +
  N.of_nat (edge_count g) *
    (5 + 2 * DomLayoutCost.rank_width p +
      N.pos (DomSemiCost.rank_limit p) * (20 + 11 * DomLayoutCost.rank_width p)).

(** Settlement is bounded by actual graph edges without an assumed state or occurrence budget. *)
Theorem settlement_cost :
  Prepared.ready p ->
  Cost.ticks
    (fold_left_c (DomSemi.settle_c ranked) (DomSemi.reverse_order ranked) DomSemi.initial) <=
    settlement_bound.
Proof.
  intro Hready.
  pose proof (proj2 (DomSemiCost.actual_settlement_cost p Hready)) as Hsettle.
  pose proof (DomPredSize.actual_incoming_mass p Hready) as Hmass.
  assert (Hlength : length (DomSemi.reverse_order ranked) = length (Search.preorder result)).
  { rewrite (DomDfs.settlement_order p Hready), length_rev, length_map, length_seq. reflexivity. }
  unfold DomSemiCost.settlement_bound in Hsettle. rewrite Hlength in Hsettle.
  change (Cost.ticks (fold_left_c (DomSemi.settle_c ranked)
    (DomSemi.reverse_order ranked) DomSemi.initial) <=
    N.of_nat (length (Search.preorder result)) * (13 + 6 * DomLayoutCost.rank_width p) +
      DomSemiCost.incoming_mass ranked (DomSemi.reverse_order ranked) *
        (1 + (N.pos (DomSemiCost.rank_limit p) * (20 + 11 * DomLayoutCost.rank_width p) +
          4 + 2 * DomLayoutCost.rank_width p))) in Hsettle.
  replace (1 + (N.pos (DomSemiCost.rank_limit p) * (20 + 11 * DomLayoutCost.rank_width p) +
    4 + 2 * DomLayoutCost.rank_width p)) with
    (5 + 2 * DomLayoutCost.rank_width p +
      N.pos (DomSemiCost.rank_limit p) * (20 + 11 * DomLayoutCost.rank_width p)) in Hsettle by lia.
  eapply N.le_trans; [exact Hsettle|].
  apply N.add_le_mono; [reflexivity|].
  apply N.mul_le_mono; [exact Hmass|reflexivity].
Qed.

Definition prologue_bound e b ko ks kt :=
  DomVirtualCost.virtual_bound p e b ko ks kt + search_bound +
    DomLayoutCost.layout_bound p e b + settlement_bound.

(** The entire prologue has a four-phase primitive numeric bound without a result premise. *)
Theorem semi_cost e b ko ks kt :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  Cost.ticks (DomSemi.semi_c p) <= prologue_bound e b ko ks kt.
Proof.
  intros Hready Hcallbacks.
  pose proof (DomVirtualCost.virtual_cost p e b ko ks kt Hready Hcallbacks) as Hvirtual.
  pose proof (search_cost Hready) as Hsearch.
  pose proof (DomLayoutCost.layout_cost p e b ko ks kt Hready Hcallbacks) as Hlayout.
  pose proof (settlement_cost Hready) as Hsettle.
  unfold DomSemi.semi_c.
  rewrite (Cost.ticks_bind (DomVirtual.virtual_c p)). fold q.
  rewrite (Cost.ticks_bind
    (SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt)).
  rewrite <- DomSemi.search_equation.
  rewrite (Cost.ticks_bind (DomSemi.layout_c p q result)).
  assert (Hranked : Cost.value (DomSemi.layout_c p q result) = ranked) by reflexivity.
  rewrite Hranked.
  rewrite (Cost.ticks_bind
    (fold_left_c (DomSemi.settle_c ranked) (DomSemi.reverse_order ranked) DomSemi.initial)),
    Cost.ticks_ret.
  unfold prologue_bound. lia.
Qed.

End Prologue.

(** Complete prologue costs lift over families satisfying original primitive callback duties. *)
Theorem semi_bigO {X V E} (p : X -> Prepared.t V E) (e b ko ks kt : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, PreparedCost.prepare_bounds (Prepared.node_enc (p x)) (Prepared.graph (p x))
    (e x) (b x) (ko x) (ks x) (kt x)) ->
  bigO (fun x => prologue_bound (p x) (e x) (b x) (ko x) (ks x) (kt x))
    (fun x => Cost.ticks (DomSemi.semi_c (p x))).
Proof.
  intros Hready Hcallbacks. exists 1. intro x.
  pose proof (semi_cost (p x) (e x) (b x) (ko x) (ks x) (kt x) (Hready x) (Hcallbacks x)).
  lia.
Qed.

End DomPrologueCost.
