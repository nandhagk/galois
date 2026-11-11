(** * Primitive virtual-root preparation costs

    Virtual construction retains raw entry multiplicity and original callback work.
    For example, repeated entries are charged before synthetic entry edges are deduplicated.
    Builds on: GraphDomVirtual, BaseCode serialization and public preparation credit bounds. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap BaseSet BaseInternCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphDomVirtual
  GraphDomCostBasis GraphDomSize.
Import List.ListNotations Cost.Notations.

Module DomVirtualCost.
Local Open Scope N_scope.

Definition node_width b := 10 + 2 * b.
Definition node_price e b := 4 + e + encode_k * node_width b.

(** A real-node tag charges the actual client encoder and the public serializer coefficient. *)
Theorem real_key_bounds {V} (enc : encoding V) e b v :
  Cost.ticks (encode_c enc v) <= e -> key_bits enc v <= b ->
  Cost.ticks (encode_c (DomVirtual.node_encoding enc) (Some v)) <= node_price e b /\
    key_bits (DomVirtual.node_encoding enc) (Some v) <= node_width b.
Proof.
  intros Hprice Hwidth.
  pose proof (sum_encoding_cost enc unit_encoding (inl v)) as Hsum.
  rewrite sum_encoding_bits in Hsum.
  split.
  - change (1 + Cost.ticks (encode_c (sum_encoding enc unit_encoding) (inl v)) <= node_price e b).
    unfold node_price, node_width.
    assert (Hscale : encode_k * (5 + 2 * key_bits enc v) <= encode_k * (10 + 2 * b)).
    { apply N.mul_le_mono; lia. }
    lia.
  - unfold key_bits at 1. rewrite DomVirtual.node_encoding_equation.
    change (key_bits (sum_encoding enc unit_encoding) (inl v) <= node_width b).
    rewrite sum_encoding_bits. unfold node_width. lia.
Qed.

(** The fresh root uses the fixed unit-side tag and requires no client encoder call. *)
Theorem root_key_bounds {V} (enc : encoding V) e b :
  Cost.ticks (encode_c (DomVirtual.node_encoding enc) None) <= node_price e b /\
    key_bits (DomVirtual.node_encoding enc) None <= node_width b.
Proof.
  pose proof (sum_encoding_cost enc unit_encoding (inr tt)) as Hsum.
  rewrite sum_encoding_bits, unit_encoding_cost, unit_encoding_bits in Hsum.
  split.
  - change (1 + Cost.ticks (encode_c (sum_encoding enc unit_encoding) (inr tt)) <= node_price e b).
    unfold node_price, node_width.
    assert (Hscale : encode_k * 10 <= encode_k * (10 + 2 * b))
      by (apply N.mul_le_mono; lia).
    lia.
  - unfold key_bits at 1. rewrite DomVirtual.node_encoding_equation.
    change (key_bits (sum_encoding enc unit_encoding) (inr tt) <= node_width b).
    rewrite sum_encoding_bits, unit_encoding_bits. unfold node_width. lia.
Qed.

Local Lemma entries_length {V E} enc (g : Graph.t V E) :
  encoding_laws enc -> (length (DomVirtual.entries enc g) <= length (Graph.entries g))%nat.
Proof.
  intro Henc. destruct (DomVirtual.entries_exact enc g Henc) as [Hnodup Hmembers].
  apply NoDup_incl_length; [exact Hnodup|]. intros v Hv. now apply Hmembers in Hv.
Qed.

Local Lemma outgoing_length {V E} (g : Graph.t V E) v :
  In v (Graph.nodes g) -> (length (Graph.out g v) <= edge_count g)%nat.
Proof.
  unfold edge_count. induction (Graph.nodes g) as [|u rest IH]; intro Hv; [contradiction|].
  cbn [fold_right]. destruct Hv as [<-|Hv]; [lia|specialize (IH Hv); lia].
Qed.

Definition graph_bound {V E} (g : Graph.t V E) e b :=
  3 * N.of_nat (length (Graph.entries g)) * (1 + e + b) +
    N.of_nat (length (Graph.entries g)) + 2 * N.of_nat (length (Graph.nodes g)).

(** Tagged construction pays entry deduplication, synthetic-edge mapping and real-node copying. *)
Theorem graph_cost {V E} enc (g : Graph.t V E) e b ko ks kt :
  encoding_laws enc -> PreparedCost.prepare_bounds enc g e b ko ks kt ->
  Cost.ticks (DomVirtual.graph_c enc g) <= graph_bound g e b.
Proof.
  intros Henc Hcallbacks.
  pose proof (DomVirtual.entries_numeric_cost enc (Graph.entries g) FinSet.empty e b
    ltac:(intros v Hv; exact (proj1 (PreparedCost.entry_keys _ _ _ _ _ _ _ Hcallbacks v Hv)))
    ltac:(intros v Hv; exact
      (proj2 (PreparedCost.entry_keys _ _ _ _ _ _ _ Hcallbacks v Hv)))) as Hentries.
  pose proof (DomCostBasis.map_cost (fun v : V => Cost.ret (@inr E V v))
    (DomVirtual.entries enc g) 0 ltac:(intros; reflexivity)) as Hroots.
  pose proof (DomCostBasis.map_cost (fun v : V => Cost.ret (Some v))
    (Graph.nodes g) 0 ltac:(intros; reflexivity)) as Hnodes.
  pose proof (entries_length enc g Henc) as Hlength.
  unfold DomVirtual.graph_c.
  rewrite (Cost.ticks_bind (DomVirtual.entries_from_c enc FinSet.empty (Graph.entries g))).
  fold (DomVirtual.entries enc g).
  rewrite (Cost.ticks_bind (map_c (fun v => Cost.ret (@inr E V v)) (DomVirtual.entries enc g))).
  rewrite (Cost.ticks_bind (map_c (fun v => Cost.ret (Some v)) (Graph.nodes g))), value_map_c.
  rewrite (Cost.ticks_bind (app_c (map (@Some V) (Graph.nodes g)) [None])),
    Cost.ticks_ret, ticks_app_c, length_map.
  unfold graph_bound. nia.
Qed.

(** Every listed tagged node is either the fresh root or a listed original node. *)
Theorem virtual_node {V E} enc (g : Graph.t V E) x :
  In x (Graph.nodes (DomVirtual.graph enc g)) ->
  x = None \/ exists v, x = Some v /\ In v (Graph.nodes g).
Proof.
  rewrite DomVirtual.graph_equation. cbn [Graph.nodes]. rewrite in_app_iff.
  intros [Hreal|[Heq|Hfalse]]; [|now left|contradiction].
  right. apply in_map_iff in Hreal. destruct Hreal as [v [Heq Hv]]. exists v. auto.
Qed.

Definition outgoing_price {V E} (g : Graph.t V E) ko :=
  1 + ko + N.of_nat (edge_count g).

(** Virtual callback prices follow from original primitive callbacks and finite row lengths. *)
Theorem preparation_bounds {V E} (p : Prepared.t V E) e b ko ks kt :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  PreparedCost.prepare_bounds (DomVirtual.node_encoding (Prepared.node_enc p))
    (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p))
    (node_price e b) (node_width b) (outgoing_price (Prepared.graph p) ko) (1 + ks) (1 + kt).
Proof.
  intros Hready Hcallbacks.
  pose proof (Prepared.encoding_valid p (proj2 (proj2 Hready))) as Henc.
  constructor.
  - intros x Hx. apply virtual_node in Hx. destruct Hx as [->|[v [-> Hv]]].
    + apply root_key_bounds.
    + destruct (PreparedCost.node_keys _ _ _ _ _ _ _ Hcallbacks v Hv) as [Hprice Hwidth].
      now apply real_key_bounds.
  - intros x Hx. rewrite DomVirtual.graph_equation in Hx.
    change (In x [None]) in Hx. destruct Hx as [<-|Hfalse];
      [apply root_key_bounds|contradiction].
  - intros x Hx. apply virtual_node in Hx. destruct Hx as [->|[v [-> Hv]]].
    + change (0 <= outgoing_price (Prepared.graph p) ko). unfold outgoing_price. lia.
    + pose proof (PreparedCost.out_calls _ _ _ _ _ _ _ Hcallbacks v Hv) as Hout.
      pose proof (outgoing_length (Prepared.graph p) v Hv) as Hlength.
      pose proof (DomCostBasis.map_cost (fun edge : E => Cost.ret (@inl E V edge))
        (Graph.out (Prepared.graph p) v) 0 ltac:(intros; reflexivity)) as Hmap.
      change (1 + (Cost.ticks (Graph.out_c (Prepared.graph p) v) +
        Cost.ticks (map_c (fun edge : E => Cost.ret (@inl E V edge))
          (Graph.out (Prepared.graph p) v))) <= outgoing_price (Prepared.graph p) ko).
      unfold outgoing_price. nia.
  - intros edge Hedge. unfold Prepared.all_edges in Hedge. apply in_flat_map in Hedge.
    destruct Hedge as [source [Hsource Hedge]].
    apply virtual_node in Hsource. destruct Hsource as [->|[v [-> Hv]]].
    + rewrite DomVirtual.out_root in Hedge. apply in_map_iff in Hedge.
      destruct Hedge as [v [<- Hv]].
      apply (proj2 (DomVirtual.entries_exact _ _ Henc) v) in Hv.
      destruct (PreparedCost.entry_keys _ _ _ _ _ _ _ Hcallbacks v Hv) as [Hprice Hwidth].
      destruct (root_key_bounds (Prepared.node_enc p) e b) as [Hroot_price Hroot_width].
      destruct (real_key_bounds (Prepared.node_enc p) e b v Hprice Hwidth)
        as [Hreal_price Hreal_width].
      change (0 <= 1 + ks /\ 0 <= 1 + kt /\
        Cost.ticks (encode_c (DomVirtual.node_encoding (Prepared.node_enc p)) None) <=
          node_price e b /\
        key_bits (DomVirtual.node_encoding (Prepared.node_enc p)) None <= node_width b /\
        Cost.ticks (encode_c (DomVirtual.node_encoding (Prepared.node_enc p)) (Some v)) <=
          node_price e b /\
        key_bits (DomVirtual.node_encoding (Prepared.node_enc p)) (Some v) <= node_width b).
      split; [lia|]. split; [lia|]. auto.
    + rewrite DomVirtual.out_real in Hedge. apply in_map_iff in Hedge.
      destruct Hedge as [original [<- Hedge]].
      assert (Horiginal : In original (Prepared.all_edges (Prepared.graph p))).
      { unfold Prepared.all_edges. apply in_flat_map. now exists v. }
      destruct (PreparedCost.edge_calls _ _ _ _ _ _ _ Hcallbacks original Horiginal)
        as [Hsource_price [Htarget_price [Hsource_key [Hsource_bits [Htarget_key Htarget_bits]]]]].
      destruct (real_key_bounds (Prepared.node_enc p) e b (Graph.source (Prepared.graph p) original)
        Hsource_key Hsource_bits) as [Hsource_encoded Hsource_width].
      destruct (real_key_bounds (Prepared.node_enc p) e b (Graph.target (Prepared.graph p) original)
        Htarget_key Htarget_bits) as [Htarget_encoded Htarget_width].
      change (1 + Cost.ticks (Graph.source_c (Prepared.graph p) original) <= 1 + ks /\
        1 + Cost.ticks (Graph.target_c (Prepared.graph p) original) <= 1 + kt /\
        Cost.ticks (encode_c (DomVirtual.node_encoding (Prepared.node_enc p))
          (Some (Graph.source (Prepared.graph p) original))) <= node_price e b /\
        key_bits (DomVirtual.node_encoding (Prepared.node_enc p))
          (Some (Graph.source (Prepared.graph p) original)) <= node_width b /\
        Cost.ticks (encode_c (DomVirtual.node_encoding (Prepared.node_enc p))
          (Some (Graph.target (Prepared.graph p) original))) <= node_price e b /\
        key_bits (DomVirtual.node_encoding (Prepared.node_enc p))
          (Some (Graph.target (Prepared.graph p) original)) <= node_width b).
      split; [lia|]. split; [lia|]. auto.
Qed.

(** The credit budget keeps outgoing-list copying in its actual node factor. *)
Definition preparation_bound {V E} (p : Prepared.t V E) e b ko ks kt :=
  let g := DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p) in
  2 + N.of_nat (length (Graph.nodes g)) *
    (20 + InternCost.intern_k + 5 * node_price e b + 5 * node_width b +
      3 * PreparedCost.id_width g + 3 * outgoing_price (Prepared.graph p) ko) +
  N.of_nat (edge_count g) *
    (17 + 4 * node_price e b + 6 * node_width b + (1 + ks) + 2 * (1 + kt)) +
  N.of_nat (length (Graph.entries g)) * (3 + node_price e b + node_width b).

Definition virtual_bound {V E} (p : Prepared.t V E) e b ko ks kt :=
  graph_bound (Prepared.graph p) e b + preparation_bound p e b ko ks kt.

(** Complete virtual preparation is priced from original primitive callbacks and finite data. *)
Theorem virtual_cost {V E} (p : Prepared.t V E) e b ko ks kt :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  Cost.ticks (DomVirtual.virtual_c p) <= virtual_bound p e b ko ks kt.
Proof.
  intros Hready Hcallbacks.
  pose proof (DomVirtual.virtual_ready p Hready) as Hvirtual.
  pose proof (nodes_nodup (proj1 Hvirtual)) as Hnodes.
  rewrite DomVirtual.prepared_graph in Hnodes.
  pose proof (PreparedCost.prepare_credit_cost (DomVirtual.node_encoding (Prepared.node_enc p))
    (DomVirtual.node_encoding_laws _ (Prepared.encoding_valid p (proj2 (proj2 Hready))))
    (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p))
    (node_price e b) (node_width b) (outgoing_price (Prepared.graph p) ko) (1 + ks) (1 + kt)
    Hnodes (preparation_bounds p e b ko ks kt Hready Hcallbacks)) as Hprepare.
  unfold DomVirtual.virtual_c.
  rewrite (Cost.ticks_bind (DomVirtual.graph_c (Prepared.node_enc p) (Prepared.graph p))).
  fold (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)).
  apply N.add_le_mono.
  - exact (graph_cost _ _ e b ko ks kt
      (Prepared.encoding_valid p (proj2 (proj2 Hready))) Hcallbacks).
  - exact Hprepare.
Qed.

End DomVirtualCost.
