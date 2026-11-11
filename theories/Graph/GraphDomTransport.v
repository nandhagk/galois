(** * The actual discovery-rank inverse map

    The prologue's inverse map relates only discovered real vertices to original prepared IDs.
    For example, the virtual root has a discovery rank and has no real-ID inverse binding.
    Builds on: GraphDomSemi, GraphDomRankMap and the prepared-name bijections. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSemi
  GraphDomVirtual GraphDomErase GraphDomRankMap.

Module DomTransport.

(** The inverse-map representation is canonical independently of readiness. *)
Theorem inverse_wf {V E} (p : Prepared.t V E) :
  Map.wf positive_encoding (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))).
Proof.
  rewrite DomSemi.ranked_equation, DomSemi.layout_real_ids.
  apply DomRankMap.fold_wf. apply Map.wf_empty.
Qed.

(** Every discovered target has exactly its own converted predecessor row at its discovery rank. *)
Theorem predecessor_row {V E} (p : Prepared.t V E) v rank :
  Prepared.ready p ->
  In v (Search.preorder (DomSemi.search (DomSemi.compute p))) ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  Map.get positive_encoding rank (DomSemi.predecessors (DomSemi.ranked (DomSemi.compute p))) =
    Some (Cost.value (DomSemi.ranked_predecessors_c
      (DomSemi.prepared (DomSemi.compute p)) (DomSemi.search (DomSemi.compute p)) v)).
Proof.
  intros Hready Hv Hrank. rewrite DomSemi.ranked_equation, DomSemi.layout_predecessors.
  apply (DomRankMap.fold_complete
    (fun v => Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))))
    (fun v => Some (Cost.value (DomSemi.ranked_predecessors_c
      (DomSemi.prepared (DomSemi.compute p)) (DomSemi.search (DomSemi.compute p)) v)))
    v rank _).
  - intros a b k Ha Hb. exact (DomSemi.discovery_rank_injective p a b k Hready Ha Hb).
  - exact Hrank.
  - reflexivity.
  - exact Hv.
  - apply Map.wf_empty.
Qed.

Local Lemma predecessor_arc {V E} (q : Prepared.t V E) u e v :
  Prepared.ready q ->
  (In (e, u) (Prepared.pred_edges q v) <-> Prepared.arc q u e v).
Proof.
  intros Hready. pose proof Hready as [Hwf [Hout Hq]].
  rewrite <- (Prepared.adjacency_dual q u e v Hready). split.
  - intro Hin. destruct (Prepared.name_of q u) as [a|] eqn:Hname.
    + pose proof (Prepared.id_of_name_of q u a Hq Hname) as Hi.
      apply (Prepared.succ_spec q a u e v Hq Hi) in Hin. destruct Hin as [He Hj].
      exists a, (Graph.target (Prepared.graph q) e). split.
      * apply (Prepared.ids_domain q Hq). now exists u.
      * split; [exact Hi|]. split; [exact Hj|].
        split; [exact (out_source Hwf a e He)|]. split; [reflexivity|exact He].
    + rewrite (Prepared.succ_domain q Hq u Hname) in Hin. contradiction.
  - intros [a [b [Ha [Hi [Hj [Hsource [Htarget He]]]]]]].
    apply (Prepared.succ_spec q a u e v Hq Hi). split; [exact He|].
    now rewrite Htarget.
Qed.

(** Ranked labelled arcs correspond exactly to actual prepared arcs with a discovered source. *)
Theorem ranked_arc_spec {V E} (p : Prepared.t V E) target rank e source_rank :
  Prepared.ready p ->
  Map.get positive_encoding target
    (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  (DomSemi.ranked_arc (DomSemi.compute p) source_rank e rank <->
    exists source, Prepared.arc (DomSemi.prepared (DomSemi.compute p)) source e target /\
      Map.get positive_encoding source
        (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some source_rank).
Proof.
  intros Hready Hrank.
  pose proof (DomSemi.search_exact p Hready) as Hsearch.
  assert (Hvisited : In target (Search.preorder (DomSemi.search (DomSemi.compute p)))).
  { apply (Search.pre_num_index _ _ _ _ Hsearch) in Hrank.
    now apply nth_error_In in Hrank. }
  pose proof (predecessor_row p target rank Hready Hvisited Hrank) as Hrow.
  unfold DomSemi.ranked_arc. rewrite Index.find_equation, Hrow.
  rewrite DomSemi.ranked_predecessors_spec.
  split; intros [source [Harc Hsource]]; exists source; split; [|exact Hsource| |exact Hsource].
  - apply predecessor_arc.
    + rewrite DomSemi.prepared_equation. now apply DomVirtual.virtual_ready.
    + exact Harc.
  - apply predecessor_arc.
    + rewrite DomSemi.prepared_equation. now apply DomVirtual.virtual_ready.
    + exact Harc.
Qed.

(** Every inverse binding records an actual discovered virtual ID and both of its conversions. *)
Theorem inverse_sound {V E} (p : Prepared.t V E) rank original :
  Map.get positive_encoding rank (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) =
    Some original ->
  exists v, In v (Search.preorder (DomSemi.search (DomSemi.compute p))) /\
    Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
      Some rank /\
    DomErase.real_id p (DomSemi.prepared (DomSemi.compute p)) v = Some original.
Proof.
  rewrite DomSemi.ranked_equation, DomSemi.layout_real_ids.
  intro Hget.
  pose proof (DomRankMap.fold_sound
    (fun v => Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))))
    (DomErase.real_id p (DomSemi.prepared (DomSemi.compute p)))
    (Search.preorder (DomSemi.search (DomSemi.compute p)))
    Map.empty (Map.wf_empty positive_encoding) rank original Hget) as Hsource.
  destruct Hsource as [Hempty|Hsource]; [rewrite Map.get_empty in Hempty; discriminate|].
  exact Hsource.
Qed.

(** Every discovered real vertex has its exact inverse binding on the readiness domain. *)
Theorem inverse_complete {V E} (p : Prepared.t V E) v rank original :
  Prepared.ready p ->
  In v (Search.preorder (DomSemi.search (DomSemi.compute p))) ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank ->
  DomErase.real_id p (DomSemi.prepared (DomSemi.compute p)) v = Some original ->
  Map.get positive_encoding rank (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) =
    Some original.
Proof.
  intros Hready Hin Hrank Hreal.
  rewrite DomSemi.ranked_equation, DomSemi.layout_real_ids.
  apply (DomRankMap.fold_complete
    (fun v => Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))))
    (DomErase.real_id p (DomSemi.prepared (DomSemi.compute p))) v rank original).
  - intros a b k Ha Hb. exact (DomSemi.discovery_rank_injective p a b k Hready Ha Hb).
  - exact Hrank.
  - exact Hreal.
  - exact Hin.
  - apply Map.wf_empty.
Qed.

(** On ready graphs inverse lookup is exactly the discovered real-node conversion relation. *)
Theorem inverse_spec {V E} (p : Prepared.t V E) rank original :
  Prepared.ready p ->
  (Map.get positive_encoding rank (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) =
    Some original <->
  exists v, In v (Search.preorder (DomSemi.search (DomSemi.compute p))) /\
    Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
      Some rank /\
    DomErase.real_id p (DomSemi.prepared (DomSemi.compute p)) v = Some original).
Proof.
  intro Hready. split; [apply inverse_sound|].
  intros [v [Hin [Hrank Hreal]]]. exact (inverse_complete p v rank original Hready Hin Hrank Hreal).
Qed.

(** Distinct discovered ranks cannot name the same original real vertex. *)
Theorem inverse_injective {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  DomErase.injective
    (fun rank => Map.get positive_encoding rank
      (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p)))).
Proof.
  intros Hready i j original Hi Hj.
  apply inverse_sound in Hi, Hj.
  destruct Hi as [a [Ha [Hrank_a Hreal_a]]].
  destruct Hj as [b [Hb [Hrank_b Hreal_b]]].
  pose proof (proj2 (proj2 Hready)) as Hp.
  pose proof (proj2 (proj2 (DomVirtual.virtual_ready p Hready))) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  assert (a = b).
  { exact (DomErase.real_id_injective p (DomSemi.prepared (DomSemi.compute p))
      Hp Hq a b original Hreal_a Hreal_b). }
  subst b. congruence.
Qed.

(** Shared-prologue erasure preserves exactly each represented ranked parent with real endpoints. *)
Theorem erase_get {V E} (p : Prepared.t V E) m v u :
  Prepared.ready p -> Map.wf positive_encoding m ->
  (Map.get positive_encoding v (DomSemi.erase (DomSemi.compute p) m) = Some u <->
    exists i j, Map.get positive_encoding i m = Some j /\
      Map.get positive_encoding i
        (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) = Some v /\
      Map.get positive_encoding j
        (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) = Some u).
Proof.
  intros Hready Hmap. apply DomErase.with_get; [|exact Hmap].
  exact (inverse_injective p Hready).
Qed.

End DomTransport.
