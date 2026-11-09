(** * Primitive discovery-rank layout costs

    Actual search bounds the raw IDs and ranks used by parent and predecessor conversion.
    For example, every retained incoming source pays its actual discovery-map query.
    Builds on: GraphDomVirtualCost, Search specifications and public preparation/map contracts. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex BaseIntern BaseInternCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphSearchSpec
  GraphDomVirtual GraphDomSemi GraphDomErase GraphDomVirtualCost GraphDomSize GraphDomCostBasis
  GraphReach.
Import Cost.Notations.

Module DomLayoutCost.
Local Open Scope N_scope.

Local Lemma scoped_endpoint {A B} (q : Prepared.t A B) scope u es v :
  Search.scoped_path q scope u es v -> Prepared.valid_id q v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

(** Valid predecessors have finite source support and at most the actual graph edge count. *)
Theorem predecessor_resources {V E} (q : Prepared.t V E) v :
  Prepared.ready q ->
  Forall (fun eu => Prepared.valid_id q (snd eu)) (Prepared.pred_edges q v) /\
    (length (Prepared.pred_edges q v) <= edge_count (Prepared.graph q))%nat.
Proof.
  intros Hready. pose proof (proj2 (proj2 Hready)) as Hq.
  destruct (Prepared.name_of q v) as [name|] eqn:Hname.
  - pose proof (Prepared.id_of_name_of q v name Hq Hname) as Hid.
    assert (Hedges : forall e u, In (e, u) (Prepared.pred_edges q v) ->
      In e (Prepared.all_edges (Prepared.graph q)) /\ Prepared.valid_id q u).
    { intros e u Heu. apply (Prepared.pred_agrees q Hq name v e u Hid) in Heu.
      destruct Heu as [Hsource [Hedge [Htarget Huid]]]. split.
      - unfold Prepared.all_edges. apply in_flat_map.
        exists (Graph.source (Prepared.graph q) e). auto.
      - exists (Graph.source (Prepared.graph q) e). auto. }
    split.
    + apply Forall_forall. intros [e u] Heu. exact (proj2 (Hedges e u Heu)).
    + rewrite <- (length_map fst (Prepared.pred_edges q v)), <- DomSize.all_edges_length.
      apply NoDup_incl_length; [exact (Prepared.pred_nodup q Hq v)|].
      intros e He. apply in_map_iff in He. destruct He as [[label u] [Heq Heu]].
      cbn [fst] in Heq. subst label. exact (proj1 (Hedges e u Heu)).
  - rewrite (Prepared.pred_domain q Hq v Hname). split; [constructor|cbn; lia].
Qed.

Section Layout.
Context {V E : Type} (p : Prepared.t V E).
Local Abbreviation q := (DomVirtual.virtual p).
Local Abbreviation g := (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)).
Local Abbreviation result := (DomSemi.search (DomSemi.compute p)).

Definition raw_width := PreparedCost.id_width g.
Definition rank_limit := Pos.of_succ_nat (length (Search.preorder result)).
Definition rank_width := key_bits positive_encoding rank_limit.

Local Lemma search_exact :
  Prepared.ready p -> Search.exact q Reach.unrestricted (Prepared.entry_ids q) result.
Proof.
  intro Hready. pose proof (DomSemi.search_exact p Hready) as Hsearch.
  now rewrite DomSemi.prepared_equation in Hsearch.
Qed.

(** Actual virtual bindings fit the width of the once-prepared virtual dictionary. *)
Theorem virtual_id_width name i :
  Prepared.ready p ->
  Prepared.id_of q name = Some i -> key_bits positive_encoding i <= raw_width.
Proof.
  intros Hready Hi. rewrite Prepared.id_of_equation in Hi.
  assert (Hencoding : Prepared.node_enc q = DomVirtual.node_encoding (Prepared.node_enc p)).
  { rewrite DomVirtual.virtual_equation, Prepared.prepare_equation. reflexivity. }
  rewrite Hencoding, DomVirtual.virtual_equation, Prepared.prepare_names in Hi.
  exact (PreparedCost.table_id_width _ (DomVirtual.node_encoding_laws _
    (Prepared.encoding_valid p (proj2 (proj2 Hready)))) g name i Hi).
Qed.

(** Every valid raw virtual ID satisfies the same input-derived dictionary-width bound. *)
Theorem valid_width i :
  Prepared.ready p -> Prepared.valid_id q i -> key_bits positive_encoding i <= raw_width.
Proof.
  intros Hready [name [Hnode Hid]]. exact (virtual_id_width name i Hready Hid).
Qed.

Local Lemma discovered_valid v :
  Prepared.ready p -> In v (Search.preorder result) -> Prepared.valid_id q v.
Proof.
  intros Hready Hv. apply (Search.pre_complete _ _ _ _ (search_exact Hready)) in Hv.
  destruct Hv as [root [es [Hroot Hpath]]]. exact (scoped_endpoint q _ _ _ _ Hpath).
Qed.

(** Every successfully recorded discovery rank fits its actual finite discovery frontier. *)
Theorem recorded_rank_width v rank :
  Prepared.ready p -> Map.get positive_encoding v (Search.pre_num result) = Some rank ->
  key_bits positive_encoding rank <= rank_width.
Proof.
  intros Hready Hrank.
  apply (Search.pre_num_index _ _ _ _ (search_exact Hready)) in Hrank.
  assert (Hindex : (Nat.pred (Pos.to_nat rank) < length (Search.preorder result))%nat).
  { apply nth_error_Some. rewrite Hrank. discriminate. }
  unfold rank_width. apply InternCost.bits_monotone, Pos2Nat.inj_le.
  change (Pos.to_nat rank <=
    Pos.to_nat (Pos.of_succ_nat (length (Search.preorder result))))%nat.
  rewrite SuccNat2Pos.id_succ.
  pose proof (Pos2Nat.is_pos rank). lia.
Qed.

Definition predecessors_bound :=
  2 + raw_width + N.of_nat (edge_count g) * (3 + raw_width).

(** Incoming conversion retains every occurrence, source query and explicit missing-rank filter. *)
Theorem ranked_predecessors_cost v :
  Prepared.ready p -> Prepared.valid_id q v ->
  Cost.ticks (DomSemi.ranked_predecessors_c q result v) <= predecessors_bound.
Proof.
  intros Hready Hv.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  destruct (predecessor_resources q v Hq) as [Hsources Hlength].
  rewrite DomVirtual.prepared_graph in Hlength.
  pose proof (DomCostBasis.filter_map_cost (fun eu : (E + V) * positive =>
    let '(e, u) := eu in
    let* rank := Map.get_c positive_encoding u (Search.pre_num result) in
    Cost.ret (option_map (fun rank => (e, rank)) rank))
    (Prepared.pred_edges q v) (2 + raw_width)
    ltac:(intros [e u] Heu; cbn beta iota;
      change (Cost.ticks (Map.get_c positive_encoding u (Search.pre_num result)) + 0 <=
        2 + raw_width);
      rewrite DomCostBasis.get_cost;
      pose proof (proj1 (Forall_forall _ _) Hsources (e, u) Heu) as Hu;
      pose proof (valid_width u Hready Hu); lia)) as Hfilter.
  unfold DomSemi.ranked_predecessors_c.
  rewrite (Cost.ticks_bind (Prepared.pred_edges_c q v)).
  fold (Prepared.pred_edges q v).
  assert (Hlookup : Cost.ticks (Prepared.pred_edges_c q v) <= 2 + raw_width).
  { unfold Prepared.pred_edges_c. rewrite Index.find_cost, DomCostBasis.get_cost.
    pose proof (valid_width v Hready Hv). lia. }
  unfold predecessors_bound.
  assert (Hscale : N.of_nat (length (Prepared.pred_edges q v)) * (1 + (2 + raw_width)) <=
    N.of_nat (edge_count g) * (3 + raw_width)) by (apply N.mul_le_mono; lia).
  lia.
Qed.

Definition real_id_bound e b := 3 + raw_width + e + b.

(** Real-name inversion pays its virtual inverse lookup and original primitive encoder. *)
Theorem real_id_cost e b ko ks kt v :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  Prepared.valid_id q v ->
  Cost.ticks (DomErase.real_id_c p q v) <= real_id_bound e b.
Proof.
  intros Hready Hcallbacks Hv.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  assert (Hlookup : Cost.ticks (Prepared.name_of_c q v) <= 2 + raw_width).
  { unfold Prepared.name_of_c. rewrite Intern.key_of_cost, DomCostBasis.get_cost.
    pose proof (valid_width v Hready Hv). lia. }
  unfold DomErase.real_id_c. rewrite (Cost.ticks_bind (Prepared.name_of_c q v)).
  fold (Prepared.name_of q v).
  destruct (Prepared.name_of q v) as [[name|]|] eqn:Hname.
  - assert (Hnode : In (Some name) (Graph.nodes (Prepared.graph q))).
    { apply (Prepared.ids_domain q (proj2 (proj2 Hq))).
      exists v. exact (Prepared.id_of_name_of q v (Some name) (proj2 (proj2 Hq)) Hname). }
    rewrite DomVirtual.prepared_graph in Hnode.
    apply DomVirtualCost.virtual_node in Hnode.
    destruct Hnode as [Hfalse|[original [Heq Horiginal]]]; [discriminate|].
    injection Heq as <-.
    destruct (PreparedCost.node_keys _ _ _ _ _ _ _ Hcallbacks name Horiginal)
      as [Hprice Hbits].
    unfold Prepared.id_of_c. rewrite Intern.find_cost, Map.get_cost.
    fold (key_bits (Prepared.node_enc p) name). unfold real_id_bound. lia.
  - rewrite Cost.ticks_ret. unfold real_id_bound. lia.
  - rewrite Cost.ticks_ret. unfold real_id_bound. lia.
Qed.

Definition step_bound e b :=
  20 + 6 * raw_width + 4 * rank_width + e + b +
    N.of_nat (edge_count g) * (3 + raw_width).

(** Actual layout steps price parent conversion, incoming occurrences and real-name inversion. *)
Theorem step_cost e b ko ks kt st v :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  In v (Search.preorder result) ->
  Cost.ticks (DomSemi.layout_step_c p q result st v) <= step_bound e b.
Proof.
  intros Hready Hcallbacks Hv.
  pose proof (discovered_valid v Hready Hv) as Hvalid.
  pose proof (valid_width v Hready Hvalid) as Hv_width.
  pose proof (ranked_predecessors_cost v Hready Hvalid) as Hincoming.
  pose proof (real_id_cost e b ko ks kt v Hready Hcallbacks Hvalid) as Hreal.
  unfold DomSemi.layout_step_c.
  rewrite (Cost.ticks_bind (Map.get_c positive_encoding v (Search.pre_num result))).
  fold (Map.get positive_encoding v (Search.pre_num result)).
  destruct (Map.get positive_encoding v (Search.pre_num result)) as [rank|] eqn:Hrank.
  - pose proof (recorded_rank_width v rank Hready Hrank) as Hrank_width.
    assert (Hfinish : forall (parents : Map.t positive positive)
      (predecessors : Map.t positive (list ((E + V) * positive))),
      Cost.ticks
        (let* real := DomErase.real_id_c p q v in
         let* real_ids :=
           match real with
           | None => Cost.ret (DomSemi.real_ids st)
           | Some original => Map.set_c positive_encoding rank original (DomSemi.real_ids st)
           end in
         Cost.ret
           (DomSemi.Layout (rank :: DomSemi.reverse_order st) parents predecessors real_ids)) <=
        real_id_bound e b + (2 + rank_width)).
    { intros parents predecessors.
      rewrite (Cost.ticks_bind (DomErase.real_id_c p q v)).
      apply N.add_le_mono; [exact Hreal|].
      destruct (Cost.value (DomErase.real_id_c p q v)) as [original|].
      - rewrite (Cost.ticks_bind (Map.set_c positive_encoding rank original (DomSemi.real_ids st))),
          Cost.ticks_ret, DomCostBasis.set_cost. lia.
      - rewrite Cost.bind_ret_l, Cost.ticks_ret. lia. }
    assert (Hparents : forall (predecessors : Map.t positive (list ((E + V) * positive))),
      Cost.ticks
        (let* via := Map.get_c positive_encoding v (Search.parent_edge result) in
         let* parents :=
           match via with
           | None => Cost.ret (DomSemi.parents st)
           | Some (_, u) =>
             let* parent_rank := Map.get_c positive_encoding u (Search.pre_num result) in
             match parent_rank with
             | None => Cost.ret (DomSemi.parents st)
             | Some parent_rank => Map.set_c positive_encoding rank parent_rank (DomSemi.parents st)
             end
           end in
         let* real := DomErase.real_id_c p q v in
         let* real_ids :=
           match real with
           | None => Cost.ret (DomSemi.real_ids st)
           | Some original => Map.set_c positive_encoding rank original (DomSemi.real_ids st)
           end in
         Cost.ret
           (DomSemi.Layout (rank :: DomSemi.reverse_order st) parents predecessors real_ids)) <=
        (2 + raw_width) + ((4 + raw_width + rank_width) +
          (real_id_bound e b + (2 + rank_width)))).
    { intro predecessors.
      rewrite (Cost.ticks_bind (Map.get_c positive_encoding v (Search.parent_edge result))).
      fold (Map.get positive_encoding v (Search.parent_edge result)).
      apply N.add_le_mono.
      - rewrite DomCostBasis.get_cost. lia.
      - destruct (Map.get positive_encoding v (Search.parent_edge result)) as [[edge u]|] eqn:Hvia.
        + pose proof (proj1 (proj2 (Search.parent_edge_valid _ _ _ _ (search_exact Hready)
            v edge u Hvia))) as Hu.
          pose proof (valid_width u Hready (discovered_valid u Hready Hu)) as Hu_width.
          apply DomCostBasis.bind_cost; [|intro parents; apply Hfinish].
          rewrite (Cost.ticks_bind (Map.get_c positive_encoding u (Search.pre_num result))).
          fold (Map.get positive_encoding u (Search.pre_num result)).
          destruct (Map.get positive_encoding u (Search.pre_num result));
            rewrite ?DomCostBasis.set_cost, ?Cost.ticks_ret, DomCostBasis.get_cost; lia.
        + rewrite Cost.bind_ret_l. eapply N.le_trans; [apply Hfinish|lia]. }
    eapply N.le_trans with (m := (2 + raw_width) +
      (predecessors_bound + ((2 + rank_width) +
        ((2 + raw_width) + ((4 + raw_width + rank_width) +
          (real_id_bound e b + (2 + rank_width))))))).
    + apply N.add_le_mono.
      * rewrite DomCostBasis.get_cost. lia.
      * apply DomCostBasis.bind_cost; [exact Hincoming|].
        intro incoming. apply DomCostBasis.bind_cost.
        -- rewrite DomCostBasis.set_cost. lia.
        -- intro predecessors. apply Hparents.
    + unfold step_bound, predecessors_bound, real_id_bound. lia.
  - rewrite Cost.ticks_ret, DomCostBasis.get_cost. unfold step_bound. lia.
Qed.

Definition layout_bound e b :=
  N.of_nat (length (Search.preorder result)) * (1 + step_bound e b).

(** The complete actual rank-layout fold has a primitive budget uniform in all intermediate maps. *)
Theorem layout_cost e b ko ks kt :
  Prepared.ready p ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) e b ko ks kt ->
  Cost.ticks (DomSemi.layout_c p q result) <= layout_bound e b.
Proof.
  intros Hready Hcallbacks. unfold DomSemi.layout_c.
  apply DomCostBasis.fold_left_cost.
  intros st v Hv. exact (step_cost e b ko ks kt st v Hready Hcallbacks Hv).
Qed.

End Layout.
End DomLayoutCost.
