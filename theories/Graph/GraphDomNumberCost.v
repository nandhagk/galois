(** * Complete actual parent-forest annotation costs

    Forest construction, preparation, one indexed search and both inverse annotations are charged.
    For example, a parentless live node still pays preparation and root-search work.
    Builds on: GraphDomNumber and public grouping, preparation and search cost contracts. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Ring.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIndex BaseIndexCost BaseIntern
  BaseInternCost BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphVisitor
  GraphSearchSpec GraphSearch GraphSearchCost GraphDomNumber GraphDomCostBasis GraphReach.
Import Cost.Notations.

Module DomNumberCost.
Local Open Scope N_scope.

(** Finite input storage/domain duties require neither acyclicity nor output numbering. *)
Record bounds live (parents : Map.t positive positive) (c : nat) wo : Prop := {
  live_nodup : NoDup live;
  parent_wf : Map.wf positive_encoding parents;
  parent_domain : forall v u, Map.get positive_encoding v parents = Some u ->
    In v live /\ In u live;
  live_length : (length live <= c)%nat;
  live_width : forall v, In v live -> key_bits positive_encoding v <= wo
}.
Arguments live_nodup {live parents c wo} _.
Arguments parent_wf {live parents c wo} _.
Arguments parent_domain {live parents c wo} _ _ _ _.
Arguments live_length {live parents c wo} _.
Arguments live_width {live parents c wo} _ _ _.

Definition rank_width c := N.pos (Pos.size (Pos.of_succ_nat c)).
Definition fuel_width c := N.pos (Pos.size (Pos.of_succ_nat (2 * c + c * c + 1))).

Section Number.
Context (live : list positive) (parents : Map.t positive positive).
Local Abbreviation forest := (DomNumber.forest live parents).
Local Abbreviation q := (DomNumber.prepared live parents).

(** Candidate cardinality follows from actual canonical parent keys and the finite input domain. *)
Theorem parent_size c wo :
  bounds live parents c wo -> (Map.size parents <= c)%nat.
Proof.
  intro Hb.
  eapply Nat.le_trans;
    [apply (Map.size_support_bound positive_encoding positive_encoding_laws live)|].
  - exact (parent_wf Hb).
  - intros v u Hget. exact (proj1 (parent_domain Hb v u Hget)).
  - exact (live_length Hb).
Qed.

Local Lemma stored_width c wo vu :
  bounds live parents c wo -> In vu (Map.elements parents) ->
  key_bits positive_encoding (fst vu) <= wo /\ key_bits positive_encoding (snd vu) <= wo.
Proof.
  intros Hb Hvu. destruct vu as [v u].
  apply (Map.elements_spec positive_encoding positive_encoding_laws
    v u parents (parent_wf Hb)) in Hvu.
  destruct (parent_domain Hb v u Hvu) as [Hv Hu].
  split; [exact (live_width Hb v Hv)|exact (live_width Hb u Hu)].
Qed.

Definition forest_bound c wo :=
  TrieCost.trie_k * (1 + N.of_nat c * wo) + 1 + N.of_nat c * (11 + 5 * wo).

(** Forest construction retains the parent scan, stable grouping and parentless-root filtering. *)
Theorem forest_cost c wo :
  bounds live parents c wo ->
  Cost.ticks (DomNumber.forest_c live parents) <= forest_bound c wo.
Proof.
  intro Hb.
  pose proof (MapCost.elements_numeric_cost positive_encoding parents wo (parent_wf Hb)
    ltac:(intros v u Hget; exact (live_width Hb v (proj1 (parent_domain Hb v u Hget))))) as Hscan.
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold positive_encoding positive_encoding_laws
    (fun vu : positive * positive => Cost.ret (snd vu)) (Map.elements parents) 1 wo 0
    ltac:(intros vu Hvu; split; [reflexivity|];
      split; [rewrite positive_encoding_cost; reflexivity|
        exact (proj2 (stored_width c wo vu Hb Hvu))]))
    as Hgroup.
  pose proof (DomCostBasis.filter_cost (fun v =>
    Cost.map negb (Map.mem_c positive_encoding v parents)) live (2 + wo)
    ltac:(intros v Hv; cbn beta; rewrite Cost.ticks_map, Map.mem_cost, positive_encoding_cost;
      fold (key_bits positive_encoding v);
      pose proof (live_width Hb v Hv); lia)) as Hroots.
  pose proof (parent_size c wo Hb) as Hsize.
  pose proof (live_length Hb) as Hlength.
  unfold DomNumber.forest_c.
  rewrite (Cost.ticks_bind (Map.elements_c parents)). fold (Map.elements parents).
  rewrite (Cost.ticks_bind (Index.group_by_c positive_encoding
    (fun vu : positive * positive => Cost.ret (snd vu)) (Map.elements parents))).
  rewrite (Cost.ticks_bind (filter_c (fun v =>
    Cost.map negb (Map.mem_c positive_encoding v parents)) live)), Cost.ticks_ret.
  rewrite <- Map.size_elements in Hgroup.
  assert (Hscan_scale : TrieCost.trie_k * (1 + N.of_nat (Map.size parents) * wo) <=
    TrieCost.trie_k * (1 + N.of_nat c * wo)).
  { apply N.mul_le_mono; [reflexivity|]. apply N.add_le_mono; [reflexivity|].
    apply N.mul_le_mono; lia. }
  assert (Hgroup_scale : N.of_nat (Map.size parents) * (6 + 0 + 2 * 1 + 4 * wo) <=
    N.of_nat c * (8 + 4 * wo)) by (apply N.mul_le_mono; lia).
  assert (Hroots_scale : N.of_nat (length live) * (1 + (2 + wo)) <=
    N.of_nat c * (3 + wo)) by (apply N.mul_le_mono; lia).
  unfold forest_bound. lia.
Qed.

Local Lemma child_row_length u c wo :
  bounds live parents c wo ->
  (length (Index.find positive_encoding u
    (Index.group_by positive_encoding (@snd positive positive) (Map.elements parents))) <= c)%nat.
Proof.
  intro Hb. rewrite Index.find_group_by.
  eapply Nat.le_trans; [apply filter_length_le|]. rewrite <- Map.size_elements.
  exact (parent_size c wo Hb).
Qed.

(** Forest callbacks price their actual grouped row mapping and input-parent lookup. *)
Theorem callback_bounds c wo :
  bounds live parents c wo ->
  PreparedCost.prepare_bounds positive_encoding forest 1 wo
    (2 + wo + N.of_nat c) (2 + wo) 0.
Proof.
  intro Hb. constructor.
  - intros v Hv. split; [rewrite positive_encoding_cost; reflexivity|].
    apply (live_width Hb v). exact Hv.
  - intros v Hv. split; [rewrite positive_encoding_cost; reflexivity|].
    apply (live_width Hb v). now apply DomNumber.forest_roots in Hv as [Hv Hparent].
  - intros u Hu.
    pose proof (child_row_length u c wo Hb) as Hlength.
    pose proof (DomCostBasis.map_cost (fun vu : positive * positive => Cost.ret (fst vu))
      (Index.find positive_encoding u
        (Index.group_by positive_encoding (@snd positive positive) (Map.elements parents))) 0
      ltac:(intros; reflexivity)) as Hmap.
    rewrite DomNumber.forest_equation.
    change (Cost.ticks (DomNumber.children_c
      (Index.group_by positive_encoding (@snd positive positive) (Map.elements parents)) u) <=
      2 + wo + N.of_nat c).
    unfold DomNumber.children_c.
    rewrite (Cost.ticks_bind (Index.find_c positive_encoding u
      (Index.group_by positive_encoding (@snd positive positive) (Map.elements parents)))).
    fold (Index.find positive_encoding u
      (Index.group_by positive_encoding (@snd positive positive) (Map.elements parents))).
    rewrite Index.find_cost, DomCostBasis.get_cost.
    pose proof (live_width Hb u Hu). lia.
  - intros edge Hedge. unfold Prepared.all_edges in Hedge. apply in_flat_map in Hedge.
    destruct Hedge as [u [Hu Hedge]].
    pose proof (DomNumber.forest_wf live parents (live_nodup Hb)
      (parent_wf Hb) (parent_domain Hb)) as Hwf.
    pose proof (out_source Hwf u edge Hedge) as Hsource.
    pose proof (out_target_in Hwf u edge Hu Hedge) as Htarget.
    assert (Hedge_live : In edge live).
    { rewrite DomNumber.forest_target in Htarget. exact Htarget. }
    change (Cost.ticks (DomNumber.source_c parents edge) <= 2 + wo /\ 0 <= 0 /\
      Cost.ticks (encode_c positive_encoding (Graph.source forest edge)) <= 1 /\
      key_bits positive_encoding (Graph.source forest edge) <= wo /\
      Cost.ticks (encode_c positive_encoding (Graph.target forest edge)) <= 1 /\
      key_bits positive_encoding (Graph.target forest edge) <= wo).
    rewrite !positive_encoding_cost.
    split.
    + unfold DomNumber.source_c.
      rewrite (Cost.ticks_bind (Map.get_c positive_encoding edge parents)), Cost.ticks_ret,
        DomCostBasis.get_cost. pose proof (live_width Hb edge Hedge_live). lia.
    + split; [reflexivity|]. split; [reflexivity|]. split.
      * rewrite Hsource. exact (live_width Hb u Hu).
      * split; [reflexivity|]. rewrite DomNumber.forest_target.
        exact (live_width Hb edge Hedge_live).
Qed.

Local Lemma edge_inventory c wo :
  bounds live parents c wo -> N.of_nat (edge_count forest) <= N.of_nat c * N.of_nat c.
Proof.
  intro Hb.
  assert (Hrows : forall nodes, incl nodes live ->
    N.of_nat (fold_right (fun u rest => length (Graph.out forest u) + rest)%nat 0%nat nodes) <=
      N.of_nat (length nodes) * N.of_nat c).
  { intro nodes. induction nodes as [|u rest IH]; intro Hincl; [reflexivity|].
    cbn [fold_right length]. rewrite Nat2N.inj_add, Nat2N.inj_succ.
    specialize (IH ltac:(intros v Hv; apply Hincl; now right)).
    assert (Hlength : (length (Graph.out forest u) <= c)%nat).
    { rewrite DomNumber.forest_out, length_map.
      eapply Nat.le_trans; [apply filter_length_le|].
      rewrite <- Map.size_elements. exact (parent_size c wo Hb). }
    nia. }
  unfold edge_count. change (N.of_nat
    (fold_right (fun u rest => length (Graph.out forest u) + rest)%nat 0%nat live) <=
      N.of_nat c * N.of_nat c).
  eapply N.le_trans; [apply Hrows; intros v Hv; exact Hv|].
  apply N.mul_le_mono; [pose proof (live_length Hb); lia|reflexivity].
Qed.

Local Lemma dense_width c wo :
  bounds live parents c wo -> PreparedCost.id_width forest <= rank_width c.
Proof.
  intro Hb. unfold PreparedCost.id_width, rank_width.
  apply InternCost.bits_monotone, Pos2Nat.inj_le.
  rewrite !SuccNat2Pos.id_succ. change (S (length live) <= S c)%nat.
  pose proof (live_length Hb). lia.
Qed.

Definition preparation_bound c wo :=
  2 + N.of_nat c * (31 + InternCost.intern_k + 8 * wo + 3 * rank_width c + 3 * N.of_nat c) +
    (N.of_nat c * N.of_nat c) * (23 + 7 * wo) + N.of_nat c * (4 + wo).

(** Forest preparation includes its callbacks, node/edge inventory and dense width. *)
Theorem preparation_cost c wo :
  bounds live parents c wo ->
  Cost.ticks (Prepared.prepare_c positive_encoding forest) <= preparation_bound c wo.
Proof.
  intro Hb.
  pose proof (PreparedCost.prepare_credit_cost positive_encoding positive_encoding_laws forest
    1 wo (2 + wo + N.of_nat c) (2 + wo) 0
    (live_nodup Hb) (callback_bounds c wo Hb)) as Hprepare.
  pose proof (live_length Hb) as Hnodes.
  assert (Hentries : (length (Graph.entries forest) <= c)%nat).
  { rewrite DomNumber.forest_equation. cbn [Graph.entries].
    eapply Nat.le_trans; [apply filter_length_le|exact Hnodes]. }
  pose proof (edge_inventory c wo Hb) as Hedges.
  pose proof (dense_width c wo Hb) as Hwidth.
  unfold preparation_bound.
  eapply N.le_trans; [exact Hprepare|].
  apply N.add_le_mono.
  - apply N.add_le_mono.
    + apply N.add_le_mono; [reflexivity|].
      apply N.mul_le_mono; [exact (ltac:(change (N.of_nat (length live) <= N.of_nat c); lia))|lia].
    + apply N.mul_le_mono; [exact Hedges|lia].
  - apply N.mul_le_mono; [lia|lia].
Qed.

Local Lemma ready c wo : bounds live parents c wo -> Prepared.ready q.
Proof.
  intro Hb. apply DomNumber.forest_prepared_ready;
    [exact (live_nodup Hb)|exact (parent_wf Hb)|exact (parent_domain Hb)].
Qed.

Local Lemma id_width c wo v i :
  bounds live parents c wo -> Prepared.id_of q v = Some i ->
  key_bits positive_encoding i <= rank_width c.
Proof.
  intros Hb Hi.
  assert (Hencoding : Prepared.node_enc q = positive_encoding).
  { unfold DomNumber.prepared. rewrite Prepared.prepare_equation. reflexivity. }
  rewrite Prepared.id_of_equation, Hencoding in Hi.
  unfold DomNumber.prepared in Hi. rewrite Prepared.prepare_names in Hi.
  eapply N.le_trans; [exact (PreparedCost.table_id_width _ positive_encoding_laws forest v i Hi)|].
  exact (dense_width c wo Hb).
Qed.

Local Lemma entry_length c wo :
  bounds live parents c wo -> (length (Prepared.entry_ids q) <= c)%nat.
Proof.
  intro Hb. rewrite (Prepared.entries_agree q (proj2 (proj2 (ready c wo Hb)))).
  unfold Prepared.ids. eapply Nat.le_trans; [apply Prepared.present_length|].
  unfold DomNumber.prepared. rewrite Prepared.prepare_graph, DomNumber.forest_equation.
  cbn [Graph.entries]. eapply Nat.le_trans; [apply filter_length_le|exact (live_length Hb)].
Qed.

Local Lemma prepared_fuel_width c wo :
  bounds live parents c wo -> N.pos (Pos.size (Prepared.fuel q)) <= fuel_width c.
Proof.
  intro Hb.
  pose proof (Prepared.fuel_value q (proj2 (proj2 (ready c wo Hb)))) as Hfuel.
  unfold DomNumber.prepared in Hfuel. rewrite Prepared.prepare_graph in Hfuel.
  pose proof (edge_inventory c wo Hb) as Hedges.
  rewrite <- Nat2N.inj_mul in Hedges.
  assert (Hedges_nat : (edge_count forest <= c * c)%nat) by lia.
  unfold fuel_width. apply InternCost.bits_monotone, Pos2Nat.inj_le.
  rewrite SuccNat2Pos.id_succ.
  change (Pos.to_nat (Prepared.fuel q) = 2 * length live + edge_count forest + 2)%nat in Hfuel.
  pose proof (live_length Hb) as Hnodes. lia.
Qed.

Definition search_bound c :=
  SearchCost.search_k *
    ((2 * N.of_nat c + N.of_nat c * N.of_nat c) * (2 + rank_width c) +
      N.of_nat c * fuel_width c).

(** The single actual forest search retains converted roots and binary-fuel work. *)
Theorem search_cost c wo :
  bounds live parents c wo ->
  Cost.ticks (SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt) <=
    search_bound c.
Proof.
  intro Hb.
  assert (Hwidth : SearchCost.width_bound q (Prepared.entry_ids q) (rank_width c)).
  { intros i [Hvalid|Hroot].
    - destruct Hvalid as [v [Hv Hi]]. exact (id_width c wo v i Hb Hi).
    - apply (Prepared.entry_ids_spec q i (proj2 (proj2 (ready c wo Hb)))) in Hroot.
      destruct Hroot as [v [Hv Hi]]. exact (id_width c wo v i Hb Hi). }
  pose proof (SearchCost.search_cost q Visitor.noop (fun _ : unit => 0) 1 Reach.unrestricted
    (Prepared.entry_ids q) (rank_width c) tt (ready c wo Hb) Hwidth
    (Visitor.noop_amortised (fun _ : unit => 0))) as Hsearch.
  cbn beta in Hsearch. rewrite N.add_0_r in Hsearch.
  pose proof (live_length Hb) as Hnodes.
  pose proof (edge_inventory c wo Hb) as Hedges.
  pose proof (entry_length c wo Hb) as Hentries.
  pose proof (prepared_fuel_width c wo Hb) as Hfuel.
  unfold SearchCost.search_size in Hsearch.
  unfold DomNumber.prepared in Hsearch. rewrite Prepared.prepare_graph in Hsearch.
  unfold search_bound. eapply N.le_trans; [exact Hsearch|].
  apply N.mul_le_mono; [reflexivity|]. apply N.add_le_mono.
  - apply N.mul_le_mono.
    + change (N.of_nat (length live) + N.of_nat (edge_count forest) +
        N.of_nat (length (Prepared.entry_ids q)) <= 2 * N.of_nat c + N.of_nat c * N.of_nat c).
      lia.
    + lia.
  - apply N.mul_le_mono.
    + change (N.of_nat (length (Prepared.entry_ids q)) <= N.of_nat c). lia.
    + exact Hfuel.
Qed.

Definition annotation_bound c wo := N.of_nat c * (7 + 2 * wo + rank_width c).

(** Inverse annotation pays original-name lookup, dense query and selected original-ID insertion. *)
Theorem annotation_cost c wo index :
  bounds live parents c wo ->
  Cost.ticks (DomNumber.annotation_c q index live) <= annotation_bound c wo.
Proof.
  intro Hb.
  assert (Hencoding : Prepared.node_enc q = positive_encoding).
  { unfold DomNumber.prepared. rewrite Prepared.prepare_equation. reflexivity. }
  unfold DomNumber.annotation_c.
  eapply N.le_trans;
    [apply (DomCostBasis.fold_right_cost _ live Map.empty (6 + 2 * wo + rank_width c))|].
  - intros v tail Hv. cbn beta.
    rewrite (Cost.ticks_bind (Prepared.id_of_c q v)).
    fold (Prepared.id_of q v).
    destruct (Prepared.id_of q v) as [i|] eqn:Hi.
    + pose proof (id_width c wo v i Hb Hi) as Hi_width.
      rewrite (Cost.ticks_bind (Map.get_c positive_encoding i index)).
      fold (Map.get positive_encoding i index).
      destruct (Map.get positive_encoding i index);
        rewrite ?DomCostBasis.set_cost, ?Cost.ticks_ret, DomCostBasis.get_cost;
        unfold Prepared.id_of_c; rewrite Hencoding, Intern.find_cost, DomCostBasis.get_cost;
        pose proof (live_width Hb v Hv); lia.
    + rewrite Cost.ticks_ret. unfold Prepared.id_of_c.
      rewrite Hencoding, Intern.find_cost, DomCostBasis.get_cost.
      pose proof (live_width Hb v Hv). lia.
  - unfold annotation_bound. apply N.mul_le_mono; [pose proof (live_length Hb); lia|lia].
Qed.

Definition number_bound c wo :=
  forest_bound c wo + preparation_bound c wo + search_bound c + 2 * annotation_bound c wo.

(** Complete numbering expands forest construction, preparation, one search and both annotations. *)
Theorem number_cost c wo :
  bounds live parents c wo ->
  Cost.ticks (DomNumber.of_parents_c live parents) <= number_bound c wo.
Proof.
  intro Hb.
  pose proof (forest_cost c wo Hb) as Hforest.
  pose proof (preparation_cost c wo Hb) as Hprepare.
  pose proof (search_cost c wo Hb) as Hsearch.
  unfold DomNumber.of_parents_c.
  rewrite (Cost.ticks_bind (DomNumber.forest_c live parents)). fold forest.
  rewrite (Cost.ticks_bind (Prepared.prepare_c positive_encoding forest)). fold q.
  rewrite (Cost.ticks_bind
    (SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt)).
  rewrite (Cost.ticks_bind (DomNumber.annotation_c q
    (Search.pre_num (fst (Cost.value
      (SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt)))) live)).
  rewrite (Cost.ticks_bind (DomNumber.annotation_c q
    (Search.post_num (fst (Cost.value
      (SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt)))) live)),
    Cost.ticks_ret.
  pose proof (annotation_cost c wo
    (Search.pre_num (fst (Cost.value (SearchRun.run_c q Visitor.noop Reach.unrestricted
      (Prepared.entry_ids q) tt)))) Hb) as Hin.
  pose proof (annotation_cost c wo
    (Search.post_num (fst (Cost.value (SearchRun.run_c q Visitor.noop Reach.unrestricted
      (Prepared.entry_ids q) tt)))) Hb) as Hout.
  unfold number_bound. lia.
Qed.

End Number.

(** The annotation coefficient retains public primitive coefficients symbolically. *)
Definition number_k := 128 * (1 + TrieCost.trie_k + InternCost.intern_k + SearchCost.search_k).

(** Finite original, dense and fuel widths give the quadratic annotation upper-bound shape. *)
Theorem number_shape c wo w :
  wo <= w -> rank_width c <= w -> fuel_width c <= w ->
  number_bound c wo <= number_k * (1 + N.of_nat c) * (1 + N.of_nat c) * (1 + w).
Proof.
  intros Ho Hr Hf.
  set (a := N.of_nat c).
  set (target := (1 + a) * (1 + a) * (1 + w)).
  assert (Hproduct : forall x y z, x <= 1 + a -> y <= 1 + a -> z <= 1 + w ->
    x * y * z <= target).
  { intros x y z Hx Hy Hz. unfold target.
    apply N.mul_le_mono; [now apply N.mul_le_mono|exact Hz]. }
  assert (Hone : 1 <= target).
  { change (1 * 1 * 1 <= target). apply Hproduct; lia. }
  assert (Ha : a <= target).
  { replace a with (a * 1 * 1) at 1 by ring. apply Hproduct; lia. }
  assert (Haw : a * w <= target).
  { replace (a * w) with (a * 1 * w) at 1 by ring. apply Hproduct; lia. }
  assert (Haa : a * a <= target).
  { replace (a * a) with (a * a * 1) at 1 by ring. apply Hproduct; lia. }
  assert (Haaw : a * a * w <= target) by (apply Hproduct; lia).
  assert (Hpath : 1 + a * w <= target).
  { eapply N.le_trans with (m := (1 + a) * (1 + w)).
    - replace ((1 + a) * (1 + w)) with (1 + a * w + (a + w)) by ring.
      apply N.le_add_r.
    - unfold target.
      replace ((1 + a) * (1 + w)) with ((1 + a) * 1 * (1 + w)) at 1 by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; lia|reflexivity]. }
  assert (Hmono : number_bound c wo <=
    (TrieCost.trie_k * (1 + a * w) + 1 + a * (11 + 5 * w)) +
    (2 + a * (31 + InternCost.intern_k + 8 * w + 3 * w + 3 * a) +
      (a * a) * (23 + 7 * w) + a * (4 + w)) +
    SearchCost.search_k * ((2 * a + a * a) * (2 + w) + a * w) +
    2 * (a * (7 + 2 * w + w))).
  { unfold number_bound, forest_bound, preparation_bound, search_bound, annotation_bound. fold a.
    repeat match goal with
    | |- (?x + ?y <= ?z + ?t)%N => apply N.add_le_mono
    | |- (?x * ?y <= ?z * ?t)%N => apply N.mul_le_mono
    | |- _ => first [reflexivity | assumption | lia]
    end. }
  assert (Htrie : TrieCost.trie_k * (1 + a * w) <= TrieCost.trie_k * target)
    by (apply N.mul_le_mono; [reflexivity|exact Hpath]).
  assert (Hintern : InternCost.intern_k * a <= InternCost.intern_k * target)
    by (apply N.mul_le_mono; [reflexivity|exact Ha]).
  assert (Hsearch_factor : (2 * a + a * a) * (2 + w) + a * w <= 10 * target).
  { replace ((2 * a + a * a) * (2 + w) + a * w) with
      (4 * a + 3 * (a * w) + 2 * (a * a) + a * a * w) by ring. lia. }
  assert (Hsearch : SearchCost.search_k * ((2 * a + a * a) * (2 + w) + a * w) <=
    SearchCost.search_k * (10 * target))
    by (apply N.mul_le_mono; [reflexivity|exact Hsearch_factor]).
  assert (Hpure : 3 + 60 * a + 23 * (a * w) + 26 * (a * a) + 7 * (a * a * w) <= 119 * target)
    by lia.
  eapply N.le_trans; [exact Hmono|].
  replace ((TrieCost.trie_k * (1 + a * w) + 1 + a * (11 + 5 * w)) +
    (2 + a * (31 + InternCost.intern_k + 8 * w + 3 * w + 3 * a) +
      (a * a) * (23 + 7 * w) + a * (4 + w)) +
    SearchCost.search_k * ((2 * a + a * a) * (2 + w) + a * w) +
    2 * (a * (7 + 2 * w + w))) with
    ((3 + 60 * a + 23 * (a * w) + 26 * (a * a) + 7 * (a * a * w)) +
      TrieCost.trie_k * (1 + a * w) + InternCost.intern_k * a +
      SearchCost.search_k * ((2 * a + a * a) * (2 + w) + a * w)) by ring.
  replace (number_k * (1 + a) * (1 + a) * (1 + w)) with (number_k * target)
    by (unfold target; ring).
  eapply N.le_trans.
  - apply N.add_le_mono; [|exact Hsearch].
    apply N.add_le_mono; [|exact Hintern].
    apply N.add_le_mono; [exact Hpure|exact Htrie].
  - replace (119 * target + TrieCost.trie_k * target + InternCost.intern_k * target +
      SearchCost.search_k * (10 * target)) with
      ((119 + TrieCost.trie_k + InternCost.intern_k + 10 * SearchCost.search_k) * target) by ring.
    apply N.mul_le_mono; [unfold number_k; lia|reflexivity].
Qed.

End DomNumberCost.
