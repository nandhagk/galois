(** * Primitive costs of finite-view normalization

    Normalization prices original key callbacks, every cached occurrence and actual graph preparation.
    For example, a rejected out-of-universe target still incurs its filtering query.
    Builds on: GraphDomFiniteView, GraphDomCostBasis and public preparation cost contracts. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern
  BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphReach
  GraphDomFiniteView GraphDomCostBasis.
Import Cost.Notations.

Module DomFiniteCost.
Local Open Scope N_scope.

(** Budgets concern primitive callbacks and actual finite input, row, root and normalized graph sizes. *)
Record bounds {V E} (p : Prepared.t V E) roots (n m r : nat) ek bk w : Prop := {
  input_nodes : (length (Graph.nodes (Prepared.graph p)) <= n)%nat;
  input_roots : (length roots <= r)%nat;
  input_keys : forall v, In v (Graph.nodes (Prepared.graph p)) ->
    Cost.ticks (encode_c (Prepared.node_enc p) v) <= ek /\
    key_bits (Prepared.node_enc p) v <= bk;
  universe_width : forall v, In v (Reach.universe p) -> key_bits positive_encoding v <= w;
  root_width : forall v, In v roots -> key_bits positive_encoding v <= w;
  row_width : forall u ev, In u (Reach.universe p) ->
    In ev (Prepared.succ_edges p u) -> key_bits positive_encoding (snd ev) <= w;
  row_length : forall u, In u (Reach.universe p) -> (length (Prepared.succ_edges p u) <= m)%nat;
  graph_edges : (edge_count (DomFiniteView.graph (DomFiniteView.view p roots)) <= m)%nat;
  dense_width : PreparedCost.id_width (DomFiniteView.graph (DomFiniteView.view p roots)) <= w
}.
Arguments input_nodes {V E p roots n m r ek bk w} _.
Arguments input_roots {V E p roots n m r ek bk w} _.
Arguments input_keys {V E p roots n m r ek bk w} _ _ _.
Arguments universe_width {V E p roots n m r ek bk w} _ _ _.
Arguments root_width {V E p roots n m r ek bk w} _ _ _.
Arguments row_width {V E p roots n m r ek bk w} _ _ _ _ _.
Arguments row_length {V E p roots n m r ek bk w} _ _ _.
Arguments graph_edges {V E p roots n m r ek bk w} _.
Arguments dense_width {V E p roots n m r ek bk w} _.

(** Option mapping charges traversal and invocation overhead on every supplied occurrence. *)
Theorem present_cost {A B} (f : A -> Cost.t (option B)) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (Prepared.present_c f xs) <= N.of_nat (length xs) * (2 + k).
Proof.
  apply DomCostBasis.present_cost.
Qed.

Local Lemma set_members {V E} (p : Prepared.t V E) v :
  In v (FinSet.elements (DomFiniteView.universe_set p)) <->
    In v (Reach.universe p).
Proof.
  rewrite (FinSet.elements_spec positive_encoding positive_encoding_laws)
    by apply FinSet.wf_of_list.
  apply DomFiniteView.universe_members.
Qed.

(** Normalized universe cardinality is bounded by the original node occurrences, including duplicates. *)
Theorem universe_size {V E} (p : Prepared.t V E) :
  (FinSet.size (DomFiniteView.universe_set p) <= length (Graph.nodes (Prepared.graph p)))%nat.
Proof.
  unfold DomFiniteView.universe_set.
  eapply Nat.le_trans; [apply DomCostBasis.of_list_size|apply Prepared.present_length].
Qed.

(** The canonical vertex list has the same bounded cardinality. *)
Theorem vertex_length {V E} (p : Prepared.t V E) roots :
  (length (DomFiniteView.vertices (DomFiniteView.view p roots)) <=
    length (Graph.nodes (Prepared.graph p)))%nat.
Proof.
  rewrite DomFiniteView.view_vertices, <- FinSet.size_elements. apply universe_size.
Qed.

(** A canonical target row contains at most one binding per original universe member. *)
Theorem target_size {V E} (p : Prepared.t V E) u :
  (FinSet.size (Cost.value (DomFiniteView.targets_c p (DomFiniteView.universe_set p) u)) <=
    length (Graph.nodes (Prepared.graph p)))%nat.
Proof.
  eapply Nat.le_trans; [|apply universe_size].
  rewrite (FinSet.size_elements (DomFiniteView.universe_set p)).
  apply (Map.size_support_bound positive_encoding positive_encoding_laws).
  - rewrite DomFiniteView.targets_value. apply FinSet.wf_of_list.
  - intros v [] Hget. apply FinSet.mem_spec in Hget.
    apply DomFiniteView.targets_members in Hget.
    apply (FinSet.elements_spec positive_encoding positive_encoding_laws);
      [apply FinSet.wf_of_list|exact (proj1 Hget)].
Qed.

(** Every raw cached occurrence is traversed, filtered and, when retained, inserted at its actual width. *)
Theorem targets_cost {V E} (p : Prepared.t V E) roots n m r ek bk w u :
  bounds p roots n m r ek bk w -> In u (Reach.universe p) ->
  Cost.ticks (DomFiniteView.targets_c p (DomFiniteView.universe_set p) u) <=
    2 + w + N.of_nat m * (8 + 2 * w).
Proof.
  intros Hb Hu.
  set (outgoing := Prepared.succ_edges p u).
  set (targets := map snd outgoing).
  set (all := DomFiniteView.universe_set p).
  assert (Hwidth : forall v, In v targets -> key_bits positive_encoding v <= w).
  { intros v Hv. apply in_map_iff in Hv. destruct Hv as [ev [<- Hev]].
    exact (row_width Hb u ev Hu Hev). }
  assert (Hlength : (length outgoing <= m)%nat) by exact (row_length Hb u Hu).
  pose proof (DomCostBasis.map_cost (fun ev : E * positive => Cost.ret (snd ev))
    outgoing 0 ltac:(intros; reflexivity)) as Hmap.
  pose proof (DomCostBasis.filter_cost (fun v => FinSet.mem_c positive_encoding v all)
    targets (2 + w) ltac:(intros v Hv; cbn beta; rewrite DomCostBasis.mem_cost;
      pose proof (Hwidth v Hv); lia)) as Hfilter.
  set (valid := filter (fun v => FinSet.mem positive_encoding v all) targets).
  pose proof (DomCostBasis.of_list_cost valid w
    ltac:(intros v Hv; apply filter_In in Hv; exact (Hwidth v (proj1 Hv)))) as Hset.
  assert (Hvalid : (length valid <= m)%nat).
  { unfold valid. eapply Nat.le_trans; [apply filter_length_le|].
    unfold targets. rewrite length_map. exact Hlength. }
  assert (Hget : Cost.ticks (Prepared.succ_edges_c p u) <= 2 + w).
  { unfold Prepared.succ_edges_c. rewrite Index.find_cost, DomCostBasis.get_cost.
    pose proof (universe_width Hb u Hu). lia. }
  unfold DomFiniteView.targets_c.
  rewrite !Cost.ticks_bind, value_map_c, value_filter_c.
  fold outgoing. fold targets all valid.
  change (Cost.ticks (Prepared.succ_edges_c p u) +
    (Cost.ticks (map_c (fun ev : E * positive => Cost.ret (snd ev)) outgoing) +
      (Cost.ticks (filter_c (fun v => FinSet.mem_c positive_encoding v all) targets) +
        Cost.ticks (FinSet.of_list_c positive_encoding valid))) <=
    2 + w + N.of_nat m * (8 + 2 * w)).
  unfold targets in Hfilter. rewrite length_map in Hfilter. fold targets in Hfilter.
  assert (Hscale1 : N.of_nat (length outgoing) * (1 + 0) <= N.of_nat m) by nia.
  assert (Hscale2 : N.of_nat (length outgoing) * (1 + (2 + w)) <=
    N.of_nat m * (3 + w)) by (apply N.mul_le_mono; lia).
  assert (Hscale3 : N.of_nat (length valid) * (4 + w) <= N.of_nat m * (4 + w))
    by (apply N.mul_le_mono; lia).
  nia.
Qed.

Definition data_bound (n m r : nat) ek bk w :=
  N.of_nat n * (3 + ek + bk + (4 + w)) +
  (TrieCost.trie_k * (1 + N.of_nat n * w) + N.of_nat n) +
  N.of_nat r * (3 + w) +
  N.of_nat n * (5 + 2 * w + N.of_nat m * (8 + 2 * w)).

(** The full normalization-data bound includes encoder inventory, root filtering and every row construction. *)
Theorem data_cost {V E} (p : Prepared.t V E) roots n m r ek bk w :
  bounds p roots n m r ek bk w ->
  Cost.ticks (DomFiniteView.data_c p roots) <= data_bound n m r ek bk w.
Proof.
  intro Hb.
  set (ids := Prepared.present (Prepared.id_of p) (Graph.nodes (Prepared.graph p))).
  set (all := DomFiniteView.universe_set p).
  set (vertices := FinSet.elements all).
  assert (Hids_length : (length ids <= n)%nat).
  { eapply Nat.le_trans; [apply Prepared.present_length|exact (input_nodes Hb)]. }
  assert (Hids_width : forall v, In v ids -> key_bits positive_encoding v <= w).
  { intros v Hv. apply (universe_width Hb v). unfold Reach.universe. now apply nodup_In. }
  pose proof (present_cost (Prepared.id_of_c p) (Graph.nodes (Prepared.graph p))
    (1 + ek + bk) ltac:(intros v Hv; unfold Prepared.id_of_c; rewrite Intern.find_cost, Map.get_cost;
      destruct (input_keys Hb v Hv) as [Henc Hbits]; fold (key_bits (Prepared.node_enc p) v); lia))
    as Hids.
  pose proof (DomCostBasis.of_list_cost ids w Hids_width) as Hset.
  assert (Hall_size : (FinSet.size all <= n)%nat).
  { eapply Nat.le_trans; [apply universe_size|exact (input_nodes Hb)]. }
  pose proof (DomCostBasis.elements_cost all n w (FinSet.wf_of_list positive_encoding ids)
    Hall_size ltac:(intros v Hv; apply universe_width with (1 := Hb);
      now apply DomFiniteView.universe_members)) as Hvertices.
  assert (Hvertices_length : (length vertices <= n)%nat).
  { unfold vertices. rewrite <- FinSet.size_elements. exact Hall_size. }
  pose proof (DomCostBasis.filter_cost (fun v => FinSet.mem_c positive_encoding v all)
    roots (2 + w) ltac:(intros v Hv; cbn beta; rewrite DomCostBasis.mem_cost;
      pose proof (root_width Hb v Hv); lia)) as Hroots.
  pose proof (DomCostBasis.fold_right_cost
    (fun u rows => let* targets := DomFiniteView.targets_c p all u in
      Map.set_c positive_encoding u targets rows) vertices Map.empty
    (4 + 2 * w + N.of_nat m * (8 + 2 * w))
    ltac:(intros u rows Hu; cbn beta; rewrite Cost.ticks_bind, DomCostBasis.set_cost;
      assert (Hlive : In u (Reach.universe p)) by (apply set_members; exact Hu);
      pose proof (targets_cost p roots n m r ek bk w u Hb Hlive) as Htarget;
      fold all in Htarget;
      pose proof (universe_width Hb u Hlive); lia)) as Hrows.
  unfold DomFiniteView.data_c.
  rewrite (Cost.ticks_bind (Prepared.present_c (Prepared.id_of_c p)
    (Graph.nodes (Prepared.graph p)))).
  rewrite Prepared.present_c_value. fold ids.
  change (Cost.ticks (Prepared.present_c (Prepared.id_of_c p) (Graph.nodes (Prepared.graph p))) +
    Cost.ticks
      (let* all := FinSet.of_list_c positive_encoding ids in
       let* vertices := FinSet.elements_c all in
       let* entries := filter_c (fun v => FinSet.mem_c positive_encoding v all) roots in
       let* rows := fold_right_c (fun u rows =>
         let* targets := DomFiniteView.targets_c p all u in
         Map.set_c positive_encoding u targets rows) Map.empty vertices in
       Cost.ret (DomFiniteView.Data all vertices entries rows)) <= data_bound n m r ek bk w).
  rewrite (Cost.ticks_bind (FinSet.of_list_c positive_encoding ids)).
  fold all.
  rewrite (Cost.ticks_bind (FinSet.elements_c all)). fold vertices.
  rewrite (Cost.ticks_bind (filter_c (fun v => FinSet.mem_c positive_encoding v all) roots)).
  rewrite (Cost.ticks_bind (fold_right_c
    (fun u rows => let* targets := DomFiniteView.targets_c p all u in
      Map.set_c positive_encoding u targets rows) Map.empty vertices)).
  rewrite Cost.ticks_ret.
  change (Cost.ticks (Prepared.present_c (Prepared.id_of_c p) (Graph.nodes (Prepared.graph p))) +
    (Cost.ticks (FinSet.of_list_c positive_encoding ids) +
      (Cost.ticks (FinSet.elements_c all) +
        (Cost.ticks (filter_c (fun v => FinSet.mem_c positive_encoding v all) roots) +
          (Cost.ticks (fold_right_c
            (fun u rows => let* targets := DomFiniteView.targets_c p all u in
              Map.set_c positive_encoding u targets rows) Map.empty vertices) + 0)))) <=
    data_bound n m r ek bk w).
  unfold data_bound.
  assert (Hscale_ids : N.of_nat (length (Graph.nodes (Prepared.graph p))) *
    (2 + (1 + ek + bk)) <= N.of_nat n * (3 + ek + bk))
    by (apply N.mul_le_mono; [pose proof (input_nodes Hb); lia|lia]).
  assert (Hscale_set : N.of_nat (length ids) * (4 + w) <= N.of_nat n * (4 + w))
    by (apply N.mul_le_mono; lia).
  assert (Hscale_roots : N.of_nat (length roots) * (1 + (2 + w)) <= N.of_nat r * (3 + w))
    by (apply N.mul_le_mono; [pose proof (input_roots Hb); lia|lia]).
  assert (Hscale_rows : N.of_nat (length vertices) *
    (1 + (4 + 2 * w + N.of_nat m * (8 + 2 * w))) <=
    N.of_nat n * (5 + 2 * w + N.of_nat m * (8 + 2 * w)))
    by (apply N.mul_le_mono; lia).
  nia.
Qed.

Definition out_bound n w :=
  2 + w + TrieCost.trie_k * (1 + N.of_nat n * w) + 2 * N.of_nat n.

(** A normalized outgoing callback pays its row lookup, canonical enumeration and edge-label mapping. *)
Theorem outgoing_cost {V E} (p : Prepared.t V E) roots n m r ek bk w u :
  bounds p roots n m r ek bk w -> In u (Reach.universe p) ->
  Cost.ticks (Graph.out_c (DomFiniteView.graph (DomFiniteView.view p roots)) u) <= out_bound n w.
Proof.
  intros Hb Hu.
  set (all := DomFiniteView.universe_set p).
  set (targets := Cost.value (DomFiniteView.targets_c p all u)).
  assert (Hsize : (FinSet.size targets <= n)%nat).
  { eapply Nat.le_trans; [apply target_size|exact (input_nodes Hb)]. }
  assert (Hset : FinSet.wf positive_encoding targets).
  { unfold targets. rewrite DomFiniteView.targets_value. apply FinSet.wf_of_list. }
  pose proof (DomCostBasis.elements_cost targets n w Hset Hsize
    ltac:(intros v Hv; apply DomFiniteView.targets_members in Hv;
      apply (universe_width Hb v); now apply DomFiniteView.universe_members)) as Henumerate.
  pose proof (DomCostBasis.map_cost (fun v : positive => Cost.ret (u, v))
    (FinSet.elements targets) 0 ltac:(intros; reflexivity)) as Hmap.
  assert (Hlength : (length (FinSet.elements targets) <= n)%nat).
  { rewrite <- FinSet.size_elements. exact Hsize. }
  change (Cost.ticks
    (Map.get_c positive_encoding u (DomFiniteView.rows (DomFiniteView.view p roots))) +
    Cost.ticks
      (match Map.get positive_encoding u (DomFiniteView.rows (DomFiniteView.view p roots)) with
      | None => Cost.ret nil
      | Some targets =>
        let* listed := FinSet.elements_c targets in
        map_c (fun v => Cost.ret (u, v)) listed
      end) <= out_bound n w).
  rewrite DomCostBasis.get_cost, DomFiniteView.view_rows, DomFiniteView.rows_get
    by (apply set_members; exact Hu).
  fold all targets.
  rewrite (Cost.ticks_bind (FinSet.elements_c targets)).
  fold (FinSet.elements targets).
  pose proof (universe_width Hb u Hu).
  unfold out_bound.
  assert (Hscale : N.of_nat (length (FinSet.elements targets)) * (1 + 0) <= N.of_nat n) by nia.
  lia.
Qed.

(** All preparation callback prices are derived from primitive queries and finite canonical row support. *)
Theorem preparation_bounds {V E} (p : Prepared.t V E) roots n m r ek bk w :
  bounds p roots n m r ek bk w ->
  PreparedCost.prepare_bounds positive_encoding (DomFiniteView.graph (DomFiniteView.view p roots))
    1 w (out_bound n w) 0 0.
Proof.
  intro Hb. constructor.
  - intros v Hv. split; [reflexivity|].
    apply (universe_width Hb v). now apply DomFiniteView.graph_nodes in Hv.
  - intros v Hv. split; [reflexivity|].
    apply (universe_width Hb v). apply DomFiniteView.graph_entries in Hv. exact (proj2 Hv).
  - intros v Hv. apply outgoing_cost with (1 := Hb).
    now apply DomFiniteView.graph_nodes in Hv.
  - intros edge Hedge. unfold Prepared.all_edges in Hedge.
    apply in_flat_map in Hedge. destruct Hedge as [u [Hu Hedge]].
    apply DomFiniteView.graph_edge in Hedge.
    destruct Hedge as [Hsource [Hsource_live [Htarget_live Hoccurrence]]].
    change (0 <= 0 /\ 0 <= 0 /\ 1 <= 1 /\
      key_bits positive_encoding (fst edge) <= w /\ 1 <= 1 /\
      key_bits positive_encoding (snd edge) <= w).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite Hsource; exact (universe_width Hb u Hsource_live)|].
    split; [reflexivity|exact (universe_width Hb (snd edge) Htarget_live)].
Qed.

Definition preparation_bound (n m r : nat) w :=
  PreparedCost.prepare_k *
    (1 + (N.of_nat n + N.of_nat m + N.of_nat r) * (2 + 2 * w + out_bound n w)).

(** Actual normalized preparation includes all interning, predecessor indexing, callback and fuel work. *)
Theorem preparation_cost {V E} (p : Prepared.t V E) roots n m r ek bk w :
  bounds p roots n m r ek bk w ->
  Cost.ticks (Prepared.prepare_c positive_encoding
    (DomFiniteView.graph (DomFiniteView.view p roots))) <= preparation_bound n m r w.
Proof.
  intro Hb.
  pose proof (PreparedCost.prepare_cost positive_encoding positive_encoding_laws
    (DomFiniteView.graph (DomFiniteView.view p roots)) 1 w (out_bound n w) 0 0
    (nodes_nodup (DomFiniteView.graph_well_formed p roots))
    (preparation_bounds p roots n m r ek bk w Hb)) as Hprepare.
  assert (Hnodes : (length (Graph.nodes (DomFiniteView.graph (DomFiniteView.view p roots))) <= n)%nat).
  { eapply Nat.le_trans; [apply vertex_length|exact (input_nodes Hb)]. }
  assert (Hentries : (length (Graph.entries (DomFiniteView.graph (DomFiniteView.view p roots))) <= r)%nat).
  { change (length (DomFiniteView.entries (DomFiniteView.view p roots)) <= r)%nat.
    rewrite DomFiniteView.view_entries.
    eapply Nat.le_trans; [apply filter_length_le|exact (input_roots Hb)]. }
  pose proof (graph_edges Hb) as Hedges. pose proof (dense_width Hb) as Hwidth.
  unfold PreparedCost.prepare_size in Hprepare. unfold preparation_bound.
  eapply N.le_trans; [exact Hprepare|].
  apply N.mul_le_mono; [reflexivity|].
  apply N.add_le_mono; [reflexivity|].
  apply N.mul_le_mono; [lia|lia].
Qed.

Definition prepare_bound (n m r : nat) ek bk w :=
  data_bound n m r ek bk w + preparation_bound n m r w.

(** One complete view setup has a closed primitive budget with no owned-operation price premise. *)
Theorem prepare_cost {V E} (p : Prepared.t V E) roots n m r ek bk w :
  bounds p roots n m r ek bk w ->
  Cost.ticks (DomFiniteView.prepare_c p roots) <= prepare_bound n m r ek bk w.
Proof.
  intro Hb. unfold DomFiniteView.prepare_c.
  rewrite (Cost.ticks_bind (DomFiniteView.data_c p roots)).
  fold (DomFiniteView.view p roots).
  apply N.add_le_mono.
  - exact (data_cost p roots n m r ek bk w Hb).
  - exact (preparation_cost p roots n m r ek bk w Hb).
Qed.

End DomFiniteCost.
