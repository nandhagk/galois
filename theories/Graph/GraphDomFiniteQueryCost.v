(** * Primitive costs of reused normalized searches

    Each query pays scope conversion, the shared indexed kernel and original-ID materialization.
    For example, repeated entry occurrences retain their own binary-fuel descent costs.
    Builds on: GraphDomFiniteCost and the public SearchCost contract. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphVisitor
  GraphSearchSpec GraphSearch GraphSearchCost GraphReach GraphDomFiniteView GraphDomFiniteSearch
  GraphDomFiniteReach GraphDomFiniteCost GraphDomCostBasis.
Import Cost.Notations.

Module DomFiniteQueryCost.
Local Open Scope N_scope.

Local Lemma scoped_endpoint {A B} (prepared : Prepared.t A B) scope u es v :
  Search.scoped_path prepared scope u es v -> Prepared.valid_id prepared v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

Section Query.
Context {V E : Type} (p : Prepared.t V E) (roots : list positive).
Local Abbreviation q := (DomFiniteView.prepared p roots).
Local Abbreviation g := (DomFiniteView.graph (DomFiniteView.view p roots)).

Local Lemma encoding_equation : Prepared.node_enc q = positive_encoding.
Proof.
  rewrite DomFiniteView.prepared_equation, Prepared.prepare_equation. reflexivity.
Qed.

(** Forward conversion prices the queried original positive ID independently of lookup success. *)
Theorem id_cost v :
  Cost.ticks (Prepared.id_of_c q v) = 2 + key_bits positive_encoding v.
Proof.
  unfold Prepared.id_of_c. rewrite encoding_equation, Intern.find_cost, DomCostBasis.get_cost.
  reflexivity.
Qed.

(** Inverse conversion prices the actual dense ID even when no name is returned. *)
Theorem name_cost i :
  Cost.ticks (Prepared.name_of_c q i) = 2 + key_bits positive_encoding i.
Proof.
  unfold Prepared.name_of_c. rewrite Intern.key_of_cost. apply DomCostBasis.get_cost.
Qed.

(** Every actual normalized binding has the finite dense width proved by preparation. *)
Theorem id_width v i :
  Prepared.id_of q v = Some i -> key_bits positive_encoding i <= PreparedCost.id_width g.
Proof.
  intro Hi. rewrite Prepared.id_of_equation, encoding_equation,
    DomFiniteView.prepared_equation, Prepared.prepare_names in Hi.
  exact (PreparedCost.table_id_width positive_encoding positive_encoding_laws g v i Hi).
Qed.

(** Listed normalized nodes retain their original positive-ID width duty. *)
Theorem node_width n m r ek bk w v :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  In v (Graph.nodes (Prepared.graph q)) -> key_bits positive_encoding v <= w.
Proof.
  intros Hb Hv. apply (DomFiniteCost.universe_width Hb v).
  rewrite DomFiniteView.prepared_graph in Hv. now apply DomFiniteView.graph_nodes in Hv.
Qed.

(** Search root multiplicity is bounded by supplied root occurrences rather than universe cardinality. *)
Theorem entry_length n m r ek bk w :
  DomFiniteCost.bounds p roots n m r ek bk w -> (length (Prepared.entry_ids q) <= r)%nat.
Proof.
  intro Hb.
  rewrite (Prepared.entries_agree q (proj2 (proj2 (DomFiniteView.prepared_ready p roots)))).
  unfold Prepared.ids. eapply Nat.le_trans; [apply Prepared.present_length|].
  rewrite DomFiniteView.prepared_graph.
  change (length (DomFiniteView.entries (DomFiniteView.view p roots)) <= r)%nat.
  rewrite DomFiniteView.view_entries.
  eapply Nat.le_trans; [apply filter_length_le|exact (DomFiniteCost.input_roots Hb)].
Qed.

(** All valid normalized IDs and all actual converted roots satisfy the same derived dense width. *)
Theorem search_width n m r ek bk w :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  SearchCost.width_bound q (Prepared.entry_ids q) w.
Proof.
  intros Hb i [Hvalid|Hroot].
  - destruct Hvalid as [v [Hv Hi]].
    eapply N.le_trans; [exact (id_width v i Hi)|exact (DomFiniteCost.dense_width Hb)].
  - apply (Prepared.entry_ids_spec q i (proj2 (proj2 (DomFiniteView.prepared_ready p roots))))
      in Hroot.
    destruct Hroot as [v [Hv Hi]].
    eapply N.le_trans; [exact (id_width v i Hi)|exact (DomFiniteCost.dense_width Hb)].
Qed.

(** Actual search coverage bounds the query result without assuming a successful output. *)
Theorem preorder_length n m r ek bk w scope :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  (length (Search.preorder (DomFiniteSearch.run q scope)) <= n)%nat.
Proof.
  intro Hb. rewrite DomFiniteSearch.run_equation.
  change (length (Search.preorder
    (SearchRun.dfs q (DomFiniteSearch.translate q scope) (Prepared.entry_ids q))) <= n)%nat.
  eapply Nat.le_trans; [apply SearchCost.preorder_length; apply DomFiniteView.prepared_ready|].
  rewrite DomFiniteView.prepared_graph.
  eapply Nat.le_trans; [apply DomFiniteCost.vertex_length|exact (DomFiniteCost.input_nodes Hb)].
Qed.

Local Lemma discovered_id scope i :
  In i (Search.preorder (DomFiniteSearch.run q scope)) -> Prepared.valid_id q i.
Proof.
  intro Hi.
  apply (Search.pre_complete _ _ _ _ (DomFiniteSearch.normalized_run_exact p roots scope)) in Hi.
  destruct Hi as [root [es [Hroot Hpath]]].
  exact (scoped_endpoint q _ _ _ _ Hpath).
Qed.

Definition translation_bound (n : nat) w hs := N.of_nat n * (8 + hs + 2 * w).

(** Scope translation expands all admission, dictionary and allowed-set construction work. *)
Theorem translate_cost n m r ek bk w hs scope :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  (forall v, In v (Reach.universe p) -> Cost.ticks (Scope.admits_c scope v) <= hs) ->
  Cost.ticks (DomFiniteSearch.translate_c q scope) <= translation_bound n w hs.
Proof.
  intros Hb Hscope.
  set (nodes := Graph.nodes (Prepared.graph q)).
  set (f := fun v =>
    let* allowed := Scope.admits_c scope v in
    if allowed then Prepared.id_of_c q v else Cost.ret None).
  assert (Hlength : (length nodes <= n)%nat).
  { unfold nodes. rewrite DomFiniteView.prepared_graph.
    eapply Nat.le_trans; [apply DomFiniteCost.vertex_length|exact (DomFiniteCost.input_nodes Hb)]. }
  pose proof (DomFiniteCost.present_cost f nodes (hs + 2 + w)
    ltac:(intros v Hv; unfold f; rewrite Cost.ticks_bind;
      fold (Scope.admits scope v);
      assert (Hlive : In v (Reach.universe p)) by
        (unfold nodes in Hv; rewrite DomFiniteView.prepared_graph in Hv;
          now apply DomFiniteView.graph_nodes in Hv);
      pose proof (Hscope v Hlive); pose proof (node_width n m r ek bk w v Hb Hv);
      destruct (Scope.admits scope v); rewrite ?id_cost, ?Cost.ticks_ret; lia)) as Hpresent.
  set (ids := Prepared.present (fun v => Cost.value (f v)) nodes).
  assert (Hids : (length ids <= n)%nat).
  { eapply Nat.le_trans; [apply Prepared.present_length|exact Hlength]. }
  pose proof (DomCostBasis.of_list_cost ids w
    ltac:(intros i Hi; apply Prepared.present_spec in Hi; destruct Hi as [v [Hv Hi]];
      unfold f in Hi; rewrite Cost.value_bind in Hi; fold (Scope.admits scope v) in Hi;
      destruct (Scope.admits scope v); [|discriminate];
      change (Prepared.id_of q v = Some i) in Hi;
      eapply N.le_trans; [exact (id_width v i Hi)|exact (DomFiniteCost.dense_width Hb)])) as Hset.
  unfold DomFiniteSearch.translate_c. fold nodes f.
  rewrite (Cost.ticks_bind (Prepared.present_c f nodes)), Prepared.present_c_value.
  fold ids.
  change (Cost.ticks (Prepared.present_c f nodes) +
    (Cost.ticks (FinSet.of_list_c positive_encoding ids) + 0) <= translation_bound n w hs).
  unfold translation_bound.
  assert (Hscale1 : N.of_nat (length nodes) * (2 + (hs + 2 + w)) <=
    N.of_nat n * (4 + hs + w)) by (apply N.mul_le_mono; lia).
  assert (Hscale2 : N.of_nat (length ids) * (4 + w) <= N.of_nat n * (4 + w))
    by (apply N.mul_le_mono; lia).
  nia.
Qed.

Definition search_bound (n m r : nat) w f :=
  SearchCost.search_k * ((N.of_nat n + N.of_nat m + N.of_nat r) * (2 + w) + N.of_nat r * f).

(** Each reused indexed search retains all root occurrences and their actual prepared-fuel width. *)
Theorem run_cost n m r ek bk w f hs scope :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  N.pos (Pos.size (Prepared.fuel q)) <= f ->
  (forall v, In v (Reach.universe p) -> Cost.ticks (Scope.admits_c scope v) <= hs) ->
  Cost.ticks (DomFiniteSearch.run_c q scope) <=
    translation_bound n w hs + search_bound n m r w f.
Proof.
  intros Hb Hfuel Hscope.
  pose proof (translate_cost n m r ek bk w hs scope Hb Hscope) as Htranslate.
  pose proof (SearchCost.search_cost q Visitor.noop (fun _ : unit => 0) 1
    (DomFiniteSearch.translate q scope) (Prepared.entry_ids q) w tt
    (DomFiniteView.prepared_ready p roots) (search_width n m r ek bk w Hb)
    (Visitor.noop_amortised (fun _ : unit => 0))) as Hsearch.
  assert (Hnodes : (length (Graph.nodes (Prepared.graph q)) <= n)%nat).
  { rewrite DomFiniteView.prepared_graph.
    eapply Nat.le_trans; [apply DomFiniteCost.vertex_length|exact (DomFiniteCost.input_nodes Hb)]. }
  pose proof (entry_length n m r ek bk w Hb) as Hroots.
  pose proof (DomFiniteCost.graph_edges Hb) as Hedges.
  unfold DomFiniteSearch.run_c.
  rewrite (Cost.ticks_bind (DomFiniteSearch.translate_c q scope)), Cost.ticks_map.
  fold (DomFiniteSearch.translate q scope).
  apply N.add_le_mono; [exact Htranslate|].
  unfold search_bound, SearchCost.search_size in *.
  rewrite DomFiniteView.prepared_graph in Hsearch.
  rewrite DomFiniteView.prepared_graph in Hnodes.
  rewrite N.add_0_r in Hsearch.
  eapply N.le_trans; [exact Hsearch|].
  apply N.mul_le_mono; [reflexivity|].
  apply N.add_le_mono.
  - apply N.mul_le_mono; [lia|lia].
  - apply N.mul_le_mono; [lia|exact Hfuel].
Qed.

Definition reach_bound (n m r : nat) w f hs :=
  translation_bound n w hs + search_bound n m r w f + 2 * N.of_nat n * (4 + w).

(** Full materialized reachability expands the actual search, inverse lookups and output-set insertion. *)
Theorem reach_cost n m r ek bk w f hs scope :
  DomFiniteCost.bounds p roots n m r ek bk w ->
  N.pos (Pos.size (Prepared.fuel q)) <= f ->
  (forall v, In v (Reach.universe p) -> Cost.ticks (Scope.admits_c scope v) <= hs) ->
  Cost.ticks (DomFiniteReach.reach_c q scope) <= reach_bound n m r w f hs.
Proof.
  intros Hb Hfuel Hscope.
  pose proof (run_cost n m r ek bk w f hs scope Hb Hfuel Hscope) as Hrun.
  set (order := Search.preorder (DomFiniteSearch.run q scope)).
  pose proof (preorder_length n m r ek bk w scope Hb) as Horder. fold order in Horder.
  pose proof (DomFiniteCost.present_cost (Prepared.name_of_c q) order (2 + w)
    ltac:(intros i Hi; rewrite name_cost; pose proof (discovered_id scope i Hi) as Hvalid;
      pose proof (search_width n m r ek bk w Hb i (or_introl Hvalid)); lia)) as Hnames.
  set (names := Prepared.present (Prepared.name_of q) order).
  assert (Hnames_length : (length names <= n)%nat).
  { eapply Nat.le_trans; [apply Prepared.present_length|exact Horder]. }
  pose proof (DomCostBasis.of_list_cost names w
    ltac:(intros v Hv; apply Prepared.present_spec in Hv; destruct Hv as [i [Hi Hname]];
      apply (DomFiniteCost.universe_width Hb v); apply DomFiniteView.graph_nodes with (roots := roots);
      rewrite <- DomFiniteView.prepared_graph;
      apply (Prepared.ids_domain q (proj2 (proj2 (DomFiniteView.prepared_ready p roots))));
      exists i; exact (Prepared.id_of_name_of q i v
        (proj2 (proj2 (DomFiniteView.prepared_ready p roots))) Hname))) as Hset.
  unfold DomFiniteReach.reach_c.
  rewrite (Cost.ticks_bind (DomFiniteSearch.run_c q scope)).
  fold (DomFiniteSearch.run q scope). fold order.
  rewrite (Cost.ticks_bind (Prepared.present_c (Prepared.name_of_c q) order)),
    Prepared.present_c_value. fold names.
  change (Cost.ticks (DomFiniteSearch.run_c q scope) +
    (Cost.ticks (Prepared.present_c (Prepared.name_of_c q) order) +
      Cost.ticks (FinSet.of_list_c positive_encoding names)) <= reach_bound n m r w f hs).
  assert (Hscale1 : N.of_nat (length order) * (2 + (2 + w)) <= N.of_nat n * (4 + w))
    by (apply N.mul_le_mono; lia).
  assert (Hscale2 : N.of_nat (length names) * (4 + w) <= N.of_nat n * (4 + w))
    by (apply N.mul_le_mono; lia).
  unfold reach_bound. nia.
Qed.

End Query.
End DomFiniteQueryCost.
