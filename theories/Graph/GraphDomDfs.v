(** * Actual ranked DFS parents and settlement order

    The layout's parent bindings and reverse pass follow the recorded search ranks exactly.
    For example, each stored parent rank is smaller than its child rank.
    Builds on: GraphDomSemi, GraphDomRankMap and public Search ordering contracts. *)

From Stdlib Require Import List PArith Arith Lia Wf_nat.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchOrder GraphReach GraphDomSpec GraphDomSemi GraphDomRankMap GraphDomPath
  GraphDomTransport GraphDomVirtual.
Import List.ListNotations.

Module DomDfs.

(** Ranked parent storage is canonical independently of graph readiness. *)
Theorem parents_wf {V E} (p : Prepared.t V E) :
  Map.wf positive_encoding (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))).
Proof.
  rewrite DomSemi.ranked_equation, DomSemi.layout_parents.
  apply DomRankMap.fold_wf. apply Map.wf_empty.
Qed.

(** Ranked parents are exactly the same labelled parent bindings converted through both actual ranks. *)
Theorem parent_spec {V E} (p : Prepared.t V E) child parent :
  Prepared.ready p ->
  (Map.get positive_encoding child (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent <->
  exists v u e,
    Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
      Some child /\
    Map.get positive_encoding v (Search.parent_edge (DomSemi.search (DomSemi.compute p))) =
      Some (e, u) /\
    Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
      Some parent).
Proof.
  intro Hready. rewrite DomSemi.ranked_equation, DomSemi.layout_parents. split.
  - intro Hget.
    pose proof (DomRankMap.fold_sound
      (fun v => Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))))
      (DomSemi.parent_rank (DomSemi.search (DomSemi.compute p)))
      (Search.preorder (DomSemi.search (DomSemi.compute p)))
      Map.empty (Map.wf_empty positive_encoding) child parent Hget) as Hsource.
    destruct Hsource as [Hempty|[v [Hv [Hrank Hparent]]]].
    + rewrite Map.get_empty in Hempty. discriminate.
    + rewrite DomSemi.parent_rank_equation in Hparent.
      destruct (Map.get positive_encoding v (Search.parent_edge (DomSemi.search (DomSemi.compute p))))
        as [[e u]|] eqn:Hvia; [|discriminate].
      exists v, u, e. auto.
  - intros [v [u [e [Hv [Hvia Hu]]]]].
    apply (DomRankMap.fold_complete
      (fun v => Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))))
      (DomSemi.parent_rank (DomSemi.search (DomSemi.compute p))) v child parent).
    + intros a b k Ha Hb. exact (DomSemi.discovery_rank_injective p a b k Hready Ha Hb).
    + exact Hv.
    + rewrite DomSemi.parent_rank_equation, Hvia. exact Hu.
    + apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hv.
      now apply nth_error_In in Hv.
    + apply Map.wf_empty.
Qed.

(** Every actual ranked DFS parent strictly decreases the child's discovery rank. *)
Theorem parent_decreases {V E} (p : Prepared.t V E) child parent :
  Prepared.ready p ->
  Map.get positive_encoding child (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent -> (parent < child)%positive.
Proof.
  intros Hready Hget. apply (parent_spec p child parent Hready) in Hget.
  destruct Hget as [v [u [e [Hv [Hvia Hu]]]]].
  exact (SearchOrder.parent_rank _ _ _ _ v e u parent child
    (DomSemi.search_exact p Hready) Hvia Hu Hv).
Qed.

(** Both endpoints of an actual ranked parent denote discovered vertices. *)
Theorem parent_vertices {V E} (p : Prepared.t V E) child parent :
  Prepared.ready p ->
  Map.get positive_encoding child (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent -> DomPath.vertex (DomSemi.compute p) child /\ DomPath.vertex (DomSemi.compute p) parent.
Proof.
  intros Hready Hget. apply (parent_spec p child parent Hready) in Hget.
  destruct Hget as [v [u [e [Hv [Hvia Hu]]]]]. split; [now exists v|now exists u].
Qed.

(** Every converted DFS parent is an actual retained labelled predecessor occurrence. *)
Theorem parent_arc {V E} (p : Prepared.t V E) child parent :
  Prepared.ready p ->
  Map.get positive_encoding child (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent -> exists e, DomSemi.ranked_arc (DomSemi.compute p) parent e child.
Proof.
  intros Hready Hget. apply (parent_spec p child parent Hready) in Hget.
  destruct Hget as [v [u [e [Hv [Hvia Hu]]]]]. exists e.
  apply (proj2 (DomTransport.ranked_arc_spec p v child e parent Hready Hv)).
  exists u. split; [|exact Hu].
  exact (proj1 (Search.parent_edge_valid _ _ _ _ (DomSemi.search_exact p Hready) v e u Hvia)).
Qed.

Local Lemma ranks_of_numbered xs f :
  forall start,
  (forall i v, nth_error xs i = Some v -> f v = Some (Pos.of_succ_nat (start + i))) ->
  DomSemi.ranks_of f xs = map Pos.of_succ_nat (seq start (length xs)).
Proof.
  induction xs as [|v rest IH]; intros start Hnumber.
  - rewrite DomSemi.ranks_of_nil. reflexivity.
  - rewrite DomSemi.ranks_of_cons, (Hnumber 0 v eq_refl), Nat.add_0_r.
    cbn [length seq map]. f_equal. apply IH.
    intros i u Hu.
    pose proof (Hnumber (S i) u Hu) as Hrank.
    replace (start + S i) with (S start + i) in Hrank by lia. exact Hrank.
Qed.

(** Reverse settlement visits exactly the dense discovery ranks in descending order. *)
Theorem settlement_order {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)) =
    rev (map Pos.of_succ_nat (seq 0 (length (Search.preorder (DomSemi.search (DomSemi.compute p)))))).
Proof.
  intro Hready. rewrite DomSemi.ranked_equation, DomSemi.layout_order.
  f_equal. apply (ranks_of_numbered _ _ 0).
  intros i v Hi.
  apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)).
  rewrite SuccNat2Pos.id_succ. exact Hi.
Qed.

(** Settlement membership is precisely the finite positive discovery-rank range. *)
Theorem settlement_member {V E} (p : Prepared.t V E) rank :
  Prepared.ready p ->
  (In rank (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) <->
    (Pos.to_nat rank <= length (Search.preorder (DomSemi.search (DomSemi.compute p))))%nat).
Proof.
  intro Hready. rewrite settlement_order by exact Hready.
  rewrite <- in_rev, in_map_iff. split.
  - intros [i [Heq Hi]]. apply in_seq in Hi. subst rank.
    rewrite SuccNat2Pos.id_succ. lia.
  - intro Hbound. exists (Nat.pred (Pos.to_nat rank)). split.
    + apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ.
      pose proof (Pos2Nat.is_pos rank). lia.
    + apply in_seq. pose proof (Pos2Nat.is_pos rank). lia.
Qed.

(** Ranked vertices are exactly the actual settlement domain. *)
Theorem vertex_member {V E} (p : Prepared.t V E) rank :
  Prepared.ready p ->
  (DomPath.vertex (DomSemi.compute p) rank <->
    In rank (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)))).
Proof.
  intro Hready. rewrite settlement_member by exact Hready. split.
  - intros [v Hv].
    apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hv.
    pose proof (nth_error_Some (Search.preorder (DomSemi.search (DomSemi.compute p)))
      (Nat.pred (Pos.to_nat rank))) as Hbound.
    assert (Hindex : (Nat.pred (Pos.to_nat rank) <
      length (Search.preorder (DomSemi.search (DomSemi.compute p))))%nat).
    { apply Hbound. congruence. }
    pose proof (Pos2Nat.is_pos rank). lia.
  - intro Hbound.
    destruct (nth_error (Search.preorder (DomSemi.search (DomSemi.compute p)))
      (Nat.pred (Pos.to_nat rank))) as [v|] eqn:Hv.
    + exists v. now apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)).
    + apply nth_error_None in Hv. pose proof (Pos2Nat.is_pos rank). lia.
Qed.

(** Strict actual parent ranks make the layout parent relation well founded. *)
Theorem parent_finite {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  well_founded (fun u v => Map.get positive_encoding v
    (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some u).
Proof.
  intro Hready. apply (well_founded_lt_compat positive Pos.to_nat).
  intros u v Hget. apply Pos2Nat.inj_lt. now apply (parent_decreases p v u).
Qed.

Local Lemma recorded_rank {V E} (p : Prepared.t V E) v :
  Prepared.ready p -> In v (Search.preorder (DomSemi.search (DomSemi.compute p))) ->
  exists rank, Map.get positive_encoding v
    (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank.
Proof.
  intros Hready Hv. apply In_nth_error in Hv. destruct Hv as [i Hi].
  exists (Pos.of_succ_nat i).
  apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)).
  rewrite SuccNat2Pos.id_succ. exact Hi.
Qed.

(** Every actual virtual entry ID names the same unique fresh root. *)
Theorem entry_id_unique {V E} (p : Prepared.t V E) v :
  Prepared.ready p ->
  In v (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p))) ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) None = Some v.
Proof.
  intros Hready Hv. pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  apply (Prepared.entry_ids_spec _ v (proj2 (proj2 Hq))) in Hv.
  destruct Hv as [n [Hentry Hname]].
  rewrite DomSemi.prepared_equation, DomVirtual.prepared_graph, DomVirtual.graph_equation
    in Hentry.
  cbn [Graph.entries] in Hentry. destruct Hentry as [Heq|Hfalse];
    [now subst n|contradiction].
Qed.

(** Rank one is never linked to a fabricated parent. *)
Theorem first_parent_none {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Map.get positive_encoding 1%positive
    (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = None.
Proof.
  intro Hready.
  destruct (Map.get positive_encoding 1%positive
    (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))))
    as [a|] eqn:Hget; [|reflexivity].
  pose proof (parent_decreases p 1%positive a Hready Hget) as Hlt.
  apply Pos2Nat.inj_lt in Hlt. pose proof (Pos2Nat.is_pos a). cbn in Hlt. lia.
Qed.

Local Lemma search_nonempty {V E} (p : Prepared.t V E) :
  Prepared.ready p -> Search.preorder (DomSemi.search (DomSemi.compute p)) <> [].
Proof.
  intro Hready. pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  pose proof (DomVirtual.root_id p Hready) as Hroot.
  rewrite <- DomSemi.prepared_equation in Hroot.
  set (root := Pos.of_succ_nat (length (Graph.nodes (Prepared.graph p)))) in *.
  assert (Hvalid : Prepared.valid_id (DomSemi.prepared (DomSemi.compute p)) root).
  { exists None. split; [|exact Hroot].
    apply (Prepared.ids_domain _ (proj2 (proj2 Hq))). now exists root. }
  assert (Hentry : In root (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p)))).
  { apply (Prepared.entry_ids_spec _ root (proj2 (proj2 Hq))). exists None.
    split; [|exact Hroot].
    rewrite DomSemi.prepared_equation, DomVirtual.prepared_graph, DomVirtual.graph_equation.
    now left. }
  assert (Hvisit : In root (Search.preorder (DomSemi.search (DomSemi.compute p)))).
  { apply (Search.pre_complete _ _ _ _ (DomSemi.search_exact p Hready)).
    exists root, []. split; [exact Hentry|].
    constructor; [exact Hvalid|apply Reach.admits_unrestricted]. }
  intro Hempty. rewrite Hempty in Hvisit. contradiction.
Qed.

(** The actual unique virtual entry receives discovery rank one. *)
Theorem root_rank {V E} (p : Prepared.t V E) root :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) None = Some root ->
  Map.get positive_encoding root (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some 1%positive.
Proof.
  intros Hready Hroot.
  assert (Hfirst : DomPath.vertex (DomSemi.compute p) 1%positive).
  { apply (vertex_member p 1%positive Hready). apply (settlement_member p 1%positive Hready).
    pose proof (search_nonempty p Hready) as Hnonempty.
    destruct (Search.preorder (DomSemi.search (DomSemi.compute p)));
      [contradiction|cbn [List.length Pos.to_nat]; lia]. }
  destruct Hfirst as [v Hv].
  assert (Hnone : Map.get positive_encoding v
    (Search.parent_edge (DomSemi.search (DomSemi.compute p))) = None).
  { destruct (Map.get positive_encoding v (Search.parent_edge (DomSemi.search (DomSemi.compute p))))
      as [[e u]|] eqn:Hvia; [|reflexivity].
    destruct (Search.parent_edge_valid _ _ _ _ (DomSemi.search_exact p Hready) v e u Hvia)
      as [Harc [Hu Hvisited]].
    destruct (recorded_rank p u Hready Hu) as [parent Hparent].
    assert (Hget : Map.get positive_encoding 1%positive
      (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some parent).
    { apply (parent_spec p 1%positive parent Hready). exists v, u, e. auto. }
    rewrite first_parent_none in Hget by exact Hready. discriminate. }
  assert (Hvisit : In v (Search.preorder (DomSemi.search (DomSemi.compute p)))).
  { apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hv.
    now apply nth_error_In in Hv. }
  pose proof (Search.parent_roots _ _ _ _ (DomSemi.search_exact p Hready) v Hvisit Hnone) as Hentry.
  pose proof (entry_id_unique p v Hready Hentry) as Hname.
  assert (v = root) by congruence. now subst v.
Qed.

(** Every discovered rank except the unique entry has an actual ranked DFS parent. *)
Theorem parent_none_iff {V E} (p : Prepared.t V E) rank :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) rank ->
  (Map.get positive_encoding rank (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = None <->
    rank = 1%positive).
Proof.
  intros Hready [v Hv]. split; [|intro Heq; subst rank; now apply first_parent_none].
  intro Hnone.
  assert (Hraw_none : Map.get positive_encoding v
    (Search.parent_edge (DomSemi.search (DomSemi.compute p))) = None).
  { destruct (Map.get positive_encoding v (Search.parent_edge (DomSemi.search (DomSemi.compute p))))
      as [[e u]|] eqn:Hvia; [|reflexivity].
    destruct (Search.parent_edge_valid _ _ _ _ (DomSemi.search_exact p Hready) v e u Hvia)
      as [Harc [Hu Hvisited]].
    destruct (recorded_rank p u Hready Hu) as [parent Hparent].
    assert (Hget : Map.get positive_encoding rank
      (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some parent).
    { apply (parent_spec p rank parent Hready). exists v, u, e. auto. }
    congruence. }
  assert (Hvisit : In v (Search.preorder (DomSemi.search (DomSemi.compute p)))).
  { apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hv.
    now apply nth_error_In in Hv. }
  pose proof (Search.parent_roots _ _ _ _ (DomSemi.search_exact p Hready) v Hvisit Hraw_none)
    as Hentry.
  pose proof (root_rank p v Hready (entry_id_unique p v Hready Hentry)) as Hfirst.
  congruence.
Qed.

(** Every discovered ranked vertex belongs to the actual unique-entry DFS tree. *)
Theorem rooted {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  forall v, DomPath.vertex (DomSemi.compute p) v ->
  idom_ancestor (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) 1%positive v.
Proof.
  intro Hready. intro v. induction (parent_finite p Hready v) as [v Hparents IH].
  intro Hv. destruct (Map.get positive_encoding v
    (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))) as [u|] eqn:Hget.
  - eapply rt_trans; [apply (IH u)|apply rt_step; exact Hget].
    + reflexivity.
    + exact (proj2 (parent_vertices p v u Hready Hget)).
  - apply (proj1 (parent_none_iff p v Hready Hv)) in Hget. subst v. apply rt_refl.
Qed.

(** Ranked DFS ancestry is the closure of the actual converted labelled-parent map. *)
Definition ancestor {V E} (p : Prepared.t V E) :=
  idom_ancestor (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))).

Local Lemma ordered_closure (parent : positive -> positive -> Prop) :
  (forall u v, parent u v -> (u < v)%positive) ->
  forall u v, clos_refl_trans positive parent u v -> u = v \/ (u < v)%positive.
Proof.
  intros Hparent u v Hancestor.
  induction Hancestor as [u v Huv|u|u middle v Hum IHum Hmv IHmv].
  - right. now apply Hparent.
  - now left.
  - destruct IHum as [Heq|Hlt], IHmv as [Heq'|Hlt']; subst; auto.
    right. eapply Pos.lt_trans; eassumption.
Qed.

(** Actual DFS ancestry is reflexive or strictly increasing in discovery rank. *)
Theorem ancestor_order {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> ancestor p u v -> u = v \/ (u < v)%positive.
Proof.
  intros Hready Hancestor. eapply ordered_closure; [|exact Hancestor].
  intros a b Hget. exact (parent_decreases p b a Hready Hget).
Qed.

Local Lemma ancestor_vertex {V E} (p : Prepared.t V E) i j :
  Prepared.ready p -> ancestor p i j ->
  DomPath.vertex (DomSemi.compute p) j -> DomPath.vertex (DomSemi.compute p) i.
Proof.
  intros Hready Hancestor.
  induction Hancestor as [i j Hget|i|i k j Hik IHik Hkj IHkj]; intro Hj.
  - exact (proj2 (parent_vertices p j i Hready Hget)).
  - exact Hj.
  - apply IHik. now apply IHkj.
Qed.

(** Ancestors of an actual discovered rank are discovered as well. *)
Theorem ancestor_vertices {V E} (p : Prepared.t V E) i j :
  Prepared.ready p -> ancestor p i j ->
  DomPath.vertex (DomSemi.compute p) j -> DomPath.vertex (DomSemi.compute p) i.
Proof.
  apply ancestor_vertex.
Qed.

Local Lemma functional_parent_prefix (m : Map.t positive positive) u v parent :
  idom_ancestor m u v -> u <> v ->
  Map.get positive_encoding v m = Some parent -> idom_ancestor m u parent.
Proof.
  intros Hancestor Hdistinct Hparent.
  pose proof (clos_rt_rtn1 positive
    (fun a b => Map.get positive_encoding b m = Some a) u v Hancestor) as Hchain.
  inversion Hchain as [|a target Hlast Hprefix]; subst.
  - contradiction.
  - assert (a = parent) by congruence. subst a.
    exact (clos_rtn1_rt positive (fun a b => Map.get positive_encoding b m = Some a)
      u parent Hprefix).
Qed.

(** A proper ancestor of a child is an ancestor of its actual unique DFS parent. *)
Theorem ancestor_parent {V E} (p : Prepared.t V E) u v parent :
  ancestor p u v -> u <> v ->
  Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent -> ancestor p u parent.
Proof.
  apply functional_parent_prefix.
Qed.

Local Lemma ancestor_recorded {V E} (p : Prepared.t V E) i j :
  Prepared.ready p -> Search.ancestor (DomSemi.search (DomSemi.compute p)) i j ->
  In j (Search.preorder (DomSemi.search (DomSemi.compute p))) ->
  In i (Search.preorder (DomSemi.search (DomSemi.compute p))).
Proof.
  intros Hready Hancestor.
  induction Hancestor as [i j [e Hget]|i|i k j Hik IHik Hkj IHkj]; intro Hj.
  - exact (proj1 (proj2 (Search.parent_edge_valid _ _ _ _
      (DomSemi.search_exact p Hready) j e i Hget))).
  - exact Hj.
  - apply IHik. now apply IHkj.
Qed.

Local Lemma rank_to_search {V E} (p : Prepared.t V E) i j :
  Prepared.ready p -> ancestor p i j ->
  forall u v,
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some i ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some j ->
  Search.ancestor (DomSemi.search (DomSemi.compute p)) u v.
Proof.
  intros Hready Hancestor.
  induction Hancestor as [i j Hget|i|i k j Hik IHik Hkj IHkj]; intros u v Hu Hv.
  - destruct (proj1 (parent_spec p j i Hready) Hget) as [x [y [e [Hx [Hvia Hy]]]]].
    assert (x = v) by (exact (DomSemi.discovery_rank_injective p x v j Hready Hx Hv)).
    assert (y = u) by (exact (DomSemi.discovery_rank_injective p y u i Hready Hy Hu)).
    subst x y. apply rt_step. now exists e.
  - assert (u = v) by (exact (DomSemi.discovery_rank_injective p u v i Hready Hu Hv)).
    subst v. apply rt_refl.
  - destruct (ancestor_vertex p k j Hready Hkj (ex_intro _ v Hv)) as [middle Hmiddle].
    eapply rt_trans; [apply (IHik u middle); eassumption|apply (IHkj middle v); eassumption].
Qed.

Local Lemma ancestor_numbered (number : positive -> option positive)
    (parent : positive -> positive -> Prop) :
  (forall u v, parent u v -> exists rank, number u = Some rank) ->
  forall u v, clos_refl_trans positive parent u v ->
  (exists rank, number v = Some rank) -> exists rank, number u = Some rank.
Proof.
  intros Hparent u v Hancestor.
  induction Hancestor as [u v Huv|u|u middle v Hum IHum Hmv IHmv]; intro Hnumber.
  - now apply (Hparent u v).
  - exact Hnumber.
  - apply IHum. now apply IHmv.
Qed.

Local Lemma ancestry_lift (number : positive -> option positive)
    (parent ranked_parent : positive -> positive -> Prop) :
  (forall u v, parent u v -> exists rank, number u = Some rank) ->
  (forall u v i j, parent u v -> number u = Some i -> number v = Some j ->
    ranked_parent i j) ->
  forall u v, clos_refl_trans positive parent u v ->
  forall i j, number u = Some i -> number v = Some j ->
    clos_refl_trans positive ranked_parent i j.
Proof.
  intros Hnumber Hparent u v Hancestor.
  induction Hancestor as [u v Huv|u|u middle v Hum IHum Hmv IHmv]; intros i j Hi Hj.
  - apply rt_step. exact (Hparent u v i j Huv Hi Hj).
  - assert (i = j) by congruence. subst j. apply rt_refl.
  - destruct (ancestor_numbered number parent Hnumber middle v Hmv (ex_intro _ j Hj))
      as [k Hk].
    eapply rt_trans; [apply (IHum i k); eassumption|apply (IHmv k j); eassumption].
Qed.

Local Lemma search_to_rank {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> Search.ancestor (DomSemi.search (DomSemi.compute p)) u v ->
  forall i j,
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some i ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some j ->
  ancestor p i j.
Proof.
  intros Hready Hancestor i j Hi Hj.
  eapply (ancestry_lift
    (fun u => Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))))
    (fun u v => exists e, Map.get positive_encoding v
      (Search.parent_edge (DomSemi.search (DomSemi.compute p))) = Some (e, u))
    (fun a b => Map.get positive_encoding b
      (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some a)).
  - intros a b [e Hvia].
    destruct (Search.parent_edge_valid _ _ _ _ (DomSemi.search_exact p Hready) b e a Hvia)
      as [Harc [Ha Hb]].
    exact (recorded_rank p a Hready Ha).
  - intros a b x y [e Hvia] Hx Hy.
    apply (proj2 (parent_spec p y x Hready)). exists b, a, e.
    split; [exact Hy|]. split; [exact Hvia|exact Hx].
  - exact Hancestor.
  - exact Hi.
  - exact Hj.
Qed.

(** Both ancestry directions use the same actual labelled search and converted parent bindings. *)
Theorem ancestor_transport {V E} (p : Prepared.t V E) u v i j :
  Prepared.ready p ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some i ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some j ->
  (ancestor p i j <-> Search.ancestor (DomSemi.search (DomSemi.compute p)) u v).
Proof.
  intros Hready Hi Hj. split.
  - intro Hancestor. exact (rank_to_search p i j Hready Hancestor u v Hi Hj).
  - intro Hancestor. exact (search_to_rank p u v Hready Hancestor i j Hi Hj).
Qed.

Local Lemma map_injective_nodup {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinjective Hnodup. induction Hnodup as [|x rest Hfresh Hrest IH].
  - constructor.
  - cbn [map]. constructor; [|exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    apply Hinjective in Heq. subst y. contradiction.
Qed.

(** The actual reverse settlement pass processes each discovered rank once. *)
Theorem settlement_nodup {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  NoDup (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))).
Proof.
  intro Hready. rewrite settlement_order by exact Hready.
  apply NoDup_rev. apply map_injective_nodup.
  - intros i j Heq. apply (f_equal Pos.to_nat) in Heq.
    rewrite !SuccNat2Pos.id_succ in Heq. lia.
  - apply seq_NoDup.
Qed.

Local Lemma before_reverse (xs : list positive) u v :
  before xs u v -> before (rev xs) v u.
Proof.
  intros [pre [middle [post Heq]]]. subst xs.
  exists (rev post), (rev middle), (rev pre).
  rewrite rev_app_distr. cbn [rev].
  rewrite rev_app_distr. cbn [rev].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

Local Lemma before_cons (xs : list positive) x u v :
  before (x :: xs) u v -> (u = x /\ In v xs) \/ before xs u v.
Proof.
  intros [[|a pre] [middle [post Heq]]].
  - cbn [app] in Heq. injection Heq as Heq Htail. subst u.
    left. split; [reflexivity|]. rewrite Htail.
    apply in_or_app. right. now left.
  - cbn [app] in Heq. injection Heq as Heq Htail.
    right. exists pre, middle, post. exact Htail.
Qed.

Local Lemma before_seq length :
  forall start u v,
  before (map Pos.of_succ_nat (seq start length)) u v -> (u < v)%positive.
Proof.
  induction length as [|length IH]; intros start u v Hbefore.
  - cbn [seq map] in Hbefore.
    destruct Hbefore as [[|a pre] [middle [post Hfalse]]]; discriminate.
  - cbn [seq map] in Hbefore. apply before_cons in Hbefore.
    destruct Hbefore as [[-> Hv]|Hbefore].
    + apply in_map_iff in Hv. destruct Hv as [i [Heq Hi]]. subst v.
      apply in_seq in Hi. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
    + now apply IH in Hbefore.
Qed.

(** Every earlier occurrence in the actual reverse pass has strictly greater discovery rank. *)
Theorem settlement_decreases {V E} (p : Prepared.t V E) u v :
  Prepared.ready p ->
  before (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) u v -> (v < u)%positive.
Proof.
  intros Hready Hbefore. rewrite settlement_order in Hbefore by exact Hready.
  apply before_reverse in Hbefore. rewrite rev_involutive in Hbefore.
  now apply before_seq in Hbefore.
Qed.

Local Lemma ancestor_cut_ordered m :
  (forall v a, Map.get positive_encoding v m = Some a -> (a < v)%positive) ->
  forall u v, idom_ancestor m u v ->
  forall d, idom_ancestor m d v -> (d <= u)%positive -> idom_ancestor m d u.
Proof.
  intros Hdecrease u v Hancestor.
  pose proof (clos_rt_rtn1 positive
    (fun a b => Map.get positive_encoding b m = Some a) u v Hancestor) as Hchain.
  clear Hancestor.
  induction Hchain as [|parent child Hlink Hprefix IH]; intros d Hd Hle.
  - exact Hd.
  - assert (Hparent_order : (u <= parent)%positive).
    { clear IH Hd Hle Hlink d child.
      induction Hprefix as [|a b Hab Hup IHup]; [apply Pos.le_refl|].
      eapply Pos.le_trans; [exact IHup|].
      exact (Pos.lt_le_incl _ _ (Hdecrease b a Hab)). }
    assert (Hne : d <> child).
    { intro Heq. subst d. pose proof (Hdecrease child parent Hlink) as Hlt.
      apply Pos2Nat.inj_le in Hle, Hparent_order. apply Pos2Nat.inj_lt in Hlt. lia. }
    apply IH; [|exact Hle].
    pose proof (clos_rt_rtn1 positive
      (fun a b => Map.get positive_encoding b m = Some a) d child Hd) as Hdchain.
    inversion Hdchain as [|a b Hlast Hfirst]; subst; [contradiction|].
    assert (a = parent) by congruence. subst a.
    exact (clos_rtn1_rt positive
      (fun a b => Map.get positive_encoding b m = Some a) d parent Hfirst).
Qed.

(** Ancestors of one discovered branch are ordered by rank along that same parent chain. *)
Theorem ancestor_cut {V E} (p : Prepared.t V E) d u v :
  Prepared.ready p -> ancestor p d v -> ancestor p u v -> (d <= u)%positive ->
  ancestor p d u.
Proof.
  intros Hready Hd Hu Hle.
  apply (ancestor_cut_ordered (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))
    (fun v a Hget => parent_decreases p v a Hready Hget) u v Hu d Hd Hle).
Qed.

End DomDfs.
