(** * White-path closure of actual ranked DFS subtrees

    A retained edge cannot leave a subtree for a target ranked at or after its root.
    For example, a path whose targets stay above a cutoff stays under that cutoff's DFS ancestor.
    Builds on: public Search.white_path and the actual ranked ancestry and arc transports. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchOrder GraphReach GraphDomSemi GraphDomDfs GraphDomPath GraphDomTransport.
Import List.ListNotations.

Module DomDfsPath.

Local Lemma before_indices {A} (xs : list A) u v :
  before xs u v ->
  exists i j, (i < j)%nat /\ nth_error xs i = Some u /\ nth_error xs j = Some v.
Proof.
  intros [pre [middle [post Heq]]]. subst xs.
  exists (length pre), (length pre + S (length middle)).
  split; [lia|]. split.
  - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - rewrite nth_error_app2 by lia.
    replace (length pre + S (length middle) - length pre)%nat
      with (S (length middle)) by lia.
    cbn [nth_error]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Local Lemma before_from_indices {A} (xs : list A) :
  forall i j u v, (i < j)%nat -> nth_error xs i = Some u -> nth_error xs j = Some v ->
  before xs u v.
Proof.
  induction xs as [|x rest IH]; intros [|i] [|j] u v Hlt Hu Hv;
    cbn [nth_error] in Hu, Hv; try discriminate; try lia.
  - injection Hu as <-. apply nth_error_In in Hv.
    apply in_split in Hv. destruct Hv as [middle [post Heq]].
    exists [], middle, post. cbn [app]. now rewrite Heq.
  - destruct (IH i j u v ltac:(lia) Hu Hv) as [pre [middle [post Heq]]].
    exists (x :: pre), middle, post. cbn [app]. now rewrite Heq.
Qed.

Local Lemma rank_before {V E} (q : Prepared.t V E) scope roots r u v a b :
  Search.exact q scope roots r ->
  Map.get positive_encoding u (Search.pre_num r) = Some a ->
  Map.get positive_encoding v (Search.pre_num r) = Some b ->
  (before (Search.preorder r) u v <-> (a < b)%positive).
Proof.
  intros Hsearch Ha Hb. split.
  - intro Hbefore. destruct (before_indices _ _ _ Hbefore) as [i [j [Hlt [Hi Hj]]]].
    assert (Hai : Map.get positive_encoding u (Search.pre_num r) = Some (Pos.of_succ_nat i)).
    { apply (Search.pre_num_index _ _ _ _ Hsearch). rewrite SuccNat2Pos.id_succ. exact Hi. }
    assert (Hbj : Map.get positive_encoding v (Search.pre_num r) = Some (Pos.of_succ_nat j)).
    { apply (Search.pre_num_index _ _ _ _ Hsearch). rewrite SuccNat2Pos.id_succ. exact Hj. }
    assert (a = Pos.of_succ_nat i) by congruence.
    assert (b = Pos.of_succ_nat j) by congruence.
    subst a b. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  - intro Hlt. apply (Search.pre_num_index _ _ _ _ Hsearch) in Ha, Hb.
    apply (before_from_indices _ (Nat.pred (Pos.to_nat a)) (Nat.pred (Pos.to_nat b))
      u v); try assumption.
    apply Pos2Nat.inj_lt in Hlt. pose proof (Pos2Nat.is_pos a). lia.
Qed.

Local Lemma arc_source_unique {V E} (q : Prepared.t V E) u e v x y :
  Prepared.arc q u e v -> Prepared.arc q x e y -> u = x.
Proof.
  intros [a [b [Ha [Hia [Hib [Hs [Ht He]]]]]]]
    [c [d [Hc [Hic [Hid [Hs' [Ht' He']]]]]]].
  assert (a = c) by congruence. subst c. congruence.
Qed.

Local Lemma scoped_snoc {V E} (q : Prepared.t V E) scope u es v e z :
  Search.scoped_path q scope u es v -> Prepared.arc q v e z ->
  Prepared.valid_id q z -> Scope.admits scope z = true ->
  Search.scoped_path q scope u (es ++ [e]) z.
Proof.
  intros Hpath Hedge Hz Hallowed.
  induction Hpath as [v Hv Hallow|u a v es target Hu Hallow Huv Htail IH]; cbn [app].
  - econstructor; [exact Hv|exact Hallow|exact Hedge|now constructor].
  - econstructor; [exact Hu|exact Hallow|exact Huv|now apply IH].
Qed.

Local Lemma recorded {V E} (q : Prepared.t V E) scope roots r u a :
  Search.exact q scope roots r ->
  Map.get positive_encoding u (Search.pre_num r) = Some a -> In u (Search.preorder r).
Proof.
  intros Hsearch Ha. apply (Search.pre_num_index _ _ _ _ Hsearch) in Ha.
  now apply nth_error_In in Ha.
Qed.

Local Lemma white_extension {V E} (q : Prepared.t V E) roots r a u v e first current target :
  Search.exact q Reach.unrestricted roots r ->
  Map.get positive_encoding a (Search.pre_num r) = Some first ->
  Map.get positive_encoding u (Search.pre_num r) = Some current ->
  Map.get positive_encoding v (Search.pre_num r) = Some target ->
  Search.ancestor r a u -> Prepared.arc q u e v ->
  (first <= target)%positive -> Search.ancestor r a v.
Proof.
  intros Hsearch Ha Hu Hv Hancestor Hedge Hbound.
  pose proof (recorded _ _ _ _ _ _ Hsearch Ha) as Hvisited_a.
  pose proof (recorded _ _ _ _ _ _ Hsearch Hu) as Hvisited_u.
  pose proof (recorded _ _ _ _ _ _ Hsearch Hv) as Hvisited_v.
  destruct (proj1 (Search.white_path _ _ _ _ Hsearch a u Hvisited_a Hvisited_u) Hancestor)
    as [es [Hpath [Horder Hwhite]]].
  apply (proj2 (Search.white_path _ _ _ _ Hsearch a v Hvisited_a Hvisited_v)).
  exists (es ++ [e]). split.
  - apply scoped_snoc with (v := u).
    + exact Hpath.
    + exact Hedge.
    + exact (proj1 (SearchOrder.recorded_admitted _ _ _ _ v Hsearch Hvisited_v)).
    + apply Reach.admits_unrestricted.
  - split.
    + apply Pos.lt_eq_cases in Hbound. destruct Hbound as [Hlt|Heq].
      * right. apply (rank_before _ _ _ _ a v first target Hsearch Ha Hv). exact Hlt.
      * left. subst target.
        apply (Search.pre_num_index _ _ _ _ Hsearch) in Ha, Hv. congruence.
    + intros x label y Hin Hxy. apply in_app_or in Hin.
      destruct Hin as [Hin|[Heq|Hfalse]].
      * exact (Hwhite x label y Hin Hxy).
      * subst label. assert (x = u) by (symmetry; exact (arc_source_unique q u e v x y Hedge Hxy)).
        subst x. exact Horder.
      * contradiction.
Qed.

(** A ranked edge stays under its DFS ancestor whenever its target stays above that ancestor's rank. *)
Theorem subtree_edge {V E} (p : Prepared.t V E) a u v e :
  Prepared.ready p ->
  DomPath.vertex (DomSemi.compute p) a ->
  DomPath.vertex (DomSemi.compute p) u ->
  DomPath.vertex (DomSemi.compute p) v ->
  DomDfs.ancestor p a u -> DomSemi.ranked_arc (DomSemi.compute p) u e v ->
  (a <= v)%positive -> DomDfs.ancestor p a v.
Proof.
  intros Hready [raw_a Ha] [raw_u Hu] [raw_v Hv] Hancestor Hedge Hbound.
  apply (proj1 (DomDfs.ancestor_transport p raw_a raw_u a u Hready Ha Hu)) in Hancestor.
  apply (proj1 (DomTransport.ranked_arc_spec p raw_v v e u Hready Hv)) in Hedge.
  destruct Hedge as [source [Harc Hsource]].
  assert (source = raw_u) by
    (exact (DomSemi.discovery_rank_injective p source raw_u u Hready Hsource Hu)).
  subst source.
  apply (proj2 (DomDfs.ancestor_transport p raw_a raw_v a v Hready Ha Hv)).
  exact (white_extension _ _ _ raw_a raw_u raw_v e a u v
    (DomSemi.search_exact p Hready) Ha Hu Hv Hancestor Harc Hbound).
Qed.

End DomDfsPath.
