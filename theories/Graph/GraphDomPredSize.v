(** * Actual incoming-occurrence inventories

    Distinct discovered targets partition their incoming edge labels before rank filtering.
    For example, an edge occurrence can contribute to at most one settled target row.
    Builds on: prepared predecessor laws and the actual discovery-rank row transport. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSemi
  GraphDomSemiCost GraphDomTransport GraphDomVirtual GraphDomSize.
Import List.ListNotations.

Module DomPredSize.
Local Open Scope N_scope.

Local Lemma predecessor_label {V E} (q : Prepared.t V E) i e u :
  Prepared.ready q -> In (e, u) (Prepared.pred_edges q i) ->
  In e (Prepared.all_edges (Prepared.graph q)) /\
    Prepared.id_of q (Graph.target (Prepared.graph q) e) = Some i.
Proof.
  intros Hready Heu. pose proof (proj2 (proj2 Hready)) as Hq.
  destruct (Prepared.name_of q i) as [name|] eqn:Hname.
  - pose proof (Prepared.id_of_name_of q i name Hq Hname) as Hi.
    apply (Prepared.pred_agrees q Hq name i e u Hi) in Heu.
    destruct Heu as [Hsource [Hedge [Htarget Hsource_id]]]. split.
    + unfold Prepared.all_edges. apply in_flat_map.
      exists (Graph.source (Prepared.graph q) e). auto.
    + now rewrite Htarget.
  - rewrite (Prepared.pred_domain q Hq i Hname) in Heu. contradiction.
Qed.

Local Lemma append_nodup {A} (xs ys : list A) :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intro Hxs. induction Hxs as [|x rest Hfresh Hrest IH]; intros Hys Hdisjoint.
  - exact Hys.
  - cbn [app]. constructor.
    + intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      * contradiction.
      * exact (Hdisjoint x (or_introl eq_refl) Hin).
    + apply IH; [exact Hys|].
      intros y Hy. apply Hdisjoint. now right.
Qed.

Definition labels {V E} (q : Prepared.t V E) ids :=
  flat_map (fun i => map fst (Prepared.pred_edges q i)) ids.

Local Lemma labels_nodup {V E} (q : Prepared.t V E) ids :
  Prepared.ready q -> NoDup ids -> NoDup (labels q ids).
Proof.
  intros Hready Hids. induction Hids as [|i rest Hfresh Hrest IH]; [constructor|].
  unfold labels at 1. cbn [flat_map]. fold (labels q rest).
  apply append_nodup; [exact (Prepared.pred_nodup q (proj2 (proj2 Hready)) i)|exact IH|].
  intros e He Htail. apply in_map_iff in He. destruct He as [[edge u] [Heq Heu]].
  cbn [fst] in Heq. subst edge.
  unfold labels in Htail. apply in_flat_map in Htail. destruct Htail as [j [Hj He]].
  apply in_map_iff in He. destruct He as [[edge v] [Heq Hev]].
  cbn [fst] in Heq. subst edge.
  pose proof (proj2 (predecessor_label q i e u Hready Heu)) as Hi.
  pose proof (proj2 (predecessor_label q j e v Hready Hev)) as Hsame.
  assert (i = j) by congruence. now subst j.
Qed.

Local Lemma labels_length {V E} (q : Prepared.t V E) ids :
  N.of_nat (length (labels q ids)) =
    fold_right (fun i rest => N.of_nat (length (Prepared.pred_edges q i)) + rest) 0 ids.
Proof.
  induction ids as [|i rest IH]; [reflexivity|].
  unfold labels at 1. cbn [flat_map fold_right]. fold (labels q rest).
  rewrite length_app, length_map, Nat2N.inj_add, IH. reflexivity.
Qed.

(** Distinct targets inspect at most the prepared graph's actual edge inventory. *)
Theorem predecessor_mass {V E} (q : Prepared.t V E) ids :
  Prepared.ready q -> NoDup ids ->
  fold_right (fun i rest => N.of_nat (length (Prepared.pred_edges q i)) + rest) 0 ids <=
    N.of_nat (edge_count (Prepared.graph q)).
Proof.
  intros Hready Hids. rewrite <- labels_length.
  assert (Hlength : (length (labels q ids) <= length (Prepared.all_edges (Prepared.graph q)))%nat).
  { apply NoDup_incl_length; [now apply labels_nodup|].
    intros e He. unfold labels in He. apply in_flat_map in He.
    destruct He as [i [Hi He]]. apply in_map_iff in He.
    destruct He as [[edge u] [Heq Heu]]. cbn [fst] in Heq. subst edge.
    exact (proj1 (predecessor_label q i e u Hready Heu)). }
  rewrite DomSize.all_edges_length in Hlength. lia.
Qed.

Local Lemma sum_app {A} (f : A -> N) xs ys :
  fold_right (fun x rest => f x + rest) 0 (xs ++ ys) =
    fold_right (fun x rest => f x + rest) 0 xs + fold_right (fun x rest => f x + rest) 0 ys.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [app fold_right]. rewrite IH. lia.
Qed.

Local Lemma sum_rev {A} (f : A -> N) xs :
  fold_right (fun x rest => f x + rest) 0 (rev xs) =
    fold_right (fun x rest => f x + rest) 0 xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [rev]. rewrite sum_app, IH. cbn [fold_right]. lia.
Qed.

Local Lemma ranks_sum_le f (weight original : positive -> N) xs :
  (forall v, In v xs -> exists rank, f v = Some rank /\ weight rank <= original v) ->
  fold_right (fun rank rest => weight rank + rest) 0 (DomSemi.ranks_of f xs) <=
    fold_right (fun v rest => original v + rest) 0 xs.
Proof.
  induction xs as [|v rest IH]; intro Hrow; [reflexivity|].
  destruct (Hrow v (or_introl eq_refl)) as [rank [Hrank Hweight]].
  rewrite DomSemi.ranks_of_cons, Hrank. cbn [fold_right].
  specialize (IH ltac:(intros u Hu; apply Hrow; now right)). lia.
Qed.

Local Lemma filter_map_length {A B} (f : A -> option B) xs :
  (length (filter_map f xs) <= length xs)%nat.
Proof.
  unfold filter_map. induction xs as [|x rest IH]; [reflexivity|].
  cbn [fold_right]. destruct (f x); cbn [length]; lia.
Qed.

Local Lemma nat_to_N_le a b : (a <= b)%nat -> N.of_nat a <= N.of_nat b.
Proof.
  lia.
Qed.

(** Actual ranked settlement inspects at most the virtual graph's edge inventory. *)
Theorem actual_incoming_mass {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  DomSemiCost.incoming_mass (DomSemi.ranked (DomSemi.compute p))
    (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) <=
    N.of_nat (edge_count (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p))).
Proof.
  intro Hready.
  assert (Horder :
    DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)) =
      rev (DomSemi.ranks_of
        (fun v => Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))))
        (Search.preorder (DomSemi.search (DomSemi.compute p))))).
  { rewrite DomSemi.ranked_equation, DomSemi.layout_order. reflexivity. }
  unfold DomSemiCost.incoming_mass. rewrite Horder, sum_rev.
  eapply N.le_trans.
  - apply (ranks_sum_le _ _
      (fun v => N.of_nat
        (length (Prepared.pred_edges (DomSemi.prepared (DomSemi.compute p)) v))) _).
    intros v Hv. apply In_nth_error in Hv as Hposition. destruct Hposition as [index Hindex].
    exists (Pos.of_succ_nat index).
    assert (Hrank : Map.get positive_encoding v
      (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some (Pos.of_succ_nat index)).
    { apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)).
      rewrite SuccNat2Pos.id_succ. exact Hindex. }
    split; [exact Hrank|].
    rewrite Index.find_equation, (DomTransport.predecessor_row p v _ Hready Hv Hrank).
    rewrite DomSemi.ranked_predecessors_equation.
    apply nat_to_N_le. apply filter_map_length.
  - pose proof (DomVirtual.virtual_ready p Hready) as Hq.
    rewrite <- DomSemi.prepared_equation in Hq.
    pose proof (predecessor_mass (DomSemi.prepared (DomSemi.compute p))
      (Search.preorder (DomSemi.search (DomSemi.compute p))) Hq
      (Search.pre_nodup _ _ _ _ (DomSemi.search_exact p Hready))) as Hmass.
    rewrite DomSemi.prepared_equation, DomVirtual.prepared_graph in Hmass. exact Hmass.
Qed.

End DomPredSize.
