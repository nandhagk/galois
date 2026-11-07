(** * Independent weak-order validation

    The checker validates tokens against rooted reachability and labelled graph arcs.
    For example, a self-loop needs an opening token at its node.
    Builds on: GraphHierSpec, GraphReach and BaseMap. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphHierSpec GraphReach.
Import List.ListNotations Wto.

Module WtoCheck.

Definition member (v : positive) xs := existsb (Pos.eqb v) xs.

Local Lemma member_spec v xs : member v xs = true <-> In v xs.
Proof.
  unfold member. rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hin. exists v. split; [exact Hin|apply Pos.eqb_refl].
Qed.

Fixpoint unique_b (xs : list positive) :=
  match xs with
  | [] => true
  | x :: rest => negb (member x rest) && unique_b rest
  end.

Local Lemma unique_spec xs : unique_b xs = true <-> NoDup xs.
Proof.
  induction xs as [|x rest IH]; cbn [unique_b].
  - split; [intros _; constructor|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false, member_spec, IH.
    split; [intros [Hnot Hnd]; now constructor|intro H; now inversion H].
Qed.

(** Each position stores its strict suffix and its enclosing heads in one index.
    Suffix positions keep the reference proof independent of numeric rank conventions. *)
Fixpoint positions (rows : list (positive * list positive)) :
    Map.t positive (list positive * list positive) :=
  match rows with
  | [] => Map.empty
  | (v, stack) :: rest =>
    Map.set positive_encoding v (map fst rest, stack) (positions rest)
  end.

Local Lemma positions_wf rows : Map.wf positive_encoding (positions rows).
Proof.
  induction rows as [|[v stack] rest IH]; cbn [positions].
  - apply Map.wf_empty.
  - now apply Map.wf_set.
Qed.

Definition edge_b index a b :=
  match Map.get positive_encoding a index with
  | None => false
  | Some (after, stack) => member b after || member b stack
  end.

Local Lemma before_cons {A} (x a b : A) xs :
  before (x :: xs) a b <-> (x = a /\ In b xs) \/ before xs a b.
Proof.
  unfold before. split.
  - intros [[|y pre] [mid [post Heq]]].
    + cbn in Heq. injection Heq as Hx Hxs. left. split; [exact Hx|].
      rewrite Hxs. apply in_or_app. right. now left.
    + cbn in Heq. injection Heq as _ Hxs.
      right. exists pre, mid, post. exact Hxs.
  - intros [[-> Hin]|[pre [mid [post Heq]]]].
    + apply in_split in Hin. destruct Hin as [mid [post ->]].
      exists [], mid, post. reflexivity.
    + exists (x :: pre), mid, post. now cbn; rewrite Heq.
Qed.

Local Lemma before_member {A} (xs : list A) a b :
  before xs a b -> In a xs.
Proof.
  intros [pre [mid [post ->]]]. apply in_or_app. right. now left.
Qed.

Local Lemma edge_spec rows :
  NoDup (map fst rows) -> forall a b,
  (edge_b (positions rows) a b = true <->
    before (map fst rows) a b \/
    exists stack, In (a, stack) rows /\ In b stack).
Proof.
  induction rows as [|[x stack] rest IH]; intros Hnd a b.
  - unfold edge_b. cbn [positions map]. rewrite Map.get_empty.
    split; [discriminate|intros [Hbefore|[s [Hin _]]]; [|contradiction]].
    destruct Hbefore as [[|z pre] [mid [post Heq]]]; discriminate.
  - cbn [map fst] in Hnd.
    inversion Hnd as [|head tail Hfresh Htail]; subst.
    cbn [positions]. unfold edge_b at 1.
    destruct (Pos.eq_dec a x) as [->|Hne].
    + rewrite Map.get_set_same by apply positions_wf.
      cbn [map fst]. rewrite orb_true_iff, !member_spec, before_cons.
      split.
      * intros [Hafter|Hstack].
        -- left. left. auto.
        -- right. exists stack. split; [now left|exact Hstack].
      * intros [[[Heq Hafter]|Hbefore]|[s [[Heq|Hin] Hb]]].
        -- now left.
        -- exfalso. apply Hfresh. eapply before_member; eauto.
        -- injection Heq as Heq. subst s. now right.
        -- exfalso. apply Hfresh. apply in_map with (f := fst) in Hin. exact Hin.
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
        by (try apply positions_wf; exact Hne).
      fold (edge_b (positions rest) a b).
      rewrite (IH Htail). cbn [map fst]. rewrite before_cons. cbn [In]. split.
      * intros [Hbefore|[s [Hin Hb]]].
        -- left. now right.
        -- right. exists s. auto.
      * intros [[[Heq _]|Hbefore]|[s [[Heq|Hin] Hb]]].
        -- congruence.
        -- now left.
        -- injection Heq as Heq _. congruence.
        -- right. exists s. auto.
Qed.

Local Lemma annotation_order w stack : map fst (annotate stack w) = order w.
Proof.
  revert stack. induction w as [|[v|h|] rest IH]; intro stack;
    unfold annotate, order; cbn [annotate_c order_c];
    autorewrite with galois_cost; cbn [map fst]; try reflexivity.
  - change (v :: map fst (annotate stack rest) = v :: order rest).
    now rewrite IH.
  - change (h :: map fst (annotate (h :: stack) rest) = h :: order rest).
    now rewrite IH.
  - change (map fst (annotate (tl stack) rest) = order rest). apply IH.
Qed.

Definition live {V E} (p : Prepared.t V E) roots :=
  FinSet.elements (Reach.set p Reach.unrestricted roots).

Local Lemma live_spec {V E} (p : Prepared.t V E) roots v :
  Prepared.ready p ->
  (In v (live p roots) <-> Search.scoped_reachable p Reach.unrestricted roots v).
Proof.
  intro Hready. unfold live.
  rewrite (FinSet.elements_spec positive_encoding positive_encoding_laws)
    by apply Reach.set_wf.
  apply Reach.exact. exact Hready.
Qed.

(** Validated positions and exact coverage decide the unrestricted candidate contract. *)
Definition check {V E} (p : Prepared.t V E) roots w : bool :=
  let vs := order w in
  let reachable := live p roots in
  let index := positions (annotate [] w) in
  balanced_from 0 w && unique_b vs &&
  forallb (fun v => member v reachable) vs &&
  forallb (fun v => member v vs) reachable &&
  forallb (fun a => forallb (fun eb => edge_b index a (snd eb))
    (Prepared.succ_edges p a)) vs.

Local Lemma arc_successor {V E} (p : Prepared.t V E) a e b :
  Prepared.ready p -> Prepared.valid_id p a ->
  (In (e, b) (Prepared.succ_edges p a) <-> Prepared.arc p a e b).
Proof.
  intros [Hwf [_ Hp]] [x [Hx Hi]].
  rewrite (Prepared.succ_spec p x a e b Hp Hi). split.
  - intros [He Hj]. exists x, (Graph.target (Prepared.graph p) e).
    repeat split; auto. exact (out_source Hwf x e He).
  - intros [u [v [Hu [Hiu [Hiv [Hs [Ht He]]]]]]].
    assert (Hname : u = x).
    { pose proof (Prepared.name_of_id_of p x a Hp Hi).
      pose proof (Prepared.name_of_id_of p u a Hp Hiu). congruence. }
    rewrite Hname in He. split; [exact He|now rewrite Ht].
Qed.

Local Lemma reachable_valid {V E} (p : Prepared.t V E) roots a :
  Search.scoped_reachable p Reach.unrestricted roots a -> Prepared.valid_id p a.
Proof.
  intros [r [es [_ Hpath]]]. induction Hpath; auto.
Qed.

(** Acceptance is equivalent to exact rooted coverage and every forward or enclosing-head edge. *)
Theorem check_correct {V E} (p : Prepared.t V E) roots w :
  Prepared.ready p -> (check p roots w = true <-> valid p roots w).
Proof.
  intro Hready. unfold check. rewrite !andb_true_iff.
  rewrite unique_spec, !forallb_forall. split.
  - intros [[[[Hbalance Hunique] Hin] Hcover] Hedges].
    assert (Hcoverage : forall v, In v (order w) <->
      Search.scoped_reachable p Reach.unrestricted roots v).
    { intro v. rewrite <- (live_spec p roots v Hready). split.
      - intro Hv. apply member_spec, Hin. exact Hv.
      - intro Hv. apply member_spec, Hcover. exact Hv. }
    constructor; try assumption.
    intros a e b Harc Ha Hallowed.
    rewrite <- (annotation_order w []).
    apply (proj1 (edge_spec _ ltac:(rewrite annotation_order; exact Hunique) a b)).
    specialize (Hedges a Ha).
    rewrite forallb_forall in Hedges.
    apply (Hedges (e, b)).
    apply (arc_successor p a e b Hready).
    + apply reachable_valid with (roots := roots). now apply Hcoverage.
    + exact Harc.
  - intros [Hbalance Hunique Hcoverage Hedges].
    split; [split; [split; [split|]|]|]; try assumption.
    + intros v Hv. apply member_spec. apply (live_spec p roots v Hready).
      now apply Hcoverage.
    + intros v Hv. apply member_spec, Hcoverage. now apply (live_spec p roots v Hready).
    + intros a Ha. apply forallb_forall. intros [e b] Heb.
      change (edge_b (positions (annotate [] w)) a b = true).
      apply (proj2 (edge_spec _ ltac:(rewrite annotation_order; exact Hunique) a b)).
      rewrite annotation_order.
      apply (Hedges a e b); [|exact Ha|apply Reach.admits_unrestricted].
      apply (arc_successor p a e b Hready); [|exact Heb].
      apply reachable_valid with (roots := roots). now apply Hcoverage.
Qed.

(** A hand-written hierarchy is checked solely through its flattened token list. *)
Definition check_forest {V E} (p : Prepared.t V E) roots f := check p roots (of_forest f).

Arguments check {V E} p roots w : simpl never.
Arguments check_forest {V E} p roots f : simpl never.

End WtoCheck.
