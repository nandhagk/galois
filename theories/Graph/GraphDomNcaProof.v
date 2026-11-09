(** * Exact closed cuts of the actual Semi-NCA finisher

    The forward walk removes precisely the closed cuts above its supplied threshold.
    For example, the diamond join inherits its branching ancestor's cut set.
    Builds on: GraphDomCut and the public value equations of GraphDomNca. *)

From Stdlib Require Import List PArith Arith Lia Wf_nat.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSpec GraphDomSemi
  GraphDomLink GraphDomRank GraphDomPath GraphDomDfs GraphDomCut GraphDomNca
  GraphDomCutTransport GraphCheckDom GraphDomVirtual GraphDomParents.
Import List.ListNotations.

Module DomNcaProof.

(** A produced parent's cuts are precisely the strict cuts of its child. *)
Definition parent_property {V E} (p : Prepared.t V E) v a :=
  DomCut.parent_property p v a.

(** Every stored binding has its proved cut law and every processed nonroot is present. *)
Record valid {V E} (p : Prepared.t V E) done m : Prop := {
  map_wf : Map.wf positive_encoding m;
  map_sound : forall v a, Map.get positive_encoding v m = Some a ->
    In v done /\ DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ parent_property p v a;
  map_total : forall v, In v done -> DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
    exists a, Map.get positive_encoding v m = Some a
}.

Local Lemma ancestor_le {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> DomDfs.ancestor p u v -> (u <= v)%positive.
Proof.
  intros Hready Hancestor. destruct (DomDfs.ancestor_order p u v Hready Hancestor) as [->|Hlt];
    [apply Pos.le_refl|now apply Pos.lt_le_incl].
Qed.

(** The actual threshold walk retains exactly the current vertex's closed cuts below its limit. *)
Theorem walk_correct {V E} (p : Prepared.t V E) done m current limit :
  Prepared.ready p -> valid p done m ->
  (forall u, DomPath.vertex (DomSemi.compute p) u -> (u < current)%positive -> In u done) ->
  forall v, DomPath.vertex (DomSemi.compute p) v -> (v < current)%positive ->
  let a := Cost.value (DomNca.walk_c limit m v) in
  DomPath.vertex (DomSemi.compute p) a /\ (a <= v)%positive /\ (a <= limit)%positive /\
    forall d, DomCut.cut p d v /\ (d <= limit)%positive <-> DomCut.cut p d a.
Proof.
  intros Hready Hvalid Hprior.
  refine (well_founded_induction (well_founded_ltof positive Pos.to_nat)
    (fun v => DomPath.vertex (DomSemi.compute p) v -> (v < current)%positive ->
      let a := Cost.value (DomNca.walk_c limit m v) in
      DomPath.vertex (DomSemi.compute p) a /\ (a <= v)%positive /\ (a <= limit)%positive /\
        forall d, DomCut.cut p d v /\ (d <= limit)%positive <-> DomCut.cut p d a) _).
  intros v IH Hv Hbefore. rewrite DomNca.walk_value.
  destruct (Pos.compare v limit) eqn:Hcompare.
  - apply Pos.compare_eq_iff in Hcompare. subst limit.
    split; [exact Hv|]. split; [apply Pos.le_refl|]. split; [apply Pos.le_refl|].
    intro d. split; [tauto|]. intro Hcut. split; [exact Hcut|].
    exact (ancestor_le p d v Hready (proj1 Hcut)).
  - apply Pos.compare_lt_iff in Hcompare.
    split; [exact Hv|]. split; [apply Pos.le_refl|]. split; [now apply Pos.lt_le_incl|].
    intro d. split; [tauto|]. intro Hcut. split; [exact Hcut|].
    eapply Pos.le_trans; [exact (ancestor_le p d v Hready (proj1 Hcut))|].
    now apply Pos.lt_le_incl.
  - apply Pos.compare_gt_iff in Hcompare.
    assert (Hnonroot : v <> 1%positive).
    { intro Heq. subst v. apply Pos2Nat.inj_lt in Hcompare.
      pose proof (Pos2Nat.is_pos limit). cbn in Hcompare. lia. }
    destruct (map_total _ _ _ Hvalid v (Hprior v Hv Hbefore) Hv Hnonroot) as [b Hparent].
    rewrite Hparent.
    destruct (map_sound _ _ _ Hvalid v b Hparent) as [Hin [Hv' [Hnonroot' [Hb [Hrank Hlaw]]]]].
    destruct (Cost.value (DomRank.smaller_c b v)) as [Hdecrease|Hnot].
    + destruct (IH b Hdecrease Hb (Pos.lt_trans _ _ _ Hrank Hbefore))
        as [Ha [Hav [Halimit Hresult]]].
      split; [exact Ha|]. split.
      * eapply Pos.le_trans; [exact Hav|now apply Pos.lt_le_incl].
      * split; [exact Halimit|]. intro d. rewrite <- Hresult. split.
        -- intros [Hcut Hbound]. split; [apply (proj1 (Hlaw d)); split; [exact Hcut|]|exact Hbound].
           intro Heq. subst d.
           exact (Pos.lt_irrefl limit (Pos.lt_le_trans _ _ _ Hcompare Hbound)).
        -- intros [Hcut Hbound]. split; [exact (proj1 (proj2 (Hlaw d) Hcut))|exact Hbound].
    + exfalso. apply Hnot. now apply Pos2Nat.inj_lt.
Qed.

Local Lemma step_parent {V E} (p : Prepared.t V E) done m v parent :
  Prepared.ready p -> valid p done m -> DomPath.vertex (DomSemi.compute p) v ->
  Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent ->
  (forall u, DomPath.vertex (DomSemi.compute p) u -> (u < v)%positive -> In u done) ->
  exists a, Cost.value (DomNca.step_c (DomSemi.ranked (DomSemi.compute p))
      (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) m v) =
    Map.set positive_encoding v a m /\ parent_property p v a.
Proof.
  intros Hready Hvalid Hv Hparent Hprior.
  pose proof (proj2 (DomDfs.parent_vertices p v parent Hready Hparent)) as Hp.
  pose proof (DomDfs.parent_decreases p v parent Hready Hparent) as Hrank.
  destruct (walk_correct p done m v (DomCut.score p v) Hready Hvalid Hprior parent Hp Hrank)
    as [Ha [Hle [Hlimit Hlaw]]].
  exists (Cost.value (DomNca.walk_c (DomCut.score p v) m parent)). split.
  - rewrite DomNca.step_value, Hparent. reflexivity.
  - split; [exact Ha|]. split.
    + exact (Pos.le_lt_trans _ parent v Hle Hrank).
    + intro d. rewrite (DomCut.cut_parent p v parent d Hready Hparent). apply Hlaw.
Qed.

Local Lemma step_correct {V E} (p : Prepared.t V E) done m v :
  Prepared.ready p -> valid p done m -> DomPath.vertex (DomSemi.compute p) v ->
  (forall u, DomPath.vertex (DomSemi.compute p) u -> (u < v)%positive -> In u done) ->
  valid p (v :: done) (Cost.value (DomNca.step_c (DomSemi.ranked (DomSemi.compute p))
    (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) m v)).
Proof.
  intros Hready Hvalid Hv Hprior.
  pose proof (map_wf _ _ _ Hvalid) as Hmap.
  destruct (Map.get positive_encoding v
    (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))) as [parent|] eqn:Hparent.
  - destruct (step_parent p done m v parent Hready Hvalid Hv Hparent Hprior)
      as [a [Hstep Hproperty]]. rewrite Hstep.
    assert (Hnonroot : v <> 1%positive).
    { intro Heq. subst v. rewrite (DomDfs.first_parent_none p Hready) in Hparent. discriminate. }
    constructor.
    + now apply Map.wf_set.
    + intros x b Hget. destruct (Pos.eq_dec x v) as [->|Hne].
      * rewrite Map.get_set_same in Hget by exact Hmap. injection Hget as <-.
        split; [now left|]. auto.
      * rewrite Map.get_set_other in Hget by
          (try exact positive_encoding_laws; try exact Hmap; exact Hne).
        destruct (map_sound _ _ _ Hvalid x b Hget) as [Hin Hrest].
        split; [now right|exact Hrest].
    + intros x [Heq|Hin] Hx Hnonroot'. destruct (Pos.eq_dec x v) as [->|Hne].
      * exists a. now apply Map.get_set_same.
      * congruence.
      * destruct (map_total _ _ _ Hvalid x Hin Hx Hnonroot') as [b Hb].
        destruct (Pos.eq_dec x v) as [->|Hne].
        -- exists a. now apply Map.get_set_same.
        -- exists b. rewrite Map.get_set_other;
             [exact Hb|exact positive_encoding_laws|exact Hmap|exact Hne].
  - rewrite DomNca.step_value, Hparent.
    apply (proj1 (DomDfs.parent_none_iff p v Hready Hv)) in Hparent. subst v.
    constructor.
    + exact Hmap.
    + intros x a Hget. destruct (map_sound _ _ _ Hvalid x a Hget) as [Hin Hrest].
      split; [now right|exact Hrest].
    + intros x [Heq|Hin] Hx Hnonroot; [congruence|].
      exact (map_total _ _ _ Hvalid x Hin Hx Hnonroot).
Qed.

Local Lemma before_head (xs : list positive) head v :
  In v xs -> before (head :: xs) head v.
Proof.
  intro Hin. apply in_split in Hin. destruct Hin as [pre [post Heq]].
  exists [], pre, post. cbn [app]. now rewrite Heq.
Qed.

Local Lemma before_tail (xs : list positive) head u v :
  before xs u v -> before (head :: xs) u v.
Proof.
  intros [pre [middle [post Heq]]].
  exists (head :: pre), middle, post. cbn [app]. now rewrite Heq.
Qed.

Local Lemma forward_fold {V E} (p : Prepared.t V E) todo :
  Prepared.ready p ->
  (forall u v, before todo u v -> (u < v)%positive) ->
  forall done m, valid p done m ->
  (forall n, DomPath.vertex (DomSemi.compute p) n <-> In n done \/ In n todo) ->
  (forall u v, In u done -> In v todo -> (u < v)%positive) ->
  exists final, valid p final
    (fold_left (fun m v => Cost.value (DomNca.step_c (DomSemi.ranked (DomSemi.compute p))
      (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) m v)) todo m) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n final.
Proof.
  intro Hready. induction todo as [|v rest IH]; intros Horder done m Hvalid Hcover Hgap.
  - exists done. split; [exact Hvalid|].
    intros n Hn. apply Hcover in Hn. destruct Hn as [Hin|Hin]; [exact Hin|contradiction].
  - assert (Hv : DomPath.vertex (DomSemi.compute p) v).
    { apply Hcover. right. now left. }
    assert (Hprior : forall u, DomPath.vertex (DomSemi.compute p) u ->
      (u < v)%positive -> In u done).
    { intros u Hu Hlow. apply Hcover in Hu. destruct Hu as [Hin|[Heq|Hin]]; [exact Hin| |].
      - subst u. exact (False_rect _ (Pos.lt_irrefl v Hlow)).
      - pose proof (Horder v u (before_head rest v u Hin)) as Hhigh.
        exact (False_rect _ (Pos.lt_irrefl u (Pos.lt_trans _ _ _ Hlow Hhigh))). }
    cbn [fold_left].
    apply (IH (fun u w Hbefore => Horder u w (before_tail rest v u w Hbefore)) (v :: done)).
    + exact (step_correct p done m v Hready Hvalid Hv Hprior).
    + intro n. rewrite Hcover. cbn [In]. tauto.
    + intros u w [Heq|Hin] Hw.
      * subst u. exact (Horder v w (before_head rest v w Hw)).
      * apply (Hgap u w Hin). now right.
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

Local Lemma finish_valid {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  exists done, valid p done (DomNca.finish (DomSemi.compute p)) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n done.
Proof.
  intro Hready. rewrite DomNca.finish_value.
  refine (forward_fold p (rev (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))))
    Hready _ [] Map.empty _ _ _).
  - intros u v Hbefore.
    apply before_reverse in Hbefore. rewrite rev_involutive in Hbefore.
    exact (DomDfs.settlement_decreases p v u Hready Hbefore).
  - constructor.
    + apply Map.wf_empty.
    + intros v a Hget. rewrite Map.get_empty in Hget. discriminate.
    + intros v Hin. contradiction.
  - intro n. rewrite (DomDfs.vertex_member p n Hready), <- in_rev. cbn [In]. tauto.
  - intros u v Hin. contradiction.
Qed.

(** Every actual Semi-NCA binding has its exact cut law and every discovered nonroot has a parent. *)
Theorem finish_parents {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  (forall v a, Map.get positive_encoding v (DomNca.finish (DomSemi.compute p)) = Some a ->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ parent_property p v a) /\
  (forall v, DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
    exists a, Map.get positive_encoding v (DomNca.finish (DomSemi.compute p)) = Some a).
Proof.
  intro Hready. destruct (finish_valid p Hready) as [done [Hvalid Hall]]. split.
  - intros v a Hget. exact (proj2 (map_sound _ _ _ Hvalid v a Hget)).
  - intros v Hv Hnonroot. exact (map_total _ _ _ Hvalid v (Hall v Hv) Hv Hnonroot).
Qed.

(** The actual Semi-NCA map contains precisely the discovered ranks other than the virtual root. *)
Theorem finish_domain {V E} (p : Prepared.t V E) v :
  Prepared.ready p ->
  ((exists a, Map.get positive_encoding v (DomNca.finish (DomSemi.compute p)) = Some a) <->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive).
Proof.
  intro Hready. destruct (finish_parents p Hready) as [Hsound Htotal]. split.
  - intros [a Hget]. destruct (Hsound v a Hget) as [Hv [Hnonroot Hrest]]. auto.
  - intros [Hv Hnonroot]. exact (Htotal v Hv Hnonroot).
Qed.

(** Actual Semi-NCA parent bindings descend strictly in numeric rank on every computational key. *)
Theorem finish_well_founded {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  well_founded (fun a v => Map.get positive_encoding v (DomNca.finish (DomSemi.compute p)) = Some a).
Proof.
  intro Hready.
  refine (well_founded_induction (well_founded_ltof positive Pos.to_nat)
    (fun v => Acc (fun a v => Map.get positive_encoding v
      (DomNca.finish (DomSemi.compute p)) = Some a) v) _).
  intros v IH. constructor. intros a Hget. apply IH.
  destruct (proj1 (finish_parents p Hready) v a Hget) as [Hv [Hnonroot [Ha [Hrank Hlaw]]]].
  now apply Pos2Nat.inj_lt.
Qed.

Local Lemma ancestry_sound {V E} (p : Prepared.t V E) m :
  Prepared.ready p ->
  (forall v a, Map.get positive_encoding v m = Some a -> DomCut.cut p a v) ->
  forall d n, idom_ancestor m d n -> DomCut.cut p d n.
Proof.
  intros Hready Hbinding d n Hancestor.
  induction Hancestor as [d n Hget|n|d u n Hfirst IHfirst Hlast IHlast].
  - exact (Hbinding n d Hget).
  - now apply DomCut.cut_refl.
  - exact (DomCut.cut_trans p d u n Hready IHfirst IHlast).
Qed.

(** The actual Semi-NCA parent forest's ancestors coincide with closed cuts at every discovered target. *)
Theorem finish_cuts {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n ->
  (idom_ancestor (DomNca.finish (DomSemi.compute p)) d n <-> DomCut.cut p d n).
Proof.
  intros Hready Hn. destruct (finish_parents p Hready) as [Hsound Htotal]. split.
  - apply (ancestry_sound p _ Hready). intros v a Hget.
    destruct (Hsound v a Hget) as [Hv [Hnonroot [Ha [Hrank Hlaw]]]].
    exact (proj1 (proj2 (Hlaw a) (DomCut.cut_refl p a Hready))).
  - revert n Hn.
    refine (well_founded_induction (well_founded_ltof positive Pos.to_nat)
      (fun n => DomPath.vertex (DomSemi.compute p) n -> DomCut.cut p d n ->
        idom_ancestor (DomNca.finish (DomSemi.compute p)) d n) _).
    intros n IH Hn Hcut. destruct (Pos.eq_dec d n) as [->|Hne]; [apply rt_refl|].
    assert (Hnonroot : n <> 1%positive).
    { intro Heq. subst n.
      pose proof (ancestor_le p d 1%positive Hready (proj1 Hcut)) as Hle.
      apply Pos2Nat.inj_le in Hle.
      pose proof (Pos2Nat.is_pos d). cbn in Hle.
      apply Hne. apply Pos2Nat.inj. cbn. lia. }
    destruct (Htotal n Hn Hnonroot) as [a Hget].
    destruct (Hsound n a Hget) as [Hn' [Hnonroot' [Ha [Hrank Hlaw]]]].
    eapply rt_trans; [apply (IH a)|apply rt_step; exact Hget].
    + now apply Pos2Nat.inj_lt.
    + exact Ha.
    + apply (proj1 (Hlaw d)). split; assumption.
Qed.

(** The actual Semi-NCA forest represents the fixed dominance predicate at named discovered endpoints. *)
Theorem finish_dominates {V E} (p : Prepared.t V E) d n deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) d = Some deleted ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some target ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  (idom_ancestor (DomNca.finish (DomSemi.compute p)) rank_deleted rank_target <->
    dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n).
Proof.
  intros Hready Hd Hn Hdeleted Htarget.
  rewrite (finish_cuts p rank_deleted rank_target Hready ltac:(now exists target)).
  exact (DomCutTransport.cut_dominates p d n deleted target rank_deleted rank_target
    Hready Hd Hn Hdeleted Htarget).
Qed.

Local Lemma binding_immediate {V E} (p : Prepared.t V E) d n deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) d = Some deleted ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some target ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  Map.get positive_encoding rank_target (DomNca.finish (DomSemi.compute p)) = Some rank_deleted ->
  immediately_dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n.
Proof.
  intros Hready Hd Hn Hdeleted Htarget Hget.
  destruct (proj1 (finish_parents p Hready) rank_target rank_deleted Hget)
    as [Hvertex [Hnonroot [Ha [Hrank Hlaw]]]].
  assert (Hdom : dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n).
  { apply (proj1 (DomCutTransport.cut_dominates p d n deleted target rank_deleted rank_target
      Hready Hd Hn Hdeleted Htarget)).
    exact (proj1 (proj2 (Hlaw rank_deleted) (DomCut.cut_refl p rank_deleted Hready))). }
  split.
  - split; [exact Hdom|]. intro Heq. subst d.
    assert (deleted = target) by congruence. subst deleted.
    assert (rank_deleted = rank_target) by congruence. subst rank_deleted.
    exact (Pos.lt_irrefl rank_target Hrank).
  - intros x [Hx Hne].
    pose proof (DomCutTransport.recorded_reachable p n target rank_target Hready Hn Htarget) as Hr.
    pose proof (DomCheck.dominator_reachable _ x n Hr Hx) as Hrx.
    destruct (DomCutTransport.reachable_rank p x Hready Hrx) as [id [rank [Hid Hpre]]].
    apply (proj1 (DomCutTransport.cut_dominates p x d id deleted rank rank_deleted
      Hready Hid Hd Hpre Hdeleted)).
    apply (proj1 (Hlaw rank)). split.
    + apply (proj2 (DomCutTransport.cut_dominates p x n id target rank rank_target
        Hready Hid Hn Hpre Htarget)). exact Hx.
    + intro Heq. subst rank. apply Hne.
      exact (DomCutTransport.named_rank_injective p x n id target rank_target
        Hready Hid Hn Hpre Htarget).
Qed.

(** Actual Semi-NCA bindings are exactly semantic immediate dominators at named discovered endpoints. *)
Theorem finish_immediate {V E} (p : Prepared.t V E) d n deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) d = Some deleted ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some target ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  (Map.get positive_encoding rank_target (DomNca.finish (DomSemi.compute p)) = Some rank_deleted <->
    immediately_dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n).
Proof.
  intros Hready Hd Hn Hdeleted Htarget. split.
  - now apply (binding_immediate p d n deleted target rank_deleted rank_target).
  - intro Himmediate.
    assert (Hcut : DomCut.cut p rank_deleted rank_target).
    { apply (proj2 (DomCutTransport.cut_dominates p d n deleted target rank_deleted rank_target
        Hready Hd Hn Hdeleted Htarget)). exact (proj1 (proj1 Himmediate)). }
    assert (Hdistinct : rank_deleted <> rank_target).
    { intro Heq. subst rank_deleted. apply (proj2 (proj1 Himmediate)).
      exact (DomCutTransport.named_rank_injective p d n deleted target rank_target
        Hready Hd Hn Hdeleted Htarget). }
    assert (Hnonroot : rank_target <> 1%positive).
    { intro Heq. subst rank_target.
      pose proof (ancestor_le p rank_deleted 1%positive Hready (proj1 Hcut)) as Hle.
      apply Pos2Nat.inj_le in Hle. pose proof (Pos2Nat.is_pos rank_deleted). cbn in Hle.
      apply Hdistinct. apply Pos2Nat.inj. cbn. lia. }
    destruct (proj2 (finish_parents p Hready) rank_target ltac:(now exists target) Hnonroot)
      as [a Hget].
    pose proof (proj1 (proj2 (proj2 (proj1 (finish_parents p Hready)
      rank_target a Hget)))) as Ha.
    destruct (DomCutTransport.vertex_name p a Hready Ha) as [name [id [Hid Hpre]]].
    pose proof (binding_immediate p name n id target a rank_target
      Hready Hid Hn Hpre Htarget Hget) as Hother.
    pose proof (DomVirtual.virtual_ready p Hready) as Hq.
    rewrite <- DomSemi.prepared_equation in Hq.
    pose proof (DomParents.immediate_unique _ d name n Hq
      (DomCutTransport.recorded_reachable p n target rank_target Hready Hn Htarget)
      Himmediate Hother) as Heq.
    subst name. assert (id = deleted) by congruence. subst id.
    assert (a = rank_deleted) by congruence. now subst a.
Qed.

End DomNcaProof.
