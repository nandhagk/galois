(** * Actual LT forward-correction correctness

    Increasing-rank correction resolves provisional choices into exact strict-cut parents.
    For example, a deferred bucket member reads the proved parent of its earlier representative.
    Builds on: GraphDomLtReverse, shared cut laws and canonical parent-map uniqueness. *)

From Stdlib Require Import List PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSpec
  GraphDomSemi GraphDomPath GraphDomDfs GraphDomCut GraphDomLink GraphDomLt
  GraphDomLtChoice GraphDomLtReverse GraphDomNca GraphDomNcaProof.
Import List.ListNotations.

Module DomLtProof.

(** A corrected parent's cuts are precisely its child's strict cuts. *)
Definition parent_property {V E} (p : Prepared.t V E) v a :=
  DomCut.parent_property p v a.

(** The increasing prefix stores exactly processed nonroots with their proved corrected parent laws. *)
Record valid {V E} (p : Prepared.t V E) done m : Prop := {
  map_wf : Map.wf positive_encoding m;
  map_sound : forall v a, Map.get positive_encoding v m = Some a ->
    In v done /\ DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ parent_property p v a;
  map_total : forall v, In v done -> DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
    exists a, Map.get positive_encoding v m = Some a
}.

Local Lemma correct_parent {V E} (p : Prepared.t V E) done m v a :
  Prepared.ready p -> valid p done m ->
  DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
  (forall u, DomPath.vertex (DomSemi.compute p) u -> (u < v)%positive -> In u done) ->
  Map.get positive_encoding v (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) =
    Some a ->
  exists b, Cost.value (DomLt.correct_step_c
      (DomSemi.semis (DomSemi.settled (DomSemi.compute p)))
      (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) m v) =
    Map.set positive_encoding v b m /\ parent_property p v b.
Proof.
  intros Hready Hvalid Hv Hnonroot Hprior Hget.
  destruct (proj1 (proj2 (DomLtReverse.provisional_exact p Hready)) v a Hget)
    as [Hv' [Hnonroot' Hchoice]].
  rewrite DomLt.correct_step_value, Hget.
  fold (DomCut.score p v).
  destruct Hchoice as [[-> Hlaw]|[Hne [Ha [Hanonroot [Hrank Hlaw]]]]].
  - rewrite Pos.eqb_refl. exists (DomCut.score p v). split; [reflexivity|].
    destruct (DomCut.score_exact p v Hready Hv Hnonroot) as [Hsemi [Hrank Hancestor]].
    split; [exact (DomDfs.ancestor_vertices p _ v Hready Hancestor Hv)|]. auto.
  - assert (Hcompare : Pos.eqb a (DomCut.score p v) = false) by (now apply Pos.eqb_neq).
    rewrite Hcompare.
    destruct (map_total _ _ _ Hvalid a (Hprior a Ha Hrank) Ha Hanonroot) as [b Hparent].
    rewrite DomLink.identity_value_equation, Hparent.
    exists b. split; [reflexivity|].
    destruct (map_sound _ _ _ Hvalid a b Hparent) as [Hin [Ha' [Hanonroot' [Hb [Hbrank Hblaw]]]]].
    split; [exact Hb|]. split.
    + exact (Pos.lt_trans _ _ _ Hbrank Hrank).
    + intro d. rewrite Hlaw, Hblaw. reflexivity.
Qed.

Local Lemma correct_step {V E} (p : Prepared.t V E) done m v :
  Prepared.ready p -> valid p done m -> DomPath.vertex (DomSemi.compute p) v ->
  (forall u, DomPath.vertex (DomSemi.compute p) u -> (u < v)%positive -> In u done) ->
  valid p (v :: done) (Cost.value (DomLt.correct_step_c
    (DomSemi.semis (DomSemi.settled (DomSemi.compute p)))
    (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) m v)).
Proof.
  intros Hready Hvalid Hv Hprior. pose proof (map_wf _ _ _ Hvalid) as Hmap.
  destruct (Map.get positive_encoding v
    (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p)))) as [a|] eqn:Hget.
  - pose proof (proj1 (proj2 (DomLtReverse.provisional_exact p Hready)) v a Hget)
      as [Hv' [Hnonroot Hchoice]].
    destruct (correct_parent p done m v a Hready Hvalid Hv Hnonroot Hprior Hget)
      as [b [Hstep Hproperty]]. rewrite Hstep. constructor.
    + now apply Map.wf_set.
    + intros x c Hlookup. destruct (Pos.eq_dec x v) as [->|Hne].
      * rewrite Map.get_set_same in Hlookup by exact Hmap. injection Hlookup as <-.
        split; [now left|]. auto.
      * rewrite Map.get_set_other in Hlookup by
          (try exact positive_encoding_laws; try exact Hmap; exact Hne).
        destruct (map_sound _ _ _ Hvalid x c Hlookup) as [Hin Hrest].
        split; [now right|exact Hrest].
    + intros x [Heq|Hin] Hx Hnonroot'.
      * subst x. exists b. now apply Map.get_set_same.
      * destruct (Pos.eq_dec x v) as [->|Hne].
        -- exists b. now apply Map.get_set_same.
        -- destruct (map_total _ _ _ Hvalid x Hin Hx Hnonroot') as [c Hc].
           exists c. rewrite Map.get_set_other;
             [exact Hc|exact positive_encoding_laws|exact Hmap|exact Hne].
  - rewrite DomLt.correct_step_value, Hget. constructor.
    + exact Hmap.
    + intros x a Hlookup. destruct (map_sound _ _ _ Hvalid x a Hlookup) as [Hin Hrest].
      split; [now right|exact Hrest].
    + intros x [Heq|Hin] Hx Hnonroot.
      * subst x. destruct (proj2 (proj2 (DomLtReverse.provisional_exact p Hready))
          v Hx Hnonroot) as [a Ha]. congruence.
      * exact (map_total _ _ _ Hvalid x Hin Hx Hnonroot).
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
    (fold_left (fun m v => Cost.value (DomLt.correct_step_c
      (DomSemi.semis (DomSemi.settled (DomSemi.compute p)))
      (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) m v)) todo m) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n final.
Proof.
  intro Hready. induction todo as [|v rest IH]; intros Horder done m Hvalid Hcover Hgap.
  - exists done. split; [exact Hvalid|].
    intros n Hn. apply Hcover in Hn. destruct Hn as [Hin|Hin]; [exact Hin|contradiction].
  - assert (Hv : DomPath.vertex (DomSemi.compute p) v) by (apply Hcover; right; now left).
    assert (Hprior : forall u, DomPath.vertex (DomSemi.compute p) u ->
      (u < v)%positive -> In u done).
    { intros u Hu Hlow. apply Hcover in Hu. destruct Hu as [Hin|[Heq|Hin]]; [exact Hin| |].
      - subst u. exact (False_rect _ (Pos.lt_irrefl v Hlow)).
      - pose proof (Horder v u (before_head rest v u Hin)) as Hhigh.
        exact (False_rect _ (Pos.lt_irrefl u (Pos.lt_trans _ _ _ Hlow Hhigh))). }
    cbn [fold_left].
    apply (IH (fun u w Hb => Horder u w (before_tail rest v u w Hb)) (v :: done)).
    + exact (correct_step p done m v Hready Hvalid Hv Hprior).
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
  exists done, valid p done (DomLt.finish (DomSemi.compute p)) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n done.
Proof.
  intro Hready. rewrite DomLt.finish_value.
  refine (forward_fold p (rev (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))))
    Hready _ [] Map.empty _ _ _).
  - intros u v Hb. apply before_reverse in Hb. rewrite rev_involutive in Hb.
    exact (DomDfs.settlement_decreases p v u Hready Hb).
  - constructor.
    + apply Map.wf_empty.
    + intros v a Hget. rewrite Map.get_empty in Hget. discriminate.
    + intros v Hin. contradiction.
  - intro n. rewrite (DomDfs.vertex_member p n Hready), <- in_rev. cbn [In]. tauto.
  - intros u v Hin. contradiction.
Qed.

(** Every actual LT binding has its exact cut law and every discovered nonroot has a parent. *)
Theorem finish_parents {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  (forall v a, Map.get positive_encoding v (DomLt.finish (DomSemi.compute p)) = Some a ->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ parent_property p v a) /\
  (forall v, DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
    exists a, Map.get positive_encoding v (DomLt.finish (DomSemi.compute p)) = Some a).
Proof.
  intro Hready. destruct (finish_valid p Hready) as [done [Hvalid Hall]]. split.
  - intros v a Hget. exact (proj2 (map_sound _ _ _ Hvalid v a Hget)).
  - intros v Hv Hnonroot. exact (map_total _ _ _ Hvalid v (Hall v Hv) Hv Hnonroot).
Qed.

(** Independent actual LT correction laws and Semi-NCA parent laws identify the same canonical ranked map. *)
Theorem finish_agrees {V E} (p : Prepared.t V E) :
  Prepared.ready p -> DomLt.finish (DomSemi.compute p) = DomNca.finish (DomSemi.compute p).
Proof.
  intro Hready. destruct (finish_parents p Hready) as [Hlt_sound Hlt_total].
  destruct (DomNcaProof.finish_parents p Hready) as [Hnca_sound Hnca_total].
  apply (Map.ext positive_encoding positive_encoding_laws);
    [apply DomLt.finish_wf|apply DomNca.finish_wf|].
  intro v. destruct (Map.get positive_encoding v (DomLt.finish (DomSemi.compute p)))
    as [a|] eqn:Hlt.
  - destruct (Hlt_sound v a Hlt) as [Hv [Hnonroot Hproperty]].
    destruct (Hnca_total v Hv Hnonroot) as [b Hb]. rewrite Hb.
    f_equal. apply (DomCut.parent_unique p v a b Hready Hproperty).
    exact (proj2 (proj2 (Hnca_sound v b Hb))).
  - destruct (Map.get positive_encoding v (DomNca.finish (DomSemi.compute p))) as [b|] eqn:Hnca;
      [|reflexivity].
    destruct (Hnca_sound v b Hnca) as [Hv [Hnonroot Hproperty]].
    destruct (Hlt_total v Hv Hnonroot) as [a Ha]. congruence.
Qed.

(** The actual LT forest's ancestors coincide with closed cuts at every discovered target. *)
Theorem finish_cuts {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n ->
  (idom_ancestor (DomLt.finish (DomSemi.compute p)) d n <-> DomCut.cut p d n).
Proof.
  intros Hready Hn. rewrite finish_agrees by exact Hready.
  exact (DomNcaProof.finish_cuts p d n Hready Hn).
Qed.

(** Actual LT bindings are exactly semantic immediate dominators at named discovered virtual endpoints. *)
Theorem finish_immediate {V E} (p : Prepared.t V E) d n deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) d = Some deleted ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some target ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  (Map.get positive_encoding rank_target (DomLt.finish (DomSemi.compute p)) = Some rank_deleted <->
    immediately_dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n).
Proof.
  intros Hready Hd Hn Hdeleted Htarget. rewrite finish_agrees by exact Hready.
  exact (DomNcaProof.finish_immediate p d n deleted target rank_deleted rank_target
    Hready Hd Hn Hdeleted Htarget).
Qed.

End DomLtProof.
