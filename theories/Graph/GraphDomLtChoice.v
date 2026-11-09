(** * Exact provisional LT parent choices

    A minimum below a bucket root either settles the parent or defers to an earlier vertex.
    For example, a deferred diamond-join choice inherits an earlier vertex's strict cuts.
    Builds on: GraphDomCut, GraphDomSemiEval and the actual LT member equation. *)

From Stdlib Require Import PArith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSemi GraphDomPath
  GraphDomDfs GraphDomCut GraphDomSemiEval GraphDomLink GraphDomLinkProof GraphDomLt.

Module DomLtChoice.

(** The chosen representative minimizes settled scores on the actual branch below the bucket root. *)
Definition segment_minimum {V E} (p : Prepared.t V E) s v u :=
  DomDfs.ancestor p u v /\ (s < u)%positive /\
    forall w, DomDfs.ancestor p w v -> (s < w)%positive ->
      (DomCut.score p u <= DomCut.score p w)%positive.

Local Lemma ancestor_le {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> DomDfs.ancestor p u v -> (u <= v)%positive.
Proof.
  intros Hready Hancestor.
  destruct (DomDfs.ancestor_order p u v Hready Hancestor) as [->|Hlt];
    [apply Pos.le_refl|now apply Pos.lt_le_incl].
Qed.

Local Lemma settled_parent {V E} (p : Prepared.t V E) v u :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
  segment_minimum p (DomCut.score p v) v u ->
  (DomCut.score p v <= DomCut.score p u)%positive ->
  forall d, DomCut.cut p d v /\ d <> v <-> DomCut.cut p d (DomCut.score p v).
Proof.
  intros Hready Hv Hnonroot [Huv [Hsu Hminimum]] Hgood d.
  destruct (DomCut.score_exact p v Hready Hv Hnonroot) as [Hsemi [Hrank Hsv]].
  split.
  - intros [Hcut Hdistinct].
    apply (DomCut.cut_prefix p d _ v Hready Hcut Hsv).
    exact (DomCut.cut_bound p d v Hready Hcut Hdistinct).
  - intros [Hd Hcuts]. split.
    + split; [eapply rt_trans; eassumption|].
      intros w Hw Hdw. destruct (Pos.leb w (DomCut.score p v)) eqn:Hcompare.
      * apply Pos.leb_le in Hcompare. apply Hcuts; [|exact Hdw].
        exact (DomDfs.ancestor_cut p w _ v Hready Hw Hsv Hcompare).
      * apply Pos.leb_gt in Hcompare. eapply Pos.le_trans.
        -- exact (ancestor_le p d _ Hready Hd).
        -- eapply Pos.le_trans; [exact Hgood|exact (Hminimum w Hw Hcompare)].
    + intro Heq. subst d. pose proof (ancestor_le p v _ Hready Hd) as Hle.
      exact (Pos.lt_irrefl v (Pos.le_lt_trans _ _ _ Hle Hrank)).
Qed.

Local Lemma deferred_parent {V E} (p : Prepared.t V E) v u :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
  segment_minimum p (DomCut.score p v) v u ->
  (DomCut.score p u < DomCut.score p v)%positive ->
  forall d, DomCut.cut p d v /\ d <> v <-> DomCut.cut p d u /\ d <> u.
Proof.
  intros Hready Hv Hnonroot [Huv [Hsu Hminimum]] Hlow d. split.
  - intros [Hcut Hdistinct].
    pose proof (DomCut.cut_bound p d v Hready Hcut Hdistinct) as Hbound. split.
    + apply (DomCut.cut_prefix p d u v Hready Hcut Huv).
      eapply Pos.le_trans; [exact Hbound|now apply Pos.lt_le_incl].
    + intro Heq. subst d.
      exact (Pos.lt_irrefl u (Pos.le_lt_trans _ _ _ Hbound Hsu)).
  - intros [Hcut Hdistinct].
    pose proof (DomCut.cut_bound p d u Hready Hcut Hdistinct) as Hbound.
    pose proof (Pos.le_lt_trans _ _ _ Hbound Hlow) as Hds.
    split.
    + split; [eapply rt_trans; [exact (proj1 Hcut)|exact Huv]|].
      intros w Hw Hdw. destruct (Pos.leb w (DomCut.score p v)) eqn:Hcompare.
      * apply Pos.leb_le in Hcompare. apply (proj2 Hcut); [|exact Hdw].
        apply (DomDfs.ancestor_cut p w u v Hready Hw Huv).
        eapply Pos.le_trans; [exact Hcompare|now apply Pos.lt_le_incl].
      * apply Pos.leb_gt in Hcompare.
        eapply Pos.le_trans; [exact Hbound|exact (Hminimum w Hw Hcompare)].
    + intro Heq. subst d.
      pose proof (ancestor_le p u v Hready Huv) as Hle.
      exact (Pos.lt_irrefl v (Pos.lt_le_trans _ _ _
        (Pos.lt_trans _ _ _ Hds Hsu) Hle)).
Qed.

(** A provisional parent either settles to the semidominator or inherits an earlier nonroot's strict cuts. *)
Definition parent_choice {V E} (p : Prepared.t V E) v a :=
  (a = DomCut.score p v /\ forall d, DomCut.cut p d v /\ d <> v <-> DomCut.cut p d a) \/
  (a <> DomCut.score p v /\ DomPath.vertex (DomSemi.compute p) a /\ a <> 1%positive /\
    (a < v)%positive /\ forall d, DomCut.cut p d v /\ d <> v <-> DomCut.cut p d a /\ d <> a).

(** The actual comparison of a segment minimum yields the exact provisional correction law. *)
Theorem minimum_choice {V E} (p : Prepared.t V E) s v u :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
  DomCut.score p v = s -> segment_minimum p s v u ->
  parent_choice p v
    (match Pos.compare (DomCut.score p u) s with
    | Lt => u
    | _ => s
    end).
Proof.
  intros Hready Hv Hnonroot Hsemi Hminimum. subst s.
  destruct (Pos.compare (DomCut.score p u) (DomCut.score p v)) eqn:Hcompare.
  - apply Pos.compare_eq_iff in Hcompare. left. split; [reflexivity|].
    apply (settled_parent p v u Hready Hv Hnonroot Hminimum).
    rewrite Hcompare. apply Pos.le_refl.
  - apply Pos.compare_lt_iff in Hcompare.
    destruct Hminimum as [Huv [Hsu Hminimum]]. right. split.
    + intro Heq. rewrite Heq in Hsu. exact (Pos.lt_irrefl _ Hsu).
    + split; [exact (DomDfs.ancestor_vertices p u v Hready Huv Hv)|].
      split.
      * intro Heq. subst u. apply Pos2Nat.inj_lt in Hsu.
        pose proof (Pos2Nat.is_pos (DomCut.score p v)). cbn in Hsu. lia.
      * split.
        -- destruct (DomDfs.ancestor_order p u v Hready Huv) as [Heq|Hlt]; [|exact Hlt].
           rewrite Heq in Hcompare. exact (False_rect _ (Pos.lt_irrefl _ Hcompare)).
        -- apply (deferred_parent p v u Hready Hv Hnonroot); [|exact Hcompare].
           split; [exact Huv|]. auto.
  - apply Pos.compare_gt_iff in Hcompare. left. split; [reflexivity|].
    apply (settled_parent p v u Hready Hv Hnonroot Hminimum).
    now apply Pos.lt_le_incl.
Qed.

(** The real bucket member operation preserves linked minima and stores an exact provisional choice. *)
Theorem bucket_query {V E} (p : Prepared.t V E) s v st :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
  DomCut.score p v = s ->
  DomLinkProof.valid (DomCut.score p) (DomLt.links st) ->
  DomSemiEval.cut_forest p s (DomLt.links st) ->
  let st' := Cost.value (DomLt.member_c
    (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) s st v) in
  DomLink.original (DomLt.links st') = DomLink.original (DomLt.links st) /\
    DomLinkProof.valid (DomCut.score p) (DomLt.links st') /\
    exists a, DomLt.provisional st' = Map.set positive_encoding v a (DomLt.provisional st) /\
      parent_choice p v a.
Proof.
  intros Hready Hv Hnonroot Hsemi Hvalid Hforest.
  pose proof (DomSemiEval.eval_minima p s
    (DomLink.identity_value_c (DomSemi.semis (DomSemi.settled (DomSemi.compute p))))
    (DomLt.links st) v Hready Hvalid Hforest Hv) as Hquery.
  rewrite DomLt.member_value.
  destruct (Cost.value (DomLink.eval_c
    (DomLink.identity_value_c (DomSemi.semis (DomSemi.settled (DomSemi.compute p))))
    (DomLt.links st) v)) as [links u].
  destruct Hquery as [Horiginal [Hvalid' [Hposition [Hbound Hminimum]]]].
  cbn [DomLt.links DomLt.provisional]. split; [exact Horiginal|].
  split; [exact Hvalid'|]. eexists. split; [reflexivity|].
  apply (minimum_choice p s v u Hready Hv Hnonroot Hsemi).
  destruct Hposition as [[Heq Hlow]|[Hhigh [Hu Hancestor]]].
  - subst u. pose proof (proj1 (proj2 (DomCut.score_exact p v Hready Hv Hnonroot))) as Hlt.
    rewrite Hsemi in Hlt. exact (False_rect _ (Pos.lt_irrefl s (Pos.lt_le_trans _ _ _ Hlt Hlow))).
  - split; [exact Hancestor|]. split; [exact Hhigh|].
    intros w Hw Hsw. exact (Hminimum w Hsw Hw).
Qed.

End DomLtChoice.
