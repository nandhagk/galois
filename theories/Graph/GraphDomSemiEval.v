(** * Evaluation at the shared reverse-pass cutoff

    Original links above a cutoff expose exactly the higher-ranked DFS ancestors.
    For example, a predecessor query minimizes the settled scores on its linked ancestor segment.
    Builds on: GraphDomLinkProof and the actual ranked DFS parent contracts. *)

From Stdlib Require Import List PArith Arith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSemi GraphDomDfs
  GraphDomPath GraphDomLink GraphDomLinkProof.
Import List.ListNotations.

Module DomSemiEval.

(** At a cutoff, original links are exactly the actual DFS parents of higher-ranked vertices. *)
Definition cut_forest {V E} (p : Prepared.t V E) cutoff st : Prop :=
  forall v parent,
  Map.get positive_encoding v (DomLink.original st) = Some parent <->
    Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
      Some parent /\ (cutoff < v)%positive.

Local Lemma cut_decreases {V E} (p : Prepared.t V E) cutoff st :
  Prepared.ready p -> cut_forest p cutoff st ->
  forall v parent, Map.get positive_encoding v (DomLink.original st) = Some parent ->
    (parent < v)%positive.
Proof.
  intros Hready Hforest v parent Hget. apply Hforest in Hget.
  exact (DomDfs.parent_decreases p v parent Hready (proj1 Hget)).
Qed.

Local Lemma root_low {V E} (p : Prepared.t V E) cutoff st v :
  Prepared.ready p -> cut_forest p cutoff st ->
  DomPath.vertex (DomSemi.compute p) v ->
  Map.get positive_encoding v (DomLink.original st) = None -> (v <= cutoff)%positive.
Proof.
  intros Hready Hforest Hv Hnone.
  destruct (Pos.leb v cutoff) eqn:Hcompare; [now apply Pos.leb_le|].
  apply Pos.leb_gt in Hcompare.
  destruct (Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))))
    as [parent|] eqn:Hparent.
  - assert (Hsome : Map.get positive_encoding v (DomLink.original st) = Some parent).
    { apply Hforest. auto. }
    congruence.
  - apply (proj1 (DomDfs.parent_none_iff p v Hready Hv)) in Hparent. subst v.
    apply Pos2Nat.inj_lt in Hcompare.
    pose proof (Pos2Nat.is_pos cutoff). cbn in Hcompare. lia.
Qed.

Local Lemma segment_ancestor {V E} (p : Prepared.t V E) cutoff st v root xs :
  cut_forest p cutoff st ->
  DomLinkProof.segment (DomLink.original st) v root xs -> DomDfs.ancestor p root v.
Proof.
  intros Hforest Hsegment.
  induction Hsegment as [v|v a root xs Hlink Htail IH].
  - apply rt_refl.
  - apply Hforest in Hlink.
    eapply rt_trans; [exact IH|apply rt_step; exact (proj1 Hlink)].
Qed.

Local Lemma segment_members {V E} (p : Prepared.t V E) cutoff st v root xs :
  Prepared.ready p -> cut_forest p cutoff st ->
  DomLinkProof.segment (DomLink.original st) v root xs ->
  forall u, In u xs ->
    (cutoff < u)%positive /\ DomPath.vertex (DomSemi.compute p) u /\ DomDfs.ancestor p u v.
Proof.
  intros Hready Hforest Hsegment.
  induction Hsegment as [v|v a root xs Hlink Htail IH]; intros u Hin; [contradiction|].
  apply Hforest in Hlink. destruct Hlink as [Hparent Hhigh].
  destruct Hin as [Heq|Hin].
  - subst u. split; [exact Hhigh|]. split.
    + exact (proj1 (DomDfs.parent_vertices p v a Hready Hparent)).
    + apply rt_refl.
  - destruct (IH u Hin) as [Hu [Hvertex Hancestor]].
    split; [exact Hu|]. split; [exact Hvertex|].
    eapply rt_trans; [exact Hancestor|apply rt_step; exact Hparent].
Qed.

Local Lemma segment_covers {V E} (p : Prepared.t V E) cutoff st v root xs :
  Prepared.ready p -> cut_forest p cutoff st ->
  DomLinkProof.segment (DomLink.original st) v root xs ->
  (root <= cutoff)%positive ->
  forall u, (cutoff < u)%positive -> DomDfs.ancestor p u v -> In u xs.
Proof.
  intros Hready Hforest Hsegment.
  induction Hsegment as [v|v a root xs Hlink Htail IH]; intros Hlow u Hhigh Hancestor.
  - destruct (DomDfs.ancestor_order p u v Hready Hancestor) as [Heq|Hlt].
    + subst u. apply Pos2Nat.inj_le in Hlow. apply Pos2Nat.inj_lt in Hhigh. lia.
    + apply Pos2Nat.inj_lt in Hlt, Hhigh. apply Pos2Nat.inj_le in Hlow. lia.
  - destruct (Pos.eq_dec u v) as [Heq|Hne]; [now left|right].
    apply Hforest in Hlink.
    apply (IH Hlow u Hhigh).
    exact (DomDfs.ancestor_parent p u v a Hancestor Hne (proj1 Hlink)).
Qed.

(** Actual evaluation minimizes every higher DFS ancestor and preserves the cutoff forest. *)
Theorem eval_minima {V E} (p : Prepared.t V E) cutoff score st v :
  Prepared.ready p ->
  DomLinkProof.valid (fun x => Cost.value (score x)) st ->
  cut_forest p cutoff st -> DomPath.vertex (DomSemi.compute p) v ->
  let '(st', best) := Cost.value (DomLink.eval_c score st v) in
  DomLink.original st' = DomLink.original st /\
    DomLinkProof.valid (fun x => Cost.value (score x)) st' /\
    ((best = v /\ (v <= cutoff)%positive) \/
      ((cutoff < best)%positive /\ DomPath.vertex (DomSemi.compute p) best /\
        DomDfs.ancestor p best v)) /\
    (Cost.value (score best) <= Cost.value (score v))%positive /\
    forall u, (cutoff < u)%positive -> DomDfs.ancestor p u v ->
      (Cost.value (score best) <= Cost.value (score u))%positive.
Proof.
  intros Hready Hvalid Hforest Hv.
  pose proof (DomLinkProof.eval_correct score st v Hvalid
    (cut_decreases p cutoff st Hready Hforest)) as Heval.
  destruct (Cost.value (DomLink.eval_c score st v)) as [st' best].
  destruct Heval as [Horiginal [Hvalid' [Hunlinked|[root [xs [Hxs [Hpath [Hroot Hminimum]]]]]]]].
  - destruct Hunlinked as [Heq Hnone]. subst best.
    pose proof (root_low p cutoff st v Hready Hforest Hv Hnone) as Hlow.
    split; [exact Horiginal|]. split; [exact Hvalid'|].
    split; [left; auto|]. split; [apply Pos.le_refl|].
    intros u Hhigh Hancestor.
    destruct (DomDfs.ancestor_order p u v Hready Hancestor) as [Heq|Hlt].
    + subst u. apply Pos2Nat.inj_le in Hlow. apply Pos2Nat.inj_lt in Hhigh. lia.
    + apply Pos2Nat.inj_le in Hlow. apply Pos2Nat.inj_lt in Hhigh, Hlt. lia.
  - destruct Hminimum as [Hin Hminimum].
    assert (Hroot_vertex : DomPath.vertex (DomSemi.compute p) root).
    { apply (DomDfs.ancestor_vertices p root v Hready
        (segment_ancestor p cutoff st v root xs Hforest Hpath)). exact Hv. }
    pose proof (root_low p cutoff st root Hready Hforest Hroot_vertex Hroot) as Hlow.
    split; [exact Horiginal|]. split; [exact Hvalid'|].
    split.
    + right. exact (segment_members p cutoff st v root xs Hready Hforest Hpath best Hin).
    + split.
      * apply Hminimum. inversion Hpath; subst; [contradiction|now left].
      * intros u Hhigh Hancestor. apply Hminimum.
        exact (segment_covers p cutoff st v root xs Hready Hforest Hpath Hlow u Hhigh Hancestor).
Qed.

End DomSemiEval.
