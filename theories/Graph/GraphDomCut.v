(** * Closed cuts of the shared DFS parent tree

    A cut forbids settled semidominators from crossing a chosen ancestor rank.
    For example, a diamond's branch is a closed cut for its join.
    Builds on: GraphDomDfs and the actual GraphDomSemiExact settlement theorem. *)

From Stdlib Require Import PArith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSemi GraphDomLink
  GraphDomPath GraphDomDfs GraphDomSemiExact.

Module DomCut.

(** The cut score reads the same settled semidominator map used by both actual finishers. *)
Definition score {V E} (p : Prepared.t V E) :=
  DomLink.identity_value (DomSemi.semis (DomSemi.settled (DomSemi.compute p))).

(** A closed ancestor cut admits no higher ancestor whose semidominator falls below the cut. *)
Definition cut {V E} (p : Prepared.t V E) d n : Prop :=
  DomDfs.ancestor p d n /\
    forall w, DomDfs.ancestor p w n -> (d < w)%positive -> (d <= score p w)%positive.

(** A strict parent is discovered, decreases rank and represents exactly its child's strict cuts. *)
Definition parent_property {V E} (p : Prepared.t V E) v a : Prop :=
  DomPath.vertex (DomSemi.compute p) a /\ (a < v)%positive /\
    forall d, cut p d v /\ d <> v <-> cut p d a.

(** Every actual nonroot score is a strict ancestor and has the independently specified minimum. *)
Theorem score_exact {V E} (p : Prepared.t V E) n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n -> n <> 1%positive ->
  DomSemiExact.semidominator p (score p n) n /\
    (score p n < n)%positive /\ DomDfs.ancestor p (score p n) n.
Proof.
  intros Hready Hn Hnonroot.
  pose proof (DomSemiExact.semidominator_value p n Hready Hn Hnonroot) as Hsemi.
  split; [exact Hsemi|]. split.
  - exact (DomSemiExact.semidominator_bound p _ n Hready Hnonroot Hsemi).
  - exact (DomSemiExact.semidominator_ancestor p _ n Hready Hnonroot Hsemi).
Qed.

Local Lemma ancestor_le {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> DomDfs.ancestor p u v -> (u <= v)%positive.
Proof.
  intros Hready Hancestor.
  destruct (DomDfs.ancestor_order p u v Hready Hancestor) as [->|Hlt];
    [apply Pos.le_refl|now apply Pos.lt_le_incl].
Qed.

(** Every rank is its own closed ancestor cut. *)
Theorem cut_refl {V E} (p : Prepared.t V E) n :
  Prepared.ready p -> cut p n n.
Proof.
  intro Hready. split; [apply rt_refl|]. intros w Hancestor Hlt.
  pose proof (ancestor_le p w n Hready Hancestor) as Hle.
  exact (False_rect _ (Pos.lt_irrefl n (Pos.lt_le_trans _ _ _ Hlt Hle))).
Qed.

(** Restricting a closed cut to an intervening ancestor preserves its closure. *)
Theorem cut_prefix {V E} (p : Prepared.t V E) d u v :
  Prepared.ready p -> cut p d v -> DomDfs.ancestor p u v -> (d <= u)%positive -> cut p d u.
Proof.
  intros Hready [Hd Hcuts] Hu Hle. split.
  - exact (DomDfs.ancestor_cut p d u v Hready Hd Hu Hle).
  - intros w Hw Hlt. apply Hcuts; [|exact Hlt]. eapply rt_trans; eassumption.
Qed.

(** A strict closed ancestor lies no higher than the endpoint's semidominator score. *)
Theorem cut_bound {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> cut p d n -> d <> n -> (d <= score p n)%positive.
Proof.
  intros Hready [Hd Hcuts] Hne. apply Hcuts; [apply rt_refl|].
  destruct (DomDfs.ancestor_order p d n Hready Hd) as [Heq|Hlt]; [contradiction|exact Hlt].
Qed.

(** Closed cuts compose along the same actual DFS branch. *)
Theorem cut_trans {V E} (p : Prepared.t V E) a b c :
  Prepared.ready p -> cut p a b -> cut p b c -> cut p a c.
Proof.
  intros Hready [Hab Hcuts_ab] [Hbc Hcuts_bc]. split; [eapply rt_trans; eassumption|].
  intros w Hw Haw. destruct (Pos.leb w b) eqn:Hcompare.
  - apply Pos.leb_le in Hcompare. apply Hcuts_ab; [|exact Haw].
    exact (DomDfs.ancestor_cut p w b c Hready Hw Hbc Hcompare).
  - apply Pos.leb_gt in Hcompare. eapply Pos.le_trans.
    + exact (ancestor_le p a b Hready Hab).
    + exact (Hcuts_bc w Hw Hcompare).
Qed.

(** A nonroot's strict cuts are its DFS parent's cuts below its actual semidominator score. *)
Theorem cut_parent {V E} (p : Prepared.t V E) n parent d :
  Prepared.ready p ->
  Map.get positive_encoding n (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent ->
  (cut p d n /\ d <> n <-> cut p d parent /\ (d <= score p n)%positive).
Proof.
  intros Hready Hparent.
  assert (Hedge : DomDfs.ancestor p parent n) by (apply rt_step; exact Hparent).
  pose proof (DomDfs.parent_decreases p n parent Hready Hparent) as Hrank.
  split.
  - intros [Hcut Hne]. split.
    + apply (cut_prefix p d parent n Hready Hcut Hedge).
      apply (ancestor_le p d parent Hready).
      exact (DomDfs.ancestor_parent p d n parent (proj1 Hcut) Hne Hparent).
    + exact (cut_bound p d n Hready Hcut Hne).
  - intros [[Hd Hcuts] Hbound]. split.
    + split; [eapply rt_trans; eassumption|].
      intros w Hw Hhigh. destruct (Pos.eq_dec w n) as [->|Hne]; [exact Hbound|].
      apply Hcuts; [|exact Hhigh].
      exact (DomDfs.ancestor_parent p w n parent Hw Hne Hparent).
    + intro Heq. subst d. pose proof (ancestor_le p n parent Hready Hd) as Hle.
      exact (Pos.lt_irrefl parent (Pos.lt_le_trans _ _ _ Hrank Hle)).
Qed.

(** The two Semi-NCA inputs have exactly the child's strict closed cuts in common. *)
Theorem common_cuts {V E} (p : Prepared.t V E) n parent d :
  Prepared.ready p ->
  Map.get positive_encoding n (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) =
    Some parent ->
  (cut p d n /\ d <> n <-> cut p d parent /\ cut p d (score p n)).
Proof.
  intros Hready Hparent. rewrite (cut_parent p n parent d Hready Hparent).
  pose proof (proj1 (DomDfs.parent_vertices p n parent Hready Hparent)) as Hn.
  assert (Hnonroot : n <> 1%positive).
  { intro Heq. subst n. rewrite (DomDfs.first_parent_none p Hready) in Hparent. discriminate. }
  destruct (score_exact p n Hready Hn Hnonroot) as [Hsemi [Hrank Hancestor]].
  assert (Hsemi_parent : DomDfs.ancestor p (score p n) parent).
  { apply (DomDfs.ancestor_parent p _ n parent Hancestor); [|exact Hparent].
    intro Heq. rewrite Heq in Hrank. exact (Pos.lt_irrefl n Hrank). }
  split.
  - intros [Hcut Hbound]. split; [exact Hcut|].
    exact (cut_prefix p d (score p n) parent Hready Hcut Hsemi_parent Hbound).
  - intros [Hcut [Hanc Hcuts]]. split; [exact Hcut|exact (ancestor_le p d _ Hready Hanc)].
Qed.

(** The same strict-cut parent law identifies one unique parent rank. *)
Theorem parent_unique {V E} (p : Prepared.t V E) v a b :
  Prepared.ready p -> parent_property p v a -> parent_property p v b -> a = b.
Proof.
  intros Hready [Ha [Hrank_a Hlaw_a]] [Hb [Hrank_b Hlaw_b]].
  pose proof (proj1 (Hlaw_b a) (proj2 (Hlaw_a a) (cut_refl p a Hready))) as Hab.
  pose proof (proj1 (Hlaw_a b) (proj2 (Hlaw_b b) (cut_refl p b Hready))) as Hba.
  apply Pos.le_antisym.
  - exact (ancestor_le p a b Hready (proj1 Hab)).
  - exact (ancestor_le p b a Hready (proj1 Hba)).
Qed.

End DomCut.
