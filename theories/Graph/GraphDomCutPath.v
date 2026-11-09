(** * Closed cuts and avoiding ranked paths

    A closed DFS cut is precisely the absence of a root path that avoids its rank.
    For example, either diamond arm avoids the other arm but cannot avoid their branch.
    Builds on: GraphDomCut and the independent high-path minimum decomposition. *)

From Stdlib Require Import List PArith Lia.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphDomSemi
  GraphDomPath GraphDomDfs GraphDomCut GraphDomSemiExact.
Import List.ListNotations.

Module DomCutPath.

(** A rank dominates a target when no actual root path avoids that rank at every visited vertex. *)
Definition no_avoiding {V E} (p : Prepared.t V E) d n : Prop :=
  forall es, DomSemiExact.bounded_path (DomSemi.compute p) (fun x => x <> d) 1%positive es n ->
    1%positive <> d -> False.

Local Lemma ancestor_le {V E} (p : Prepared.t V E) u v :
  Prepared.ready p -> DomDfs.ancestor p u v -> (u <= v)%positive.
Proof.
  intros Hready Hancestor.
  destruct (DomDfs.ancestor_order p u v Hready Hancestor) as [->|Hlt];
    [apply Pos.le_refl|now apply Pos.lt_le_incl].
Qed.

Local Lemma tree_guard {V E} (shared : DomSemi.semi V E) m :
  (forall child parent, Map.get positive_encoding child m = Some parent ->
    DomPath.vertex shared child /\ exists e, DomSemi.ranked_arc shared parent e child) ->
  forall u v, idom_ancestor m u v -> DomPath.vertex shared u ->
  exists es, DomSemiExact.bounded_path shared
    (fun x => idom_ancestor m u x /\ idom_ancestor m x v) u es v.
Proof.
  intros Hedges u v Hancestor Hu.
  pose proof (clos_rt_rtn1 positive
    (fun a b => Map.get positive_encoding b m = Some a) u v Hancestor) as Hchain.
  clear Hancestor.
  induction Hchain as [|parent child Hlink Hprefix IH].
  - exists []. now constructor.
  - destruct IH as [es Hpath]. destruct (Hedges child parent Hlink) as [Hchild [edge Hedge]].
    assert (Hstep : idom_ancestor m parent child) by (apply rt_step; exact Hlink).
    assert (Hfirst : idom_ancestor m u parent) by
      (exact (clos_rtn1_rt positive
        (fun a b => Map.get positive_encoding b m = Some a) u parent Hprefix)).
    exists (es ++ [edge]).
    apply (DomSemiExact.bounded_app shared _ u es parent [edge] child).
    + eapply (DomSemiExact.bounded_mono shared); [|exact Hpath].
      intros x [Hux Hxp]. split; [exact Hux|]. eapply rt_trans; eassumption.
    + econstructor; [exact (DomSemiExact.bounded_end _ _ _ _ _ Hpath)|exact Hedge| |].
      * split; [eapply rt_trans; eassumption|apply rt_refl].
      * now constructor.
Qed.

Local Lemma guarded_dec {V E} (shared : DomSemi.semi V E) guard u es v d :
  DomSemiExact.bounded_path shared guard u es v ->
  guard d \/ DomSemiExact.bounded_path shared (fun x => x <> d) u es v.
Proof.
  intro Hpath.
  induction Hpath as [u Hu|u e v es z Hu Hedge Hv Htail IH].
  - right. now constructor.
  - destruct (Pos.eq_dec v d) as [->|Hne]; [now left|].
    destruct IH as [Hd|Hfree]; [now left|].
    right. econstructor; eassumption.
Qed.

(** Absence of an avoiding path forces membership on the actual rooted DFS branch. *)
Theorem no_avoiding_ancestor {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n ->
  no_avoiding p d n -> DomDfs.ancestor p d n.
Proof.
  intros Hready Hn Hno.
  pose proof (DomDfs.rooted p Hready n Hn) as Hrooted.
  pose proof (DomDfs.ancestor_vertices p 1%positive n Hready Hrooted Hn) as Hroot.
  destruct (tree_guard (DomSemi.compute p) (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))
    (fun child parent Hget =>
      conj (proj1 (DomDfs.parent_vertices p child parent Hready Hget))
        (DomDfs.parent_arc p child parent Hready Hget))
    1%positive n Hrooted Hroot) as [es Htree].
  destruct (Pos.eq_dec 1%positive d) as [<-|Hne]; [exact Hrooted|].
  destruct (guarded_dec _ _ _ _ _ d Htree) as [[Hfirst Hlast]|Hfree]; [exact Hlast|].
  exact (False_rect _ (Hno es Hfree Hne)).
Qed.

(** An avoiding path to a higher ancestor would extend to an avoiding path to the dominated target. *)
Theorem no_avoiding_prefix {V E} (p : Prepared.t V E) d u v :
  Prepared.ready p -> no_avoiding p d v -> DomPath.vertex (DomSemi.compute p) u ->
  DomDfs.ancestor p u v -> (d < u)%positive -> no_avoiding p d u.
Proof.
  intros Hready Hno Hu Hancestor Hlt es Hpath Hstart.
  destruct (DomSemiExact.tree_path p u v Hready Hu Hancestor) as [suffix Hsuffix].
  apply (Hno (es ++ suffix)); [|exact Hstart].
  apply (DomSemiExact.bounded_app _ _ _ _ u); [exact Hpath|].
  eapply DomSemiExact.bounded_mono; [|exact Hsuffix].
  intros x Hbound Heq. subst x.
  exact (Pos.lt_irrefl d (Pos.lt_le_trans _ _ _ Hlt Hbound)).
Qed.

(** A strict dominator cut cannot lie above the actual endpoint's semidominator. *)
Theorem no_avoiding_score_bound {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n -> n <> 1%positive ->
  no_avoiding p d n -> d <> n -> (d <= DomCut.score p n)%positive.
Proof.
  intros Hready Hn Hnonroot Hno Hne.
  pose proof (no_avoiding_ancestor p d n Hready Hn Hno) as Hd.
  destruct (DomDfs.ancestor_order p d n Hready Hd) as [Heq|Hdn]; [contradiction|].
  destruct (DomCut.score_exact p n Hready Hn Hnonroot) as [[Hpath Hminimum] [Hscore Hancestor]].
  destruct (Pos.leb d (DomCut.score p n)) eqn:Hcompare; [now apply Pos.leb_le|].
  apply Pos.leb_gt in Hcompare.
  pose proof (proj1 (DomSemiExact.candidate_vertices p _ n Hpath)) as Hs.
  pose proof (DomDfs.rooted p Hready _ Hs) as Hrooted.
  pose proof (DomDfs.ancestor_vertices p _ _ Hready Hrooted Hs) as Hroot.
  destruct (tree_guard (DomSemi.compute p) (DomSemi.parents (DomSemi.ranked (DomSemi.compute p)))
    (fun child parent Hget =>
      conj (proj1 (DomDfs.parent_vertices p child parent Hready Hget))
        (DomDfs.parent_arc p child parent Hready Hget))
    1%positive (DomCut.score p n) Hrooted Hroot) as [prefix Hprefix].
  destruct Hpath as [suffix Hsuffix].
  exfalso. apply (Hno (prefix ++ suffix)).
  - apply (DomSemiExact.bounded_app _ _ _ _ (DomCut.score p n)).
    + eapply DomSemiExact.bounded_mono; [|exact Hprefix].
      intros x [Hfirst Hlast] Heq. subst x.
      pose proof (ancestor_le p d _ Hready Hlast) as Hle.
      exact (Pos.lt_irrefl d (Pos.le_lt_trans _ _ _ Hle Hcompare)).
    + apply (DomSemiExact.high_as_bounded _ _ _ _ _ _ Hsuffix).
      * intros x Hhigh Heq. subst x.
        exact (Pos.lt_irrefl d (Pos.lt_trans _ _ _ Hdn Hhigh)).
      * congruence.
  - intro Heq. rewrite <- Heq in Hcompare.
    apply Pos2Nat.inj_lt in Hcompare. pose proof (Pos2Nat.is_pos (DomCut.score p n)).
    cbn in Hcompare. lia.
Qed.

(** Every absent avoiding path establishes the full semidominator closure of its ancestor cut. *)
Theorem no_avoiding_cut {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n -> no_avoiding p d n ->
  DomCut.cut p d n.
Proof.
  intros Hready Hn Hno. split; [now apply no_avoiding_ancestor|].
  intros w Hw Hhigh. pose proof (DomDfs.ancestor_vertices p w n Hready Hw Hn) as Hvertex.
  apply (no_avoiding_score_bound p d w Hready Hvertex).
  - intro Heq. subst w. apply Pos2Nat.inj_lt in Hhigh.
    pose proof (Pos2Nat.is_pos d). cbn in Hhigh. lia.
  - exact (no_avoiding_prefix p d w n Hready Hno Hvertex Hw Hhigh).
  - intro Heq. subst w. exact (Pos.lt_irrefl d Hhigh).
Qed.

Local Lemma high_suffix {V E} (shared : DomSemi.semi V E) d u es n :
  DomSemiExact.bounded_path shared (fun x => x <> d) u es n ->
  (d <= n)%positive ->
  DomSemiExact.bounded_path shared (fun x => (d <= x)%positive /\ x <> d) u es n \/
    exists start suffix, (start < d)%positive /\
      DomSemiExact.bounded_path shared (fun x => (d <= x)%positive /\ x <> d) start suffix n.
Proof.
  intro Hpath.
  induction Hpath as [u Hu|u e v es z Hu Hedge Hne Htail IH]; intro Hend.
  - left. now constructor.
  - destruct (IH Hend) as [Hhigh|Hsuffix]; [|now right].
    destruct (Pos.leb d v) eqn:Hcompare.
    + apply Pos.leb_le in Hcompare. left.
      econstructor; [exact Hu|exact Hedge|auto|exact Hhigh].
    + apply Pos.leb_gt in Hcompare. right. exists v, es. auto.
Qed.

Local Lemma cut_low_suffix {V E} (p : Prepared.t V E) d n start es :
  Prepared.ready p -> DomCut.cut p d n -> (start < d)%positive ->
  DomSemiExact.bounded_path (DomSemi.compute p)
    (fun x => (d <= x)%positive /\ x <> d) start es n -> False.
Proof.
  intros Hready [Hd Hcuts] Hlow Hpath.
  assert (Hnonempty : es <> []).
  { intro Heq. subst es. inversion Hpath; subst n.
    pose proof (ancestor_le p d start Hready Hd) as Hle.
    exact (Pos.lt_irrefl d (Pos.le_lt_trans _ _ _ Hle Hlow)). }
  destruct (DomSemiExact.bounded_minimum _ _ _ _ _ Hpath Hnonempty)
    as [least [prefix [suffix [Hsplit [Hprefix [Hcandidate [Hsuffix [Hwhole [Hle Hne]]]]]]]]].
  pose proof (proj2 (DomSemiExact.high_vertices _ _ _ _ _ Hcandidate)) as Hleast.
  assert (Hhigh : (d < least)%positive).
  { apply Pos2Nat.inj_lt. apply Pos2Nat.inj_le in Hle.
    assert (Pos.to_nat d <> Pos.to_nat least) by
      (intro Heq; apply Hne; symmetry; now apply Pos2Nat.inj).
    lia. }
  assert (Hnonroot : least <> 1%positive).
  { intro Heq. subst least. apply Pos2Nat.inj_lt in Hhigh.
    pose proof (Pos2Nat.is_pos d). cbn in Hhigh. lia. }
  assert (Hancestor : DomDfs.ancestor p least n).
  { apply (DomSemiExact.bounded_region p least least suffix n Hready Hleast Hsuffix).
    apply rt_refl. }
  destruct (DomCut.score_exact p least Hready Hleast Hnonroot) as [[Hsemi Hminimum] Hrest].
  pose proof (Hcuts least Hancestor Hhigh) as Hbound.
  assert (Hcandidate' : DomSemiExact.semidom_path p start least) by (now exists prefix).
  pose proof (Hminimum start Hcandidate') as Hminimum'.
  exact (Pos.lt_irrefl d (Pos.le_lt_trans _ _ _
    (Pos.le_trans _ _ _ Hbound Hminimum') Hlow)).
Qed.

(** A closed cut excludes every actual ranked root path that avoids its rank. *)
Theorem cut_no_avoiding {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomCut.cut p d n -> no_avoiding p d n.
Proof.
  intros Hready Hcut es Hpath Hstart.
  assert (Hrootlow : (1 < d)%positive).
  { apply Pos2Nat.inj_lt. pose proof (Pos2Nat.is_pos d).
    assert (Pos.to_nat d <> 1%nat) by
      (intro Heq; apply Hstart; symmetry; apply Pos2Nat.inj; exact Heq).
    cbn. lia. }
  destruct (high_suffix _ d _ _ _ Hpath (ancestor_le p d n Hready (proj1 Hcut)))
    as [Hhigh|[start [suffix [Hlow Hsuffix]]]].
  - exact (cut_low_suffix p d n 1%positive es Hready Hcut Hrootlow Hhigh).
  - exact (cut_low_suffix p d n start suffix Hready Hcut Hlow Hsuffix).
Qed.

(** At every discovered target, closed cuts coincide with the absence of avoiding ranked root paths. *)
Theorem cut_exact {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) n ->
  (DomCut.cut p d n <-> no_avoiding p d n).
Proof.
  intros Hready Hn. split; [now apply cut_no_avoiding|now apply no_avoiding_cut].
Qed.

End DomCutPath.
