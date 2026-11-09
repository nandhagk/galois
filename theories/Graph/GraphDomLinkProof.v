(** * Exact compressed linked-path labels

    Shortcut labels minimize scores on original-link segments excluding their final root.
    For example, compressing a two-link chain keeps the minimum of its two nonroot vertices.
    Builds on: GraphDomLink and public canonical map update contracts. *)

From Stdlib Require Import List PArith Arith Wf_nat.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphDomLink GraphDomRank.
Import List.ListNotations.

Module DomLinkProof.

(** A segment includes its start and excludes its final endpoint. *)
Inductive segment (m : Map.t positive positive) : positive -> positive -> list positive -> Prop :=
  | SegmentNil : forall v, segment m v v []
  | SegmentCons : forall v a root xs, Map.get positive_encoding v m = Some a ->
      segment m a root xs -> segment m v root (v :: xs).

(** A minimum is an actual segment member and bounds every member's score. *)
Definition minimum (score : positive -> positive) best xs : Prop :=
  In best xs /\ forall v, In v xs -> (score best <= score v)%positive.

(** Every shortcut represents its original segment and both forests have the same roots. *)
Record valid (score : positive -> positive) (st : DomLink.t) : Prop := {
  original_wf : Map.wf positive_encoding (DomLink.original st);
  shortcut_wf : Map.wf positive_encoding (DomLink.shortcut st);
  labels_wf : Map.wf positive_encoding (DomLink.labels st);
  same_roots : forall v,
    Map.get positive_encoding v (DomLink.shortcut st) = None <->
      Map.get positive_encoding v (DomLink.original st) = None;
  shortcut_segments : forall v a, Map.get positive_encoding v (DomLink.shortcut st) = Some a ->
    exists xs, xs <> [] /\ segment (DomLink.original st) v a xs /\
      minimum score (DomLink.identity_value (DomLink.labels st) v) xs
}.

(** Empty linked forests establish every score's segment invariant without a graph premise. *)
Theorem empty_valid score : valid score DomLink.empty.
Proof.
  constructor; cbn [DomLink.empty DomLink.original DomLink.shortcut DomLink.labels].
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - intro v. reflexivity.
  - intros v a Hget. rewrite Map.get_empty in Hget. discriminate.
Qed.

Local Lemma segment_app m u v root xs ys :
  segment m u v xs -> segment m v root ys -> segment m u root (xs ++ ys).
Proof.
  intros Hfirst Hlast. induction Hfirst as [v|u a v xs Hlink Hsegment IH].
  - exact Hlast.
  - cbn [app]. eapply SegmentCons; [exact Hlink|now apply IH].
Qed.

Local Lemma segment_decreases m :
  (forall v a, Map.get positive_encoding v m = Some a -> (a < v)%positive) ->
  forall v a xs, segment m v a xs -> (xs = [] /\ v = a) \/ (a < v)%positive.
Proof.
  intros Hrank v a xs Hsegment.
  induction Hsegment as [v|v b a xs Hlink Hsegment IH].
  - now left.
  - right. destruct IH as [[Hempty Heq]|Hlt].
    + subst a. now apply Hrank.
    + eapply Pos.lt_trans; [exact Hlt|now apply Hrank].
Qed.

Local Lemma shortcut_decreases score st :
  valid score st ->
  (forall v a, Map.get positive_encoding v (DomLink.original st) = Some a -> (a < v)%positive) ->
  forall v a, Map.get positive_encoding v (DomLink.shortcut st) = Some a -> (a < v)%positive.
Proof.
  intros Hvalid Hrank v a Hget.
  destruct (shortcut_segments _ _ Hvalid v a Hget) as [xs [Hnonempty [Hsegment Hminimum]]].
  destruct (segment_decreases _ Hrank v a xs Hsegment) as [[Hempty Heq]|Hlt];
    [contradiction|exact Hlt].
Qed.

(** Binary minimum selection always returns one of its actual two inputs. *)
Theorem minimum_member score u v :
  Cost.value (DomLink.minimum_c score u v) = u \/
    Cost.value (DomLink.minimum_c score u v) = v.
Proof.
  rewrite DomLink.minimum_value.
  destruct (Pos.compare (Cost.value (score u)) (Cost.value (score v))); auto.
Qed.

(** The selected input bounds both supplied scores, including ties. *)
Theorem minimum_bounds score u v :
  (Cost.value (score (Cost.value (DomLink.minimum_c score u v))) <= Cost.value (score u))%positive /\
  (Cost.value (score (Cost.value (DomLink.minimum_c score u v))) <= Cost.value (score v))%positive.
Proof.
  rewrite DomLink.minimum_value.
  destruct (Pos.compare (Cost.value (score u)) (Cost.value (score v))) eqn:Hcompare.
  - apply Pos.compare_eq_iff in Hcompare. rewrite Hcompare. split; apply Pos.le_refl.
  - apply Pos.compare_lt_iff in Hcompare. split; [apply Pos.le_refl|now apply Pos.lt_le_incl].
  - apply Pos.compare_gt_iff in Hcompare. split; [now apply Pos.lt_le_incl|apply Pos.le_refl].
Qed.

Local Lemma minimum_app score u v xs ys :
  minimum (fun x => Cost.value (score x)) u xs ->
  minimum (fun x => Cost.value (score x)) v ys ->
  minimum (fun x => Cost.value (score x)) (Cost.value (DomLink.minimum_c score u v)) (xs ++ ys).
Proof.
  intros [Hu Hmin_u] [Hv Hmin_v]. split.
  - destruct (minimum_member score u v) as [Heq|Heq]; rewrite Heq; apply in_or_app; auto.
  - intros w Hw. apply in_app_or in Hw.
    destruct (minimum_bounds score u v) as [Hleft Hright].
    destruct Hw as [Hw|Hw].
    + eapply Pos.le_trans; [exact Hleft|now apply Hmin_u].
    + eapply Pos.le_trans; [exact Hright|now apply Hmin_v].
Qed.

Definition update st v root best :=
  DomLink.Links (DomLink.original st)
    (Map.set positive_encoding v root (DomLink.shortcut st))
    (Map.set positive_encoding v best (DomLink.labels st)).

Local Lemma update_valid score st v root best xs :
  valid score st -> xs <> [] -> segment (DomLink.original st) v root xs ->
  minimum score best xs -> valid score (update st v root best).
Proof.
  intros Hvalid Hnonempty Hsegment Hminimum. constructor.
  - exact (original_wf _ _ Hvalid).
  - cbn [update DomLink.shortcut]. apply Map.wf_set. exact (shortcut_wf _ _ Hvalid).
  - cbn [update DomLink.labels]. apply Map.wf_set. exact (labels_wf _ _ Hvalid).
  - intro x. cbn [update DomLink.original DomLink.shortcut].
    destruct (Pos.eq_dec x v) as [->|Hne].
    + rewrite Map.get_set_same by exact (shortcut_wf _ _ Hvalid).
      split; [discriminate|]. intro Hnone.
      inversion Hsegment; subst; [contradiction|congruence].
    + rewrite Map.get_set_other by
        (try exact positive_encoding_laws; try exact (shortcut_wf _ _ Hvalid); exact Hne).
      apply (same_roots _ _ Hvalid).
  - intros x a Hget. cbn [update DomLink.shortcut] in Hget.
    destruct (Pos.eq_dec x v) as [->|Hne].
    + rewrite Map.get_set_same in Hget by exact (shortcut_wf _ _ Hvalid).
      injection Hget as <-. exists xs. split; [exact Hnonempty|].
      split; [exact Hsegment|].
      rewrite DomLink.identity_value_equation. cbn [update DomLink.labels].
      rewrite Map.get_set_same by exact (labels_wf _ _ Hvalid). exact Hminimum.
    + rewrite Map.get_set_other in Hget by
        (try exact positive_encoding_laws; try exact (shortcut_wf _ _ Hvalid); exact Hne).
      destruct (shortcut_segments _ _ Hvalid x a Hget) as [ys [Hys [Hpath Hmin]]].
      exists ys. split; [exact Hys|]. split; [exact Hpath|].
      rewrite DomLink.identity_value_equation. cbn [update DomLink.labels].
      rewrite Map.get_set_other by
        (try exact positive_encoding_laws; try exact (labels_wf _ _ Hvalid); exact Hne).
      rewrite <- DomLink.identity_value_equation. exact Hmin.
Qed.

Local Lemma segment_extend m v parent :
  Map.wf positive_encoding m -> Map.get positive_encoding v m = None ->
  forall u root xs, segment m u root xs ->
    segment (Map.set positive_encoding v parent m) u root xs.
Proof.
  intros Hmap Hnone u root xs Hsegment.
  induction Hsegment as [u|u a root xs Hlink Hsegment IH]; [constructor|].
  eapply SegmentCons; [|exact IH].
  rewrite Map.get_set_other; [exact Hlink|exact positive_encoding_laws|exact Hmap|].
  congruence.
Qed.

(** Linking a previously unlinked vertex preserves every original segment and its score minimum. *)
Theorem link_valid score st v parent :
  valid score st -> Map.get positive_encoding v (DomLink.original st) = None ->
  valid score (Cost.value (DomLink.link_c st v parent)).
Proof.
  intros Hvalid Hnone. rewrite DomLink.link_value. constructor.
  - cbn [DomLink.original]. apply Map.wf_set. exact (original_wf _ _ Hvalid).
  - cbn [DomLink.shortcut]. apply Map.wf_set. exact (shortcut_wf _ _ Hvalid).
  - cbn [DomLink.labels]. apply Map.wf_set. exact (labels_wf _ _ Hvalid).
  - intro x. cbn [DomLink.original DomLink.shortcut].
    destruct (Pos.eq_dec x v) as [->|Hne].
    + rewrite !Map.get_set_same by
        first [exact (original_wf _ _ Hvalid)|exact (shortcut_wf _ _ Hvalid)].
      reflexivity.
    + rewrite !Map.get_set_other by
        first [exact positive_encoding_laws|exact (original_wf _ _ Hvalid)|
          exact (shortcut_wf _ _ Hvalid)|exact Hne].
      apply (same_roots _ _ Hvalid).
  - intros x a Hget. cbn [DomLink.original DomLink.shortcut] in Hget |- *.
    destruct (Pos.eq_dec x v) as [->|Hne].
    + rewrite Map.get_set_same in Hget by exact (shortcut_wf _ _ Hvalid).
      injection Hget as <-. exists [v]. split; [discriminate|]. split.
      * eapply SegmentCons.
        -- apply Map.get_set_same. exact (original_wf _ _ Hvalid).
        -- constructor.
      * rewrite DomLink.identity_value_equation. cbn [DomLink.labels].
        rewrite Map.get_set_same by exact (labels_wf _ _ Hvalid).
        split; [now left|]. intros x [<-|Hfalse]; [apply Pos.le_refl|contradiction].
    + rewrite Map.get_set_other in Hget by
        (try exact positive_encoding_laws; try exact (shortcut_wf _ _ Hvalid); exact Hne).
      destruct (shortcut_segments _ _ Hvalid x a Hget) as [xs [Hxs [Hpath Hmin]]].
      exists xs. split; [exact Hxs|]. split.
      * apply segment_extend; [exact (original_wf _ _ Hvalid)|exact Hnone|exact Hpath].
      * rewrite DomLink.identity_value_equation. cbn [DomLink.labels].
        rewrite Map.get_set_other by
          (try exact positive_encoding_laws; try exact (labels_wf _ _ Hvalid); exact Hne).
        rewrite <- DomLink.identity_value_equation. exact Hmin.
Qed.

Local Lemma segment_linked m v root xs :
  segment m v root xs -> forall u, In u xs -> exists a, Map.get positive_encoding u m = Some a.
Proof.
  intro Hsegment. induction Hsegment as [v|v a root xs Hlink Hsegment IH];
    intros u Hin; [contradiction|].
  destruct Hin as [<-|Hin]; [now exists a|now apply IH].
Qed.

(** Changing scores only at unlinked roots preserves all existing root-excluding segment minima. *)
Theorem rescore_valid score score' st :
  valid score st ->
  (forall v a, Map.get positive_encoding v (DomLink.original st) = Some a ->
    score' v = score v) ->
  valid score' st.
Proof.
  intros Hvalid Hagree. constructor.
  - exact (original_wf _ _ Hvalid).
  - exact (shortcut_wf _ _ Hvalid).
  - exact (labels_wf _ _ Hvalid).
  - exact (same_roots _ _ Hvalid).
  - intros v a Hget.
    destruct (shortcut_segments _ _ Hvalid v a Hget) as [xs [Hxs [Hpath [Hin Hmin]]]].
    exists xs. split; [exact Hxs|]. split; [exact Hpath|]. split; [exact Hin|].
    intros u Hu.
    destruct (segment_linked _ _ _ _ Hpath _ Hin) as [b Hbest].
    destruct (segment_linked _ _ _ _ Hpath _ Hu) as [c Hmember].
    rewrite (Hagree _ _ Hbest), (Hagree _ _ Hmember). now apply Hmin.
Qed.

(** Compression's result describes its actual original path and root-excluding selected minimum. *)
Definition query_valid (score : positive -> positive) st v (answer : DomLink.query) : Prop :=
  let '(st', (root, part)) := answer in
  DomLink.original st' = DomLink.original st /\ valid score st' /\
    Map.get positive_encoding root (DomLink.original st) = None /\
    exists xs, segment (DomLink.original st) v root xs /\
      match part with
      | None => xs = []
      | Some best => xs <> [] /\ minimum score best xs
      end.

(** The actual rank-decreasing compression preserves segments and returns their exact minimum. *)
Theorem compress_correct score st :
  valid (fun x => Cost.value (score x)) st ->
  (forall v a, Map.get positive_encoding v (DomLink.original st) = Some a -> (a < v)%positive) ->
  forall v, query_valid (fun x => Cost.value (score x)) st v
    (Cost.value (DomLink.compress_c score st v)).
Proof.
  intros Hvalid Hrank.
  apply (well_founded_induction (well_founded_ltof positive Pos.to_nat)).
  intros v IH. rewrite DomLink.compress_value.
  destruct (Map.get positive_encoding v (DomLink.shortcut st)) as [a|] eqn:Hlink.
  - pose proof (shortcut_decreases _ _ Hvalid Hrank v a Hlink) as Hlt.
    apply Pos2Nat.inj_lt in Hlt.
    destruct (Cost.value (DomRank.smaller_c a v)) as [Hsmaller|Hnot]; [|contradiction].
    specialize (IH a Hsmaller).
    destruct (Cost.value (DomLink.compress_c score st a)) as [st' [root part]] eqn:Hrun.
    cbn [query_valid] in IH.
    destruct IH as [Horiginal [Hvalid' [Hroot [ys [Hrest Hmin_rest]]]]].
    destruct (shortcut_segments _ _ Hvalid v a Hlink) as [xs [Hxs [Hsegment Hlabel]]].
    assert (Hwhole : segment (DomLink.original st) v root (xs ++ ys))
      by (eapply segment_app; eauto).
    assert (Hnonempty : xs ++ ys <> []).
    { intro Heq. apply app_eq_nil in Heq. tauto. }
    destruct part as [best|].
    + destruct Hmin_rest as [Hys Hbest].
      pose proof (minimum_app score _ _ _ _ Hlabel Hbest) as Hcombined.
      cbn [query_valid]. split; [exact Horiginal|]. split.
      * apply update_valid with (xs := xs ++ ys); try assumption.
        rewrite Horiginal. exact Hwhole.
      * split; [exact Hroot|]. exists (xs ++ ys). auto.
    + subst ys. rewrite app_nil_r in Hwhole.
      cbn [query_valid]. split; [exact Horiginal|]. split.
      * apply update_valid with (xs := xs); try assumption.
        rewrite Horiginal. exact Hwhole.
      * split; [exact Hroot|]. exists xs. auto.
  - cbn [query_valid]. split; [reflexivity|]. split; [exact Hvalid|]. split.
    + apply (proj1 (same_roots _ _ Hvalid v)). exact Hlink.
    + exists []. split; [constructor|reflexivity].
Qed.

(** Evaluation returns either the actual unlinked start or the minimum on its nonempty original path. *)
Theorem eval_correct score st v :
  valid (fun x => Cost.value (score x)) st ->
  (forall v a, Map.get positive_encoding v (DomLink.original st) = Some a -> (a < v)%positive) ->
  let '(st', best) := Cost.value (DomLink.eval_c score st v) in
  DomLink.original st' = DomLink.original st /\
    valid (fun x => Cost.value (score x)) st' /\
    ((best = v /\ Map.get positive_encoding v (DomLink.original st) = None) \/
      exists root xs, xs <> [] /\ segment (DomLink.original st) v root xs /\
        Map.get positive_encoding root (DomLink.original st) = None /\
        minimum (fun x => Cost.value (score x)) best xs).
Proof.
  intros Hvalid Hrank.
  pose proof (compress_correct score st Hvalid Hrank v) as Hquery.
  rewrite DomLink.eval_value.
  destruct (Cost.value (DomLink.compress_c score st v)) as [st' [root part]].
  cbn [query_valid] in Hquery.
  destruct Hquery as [Horiginal [Hvalid' [Hroot [xs [Hpath Hminimum]]]]].
  split; [exact Horiginal|]. split; [exact Hvalid'|].
  destruct part as [best|].
  - right. destruct Hminimum as [Hnonempty Hmin]. exists root, xs. auto.
  - subst xs. inversion Hpath; subst root. left. auto.
Qed.

End DomLinkProof.
