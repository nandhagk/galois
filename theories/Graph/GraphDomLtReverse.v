(** * Actual LT bucket-index and reverse-pass correctness

    Processed buckets supply exactly their provisional parents while links follow the same DFS tree.
    For example, a bucket receives each vertex at its actual stored semidominator rank.
    Builds on: GraphDomLtChoice and the public LT operation equations. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSemi GraphDomPath GraphDomDfs
  GraphDomCut GraphDomSemiExact GraphDomSemiEval GraphDomLink GraphDomLinkProof
  GraphDomLt GraphDomLtChoice.
Import List.ListNotations.

Module DomLtReverse.

Local Lemma insert_wf semis buckets v :
  Map.wf positive_encoding buckets ->
  Map.wf positive_encoding (Cost.value (DomLt.bucket_insert_c semis buckets v)).
Proof.
  intro Hmap. rewrite DomLt.bucket_insert_value.
  destruct (Map.get positive_encoding v semis); [now apply Map.wf_set|exact Hmap].
Qed.

Local Lemma insert_member semis buckets v s x :
  Map.wf positive_encoding buckets ->
  (In x (Index.find positive_encoding s (Cost.value (DomLt.bucket_insert_c semis buckets v))) <->
    In x (Index.find positive_encoding s buckets) \/
      (x = v /\ Map.get positive_encoding v semis = Some s)).
Proof.
  intro Hmap. rewrite DomLt.bucket_insert_value.
  destruct (Map.get positive_encoding v semis) as [t|] eqn:Hsemi.
  - destruct (Pos.eq_dec s t) as [->|Hne].
    + rewrite Index.find_equation, Map.get_set_same by exact Hmap.
      cbn [In]. split.
      * intros [Heq|Hin]; [right; auto|now left].
      * intros [Hin|[Heq Hsame]]; [now right|left; congruence].
    + rewrite Index.find_equation, Map.get_set_other by
        (try exact positive_encoding_laws; try exact Hmap; exact Hne).
      rewrite <- Index.find_equation. split; [now left|].
      intros [Hin|[Heq Hsame]]; [exact Hin|congruence].
  - split; [now left|]. intros [Hin|[Heq Hfalse]]; [exact Hin|discriminate].
Qed.

Local Lemma index_fold semis xs :
  forall buckets, Map.wf positive_encoding buckets ->
  let result := fold_left
    (fun buckets v => Cost.value (DomLt.bucket_insert_c semis buckets v)) xs buckets in
  Map.wf positive_encoding result /\
    forall s v, In v (Index.find positive_encoding s result) <->
      In v (Index.find positive_encoding s buckets) \/
        (In v xs /\ Map.get positive_encoding v semis = Some s).
Proof.
  induction xs as [|x rest IH]; intros buckets Hmap.
  - split; [exact Hmap|]. intros s v. cbn [fold_left In]. tauto.
  - cbn [fold_left].
    destruct (IH _ (insert_wf semis buckets x Hmap)) as [Hwf Hmembers].
    split; [exact Hwf|]. intros s v.
    rewrite Hmembers, (insert_member semis buckets x s v Hmap).
    cbn [In]. split.
    + intros [[Hin|[Heq Hsemi]]|[Hin Hsemi]].
      * now left.
      * subst v. right. auto.
      * right. auto.
    + intros [Hin|[[Heq|Hin] Hsemi]].
      * left. now left.
      * subst v. left. right. auto.
      * right. auto.
Qed.

(** The bucket index is canonical and contains exactly each input vertex with its stored semi value. *)
Theorem bucket_index_spec semis order :
  Map.wf positive_encoding (DomLt.bucket_index semis order) /\
    forall s v, In v (Index.find positive_encoding s (DomLt.bucket_index semis order)) <->
      In v order /\ Map.get positive_encoding v semis = Some s.
Proof.
  rewrite DomLt.bucket_index_value.
  destruct (index_fold semis order Map.empty (Map.wf_empty positive_encoding)) as [Hwf Hmembers].
  split; [exact Hwf|]. intros s v. rewrite Hmembers.
  rewrite Index.find_equation, Map.get_empty. cbn [In]. tauto.
Qed.

(** This observer names the exact bucket index consumed by the actual LT reverse pass. *)
Definition buckets {V E} (p : Prepared.t V E) :=
  DomLt.bucket_index (DomSemi.semis (DomSemi.settled (DomSemi.compute p)))
    (rev (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)))).

(** Actual bucket membership is precisely a discovered nonroot with that same settled score. *)
Theorem bucket_spec {V E} (p : Prepared.t V E) s v :
  Prepared.ready p ->
  (In v (Index.find positive_encoding s (buckets p)) <->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ DomCut.score p v = s).
Proof.
  intro Hready. unfold buckets. rewrite (proj2 (bucket_index_spec _ _)), <- in_rev.
  rewrite <- (DomDfs.vertex_member p v Hready).
  rewrite (DomSemiExact.semidominators_exact p v s Hready). split.
  - intros [Hv [Hv' [Hnonroot Hsemi]]]. split; [exact Hv|]. split; [exact Hnonroot|].
    exact (DomSemiExact.semidominator_unique p _ s v
      (proj1 (DomCut.score_exact p v Hready Hv Hnonroot)) Hsemi).
  - intros [Hv [Hnonroot Hscore]]. split; [exact Hv|].
    split; [exact Hv|]. split; [exact Hnonroot|].
    rewrite <- Hscore. exact (proj1 (DomCut.score_exact p v Hready Hv Hnonroot)).
Qed.

Local Lemma bucket_fold {V E} (p : Prepared.t V E) s members :
  Prepared.ready p ->
  (forall v, In v members ->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ DomCut.score p v = s) ->
  forall st,
  Map.wf positive_encoding (DomLt.provisional st) ->
  DomLinkProof.valid (DomCut.score p) (DomLt.links st) ->
  DomSemiEval.cut_forest p s (DomLt.links st) ->
  let result := fold_left (fun st v => Cost.value (DomLt.member_c
    (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) s st v)) members st in
  DomLink.original (DomLt.links result) = DomLink.original (DomLt.links st) /\
    DomLinkProof.valid (DomCut.score p) (DomLt.links result) /\
    Map.wf positive_encoding (DomLt.provisional result) /\
    (forall v a, Map.get positive_encoding v (DomLt.provisional result) = Some a ->
      Map.get positive_encoding v (DomLt.provisional st) = Some a \/
        (In v members /\ DomLtChoice.parent_choice p v a)) /\
    (forall v, (exists a, Map.get positive_encoding v (DomLt.provisional st) = Some a) \/
      In v members -> exists a, Map.get positive_encoding v (DomLt.provisional result) = Some a).
Proof.
  intro Hready. induction members as [|v rest IH]; intros Hmembers st Hmap Hvalid Hforest.
  - cbn [fold_left]. split; [reflexivity|]. split; [exact Hvalid|].
    split; [exact Hmap|]. split.
    + intros x a Hget. now left.
    + intros x [Hsome|Hfalse]; [exact Hsome|contradiction].
  - destruct (Hmembers v (or_introl eq_refl)) as [Hv [Hnonroot Hsemi]].
    pose proof (DomLtChoice.bucket_query p s v st Hready Hv Hnonroot Hsemi Hvalid Hforest)
      as [Horiginal [Hvalid' [a [Hparents Hchoice]]]].
    set (st1 := Cost.value (DomLt.member_c
      (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) s st v)) in *.
    assert (Hmap' : Map.wf positive_encoding (DomLt.provisional st1)).
    { rewrite Hparents. now apply Map.wf_set. }
    assert (Hforest' : DomSemiEval.cut_forest p s (DomLt.links st1)).
    { unfold DomSemiEval.cut_forest in *. now rewrite Horiginal. }
    destruct (IH (fun x Hin => Hmembers x (or_intror Hin)) st1 Hmap' Hvalid' Hforest')
      as [Horiginal' [Hvalid'' [Hmap'' [Hsound Htotal]]]].
    cbn [fold_left]. fold st1. split; [now rewrite Horiginal', Horiginal|].
    split; [exact Hvalid''|]. split; [exact Hmap''|]. split.
    + intros x b Hget. destruct (Hsound x b Hget) as [Hold|[Hin Hchoice']].
      * rewrite Hparents in Hold. destruct (Pos.eq_dec x v) as [->|Hne].
        -- rewrite Map.get_set_same in Hold by exact Hmap. injection Hold as <-.
           right. split; [now left|exact Hchoice].
        -- rewrite Map.get_set_other in Hold by
             (try exact positive_encoding_laws; try exact Hmap; exact Hne).
           now left.
      * right. split; [now right|exact Hchoice'].
    + intros x [Hsome|[Heq|Hin]]; apply Htotal.
      * left. rewrite Hparents. destruct (Pos.eq_dec x v) as [->|Hne].
        -- exists a. now apply Map.get_set_same.
        -- destruct Hsome as [b Hb]. exists b. rewrite Map.get_set_other;
             [exact Hb|exact positive_encoding_laws|exact Hmap|exact Hne].
      * subst x. left. exists a. rewrite Hparents. now apply Map.get_set_same.
      * now right.
Qed.

(** Processed buckets account for provisional support while original links follow processed DFS parents. *)
Record valid {V E} (p : Prepared.t V E) done (st : DomLt.state) : Prop := {
  valid_links : DomLinkProof.valid (DomCut.score p) (DomLt.links st);
  valid_original : forall v a,
    Map.get positive_encoding v (DomLink.original (DomLt.links st)) = Some a <->
      Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some a /\
        In v done;
  valid_map : Map.wf positive_encoding (DomLt.provisional st);
  valid_sound : forall v a, Map.get positive_encoding v (DomLt.provisional st) = Some a ->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ In (DomCut.score p v) done /\
      DomLtChoice.parent_choice p v a;
  valid_total : forall v, DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
    In (DomCut.score p v) done -> exists a, Map.get positive_encoding v (DomLt.provisional st) = Some a
}.

Local Lemma cut_forest {V E} (p : Prepared.t V E) done st s :
  Prepared.ready p -> valid p done st ->
  (forall v, DomPath.vertex (DomSemi.compute p) v -> (In v done <-> (s < v)%positive)) ->
  DomSemiEval.cut_forest p s (DomLt.links st).
Proof.
  intros Hready Hvalid Hcut v a. rewrite (valid_original _ _ _ Hvalid v a). split.
  - intros [Hparent Hin]. split; [exact Hparent|].
    apply (proj1 (Hcut v (proj1 (DomDfs.parent_vertices p v a Hready Hparent)))). exact Hin.
  - intros [Hparent Hhigh]. split; [exact Hparent|].
    apply (proj2 (Hcut v (proj1 (DomDfs.parent_vertices p v a Hready Hparent)))). exact Hhigh.
Qed.

Local Lemma link_finish {V E} (p : Prepared.t V E) done st s :
  DomLinkProof.valid (DomCut.score p) (DomLt.links st) ->
  (forall v a, Map.get positive_encoding v (DomLink.original (DomLt.links st)) = Some a <->
    Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) = Some a /\
      In v done) ->
  Map.get positive_encoding s (DomLink.original (DomLt.links st)) = None ->
  Map.wf positive_encoding (DomLt.provisional st) ->
  (forall v a, Map.get positive_encoding v (DomLt.provisional st) = Some a ->
    DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ In (DomCut.score p v) (s :: done) /\
      DomLtChoice.parent_choice p v a) ->
  (forall v, DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
    In (DomCut.score p v) (s :: done) ->
    exists a, Map.get positive_encoding v (DomLt.provisional st) = Some a) ->
  valid p (s :: done)
    (match Map.get positive_encoding s (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))) with
    | None => st
    | Some parent => DomLt.State (Cost.value (DomLink.link_c (DomLt.links st) s parent))
        (DomLt.provisional st)
    end).
Proof.
  intros Hlinks Horiginal Hnone Hmap Hsound Htotal.
  destruct (Map.get positive_encoding s (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))))
    as [parent|] eqn:Hparent.
  - constructor; cbn [DomLt.links DomLt.provisional].
    + now apply DomLinkProof.link_valid.
    + intros v a. rewrite DomLink.link_value. cbn [DomLink.original].
      destruct (Pos.eq_dec v s) as [->|Hne].
      * rewrite Map.get_set_same by exact (DomLinkProof.original_wf _ _ Hlinks).
        rewrite Hparent. split; [intro Heq; split; [exact Heq|now left]|tauto].
      * rewrite Map.get_set_other by
          (try exact positive_encoding_laws;
            try exact (DomLinkProof.original_wf _ _ Hlinks); exact Hne).
        rewrite Horiginal. cbn [In]. split; [tauto|].
        intros [Hget [Heq|Hin]]; [congruence|auto].
    + exact Hmap.
    + exact Hsound.
    + exact Htotal.
  - constructor.
    + exact Hlinks.
    + intros v a. rewrite Horiginal. cbn [In]. split; [tauto|].
      intros [Hget [Heq|Hin]]; [subst v; rewrite Hparent in Hget; discriminate|auto].
    + exact Hmap.
    + exact Hsound.
    + exact Htotal.
Qed.

(** One actual reverse step settles precisely the current bucket and extends the real link domain. *)
Theorem reverse_step_correct {V E} (p : Prepared.t V E) done st s :
  Prepared.ready p -> valid p done st -> DomPath.vertex (DomSemi.compute p) s ->
  (forall v, DomPath.vertex (DomSemi.compute p) v -> (In v done <-> (s < v)%positive)) ->
  valid p (s :: done) (Cost.value (DomLt.reverse_step_c (DomSemi.ranked (DomSemi.compute p))
    (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) (buckets p) st s)).
Proof.
  intros Hready Hvalid Hs Hcut.
  pose proof (bucket_fold p s (Index.find positive_encoding s (buckets p)) Hready
    (fun v Hin => proj1 (bucket_spec p s v Hready) Hin) st
    (valid_map _ _ _ Hvalid) (valid_links _ _ _ Hvalid)
    (cut_forest p done st s Hready Hvalid Hcut)) as Hfold.
  set (st1 := fold_left (fun st v => Cost.value (DomLt.member_c
    (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) s st v))
    (Index.find positive_encoding s (buckets p)) st) in *.
  destruct Hfold as [Horiginal [Hlinks [Hmap [Hsound Htotal]]]].
  rewrite DomLt.reverse_step_value. fold st1.
  apply (link_finish p done st1 s Hlinks).
  - intros v a. rewrite Horiginal. exact (valid_original _ _ _ Hvalid v a).
  - destruct (Map.get positive_encoding s (DomLink.original (DomLt.links st1))) as [a|] eqn:Hget;
      [|reflexivity].
    rewrite Horiginal in Hget. apply (valid_original _ _ _ Hvalid) in Hget.
    pose proof (proj1 (Hcut s Hs) (proj2 Hget)) as Hfalse.
    exact (False_rect _ (Pos.lt_irrefl s Hfalse)).
  - exact Hmap.
  - intros v a Hget. destruct (Hsound v a Hget) as [Hold|[Hin Hchoice]].
    + destruct (valid_sound _ _ _ Hvalid v a Hold) as [Hv [Hnonroot [Hin Hchoice]]].
      split; [exact Hv|]. split; [exact Hnonroot|]. split; [now right|exact Hchoice].
    + destruct (proj1 (bucket_spec p s v Hready) Hin) as [Hv [Hnonroot Hscore]].
      split; [exact Hv|]. split; [exact Hnonroot|]. split; [left; symmetry; exact Hscore|exact Hchoice].
  - intros v Hv Hnonroot [Heq|Hin]; apply Htotal.
    + right. apply (proj2 (bucket_spec p s v Hready)). split; [exact Hv|].
      split; [exact Hnonroot|congruence].
    + left. exact (valid_total _ _ _ Hvalid v Hv Hnonroot Hin).
Qed.

Local Lemma empty_valid {V E} (p : Prepared.t V E) :
  valid p [] (DomLt.State DomLink.empty Map.empty).
Proof.
  constructor; cbn [DomLt.links DomLt.provisional].
  - apply DomLinkProof.empty_valid.
  - intros v a. cbn [DomLink.empty DomLink.original]. rewrite Map.get_empty.
    split; [discriminate|intros [_ Hfalse]; contradiction].
  - apply Map.wf_empty.
  - intros v a Hget. rewrite Map.get_empty in Hget. discriminate.
  - intros v Hv Hnonroot Hin. contradiction.
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

Local Lemma reverse_fold {V E} (p : Prepared.t V E) todo :
  Prepared.ready p ->
  (forall u v, before todo u v -> (v < u)%positive) ->
  forall done st, valid p done st ->
  (forall n, DomPath.vertex (DomSemi.compute p) n <-> In n done \/ In n todo) ->
  (forall u v, In u done -> In v todo -> (v < u)%positive) ->
  exists final, valid p final
    (fold_left (fun st s => Cost.value (DomLt.reverse_step_c (DomSemi.ranked (DomSemi.compute p))
      (DomSemi.semis (DomSemi.settled (DomSemi.compute p))) (buckets p) st s)) todo st) /\
    forall n, DomPath.vertex (DomSemi.compute p) n -> In n final.
Proof.
  intro Hready. induction todo as [|s rest IH]; intros Horder done st Hvalid Hcover Hgap.
  - exists done. split; [exact Hvalid|].
    intros n Hn. apply Hcover in Hn. destruct Hn as [Hin|Hin]; [exact Hin|contradiction].
  - assert (Hs : DomPath.vertex (DomSemi.compute p) s) by (apply Hcover; right; now left).
    assert (Hcut : forall n, DomPath.vertex (DomSemi.compute p) n ->
      (In n done <-> (s < n)%positive)).
    { intros n Hn. split.
      - intro Hin. apply (Hgap n s Hin). now left.
      - intro Hhigh. apply Hcover in Hn. destruct Hn as [Hin|[Heq|Hin]]; [exact Hin| |].
        + subst n. exact (False_rect _ (Pos.lt_irrefl s Hhigh)).
        + pose proof (Horder s n (before_head rest s n Hin)) as Hlow.
          exact (False_rect _ (Pos.lt_irrefl s (Pos.lt_trans _ _ _ Hhigh Hlow))). }
    cbn [fold_left].
    apply (IH (fun u v Hb => Horder u v (before_tail rest s u v Hb)) (s :: done)).
    + exact (reverse_step_correct p done st s Hready Hvalid Hs Hcut).
    + intro n. rewrite Hcover. cbn [In]. tauto.
    + intros u v [Heq|Hin] Hv.
      * subst u. exact (Horder s v (before_head rest s v Hv)).
      * apply (Hgap u v Hin). now right.
Qed.

(** The actual reverse pass produces every discovered nonroot's proved provisional parent choice. *)
Theorem provisional_exact {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Map.wf positive_encoding (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) /\
    (forall v a, Map.get positive_encoding v
      (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) = Some a ->
      DomPath.vertex (DomSemi.compute p) v /\ v <> 1%positive /\ DomLtChoice.parent_choice p v a) /\
    (forall v, DomPath.vertex (DomSemi.compute p) v -> v <> 1%positive ->
      exists a, Map.get positive_encoding v
        (DomLt.provisional (DomLt.reverse_result (DomSemi.compute p))) = Some a).
Proof.
  intro Hready. rewrite DomLt.reverse_result_value.
  destruct (reverse_fold p (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) Hready
    (fun u v Hb => DomDfs.settlement_decreases p u v Hready Hb)
    [] (DomLt.State DomLink.empty Map.empty) (empty_valid p)
    ltac:(intro n; rewrite (DomDfs.vertex_member p n Hready); cbn [In]; tauto)
    ltac:(intros u v Hin; contradiction)) as [done [Hvalid Hall]].
  split; [exact (valid_map _ _ _ Hvalid)|]. split.
  - intros v a Hget. destruct (valid_sound _ _ _ Hvalid v a Hget)
      as [Hv [Hnonroot [Hin Hchoice]]]. auto.
  - intros v Hv Hnonroot. apply (valid_total _ _ _ Hvalid v Hv Hnonroot).
    apply Hall. apply (DomDfs.ancestor_vertices p (DomCut.score p v) v Hready).
    + exact (proj2 (proj2 (DomCut.score_exact p v Hready Hv Hnonroot))).
    + exact Hv.
Qed.

End DomLtReverse.
