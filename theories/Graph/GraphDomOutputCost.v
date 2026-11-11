(** * Complete inverse erasure and actual output annotation costs

    The same inverse erases ranked parents and supplies the single parent-forest annotation.
    For example, virtual-root children are filtered while their inverse queries remain charged.
    Builds on: GraphDomNumberCost and the proved actual LT output support. *)

From Stdlib Require Import List PArith NArith Arith Lia Ring.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex BaseIntern BaseInternCost
  BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphSearchSpec
  GraphDomSemi GraphDomErase GraphDomLt GraphDomLtProof GraphDomCut GraphDomPath GraphDomDfs
  GraphDomSemiCost GraphDomLinkCost GraphDomOutput GraphDomVirtual GraphDomNumber GraphDomNumberCost
  GraphDomCostBasis.
Import Cost.Notations.

Module DomOutputCost.
Local Open Scope N_scope.

(** Inverse erasure retains the map scan, both renaming callbacks and selected insertion. *)
Theorem erase_cost limit (m : Map.t positive positive) rename c k wo :
  DomLinkCost.values_bounded limit m ->
  (forall v u, Map.get positive_encoding v m = Some u -> (v <= limit)%positive) ->
  (Map.size m <= c)%nat ->
  (forall rank, (rank <= limit)%positive -> Cost.ticks (rename rank) <= k) ->
  (forall rank v, Cost.value (rename rank) = Some v -> key_bits positive_encoding v <= wo) ->
  Cost.ticks (DomErase.with_c rename m) <=
    TrieCost.trie_k * (1 + N.of_nat c * key_bits positive_encoding limit) +
      N.of_nat c * (5 + 2 * k + wo).
Proof.
  intros [Hmap Hvalues] Hkeys Hsize Hrename Hwidth.
  pose proof (MapCost.elements_numeric_cost positive_encoding m
    (key_bits positive_encoding limit) Hmap
    ltac:(intros v u Hget; apply DomCostBasis.bits_monotone; now apply (Hkeys v u))) as Hscan.
  pose proof (DomCostBasis.fold_right_cost (DomErase.binding_c rename) (Map.elements m) Map.empty
    (4 + 2 * k + wo)
    ltac:(intros [v u] tail Hbinding; cbn beta;
      apply (Map.elements_spec positive_encoding positive_encoding_laws v u m Hmap) in Hbinding;
      pose proof (Hrename v (Hkeys v u Hbinding)) as Hchild;
      pose proof (Hrename u (Hvalues v u Hbinding)) as Hparent;
      unfold DomErase.binding_c;
      rewrite (Cost.ticks_bind Cost.step), Cost.ticks_step,
        (Cost.ticks_bind (rename v)), (Cost.ticks_bind Cost.step), Cost.ticks_step,
        (Cost.ticks_bind (rename u));
      destruct (Cost.value (rename v)) as [child|] eqn:Hchild_value;
      destruct (Cost.value (rename u)) as [parent|];
      rewrite ?DomCostBasis.set_cost, ?Cost.ticks_ret;
      try pose proof (Hwidth v child Hchild_value) as Hchild_width;
      cbn [fst snd] in *; lia)) as Hbindings.
  unfold DomErase.with_c. rewrite (Cost.ticks_bind (Map.elements_c m)). fold (Map.elements m).
  rewrite <- Map.size_elements in Hbindings.
  assert (Hscan_scale : TrieCost.trie_k *
    (1 + N.of_nat (Map.size m) * key_bits positive_encoding limit) <=
    TrieCost.trie_k * (1 + N.of_nat c * key_bits positive_encoding limit)).
  { apply N.mul_le_mono; [reflexivity|]. apply N.add_le_mono; [reflexivity|].
    apply N.mul_le_mono; lia. }
  assert (Hbinding_scale : N.of_nat (Map.size m) * (1 + (4 + 2 * k + wo)) <=
    N.of_nat c * (5 + 2 * k + wo)) by (apply N.mul_le_mono; lia).
  lia.
Qed.

Section Output.
Context {V E : Type} (p : Prepared.t V E).
Local Abbreviation shared := (DomSemi.compute p).
Local Abbreviation limit := (DomSemiCost.rank_limit p).
Local Abbreviation ranked := (DomSemi.ranked shared).
Local Abbreviation ranked_parents := (DomLt.finish shared).

Definition count := length (Search.preorder (DomSemi.search shared)).
Definition original_width := PreparedCost.id_width (Prepared.graph p).
Definition rank_width := key_bits positive_encoding limit.

(** Every original prepared ID is bounded by the original finite node allocation frontier. *)
Theorem original_id_width name i :
  Prepared.ready p -> Prepared.id_of p name = Some i ->
  key_bits positive_encoding i <= original_width.
Proof.
  intros Hready Hi. rewrite Prepared.id_of_equation in Hi.
  pose proof (InternCost.dense_id_bits (Prepared.node_enc p)
    (Prepared.encoding_valid p (proj2 (proj2 Hready))) name i (Prepared.names p)
    (Prepared.names_wf p (proj2 (proj2 Hready))) Hi) as Hwidth.
  rewrite (DomVirtual.size_nodes p Hready) in Hwidth. exact Hwidth.
Qed.

Local Lemma vertex_rank v :
  Prepared.ready p -> DomPath.vertex shared v -> (v <= limit)%positive.
Proof.
  intros Hready Hv. apply (DomSemiCost.actual_rank_bound p v Hready).
  now apply (DomDfs.vertex_member p v Hready).
Qed.

(** Ranked parents have bounded keys and values and at most one binding per discovered rank. *)
Theorem ranked_parent_resources :
  Prepared.ready p ->
  DomLinkCost.values_bounded limit ranked_parents /\
  (forall v u, Map.get positive_encoding v ranked_parents = Some u -> (v <= limit)%positive) /\
    (Map.size ranked_parents <= count)%nat.
Proof.
  intro Hready.
  pose proof (proj1 (DomLtProof.finish_parents p Hready)) as Hparents.
  assert (Hkeys : forall v u, Map.get positive_encoding v ranked_parents = Some u ->
    DomPath.vertex shared v /\ DomPath.vertex shared u).
  { intros v u Hget. destruct (Hparents v u Hget) as [Hv [Hnonroot [Hu Hrest]]]. auto. }
  split.
  - split; [apply DomLt.finish_wf|].
    intros v u Hget. exact (vertex_rank u Hready (proj2 (Hkeys v u Hget))).
  - split.
    + intros v u Hget. exact (vertex_rank v Hready (proj1 (Hkeys v u Hget))).
    + eapply Nat.le_trans with (m := length (DomSemi.reverse_order ranked)).
      * apply (Map.size_support_bound positive_encoding positive_encoding_laws);
          [apply DomLt.finish_wf|].
        intros v u Hget. apply (DomDfs.vertex_member p v Hready).
        exact (proj1 (Hkeys v u Hget)).
      * rewrite (DomDfs.settlement_order p Hready), length_rev, length_map, length_seq. reflexivity.
Qed.

Definition erasure_bound :=
  TrieCost.trie_k * (1 + N.of_nat count * rank_width) +
    N.of_nat count * (9 + 2 * rank_width + original_width).

(** The actual inverse erasure uses its constructed map and actual original-ID widths. *)
Theorem actual_erasure_cost :
  Prepared.ready p ->
  Cost.ticks (DomSemi.erase_c shared ranked_parents) <= erasure_bound.
Proof.
  intro Hready. destruct (ranked_parent_resources Hready) as [Hvalues [Hkeys Hsize]].
  pose proof (erase_cost limit ranked_parents
    (fun rank => Map.get_c positive_encoding rank (DomSemi.real_ids ranked)) count
    (2 + rank_width) original_width Hvalues Hkeys Hsize
    ltac:(intros rank Hrank; cbn beta; rewrite DomCostBasis.get_cost;
      pose proof (DomCostBasis.bits_monotone rank limit Hrank) as Hwidth;
      change (key_bits positive_encoding rank <= rank_width) in Hwidth; lia)
    ltac:(intros rank v Hget;
      change (Map.get positive_encoding rank (DomSemi.real_ids ranked) = Some v) in Hget;
      apply (DomOutput.inverse_real p rank v Hready) in Hget;
      destruct Hget as [name [raw [Hid Hrest]]];
      exact (original_id_width name v Hready Hid))) as Herase.
  unfold DomSemi.erase_c.
  eapply N.le_trans; [exact Herase|].
  clear Herase Hvalues Hkeys Hsize.
  unfold erasure_bound.
  apply N.add_le_mono; [reflexivity|]. apply N.mul_le_mono; [reflexivity|lia].
Qed.

Local Lemma live_length :
  Prepared.ready p -> (length (DomOutput.live p) <= count)%nat.
Proof.
  intro Hready. unfold DomOutput.live.
  eapply Nat.le_trans; [apply Prepared.present_length|].
  rewrite length_rev, (DomDfs.settlement_order p Hready), length_rev, length_map, length_seq.
  reflexivity.
Qed.

(** Actual erasure and live enumeration discharge every parent-forest numbering input duty. *)
Theorem numbering_bounds :
  Prepared.ready p ->
  DomNumberCost.bounds (DomOutput.live p) (DomOutput.parents p) count original_width.
Proof.
  intro Hready. constructor.
  - exact (DomOutput.live_nodup p Hready).
  - exact (DomSemi.erase_wf shared ranked_parents).
  - intros v u Hget.
    destruct (DomOutput.parent_sound p v u Hready Hget)
      as [name [parent [Hname [Hparent [Hreachable [Hparent_reachable Himmediate]]]]]].
    split.
    + exact (proj2 (DomOutput.live_spec p v Hready)
        (ex_intro _ name (conj Hname Hreachable))).
    + exact (proj2 (DomOutput.live_spec p u Hready)
        (ex_intro _ parent (conj Hparent Hparent_reachable))).
  - exact (live_length Hready).
  - intros v Hv.
    destruct (proj1 (DomOutput.live_spec p v Hready) Hv) as [name [Hid Hreachable]].
    exact (original_id_width name v Hready Hid).
Qed.

Definition output_bound :=
  erasure_bound + N.of_nat count + N.of_nat count * (4 + rank_width) +
    DomNumberCost.number_bound count original_width.

(** The suffix pays inverse erasure, rank reversal, live-ID queries and complete numbering. *)
Theorem output_cost :
  Prepared.ready p ->
  Cost.ticks
    (let* parents := DomSemi.erase_c shared ranked_parents in
     let* ranks := rev_c (DomSemi.reverse_order ranked) in
     let* live := Prepared.present_c
       (fun rank => Map.get_c positive_encoding rank (DomSemi.real_ids ranked)) ranks in
     DomNumber.of_parents_c live parents) <= output_bound.
Proof.
  intro Hready.
  pose proof (actual_erasure_cost Hready) as Herase.
  pose proof (DomNumberCost.number_cost (DomOutput.live p) (DomOutput.parents p)
    count original_width (numbering_bounds Hready)) as Hnumber.
  assert (Hlength : length (DomSemi.reverse_order ranked) = count).
  { rewrite (DomDfs.settlement_order p Hready), length_rev, length_map, length_seq. reflexivity. }
  pose proof (DomCostBasis.present_cost
    (fun rank => Map.get_c positive_encoding rank (DomSemi.real_ids ranked))
    (rev (DomSemi.reverse_order ranked)) (2 + rank_width)
    ltac:(intros rank Hrank; cbn beta; rewrite DomCostBasis.get_cost;
      apply in_rev in Hrank;
      pose proof (DomCostBasis.bits_monotone rank limit
        (DomSemiCost.actual_rank_bound p rank Hready Hrank)) as Hwidth;
      change (key_bits positive_encoding rank <= rank_width) in Hwidth; lia)) as Hlive.
  rewrite length_rev, Hlength in Hlive.
  rewrite (Cost.ticks_bind (DomSemi.erase_c shared ranked_parents)).
  change (Cost.ticks (DomSemi.erase_c shared ranked_parents) +
    Cost.ticks
      (let* ranks := rev_c (DomSemi.reverse_order ranked) in
       let* live := Prepared.present_c
         (fun rank => Map.get_c positive_encoding rank (DomSemi.real_ids ranked)) ranks in
       DomNumber.of_parents_c live (DomOutput.parents p)) <= output_bound).
  rewrite (Cost.ticks_bind (rev_c (DomSemi.reverse_order ranked))), ticks_rev_c, value_rev_c.
  rewrite (Cost.ticks_bind (Prepared.present_c
    (fun rank => Map.get_c positive_encoding rank (DomSemi.real_ids ranked))
    (rev (DomSemi.reverse_order ranked)))), Prepared.present_c_value.
  fold (DomOutput.live p). rewrite Hlength.
  change (Cost.ticks (DomSemi.erase_c shared ranked_parents) +
    (N.of_nat count +
      (Cost.ticks (Prepared.present_c
        (fun rank => Map.get_c positive_encoding rank (DomSemi.real_ids ranked))
        (rev (DomSemi.reverse_order ranked))) +
        Cost.ticks
          (DomNumber.of_parents_c (DomOutput.live p) (DomOutput.parents p)))) <= output_bound).
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Herase|].
    apply N.add_le_mono; [reflexivity|].
    apply N.add_le_mono; [exact Hlive|exact Hnumber].
  - unfold output_bound. lia.
Qed.

(** The suffix coefficient retains public annotation and trie coefficients. *)
Definition output_k := DomNumberCost.number_k + TrieCost.trie_k + 14.

(** Actual output costs are quadratic in discovery count on the stated finite-width domain. *)
Theorem output_shape w :
  original_width <= w -> rank_width <= w -> DomNumberCost.fuel_width count <= w ->
  output_bound <= output_k * (1 + N.of_nat count) * (1 + N.of_nat count) * (1 + w).
Proof.
  intros Ho Hr Hf.
  pose proof (DomNumberCost.number_shape count original_width w Ho Hr Hf) as Hnumber.
  set (a := N.of_nat count) in *.
  set (target := (1 + a) * (1 + a) * (1 + w)).
  assert (Hpath : 1 + a * w <= target).
  { eapply N.le_trans with (m := (1 + a) * (1 + w)).
    - replace ((1 + a) * (1 + w)) with (1 + a * w + (a + w)) by ring.
      apply N.le_add_r.
    - unfold target.
      replace ((1 + a) * (1 + w)) with ((1 + a) * 1 * (1 + w)) at 1 by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; lia|reflexivity]. }
  assert (Hcells : a * (1 + w) <= target).
  { unfold target. replace (a * (1 + w)) with (a * 1 * (1 + w)) at 1 by ring.
    apply N.mul_le_mono; [apply N.mul_le_mono; lia|reflexivity]. }
  assert (Hprefix : erasure_bound + a + a * (4 + rank_width) <=
    TrieCost.trie_k * (1 + a * w) + a * (9 + 2 * w + w) + a + a * (4 + w)).
  { unfold erasure_bound. fold a.
    repeat match goal with
    | |- (?x + ?y <= ?z + ?t)%N => apply N.add_le_mono
    | |- (?x * ?y <= ?z * ?t)%N => apply N.mul_le_mono
    | |- _ => first [reflexivity | assumption | lia]
    end. }
  replace (9 + 2 * w + w) with (9 + 3 * w) in Hprefix by lia.
  assert (Htrie : TrieCost.trie_k * (1 + a * w) <= TrieCost.trie_k * target)
    by (apply N.mul_le_mono; [reflexivity|exact Hpath]).
  assert (Hplain : a * (9 + 3 * w) + a + a * (4 + w) <= 14 * target).
  { eapply N.le_trans with (m := 14 * (a * (1 + w))).
    - replace (a * (9 + 3 * w) + a + a * (4 + w)) with (14 * a + 4 * (a * w)) by ring.
      replace (14 * (a * (1 + w))) with (14 * a + 14 * (a * w)) by ring. lia.
    - apply N.mul_le_mono; [reflexivity|exact Hcells]. }
  assert (Hpriced : TrieCost.trie_k * (1 + a * w) + a * (9 + 3 * w) + a + a * (4 + w) <=
    (TrieCost.trie_k + 14) * target).
  { replace (TrieCost.trie_k * (1 + a * w) + a * (9 + 3 * w) + a + a * (4 + w)) with
      (TrieCost.trie_k * (1 + a * w) + (a * (9 + 3 * w) + a + a * (4 + w))) by ring.
    replace ((TrieCost.trie_k + 14) * target) with
      (TrieCost.trie_k * target + 14 * target) by ring. now apply N.add_le_mono. }
  replace (DomNumberCost.number_k * (1 + a) * (1 + a) * (1 + w)) with
    (DomNumberCost.number_k * target) in Hnumber by (unfold target; ring).
  replace (output_k * (1 + a) * (1 + a) * (1 + w)) with (output_k * target)
    by (unfold target; ring).
  unfold output_bound. fold a.
  eapply N.le_trans.
  - apply N.add_le_mono; [eapply N.le_trans; [exact Hprefix|exact Hpriced]|exact Hnumber].
  - unfold output_k. nia.
Qed.

End Output.
End DomOutputCost.
