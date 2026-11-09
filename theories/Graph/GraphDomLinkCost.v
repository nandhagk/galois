(** * Finite-rank link and evaluation costs

    Numeric rank descent prices the actual compression and preserves finite shortcut and label support.
    For example, a query from rank four visits at most four decreasing ranks.
    Builds on: GraphDomLink, its minimum-member theorem and primitive positive-key costs. *)

From Stdlib Require Import List PArith NArith Arith Lia Wf_nat.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseInternCost.
From Galois.Graph Require Import GraphDomLink GraphDomLinkProof GraphDomRank GraphDomCostBasis.
Import Cost.Notations.

Module DomLinkCost.
Local Open Scope N_scope.

(** Finite values and canonical storage are separate from linked-path semantic validity. *)
Definition values_bounded limit (m : Map.t positive positive) :=
  Map.wf positive_encoding m /\
    forall v a, Map.get positive_encoding v m = Some a -> (a <= limit)%positive.

(** Numeric compression needs finite shortcut and label data and no semidominator-result assumption. *)
Definition bounded limit st :=
  values_bounded limit (DomLink.shortcut st) /\ values_bounded limit (DomLink.labels st).

(** Query support constrains the actual returned state, root and optional selected label. *)
Definition query_bounded limit (answer : DomLink.query) :=
  let '(st, (root, part)) := answer in
  bounded limit st /\ (root <= limit)%positive /\
    match part with
    | None => True
    | Some best => (best <= limit)%positive
    end.

(** Canonical insertion preserves a finite value domain at any supplied key. *)
Theorem values_set limit m v a :
  values_bounded limit m -> (a <= limit)%positive ->
  values_bounded limit (Map.set positive_encoding v a m).
Proof.
  intros [Hmap Hvalues] Ha. split; [now apply Map.wf_set|].
  intros x u Hget. destruct (Pos.eq_dec x v) as [->|Hne].
  - rewrite Map.get_set_same in Hget by exact Hmap. now injection Hget as <-.
  - rewrite Map.get_set_other in Hget by
      (try exact positive_encoding_laws; try exact Hmap; exact Hne).
    now apply (Hvalues x u).
Qed.

(** Identity-valued lookup preserves finite support at every finite queried rank. *)
Theorem identity_bounded limit m v :
  values_bounded limit m -> (v <= limit)%positive ->
  (DomLink.identity_value m v <= limit)%positive.
Proof.
  intros [Hmap Hvalues] Hv. rewrite DomLink.identity_value_equation.
  destruct (Map.get positive_encoding v m) as [a|] eqn:Hget;
    [now apply (Hvalues v a)|exact Hv].
Qed.

(** Empty linked data has finite numeric support for every bound. *)
Theorem empty_bounded limit : bounded limit DomLink.empty.
Proof.
  unfold bounded, values_bounded, DomLink.empty.
  cbn [DomLink.shortcut DomLink.labels].
  split; split; try apply Map.wf_empty; intros v a Hget;
    rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Actual linking preserves finite support when both supplied ranks are within the finite domain. *)
Theorem link_bounded limit st v parent :
  bounded limit st -> (v <= limit)%positive -> (parent <= limit)%positive ->
  bounded limit (Cost.value (DomLink.link_c st v parent)).
Proof.
  intros [Hshortcuts Hlabels] Hv Hparent. rewrite DomLink.link_value.
  split; cbn [DomLink.shortcut DomLink.labels]; now apply values_set.
Qed.

(** Every actual compression result preserves finite numeric support independently of score semantics. *)
Theorem compress_bounded limit score st :
  bounded limit st ->
  forall v, (v <= limit)%positive ->
  query_bounded limit (Cost.value (DomLink.compress_c score st v)).
Proof.
  intro Hbounded.
  induction v as [v IH] using (well_founded_induction (well_founded_ltof _ Pos.to_nat)).
  intro Hv. rewrite DomLink.compress_value.
  destruct (Map.get positive_encoding v (DomLink.shortcut st)) as [a|] eqn:Hparent.
  - destruct (Cost.value (DomRank.smaller_c a v)) as [Hsmaller|Hstop].
    + assert (Ha : (a <= limit)%positive) by exact (proj2 (proj1 Hbounded) v a Hparent).
      specialize (IH a Hsmaller Ha).
      destruct (Cost.value (DomLink.compress_c score st a)) as [st' [root part]].
      cbn [query_bounded] in IH. destruct IH as [[Hshortcuts Hlabels] [Hroot Hpart]].
      assert (Hlabel : (DomLink.identity_value (DomLink.labels st) v <= limit)%positive).
      { exact (identity_bounded limit _ v (proj2 Hbounded) Hv). }
      destruct part as [best|].
      * assert (Hbest : (Cost.value (DomLink.minimum_c score
          (DomLink.identity_value (DomLink.labels st) v) best) <= limit)%positive).
        { destruct (DomLinkProof.minimum_member score
            (DomLink.identity_value (DomLink.labels st) v) best) as [Heq|Heq];
            rewrite Heq; assumption. }
        cbn [query_bounded DomLink.shortcut DomLink.labels].
        split; [split; apply values_set; assumption|]. auto.
      * cbn [query_bounded DomLink.shortcut DomLink.labels].
        split; [split; apply values_set; assumption|]. auto.
    + cbn [query_bounded]. auto.
  - cbn [query_bounded]. auto.
Qed.

(** Primitive score callbacks have finite prices and output widths on the actual finite rank domain. *)
Definition score_bounds limit (score : positive -> Cost.t positive) ks ws :=
  forall v, (v <= limit)%positive ->
    Cost.ticks (score v) <= ks /\ key_bits positive_encoding (Cost.value (score v)) <= ws.

(** Actual minimum selection pays both invocation overheads, both score calls and numeric comparison. *)
Theorem minimum_cost limit score ks ws u v :
  score_bounds limit score ks ws -> (u <= limit)%positive -> (v <= limit)%positive ->
  Cost.ticks (DomLink.minimum_c score u v) <= 2 + 2 * ks + ws.
Proof.
  intros Hscore Hu Hv.
  destruct (Hscore u Hu) as [Hu_cost Hu_width].
  destruct (Hscore v Hv) as [Hv_cost Hv_width].
  pose proof (DomRank.compare_cost (Cost.value (score u)) (Cost.value (score v))) as Hcompare.
  change (1 + (Cost.ticks (score u) + (1 + (Cost.ticks (score v) +
    (Cost.ticks (DomRank.compare_c (Cost.value (score u)) (Cost.value (score v))) + 0)))) <=
    2 + 2 * ks + ws).
  change (Cost.ticks (DomRank.compare_c (Cost.value (score u)) (Cost.value (score v))) <=
    key_bits positive_encoding (Cost.value (score u))) in Hcompare.
  lia.
Qed.

(** Identity-valued score and label reads retain the full positive-key lookup charge. *)
Theorem identity_cost m v :
  Cost.ticks (DomLink.identity_value_c m v) = 2 + key_bits positive_encoding v.
Proof.
  change (Cost.ticks (Map.get_c positive_encoding v m) + 0 =
    2 + key_bits positive_encoding v).
  rewrite DomCostBasis.get_cost. lia.
Qed.

Local Lemma update_cost st v root best :
  Cost.ticks
    (let* shortcuts := Map.set_c positive_encoding v root (DomLink.shortcut st) in
     let* labels := Map.set_c positive_encoding v best (DomLink.labels st) in
     Cost.ret (DomLink.Links (DomLink.original st) shortcuts labels, (root, Some best))) =
    4 + 2 * key_bits positive_encoding v.
Proof.
  rewrite (Cost.ticks_bind (Map.set_c positive_encoding v root (DomLink.shortcut st))),
    (Cost.ticks_bind (Map.set_c positive_encoding v best (DomLink.labels st))),
    Cost.ticks_ret, !DomCostBasis.set_cost. lia.
Qed.

(** The layer coefficient retains both callback invocations and the comparison of their actual outputs. *)
Definition compress_k w ks ws := 16 + 8 * w + 2 * ks + ws.

(** Actual compression has a rank-linear numeric bound under primitive finite score prices and support. *)
Theorem compress_cost limit score st ks ws :
  bounded limit st -> score_bounds limit score ks ws ->
  forall v, (v <= limit)%positive ->
  Cost.ticks (DomLink.compress_c score st v) <=
    N.pos v * compress_k (key_bits positive_encoding limit) ks ws.
Proof.
  intros Hbounded Hscore.
  set (coefficient := compress_k (key_bits positive_encoding limit) ks ws).
  induction v as [v IH] using (well_founded_induction (well_founded_ltof _ Pos.to_nat)).
  intro Hv.
  assert (Hwidth : key_bits positive_encoding v <= key_bits positive_encoding limit).
  { apply InternCost.bits_monotone. exact Hv. }
  assert (Hpositive : 0 < N.pos v) by reflexivity.
  rewrite DomLink.compress_equation. unfold DomLink.compress_body_c.
  rewrite (Cost.ticks_bind Cost.step), Cost.ticks_step,
    (Cost.ticks_bind (Map.get_c positive_encoding v (DomLink.shortcut st))),
    DomCostBasis.get_cost.
  fold (Map.get positive_encoding v (DomLink.shortcut st)).
  destruct (Map.get positive_encoding v (DomLink.shortcut st)) as [a|] eqn:Hparent.
  - pose proof (proj2 (DomRank.compare_cont_cost Eq a v)) as Hcompare.
    change (Cost.ticks (DomRank.smaller_c a v) <= key_bits positive_encoding v) in Hcompare.
    rewrite (Cost.ticks_bind (DomRank.smaller_c a v)).
    destruct (Cost.value (DomRank.smaller_c a v)) as [Hsmaller|Hstop].
    + assert (Ha : (a <= limit)%positive) by exact (proj2 (proj1 Hbounded) v a Hparent).
      specialize (IH a Hsmaller Ha).
      pose proof (compress_bounded limit score st Hbounded a Ha) as Hsupport.
      rewrite (Cost.ticks_bind (DomLink.compress_c score st a)).
      destruct (Cost.value (DomLink.compress_c score st a)) as [st' [root part]].
      cbn [query_bounded] in Hsupport.
      destruct Hsupport as [Hstate [Hroot Hpart]].
      rewrite (Cost.ticks_bind (DomLink.identity_value_c (DomLink.labels st) v)).
      fold (DomLink.identity_value (DomLink.labels st) v).
      assert (Hlabel : (DomLink.identity_value (DomLink.labels st) v <= limit)%positive).
      { exact (identity_bounded limit _ v (proj2 Hbounded) Hv). }
      assert (Hrank : N.pos a + 1 <= N.pos v).
      { assert (Hlt : (a < v)%positive) by now apply Pos2Nat.inj_lt.
        change (N.pos a < N.pos v) in Hlt. lia. }
      destruct part as [best|].
      * pose proof (minimum_cost limit score ks ws
          (DomLink.identity_value (DomLink.labels st) v) best Hscore Hlabel Hpart) as Hminimum.
        rewrite (Cost.ticks_bind (DomLink.minimum_c score
          (DomLink.identity_value (DomLink.labels st) v) best)), update_cost, identity_cost.
        assert (Hown : 1 + (2 + key_bits positive_encoding v) +
          Cost.ticks (DomRank.smaller_c a v) + (2 + key_bits positive_encoding v) +
          Cost.ticks (DomLink.minimum_c score (DomLink.identity_value (DomLink.labels st) v) best) +
          (4 + 2 * key_bits positive_encoding v) <= coefficient).
        { unfold coefficient, compress_k. lia. }
        eapply N.le_trans with (m := (N.pos a + 1) * coefficient).
        -- nia.
        -- now apply N.mul_le_mono.
      * rewrite Cost.bind_ret_l, update_cost, identity_cost.
        assert (Hown : 1 + (2 + key_bits positive_encoding v) +
          Cost.ticks (DomRank.smaller_c a v) + (2 + key_bits positive_encoding v) +
          (4 + 2 * key_bits positive_encoding v) <= coefficient).
        { unfold coefficient, compress_k. lia. }
        eapply N.le_trans with (m := (N.pos a + 1) * coefficient).
        -- nia.
        -- now apply N.mul_le_mono.
    + rewrite Cost.ticks_ret. unfold coefficient, compress_k. nia.
  - rewrite Cost.ticks_ret. unfold coefficient, compress_k. nia.
Qed.

(** Evaluation adds no work beyond the actual compression whose returned representative it selects. *)
Theorem eval_cost_equation score st v :
  Cost.ticks (DomLink.eval_c score st v) = Cost.ticks (DomLink.compress_c score st v).
Proof.
  unfold DomLink.eval_c. rewrite (Cost.ticks_bind (DomLink.compress_c score st v)).
  destruct (Cost.value (DomLink.compress_c score st v)) as [st' [root part]].
  rewrite Cost.ticks_ret. lia.
Qed.

(** Actual evaluation preserves finite support of its returned state and representative. *)
Theorem eval_bounded limit score st v :
  bounded limit st -> (v <= limit)%positive ->
  let '(st', best) := Cost.value (DomLink.eval_c score st v) in
  bounded limit st' /\ (best <= limit)%positive.
Proof.
  intros Hbounded Hv.
  pose proof (compress_bounded limit score st Hbounded v Hv) as Hquery.
  rewrite DomLink.eval_value.
  destruct (Cost.value (DomLink.compress_c score st v)) as [st' [root part]].
  cbn [query_bounded] in Hquery. destruct Hquery as [Hstate [Hroot Hpart]].
  destruct part; split; assumption.
Qed.

(** Identity-valued primitive score maps discharge both callback price and actual output-width duties. *)
Theorem identity_score_bounds limit m :
  values_bounded limit m ->
  score_bounds limit (DomLink.identity_value_c m)
    (2 + key_bits positive_encoding limit) (key_bits positive_encoding limit).
Proof.
  intros Hmap v Hv. split.
  - rewrite identity_cost. pose proof (InternCost.bits_monotone v limit Hv) as Hwidth.
    change (key_bits positive_encoding v <= key_bits positive_encoding limit) in Hwidth.
    lia.
  - apply InternCost.bits_monotone. exact (identity_bounded limit m v Hmap Hv).
Qed.

(** The production evaluator with identity scores has a closed rank/width bound from finite map support. *)
Theorem eval_identity_cost limit settled st v :
  values_bounded limit settled -> bounded limit st -> (v <= limit)%positive ->
  Cost.ticks (DomLink.eval_c (DomLink.identity_value_c settled) st v) <=
    N.pos limit * (20 + 11 * key_bits positive_encoding limit).
Proof.
  intros Hsettled Hstate Hv. rewrite eval_cost_equation.
  pose proof (compress_cost limit (DomLink.identity_value_c settled) st
    (2 + key_bits positive_encoding limit) (key_bits positive_encoding limit)
    Hstate (identity_score_bounds limit settled Hsettled) v Hv) as Hcompress.
  eapply N.le_trans; [exact Hcompress|].
  apply N.mul_le_mono; [exact Hv|unfold compress_k; lia].
Qed.

(** Actual linking charges three canonical writes at the supplied child rank. *)
Theorem link_cost st v parent :
  Cost.ticks (DomLink.link_c st v parent) = 6 + 3 * key_bits positive_encoding v.
Proof.
  unfold DomLink.link_c.
  rewrite (Cost.ticks_bind (Map.set_c positive_encoding v parent (DomLink.original st))),
    (Cost.ticks_bind (Map.set_c positive_encoding v parent (DomLink.shortcut st))),
    (Cost.ticks_bind (Map.set_c positive_encoding v v (DomLink.labels st))),
    Cost.ticks_ret, !DomCostBasis.set_cost. lia.
Qed.

End DomLinkCost.
