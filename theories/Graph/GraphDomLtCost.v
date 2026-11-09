(** * Numeric costs of the actual LT finisher

    Bucket inventory and finite link-state support price the reverse and correction passes together.
    For example, each actual bucket membership pays one linked evaluator query.
    Builds on: GraphDomBucketCost and the readiness-derived shared settlement support. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Ring.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIndex BaseInternCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSemi GraphDomLt
  GraphDomLtReverse GraphDomRank GraphDomLink GraphDomLinkCost GraphDomSemiCost GraphDomBucketCost
  GraphDomCostBasis GraphDomDfs.
Import Cost.Notations.

Module DomLtCost.
Local Open Scope N_scope.

Definition bounded limit st : Prop :=
  DomLinkCost.bounded limit (DomLt.links st) /\
    DomLinkCost.values_bounded limit (DomLt.provisional st).

Definition member_bound limit :=
  DomSemiCost.eval_bound limit + 4 + 3 * key_bits positive_encoding limit.

Local Lemma return_set_cost links provisional v parent :
  Cost.ticks (let* parents := Map.set_c positive_encoding v parent provisional in
    Cost.ret (DomLt.State links parents)) = 2 + key_bits positive_encoding v.
Proof.
  rewrite (Cost.ticks_bind (Map.set_c positive_encoding v parent provisional)), Cost.ticks_ret,
    DomCostBasis.set_cost. lia.
Qed.

(** Actual bucket evaluation preserves finite state and expands its primitive query prices. *)
Theorem member_cost limit semis s st v :
  DomLinkCost.values_bounded limit semis -> bounded limit st ->
  (s <= limit)%positive -> (v <= limit)%positive ->
  bounded limit (Cost.value (DomLt.member_c semis s st v)) /\
    Cost.ticks (DomLt.member_c semis s st v) <= member_bound limit.
Proof.
  intros Hsemis [Hlinks Hparents] Hs Hv.
  pose proof (DomLinkCost.eval_bounded limit (DomLink.identity_value_c semis)
    (DomLt.links st) v Hlinks Hv) as Hsupport.
  pose proof (DomLinkCost.eval_identity_cost limit semis (DomLt.links st) v Hsemis Hlinks Hv)
    as Heval.
  assert (Hv_width : key_bits positive_encoding v <= key_bits positive_encoding limit)
    by (apply InternCost.bits_monotone; exact Hv).
  unfold DomLt.member_c.
  rewrite (Cost.value_bind (DomLink.eval_c (DomLink.identity_value_c semis) (DomLt.links st) v)).
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c semis) (DomLt.links st) v))
    as [links' chosen] eqn:Hquery.
  destruct Hsupport as [Hlinks' Hchosen].
  assert (Hscore : (DomLink.identity_value semis chosen <= limit)%positive).
  { exact (DomLinkCost.identity_bounded limit semis chosen Hsemis Hchosen). }
  split.
  - rewrite !Cost.value_bind. fold (DomLink.identity_value semis chosen).
    fold (DomRank.compare_c (DomLink.identity_value semis chosen) s).
    change (DomLinkCost.bounded limit links' /\
      DomLinkCost.values_bounded limit (Map.set positive_encoding v
        (match Cost.value (DomRank.compare_c (DomLink.identity_value semis chosen) s) with
        | Lt => chosen
        | _ => s
        end) (DomLt.provisional st))).
    split; [exact Hlinks'|]. apply DomLinkCost.values_set; [exact Hparents|].
    destruct (Cost.value (DomRank.compare_c (DomLink.identity_value semis chosen) s)); assumption.
  - rewrite (Cost.ticks_bind (DomLink.eval_c (DomLink.identity_value_c semis) (DomLt.links st) v)).
    rewrite Hquery.
    rewrite (Cost.ticks_bind (DomLink.identity_value_c semis chosen)).
    fold (DomLink.identity_value semis chosen).
    rewrite (Cost.ticks_bind (DomRank.compare_c (DomLink.identity_value semis chosen) s)),
      return_set_cost, DomLinkCost.identity_cost.
    pose proof (InternCost.bits_monotone chosen limit Hchosen) as Hchosen_width.
    pose proof (InternCost.bits_monotone (DomLink.identity_value semis chosen) limit Hscore)
      as Hscore_width.
    pose proof (DomRank.compare_cost (DomLink.identity_value semis chosen) s) as Hcompare.
    change (Cost.ticks (DomRank.compare_c (DomLink.identity_value semis chosen) s) <=
      key_bits positive_encoding (DomLink.identity_value semis chosen)) in Hcompare.
    change (key_bits positive_encoding chosen <= key_bits positive_encoding limit) in Hchosen_width.
    change (key_bits positive_encoding (DomLink.identity_value semis chosen) <=
      key_bits positive_encoding limit) in Hscore_width.
    unfold member_bound, DomSemiCost.eval_bound in *. lia.
Qed.

Local Lemma members_cost limit semis s members st :
  DomLinkCost.values_bounded limit semis -> bounded limit st -> (s <= limit)%positive ->
  (forall v, In v members -> (v <= limit)%positive) ->
  bounded limit (Cost.value (fold_left_c (DomLt.member_c semis s) members st)) /\
  Cost.ticks (fold_left_c (DomLt.member_c semis s) members st) <=
    N.of_nat (length members) * (1 + member_bound limit).
Proof.
  intros Hsemis Hst Hs Hmembers.
  pose proof (DomCostBasis.fold_left_weighted (DomLt.member_c semis s) (bounded limit)
    (fun _ => member_bound limit) members st Hst
    ltac:(intros current v Hcurrent Hv; exact
      (member_cost limit semis s current v Hsemis Hcurrent Hs (Hmembers v Hv)))) as Hfold.
  destruct Hfold as [Hsupport Hcost]. split; [exact Hsupport|].
  assert (Hsum : fold_right (fun _ rest => 1 + member_bound limit + rest) 0 members =
    N.of_nat (length members) * (1 + member_bound limit)).
  { clear Hmembers Hsupport Hcost.
    induction members as [|v rest IH]; [reflexivity|].
    cbn [fold_right length]. rewrite Nat2N.inj_succ, IH. nia. }
  now rewrite Hsum in Hcost.
Qed.

Definition reverse_step_bound limit (buckets : Map.t positive (list positive)) s :=
  10 + 5 * key_bits positive_encoding limit +
    N.of_nat (length (Index.find positive_encoding s buckets)) * (1 + member_bound limit).

(** Each actual reverse step prices its bucket before the optional actual DFS-parent link. *)
Theorem reverse_step_cost {L} limit (ranked : DomSemi.layout L) semis buckets st s :
  DomLinkCost.values_bounded limit semis ->
  DomLinkCost.values_bounded limit (DomSemi.parents ranked) ->
  bounded limit st -> (s <= limit)%positive ->
  (forall v, In v (Index.find positive_encoding s buckets) -> (v <= limit)%positive) ->
  bounded limit (Cost.value (DomLt.reverse_step_c ranked semis buckets st s)) /\
  Cost.ticks (DomLt.reverse_step_c ranked semis buckets st s) <=
    reverse_step_bound limit buckets s.
Proof.
  intros Hsemis Hparents Hst Hs Hmembers.
  pose proof (members_cost limit semis s (Index.find positive_encoding s buckets) st
    Hsemis Hst Hs Hmembers) as Hfold.
  assert (Hs_width : key_bits positive_encoding s <= key_bits positive_encoding limit)
    by (apply InternCost.bits_monotone; exact Hs).
  unfold DomLt.reverse_step_c.
  rewrite (Cost.value_bind (Index.find_c positive_encoding s buckets)).
  fold (Index.find positive_encoding s buckets).
  rewrite (Cost.value_bind
    (fold_left_c (DomLt.member_c semis s) (Index.find positive_encoding s buckets) st)).
  set (settled := Cost.value
    (fold_left_c (DomLt.member_c semis s) (Index.find positive_encoding s buckets) st)) in *.
  destruct Hfold as [[Hlinks Hprovisional] Hcost]. split.
  - rewrite Cost.value_bind. fold (Map.get positive_encoding s (DomSemi.parents ranked)).
    destruct (Map.get positive_encoding s (DomSemi.parents ranked)) as [parent|] eqn:Hparent.
    + rewrite Cost.value_bind.
      change (DomLinkCost.bounded limit
        (Cost.value (DomLink.link_c (DomLt.links settled) s parent)) /\
        DomLinkCost.values_bounded limit (DomLt.provisional settled)).
      split; [|exact Hprovisional].
      apply DomLinkCost.link_bounded;
        [exact Hlinks|exact Hs|exact (proj2 Hparents s parent Hparent)].
    + now split.
  - rewrite (Cost.ticks_bind (Index.find_c positive_encoding s buckets)).
    fold (Index.find positive_encoding s buckets).
    rewrite (Cost.ticks_bind
      (fold_left_c (DomLt.member_c semis s) (Index.find positive_encoding s buckets) st)).
    fold settled.
    rewrite (Cost.ticks_bind (Map.get_c positive_encoding s (DomSemi.parents ranked))).
    fold (Map.get positive_encoding s (DomSemi.parents ranked)).
    destruct (Map.get positive_encoding s (DomSemi.parents ranked)) as [parent|].
    + rewrite (Cost.ticks_bind (DomLink.link_c (DomLt.links settled) s parent)),
        Cost.ticks_ret, DomLinkCost.link_cost, Index.find_cost, !DomCostBasis.get_cost.
      unfold reverse_step_bound. lia.
    + rewrite Cost.ticks_ret, Index.find_cost, !DomCostBasis.get_cost.
      unfold reverse_step_bound. lia.
Qed.

Local Lemma reverse_sum limit buckets order :
  fold_right (fun s rest => 1 + reverse_step_bound limit buckets s + rest) 0 order =
    N.of_nat (length order) * (11 + 5 * key_bits positive_encoding limit) +
      DomBucketCost.mass order buckets * (1 + member_bound limit).
Proof.
  induction order as [|s rest IH]; [reflexivity|].
  unfold reverse_step_bound. cbn [fold_right length]. rewrite Nat2N.inj_succ.
  rewrite <- N.add_1_l.
  unfold DomBucketCost.mass at 1. cbn [fold_right].
  fold (DomBucketCost.mass rest buckets).
  unfold reverse_step_bound in IH. rewrite IH. ring.
Qed.

(** The reverse fold prices the shared inventory across all actually queried buckets. *)
Theorem reverse_cost {L} limit (ranked : DomSemi.layout L) semis buckets order st :
  DomLinkCost.values_bounded limit semis ->
  DomLinkCost.values_bounded limit (DomSemi.parents ranked) -> bounded limit st ->
  (forall s, In s order -> (s <= limit)%positive) ->
  (forall s v, In s order -> In v (Index.find positive_encoding s buckets) ->
    (v <= limit)%positive) ->
  bounded limit
    (Cost.value (fold_left_c (DomLt.reverse_step_c ranked semis buckets) order st)) /\
  Cost.ticks (fold_left_c (DomLt.reverse_step_c ranked semis buckets) order st) <=
    N.of_nat (length order) * (11 + 5 * key_bits positive_encoding limit) +
      DomBucketCost.mass order buckets * (1 + member_bound limit).
Proof.
  intros Hsemis Hparents Hst Hranks Hmembers.
  pose proof (DomCostBasis.fold_left_weighted (DomLt.reverse_step_c ranked semis buckets)
    (bounded limit) (reverse_step_bound limit buckets) order st Hst
    ltac:(intros current s Hcurrent Hs; apply reverse_step_cost;
      [exact Hsemis|exact Hparents|exact Hcurrent|now apply Hranks
      |intros v Hv; exact (Hmembers s v Hs Hv)])) as Hfold.
  destruct Hfold as [Hsupport Hcost]. split; [exact Hsupport|].
  now rewrite reverse_sum in Hcost.
Qed.

Definition correct_bound limit := 8 + 5 * key_bits positive_encoding limit.

(** Forward correction preserves finite support and prices its conditional parent query. *)
Theorem correct_step_cost limit semis provisional corrected v :
  DomLinkCost.values_bounded limit provisional ->
  DomLinkCost.values_bounded limit corrected -> (v <= limit)%positive ->
  DomLinkCost.values_bounded limit
    (Cost.value (DomLt.correct_step_c semis provisional corrected v)) /\
  Cost.ticks (DomLt.correct_step_c semis provisional corrected v) <= correct_bound limit.
Proof.
  intros Hprovisional Hcorrected Hv.
  pose proof (InternCost.bits_monotone v limit Hv) as Hv_width.
  change (key_bits positive_encoding v <= key_bits positive_encoding limit) in Hv_width.
  rewrite DomLt.correct_step_value.
  destruct (Map.get positive_encoding v provisional) as [parent|] eqn:Hparent.
  - assert (Hparent_bound : (parent <= limit)%positive)
      by exact (proj2 Hprovisional v parent Hparent).
    pose proof (InternCost.bits_monotone parent limit Hparent_bound) as Hparent_width.
    change (key_bits positive_encoding parent <= key_bits positive_encoding limit) in Hparent_width.
    split.
    + apply DomLinkCost.values_set; [exact Hcorrected|].
      destruct (Pos.eqb parent (DomLink.identity_value semis v)).
      * exact Hparent_bound.
      * exact (DomLinkCost.identity_bounded limit corrected parent Hcorrected Hparent_bound).
    + unfold DomLt.correct_step_c.
      rewrite (Cost.ticks_bind (Map.get_c positive_encoding v provisional)).
      fold (Map.get positive_encoding v provisional). rewrite Hparent.
      rewrite (Cost.ticks_bind (DomLink.identity_value_c semis v)).
      fold (DomLink.identity_value semis v).
      rewrite (Cost.ticks_bind (positive_eqb_c parent (DomLink.identity_value semis v))).
      assert (Htail : forall direct : bool,
        Cost.ticks
          (let* corrected_parent := if direct then Cost.ret parent
            else DomLink.identity_value_c corrected parent in
           Map.set_c positive_encoding v corrected_parent corrected) <=
          (2 + key_bits positive_encoding limit) + (2 + key_bits positive_encoding limit)).
      { intro direct. apply DomCostBasis.bind_cost.
        - destruct direct; rewrite ?Cost.ticks_ret, ?DomLinkCost.identity_cost; lia.
        - intro parent'. rewrite DomCostBasis.set_cost. lia. }
      pose proof
        (Htail (Cost.value (positive_eqb_c parent (DomLink.identity_value semis v)))) as Hremaining.
      pose proof (proj1 (positive_eqb_cost parent (DomLink.identity_value semis v))) as Hequality.
      change (Cost.ticks (positive_eqb_c parent (DomLink.identity_value semis v)) <=
        key_bits positive_encoding parent) in Hequality.
      rewrite DomCostBasis.get_cost, DomLinkCost.identity_cost.
      unfold correct_bound. lia.
  - split; [exact Hcorrected|].
    unfold DomLt.correct_step_c.
    rewrite (Cost.ticks_bind (Map.get_c positive_encoding v provisional)).
    fold (Map.get positive_encoding v provisional).
    rewrite Hparent, Cost.ticks_ret, DomCostBasis.get_cost.
    unfold correct_bound. lia.
Qed.

Local Lemma correct_cost limit semis provisional order corrected :
  DomLinkCost.values_bounded limit provisional ->
  DomLinkCost.values_bounded limit corrected ->
  (forall v, In v order -> (v <= limit)%positive) ->
  Cost.ticks (fold_left_c (DomLt.correct_step_c semis provisional) order corrected) <=
    N.of_nat (length order) * (9 + 5 * key_bits positive_encoding limit).
Proof.
  intros Hprovisional Hcorrected Hranks.
  pose proof (DomCostBasis.fold_left_weighted (DomLt.correct_step_c semis provisional)
    (DomLinkCost.values_bounded limit) (fun _ => correct_bound limit) order corrected Hcorrected
    ltac:(intros current v Hcurrent Hv; exact (correct_step_cost limit semis provisional
      current v Hprovisional Hcurrent (Hranks v Hv)))) as Hfold.
  destruct Hfold as [Hsupport Hcost].
  assert (Hsum : fold_right (fun _ rest => 1 + correct_bound limit + rest) 0 order =
    N.of_nat (length order) * (9 + 5 * key_bits positive_encoding limit)).
  { clear Hsupport Hcost Hranks. induction order as [|v rest IH]; [reflexivity|].
    cbn [fold_right length]. rewrite Nat2N.inj_succ, IH, <- N.add_1_l.
    unfold correct_bound. ring. }
  now rewrite Hsum in Hcost.
Qed.

Local Lemma empty_values limit : DomLinkCost.values_bounded limit Map.empty.
Proof.
  split; [apply Map.wf_empty|].
  intros v a Hget. rewrite Map.get_empty in Hget. discriminate.
Qed.

(** The complete finisher prices reversal, indexing, all reverse buckets and correction. *)
Theorem finish_cost {V E} limit (shared : DomSemi.semi V E) :
  DomLinkCost.values_bounded limit (DomSemi.semis (DomSemi.settled shared)) ->
  DomLinkCost.values_bounded limit (DomSemi.parents (DomSemi.ranked shared)) ->
  NoDup (DomSemi.reverse_order (DomSemi.ranked shared)) ->
  (forall v, In v (DomSemi.reverse_order (DomSemi.ranked shared)) -> (v <= limit)%positive) ->
  Cost.ticks (DomLt.finish_c shared) <=
    N.of_nat (length (DomSemi.reverse_order (DomSemi.ranked shared))) *
      (33 + 16 * key_bits positive_encoding limit + DomSemiCost.eval_bound limit).
Proof.
  intros Hsemis Hparents Hnodup Hranks.
  set (ranked := DomSemi.ranked shared).
  set (semis := DomSemi.semis (DomSemi.settled shared)).
  set (roots := DomSemi.reverse_order ranked).
  set (order := rev roots).
  assert (Horder : forall v, In v order -> (v <= limit)%positive).
  { intros v Hv. apply Hranks. now apply in_rev. }
  destruct (DomBucketCost.index_cost limit semis roots order Hsemis Hnodup Horder)
    as [Hmass Hindex].
  set (buckets := DomLt.bucket_index semis order).
  fold buckets in Hmass.
  pose proof (reverse_cost limit ranked semis buckets roots (DomLt.State DomLink.empty Map.empty)
    Hsemis Hparents ltac:(split; [apply DomLinkCost.empty_bounded|apply empty_values]) Hranks
    ltac:(intros s v Hs Hv; apply Horder;
      apply (proj2 (DomLtReverse.bucket_index_spec semis order) s v) in Hv;
      exact (proj1 Hv))) as Hreverse.
  destruct Hreverse as [Hstate Hreverse].
  set (reverse := Cost.value (fold_left_c (DomLt.reverse_step_c ranked semis buckets)
    roots (DomLt.State DomLink.empty Map.empty))) in *.
  pose proof (correct_cost limit semis (DomLt.provisional reverse) order Map.empty
    (proj2 Hstate) (empty_values limit) Horder) as Hcorrect.
  assert (Hlength : length order = length roots) by (unfold order; apply length_rev).
  rewrite Hlength in Hindex, Hmass, Hcorrect.
  assert (Hmass_price : DomBucketCost.mass roots buckets * (1 + member_bound limit) <=
    N.of_nat (length roots) * (1 + member_bound limit)).
  { apply N.mul_le_mono; [exact Hmass|reflexivity]. }
  unfold DomLt.finish_c. fold ranked semis roots.
  rewrite (Cost.ticks_bind (rev_c roots)), ticks_rev_c, value_rev_c. fold order.
  rewrite (Cost.ticks_bind (fold_left_c (DomLt.bucket_insert_c semis) order Map.empty)).
  fold buckets.
  rewrite (Cost.ticks_bind (fold_left_c (DomLt.reverse_step_c ranked semis buckets)
    roots (DomLt.State DomLink.empty Map.empty))). fold reverse.
  unfold member_bound in *. nia.
Qed.

Definition finish_bound {V E} (p : Prepared.t V E) :=
  let limit := DomSemiCost.rank_limit p in
  N.of_nat (length (Search.preorder (DomSemi.search (DomSemi.compute p)))) *
    (33 + 16 * key_bits positive_encoding limit + DomSemiCost.eval_bound limit).

(** Readiness discharges every numeric state and bucket duty for the actual LT finisher. *)
Theorem actual_finish_cost {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Cost.ticks (DomLt.finish_c (DomSemi.compute p)) <= finish_bound p.
Proof.
  intro Hready.
  pose proof (finish_cost (DomSemiCost.rank_limit p) (DomSemi.compute p)
    (proj1 (proj1 (DomSemiCost.actual_settlement_cost p Hready)))
    (DomSemiCost.actual_parents_bounded p Hready)
    (DomDfs.settlement_nodup p Hready)
    (fun v Hv => DomSemiCost.actual_rank_bound p v Hready Hv)) as Hfinish.
  rewrite (DomDfs.settlement_order p Hready), length_rev, length_map, length_seq in Hfinish.
  exact Hfinish.
Qed.

End DomLtCost.
