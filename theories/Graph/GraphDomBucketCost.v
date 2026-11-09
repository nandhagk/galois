(** * Charged LT bucket inventories

    Each indexed input occurrence contributes to at most one distinct queried bucket root.
    For example, processing every root once inspects at most the number of inserted occurrences.
    Builds on: GraphDomLt, canonical map updates and finite numeric score support. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex BaseInternCost.
From Galois.Graph Require Import GraphDomLt GraphDomLinkCost GraphDomCostBasis.
Import Cost.Notations.

Module DomBucketCost.
Local Open Scope N_scope.

Definition mass roots (buckets : Map.t positive (list positive)) :=
  fold_right (fun s rest =>
    N.of_nat (length (Index.find positive_encoding s buckets)) + rest) 0 roots.

Local Lemma find_set_same (buckets : Map.t positive (list positive)) s row :
  Map.wf positive_encoding buckets ->
  Index.find positive_encoding s (Map.set positive_encoding s row buckets) = row.
Proof.
  intro Hwf. rewrite Index.find_equation, Map.get_set_same by exact Hwf. reflexivity.
Qed.

Local Lemma find_set_other (buckets : Map.t positive (list positive)) s t row :
  Map.wf positive_encoding buckets -> s <> t ->
  Index.find positive_encoding s (Map.set positive_encoding t row buckets) =
    Index.find positive_encoding s buckets.
Proof.
  intros Hwf Hne. rewrite Index.find_equation, Map.get_set_other by
    (try exact positive_encoding_laws; try exact Hwf; exact Hne).
  symmetry. apply Index.find_equation.
Qed.

Local Lemma mass_unchanged roots buckets s row :
  Map.wf positive_encoding buckets -> ~ In s roots ->
  mass roots (Map.set positive_encoding s row buckets) = mass roots buckets.
Proof.
  intro Hwf. induction roots as [|t rest IH]; intro Habsent; [reflexivity|].
  unfold mass at 1 2. cbn [fold_right]. fold (mass rest (Map.set positive_encoding s row buckets)).
  fold (mass rest buckets).
  rewrite find_set_other by (try exact Hwf; intro Heq; subst t; apply Habsent; now left).
  rewrite IH; [reflexivity|intro Hin; apply Habsent; now right].
Qed.

Local Lemma mass_prepend roots buckets s v :
  NoDup roots -> Map.wf positive_encoding buckets ->
  mass roots (Map.set positive_encoding s (v :: Index.find positive_encoding s buckets) buckets) <=
    1 + mass roots buckets.
Proof.
  intros Hroots Hwf. induction Hroots as [|t rest Hfresh Hrest IH].
  - change (0 <= 1 + 0). lia.
  - unfold mass at 1 2. cbn [fold_right].
    fold (mass rest (Map.set positive_encoding s
      (v :: Index.find positive_encoding s buckets) buckets)).
    fold (mass rest buckets).
    destruct (Pos.eq_dec t s) as [->|Hne].
    + rewrite find_set_same by exact Hwf.
      rewrite mass_unchanged by assumption.
      cbn [length]. rewrite Nat2N.inj_succ. lia.
    + rewrite find_set_other by assumption. lia.
Qed.

Local Lemma insert_wf semis buckets v :
  Map.wf positive_encoding buckets ->
  Map.wf positive_encoding (Cost.value (DomLt.bucket_insert_c semis buckets v)).
Proof.
  intro Hwf. rewrite DomLt.bucket_insert_value.
  destruct (Map.get positive_encoding v semis); [now apply Map.wf_set|exact Hwf].
Qed.

Local Lemma insert_mass semis roots buckets v :
  NoDup roots -> Map.wf positive_encoding buckets ->
  mass roots (Cost.value (DomLt.bucket_insert_c semis buckets v)) <= 1 + mass roots buckets.
Proof.
  intros Hroots Hwf. rewrite DomLt.bucket_insert_value.
  destruct (Map.get positive_encoding v semis).
  - now apply mass_prepend.
  - lia.
Qed.

(** One actual insertion has only its queried rank and settled score as key-width duties. *)
Theorem insert_cost limit semis buckets v :
  DomLinkCost.values_bounded limit semis -> (v <= limit)%positive ->
  Cost.ticks (DomLt.bucket_insert_c semis buckets v) <= 6 + 3 * key_bits positive_encoding limit.
Proof.
  intros Hsemis Hv.
  pose proof (InternCost.bits_monotone v limit Hv) as Hwidth.
  change (key_bits positive_encoding v <= key_bits positive_encoding limit) in Hwidth.
  unfold DomLt.bucket_insert_c.
  rewrite (Cost.ticks_bind (Map.get_c positive_encoding v semis)).
  fold (Map.get positive_encoding v semis).
  destruct (Map.get positive_encoding v semis) as [s|] eqn:Hsemi.
  - pose proof (InternCost.bits_monotone s limit (proj2 Hsemis v s Hsemi)) as Hscore.
    change (key_bits positive_encoding s <= key_bits positive_encoding limit) in Hscore.
    rewrite (Cost.ticks_bind (Index.find_c positive_encoding s buckets)),
      Index.find_cost, !DomCostBasis.get_cost, DomCostBasis.set_cost. lia.
  - rewrite Cost.ticks_ret, DomCostBasis.get_cost. lia.
Qed.

Local Lemma fold_cost limit semis roots xs :
  DomLinkCost.values_bounded limit semis -> NoDup roots ->
  (forall v, In v xs -> (v <= limit)%positive) ->
  forall buckets, Map.wf positive_encoding buckets ->
  Map.wf positive_encoding (Cost.value (fold_left_c (DomLt.bucket_insert_c semis) xs buckets)) /\
  mass roots (Cost.value (fold_left_c (DomLt.bucket_insert_c semis) xs buckets)) <=
    mass roots buckets + N.of_nat (length xs) /\
  Cost.ticks (fold_left_c (DomLt.bucket_insert_c semis) xs buckets) <=
    N.of_nat (length xs) * (7 + 3 * key_bits positive_encoding limit).
Proof.
  intros Hsemis Hroots. induction xs as [|v rest IH]; intros Hranks buckets Hwf.
  - split; [exact Hwf|]. split.
    + change (mass roots buckets <= mass roots buckets + 0). lia.
    + rewrite ticks_fold_left_c_nil. change (0 <= 0). lia.
  - specialize (IH ltac:(intros u Hu; apply Hranks; now right)
      (Cost.value (DomLt.bucket_insert_c semis buckets v)) (insert_wf semis buckets v Hwf)).
    destruct IH as [Hwf' [Hmass Hcost]].
    pose proof (insert_mass semis roots buckets v Hroots Hwf) as Hinsert.
    pose proof (insert_cost limit semis buckets v Hsemis (Hranks v (or_introl eq_refl))) as Hprice.
    split; [exact Hwf'|]. split.
    + change (mass roots
        (Cost.value (fold_left_c (DomLt.bucket_insert_c semis) rest
          (Cost.value (DomLt.bucket_insert_c semis buckets v)))) <=
        mass roots buckets + N.of_nat (S (length rest))).
      rewrite Nat2N.inj_succ. lia.
    + rewrite ticks_fold_left_c_cons. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

Local Lemma empty_mass roots : mass roots Map.empty = 0.
Proof.
  induction roots as [|s rest IH]; [reflexivity|].
  unfold mass at 1. cbn [fold_right]. fold (mass rest Map.empty).
  rewrite Index.find_equation, Map.get_empty. cbn [length]. lia.
Qed.

(** Complete indexing prices every insertion and bounds all distinct-root buckets together. *)
Theorem index_cost limit semis roots order :
  DomLinkCost.values_bounded limit semis -> NoDup roots ->
  (forall v, In v order -> (v <= limit)%positive) ->
  mass roots (DomLt.bucket_index semis order) <= N.of_nat (length order) /\
  Cost.ticks (fold_left_c (DomLt.bucket_insert_c semis) order Map.empty) <=
    N.of_nat (length order) * (7 + 3 * key_bits positive_encoding limit).
Proof.
  intros Hsemis Hroots Horder.
  destruct (fold_cost limit semis roots order Hsemis Hroots Horder Map.empty
    (Map.wf_empty positive_encoding)) as [Hwf [Hmass Hcost]].
  rewrite empty_mass in Hmass. split; [exact Hmass|exact Hcost].
Qed.

End DomBucketCost.
