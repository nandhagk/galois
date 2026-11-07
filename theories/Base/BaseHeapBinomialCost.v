(** * Primitive binomial forest bounds

    These bounds count rank positions and the widths of the cached codes actually compared.
    For example, carrying through three occupied positions pays for three root comparisons.
    Builds on: BaseHeapBinomial and CostList. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseHeapBinomial.
Import List.ListNotations Cost.Notations.

Module HeapBinomialCost.

Local Open Scope N_scope.

(** A width budget covers the cached codes of a finite entry list. *)
Definition bounded {K} w (xs : list (HeapBinomial.entry K)) : Prop :=
  forall e, In e xs -> N.pos (Pos.size (snd (fst e))) <= w.

Local Lemma root_in {K} (t : HeapBinomial.tree K) :
  In (HeapBinomial.root t) (HeapBinomial.tree_entries t).
Proof.
  destruct t. cbn. auto.
Qed.

Local Lemma link_bounded {K} w (a b : HeapBinomial.tree K) :
  bounded w (HeapBinomial.tree_entries a) ->
  bounded w (HeapBinomial.tree_entries b) ->
  bounded w (HeapBinomial.tree_entries (HeapBinomial.link a b)).
Proof.
  intros Ha Hb e Hin. apply HeapBinomial.entries_link in Hin. destruct Hin; auto.
Qed.

Local Lemma forest_head_bounded {K} w (t : HeapBinomial.tree K) h :
  bounded w (HeapBinomial.entries (Some t :: h)) ->
  bounded w (HeapBinomial.tree_entries t).
Proof.
  intros H e Hin. apply H. cbn. apply in_or_app. left. exact Hin.
Qed.

Local Lemma forest_tail_bounded {K} w (s : option (HeapBinomial.tree K)) h :
  bounded w (HeapBinomial.entries (s :: h)) ->
  bounded w (HeapBinomial.entries h).
Proof.
  intros H e Hin. apply H. cbn. apply in_or_app. right. exact Hin.
Qed.

(** A bounded-code link pays for one priority test and at most two code widths. *)
Theorem link_cost {K} w (a b : HeapBinomial.tree K) :
  bounded w (HeapBinomial.tree_entries a) ->
  bounded w (HeapBinomial.tree_entries b) ->
  Cost.ticks (HeapBinomial.link_c a b) <= 1 + 2 * w.
Proof.
  intros Ha Hb. rewrite HeapBinomial.link_cost.
  pose proof (HeapBinomial.precedesb_cost (HeapBinomial.root a) (HeapBinomial.root b)).
  specialize (Ha _ (root_in a)). specialize (Hb _ (root_in b)). lia.
Qed.

(** Insertion charges only visited rank positions and comparisons of roots at those positions. *)
Theorem insert_cost {K} w (t : HeapBinomial.tree K) h :
  bounded w (HeapBinomial.tree_entries t) ->
  bounded w (HeapBinomial.entries h) ->
  Cost.ticks (HeapBinomial.insert_c t h) <=
    (N.of_nat (length h) + 1) * (2 + 2 * w).
Proof.
  revert t. induction h as [|[u|] hs IH]; intros t Ht Hh;
    cbn [HeapBinomial.insert_c]; autorewrite with galois_cost.
  - change (1 <= (0 + 1) * (2 + 2 * w)). nia.
  - fold (HeapBinomial.link t u).
    pose proof (forest_head_bounded w u hs Hh) as Hu.
    pose proof (forest_tail_bounded w (Some u) hs Hh) as Hhs.
    pose proof (link_cost w t u Ht Hu) as Hlink.
    specialize (IH _ (link_bounded w t u Ht Hu) Hhs).
    cbn [length]. rewrite Nat2N.inj_succ. nia.
  - cbn [length]. rewrite Nat2N.inj_succ. lia.
Qed.

(** Melding's rank-position work is linear in the two input widths, including its final carry. *)
Theorem meld_cost {K} w (a b : HeapBinomial.heap K) c :
  bounded w (HeapBinomial.entries a) ->
  bounded w (HeapBinomial.entries b) ->
  bounded w (HeapBinomial.slot_entries c) ->
  Cost.ticks (HeapBinomial.meld_c a b c) <=
    (N.of_nat (length a) + N.of_nat (length b) + 2) * (2 + 2 * w).
Proof.
  revert b c. induction a as [|[x|] xs IH]; intros b c Ha Hb Hc.
  - destruct c as [c|]; cbn [HeapBinomial.meld_c];
      autorewrite with galois_cost; [|nia].
    pose proof (insert_cost w c b Hc Hb). cbn [length]. nia.
  - pose proof (forest_head_bounded w x xs Ha) as Hx.
    pose proof (forest_tail_bounded w (Some x) xs Ha) as Hxs.
    destruct b as [|[y|] ys].
    + destruct c as [c|]; cbn [HeapBinomial.meld_c];
        autorewrite with galois_cost; [|nia].
      change (1 + Cost.ticks (HeapBinomial.insert_c c (Some x :: xs)) <=
        (N.of_nat (length (Some x :: xs)) + 0 + 2) * (2 + 2 * w)).
      pose proof (insert_cost w c (Some x :: xs) Hc Ha). nia.
    + pose proof (forest_head_bounded w y ys Hb) as Hy.
      pose proof (forest_tail_bounded w (Some y) ys Hb) as Hys.
      destruct c as [c|]; cbn [HeapBinomial.meld_c];
        autorewrite with galois_cost; fold (HeapBinomial.link x y);
        pose proof (link_cost w x y Hx Hy);
        specialize (IH ys (Some (HeapBinomial.link x y)) Hxs Hys
          (link_bounded w x y Hx Hy)); cbn [length]; rewrite !Nat2N.inj_succ; nia.
    + pose proof (forest_tail_bounded w None ys Hb) as Hys.
      destruct c as [c|]; cbn [HeapBinomial.meld_c];
        autorewrite with galois_cost.
      * fold (HeapBinomial.link x c).
        pose proof (link_cost w x c Hx Hc).
        specialize (IH ys (Some (HeapBinomial.link x c)) Hxs Hys
          (link_bounded w x c Hx Hc)). cbn [length]. rewrite !Nat2N.inj_succ. nia.
      * specialize (IH ys None Hxs Hys ltac:(intros e Hin; contradiction)).
        cbn [length]. rewrite !Nat2N.inj_succ. nia.
  - pose proof (forest_tail_bounded w None xs Ha) as Hxs.
    destruct b as [|[y|] ys].
    + destruct c as [c|]; cbn [HeapBinomial.meld_c];
        autorewrite with galois_cost; [|nia].
      change (1 + Cost.ticks (HeapBinomial.insert_c c (None :: xs)) <=
        (N.of_nat (length (None :: xs)) + 0 + 2) * (2 + 2 * w)).
      pose proof (insert_cost w c (None :: xs) Hc Ha). nia.
    + pose proof (forest_head_bounded w y ys Hb) as Hy.
      pose proof (forest_tail_bounded w (Some y) ys Hb) as Hys.
      destruct c as [c|]; cbn [HeapBinomial.meld_c];
        autorewrite with galois_cost.
      * fold (HeapBinomial.link y c).
        pose proof (link_cost w y c Hy Hc).
        specialize (IH ys (Some (HeapBinomial.link y c)) Hxs Hys
          (link_bounded w y c Hy Hc)). cbn [length]. rewrite !Nat2N.inj_succ. nia.
      * specialize (IH ys None Hxs Hys ltac:(intros e Hin; contradiction)).
        cbn [length]. rewrite !Nat2N.inj_succ. nia.
    + pose proof (forest_tail_bounded w None ys Hb) as Hys.
      destruct c; cbn [HeapBinomial.meld_c]; autorewrite with galois_cost;
        specialize (IH ys None Hxs Hys ltac:(intros e Hin; contradiction));
        cbn [length]; rewrite !Nat2N.inj_succ; nia.
Qed.

Local Lemma selected_bounded {K} w (h : HeapBinomial.heap K) t rest :
  bounded w (HeapBinomial.entries h) ->
  HeapBinomial.select h = Some (t, rest) ->
  bounded w (HeapBinomial.tree_entries t) /\ bounded w (HeapBinomial.entries rest).
Proof.
  intros Hh Hselect. pose proof (HeapBinomial.select_entries h) as Hentries.
  rewrite Hselect in Hentries. destruct Hentries as [Hin Hcount].
  split; intros e He; apply Hh; apply Hin; auto.
Qed.

(** Selection never increases the rank-position width of its remainder. *)
Theorem select_width {K} (h : HeapBinomial.heap K) t rest :
  HeapBinomial.select h = Some (t, rest) -> (length rest <= length h)%nat.
Proof.
  revert t rest. induction h as [|[u|] xs IH]; intros t rest Hselect;
    rewrite HeapBinomial.select_equation in Hselect; [discriminate| |].
  - destruct (HeapBinomial.select xs) as [[v tail]|] eqn:Htail.
    + specialize (IH v tail eq_refl).
      destruct (HeapBinomial.precedesb (HeapBinomial.root u) (HeapBinomial.root v));
        inversion Hselect; subst; unfold HeapBinomial.digit; destruct xs, tail; cbn in *;
        lia.
    + inversion Hselect. cbn. lia.
  - destruct (HeapBinomial.select xs) as [[v tail]|] eqn:Htail; [|discriminate].
    specialize (IH v tail eq_refl). inversion Hselect; subst.
    unfold HeapBinomial.digit. destruct tail; cbn in *; lia.
Qed.

(** Selection visits each rank position once and compares at most one pair of roots there. *)
Theorem select_cost {K} w (h : HeapBinomial.heap K) :
  bounded w (HeapBinomial.entries h) ->
  Cost.ticks (HeapBinomial.select_c h) <= N.of_nat (length h) * (2 + 2 * w).
Proof.
  induction h as [|[u|] xs IH]; intro Hh.
  - reflexivity.
  - pose proof (forest_head_bounded w u xs Hh) as Hu.
    pose proof (forest_tail_bounded w (Some u) xs Hh) as Hxs.
    specialize (IH Hxs).
    cbn [HeapBinomial.select_c]. autorewrite with galois_cost.
    fold (HeapBinomial.select xs).
    destruct (HeapBinomial.select xs) as [[t rest]|] eqn:Hselect.
    + pose proof (proj1 (selected_bounded w xs t rest Hxs Hselect)) as Ht.
      pose proof (HeapBinomial.precedesb_cost (HeapBinomial.root u) (HeapBinomial.root t)).
      specialize (Hu _ (root_in u)). specialize (Ht _ (root_in t)).
      autorewrite with galois_cost. cbn [length]. rewrite Nat2N.inj_succ. nia.
    + rewrite Cost.ticks_ret. cbn [length]. rewrite Nat2N.inj_succ. nia.
  - specialize (IH (forest_tail_bounded w None xs Hh)).
    cbn [HeapBinomial.select_c]. autorewrite with galois_cost.
    fold (HeapBinomial.select xs).
    destruct (HeapBinomial.select xs) as [[t rest]|]; rewrite Cost.ticks_ret;
      cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Child preparation pays one reversal tick and one mapping tick per child. *)
Theorem children_heap_cost {K} (t : HeapBinomial.tree K) :
  Cost.ticks (HeapBinomial.children_heap_c t) <=
    2 * N.of_nat (length (HeapBinomial.children_heap t)).
Proof.
  destruct t as [e cs]. unfold HeapBinomial.children_heap_c.
  rewrite Cost.ticks_bind, ticks_rev_c.
  pose proof (ticks_map_c_le (fun t : HeapBinomial.tree K => Cost.ret (Some t))
    0 (rev cs) ltac:(intros; reflexivity)) as Hmap.
  rewrite value_rev_c. rewrite HeapBinomial.children_heap_equation, length_map, length_rev.
  rewrite length_rev in Hmap. nia.
Qed.

Local Lemma children_bounded {K} w (t : HeapBinomial.tree K) :
  bounded w (HeapBinomial.tree_entries t) ->
  bounded w (HeapBinomial.entries (HeapBinomial.children_heap t)).
Proof.
  intros H e Hin. apply H. apply HeapBinomial.entries_children. right. exact Hin.
Qed.

(** Minimum removal's primitive work is logarithmic in entry count on canonical forests. *)
Theorem remove_min_cost {K} P w (h : HeapBinomial.heap K) :
  HeapBinomial.forest_valid P 0 h ->
  bounded w (HeapBinomial.entries h) ->
  Cost.ticks (HeapBinomial.remove_min_c h) <=
    16 * N.of_nat (S (Nat.log2 (HeapBinomial.heap_count h))) * (1 + w).
Proof.
  intros Hvalid Hbounded.
  pose proof (select_cost w h Hbounded) as Hselectcost.
  pose proof (HeapBinomial.forest_width P h Hvalid) as Hwidth.
  unfold HeapBinomial.remove_min_c. rewrite Cost.ticks_bind.
  fold (HeapBinomial.select h).
  destruct (HeapBinomial.select h) as [[t rest]|] eqn:Hselect.
  - destruct (selected_bounded w h t rest Hbounded Hselect) as [Ht Hrest].
    pose proof (HeapBinomial.select_rank_bounds P 0 h t rest Hvalid Hselect) as Hrank.
    pose proof (select_width h t rest Hselect) as Hrestwidth.
    pose proof (children_heap_cost t) as Hchildren.
    pose proof (meld_cost w (HeapBinomial.children_heap t) rest None
      (children_bounded w t Ht) Hrest ltac:(intros e Hin; contradiction)) as Hmeld.
    rewrite !Cost.ticks_bind, Cost.ticks_ret. fold (HeapBinomial.children_heap t).
    assert (HwidthN : N.of_nat (length h) <=
      N.of_nat (S (Nat.log2 (HeapBinomial.heap_count h)))) by lia.
    assert (HrankN : N.of_nat (length (HeapBinomial.children_heap t)) <=
      N.of_nat (length h)) by lia.
    assert (HrestN : N.of_nat (length rest) <= N.of_nat (length h)) by lia.
    rewrite Nat2N.inj_succ in *. nia.
  - rewrite Cost.ticks_ret. rewrite Nat2N.inj_succ.
    assert (N.of_nat (length h) <= N.of_nat (S (Nat.log2 (HeapBinomial.heap_count h))))
      by lia.
    rewrite Nat2N.inj_succ in *. nia.
Qed.

End HeapBinomialCost.
