(** * Factored variable shift amounts

    Each uncertainty bit contributes one charged shift-and-join stage.
    For example, the amount mask three combines the four counts zero through three.
    Builds on: DomainsTnumShift and the Cost monad. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsOp.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith DomainsTnumShift.
Import Cost.Notations.

Local Open Scope Z_scope.

Lemma tnum_equiv_leb : forall w a b c,
  tnum_equiv w a b ->
  (leb (tnum_lattice w) a c = true <-> leb (tnum_lattice w) b c = true).
Proof.
  intros w a b c Heq. pose proof (proj1 (tnum_equiv_bits w a b) Heq) as Hbits.
  rewrite !tnum_leb_bits. split; intros [Hz Ho]; split; intros i Hi Hbit;
    specialize (Hbits i Hi) as [Heqz Heqo];
    first [rewrite <- Heqz; now apply Hz|rewrite <- Heqo; now apply Ho|
      rewrite Heqz; now apply Hz|rewrite Heqo; now apply Ho].
Qed.

Lemma tnum_join_leb : forall w a b c,
  leb (tnum_lattice w) (tnum_join w a b) c = true <->
  leb (tnum_lattice w) a c = true /\ leb (tnum_lattice w) b c = true.
Proof.
  intros w a b c. split.
  - intro Hle. split; eapply (leb_trans (tnum_laws w)); try exact Hle.
    + apply (join_upper_l (tnum_laws w)).
    + apply (join_upper_r (tnum_laws w)).
  - intros [Ha Hb]. apply (join_least (tnum_lub w)); assumption.
Qed.

Lemma tnum_map_join : forall sw rw f a b,
  tnum_bit_copy sw rw f ->
  tnum_equiv rw (tnum_map sw rw f (tnum_join sw a b))
    (tnum_join rw (tnum_map sw rw f a) (tnum_map sw rw f b)).
Proof.
  intros sw rw f a b Hcopy. apply tnum_equiv_bits. intros i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]];
    rewrite (proj1 (tnum_join_bits rw _ _ i Hi)),
      (proj2 (tnum_join_bits rw _ _ i Hi));
    cbn [tnum_map zeros ones]; rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hi.
  - rewrite !Hclear by first [apply wnot_is_word|apply wrap_is_word]. auto.
  - rewrite !Hsource by first [apply wnot_is_word|apply wrap_is_word].
    unfold tnum_min, tnum_max. rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hj.
    rewrite (proj1 (tnum_join_bits sw a b j Hj)),
      (proj2 (tnum_join_bits sw a b j Hj)), !negb_involutive. auto.
Qed.

Lemma tnum_map_composition : forall sw mw rw f g a,
  tnum_bit_copy mw rw g -> (forall x, is_word sw x -> is_word mw (f x)) ->
  tnum_equiv rw (tnum_map mw rw g (tnum_map sw mw f a))
    (tnum_map sw rw (fun x => g (f x)) a).
Proof.
  intros sw mw rw f g a Hcopy Hword. apply tnum_equiv_bits. intros i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]];
    cbn [tnum_map zeros ones]; rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hi.
  - rewrite !Hclear by first [apply wnot_is_word|apply wrap_is_word|apply Hword;
      first [apply wnot_is_word|apply wrap_is_word]]. auto.
  - rewrite !Hsource by first [apply wnot_is_word|apply wrap_is_word|apply Hword;
      first [apply wnot_is_word|apply wrap_is_word]].
    unfold tnum_min, tnum_max, tnum_map. cbn [zeros ones].
    rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hj. now rewrite negb_involutive.
Qed.

Lemma tnum_source_composition : forall o w h k i,
  0 <= h -> 0 <= k -> 0 <= i < Zpos w ->
  (match tnum_source o w k i with
   | Some j => tnum_source o w h j
   | None => None
   end) = tnum_source o w (h + k) i.
Proof.
  intros o w h k i Hh Hk Hi. destruct o; cbn [tnum_source]; try reflexivity.
  - destruct (k <=? i) eqn:Hki.
    + apply Z.leb_le in Hki. destruct (h <=? i - k) eqn:Hhi.
      * apply Z.leb_le in Hhi. rewrite (proj2 (Z.leb_le (h + k) i)) by lia. f_equal. lia.
      * apply Z.leb_gt in Hhi. rewrite (proj2 (Z.leb_gt (h + k) i)) by lia. reflexivity.
    + apply Z.leb_gt in Hki. rewrite (proj2 (Z.leb_gt (h + k) i)) by lia. reflexivity.
  - destruct (i + k <? Zpos w) eqn:Hki.
    + apply Z.ltb_lt in Hki. destruct (i + k + h <? Zpos w) eqn:Hhi.
      * apply Z.ltb_lt in Hhi. rewrite (proj2 (Z.ltb_lt (i + (h + k)) (Zpos w)))
          by lia. f_equal. lia.
      * apply Z.ltb_ge in Hhi. rewrite (proj2 (Z.ltb_ge (i + (h + k)) (Zpos w)))
          by lia. reflexivity.
    + apply Z.ltb_ge in Hki. rewrite (proj2 (Z.ltb_ge (i + (h + k)) (Zpos w)))
        by lia. reflexivity.
  - f_equal. lia.
  - rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia. f_equal. f_equal. ring.
  - rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. f_equal. f_equal. ring.
Qed.

Lemma tnum_scalar_value_composition : forall o w h k x,
  0 <= h -> 0 <= k -> is_word w x ->
  tnum_scalar_value o w k (tnum_scalar_value o w h x) =
  tnum_scalar_value o w (h + k) x.
Proof.
  intros o w h k x Hh Hk Hx. apply (word_ext w);
    [apply tnum_scalar_word|apply tnum_scalar_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite !tnum_scalar_bits by (try assumption; try apply tnum_scalar_word; lia).
    pose proof (tnum_source_composition o w h k i Hh Hk ltac:(lia)) as Hcomp.
    destruct (tnum_source o w k i) as [j|] eqn:Hsource.
    + rewrite tnum_scalar_bits by
        (try assumption; exact (tnum_source_range o w k i j Hk ltac:(lia) Hsource)).
      cbn in Hcomp. now rewrite <- Hcomp.
    + cbn in Hcomp. now rewrite <- Hcomp.
  - rewrite !(word_bits_high w) by (try apply tnum_scalar_word; lia). reflexivity.
Qed.

Lemma tnum_scalar_composition : forall o w h k a,
  0 <= h -> 0 <= k ->
  tnum_equiv w (tnum_scalar o w k (tnum_scalar o w h a))
    (tnum_scalar o w (h + k) a).
Proof.
  intros o w h k a Hh Hk.
  pose proof (tnum_map_composition w w w (tnum_scalar_value o w h)
    (tnum_scalar_value o w k) a (tnum_scalar_copy o w k Hk)
    (fun x _ => tnum_scalar_word o w h x)) as Hcomp.
  assert (Hmap : tnum_map w w
    (fun x => tnum_scalar_value o w k (tnum_scalar_value o w h x)) a =
      tnum_scalar o w (h + k) a).
  { unfold tnum_scalar, tnum_map.
    rewrite !tnum_scalar_value_composition by
      (try assumption; first [apply wnot_is_word|apply wrap_is_word]). reflexivity. }
  now rewrite Hmap in Hcomp.
Qed.

Lemma tnum_scalar_zero : forall o w a, tnum_equiv w (tnum_scalar o w 0 a) a.
Proof.
  intros o w a. apply tnum_equiv_bits. intros i Hi.
  assert (Hsource : tnum_source o w 0 i = Some i).
  { destruct o; cbn [tnum_source]; try reflexivity.
    - rewrite (proj2 (Z.leb_le 0 i)) by lia. now rewrite Z.sub_0_r.
    - rewrite Z.add_0_r, (proj2 (Z.ltb_lt i (Zpos w))) by lia. reflexivity.
    - change (Some (Z.min (i + 0) (Zpos w - 1)) = Some i). f_equal. lia.
    - rewrite Z.sub_0_r, Z.mod_small by exact Hi. reflexivity.
    - rewrite Z.add_0_r, Z.mod_small by exact Hi. reflexivity. }
  unfold tnum_scalar, tnum_map. cbn [zeros ones].
  rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
  rewrite !tnum_scalar_bits, Hsource by
    (try lia; try exact Hi; first [apply wnot_is_word|apply wrap_is_word]).
  unfold tnum_min, tnum_max. rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
  now rewrite negb_involutive.
Qed.

Definition tnum_rotation (o : op) : bool :=
  match o with
  | bvrotl | bvrotr => true
  | _ => false
  end.

Definition tnum_stride (o : op) (w : width) (d : Z) : Z :=
  if tnum_rotation o then (2 * d) mod Zpos w else 2 * d.

Lemma tnum_scalar_period : forall o w h k a,
  tnum_rotation o = true -> h mod Zpos w = k mod Zpos w ->
  tnum_scalar o w h a = tnum_scalar o w k a.
Proof.
  intros o w h k a Hrot Hmod. unfold tnum_scalar, tnum_scalar_value.
  destruct o; cbn [tnum_rotation] in Hrot; try discriminate.
  - now rewrite Hmod.
  - assert (Hneg : (-h) mod Zpos w = (-k) mod Zpos w).
    { replace (-h) with (0 - h) by ring. replace (-k) with (0 - k) by ring.
      rewrite (Zminus_mod 0 h), (Zminus_mod 0 k) by lia. now rewrite Hmod. }
    now rewrite Hneg.
Qed.

Lemma tnum_stride_nonnegative : forall o w d, 0 <= d -> 0 <= tnum_stride o w d.
Proof.
  intros o w d Hd. unfold tnum_stride. destruct (tnum_rotation o);
    [apply Z.mod_pos_bound; lia|lia].
Qed.

Lemma tnum_stride_offset_agrees : forall o w d c b a,
  tnum_scalar o w (b + tnum_stride o w d * c) a =
    tnum_scalar o w (b + d * (2 * c)) a.
Proof.
  intros o w d c b a. unfold tnum_stride. destruct (tnum_rotation o) eqn:Hrot.
  - apply tnum_scalar_period; [exact Hrot|].
    rewrite Zplus_mod, Zmult_mod, Z.mod_mod, <- Zmult_mod, <- Zplus_mod by lia.
    f_equal. ring.
  - f_equal. ring.
Qed.

Lemma tnum_stride_agrees : forall o w d c a,
  tnum_scalar o w (tnum_stride o w d * c) a = tnum_scalar o w (d * (2 * c)) a.
Proof.
  intros o w d c a.
  pose proof (tnum_stride_offset_agrees o w d c 0 a) as H.
  now rewrite !Z.add_0_l in H.
Qed.

(** Choices select each set bit of a nonnegative mask independently. *)
Fixpoint tnum_choices (p : positive) (c : Z) : Prop :=
  match p with
  | xH => c = 0 \/ c = 1
  | xO q => exists t, tnum_choices q t /\ c = 2 * t
  | xI q => exists t, tnum_choices q t /\ (c = 2 * t \/ c = 2 * t + 1)
  end.

Lemma tnum_choices_nonnegative : forall p c, tnum_choices p c -> 0 <= c.
Proof.
  intro p. induction p as [p IH|p IH|]; intros c Hchoice; cbn [tnum_choices] in Hchoice.
  - destruct Hchoice as [t [Ht [Hc|Hc]]]; subst c; specialize (IH t Ht); lia.
  - destruct Hchoice as [t [Ht ->]]. specialize (IH t Ht). lia.
  - destruct Hchoice as [Hc|Hc]; subst c; lia.
Qed.

(** Every positive-mask digit incurs a visit and retains the complete recursive expansion. *)
Fixpoint tnum_expand_c (o : op) (w : width) (p : positive) (d : Z) (r : tnum)
    : Cost.t tnum :=
  Cost.step ;;
  match p with
  | xH => Cost.ret (tnum_join w r (tnum_scalar o w d r))
  | xO q => tnum_expand_c o w q (tnum_stride o w d) r
  | xI q => tnum_expand_c o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.

Definition tnum_expand (o : op) (w : width) (p : positive) (d : Z) (r : tnum) : tnum :=
  Cost.value (tnum_expand_c o w p d r).

(** Pure expansion follows the factored shift-and-join recursion. *)
Theorem tnum_expand_equation : forall o w p d r,
  tnum_expand o w p d r =
  match p with
  | xH => tnum_join w r (tnum_scalar o w d r)
  | xO q => tnum_expand o w q (tnum_stride o w d) r
  | xI q => tnum_expand o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.
Proof.
  intros o w p d r. destruct p; unfold tnum_expand; cbn [tnum_expand_c];
    autorewrite with galois_cost; reflexivity.
Qed.

Lemma tnum_scalar_stage_leb : forall o w d k r target,
  0 <= d -> 0 <= k ->
  (leb (tnum_lattice w) (tnum_scalar o w k
     (tnum_join w r (tnum_scalar o w d r))) target = true <->
   leb (tnum_lattice w) (tnum_scalar o w k r) target = true /\
   leb (tnum_lattice w) (tnum_scalar o w (d + k) r) target = true).
Proof.
  intros o w d k r target Hd Hk.
  assert (Hjoin : tnum_equiv w
    (tnum_scalar o w k (tnum_join w r (tnum_scalar o w d r)))
    (tnum_join w (tnum_scalar o w k r) (tnum_scalar o w k (tnum_scalar o w d r))))
    by (apply tnum_map_join; now apply tnum_scalar_copy).
  rewrite (tnum_equiv_leb w _ _ target Hjoin).
  rewrite tnum_join_leb.
  rewrite (tnum_equiv_leb w _ _ target (tnum_scalar_composition o w d k r Hd Hk)).
  reflexivity.
Qed.

(** The accumulator is the exact join of every allowed subset of amount bits. *)
Theorem tnum_expand_join : forall o w p d r target,
  0 <= d ->
  (leb (tnum_lattice w) (tnum_expand o w p d r) target = true <->
   forall c, tnum_choices p c ->
     leb (tnum_lattice w) (tnum_scalar o w (d * c) r) target = true).
Proof.
  intros o w p. induction p as [p IH|p IH|]; intros d r target Hd;
    rewrite tnum_expand_equation.
  - rewrite IH by (now apply tnum_stride_nonnegative).
    assert (Hstage : forall t, tnum_choices p t ->
      (leb (tnum_lattice w)
        (tnum_scalar o w (tnum_stride o w d * t)
          (tnum_join w r (tnum_scalar o w d r))) target = true <->
       leb (tnum_lattice w) (tnum_scalar o w (d * (2 * t)) r) target = true /\
       leb (tnum_lattice w) (tnum_scalar o w (d * (2 * t + 1)) r) target = true)).
    { intros t Ht. pose proof (tnum_choices_nonnegative p t Ht) as Ht0.
      rewrite tnum_scalar_stage_leb by
        (try assumption; pose proof (tnum_stride_nonnegative o w d Hd); nia).
      rewrite tnum_stride_agrees, tnum_stride_offset_agrees.
      replace (d + d * (2 * t)) with (d * (2 * t + 1)) by ring. reflexivity. }
    split.
    + intros H c [t [Ht [Hc|Hc]]]; subst c; specialize (H t Ht);
        apply (Hstage t Ht) in H; tauto.
    + intros H t Ht. apply (Hstage t Ht). split; apply H; exists t; auto.
  - rewrite IH by (now apply tnum_stride_nonnegative). split.
    + intros H c [t [Ht ->]]. rewrite <- tnum_stride_agrees. now apply H.
    + intros H t Ht. rewrite tnum_stride_agrees. apply H. exists t. auto.
  - rewrite tnum_join_leb. split.
    + intros [Hr Hshift] c [-> | ->].
      * replace (d * 0) with 0 by ring.
        apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)). exact Hr.
      * now replace (d * 1) with d by ring.
    + intro H. split.
      * apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)).
        replace 0 with (d * 0) by ring. apply H. now left.
      * replace d with (d * 1) by ring. apply H. now right.
Qed.

Lemma tnum_land_div2 : forall c u,
  Z.land c u = c <->
  Z.land (c / 2) (u / 2) = c / 2 /\
    (Z.testbit c 0 = true -> Z.testbit u 0 = true).
Proof.
  intros c u. split.
  - intro Hland. split.
    + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.div2_bits by exact Hi.
      apply (f_equal (fun z => Z.testbit z (Z.succ i))) in Hland.
      now rewrite Z.land_spec in Hland.
    + apply (f_equal (fun z => Z.testbit z 0)) in Hland.
      rewrite Z.land_spec in Hland. destruct (Z.testbit c 0), (Z.testbit u 0);
        cbn in *; congruence.
  - intros [Htail Hlow]. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hnonzero].
    + destruct (Z.testbit c 0), (Z.testbit u 0); cbn in *; intuition discriminate.
    + apply (f_equal (fun z => Z.testbit z (i - 1))) in Htail.
      rewrite Z.land_spec, !Z.div2_bits in Htail by lia.
      replace (Z.succ (i - 1)) with i in Htail by lia. exact Htail.
Qed.

Lemma tnum_double_div2 : forall t, (2 * t) / 2 = t /\ (2 * t + 1) / 2 = t.
Proof.
  intro t. split.
  - replace (2 * t) with (t * 2) by ring. apply Z.div_mul. lia.
  - replace (2 * t + 1) with (1 + t * 2) by ring.
    rewrite Z.div_add by lia. cbn. ring.
Qed.

Lemma tnum_choices_land : forall p c, tnum_choices p c <-> Z.land c (Zpos p) = c.
Proof.
  intro p. induction p as [p IH|p IH|]; intro c.
  - rewrite tnum_land_div2, (Pos2Z.inj_xI p).
    rewrite (proj2 (tnum_double_div2 (Zpos p))), Z.testbit_odd_0.
    cbn [tnum_choices]. split.
    + intros [t [Ht [-> | ->]]]; rewrite ?(proj1 (tnum_double_div2 t)),
        ?(proj2 (tnum_double_div2 t)); split; try reflexivity; now apply IH.
    + intros [Htail _]. apply IH in Htail. exists (c / 2). split; [exact Htail|].
      pose proof (Z.div2_odd c) as Hsplit. rewrite Z.div2_div in Hsplit.
      destruct (Z.odd c); cbn [Z.b2z] in Hsplit; [right|left]; lia.
  - rewrite tnum_land_div2, (Pos2Z.inj_xO p).
    rewrite (proj1 (tnum_double_div2 (Zpos p))), Z.testbit_even_0.
    cbn [tnum_choices]. split.
    + intros [t [Ht ->]]. rewrite (proj1 (tnum_double_div2 t)), Z.testbit_even_0.
      split; [now apply IH|discriminate].
    + intros [Htail Hlow]. apply IH in Htail. exists (c / 2). split; [exact Htail|].
      pose proof (Z.div2_odd c) as Hsplit. rewrite Z.div2_div, <- Z.bit0_odd in Hsplit.
      destruct (Z.testbit c 0); cbn [Z.b2z] in *;
        [specialize (Hlow eq_refl); discriminate|lia].
  - cbn [tnum_choices]. split.
    + intros [-> | ->]; reflexivity.
    + intro Hland. change (Z.land c (Z.ones 1) = c) in Hland.
      rewrite Z.land_ones in Hland by lia.
      pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Hbounds.
      change (c mod 2 = c) in Hland. lia.
Qed.

Definition tnum_expand_mask_c (o : op) (w : width) (u : Z) (r : tnum) : Cost.t tnum :=
  match u with
  | Zpos p => tnum_expand_c o w p 1 r
  | _ => Cost.ret (tnum_normalise w r)
  end.

Definition tnum_expand_mask (o : op) (w : width) (u : Z) (r : tnum) : tnum :=
  Cost.value (tnum_expand_mask_c o w u r).

(** Expanding a mask computes the exact join over its integer submasks. *)
Theorem tnum_expand_mask_join : forall o w u r target,
  0 <= u ->
  (leb (tnum_lattice w) (tnum_expand_mask o w u r) target = true <->
   forall c, Z.land c u = c ->
     leb (tnum_lattice w) (tnum_scalar o w c r) target = true).
Proof.
  intros o w [|p|p] r target Hu; [| |lia].
  - change (leb (tnum_lattice w) (tnum_normalise w r) target = true <->
      forall c, Z.land c 0 = c ->
        leb (tnum_lattice w) (tnum_scalar o w c r) target = true).
    assert (Hnorm : tnum_equiv w (tnum_normalise w r) r).
    { unfold tnum_equiv, tnum_normalise. cbn [zeros ones]. now rewrite !wrap_wrap. }
    rewrite (tnum_equiv_leb w _ _ target Hnorm). split.
    + intros Hr c Hc. rewrite Z.land_0_r in Hc. subst c.
      apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)). exact Hr.
    + intro H. apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)).
      apply H. reflexivity.
  - change (leb (tnum_lattice w) (tnum_expand o w p 1 r) target = true <->
      forall c, Z.land c (Zpos p) = c ->
        leb (tnum_lattice w) (tnum_scalar o w c r) target = true).
    rewrite tnum_expand_join by lia. setoid_rewrite tnum_choices_land.
    split; intros H c Hc; specialize (H c Hc);
      replace (1 * c) with c in * by ring; exact H.
Qed.

Lemma tnum_expand_base_join : forall o w u base a target,
  0 <= u -> 0 <= base ->
  (leb (tnum_lattice w)
     (tnum_expand_mask o w u (tnum_scalar o w base a)) target = true <->
   forall c, Z.land c u = c ->
     leb (tnum_lattice w) (tnum_scalar o w (base + c) a) target = true).
Proof.
  intros o w u base a target Hu Hb. rewrite tnum_expand_mask_join by exact Hu.
  split; intros H c Hc;
    assert (Hnonneg : 0 <= c) by
      (rewrite <- Hc; apply Z.land_nonneg; right; exact Hu);
    specialize (H c Hc);
    apply (tnum_equiv_leb w _ _ target (tnum_scalar_composition o w base c a Hb Hnonneg));
    exact H.
Qed.

Lemma tnum_submask_word : forall w u c,
  is_word w u -> Z.land c u = c -> is_word w c.
Proof.
  intros w u c Hu Hsub. apply word_of_bits. intros i Hi.
  apply (f_equal (fun z => Z.testbit z i)) in Hsub.
  rewrite Z.land_spec, (word_bits_high w u i Hu Hi), andb_false_r in Hsub. now symmetry.
Qed.

Lemma tnum_submask_bound : forall w u c,
  is_word w u -> Z.land c u = c -> 0 <= c <= u.
Proof.
  intros w u c Hu Hsub. pose proof (tnum_submask_word w u c Hu Hsub) as Hc.
  split; [exact (proj1 Hc)|]. apply (tnum_bitwise_le w); try assumption.
  intros i Hi Hbit. apply (f_equal (fun z => Z.testbit z i)) in Hsub.
  rewrite Z.land_spec, Hbit in Hsub. cbn in Hsub. now symmetry.
Qed.

Lemma tnum_submask_mod : forall c u n,
  0 <= n -> Z.land c u = c ->
  Z.land (c mod 2 ^ n) (u mod 2 ^ n) = c mod 2 ^ n.
Proof.
  intros c u n Hn Hsub. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z_lt_ge_dec i n) as [Hlow|Hhigh].
  - rewrite !Z.mod_pow2_bits_low by exact Hlow.
    apply (f_equal (fun z => Z.testbit z i)) in Hsub. now rewrite Z.land_spec in Hsub.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma tnum_scalar_oversized : forall o w k a,
  tnum_rotation o = false -> Zpos w <= k ->
  tnum_scalar o w k a = tnum_scalar o w (Zpos w) a.
Proof.
  intros o w k a Hrot Hk. unfold tnum_scalar, tnum_scalar_value.
  destruct o; cbn [tnum_rotation] in Hrot; try discriminate; try reflexivity;
    rewrite !Z.min_r by lia; reflexivity.
Qed.

Definition tnum_shift_cutoff (w : width) : Z := tnum_bitlen (Zpos w - 1).

Lemma tnum_shift_cutoff_bound : forall w,
  0 <= tnum_shift_cutoff w /\ Zpos w <= 2 ^ tnum_shift_cutoff w.
Proof.
  intro w. unfold tnum_shift_cutoff, tnum_bitlen.
  destruct (Zpos w - 1 =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. cbn. lia.
  - apply Z.eqb_neq in Hz. pose proof (Z.log2_nonneg (Zpos w - 1)).
    pose proof (Z.log2_spec (Zpos w - 1) ltac:(lia)). lia.
Qed.

Definition tnum_variable_raw_c (o : op) (w : width) (a b : tnum) : Cost.t tnum :=
  let base := tnum_min w b in
  let u := tnum_mask w b in
  let r := tnum_scalar o w base a in
  if tnum_rotation o then tnum_expand_mask_c o w u r else
  let cutoff := 2 ^ tnum_shift_cutoff w in
  let* low := tnum_expand_mask_c o w (u mod cutoff) r in
  Cost.ret (if u <? cutoff then low else tnum_join w low (tnum_scalar o w (Zpos w) a)).

Definition tnum_variable_raw (o : op) (w : width) (a b : tnum) : tnum :=
  Cost.value (tnum_variable_raw_c o w a b).

(** Variable transfer retains the expansion and all saturated-shift work. *)
Theorem tnum_variable_raw_equation : forall o w a b,
  tnum_variable_raw o w a b =
  let base := tnum_min w b in
  let u := tnum_mask w b in
  let r := tnum_scalar o w base a in
  if tnum_rotation o then tnum_expand_mask o w u r else
  let cutoff := 2 ^ tnum_shift_cutoff w in
  let low := tnum_expand_mask o w (u mod cutoff) r in
  if u <? cutoff then low else tnum_join w low (tnum_scalar o w (Zpos w) a).
Proof.
  intros o w a b. unfold tnum_variable_raw, tnum_variable_raw_c.
  destruct (tnum_rotation o); [reflexivity|]. autorewrite with galois_cost.
  destruct (tnum_mask w b <? 2 ^ tnum_shift_cutoff w); reflexivity.
Qed.

(** Every permitted concrete count's scalar transfer lies below the factored result. *)
Theorem tnum_variable_raw_amount_bound : forall o w a b k,
  is_word w k -> tnum_gamma w b k ->
  leb (tnum_lattice w) (tnum_scalar o w k a) (tnum_variable_raw o w a b) = true.
Proof.
  intros o w a b k Hk Hb. destruct (tnum_decompose w b k Hk Hb) as [c [Hc ->]].
  set (target := tnum_variable_raw o w a b).
  assert (Hself : leb (tnum_lattice w) (tnum_variable_raw o w a b) target = true)
    by apply (leb_refl (tnum_laws w)).
  rewrite tnum_variable_raw_equation in Hself.
  cbn zeta in Hself.
  pose proof (wrap_is_word w (ones b)) as Hbase.
  pose proof (wnot_is_word w (wor w (zeros b) (ones b))) as Hu.
  change (is_word w (tnum_min w b)) in Hbase.
  change (is_word w (tnum_mask w b)) in Hu.
  destruct (tnum_rotation o) eqn:Hrot.
  - apply (proj1 (tnum_expand_base_join o w _ _ a target (proj1 Hu) (proj1 Hbase))
      Hself c Hc).
  - pose proof (tnum_shift_cutoff_bound w) as [Hcut Hwidth].
    pose proof (tnum_submask_bound w _ c Hu Hc) as Hcbound.
    destruct (tnum_mask w b <? 2 ^ tnum_shift_cutoff w) eqn:Hhigh.
    + apply Z.ltb_lt in Hhigh. rewrite Z.mod_small in Hself by (unfold is_word in Hu; lia).
      apply (proj1 (tnum_expand_base_join o w _ _ a target (proj1 Hu) (proj1 Hbase))
        Hself c Hc).
    + apply tnum_join_leb in Hself as [Hsmall Hbig].
      destruct (c <? 2 ^ tnum_shift_cutoff w) eqn:Hcsmall.
      * apply Z.ltb_lt in Hcsmall.
        assert (Hpow : 0 < 2 ^ tnum_shift_cutoff w) by (apply Z.pow_pos_nonneg; lia).
        apply (proj1 (tnum_expand_base_join o w _ _ a target
          (proj1 (Z.mod_pos_bound _ _ Hpow)) (proj1 Hbase)) Hsmall).
        pose proof (tnum_submask_mod c (tnum_mask w b) (tnum_shift_cutoff w) Hcut Hc)
          as Hmod. now rewrite Z.mod_small in Hmod by lia.
      * apply Z.ltb_ge in Hcsmall.
        rewrite tnum_scalar_oversized by (try exact Hrot; unfold is_word in Hbase; lia).
        exact Hbig.
Qed.

Definition tnum_variable_c (o : op) (w : width) (a b : tnum) : Cost.t tnum :=
  if tnum_empty w a || tnum_empty w b then Cost.ret (bot (tnum_lattice w))
  else tnum_variable_raw_c o w a b.

Definition tnum_variable (o : op) (w : width) (a b : tnum) : tnum :=
  Cost.value (tnum_variable_c o w a b).

(** The factored result contains every concrete shifted or rotated word. *)
Theorem tnum_variable_sound : forall o w f a b x k,
  tnum_shift_op o -> word_fun2 o = Some f ->
  is_word w x -> is_word w k -> tnum_gamma w a x -> tnum_gamma w b k ->
  tnum_gamma w (tnum_variable o w a b) (f w x k).
Proof.
  intros o w f a b x k Ho Hf Hx Hk Ha Hb.
  unfold tnum_variable, tnum_variable_c.
  rewrite (tnum_empty_sound w a x Ha), (tnum_empty_sound w b k Hb).
  change (tnum_gamma w (tnum_variable_raw o w a b) (f w x k)).
  eapply tnum_gamma_monotone; [apply (tnum_variable_raw_amount_bound o w a b k Hk Hb)|].
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx).
  apply tnum_scalar_sound; try assumption. exact (proj1 Hk).
Qed.
