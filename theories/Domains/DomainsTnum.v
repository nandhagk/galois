(** * Known zero and one bits

    Two masks describe independent facts about the bits of a machine word.
    For example, [Tnum 15 128] describes eight-bit words with a clear low nibble.
    Builds on: LatticeCore and the public Bits word and testbit equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsOp.
Import List.ListNotations.

Local Open Scope Z_scope.

(** A set mask bit records a known Boolean value, including contradictory facts. *)
Record tnum : Type := Tnum {
  zeros : Z;
  ones : Z
}.

Definition tnum_normalise (w : width) (t : tnum) : tnum :=
  Tnum (wrap w (zeros t)) (wrap w (ones t)).

Definition tnum_join (w : width) (a b : tnum) : tnum :=
  Tnum (wand w (zeros a) (zeros b)) (wand w (ones a) (ones b)).

Definition tnum_meet (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (zeros a) (zeros b)) (wor w (ones a) (ones b)).

Definition tnum_subset (w : width) (a b : Z) : bool :=
  Z.eqb (wand w a b) (wrap w a).

(** More precise facts contain every known bit of the less precise fact. *)
Definition tnum_lattice (w : width) : lattice tnum :=
  simple
    (fun a b => tnum_subset w (zeros b) (zeros a) &&
      tnum_subset w (ones b) (ones a))
    (Tnum (modulus w - 1) (modulus w - 1)) (tnum_join w).

(** Concretisation reads masks modulo the width and does not impose a word-range premise. *)
Definition tnum_gamma (w : width) (t : tnum) (z : Z) : Prop :=
  Z.land z (wrap w (zeros t)) = 0 /\
  Z.land (wrap w (ones t)) (Z.lnot z) = 0.

(** Low bits of a normalized mask agree with the original mask. *)
Theorem tnum_wrap_bit : forall w m i, 0 <= i < Zpos w ->
  Z.testbit (wrap w m) i = Z.testbit m i.
Proof.
  intros w m i [Hi Hiw]. rewrite testbit_wrap by exact Hi.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw).
Qed.

(** Conjunction of width-normalized masks is conjunction at every low bit. *)
Theorem tnum_and_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wand w a b) i = (Z.testbit a i && Z.testbit b i).
Proof.
  intros w a b i Hi. rewrite testbit_wand_full by lia.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

(** Disjunction of width-normalized masks is disjunction at every low bit. *)
Theorem tnum_or_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wor w a b) i = (Z.testbit a i || Z.testbit b i).
Proof.
  intros w a b i Hi. rewrite testbit_wor_full by lia.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

(** Width-limited complement flips every low bit. *)
Theorem tnum_not_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (wnot w a) i = negb (Z.testbit a i).
Proof.
  intros w a i Hi. rewrite testbit_wnot_full by lia.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

(** Exclusive-or of width-normalized masks is exclusive-or at every low bit. *)
Theorem tnum_xor_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wxor w a b) i = xorb (Z.testbit a i) (Z.testbit b i).
Proof.
  intros w a b i Hi.
  rewrite <- (word_fun2_normalised bvxor wxor w a b eq_refl).
  rewrite testbit_wxor by (try apply wrap_is_word; lia).
  now rewrite !tnum_wrap_bit by exact Hi.
Qed.

(** Mask inclusion is equivalent to inclusion of all its width-relevant set bits. *)
Theorem tnum_subset_bits : forall w a b,
  tnum_subset w a b = true <->
  forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit b i = true.
Proof.
  intros w a b. unfold tnum_subset. rewrite Z.eqb_eq. split.
  - intros Heq i Hi Hbit.
    apply (f_equal (fun z => Z.testbit z i)) in Heq.
    rewrite tnum_and_bit, tnum_wrap_bit, Hbit in Heq by exact Hi.
    exact Heq.
  - intros Hbits. apply (word_ext w); [apply wand_is_word|apply wrap_is_word|].
    intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    + rewrite tnum_and_bit, tnum_wrap_bit by lia.
      destruct (Z.testbit a i) eqn:Ha; [|reflexivity].
      now rewrite (Hbits i ltac:(lia) Ha).
    + rewrite !(word_bits_high w) by
        (try apply wand_is_word; try apply wrap_is_word; lia). reflexivity.
Qed.

(** Transfer equality compares only width-relevant masks. *)
Definition tnum_equiv (w : width) (a b : tnum) : Prop :=
  wrap w (zeros a) = wrap w (zeros b) /\ wrap w (ones a) = wrap w (ones b).

(** Transfer equality is equivalent to agreement at every low bit. *)
Theorem tnum_equiv_bits : forall w a b,
  tnum_equiv w a b <->
  forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros a) i = Z.testbit (zeros b) i /\
    Z.testbit (ones a) i = Z.testbit (ones b) i.
Proof.
  intros w a b. unfold tnum_equiv. split.
  - intros [Hz Ho] i Hi. apply (f_equal (fun z => Z.testbit z i)) in Hz, Ho.
    rewrite !tnum_wrap_bit in Hz, Ho by exact Hi. exact (conj Hz Ho).
  - intro Hbits. split; apply Z.bits_inj'; intros i Hi;
      rewrite !testbit_wrap by exact Hi;
      destruct (i <? Zpos w) eqn:Hlow; cbn; try reflexivity;
      apply Z.ltb_lt in Hlow;
      first [apply (proj1 (Hbits i ltac:(lia)))|apply (proj2 (Hbits i ltac:(lia)))].
Qed.

(** The lattice order reverses the inclusion of known-zero and known-one masks. *)
Theorem tnum_leb_bits : forall w a b,
  leb (tnum_lattice w) a b = true <->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros b) i = true -> Z.testbit (zeros a) i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (ones b) i = true -> Z.testbit (ones a) i = true).
Proof.
  intros w a b.
  change (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a) = true <->
    (forall i, 0 <= i < Zpos w ->
      Z.testbit (zeros b) i = true -> Z.testbit (zeros a) i = true) /\
    (forall i, 0 <= i < Zpos w ->
      Z.testbit (ones b) i = true -> Z.testbit (ones a) i = true)).
  rewrite andb_true_iff, !tnum_subset_bits. reflexivity.
Qed.

(** Join keeps the facts shared by both inputs. *)
Theorem tnum_join_bits : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (zeros (tnum_join w a b)) i =
    (Z.testbit (zeros a) i && Z.testbit (zeros b) i) /\
  Z.testbit (ones (tnum_join w a b)) i =
    (Z.testbit (ones a) i && Z.testbit (ones b) i).
Proof.
  intros w a b i Hi. split; apply tnum_and_bit; exact Hi.
Qed.

(** The bottom masks have every width-relevant bit set. *)
Theorem tnum_all_bits : forall w i, 0 <= i < Zpos w ->
  Z.testbit (modulus w - 1) i = true.
Proof.
  intros w i Hi. rewrite all_ones_bits by lia.
  now apply Z.ltb_lt.
Qed.

(** Reverse mask inclusion and mask intersection satisfy the weak lattice laws. *)
Theorem tnum_laws : forall w, lattice_laws (tnum_lattice w).
Proof.
  intro w. apply simple_laws.
  - intro a. apply andb_true_iff. split; apply tnum_subset_bits; auto.
  - intros a b c Hab Hbc. apply andb_true_iff in Hab, Hbc.
    destruct Hab as [Haz Hao], Hbc as [Hbz Hbo].
    apply andb_true_iff. split; apply tnum_subset_bits; intros i Hi Hbit;
      first [apply (proj1 (tnum_subset_bits w _ _) Haz i Hi),
        (proj1 (tnum_subset_bits w _ _) Hbz i Hi)
      |apply (proj1 (tnum_subset_bits w _ _) Hao i Hi),
        (proj1 (tnum_subset_bits w _ _) Hbo i Hi)]; exact Hbit.
  - intro a. apply andb_true_iff. split; apply tnum_subset_bits;
      intros i Hi _; now apply tnum_all_bits.
  - intros a b. apply andb_true_iff. split; apply tnum_subset_bits;
      intros i Hi Hbit; cbn [tnum_join zeros ones] in Hbit;
      rewrite tnum_and_bit in Hbit by exact Hi; now apply andb_true_iff in Hbit as [? _].
  - intros a b. apply andb_true_iff. split; apply tnum_subset_bits;
      intros i Hi Hbit; cbn [tnum_join zeros ones] in Hbit;
      rewrite tnum_and_bit in Hbit by exact Hi; now apply andb_true_iff in Hbit as [_ ?].
Qed.

(** Mask intersection is the least upper bound for the known-bit order. *)
Theorem tnum_lub : forall w, lub_laws (tnum_lattice w).
Proof.
  intro w. constructor. intros a b c Ha Hb.
  apply tnum_leb_bits in Ha, Hb. destruct Ha as [Haz Hao], Hb as [Hbz Hbo].
  change (leb (tnum_lattice w) (tnum_join w a b) c = true).
  apply tnum_leb_bits. split; intros i Hi Hbit;
    cbn [tnum_join zeros ones]; rewrite tnum_and_bit by exact Hi;
    apply andb_true_iff; auto.
Qed.

(** Mask meaning is equivalent to its independent per-bit implications. *)
Theorem tnum_gamma_bits : forall w t z,
  tnum_gamma w t z <->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros t) i = true -> Z.testbit z i = false) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (ones t) i = true -> Z.testbit z i = true).
Proof.
  intros w t z. unfold tnum_gamma. split.
  - intros [Hz Ho]. split; intros i Hi Hbit.
    + apply (f_equal (fun x => Z.testbit x i)) in Hz.
      rewrite Z.land_spec, tnum_wrap_bit, Z.bits_0, Hbit, andb_true_r in Hz
        by exact Hi. exact Hz.
    + apply (f_equal (fun x => Z.testbit x i)) in Ho.
      rewrite Z.land_spec, tnum_wrap_bit, Z.lnot_spec, Z.bits_0, Hbit in Ho
        by lia. cbn in Ho. now apply negb_false_iff in Ho.
  - intros [Hz Ho]. split; apply Z.bits_inj'; intros i Hi;
      rewrite Z.land_spec, testbit_wrap, ?Z.lnot_spec, Z.bits_0 by exact Hi;
      destruct (i <? Zpos w) eqn:Hlow; cbn; try apply andb_false_r; try reflexivity;
      apply Z.ltb_lt in Hlow.
    + destruct (Z.testbit (zeros t) i) eqn:Hbit; [rewrite (Hz i ltac:(lia) Hbit)|];
        cbn; now rewrite ?andb_false_r.
    + destruct (Z.testbit (ones t) i) eqn:Hbit; [rewrite (Ho i ltac:(lia) Hbit)|];
        reflexivity.
Qed.

(** Forgetting bit facts preserves every represented integer. *)
Theorem tnum_gamma_monotone : forall w a b z,
  leb (tnum_lattice w) a b = true -> tnum_gamma w a z -> tnum_gamma w b z.
Proof.
  intros w a b z Hle Hgamma. apply tnum_leb_bits in Hle.
  apply tnum_gamma_bits in Hgamma. apply tnum_gamma_bits.
  destruct Hle as [Hlez Hleo], Hgamma as [Hz Ho].
  split; intros i Hi Hbit; [apply Hz, Hlez|apply Ho, Hleo]; assumption.
Qed.

(** Contradictory bottom masks denote no integer, including out-of-range integers. *)
Theorem tnum_gamma_bot_empty : forall w z, ~ tnum_gamma w (bot (tnum_lattice w)) z.
Proof.
  intros w z Hgamma. apply tnum_gamma_bits in Hgamma. destruct Hgamma as [Hz Ho].
  pose proof (tnum_all_bits w 0 ltac:(lia)) as Hbit.
  specialize (Hz 0 ltac:(lia) Hbit). specialize (Ho 0 ltac:(lia) Hbit). congruence.
Qed.

Definition tnum_top : tnum := Tnum 0 0.

Definition tnum_const (w : width) (z : Z) : tnum := Tnum (wnot w z) (wrap w z).

(** Top imposes no bit constraint. *)
Theorem tnum_top_sound : forall w z, tnum_gamma w tnum_top z.
Proof.
  intros w z. unfold tnum_gamma, tnum_top. cbn [zeros ones].
  rewrite wrap_0, Z.land_0_r, Z.land_0_l. auto.
Qed.

(** Constant masks describe the normalized integer. *)
Theorem tnum_const_sound : forall w z, tnum_gamma w (tnum_const w z) (wrap w z).
Proof.
  intros w z. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_const zeros ones] in Hbit.
  - rewrite tnum_not_bit in Hbit by exact Hi.
    rewrite tnum_wrap_bit by exact Hi. now apply negb_true_iff in Hbit.
  - rewrite tnum_wrap_bit in Hbit |- * by exact Hi. exact Hbit.
Qed.

(** Normalizing both masks does not change their meaning. *)
Theorem tnum_normalise_sound : forall w a z,
  tnum_gamma w (tnum_normalise w a) z <-> tnum_gamma w a z.
Proof.
  intros w a z. unfold tnum_gamma, tnum_normalise. cbn [zeros ones].
  now rewrite !wrap_wrap.
Qed.

(** Meet denotes the intersection of the two input meanings. *)
Theorem tnum_meet_gamma : forall w a b z,
  tnum_gamma w (tnum_meet w a b) z <-> tnum_gamma w a z /\ tnum_gamma w b z.
Proof.
  intros w a b z. rewrite !tnum_gamma_bits. split.
  - intros [Hz Ho]. split; split; intros i Hi Hbit;
      first [apply (Hz i Hi)|apply (Ho i Hi)];
      cbn [tnum_meet zeros ones]; rewrite tnum_or_bit, Hbit by exact Hi;
      now rewrite ?orb_true_r.
  - intros [[Haz Hao] [Hbz Hbo]]. split; intros i Hi Hbit;
      cbn [tnum_meet zeros ones] in Hbit;
      rewrite tnum_or_bit in Hbit by exact Hi;
      apply orb_true_iff in Hbit as [Hbit|Hbit]; auto.
Qed.

(** Combining compatible facts retains their shared concrete integer. *)
Theorem tnum_meet_sound : forall w a b z,
  tnum_gamma w a z -> tnum_gamma w b z -> tnum_gamma w (tnum_meet w a b) z.
Proof.
  intros w a b z Ha Hb. apply tnum_meet_gamma. now split.
Qed.

(** Meet refines its left input. *)
Theorem tnum_meet_lower_left : forall w a b,
  leb (tnum_lattice w) (tnum_meet w a b) a = true.
Proof.
  intros w a b. apply tnum_leb_bits. split; intros i Hi Hbit;
    cbn [tnum_meet zeros ones]; rewrite tnum_or_bit, Hbit by exact Hi; reflexivity.
Qed.

(** Join contains every integer from either input. *)
Theorem tnum_join_sound : forall w a b z,
  tnum_gamma w a z \/ tnum_gamma w b z -> tnum_gamma w (tnum_join w a b) z.
Proof.
  intros w a b z [Ha|Hb]; eapply tnum_gamma_monotone; try eassumption.
  - apply (join_upper_l (tnum_laws w)).
  - apply (join_upper_r (tnum_laws w)).
Qed.

Definition tnum_min (w : width) (a : tnum) : Z := wrap w (ones a).

Definition tnum_max (w : width) (a : tnum) : Z := wnot w (zeros a).

Definition tnum_mask (w : width) (a : tnum) : Z := wnot w (wor w (zeros a) (ones a)).

(** The value and maximum masks bound each represented integer bitwise. *)
Theorem tnum_value_bounds : forall w a x, tnum_gamma w a x ->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (tnum_min w a) i = true -> Z.testbit x i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit x i = true -> Z.testbit (tnum_max w a) i = true).
Proof.
  intros w a x Hgamma. apply tnum_gamma_bits in Hgamma. destruct Hgamma as [Hz Ho].
  split; intros i Hi Hbit.
  - unfold tnum_min in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hi. now apply Ho.
  - unfold tnum_max. rewrite tnum_not_bit by exact Hi.
    destruct (Z.testbit (zeros a) i) eqn:Hknown; [|reflexivity].
    specialize (Hz i Hi Hknown). congruence.
Qed.

(** A clear uncertainty bit makes both endpoints agree with the concrete bit. *)
Theorem tnum_known_bit : forall w a x i,
  tnum_gamma w a x -> 0 <= i < Zpos w -> Z.testbit (tnum_mask w a) i = false ->
  Z.testbit (tnum_min w a) i = Z.testbit x i /\
  Z.testbit (tnum_max w a) i = Z.testbit x i.
Proof.
  intros w a x i Hgamma Hi Hmask. apply tnum_gamma_bits in Hgamma.
  destruct Hgamma as [Hz Ho]. unfold tnum_mask in Hmask.
  rewrite tnum_not_bit, tnum_or_bit in Hmask by exact Hi.
  unfold tnum_min, tnum_max. rewrite tnum_wrap_bit, tnum_not_bit by exact Hi.
  specialize (Hz i Hi). specialize (Ho i Hi).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
    cbn in *; intuition discriminate.
Qed.

(** Bitwise inclusion between unsigned words implies numerical order. *)
Theorem tnum_bitwise_le : forall w x y,
  is_word w x -> is_word w y ->
  (forall i, 0 <= i < Zpos w -> Z.testbit x i = true -> Z.testbit y i = true) -> x <= y.
Proof.
  intros w x y Hx Hy Hbits.
  assert (Hdiff : Z.ldiff x y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    - specialize (Hbits i ltac:(lia)).
      destruct (Z.testbit x i), (Z.testbit y i); cbn in *; intuition discriminate.
    - rewrite (word_bits_high w x i Hx ltac:(lia)). reflexivity. }
  exact (proj2 (Z.ldiff_le x y (proj1 Hy) Hdiff)).
Qed.

(** Every represented word lies between the minimum and maximum masks. *)
Theorem tnum_unsigned_bounds : forall w a x,
  is_word w x -> tnum_gamma w a x -> tnum_min w a <= x <= tnum_max w a.
Proof.
  intros w a x Hx Ha. destruct (tnum_value_bounds w a x Ha) as [Hlo Hhi].
  split; apply (tnum_bitwise_le w); try assumption;
    try apply wrap_is_word; try apply wnot_is_word.
Qed.

Definition tnum_constant (w : width) (a : tnum) : option Z :=
  if wrap w (zeros a) =? wnot w (ones a) then Some (tnum_min w a) else None.

(** A successful singleton observation identifies every represented word. *)
Theorem tnum_constant_value : forall w a x c,
  is_word w x -> tnum_gamma w a x -> tnum_constant w a = Some c -> x = c.
Proof.
  intros w a x c Hx Ha Hconst. unfold tnum_constant in Hconst.
  destruct (wrap w (zeros a) =? wnot w (ones a)) eqn:Heq; [|discriminate].
  inversion Hconst; subst c. apply Z.eqb_eq in Heq.
  apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho]. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold tnum_min. rewrite tnum_wrap_bit by lia.
    apply (f_equal (fun z => Z.testbit z i)) in Heq.
    rewrite tnum_wrap_bit, tnum_not_bit in Heq by lia.
    specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
      cbn in *; intuition discriminate.
  - rewrite (word_bits_high w x i Hx ltac:(lia)).
    symmetry. apply (word_bits_high w (tnum_min w a) i); [apply wrap_is_word|lia].
Qed.

Definition tnum_empty (w : width) (a : tnum) : bool :=
  negb (Z.eqb (wand w (zeros a) (ones a)) 0).

(** Any represented integer rules out a contradictory mask bit. *)
Theorem tnum_empty_sound : forall w a x,
  tnum_gamma w a x -> tnum_empty w a = false.
Proof.
  intros w a x Ha. unfold tnum_empty. apply negb_false_iff, Z.eqb_eq.
  apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply Z.bits_inj'. intros i Hi. rewrite testbit_wand_full, Z.bits_0 by exact Hi.
  destruct (i <? Zpos w) eqn:Hlow; [|reflexivity]. apply Z.ltb_lt in Hlow.
  specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i); cbn; auto.
  exfalso. specialize (Hz eq_refl). specialize (Ho eq_refl). congruence.
Qed.

(** Both numerical endpoints are represented whenever the masks do not conflict. *)
Theorem tnum_endpoints_sound : forall w a,
  tnum_empty w a = false ->
  tnum_gamma w a (tnum_min w a) /\ tnum_gamma w a (tnum_max w a).
Proof.
  intros w a Hempty. unfold tnum_empty in Hempty.
  apply negb_false_iff, Z.eqb_eq in Hempty.
  assert (Hdisjoint : forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros a) i && Z.testbit (ones a) i = false).
  { intros i Hi. apply (f_equal (fun z => Z.testbit z i)) in Hempty.
    rewrite tnum_and_bit, Z.bits_0 in Hempty by exact Hi. exact Hempty. }
  split; apply tnum_gamma_bits; split; intros i Hi Hbit;
    unfold tnum_min, tnum_max; rewrite ?tnum_wrap_bit, ?tnum_not_bit by exact Hi.
  - specialize (Hdisjoint i Hi). rewrite Hbit in Hdisjoint. exact Hdisjoint.
  - exact Hbit.
  - now rewrite Hbit.
  - specialize (Hdisjoint i Hi). rewrite Hbit, andb_true_r in Hdisjoint.
    now rewrite Hdisjoint.
Qed.

(** An uncertainty bit is set precisely when neither known-bit mask fixes that position. *)
Theorem tnum_mask_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i =
    negb (Z.testbit (zeros a) i || Z.testbit (ones a) i).
Proof.
  intros w a i Hi. unfold tnum_mask. now rewrite tnum_not_bit, tnum_or_bit by exact Hi.
Qed.

(** A submask of the uncertainty mask is disjoint from the known-one value. *)
Theorem tnum_amount_disjoint : forall w a c,
  Z.land c (tnum_mask w a) = c -> Z.land (tnum_min w a) c = 0.
Proof.
  intros w a c Hsub. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - apply (f_equal (fun z => Z.testbit z i)) in Hsub.
    rewrite Z.land_spec, tnum_mask_bit in Hsub by lia.
    unfold tnum_min. rewrite tnum_wrap_bit by lia.
    destruct (Z.testbit c i), (Z.testbit (zeros a) i), (Z.testbit (ones a) i);
      cbn in *; congruence.
  - unfold tnum_min. rewrite (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)).
    reflexivity.
Qed.

(** Every concrete word decomposes into the known-one value and an uncertainty submask. *)
Theorem tnum_decompose : forall w a x,
  is_word w x -> tnum_gamma w a x ->
  exists c, Z.land c (tnum_mask w a) = c /\ x = tnum_min w a + c.
Proof.
  intros w a x Hx Ha. exists (Z.land x (tnum_mask w a)). split.
  - rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
  - assert (Hdisjoint : Z.land (tnum_min w a) (Z.land x (tnum_mask w a)) = 0).
    { apply tnum_amount_disjoint. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. }
    rewrite Z.add_nocarry_lxor by exact Hdisjoint.
    apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
    apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec.
    destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    + unfold tnum_min. rewrite tnum_wrap_bit, tnum_mask_bit by lia.
      specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
      destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
        cbn in *; intuition discriminate.
    + rewrite (word_bits_high w x i Hx ltac:(lia)). unfold tnum_min.
      rewrite (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)). reflexivity.
Qed.

(** For consistent masks the upper endpoint is the sum of the value and uncertainty mask. *)
Theorem tnum_max_value_mask : forall w a,
  tnum_empty w a = false -> tnum_max w a = tnum_min w a + tnum_mask w a.
Proof.
  intros w a Hempty.
  rewrite Z.add_nocarry_lxor by (apply tnum_amount_disjoint; apply Z.land_diag).
  destruct (tnum_endpoints_sound w a Hempty) as [Hmin _].
  apply tnum_gamma_bits in Hmin. destruct Hmin as [Hz _].
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold tnum_max, tnum_min. rewrite tnum_not_bit, tnum_wrap_bit, tnum_mask_bit by lia.
    specialize (Hz i ltac:(lia)). unfold tnum_min in Hz.
    rewrite tnum_wrap_bit in Hz by lia.
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i); cbn in *;
      intuition discriminate.
  - unfold tnum_max, tnum_min, tnum_mask.
    rewrite (word_bits_high w _ i (wnot_is_word w _) ltac:(lia)),
      (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)),
      (word_bits_high w _ i (wnot_is_word w _) ltac:(lia)). reflexivity.
Qed.

(** Normalizing a represented integer does not change any width-relevant bit fact. *)
Theorem tnum_gamma_wrap : forall w a z,
  tnum_gamma w a (wrap w z) <-> tnum_gamma w a z.
Proof.
  intros w a z. rewrite !tnum_gamma_bits. split; intros [Hz Ho]; split;
    intros i Hi Hbit; specialize (Hz i Hi); specialize (Ho i Hi);
    rewrite ?tnum_wrap_bit in * by exact Hi; auto.
Qed.
