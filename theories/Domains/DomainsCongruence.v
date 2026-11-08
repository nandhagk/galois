(** * Word congruences

    Congruences describe words in one residue class, including exact values and the empty set.
    For example, the eight-bit class 6 modulo 4 normalizes to the class 2 modulo 4.
    Builds on: DomainsTransfer, Bits arithmetic and Stdlib integer divisibility. *)

From Stdlib Require Import ZArith Zcong List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsNumeric DomainsTransfer DomainsTagged.
Import List.ListNotations Cost.Notations.
Local Open Scope Z_scope.

(** Modulus zero denotes an exact integer and bottom denotes no integer. *)
Inductive cong : Type :=
  | CBot
  | Cong (m r : Z).

(** Residue classes describe normalized words at the supplied width. *)
Definition cong_gamma (w : width) (c : cong) (z : Z) : Prop :=
  match c with
  | CBot => False
  | Cong m r => is_word w z /\ (z - r) mod m = 0
  end.

Definition cong_wordb w z := (0 <=? z) && (z <? modulus w).

Local Lemma cong_wordb_spec w z : cong_wordb w z = true <-> is_word w z.
Proof.
  unfold cong_wordb. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. reflexivity.
Qed.

(** Normalization chooses a positive modulus and collapses classes containing at most one word. *)
Definition cong_norm w c :=
  match c with
  | CBot => CBot
  | Cong m r =>
    let m' := Z.abs m in
    if m' =? 0 then
      if cong_wordb w r then Cong 0 r else CBot
    else
      let r' := r mod m' in
      if modulus w <=? m' then
        if cong_wordb w r' then Cong 0 r' else CBot
      else Cong m' r'
  end.

Local Lemma cong_mod_divide a m : a mod m = 0 <-> (m | a).
Proof.
  destruct (Z.eq_dec m 0) as [->|Hnonzero].
  - rewrite Z.mod_0_r. split.
    + intro Hzero. subst a. exists 0. reflexivity.
    + intros [k Hk]. lia.
  - apply Z.mod_divide. exact Hnonzero.
Qed.

Local Lemma cong_mod_abs a m : a mod (Z.abs m) = 0 <-> a mod m = 0.
Proof.
  rewrite !cong_mod_divide.
  split; [apply Z.divide_abs_l|intro H; now apply Z.divide_abs_l].
Qed.

Local Lemma cong_mod_residue z m r : 0 < m ->
  (z - r mod m) mod m = 0 <-> (z - r) mod m = 0.
Proof.
  intro Hm. rewrite (Zminus_mod z (r mod m) m), Z.mod_mod by lia.
  rewrite (Zminus_mod z r m). reflexivity.
Qed.

Local Lemma cong_large_modulus w m r z : modulus w <= m ->
  0 <= r < m -> is_word w z -> ((z - r) mod m = 0 <-> z = r).
Proof.
  intros Hlarge Hr [Hlo Hhi]. pose proof (modulus_pos w).
  rewrite cong_mod_divide. split.
  - intros [k Hk]. assert (k = 0) by nia. nia.
  - intro Heq. subst z. exists 0. ring.
Qed.

(** Normalization preserves the word meaning of raw classes, including negative moduli. *)
Theorem cong_norm_gamma w c z : cong_gamma w (cong_norm w c) z <-> cong_gamma w c z.
Proof.
  destruct c as [|m r]; [reflexivity|].
  unfold cong_norm. destruct (Z.abs m =? 0) eqn:Hm.
  - apply Z.eqb_eq in Hm.
    assert (m = 0) by (destruct m; cbn in Hm; congruence). subst m.
    destruct (cong_wordb w r) eqn:Hr; cbn [cong_gamma]; rewrite Z.mod_0_r.
    + reflexivity.
    + split; [contradiction|]. intros [Hword Hzero].
      assert (z = r) by lia. subst z.
      pose proof (proj2 (cong_wordb_spec w r) Hword). congruence.
  - apply Z.eqb_neq in Hm.
    assert (Hpositive : 0 < Z.abs m) by (pose proof (Z.abs_nonneg m); lia).
    destruct (modulus w <=? Z.abs m) eqn:Hlarge.
    + apply Z.leb_le in Hlarge.
      pose proof (Z.mod_pos_bound r (Z.abs m) Hpositive) as Hr.
      destruct (cong_wordb w (r mod Z.abs m)) eqn:Hwordr; cbn [cong_gamma].
      * rewrite Z.mod_0_r. split; intros [Hword Hz]; split; [exact Hword| |exact Hword|].
        -- apply (proj1 (cong_mod_abs (z - r) m)).
           apply (proj1 (cong_mod_residue z (Z.abs m) r Hpositive)).
           rewrite Hz. apply Z.mod_0_l. lia.
        -- apply (proj2 (cong_mod_abs (z - r) m)) in Hz.
           apply (proj2 (cong_mod_residue z (Z.abs m) r Hpositive)) in Hz.
           apply (proj1 (cong_large_modulus w _ _ _ Hlarge Hr Hword)) in Hz. lia.
      * split; [contradiction|]. intros [Hword Hz].
        apply (proj2 (cong_mod_abs (z - r) m)) in Hz.
        apply (proj2 (cong_mod_residue z (Z.abs m) r Hpositive)) in Hz.
        apply (proj1 (cong_large_modulus w _ _ _ Hlarge Hr Hword)) in Hz. subst z.
        pose proof (proj2 (cong_wordb_spec w _) Hword). congruence.
    + cbn [cong_gamma]. split; intros [Hword Hz]; split; [exact Hword| |exact Hword|].
      * apply (proj1 (cong_mod_abs (z - r) m)).
        apply (proj1 (cong_mod_residue _ _ _ Hpositive)). exact Hz.
      * apply (proj2 (cong_mod_residue _ _ _ Hpositive)).
        now apply (proj2 (cong_mod_abs (z - r) m)).
Qed.

Definition cong_raw_leb a b :=
  match a, b with
  | CBot, _ => true
  | _, CBot => false
  | Cong m r, Cong n s => (m mod n =? 0) && ((r - s) mod n =? 0)
  end.

Definition cong_leb w a b := cong_raw_leb (cong_norm w a) (cong_norm w b).

Definition cong_join w a b :=
  match cong_norm w a, cong_norm w b with
  | CBot, c => c
  | c, CBot => c
  | Cong m r, Cong n s => cong_norm w (Cong (Z.gcd (Z.gcd m n) (r - s)) r)
  end.

(** Gcd join is also widening and narrowing retains the left operand. *)
Definition cong_lattice w : lattice cong := simple (cong_leb w) CBot (cong_join w).

(** CRT intersection rejects incompatible residues before combining congruences. *)
Definition cong_meet w a b :=
  match cong_norm w a, cong_norm w b with
  | CBot, _ | _, CBot => CBot
  | Cong m r, Cong n s =>
    if r mod Z.gcd m n =? s mod Z.gcd m n then
      cong_norm w (Cong (Z.lcm m n) (Z.combinecong m n r s))
    else CBot
  end.

(** Canonical classes have a small positive modulus or an in-range exact value. *)
Definition cong_canonical w c : Prop :=
  match c with
  | CBot => True
  | Cong m r => (m = 0 /\ is_word w r) \/ (0 < m < modulus w /\ 0 <= r < m)
  end.

Local Lemma cong_norm_canonical w c : cong_canonical w (cong_norm w c).
Proof.
  destruct c as [|m r]; [exact I|]. unfold cong_norm.
  destruct (Z.abs m =? 0) eqn:Hm.
  - destruct (cong_wordb w r) eqn:Hr; cbn; [left; split|exact I];
      [reflexivity|now apply cong_wordb_spec].
  - apply Z.eqb_neq in Hm. pose proof (Z.abs_nonneg m).
    destruct (modulus w <=? Z.abs m) eqn:Hlarge.
    + destruct (cong_wordb w (r mod Z.abs m)) eqn:Hr; cbn;
        [left; split|exact I]; [reflexivity|now apply cong_wordb_spec].
    + apply Z.leb_gt in Hlarge. right. split; [lia|apply Z.mod_pos_bound; lia].
Qed.

Local Lemma cong_canonical_fixed w c : cong_canonical w c -> cong_norm w c = c.
Proof.
  destruct c as [|m r]; [reflexivity|].
  intros [[-> Hword]|[[Hpositive Hsmall] Hr]]; unfold cong_norm.
  - cbn. now rewrite (proj2 (cong_wordb_spec w r) Hword).
  - rewrite Z.abs_eq by lia. rewrite (proj2 (Z.eqb_neq m 0)) by lia.
    rewrite Z.mod_small by exact Hr.
    rewrite (proj2 (Z.leb_gt (modulus w) m)) by lia. reflexivity.
Qed.

(** Normalization is idempotent on every raw payload. *)
Theorem cong_norm_idempotent w c : cong_norm w (cong_norm w c) = cong_norm w c.
Proof.
  apply cong_canonical_fixed. apply cong_norm_canonical.
Qed.

Local Lemma cong_raw_leb_spec m r n s :
  cong_raw_leb (Cong m r) (Cong n s) = true <-> (n | m) /\ (n | r - s).
Proof.
  unfold cong_raw_leb. rewrite andb_true_iff, !Z.eqb_eq, !cong_mod_divide. reflexivity.
Qed.

Local Lemma cong_raw_leb_refl c : cong_raw_leb c c = true.
Proof.
  destruct c as [|m r]; [reflexivity|]. apply cong_raw_leb_spec.
  split; [exists 1|exists 0]; ring.
Qed.

Local Lemma cong_raw_leb_trans a b c :
  cong_raw_leb a b = true -> cong_raw_leb b c = true -> cong_raw_leb a c = true.
Proof.
  destruct a as [|m r], b as [|n s], c as [|p t]; intros Hab Hbc;
    try discriminate; try reflexivity.
  apply cong_raw_leb_spec in Hab as [Hnm Hrs].
  apply cong_raw_leb_spec in Hbc as [Hpn Hst]. apply cong_raw_leb_spec. split.
  - destruct Hnm as [k Hk], Hpn as [j Hj]. exists (k * j). nia.
  - destruct Hrs as [k Hk], Hpn as [j Hj], Hst as [l Hl]. exists (k * j + l). nia.
Qed.

Local Lemma cong_raw_leb_gamma w a b z :
  cong_raw_leb a b = true -> cong_gamma w a z -> cong_gamma w b z.
Proof.
  destruct a as [|m r], b as [|n s]; intros Hle Ha; try contradiction; try discriminate.
  destruct Ha as [Hword Hz]. split; [exact Hword|].
  apply cong_raw_leb_spec in Hle as [Hnm Hrs]. apply cong_mod_divide in Hz.
  apply cong_mod_divide. destruct Hnm as [k Hk], Hrs as [j Hj], Hz as [l Hl].
  exists (l * k + j). nia.
Qed.

(** Normalized comparison preserves every word admitted by the left operand. *)
Theorem cong_gamma_monotone w a b z :
  cong_leb w a b = true -> cong_gamma w a z -> cong_gamma w b z.
Proof.
  intros Hle Ha. apply (proj1 (cong_norm_gamma w b z)).
  eapply cong_raw_leb_gamma; [exact Hle|]. now apply (proj2 (cong_norm_gamma w a z)).
Qed.

Local Lemma cong_divide_trans a b c : (a | b) -> (b | c) -> (a | c).
Proof.
  intros [k Hk] [j Hj]. exists (j * k). nia.
Qed.

Local Lemma cong_residue_difference m r : (m | r - r mod m).
Proof.
  destruct (Z.eq_dec m 0) as [->|Hnonzero].
  - rewrite Z.mod_0_r. exists 0. ring.
  - exists (r / m). pose proof (Z.div_mod r m Hnonzero). nia.
Qed.

Local Lemma cong_small_norm_equivalent w m r :
  0 <= m < modulus w -> is_word w r ->
  cong_raw_leb (Cong m r) (cong_norm w (Cong m r)) = true /\
  cong_raw_leb (cong_norm w (Cong m r)) (Cong m r) = true.
Proof.
  intros Hm Hword. unfold cong_norm. rewrite Z.abs_eq by lia.
  destruct (m =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst m.
    rewrite (proj2 (cong_wordb_spec w r) Hword). split; apply cong_raw_leb_refl.
  - rewrite (proj2 (Z.leb_gt (modulus w) m)) by lia.
    split; apply cong_raw_leb_spec; split; try (exists 1; ring).
    + apply cong_residue_difference.
    + destruct (cong_residue_difference m r) as [k Hk]. exists (-k). nia.
Qed.

Local Lemma cong_divisor_bound a d : 0 < a -> 0 <= d -> (d | a) -> d <= a.
Proof.
  intros Ha Hd [k Hk]. destruct (Z.eq_dec d 0) as [->|Hnonzero]; [lia|].
  assert (0 < k) by nia. nia.
Qed.

Local Lemma cong_join_modulus_bound w m r n s :
  cong_canonical w (Cong m r) -> cong_canonical w (Cong n s) ->
  0 <= Z.gcd (Z.gcd m n) (r - s) < modulus w.
Proof.
  intros Ha Hb. pose proof (Z.gcd_nonneg (Z.gcd m n) (r - s)) as Hnonnegative.
  assert (Hdm : (Z.gcd (Z.gcd m n) (r - s) | m)).
  { eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_l]. }
  assert (Hdn : (Z.gcd (Z.gcd m n) (r - s) | n)).
  { eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_r]. }
  destruct Ha as [[-> Hr]|[[Hm Hsmall] Hr]].
  - destruct Hb as [[-> Hs]|[[Hn Hsmall] Hs]].
    + change (0 <= Z.abs (r - s) < modulus w).
      destruct Hr, Hs. split; [apply Z.abs_nonneg|apply Z.abs_lt; lia].
    + pose proof (cong_divisor_bound _ _ Hn Hnonnegative Hdn). lia.
  - pose proof (cong_divisor_bound _ _ Hm Hnonnegative Hdm). lia.
Qed.

Local Lemma cong_canonical_word_residue w m r :
  cong_canonical w (Cong m r) -> is_word w r.
Proof.
  intros [[_ Hword]|[[Hm Hsmall] Hr]]; [exact Hword|]. split; lia.
Qed.

Local Lemma cong_raw_join_upper m r n s :
  let c := Cong (Z.gcd (Z.gcd m n) (r - s)) r in
  cong_raw_leb (Cong m r) c = true /\ cong_raw_leb (Cong n s) c = true.
Proof.
  cbn zeta. split; apply cong_raw_leb_spec; split.
  - eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_l].
  - exists 0. ring.
  - eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_r].
  - destruct (Z.gcd_divide_r (Z.gcd m n) (r - s)) as [k Hk]. exists (-k). nia.
Qed.

Local Lemma cong_join_upper w a b :
  cong_leb w a (cong_join w a b) = true /\ cong_leb w b (cong_join w a b) = true.
Proof.
  pose proof (cong_norm_canonical w a) as Ha. pose proof (cong_norm_canonical w b) as Hb.
  unfold cong_leb, cong_join.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s].
  - split; reflexivity.
  - rewrite (cong_canonical_fixed w _ Hb). split; [reflexivity|apply cong_raw_leb_refl].
  - rewrite (cong_canonical_fixed w _ Ha). split; [apply cong_raw_leb_refl|reflexivity].
  - rewrite cong_norm_idempotent.
    destruct (cong_small_norm_equivalent w _ r (cong_join_modulus_bound w _ _ _ _ Ha Hb)
      (cong_canonical_word_residue w _ _ Ha)) as [Hnorm _].
    destruct (cong_raw_join_upper m r n s) as [Hleft Hright].
    split; eapply cong_raw_leb_trans; eassumption.
Qed.

(** Normalized comparison and gcd joins satisfy the lattice laws. *)
Theorem cong_lattice_laws w : lattice_laws (cong_lattice w).
Proof.
  apply simple_laws.
  - intro a. apply cong_raw_leb_refl.
  - intros a b c. apply cong_raw_leb_trans.
  - intro a. reflexivity.
  - intros a b. exact (proj1 (cong_join_upper w a b)).
  - intros a b. exact (proj2 (cong_join_upper w a b)).
Qed.

Local Lemma cong_abs_multiple m : (m | Z.abs m).
Proof.
  destruct m as [|p|p]; [exists 0|exists 1|exists (-1)]; cbn; ring.
Qed.

Local Lemma cong_norm_raw_lower w c : cong_raw_leb (cong_norm w c) c = true.
Proof.
  destruct c as [|m r]; [reflexivity|]. unfold cong_norm.
  assert (Hresidue : (m | r mod Z.abs m - r)).
  { eapply cong_divide_trans; [apply cong_abs_multiple|].
    destruct (cong_residue_difference (Z.abs m) r) as [k Hk]. exists (-k). nia. }
  destruct (Z.abs m =? 0) eqn:Hm.
  - apply Z.eqb_eq in Hm. assert (m = 0) by (destruct m; cbn in Hm; congruence).
    subst m. destruct (cong_wordb w r); [apply cong_raw_leb_refl|reflexivity].
  - destruct (modulus w <=? Z.abs m).
    + destruct (cong_wordb w (r mod Z.abs m)); [|reflexivity].
      apply cong_raw_leb_spec. split; [exists 0; ring|exact Hresidue].
    + apply cong_raw_leb_spec. split; [apply cong_abs_multiple|exact Hresidue].
Qed.

(** CRT intersection retains every word admitted by both operands. *)
Theorem cong_meet_sound w a b z :
  cong_gamma w a z -> cong_gamma w b z -> cong_gamma w (cong_meet w a b) z.
Proof.
  intros Ha Hb. apply (proj2 (cong_norm_gamma w a z)) in Ha.
  apply (proj2 (cong_norm_gamma w b z)) in Hb. unfold cong_meet.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s]; try contradiction.
  destruct Ha as [Hword Hr], Hb as [_ Hs].
  apply <- Z.cong_iff_0 in Hr. apply <- Z.cong_iff_0 in Hs.
  pose proof (Z.combinecong_complete' z m n r s Hr Hs) as Hcompatible.
  rewrite (proj2 (Z.eqb_eq _ _) Hcompatible).
  apply (proj2 (cong_norm_gamma w _ z)). split; [exact Hword|].
  apply Z.cong_iff_0. rewrite Z.mod_combinecong_lcm. now apply Z.combinecong_complete.
Qed.

(** CRT intersection refines its left operand for every raw input. *)
Theorem cong_meet_lower_left w a b : cong_leb w (cong_meet w a b) a = true.
Proof.
  unfold cong_leb, cong_meet.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s]; try reflexivity.
  destruct (r mod Z.gcd m n =? s mod Z.gcd m n) eqn:Hcompatible; [|reflexivity].
  rewrite cong_norm_idempotent. eapply cong_raw_leb_trans; [apply cong_norm_raw_lower|].
  apply cong_raw_leb_spec. split; [apply Z.divide_lcm_l|].
  apply cong_mod_divide. apply Z.cong_iff_0.
  exact (proj1 (Z.combinecong_sound m n r s (proj1 (Z.eqb_eq _ _) Hcompatible))).
Qed.

Definition cong_raw_rank w c :=
  match c with
  | CBot => 0
  | Cong m _ => if m =? 0 then 1 else 2 + Zpos w - Z.log2 m
  end.

Local Lemma cong_modulus_log_bound w m : 0 < m < modulus w ->
  0 <= Z.log2 m < Zpos w.
Proof.
  intros [Hpositive Hsmall]. split; [apply Z.log2_nonneg|].
  apply (proj1 (Z.log2_lt_pow2 m (Zpos w) Hpositive)). exact Hsmall.
Qed.

Local Lemma cong_raw_rank_bounds w c : cong_canonical w c ->
  0 <= cong_raw_rank w c <= 2 + Zpos w.
Proof.
  destruct c as [|m r]; cbn [cong_raw_rank]; [lia|].
  intros [[-> Hword]|[Hm Hr]]; [cbn; lia|].
  rewrite (proj2 (Z.eqb_neq m 0)) by lia.
  pose proof (cong_modulus_log_bound w m Hm). lia.
Qed.

Local Lemma cong_proper_divisor_log m n :
  0 < m -> 0 < n -> (n | m) -> m <> n -> Z.log2 n < Z.log2 m.
Proof.
  intros Hm Hn [k Hk] Hdifferent.
  assert (Hpositive : 0 < k) by nia.
  assert (Hnotone : k <> 1) by (intro Heq; subst k; nia).
  assert (Hfactor : 2 <= k) by lia.
  assert (Hdouble : 2 * n <= m) by nia.
  pose proof (Z.log2_le_mono (2 * n) m Hdouble).
  rewrite Z.log2_double in * by exact Hn. lia.
Qed.

Local Lemma cong_raw_rank_monotone w a b :
  cong_canonical w a -> cong_canonical w b -> cong_raw_leb a b = true ->
  cong_raw_rank w a <= cong_raw_rank w b.
Proof.
  destruct a as [|m r], b as [|n s]; intros Ha Hb Hle;
    try (exact (proj1 (cong_raw_rank_bounds w _ Hb))); try discriminate.
  apply cong_raw_leb_spec in Hle as [Hdivisor _].
  destruct Ha as [[-> Hr]|[Hm Hr]], Hb as [[-> Hs]|[Hn Hs]];
    cbn [cong_raw_rank]; rewrite ?Z.eqb_refl; try lia.
  - rewrite (proj2 (Z.eqb_neq n 0)) by lia.
    pose proof (cong_modulus_log_bound w n Hn). lia.
  - destruct Hdivisor as [k Hk]. nia.
  - rewrite (proj2 (Z.eqb_neq m 0)), (proj2 (Z.eqb_neq n 0)) by lia.
    pose proof (cong_divisor_bound m n ltac:(lia) ltac:(lia) Hdivisor) as Hnm.
    pose proof (Z.log2_le_mono n m Hnm). lia.
Qed.

Local Lemma cong_same_modulus_reverse m r s :
  cong_raw_leb (Cong m r) (Cong m s) = true ->
  cong_raw_leb (Cong m s) (Cong m r) = true.
Proof.
  intros Hle. apply cong_raw_leb_spec in Hle as [Hm [k Hk]].
  apply cong_raw_leb_spec. split; [exact Hm|exists (-k); nia].
Qed.

Local Lemma cong_raw_rank_strict w a b :
  cong_canonical w a -> cong_canonical w b -> cong_raw_leb a b = true ->
  cong_raw_leb b a = false -> cong_raw_rank w a < cong_raw_rank w b.
Proof.
  destruct a as [|m r], b as [|n s]; intros Ha Hb Hle Hstrict; try discriminate.
  - cbn [cong_raw_rank]. destruct Hb as [[-> Hword]|[Hn Hs]]; cbn; [lia|].
    rewrite (proj2 (Z.eqb_neq n 0)) by lia.
    change (0 < 2 + Zpos w - Z.log2 n).
    pose proof (cong_modulus_log_bound w n Hn). lia.
  - pose proof Hle as Horder. apply cong_raw_leb_spec in Hle as [Hdivisor Hresidue].
    destruct Ha as [[-> Hr]|[Hm Hr]], Hb as [[-> Hs]|[Hn Hs]];
      cbn [cong_raw_rank]; rewrite ?Z.eqb_refl.
    + pose proof (cong_same_modulus_reverse 0 r s Horder). congruence.
    + rewrite (proj2 (Z.eqb_neq n 0)) by lia.
      pose proof (cong_modulus_log_bound w n Hn). lia.
    + destruct Hdivisor as [k Hk]. nia.
    + rewrite (proj2 (Z.eqb_neq m 0)), (proj2 (Z.eqb_neq n 0)) by lia.
      assert (Hdifferent : m <> n).
      { intro Heq. subst n. pose proof (cong_same_modulus_reverse m r s Horder). congruence. }
      pose proof (cong_proper_divisor_log m n ltac:(lia) ltac:(lia) Hdivisor Hdifferent). lia.
Qed.

(** Normalized modulus losses give finite height even without a divisibility invariant. *)
Theorem cong_height w : height_on (cong_lattice w) (fun _ => True).
Proof.
  refine {| rank := fun c => Z.to_nat (cong_raw_rank w (cong_norm w c));
            bound := Z.to_nat (2 + Zpos w) |}.
  - intros c _. apply Z2Nat.inj_le; [|lia|];
      pose proof (cong_raw_rank_bounds w _ (cong_norm_canonical w c)); lia.
  - intros a b _ _ Hle. apply Z2Nat.inj_le.
    + exact (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w a))).
    + exact (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w b))).
    + apply cong_raw_rank_monotone; try apply cong_norm_canonical; exact Hle.
  - intros a b _ _ Hstrict. apply Z2Nat.inj_lt.
    + exact (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w a))).
    + exact (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w (cong_join w a b)))).
    + apply cong_raw_rank_strict; try apply cong_norm_canonical.
      * exact (join_upper_l (cong_lattice_laws w) a b).
      * exact Hstrict.
Defined.

(** Exact values and residue moduli dividing the word modulus form the word invariant. *)
Definition cong_modulus_divides w c : Prop :=
  match cong_norm w c with
  | CBot => True
  | Cong m _ => m = 0 \/ (m | modulus w)
  end.

(** The word-modulus invariant inherits the stronger height on all raw congruences. *)
Theorem cong_height_on w : height_on (cong_lattice w) (cong_modulus_divides w).
Proof.
  refine {| rank := rank (cong_height w); bound := bound (cong_height w) |}.
  - intros a _. exact (rank_bounded (cong_height w) a I).
  - intros a b _ _. exact (rank_monotone (cong_height w) a b I I).
  - intros a b _ _. exact (join_rank_grows (cong_height w) a b I I).
Defined.

Local Lemma cong_top_sound w z : is_word w z -> cong_gamma w (Cong 1 0) z.
Proof.
  intro Hword. split; [exact Hword|apply Z.mod_1_r].
Qed.

(** Wrapping retains only a divisor of the word modulus. *)
Definition cong_wrap_class w m r := cong_norm w (Cong (Z.gcd m (modulus w)) r).

Local Lemma cong_wrap_class_sound w m r z : (z - r) mod m = 0 ->
  cong_gamma w (cong_wrap_class w m r) (wrap w z).
Proof.
  intro Hz. unfold cong_wrap_class. apply (proj2 (cong_norm_gamma w _ _)).
  split; [apply wrap_is_word|]. apply cong_mod_divide. apply cong_mod_divide in Hz.
  pose proof (cong_residue_difference (modulus w) z) as Hwrap.
  rewrite <- wrap_mod in Hwrap.
  destruct (Z.gcd_divide_l m (modulus w)) as [k Hk].
  destruct (Z.gcd_divide_r m (modulus w)) as [j Hj].
  destruct Hz as [l Hl], Hwrap as [n Hn]. exists (l * k - n * j). nia.
Qed.

Definition cong_neg w a :=
  match cong_norm w a with
  | CBot => CBot
  | Cong m r => cong_wrap_class w m (-r)
  end.

Definition cong_add w a b :=
  match cong_norm w a, cong_norm w b with
  | Cong m r, Cong n s => cong_wrap_class w (Z.gcd m n) (r + s)
  | _, _ => CBot
  end.

Definition cong_sub w a b :=
  match cong_norm w a, cong_norm w b with
  | Cong m r, Cong n s => cong_wrap_class w (Z.gcd m n) (r - s)
  | _, _ => CBot
  end.

Definition cong_mul w a b :=
  match cong_norm w a, cong_norm w b with
  | Cong m r, Cong n s =>
    cong_wrap_class w (Z.gcd (m * n) (Z.gcd (m * s) (n * r))) (r * s)
  | _, _ => CBot
  end.

(** Negation retains the wrapped additive inverse of each admitted operand. *)
Theorem cong_neg_sound w a x : cong_gamma w a x -> cong_gamma w (cong_neg w a) (wneg w x).
Proof.
  intro Ha. apply (proj2 (cong_norm_gamma w a x)) in Ha.
  unfold cong_neg. destruct (cong_norm w a) as [|m r]; [contradiction|].
  destruct Ha as [_ Hresidue]. rewrite wneg_value. apply cong_wrap_class_sound.
  apply cong_mod_divide. apply cong_mod_divide in Hresidue.
  destruct Hresidue as [k Hk]. exists (-k). nia.
Qed.

(** Addition retains the gcd residue of both admitted operands under wrapping. *)
Theorem cong_add_sound w a b x y :
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_add w a b) (wadd w x y).
Proof.
  intros Ha Hb. apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold cong_add.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s]; try contradiction.
  destruct Ha as [_ Hx], Hb as [_ Hy]. rewrite wadd_value. apply cong_wrap_class_sound.
  apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
  destruct Hx as [i Hi], Hy as [j Hj].
  destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
  exists (i * k + j * l). nia.
Qed.

(** Subtraction retains the gcd residue of both admitted operands under wrapping. *)
Theorem cong_sub_sound w a b x y :
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_sub w a b) (wsub w x y).
Proof.
  intros Ha Hb. apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold cong_sub.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s]; try contradiction.
  destruct Ha as [_ Hx], Hb as [_ Hy]. rewrite wsub_value. apply cong_wrap_class_sound.
  apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
  destruct Hx as [i Hi], Hy as [j Hj].
  destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
  exists (i * k - j * l). nia.
Qed.

(** Multiplication retains the residue obtained from the constant and variable cross terms. *)
Theorem cong_mul_sound w a b x y :
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_mul w a b) (wmul w x y).
Proof.
  intros Ha Hb. apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold cong_mul.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s]; try contradiction.
  destruct Ha as [_ Hx], Hb as [_ Hy]. rewrite wmul_value. apply cong_wrap_class_sound.
  apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
  destruct Hx as [i Hi], Hy as [j Hj].
  pose (g := Z.gcd (m * n) (Z.gcd (m * s) (n * r))).
  assert (Hmn : (g | m * n)) by apply Z.gcd_divide_l.
  assert (Hms : (g | m * s)).
  { eapply cong_divide_trans; [apply Z.gcd_divide_r|apply Z.gcd_divide_l]. }
  assert (Hnr : (g | n * r)).
  { eapply cong_divide_trans; [apply Z.gcd_divide_r|apply Z.gcd_divide_r]. }
  destruct Hmn as [k Hk], Hms as [l Hl], Hnr as [p Hp].
  exists (i * j * k + i * l + j * p).
  replace (x * y - r * s) with (i * j * (m * n) + i * (m * s) + j * (n * r)) by nia.
  fold g. rewrite Hk, Hl, Hp. ring.
Qed.

Definition cong_project source target a :=
  match cong_norm source a with
  | CBot => CBot
  | Cong m r => cong_wrap_class target m r
  end.

(** Projection retains each operand's low bits at the target width. *)
Theorem cong_project_sound source target a x :
  cong_gamma source a x -> cong_gamma target (cong_project source target a) (wrap target x).
Proof.
  intro Ha. apply (proj2 (cong_norm_gamma source a x)) in Ha.
  unfold cong_project. destruct (cong_norm source a) as [|m r]; [contradiction|].
  apply cong_wrap_class_sound. exact (proj2 Ha).
Qed.

Definition cong_shl w a b :=
  match cong_norm w a, cong_norm w b with
  | CBot, _ | _, CBot => CBot
  | Cong m r, Cong 0 k =>
    if Zpos w <=? k then Cong 0 0 else cong_wrap_class w (m * 2^k) (r * 2^k)
  | _, _ => Cong 1 0
  end.

(** A known shift scales the modulus and residue, including the overshift zero case. *)
Theorem cong_shl_sound w a b x y :
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_shl w a b) (wshl w x y).
Proof.
  intros Ha Hb. apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold cong_shl.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n k]; try contradiction.
  destruct n as [|n|n]; try (apply cong_top_sound; apply wshl_is_word).
  destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
  rewrite Z.mod_0_r in Hy. assert (y = k) by lia. subst y.
  rewrite wshl_value, (wrap_id w k Hwordy), (wrap_id w x Hwordx).
  destruct (Zpos w <=? k).
  - split; [apply zero_is_word|reflexivity].
  - apply cong_wrap_class_sound. apply cong_mod_divide. apply cong_mod_divide in Hx.
    destruct Hx as [i Hi]. exists i. nia.
Qed.

Definition cong_urem w a b :=
  match cong_norm w a, cong_norm w b with
  | CBot, _ | _, CBot => CBot
  | Cong m r, Cong 0 c => cong_norm w (Cong (Z.gcd m c) r)
  | _, _ => Cong 1 0
  end.

(** Known-divisor remainder retains the gcd residue, including divisor zero. *)
Theorem cong_urem_sound w a b x y :
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_urem w a b) (wurem w x y).
Proof.
  intros Ha Hb. apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold cong_urem.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n c]; try contradiction.
  destruct n as [|n|n]; try (apply cong_top_sound; apply wurem_is_word).
  destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
  rewrite Z.mod_0_r in Hy. assert (y = c) by lia. subst y.
  apply (proj2 (cong_norm_gamma w _ _)). split; [apply wurem_is_word|].
  rewrite wurem_mod, (wrap_id w c Hwordy), (wrap_id w x Hwordx).
  apply cong_mod_divide in Hx. apply cong_mod_divide.
  destruct (Z.gcd_divide_l m c) as [k Hk], (Z.gcd_divide_r m c) as [j Hj].
  destruct Hx as [i Hi]. destruct (Z.eq_dec c 0) as [->|Hnonzero].
  - rewrite Z.mod_0_r. exists (i * k). nia.
  - destruct (cong_residue_difference c x) as [l Hl]. exists (i * k - l * j). nia.
Qed.

(** Unary adapters retain both widths and all callback costs. *)
Definition cong_unary (f : width -> width -> cong -> Cost.t cong)
    rw (xs : list (width * cong)) :=
  match xs with
  | [(w, a)] => Cost.step ;; f w rw a
  | _ => Cost.ret (Cong 1 0)
  end.

(** Binary adapters call their charged scalar callback when both widths match. *)
Definition cong_binary (f : width -> cong -> cong -> Cost.t cong)
    rw (xs : list (width * cong)) :=
  match xs with
  | [(wa, a); (wb, b)] =>
    if Pos.eqb wa rw && Pos.eqb wb rw then Cost.step ;; f rw a b else Cost.ret (Cong 1 0)
  | _ => Cost.ret (Cong 1 0)
  end.

(** Selection joins the normalized branch classes at the result width. *)
Definition cong_select rw (xs : list (width * cong)) :=
  Cost.step ;; Cost.ret
    (match xs with
     | [_; (wa, a); (wb, b)] =>
       if Pos.eqb wa rw && Pos.eqb wb rw then cong_join rw a b else Cong 1 0
     | _ => Cong 1 0
     end).

(** The table lists modular arithmetic, extensions, truncation and selection. *)
Definition cong_table : Transfer.table (width * cong) cong op width :=
  {| Transfer.fwd := fun o n => Cost.ret
       (match o, n with
        | bvneg, 1%nat => Some (cong_unary
          (fun source target a => Cost.step ;; Cost.ret
            (if Pos.eqb source target then cong_neg target a else Cong 1 0)))
        | bvzext _, 1%nat => Some (cong_unary
          (fun source target a => Cost.step ;; Cost.ret
            (if Pos.leb source target then cong_norm target a else Cong 1 0)))
        | bvtrunc _, 1%nat => Some (cong_unary
          (fun source target a => Cost.step ;; Cost.ret (cong_project source target a)))
        | bvadd, 2%nat => Some (cong_binary (fun w a b => Cost.step ;; Cost.ret (cong_add w a b)))
        | bvsub, 2%nat => Some (cong_binary (fun w a b => Cost.step ;; Cost.ret (cong_sub w a b)))
        | bvmul, 2%nat => Some (cong_binary (fun w a b => Cost.step ;; Cost.ret (cong_mul w a b)))
        | bvshl, 2%nat => Some (cong_binary (fun w a b => Cost.step ;; Cost.ret (cong_shl w a b)))
        | bvurem, 2%nat => Some (cong_binary (fun w a b => Cost.step ;; Cost.ret (cong_urem w a b)))
        | bvite, 3%nat => Some cong_select
        | _, _ => None
        end);
     Transfer.bwd := fun _ _ => Cost.ret None |}.

(** Bounded lookahead keeps arbitrary-list traversal outside the scalar evaluator. *)
Definition cong_eval_c o (xs : list word) :=
  match xs with
  | _ :: _ :: _ :: _ :: _ => Cost.ret None
  | _ => Cost.step ;; Cost.ret (eval_op o xs)
  end.

Local Lemma cong_eval_equation o xs : Cost.value (cong_eval_c o xs) = eval_op o xs.
Proof.
  destruct xs as [|a [|b [|c [|d rest]]]]; try reflexivity.
  destruct (eval_op o (a :: b :: c :: d :: rest)) as [r|] eqn:He; [|reflexivity].
  pose proof (eval_op_arity o _ r He) as Hlen.
  destruct o; cbn in Hlen; discriminate.
Qed.

(** Normalization detects empty classes and exact points before table dispatch. *)
Definition cong_shape : Transfer.shape (width * cong) cong op width word :=
  {| Transfer.eval_c := cong_eval_c;
     Transfer.point_c := fun wp => Cost.step ;; Cost.ret
       (match cong_norm (fst wp) (snd wp) with
        | Cong 0 r => Some (fst wp, r)
        | _ => None
        end);
     Transfer.is_empty_c := fun wp => Cost.step ;; Cost.ret
       (match cong_norm (fst wp) (snd wp) with CBot => true | _ => false end);
     Transfer.inj_c := fun _ c => Cost.step ;; Cost.ret (Cong 0 (snd c));
     Transfer.bot_out := fun _ => CBot;
     Transfer.top_out := fun _ => Cong 1 0;
     Transfer.keep_c := fun wp => Cost.ret (snd wp) |}.

(** The congruence domain shares concrete points, empty operands and backward identity. *)
Definition cong_word_domain : word_domain cong :=
  word_of_table cong_table cong_shape cong_lattice (fun _ => Cong 1 0)
    (fun w z => Cost.step ;; Cost.ret (Cong 0 (wrap w z)))
    (fun w a b => Cost.step ;; Cost.ret (cong_meet w a b)).

Local Lemma cong_shape_laws :
  transfer_sem cong_shape (payload_sound cong_gamma) (word_output cong_gamma) word_context.
Proof.
  constructor.
  - intros [w a] [v x] [u y] Hpoint [Hw [Hy Ha]].
    cbn in Hw. subst u. cbn in Ha.
    apply (proj2 (cong_norm_gamma w a y)) in Ha.
    change ((match cong_norm w a with
      | Cong 0 r => Some (w, r)
      | _ => None
      end) = Some (v, x)) in Hpoint.
    destruct (cong_norm w a) as [|[|m|m] r]; try discriminate.
    inversion Hpoint; subst v x. destruct Ha as [_ Hr].
    rewrite Z.mod_0_r in Hr. f_equal. lia.
  - intros [w a] [v x] Hempty [Hw [_ Ha]].
    cbn in Hw. subst v. cbn in Ha.
    apply (proj2 (cong_norm_gamma w a x)) in Ha.
    change ((match cong_norm w a with CBot => true | _ => false end) = true) in Hempty.
    destruct (cong_norm w a); [exact Ha|discriminate].
  - intros r [w z] [_ Hword]. split; [exact Hword|]. rewrite Z.sub_diag. reflexivity.
  - intros r c H. exact H.
  - intros r [w z] [_ Hword]. now apply cong_top_sound.
  - intros r [w a] [v z] [Hw [_ Ha]]. cbn in Hw. subst v. exact Ha.
Qed.

Local Lemma cong_unary_sound o f rw xs cs c :
  (forall source a x target z, cong_gamma source a x ->
    eval_op o [(source, x)] = Some (target, z) ->
    cong_gamma target (Cost.value (f source target a)) z) ->
  length xs = 1%nat -> Forall2 (payload_sound cong_gamma) xs cs ->
  eval_op o cs = Some c -> word_context rw c ->
  word_output cong_gamma rw (Cost.value (cong_unary f rw xs)) c.
Proof.
  intros Hf Hlen Hxs Heval Hcontext.
  destruct xs as [|[w a] [|wp rest]]; cbn in Hlen; try discriminate.
  inversion Hxs as [|? [v x] ? ? Hhead Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hw [Hx Ha]]. cbn in Hw, Ha. subst v.
  destruct c as [target z]. destruct Hcontext as [Hctx Hword]. cbn in Hctx. subst rw.
  change (cong_gamma target (Cost.value (f w target a)) z). now apply (Hf w a x).
Qed.

Local Lemma cong_binary_sound o f rw xs cs c :
  (forall w a b x y, cong_gamma w a x -> cong_gamma w b y ->
    cong_gamma w (Cost.value (f w a b))
      (match word_fun2 o with Some g => g w x y | None => 0 end)) ->
  (exists g, word_fun2 o = Some g) ->
  length xs = 2%nat -> Forall2 (payload_sound cong_gamma) xs cs ->
  eval_op o cs = Some c -> word_context rw c ->
  word_output cong_gamma rw (Cost.value (cong_binary f rw xs)) c.
Proof.
  intros Hf [g Hg] Hlen Hxs Heval Hcontext.
  destruct xs as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate.
  inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
  inversion Htail as [|? [vy y] ? ? Hhead' Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
  cbn in Hwx, Hvy, Ha, Hb. subst wx vy. destruct c as [target z].
  destruct Hcontext as [Hctx Hword].
  cbn in Hctx. subst rw.
  assert (Hw : w = v) by exact (eval_op_fun2_width o g w v x y (target, z) Hg Heval).
  subst v. pose proof (eq_trans (eq_sym (eval_op_fun2 o w x y g Hg)) Heval) as Hr.
  inversion Hr; subst target z.
  change (cong_gamma w (Cost.value
    (if Pos.eqb w w && Pos.eqb w w then Cost.step ;; f w a b else Cost.ret (Cong 1 0)))
    (g w x y)).
  rewrite Pos.eqb_refl. specialize (Hf w a b x y Ha Hb). now rewrite Hg in Hf.
Qed.

Local Lemma cong_select_sound rw xs cs c :
  length xs = 3%nat -> Forall2 (payload_sound cong_gamma) xs cs ->
  eval_op bvite cs = Some c -> word_context rw c ->
  word_output cong_gamma rw (Cost.value (cong_select rw xs)) c.
Proof.
  intros Hlen Hxs Heval Hcontext.
  destruct xs as [|[w a] [|[v b] [|[u d] [|wp rest]]]];
    cbn in Hlen; try discriminate.
  inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
  inversion Htail as [|? [vy y] ? ? Hhead' Htail']; subst.
  inversion Htail' as [|? [uz z] ? ? Hhead'' Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]],
    Hhead'' as [Huz [Hz Hd]].
  cbn in Hwx, Hvy, Huz, Ha, Hb, Hd. subst wx vy uz.
  destruct (eval_op_ite_width w v u x y z c Heval) as [Hw Hvu]. subst w u.
  destruct c as [target result]. destruct Hcontext as [Hctx Hword]. cbn in Hctx. subst rw.
  rewrite eval_op_ite in Heval.
  destruct (wrap 1%positive x =? 1); inversion Heval; subst target result;
    unfold word_output, cong_select; autorewrite with galois_cost; cbn [fst snd];
    rewrite Pos.eqb_refl.
  - rewrite (wrap_id v y Hy). eapply cong_gamma_monotone;
      [exact (proj1 (cong_join_upper v b d))|exact Hb].
  - rewrite (wrap_id v z Hz). eapply cong_gamma_monotone;
      [exact (proj2 (cong_join_upper v b d))|exact Hd].
Qed.

Local Lemma cong_zext_sound extra source a x target z :
  cong_gamma source a x -> eval_op (bvzext extra) [(source, x)] = Some (target, z) ->
  cong_gamma target
    (if Pos.leb source target then cong_norm target a else Cong 1 0) z.
Proof.
  intros Ha Heval. rewrite eval_zext_value in Heval. inversion Heval; subst target z.
  assert (Hwidth : (source <= source + extra)%positive) by apply width_add_le.
  rewrite (proj2 (Pos.leb_le _ _) Hwidth).
  apply (proj2 (cong_norm_gamma _ _ _)).
  destruct a as [|m r]; [contradiction|]. destruct Ha as [Hx Hr].
  rewrite (wrap_id source x Hx). split; [eapply word_widen; eassumption|exact Hr].
Qed.

Local Lemma cong_trunc_sound t source a x target z :
  cong_gamma source a x -> eval_op (bvtrunc t) [(source, x)] = Some (target, z) ->
  cong_gamma target (cong_project source target a) z.
Proof.
  intros Ha Heval. rewrite eval_op_trunc in Heval.
  destruct (Pos.leb t source) eqn:Hwidth; [|discriminate].
  inversion Heval; subst target z.
  assert (Hx : is_word source x) by (destruct a; [contradiction|exact (proj1 Ha)]).
  rewrite (wrap_id source x Hx). now apply cong_project_sound.
Qed.

(** Every supplied modular transfer preserves exact word evaluation. *)
Theorem cong_table_laws :
  table_laws cong_table cong_shape (payload_sound cong_gamma)
    (word_output cong_gamma) word_context.
Proof.
  constructor.
  - intros o n f rw xs cs c Hf Hlen Hxs Heval Hctx.
    change (Cost.value (cong_eval_c o cs) = Some c) in Heval.
    rewrite cong_eval_equation in Heval.
    destruct o; destruct n as [|[|[|[|n]]]]; cbn in Hf; try discriminate;
      injection Hf as <-.
    all: first
      [eapply cong_unary_sound; [|exact Hlen|exact Hxs|exact Heval|exact Hctx]
      |match type of Heval with
       | eval_op ?k _ = _ =>
         eapply (cong_binary_sound k _ rw xs cs c);
           [|eexists; reflexivity|exact Hlen|exact Hxs|exact Heval|exact Hctx]
       end
      |exact (cong_select_sound rw xs cs c Hlen Hxs Heval Hctx)].
    all: intros; autorewrite with galois_cost;
      try solve [now apply cong_add_sound|now apply cong_sub_sound|
      now apply cong_mul_sound|now apply cong_urem_sound|now apply cong_shl_sound|
      eapply cong_zext_sound; eassumption|eapply cong_trunc_sound; eassumption].
    match goal with
    | He : eval_op bvneg [(?w, ?x)] = Some (?t, ?z) |- _ =>
      pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) He) as Hr;
      inversion Hr; subst t z; rewrite Pos.eqb_refl; now apply cong_neg_sound
    end.
  - intros o n f rw q xs cs c Hf. discriminate Hf.
  - intros o n f rw q xs Hf. discriminate Hf.
Qed.

(** Congruence backward transfer is the harness's reductive identity default. *)
Theorem cong_table_refines :
  table_refines cong_table cong_shape
    (fun wp q => leb (cong_lattice (fst wp)) q (snd wp) = true).
Proof.
  constructor.
  - intros [w a]. apply (leb_refl (cong_lattice_laws w)).
  - intros o n f rw q xs Hf. discriminate Hf.
Qed.

(** Congruences satisfy word evaluation, CRT intersection and backward refinement laws. *)
Theorem cong_word_laws : word_laws cong_word_domain cong_gamma.
Proof.
  apply word_of_table_laws.
  - exact cong_eval_equation.
  - exact cong_shape_laws.
  - exact cong_table_laws.
  - exact cong_lattice_laws.
  - exact cong_gamma_monotone.
  - intros w z H. exact H.
  - exact cong_top_sound.
  - intros. split; [apply wrap_is_word|]. rewrite Z.sub_diag. reflexivity.
  - exact cong_table_refines.
  - exact cong_meet_sound.
  - exact cong_meet_lower_left.
Qed.

(** Width tagging supplies numeric soundness and refinement for congruences. *)
Theorem cong_numeric_laws :
  numeric_laws (tagged_domain cong_word_domain) (tagged_gamma cong_gamma).
Proof.
  apply tagged_numeric_laws. exact cong_word_laws.
Qed.

#[export] Hint Resolve cong_neg_sound cong_add_sound cong_sub_sound cong_mul_sound
  cong_project_sound cong_shl_sound cong_urem_sound cong_meet_sound : galois_gamma.
