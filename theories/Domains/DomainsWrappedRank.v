(** * Logarithmic circular widening rank

    Expansion consumes a logarithmic size credit whenever the next arc escapes containment.
    For example, the full circle has rank zero.
    Builds on: DomainsWrapped and LatticeHeight. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsWrapped.

Local Open Scope Z_scope.

Definition wrapped_size_rank (w : width) (size : Z) : Z :=
  if size =? 0 then Zpos w + 2 else
  if size =? modulus w then 0 else Zpos w + 1 - Z.log2 size.

Local Lemma wrapped_size_rank_bounds w size :
  0 <= size <= modulus w -> 0 <= wrapped_size_rank w size <= Zpos w + 2.
Proof.
  intro Hsize. unfold wrapped_size_rank.
  destruct (size =? 0) eqn:Hzero; [lia|].
  destruct (size =? modulus w) eqn:Hfull; [lia|].
  pose proof (Z.log2_nonneg size) as Hnonneg.
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)) as Hlog.
  rewrite modulus_log2 in Hlog. lia.
Qed.

Local Lemma wrapped_size_rank_positive w size :
  0 <= size < modulus w -> 0 < wrapped_size_rank w size.
Proof.
  intro Hsize. unfold wrapped_size_rank.
  destruct (size =? 0) eqn:Hzero; [lia|].
  destruct (size =? modulus w) eqn:Hfull; [apply Z.eqb_eq in Hfull; lia|].
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)) as Hlog.
  rewrite modulus_log2 in Hlog. lia.
Qed.

Local Lemma wrapped_size_rank_progress w old next :
  0 <= old < modulus w -> 0 < next <= modulus w ->
  Z.min (modulus w) (3 * old) <= next ->
  wrapped_size_rank w next < wrapped_size_rank w old.
Proof.
  intros Hold Hnext Hgrow.
  pose proof (wrapped_size_rank_positive w old Hold) as Hpositive.
  unfold wrapped_size_rank.
  destruct (next =? 0) eqn:Hnext_zero; [apply Z.eqb_eq in Hnext_zero; lia|].
  destruct (next =? modulus w) eqn:Hnext_full.
  - unfold wrapped_size_rank in Hpositive. exact Hpositive.
  - apply Z.eqb_neq in Hnext_full.
    destruct (old =? 0) eqn:Hold_zero.
    + pose proof (Z.log2_nonneg next). lia.
    + apply Z.eqb_neq in Hold_zero.
      destruct (old =? modulus w) eqn:Hold_full; [apply Z.eqb_eq in Hold_full; lia|].
      assert (Hdouble : 2 * old <= next) by lia.
      pose proof (Z.log2_le_mono (2 * old) next Hdouble) as Hlog.
      rewrite Z.log2_double in Hlog by lia. lia.
Qed.

(** Only bottom has zero cardinality. *)
Theorem wrapped_size_zero w a : wrapped_size w a = 0 <-> a = WBot.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_size].
  - tauto.
  - pose proof (modulus_pos w). split; [lia|discriminate].
  - pose proof (wrapped_offset_range w lo hi). split; [lia|discriminate].
Qed.

(** Every arc of full cardinality contains every circular payload. *)
Theorem wrapped_full_contains w a b :
  wrapped_size w a = modulus w -> wrapped_leb w b a = true.
Proof.
  intro Hsize. apply wrapped_leb_spec. intros z Hz.
  pose proof (wrapped_gamma_word w b z Hz) as Hword.
  destruct a as [| |lo hi]; cbn [wrapped_size wrapped_gamma] in *.
  - pose proof (modulus_pos w). lia.
  - exact Hword.
  - split; [exact Hword|]. pose proof (wrapped_offset_range w lo z). lia.
Qed.

Local Lemma wrapped_widen_size_progress w a b :
  wrapped_leb w b a = false ->
  0 < wrapped_size w (wrapped_widen w a b) <= modulus w /\
  Z.min (modulus w) (3 * wrapped_size w a) <= wrapped_size w (wrapped_widen w a b).
Proof.
  intro Hescape. unfold wrapped_widen. rewrite Hescape.
  pose proof (wrapped_join_cover w (wrapped_double w a) b) as Hcover.
  apply Bool.andb_true_iff in Hcover as [Hleft Hright].
  pose proof (wrapped_size_monotone w _ _ Hleft) as Hsize.
  rewrite wrapped_double_size in Hsize.
  pose proof (wrapped_size_bounds w (wrapped_join w (wrapped_double w a) b)) as Hbounds.
  split; [split; [|lia]|exact Hsize].
  destruct (Z.eq_dec (wrapped_size w (wrapped_join w (wrapped_double w a) b)) 0)
    as [Hzero|Hnonzero]; [|lia].
  apply wrapped_size_zero in Hzero. rewrite Hzero in Hright.
  destruct b; cbn [wrapped_leb] in Hright; try discriminate.
Qed.

(** A rank bounded by width plus two decreases on every escaping widening step. *)
Theorem wrapped_widening_rank_on w :
  widening_rank_on (wrapped_lattice w) (fun _ => True).
Proof.
  refine {| wrank := fun a => Z.to_nat (wrapped_size_rank w (wrapped_size w a));
            wbound := Z.to_nat (Zpos w + 2) |}.
  - intros a _. pose proof (wrapped_size_rank_bounds w (wrapped_size w a)
      (wrapped_size_bounds w a)). apply Z2Nat.inj_le; lia.
  - intros a b _ _ Hba.
    change (wrapped_leb w b a = true) in Hba.
    change (Z.to_nat (wrapped_size_rank w (wrapped_size w (wrapped_widen w a b))) <=
      Z.to_nat (wrapped_size_rank w (wrapped_size w a)))%nat.
    unfold wrapped_widen. rewrite Hba, wrapped_norm_size. lia.
  - intros a b _ _ Hba.
    change (wrapped_leb w b a = false) in Hba.
    change (Z.to_nat (wrapped_size_rank w (wrapped_size w (wrapped_widen w a b))) <
      Z.to_nat (wrapped_size_rank w (wrapped_size w a)))%nat.
    pose proof (wrapped_size_bounds w a) as Ha.
    assert (Hproper : wrapped_size w a < modulus w).
    { destruct (Z.eq_dec (wrapped_size w a) (modulus w)) as [Hfull|Hproper]; [|lia].
      pose proof (wrapped_full_contains w a b Hfull). congruence. }
    destruct (wrapped_widen_size_progress w a b Hba) as [Hnext Hgrow].
    pose proof (wrapped_size_rank_progress w (wrapped_size w a)
      (wrapped_size w (wrapped_widen w a b)) ltac:(lia) Hnext Hgrow) as Hrank.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w a) Ha) as Hrank_old.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w (wrapped_widen w a b))
      ltac:(lia)) as Hrank_next.
    apply Z2Nat.inj_lt; lia.
Defined.
