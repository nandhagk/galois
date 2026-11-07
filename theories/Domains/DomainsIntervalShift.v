(** * Unsigned interval shifts

    Bounded shift amounts use endpoint powers of two and larger ranges return the word top.
    For example, shifting [2,4] right by [1,2] gives [0,2].
    Builds on: DomainsIntervalArith and public Bits shift equations. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit.
From Galois.Domains Require Import DomainsBound DomainsInterval DomainsIntervalArith.

Local Open Scope Z_scope.

Definition interval_shl (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la * 2 ^ lb) (ha * 2 ^ hb) else interval_top w
  | _, _ => interval_top w
  end.

(** Bounded left shifts contain every modular product by the corresponding power of two. *)
Theorem interval_shl_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_shl w a b) (wshl w x y).
Proof.
  intros Ha Hb. unfold interval_shl.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wshl_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool eqn:Hrange;
    [|apply interval_top_sound, wshl_is_word].
  repeat rewrite andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hhb].
  apply Z.leb_le in Hla. apply Z.leb_le in Hlb. apply Z.ltb_lt in Hhb.
  assert (Hpowlo : 2 ^ lb <= 2 ^ y) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowhi : 2 ^ y <= 2 ^ hb) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowpos : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
  rewrite wshl_value, (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)).
  assert (Hshift : (Zpos w <=? y) = false) by (apply Z.leb_gt; lia).
  rewrite Hshift. apply interval_checked_wrap_sound. nia.
Qed.

Definition interval_lshr (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la / 2 ^ hb) (ha / 2 ^ lb) else interval_top w
  | _, _ => interval_top w
  end.

(** Bounded logical right shifts contain every represented quotient by a power of two. *)
Theorem interval_lshr_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_lshr w a b) (wlshr w x y).
Proof.
  intros Ha Hb. unfold interval_lshr.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wlshr_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool eqn:Hrange;
    [|apply interval_top_sound, wlshr_is_word].
  repeat rewrite andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hhb].
  apply Z.leb_le in Hla. apply Z.leb_le in Hlb. apply Z.ltb_lt in Hhb.
  assert (Hpowlo : 2 ^ lb <= 2 ^ y) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowhi : 2 ^ y <= 2 ^ hb) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowpos : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
  apply interval_checked_sound; [apply wlshr_is_word|].
  rewrite wlshr_value, (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)).
  assert (Hshift : (Zpos w <=? y) = false) by (apply Z.leb_gt; lia).
  rewrite Hshift. split.
  - eapply (Z.le_trans _ (x / 2 ^ hb));
      [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
  - eapply (Z.le_trans _ (x / 2 ^ lb));
      [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
Qed.
