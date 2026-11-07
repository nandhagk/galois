(** * Unsigned interval arithmetic

    Endpoint operations retain a finite result when the whole range fits the result width.
    For example, adding [1,4] to [2,5] gives [3,9] at width eight.
    Builds on: DomainsInterval and the public Bits word laws. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsOp.
From Galois.Domains Require Import DomainsBound DomainsInterval.

Local Open Scope Z_scope.

Definition interval_checked (w : width) (lo hi : Z) : interval :=
  if (Z.leb 0 lo && Z.ltb hi (modulus w))%bool
  then Itv (Fin lo) (Fin hi) else interval_top w.

(** A checked range contains every normalized word between its endpoints. *)
Theorem interval_checked_sound w lo hi z :
  is_word w z -> lo <= z <= hi -> interval_pgamma w (interval_checked w lo hi) z.
Proof.
  intros Hword Hz. unfold interval_checked.
  destruct (Z.leb 0 lo && Z.ltb hi (modulus w))%bool; [|now apply interval_top_sound].
  split; [exact Hword|]. cbn. split; apply Z.leb_le; lia.
Qed.

(** A checked range also contains the wrapped value of every integer between its endpoints. *)
Theorem interval_checked_wrap_sound w lo hi z :
  lo <= z <= hi -> interval_pgamma w (interval_checked w lo hi) (wrap w z).
Proof.
  intro Hbounds. unfold interval_checked.
  destruct (Z.leb 0 lo && Z.ltb hi (modulus w))%bool eqn:Hfit;
    [|apply interval_top_sound, wrap_is_word].
  apply andb_true_iff in Hfit as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word w z) by (split; lia).
  rewrite (wrap_id w z Hword). split; [exact Hword|].
  cbn. split; apply Z.leb_le; lia.
Qed.

Definition interval_add (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) => interval_checked w (la + lb) (ha + hb)
  | _, _ => interval_top w
  end.

(** Addition contains every modular sum of represented operands, at any operand widths. *)
Theorem interval_add_sound w wa wb a b x y :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_add w a b) (wrap w (x + y)).
Proof.
  intros Ha Hb. unfold interval_add.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa).
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
  apply interval_checked_wrap_sound. lia.
Qed.

(** Internal signed arithmetic can retain a range whose sums all wrap once. *)
Definition interval_add_modular (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb (modulus w) (la + lb) && Z.ltb (ha + hb) (2 * modulus w))%bool
    then interval_checked w (la + lb - modulus w) (ha + hb - modulus w)
    else interval_add w a b
  | _, _ => interval_top w
  end.

(** Uniform single-wrap addition retains every modular sum. *)
Theorem interval_add_modular_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_add_modular w a b) (wrap w (x + y)).
Proof.
  intros Ha Hb. unfold interval_add_modular.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wrap_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa).
  pose proof (interval_finite_sound w b lb hb y Hb Hfb).
  destruct (Z.leb (modulus w) (la + lb) && Z.ltb (ha + hb) (2 * modulus w))%bool;
    [|now apply (interval_add_sound w w w)].
  replace (x + y) with ((x + y - modulus w) + 1 * modulus w) by ring.
  rewrite wrap_add_modulus. apply interval_checked_wrap_sound. lia.
Qed.

Definition interval_sub (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) => interval_checked w (la - hb) (ha - lb)
  | _, _ => interval_top w
  end.

(** Subtraction contains every modular difference of represented operands. *)
Theorem interval_sub_sound w wa wb a b x y :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_sub w a b) (wrap w (x - y)).
Proof.
  intros Ha Hb. unfold interval_sub.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa).
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
  apply interval_checked_wrap_sound. lia.
Qed.

Definition interval_mul (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb)%bool
    then interval_checked w (la * lb) (ha * hb) else interval_top w
  | _, _ => interval_top w
  end.

(** Nonnegative endpoint multiplication contains every modular product. *)
Theorem interval_mul_sound w wa wb a b x y :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_mul w a b) (wrap w (x * y)).
Proof.
  intros Ha Hb. unfold interval_mul.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa).
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
  destruct (Z.leb 0 la && Z.leb 0 lb)%bool eqn:Hnonneg;
    [|apply interval_top_sound, wrap_is_word].
  apply andb_true_iff in Hnonneg as [Hla Hlb].
  apply Z.leb_le in Hla. apply Z.leb_le in Hlb.
  apply interval_checked_wrap_sound. nia.
Qed.

Definition interval_neg (w : width) (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.eqb hi 0 then Itv (Fin 0) (Fin 0)
    else if Z.ltb 0 lo then interval_checked w (modulus w - hi) (modulus w - lo)
    else interval_top w
  | None => interval_top w
  end.

(** Negation retains zero and the reversed strictly positive range. *)
Theorem interval_neg_sound w a x :
  interval_pgamma w a x -> interval_pgamma w (interval_neg w a) (wrap w (- x)).
Proof.
  intro Ha. unfold interval_neg.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_top_sound, wrap_is_word].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
  destruct Ha as [Hword _].
  destruct (Z.eqb hi 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. assert (x = 0) by (destruct Hword; lia).
    subst x. rewrite Z.opp_0, wrap_0. split; [apply zero_is_word|].
    cbn. split; reflexivity.
  - destruct (Z.ltb 0 lo); [|apply interval_top_sound, wrap_is_word].
    rewrite <- (wrap_add_modulus w (- x) 1).
    replace (- x + 1 * modulus w) with (modulus w - x) by ring.
    apply interval_checked_wrap_sound. lia.
Qed.

Definition interval_concat (rw lower_width : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_checked rw (la * modulus lower_width + lb) (ha * modulus lower_width + hb)
  | _, _ => interval_top rw
  end.

(** Concatenation contains every pair of represented operands in the lower operand radix. *)
Theorem interval_concat_sound rw wa wb a b x y :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma rw (interval_concat rw wb a b) (wrap rw (x * modulus wb + y)).
Proof.
  intros Ha Hb. unfold interval_concat.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa).
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
  pose proof (modulus_pos wb).
  apply interval_checked_wrap_sound. nia.
Qed.

Definition interval_rewrap (rw : width) (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) => interval_checked rw lo hi
  | None => interval_top rw
  end.

(** Rewrapping contains every represented input after reduction to the result width. *)
Theorem interval_rewrap_sound rw w a x :
  interval_pgamma w a x -> interval_pgamma rw (interval_rewrap rw a) (wrap rw x).
Proof.
  intro Ha. unfold interval_rewrap.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_top_sound, wrap_is_word].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
  apply interval_checked_wrap_sound. assumption.
Qed.

Definition interval_counts (w : width) : interval := Itv (Fin 0) (Fin (Zpos w)).

(** Leading-zero counts lie in the closed range from zero to the width. *)
Theorem interval_clz_sound w x : interval_pgamma w (interval_counts w) (wclz w x).
Proof.
  pose proof (wclz_range w x) as Hrange.
  split; [apply wclz_is_word|]. cbn. split; apply Z.leb_le; lia.
Qed.

(** Population counts lie in the closed range from zero to the width. *)
Theorem interval_popcnt_sound w x : interval_pgamma w (interval_counts w) (wpopcnt w x).
Proof.
  pose proof (wpopcnt_range w x) as Hrange.
  split; [apply wpopcnt_is_word|]. cbn. split; apply Z.leb_le; lia.
Qed.

(** Trailing-zero counts lie in the closed range from zero to the width. *)
Theorem interval_ctz_sound w x : interval_pgamma w (interval_counts w) (wctz w x).
Proof.
  pose proof (wctz_is_word w x) as Hword.
  assert (Hupper : wctz w x <= Zpos w).
  { pose proof (word_fun1_normalised bvctz wctz w x eq_refl) as Hnorm.
    destruct (Z.eq_dec (wrap w x) 0) as [Hzero|Hnonzero].
    - rewrite <- Hnorm, Hzero, wctz_zero. lia.
    - pose proof (proj1 (wctz_spec w (wrap w x) (wrap_is_word w x) Hnonzero)) as Hbit.
      rewrite Hnorm in Hbit.
      destruct (Z_le_gt_dec (Zpos w) (wctz w x)) as [Hhigh|Hlow]; [|lia].
      rewrite (word_bits_high w (wrap w x) (wctz w x) (wrap_is_word w x) Hhigh) in Hbit.
      discriminate. }
  split; [exact Hword|]. cbn. split; apply Z.leb_le; destruct Hword; lia.
Qed.

Definition interval_udiv (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.ltb 0 lb)%bool
    then interval_checked w (la / hb) (ha / lb)
    else if (Z.leb 0 la && Z.eqb lb 0 && Z.ltb 0 hb)%bool
         then interval_checked w (la / hb) (modulus w - 1)
         else if (Z.eqb lb 0 && Z.eqb hb 0)%bool
              then Itv (Fin (modulus w - 1)) (Fin (modulus w - 1))
              else interval_top w
  | _, _ => interval_top w
  end.

(** Unsigned division includes the all-ones result for a zero divisor. *)
Theorem interval_udiv_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_udiv w a b) (wudiv w x y).
Proof.
  intros Ha Hb. unfold interval_udiv.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wudiv_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  destruct (Z.leb 0 la && Z.ltb 0 lb)%bool eqn:Hvalid.
  - apply andb_true_iff in Hvalid as [Hla Hlb]. apply Z.leb_le in Hla.
    apply Z.ltb_lt in Hlb. apply interval_checked_sound; [apply wudiv_is_word|].
    rewrite (wudiv_spec w x y Hwordx Hwordy ltac:(lia)).
    split.
    + eapply (Z.le_trans _ (x / hb));
        [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
    + eapply (Z.le_trans _ (x / lb));
        [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
  - destruct (Z.leb 0 la && Z.eqb lb 0 && Z.ltb 0 hb)%bool eqn:Hcontains.
    + repeat rewrite andb_true_iff in Hcontains. destruct Hcontains as [[Hla Hlb] Hhb].
      apply Z.leb_le in Hla. apply Z.eqb_eq in Hlb. apply Z.ltb_lt in Hhb.
      apply interval_checked_sound; [apply wudiv_is_word|].
      destruct (Z.eqb y 0) eqn:Hzero.
      * apply Z.eqb_eq in Hzero. subst y. rewrite wudiv_zero.
        pose proof (Z.div_le_upper_bound la hb (modulus w - 1) Hhb
          ltac:(pose proof (modulus_pos w); destruct Hwordx; nia)). lia.
      * apply Z.eqb_neq in Hzero. rewrite (wudiv_spec w x y Hwordx Hwordy Hzero).
        assert (Hlower : la / hb <= x / y).
        { eapply (Z.le_trans _ (x / hb));
            [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; destruct Hwordy; lia]. }
        pose proof (wudiv_is_word w x y) as Hword.
        rewrite (wudiv_spec w x y Hwordx Hwordy Hzero) in Hword. destruct Hword. lia.
    + destruct (Z.eqb lb 0 && Z.eqb hb 0)%bool eqn:Hzero;
        [|apply interval_top_sound, wudiv_is_word].
      apply andb_true_iff in Hzero as [Hlb Hhb]. apply Z.eqb_eq in Hlb. apply Z.eqb_eq in Hhb.
      assert (y = 0) by lia. subst y. rewrite wudiv_zero.
      split; [apply ones_is_word|]. cbn. now rewrite Z.leb_refl.
Qed.

Definition interval_urem (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.ltb 0 lb && Z.eqb (la / hb) (ha / lb))%bool then
      let quotient := la / hb in
      interval_checked w (la - quotient * hb) (ha - quotient * lb)
    else interval_checked w 0 (if Z.ltb 0 lb then Z.min ha (hb - 1) else ha)
  | _, _ => interval_top w
  end.

(** Remainders retain the exact common-quotient range when both endpoints have one quotient. *)
Theorem interval_urem_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_urem w a b) (wurem w x y).
Proof.
  intros Ha Hb. unfold interval_urem.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wurem_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  destruct (Z.leb 0 la && Z.ltb 0 lb && Z.eqb (la / hb) (ha / lb))%bool eqn:Hexact.
  - repeat rewrite andb_true_iff in Hexact. destruct Hexact as [[Hla Hlb] Hquot].
    apply Z.leb_le in Hla. apply Z.ltb_lt in Hlb. apply Z.eqb_eq in Hquot.
    assert (Hlower : la / hb <= x / y).
    { eapply (Z.le_trans _ (x / hb));
        [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia]. }
    assert (Hupper : x / y <= ha / lb).
    { eapply (Z.le_trans _ (x / lb));
        [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia]. }
    assert (Hq : x / y = la / hb) by lia.
    assert (Hqnonnegative : 0 <= la / hb) by (apply Z.div_pos; lia).
    apply interval_checked_sound; [apply wurem_is_word|].
    rewrite (wurem_spec w x y Hwordx Hwordy ltac:(lia)).
    pose proof (Z.div_mod x y ltac:(lia)) as Hdivision. rewrite Hq in Hdivision. nia.
  - apply interval_checked_sound; [apply wurem_is_word|].
    destruct (Z.ltb 0 lb) eqn:Hpositive.
    + apply Z.ltb_lt in Hpositive.
      rewrite (wurem_spec w x y Hwordx Hwordy ltac:(lia)).
      pose proof (Z.mod_pos_bound x y ltac:(lia)).
      pose proof (Z.mod_le x y (proj1 Hwordx) ltac:(lia)).
      split; [lia|apply Z.min_glb; lia].
    + destruct (Z.eq_dec y 0) as [->|Hnonzero].
      * rewrite wurem_zero, (wrap_id w x Hwordx). destruct Hwordx. lia.
      * rewrite (wurem_spec w x y Hwordx Hwordy Hnonzero).
        pose proof (Z.mod_pos_bound x y ltac:(destruct Hwordy; lia)).
        pose proof (Z.mod_le x y (proj1 Hwordx) ltac:(destruct Hwordy; lia)). lia.
Qed.
