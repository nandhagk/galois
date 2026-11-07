(** * Signed interval arithmetic

    Sign-half observations reduce signed operations to unsigned magnitude operations.
    For example, signed division of a negative arc uses the negated unsigned magnitude.
    Builds on: DomainsIntervalArith, DomainsIntervalCompare and public Bits value equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalArith DomainsIntervalCompare DomainsIntervalBitwise DomainsIntervalRefine
  DomainsIntervalShift.

Local Open Scope Z_scope.

Definition interval_sign (w : width) (a : interval) : option bool :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some false
    else if Z.leb (half w) lo then Some true else None
  | None => None
  end.

(** A successful sign observation agrees with every represented concrete sign bit. *)
Theorem interval_sign_sound w a x sign :
  interval_pgamma w a x -> interval_sign w a = Some sign -> msb w x = sign.
Proof.
  intros Ha Hsign. unfold interval_sign in Hsign.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|discriminate].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  rewrite msb_half, (wrap_id w x (proj1 Ha)).
  destruct (Z.ltb hi (half w)) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. inversion Hsign; subst sign.
    assert (Htest : Z.ltb x (half w) = true) by (apply Z.ltb_lt; lia).
    now rewrite Htest.
  - destruct (Z.leb (half w) lo) eqn:Hhigh; [|discriminate].
    apply Z.leb_le in Hhigh. inversion Hsign; subst sign.
    assert (Htest : Z.ltb x (half w) = false) by (apply Z.ltb_ge; lia).
    now rewrite Htest.
Qed.

Definition interval_signed (w : width) (a : interval) : option (Z * Z) :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some (lo, hi)
    else if Z.leb (half w) lo then Some (lo - modulus w, hi - modulus w)
    else None
  | None => None
  end.

(** Signed endpoint conversion bounds the signed view of every represented word. *)
Theorem interval_signed_sound w a z lo hi :
  interval_pgamma w a z -> interval_signed w a = Some (lo, hi) ->
  lo <= signed w z <= hi.
Proof.
  intros Ha Hsigned. unfold interval_signed in Hsigned.
  destruct (interval_finite a) as [[l h]|] eqn:Hfinite; [|discriminate].
  pose proof (interval_finite_sound w a l h z Ha Hfinite) as Hbounds.
  rewrite signed_value, (wrap_id w z (proj1 Ha)).
  destruct (Z.ltb h (half w)) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. inversion Hsigned; subst lo hi.
    assert (Htest : Z.ltb z (half w) = true) by (apply Z.ltb_lt; lia).
    now rewrite Htest.
  - destruct (Z.leb (half w) l) eqn:Hhigh; [|discriminate].
    apply Z.leb_le in Hhigh. inversion Hsigned; subst lo hi.
    assert (Htest : Z.ltb z (half w) = false) by (apply Z.ltb_ge; lia).
    rewrite Htest. lia.
Qed.

Definition interval_sext (rw w : width) (a : interval) : interval :=
  match interval_signed w a with
  | Some (lo, hi) =>
    if Z.ltb hi 0 then interval_checked rw (modulus rw + lo) (modulus rw + hi)
    else if Z.leb 0 lo then interval_checked rw lo hi else interval_top rw
  | None => interval_top rw
  end.

(** Sign extension contains the modular signed view at every result width. *)
Theorem interval_sext_sound rw w a x :
  interval_pgamma w a x ->
  interval_pgamma rw (interval_sext rw w a) (wrap rw (signed w x)).
Proof.
  intro Ha. unfold interval_sext.
  destruct (interval_signed w a) as [[lo hi]|] eqn:Hsigned;
    [|apply interval_top_sound, wrap_is_word].
  pose proof (interval_signed_sound w a x lo hi Ha Hsigned) as Hbounds.
  destruct (Z.ltb hi 0).
  - rewrite <- (wrap_add_modulus rw (signed w x) 1).
    replace (signed w x + 1 * modulus rw) with (modulus rw + signed w x) by ring.
    apply interval_checked_wrap_sound. lia.
  - destruct (Z.leb 0 lo); [|apply interval_top_sound, wrap_is_word].
    apply interval_checked_wrap_sound. exact Hbounds.
Qed.

Definition interval_signed_compare (w : width) (strict : bool) (a b : interval) : interval :=
  match interval_signed w a, interval_signed w b with
  | Some (la, ha), Some (lb, hb) =>
    if strict then
      interval_truth (if Z.ltb ha lb then Some true
                      else if Z.leb hb la then Some false else None)
    else
      interval_truth (if Z.leb ha lb then Some true
                      else if Z.ltb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

(** Signed comparisons contain every Boolean result of represented operands. *)
Theorem interval_signed_compare_sound w a b x y rw strict :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma rw (interval_signed_compare w strict a b)
    (if (if strict then Z.ltb (signed w x) (signed w y)
         else Z.leb (signed w x) (signed w y)) then 1 else 0).
Proof.
  intros Ha Hb. unfold interval_signed_compare.
  destruct (interval_signed w a) as [[la ha]|] eqn:Hfa;
    destruct (interval_signed w b) as [[lb hb]|] eqn:Hfb;
    try (destruct strict; apply interval_truth_sound; discriminate).
  pose proof (interval_signed_sound w a x la ha Ha Hfa) as Hax.
  pose proof (interval_signed_sound w b y lb hb Hb Hfb) as Hby.
  destruct strict.
  - destruct (Z.ltb ha lb) eqn:Htrue.
    + apply Z.ltb_lt in Htrue. apply interval_truth_sound; [|discriminate].
      intros _. apply Z.ltb_lt. lia.
    + destruct (Z.leb hb la) eqn:Hfalse.
      * apply Z.leb_le in Hfalse. apply interval_truth_sound; [discriminate|].
        intros _. apply Z.ltb_ge. lia.
      * apply interval_truth_sound; discriminate.
  - destruct (Z.leb ha lb) eqn:Htrue.
    + apply Z.leb_le in Htrue. apply interval_truth_sound; [|discriminate].
      intros _. apply Z.leb_le. lia.
    + destruct (Z.ltb hb la) eqn:Hfalse.
      * apply Z.ltb_lt in Hfalse. apply interval_truth_sound; [discriminate|].
        intros _. apply Z.leb_gt. lia.
      * apply interval_truth_sound; discriminate.
Qed.

Local Lemma interval_same_sign_order w x y :
  is_word w x -> is_word w y -> msb w x = msb w y ->
  (signed w x < signed w y <-> x < y) /\
  (signed w x <= signed w y <-> x <= y).
Proof.
  intros Hx Hy Hsame. rewrite !msb_half, (wrap_id w x Hx), (wrap_id w y Hy) in Hsame.
  rewrite !signed_value, (wrap_id w x Hx), (wrap_id w y Hy).
  destruct (Z.ltb x (half w)), (Z.ltb y (half w)); cbn in *; try discriminate; lia.
Qed.

Definition interval_assume_signed (w : width) (strict result : bool)
    (a b : interval) : interval * interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    if Bool.eqb sa sb then
      match strict, result with
      | true, true => interval_assume_ult a b
      | true, false => interval_swap (interval_assume_ule b a)
      | false, true => interval_assume_ule a b
      | false, false => interval_swap (interval_assume_ult b a)
      end
    else (a, b)
  | _, _ => (a, b)
  end.

(** Common-sign refinement retains every pair satisfying the signed Boolean result. *)
Theorem interval_assume_signed_sound w (strict result : bool) a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  (if strict then Z.ltb (signed w x) (signed w y)
   else Z.leb (signed w x) (signed w y)) = result ->
  interval_pgamma w (fst (interval_assume_signed w strict result a b)) x /\
  interval_pgamma w (snd (interval_assume_signed w strict result a b)) y.
Proof.
  intros Ha Hb Hcmp. unfold interval_assume_signed.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb; try (split; assumption).
  destruct (Bool.eqb sa sb) eqn:Hsame; [|split; assumption].
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  assert (Hbits : msb w x = msb w y) by
    (rewrite Hx, Hy; destruct sa, sb; cbn in Hsame; congruence).
  pose proof (interval_same_sign_order w x y (proj1 Ha) (proj1 Hb) Hbits)
    as [Hlt Hle]. destruct strict, result; cbn in Hcmp.
  - apply Z.ltb_lt in Hcmp. apply Hlt in Hcmp. now apply interval_assume_ult_sound.
  - apply Z.ltb_ge in Hcmp. assert (Horder : y <= x) by lia.
    destruct (interval_assume_ule_sound w w b a y x Hb Ha Horder); split; assumption.
  - apply Z.leb_le in Hcmp. apply Hle in Hcmp. now apply interval_assume_ule_sound.
  - apply Z.leb_gt in Hcmp. assert (Horder : y < x) by lia.
    destruct (interval_assume_ult_sound w w b a y x Hb Ha Horder); split; assumption.
Qed.

(** Common-sign refinement lies below each operand independently of its concrete meaning. *)
Theorem interval_assume_signed_lower ts w strict result a b :
  leb (interval_lattice ts) (fst (interval_assume_signed w strict result a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_signed w strict result a b)) b = true.
Proof.
  unfold interval_assume_signed.
  destruct (interval_sign w a) as [sa|]; destruct (interval_sign w b) as [sb|];
    try (split; apply (leb_refl (interval_laws ts))).
  destruct (Bool.eqb sa sb); [|split; apply (leb_refl (interval_laws ts))].
  destruct strict, result.
  - apply interval_assume_ult_lower.
  - destruct (interval_assume_ule_lower ts b a). split; assumption.
  - apply interval_assume_ule_lower.
  - destruct (interval_assume_ult_lower ts b a). split; assumption.
Qed.

Definition interval_sdiv (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let q := interval_udiv w aa bb in
    if xorb sa sb then interval_neg w q else q
  | _, _ => interval_top w
  end.

(** Signed division contains the sign-adjusted quotient, including the zero-divisor branches. *)
Theorem interval_sdiv_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_sdiv w a b) (wsdiv w x y).
Proof.
  intros Ha Hb. unfold interval_sdiv.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (apply interval_top_sound, wsdiv_is_word).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  rewrite wsdiv_value, Hx, Hy.
  destruct sa, sb; cbn [xorb]; repeat rewrite wneg_value;
    try (apply interval_neg_sound; apply interval_udiv_sound;
      try apply interval_neg_sound; assumption);
    apply interval_udiv_sound; try apply interval_neg_sound; assumption.
Qed.

Definition interval_srem (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let r := interval_urem w aa bb in
    if sa then interval_neg w r else r
  | _, _ => interval_top w
  end.

(** Signed remainder contains the unsigned magnitude remainder adjusted to the dividend sign. *)
Theorem interval_srem_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_srem w a b) (wsrem w x y).
Proof.
  intros Ha Hb. unfold interval_srem.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (apply interval_top_sound, wsrem_is_word).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  rewrite wsrem_value, Hx, Hy.
  destruct sa, sb; cbn [xorb]; repeat rewrite wneg_value;
    try (apply interval_neg_sound; apply interval_urem_sound;
      try apply interval_neg_sound; assumption);
    apply interval_urem_sound; try apply interval_neg_sound; assumption.
Qed.

Definition interval_mod_choice (u candidate : interval) : interval :=
  match interval_finite u with
  | Some (lo, hi) =>
    if Z.ltb 0 lo then candidate
    else if Z.eqb hi 0 then Itv (Fin 0) (Fin 0)
    else interval_join (Itv (Fin 0) (Fin 0)) candidate
  | None => interval_join (Itv (Fin 0) (Fin 0)) candidate
  end.

Local Lemma interval_mod_choice_sound w u candidate r z :
  interval_pgamma w u r -> interval_pgamma w candidate z ->
  interval_pgamma w (interval_mod_choice u candidate) (if Z.eqb r 0 then r else z).
Proof.
  intros Hu Hz. unfold interval_mod_choice.
  assert (Hjoin : interval_pgamma w
    (interval_join (Itv (Fin 0) (Fin 0)) candidate) (if Z.eqb r 0 then r else z)).
  { apply (interval_join_sound ThresholdEmpty).
    destruct (Z.eqb r 0) eqn:Hzeroeq; [left|now right].
    apply Z.eqb_eq in Hzeroeq. subst r.
    split; [apply zero_is_word|]. cbn. split; reflexivity. }
  destruct (interval_finite u) as [[lo hi]|] eqn:Hfinite; [|exact Hjoin].
  pose proof (interval_finite_sound w u lo hi r Hu Hfinite) as Hbounds.
  destruct (Z.ltb 0 lo) eqn:Hpositive.
  - apply Z.ltb_lt in Hpositive.
    assert (Hnonzero : Z.eqb r 0 = false) by (apply Z.eqb_neq; lia).
    now rewrite Hnonzero.
  - destruct (Z.eqb hi 0) eqn:Hzero; [|exact Hjoin].
    apply Z.eqb_eq in Hzero. assert (r = 0) by (pose proof (proj1 (proj1 Hu)); lia).
    subst r. cbn. split; [apply zero_is_word|]. cbn. split; reflexivity.
Qed.

Definition interval_smod_base (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let u := interval_urem w aa bb in
    let candidate :=
      match sa, sb with
      | false, false => u
      | true, false => interval_add_modular w (interval_neg w u) b
      | false, true => interval_add_modular w u b
      | true, true => interval_neg w u
      end in
    interval_mod_choice u candidate
  | _, _ => interval_top w
  end.

(** Signed modulus retains the magnitude remainder and its divisor-sign adjustment. *)
Theorem interval_smod_base_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_smod_base w a b) (wsmod w x y).
Proof.
  intros Ha Hb. unfold interval_smod_base.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (apply interval_top_sound, wsmod_is_word).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  rewrite wsmod_value, Hx, Hy.
  destruct sa, sb; cbn [xorb];
    rewrite ?(wrap_id w x (proj1 Ha)), ?(wrap_id w y (proj1 Hb));
    repeat rewrite wadd_value; repeat rewrite wneg_value.
  - apply interval_mod_choice_sound.
    + apply interval_urem_sound; apply interval_neg_sound; assumption.
    + apply interval_neg_sound. apply interval_urem_sound; apply interval_neg_sound; assumption.
  - apply interval_mod_choice_sound.
    + apply interval_urem_sound; [apply interval_neg_sound|]; assumption.
    + apply interval_add_modular_sound; [apply interval_neg_sound; apply interval_urem_sound;
        [apply interval_neg_sound|]|]; assumption.
  - apply interval_mod_choice_sound.
    + apply interval_urem_sound; [|apply interval_neg_sound]; assumption.
    + apply interval_add_modular_sound; [apply interval_urem_sound; [|apply interval_neg_sound]|];
        assumption.
  - apply interval_mod_choice_sound; apply interval_urem_sound; assumption.
Qed.

Definition interval_smod (w : width) (a b : interval) : interval :=
  match interval_sign w b, interval_finite b with
  | Some false, Some (lo, hi) =>
    if Z.ltb 0 lo then
      interval_meet (interval_smod_base w a b) (Itv (Fin 0) (Fin (hi - 1)))
    else interval_smod_base w a b
  | _, _ => interval_smod_base w a b
  end.

(** A positive divisor additionally bounds signed modulus between zero and its upper endpoint. *)
Theorem interval_smod_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_smod w a b) (wsmod w x y).
Proof.
  intros Ha Hb. unfold interval_smod.
  destruct (interval_sign w b) as [sign|] eqn:Hsign;
    [destruct sign|]; try now apply interval_smod_base_sound.
  destruct (interval_finite b) as [[lo hi]|] eqn:Hfinite;
    [|now apply interval_smod_base_sound].
  destruct (Z.ltb 0 lo) eqn:Hpositive; [|now apply interval_smod_base_sound].
  apply Z.ltb_lt in Hpositive.
  pose proof (interval_finite_sound w b lo hi y Hb Hfinite) as Hy.
  pose proof (interval_sign_sound w b y false Hb Hsign) as Hmsb.
  assert (Hsignedy : signed w y = y).
  { rewrite (signed_nonnegative w y Hmsb). apply wrap_id. exact (proj1 Hb). }
  pose proof (proj1 (wsmod_sign w x y) ltac:(rewrite Hsignedy; lia)) as Hmod.
  assert (Hword : is_word w (wsmod w x y)) by apply wsmod_is_word.
  assert (Hsigned : signed w (wsmod w x y) = wsmod w x y).
  { rewrite signed_value, (wrap_id w _ Hword).
    destruct (Z.ltb (wsmod w x y) (half w)) eqn:Hhalf; [reflexivity|].
    rewrite signed_value, (wrap_id w _ Hword), Hhalf in Hmod.
    destruct Hword. lia. }
  apply interval_meet_sound; [now apply interval_smod_base_sound|].
  split; [exact Hword|]. cbn.
  rewrite Hsignedy, Hsigned in Hmod. split; apply Z.leb_le; lia.
Qed.

Local Lemma interval_div_complement x d :
  0 <= x -> 0 < d -> (-1 - x) / d = -1 - x / d.
Proof.
  intros Hx Hd. apply Z.diveq. right. left.
  pose proof (Z.div_mod x d ltac:(lia)) as Hdivision.
  pose proof (Z.mod_pos_bound x d Hd) as Hremainder. nia.
Qed.

Local Lemma interval_ashr_negative w x y :
  is_word w x -> is_word w y -> msb w x = true ->
  washr w x y = wnot w (wlshr w (wnot w x) y).
Proof.
  intros Hx Hy Hnegative.
  rewrite (interval_complement_word w (wlshr w (wnot w x) y)
    (wlshr_is_word w (wnot w x) y)).
  rewrite (interval_complement_word w x Hx), washr_value, wlshr_value.
  rewrite (wrap_id w y Hy).
  rewrite (wrap_id w (modulus w - 1 - x)) by
    (pose proof (modulus_pos w); destruct Hx; split; lia).
  destruct (Z.leb (Zpos w) y) eqn:Hlarge.
  - rewrite Hnegative. lia.
  - rewrite msb_half, (wrap_id w x Hx) in Hnegative.
    apply Bool.negb_true_iff in Hnegative. apply Z.ltb_ge in Hnegative.
    rewrite signed_value, (wrap_id w x Hx).
    assert (Hhalf : Z.ltb x (half w) = false) by (apply Z.ltb_ge; exact Hnegative).
    rewrite Hhalf. set (d := 2 ^ y).
    assert (Hd : 0 < d) by (unfold d; apply Z.pow_pos_nonneg; destruct Hy; lia).
    assert (Ht : 0 <= modulus w - 1 - x) by (destruct Hx; lia).
    replace (x - modulus w) with (-1 - (modulus w - 1 - x)) by ring.
    rewrite interval_div_complement by assumption.
    pose proof (Z.div_pos (modulus w - 1 - x) d Ht Hd) as Hqlo.
    pose proof (Z.div_le_upper_bound (modulus w - 1 - x) d (modulus w - 1)
      ltac:(lia) ltac:(pose proof (modulus_pos w); pose proof (proj1 Hx); nia)) as Hqhi.
    assert (Hout : is_word w (modulus w - 1 - (modulus w - 1 - x) / d))
      by (split; pose proof (modulus_pos w); lia).
    rewrite <- (wrap_add_modulus w (-1 - (modulus w - 1 - x) / d) 1).
    replace (-1 - (modulus w - 1 - x) / d + 1 * modulus w) with
      (modulus w - 1 - (modulus w - 1 - x) / d) by ring.
    now rewrite (wrap_id w _ Hout).
Qed.

Local Lemma interval_ashr_nonnegative w x y :
  is_word w x -> is_word w y -> msb w x = false -> washr w x y = wlshr w x y.
Proof.
  intros Hx Hy Hsign. rewrite washr_value, wlshr_value.
  rewrite (wrap_id w x Hx), (wrap_id w y Hy).
  destruct (Z.leb (Zpos w) y) eqn:Hlarge; [now rewrite Hsign|].
  rewrite (signed_nonnegative w x Hsign), (wrap_id w x Hx). apply wrap_id.
  pose proof (wlshr_is_word w x y) as Hresult.
  rewrite wlshr_value, (wrap_id w x Hx), (wrap_id w y Hy), Hlarge in Hresult.
  exact Hresult.
Qed.

Definition interval_ashr_small (w : width) (a b : interval) : interval :=
  match interval_sign w a with
  | Some false => interval_lshr w a b
  | Some true => interval_not w (interval_lshr w (interval_not w a) b)
  | None => interval_top w
  end.

Local Lemma interval_ashr_small_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_ashr_small w a b) (washr w x y).
Proof.
  intros Ha Hb. unfold interval_ashr_small.
  destruct (interval_sign w a) as [sign|] eqn:Hsign;
    [|apply interval_top_sound, washr_is_word].
  pose proof (interval_sign_sound w a x sign Ha Hsign) as Hmsb.
  destruct sign.
  - rewrite (interval_ashr_negative w x y (proj1 Ha) (proj1 Hb) Hmsb).
    apply interval_not_sound. apply interval_lshr_sound; [apply interval_not_sound|]; assumption.
  - rewrite (interval_ashr_nonnegative w x y (proj1 Ha) (proj1 Hb) Hmsb).
    now apply interval_lshr_sound.
Qed.

Definition interval_ashr (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_finite b with
  | Some sign, Some (lo, hi) =>
    let saturated := if sign then modulus w - 1 else 0 in
    if Z.ltb hi (Zpos w) then interval_ashr_small w a b
    else if Z.leb (Zpos w) lo then Itv (Fin saturated) (Fin saturated)
    else interval_join
      (interval_ashr_small w a (Itv (Fin lo) (Fin (Zpos w - 1))))
      (Itv (Fin saturated) (Fin saturated))
  | _, _ => interval_ashr_small w a b
  end.

(** Arithmetic right shift also includes sign saturation when shift amounts reach the width. *)
Theorem interval_ashr_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_ashr w a b) (washr w x y).
Proof.
  intros Ha Hb. unfold interval_ashr.
  destruct (interval_sign w a) as [sign|] eqn:Hsign;
    [|now apply interval_ashr_small_sound].
  destruct (interval_finite b) as [[lo hi]|] eqn:Hfinite;
    [|now apply interval_ashr_small_sound].
  pose proof (interval_finite_sound w b lo hi y Hb Hfinite) as Hbounds.
  pose proof (interval_sign_sound w a x sign Ha Hsign) as Hmsb.
  destruct (Z.ltb hi (Zpos w)) eqn:Hhi; [now apply interval_ashr_small_sound|].
  assert (Hsaturated : Zpos w <= y ->
    interval_pgamma w (Itv (Fin (if sign then modulus w - 1 else 0))
      (Fin (if sign then modulus w - 1 else 0))) (washr w x y)).
  { intro Hlarge. rewrite washr_value, (wrap_id w y (proj1 Hb)).
    rewrite (proj2 (Z.leb_le _ _) Hlarge), Hmsb. destruct sign.
    - split; [apply ones_is_word|]. cbn. split; apply Z.leb_refl.
    - split; [apply zero_is_word|]. cbn. split; reflexivity. }
  destruct (Z.leb (Zpos w) lo) eqn:Hlo.
  - apply Hsaturated. apply Z.leb_le in Hlo. lia.
  - apply (interval_join_sound ThresholdEmpty). destruct (Z.leb (Zpos w) y) eqn:Hy.
    + right. apply Hsaturated. now apply Z.leb_le.
    + left. apply interval_ashr_small_sound; [exact Ha|].
      split; [exact (proj1 Hb)|].
      change (Z.leb lo y = true /\ Z.leb y (Zpos w - 1) = true).
      apply Z.leb_gt in Hy. split; apply Z.leb_le; lia.
Qed.
