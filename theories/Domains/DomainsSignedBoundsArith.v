(** * Local signed-bound modular arithmetic

    Endpoint arithmetic produces constant-size modular pieces at the output width.
    For example, four-bit addition of [6,7] and [1,1] produces [7,8].
    Builds on: DomainsSignedBoundsRange and public Bits arithmetic equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsSignedBounds DomainsSignedBoundsRange.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition sb_range_add (w : width) (a b : sb_range) : list sb_range :=
  sb_mod_ranges w (fst a + fst b) (snd a + snd b).

Definition sb_range_sub (w : width) (a b : sb_range) : list sb_range :=
  sb_mod_ranges w (fst a - snd b) (snd a - fst b).

Definition sb_range_neg (w : width) (a : sb_range) : list sb_range :=
  sb_mod_ranges w (- snd a) (- fst a).

(** Addition encloses every concrete modular sum of the two endpoint ranges. *)
Theorem sb_range_add_sound : forall w a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_add w a b) (wadd w x y).
Proof.
  intros w [la ua] [lb ub] x y Ha Hb. rewrite wadd_value.
  apply sb_mod_ranges_sound. unfold sb_range_gamma in *. cbn in *. lia.
Qed.

(** Subtraction encloses every concrete modular difference of the endpoint ranges. *)
Theorem sb_range_sub_sound : forall w a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_sub w a b) (wsub w x y).
Proof.
  intros w [la ua] [lb ub] x y Ha Hb. rewrite wsub_value.
  apply sb_mod_ranges_sound. unfold sb_range_gamma in *. cbn in *. lia.
Qed.

(** Negation reverses the input endpoints before modular projection. *)
Theorem sb_range_neg_sound : forall w a x,
  sb_range_gamma a x -> sb_ranges_gamma w (sb_range_neg w a) (wneg w x).
Proof.
  intros w [la ua] x Ha. rewrite wneg_value.
  apply sb_mod_ranges_sound. unfold sb_range_gamma in *. cbn in *. lia.
Qed.

Definition sb_product_lower (a b : sb_range) : Z :=
  Z.min (Z.min (fst a * fst b) (fst a * snd b))
    (Z.min (snd a * fst b) (snd a * snd b)).

Definition sb_product_upper (a b : sb_range) : Z :=
  Z.max (Z.max (fst a * fst b) (fst a * snd b))
    (Z.max (snd a * fst b) (snd a * snd b)).

Lemma sb_product_bounds : forall a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_product_lower a b <= x * y <= sb_product_upper a b.
Proof.
  intros [a b] [c d] x y Hx Hy.
  unfold sb_product_lower, sb_product_upper, sb_range_gamma in *. cbn in *.
  set (lo := Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d))).
  set (hi := Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d))).
  assert (Hlo : lo <= a * c /\ lo <= a * d /\ lo <= b * c /\ lo <= b * d).
  { unfold lo. repeat split; repeat rewrite Z.min_le_iff; intuition lia. }
  assert (Hhi : a * c <= hi /\ a * d <= hi /\ b * c <= hi /\ b * d <= hi).
  { unfold hi. repeat split; repeat rewrite Z.max_le_iff; intuition lia. }
  destruct Hlo as [Hac [Had [Hbc Hbd]]], Hhi as [Hac' [Had' [Hbc' Hbd']]].
  destruct (Z_le_gt_dec 0 x); destruct (Z_le_gt_dec 0 c); destruct (Z_le_gt_dec 0 d); nia.
Qed.

Definition sb_signed_range (w : width) (a : sb_range) : sb_range :=
  if snd a <? half w then a else
  if half w <=? fst a then (fst a - modulus w, snd a - modulus w)
  else (- half w, half w - 1).

(** Endpoint sign classification gives a sound range for the signed input interpretation. *)
Theorem sb_signed_range_sound : forall w a x,
  is_word w x -> sb_range_gamma a x ->
  sb_range_gamma (sb_signed_range w a) (signed w x).
Proof.
  intros w [lo hi] x Hword Hx.
  unfold sb_signed_range, sb_range_gamma in *. cbn [fst snd] in *.
  destruct (hi <? half w) eqn:Hpositive.
  - apply Z.ltb_lt in Hpositive.
    assert (Hsign : msb w x = false).
    { rewrite msb_half, (wrap_id w x Hword).
      rewrite (proj2 (Z.ltb_lt x (half w))) by lia. reflexivity. }
    rewrite signed_nonnegative, (wrap_id w x Hword) by exact Hsign. exact Hx.
  - destruct (half w <=? lo) eqn:Hnegative.
    + apply Z.leb_le in Hnegative.
      rewrite signed_value, (wrap_id w x Hword),
        (proj2 (Z.ltb_ge x (half w))) by lia. cbn [fst snd]. lia.
    + pose proof (signed_range w x). cbn [fst snd]. lia.
Qed.

(** Multiplication selects the smaller unsigned or signed modular endpoint cover. *)
Definition sb_range_mul (w : width) (a b : sb_range) : list sb_range :=
  let unsigned_lo := sb_product_lower a b in
  let unsigned_hi := sb_product_upper a b in
  let signed_a := sb_signed_range w a in
  let signed_b := sb_signed_range w b in
  let signed_lo := sb_product_lower signed_a signed_b in
  let signed_hi := sb_product_upper signed_a signed_b in
  if sb_mod_size w unsigned_lo unsigned_hi <=? sb_mod_size w signed_lo signed_hi
  then sb_mod_ranges w unsigned_lo unsigned_hi
  else sb_mod_ranges w signed_lo signed_hi.

(** Both multiplication covers contain the concrete product, so selecting the smaller is sound. *)
Theorem sb_range_mul_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_mul w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold sb_range_mul.
  destruct (sb_mod_size w (sb_product_lower a b) (sb_product_upper a b) <=?
    sb_mod_size w (sb_product_lower (sb_signed_range w a) (sb_signed_range w b))
      (sb_product_upper (sb_signed_range w a) (sb_signed_range w b))).
  - rewrite wmul_value. apply sb_mod_ranges_sound. now apply sb_product_bounds.
  - rewrite wmul_signed. apply sb_mod_ranges_sound, sb_product_bounds;
      now apply sb_signed_range_sound.
Qed.

Definition sb_range_udiv (w : width) (a b : sb_range) : list sb_range :=
  let '(la, ha) := a in
  let '(lb, hb) := b in
  if (0 <=? la) && (0 <? lb) then sb_checked_ranges w (la / hb) (ha / lb) else
  if (0 <=? la) && (lb =? 0) && (0 <? hb)
  then sb_checked_ranges w (la / hb) (modulus w - 1) else
  if (lb =? 0) && (hb =? 0) then [(modulus w - 1, modulus w - 1)]
  else [(0, modulus w - 1)].

(** Unsigned division handles positive, zero-containing and zero-only divisors separately. *)
Theorem sb_range_udiv_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_udiv w a b) (wudiv w x y).
Proof.
  intros w [la ha] [lb hb] x y Hx Hy Ha Hb.
  unfold sb_range_gamma in Ha, Hb. cbn [fst snd] in Ha, Hb.
  unfold sb_range_udiv.
  destruct ((0 <=? la) && (0 <? lb)) eqn:Hpositive.
  - apply andb_true_iff in Hpositive as [Hla Hlb]. apply Z.leb_le in Hla.
    apply Z.ltb_lt in Hlb. apply sb_checked_ranges_sound; [apply wudiv_is_word|].
    rewrite wudiv_spec by (try assumption; lia). split.
    + eapply (Z.le_trans _ (x / hb));
        [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
    + eapply (Z.le_trans _ (x / lb));
        [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
  - destruct ((0 <=? la) && (lb =? 0) && (0 <? hb)) eqn:Hcontains.
    + rewrite !andb_true_iff in Hcontains. destruct Hcontains as [[Hla Hlb] Hhb].
      apply Z.leb_le in Hla. apply Z.eqb_eq in Hlb. apply Z.ltb_lt in Hhb.
      apply sb_checked_ranges_sound; [apply wudiv_is_word|].
      destruct (Z.eq_dec y 0) as [->|Hynz].
      * rewrite wudiv_zero.
        pose proof (Z.div_le_upper_bound la hb (modulus w - 1) Hhb
          ltac:(unfold is_word in Hx; nia)). lia.
      * pose proof (wudiv_is_word w x y) as Hresult.
        rewrite wudiv_spec in Hresult |- * by assumption.
        assert (Hlower : la / hb <= x / y).
        { eapply (Z.le_trans _ (x / hb)); [apply Z.div_le_mono; lia|].
          apply Z.div_le_compat_l; unfold is_word in Hy; lia. }
        unfold is_word in Hresult. lia.
    + destruct ((lb =? 0) && (hb =? 0)) eqn:Hzero.
      * apply andb_true_iff in Hzero as [Hl Hu]. apply Z.eqb_eq in Hl, Hu.
        assert (Hy0 : y = 0) by lia. subst y. rewrite wudiv_zero.
        split; [apply ones_is_word|]. exists (modulus w - 1, modulus w - 1).
        split; [now left|]. unfold sb_range_gamma. cbn [fst snd]. lia.
      * split; [apply wudiv_is_word|]. exists (0, modulus w - 1). split; [now left|].
        pose proof (wudiv_is_word w x y). unfold sb_range_gamma, is_word in *.
        cbn [fst snd]. lia.
Qed.

Definition sb_range_urem (w : width) (a b : sb_range) : list sb_range :=
  let '(la, ha) := a in
  let '(lb, hb) := b in
  if (0 <=? la) && (0 <? lb) && (la / hb =? ha / lb) then
    let q := la / hb in sb_checked_ranges w (la - q * hb) (ha - q * lb)
  else sb_checked_ranges w 0 (if 0 <? lb then Z.min ha (hb - 1) else ha).

(** Remainder uses a common quotient when available and otherwise the dividend/divisor bounds. *)
Theorem sb_range_urem_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_urem w a b) (wurem w x y).
Proof.
  intros w [la ha] [lb hb] x y Hx Hy Ha Hb.
  unfold sb_range_gamma in Ha, Hb. cbn [fst snd] in Ha, Hb. unfold sb_range_urem.
  destruct ((0 <=? la) && (0 <? lb) && (la / hb =? ha / lb)) eqn:Hexact.
  - rewrite !andb_true_iff in Hexact. destruct Hexact as [[Hla Hlb] Hquot].
    apply Z.leb_le in Hla. apply Z.ltb_lt in Hlb. apply Z.eqb_eq in Hquot.
    assert (Hqy : x / y = la / hb).
    { assert (Hlower : la / hb <= x / y).
      { eapply (Z.le_trans _ (x / hb));
          [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia]. }
      assert (Hupper : x / y <= ha / lb).
      { eapply (Z.le_trans _ (x / lb));
          [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia]. }
      lia. }
    pose proof (Z.div_pos la hb ltac:(lia) ltac:(lia)) as Hqpos.
    apply sb_checked_ranges_sound; [apply wurem_is_word|].
    rewrite wurem_spec by (try assumption; lia).
    pose proof (Z.div_mod x y ltac:(lia)) as Hmod. rewrite Hqy in Hmod. nia.
  - apply sb_checked_ranges_sound; [apply wurem_is_word|].
    destruct (0 <? lb) eqn:Hlb.
    + apply Z.ltb_lt in Hlb. rewrite wurem_spec by (try assumption; lia).
      pose proof (Z.mod_pos_bound x y ltac:(lia)).
      pose proof (Z.mod_le x y (proj1 Hx) ltac:(lia)). lia.
    + destruct (Z.eq_dec y 0) as [->|Hynz].
      * rewrite wurem_zero, (wrap_id w x Hx). unfold is_word in Hx. lia.
      * rewrite wurem_spec by assumption.
        pose proof (Z.mod_pos_bound x y ltac:(unfold is_word in Hy; lia)).
        pose proof (Z.mod_le x y (proj1 Hx) ltac:(unfold is_word in Hy; lia)). lia.
Qed.

Definition sb_range_sign (w : width) (a : sb_range) : option bool :=
  if snd a <? half w then Some false else
  if half w <=? fst a then Some true else None.

Lemma sb_range_sign_sound : forall w a x s,
  is_word w x -> sb_range_gamma a x -> sb_range_sign w a = Some s -> msb w x = s.
Proof.
  intros w [lo hi] x s Hw Hx Hsign.
  unfold sb_range_sign, sb_range_gamma in *. cbn [fst snd] in *.
  rewrite msb_half, (wrap_id w x Hw).
  destruct (hi <? half w) eqn:Hpositive.
  - injection Hsign as <-. apply Z.ltb_lt in Hpositive.
    rewrite (proj2 (Z.ltb_lt x (half w))) by lia. reflexivity.
  - destruct (half w <=? lo) eqn:Hnegative; [|discriminate].
    injection Hsign as <-. apply Z.leb_le in Hnegative.
    rewrite (proj2 (Z.ltb_ge x (half w))) by lia. reflexivity.
Qed.

Definition sb_range_magnitude (w : width) (s : bool) (a : sb_range) : sb_range :=
  if s then (modulus w - snd a, modulus w - fst a) else a.

Lemma sb_negative_magnitude_value : forall w x,
  is_word w x -> msb w x = true -> wneg w x = modulus w - x.
Proof.
  intros w x Hx Hs. rewrite msb_half, (wrap_id w x Hx) in Hs.
  apply negb_true_iff, Z.ltb_ge in Hs. pose proof (half_pos w).
  rewrite wneg_value, wrap_mod. symmetry. apply Z.mod_unique with (q := -1).
  - left. unfold is_word in Hx. lia.
  - ring.
Qed.

Lemma sb_range_magnitude_sound : forall w a x s,
  is_word w x -> sb_range_gamma a x -> sb_range_sign w a = Some s ->
  sb_range_gamma (sb_range_magnitude w s a) (if s then wneg w x else x).
Proof.
  intros w [lo hi] x s Hw Hx Hsign.
  pose proof (sb_range_sign_sound w (lo, hi) x s Hw Hx Hsign) as Hs.
  destruct s; [|exact Hx]. rewrite sb_negative_magnitude_value by assumption.
  unfold sb_range_magnitude, sb_range_gamma in *. cbn [fst snd] in *. lia.
Qed.

Definition sb_negate_ranges_c (w : width) (rs : list sb_range) : Cost.t (list sb_range) :=
  fold_right_c (fun r acc => Cost.step ;; app_c (sb_range_neg w r) acc) [] rs.

Definition sb_negate_ranges (w : width) (rs : list sb_range) : list sb_range :=
  Cost.value (sb_negate_ranges_c w rs).

Lemma sb_negate_ranges_equation : forall w rs,
  sb_negate_ranges w rs = fold_right (fun r acc => sb_range_neg w r ++ acc) [] rs.
Proof.
  intros w rs. unfold sb_negate_ranges, sb_negate_ranges_c. rewrite value_fold_right_c.
  induction rs as [|r rest IH]; cbn [fold_right]; [reflexivity|].
  rewrite Cost.value_bind, value_app_c, IH. reflexivity.
Qed.

(** Negating modular pieces retains every piece and every charged list traversal. *)
Theorem sb_negate_ranges_sound : forall w rs z,
  sb_ranges_gamma w rs z -> sb_ranges_gamma w (sb_negate_ranges w rs) (wneg w z).
Proof.
  intros w rs z [Hw [r [Hin Hr]]]. rewrite sb_negate_ranges_equation.
  pose proof (sb_range_neg_sound w r z Hr) as [Hneg [q [Hq Hbound]]].
  split; [exact Hneg|]. exists q. split; [|exact Hbound].
  induction rs as [|a rest IH]; [contradiction|].
  cbn [fold_right]. apply in_or_app. destruct Hin as [<-|Hin]; [now left|].
  right. now apply IH.
Qed.

Definition sb_range_signed_divrem_c (division : bool) (w : width) (a b : sb_range)
    : Cost.t (list sb_range) :=
  match sb_range_sign w a, sb_range_sign w b with
  | Some sa, Some sb =>
    let aa := sb_range_magnitude w sa a in
    let bb := sb_range_magnitude w sb b in
    let magnitude := if division then sb_range_udiv w aa bb else sb_range_urem w aa bb in
    if (if division then xorb sa sb else sa)
    then sb_negate_ranges_c w magnitude else Cost.ret magnitude
  | _, _ => Cost.ret [(0, modulus w - 1)]
  end.

Definition sb_range_signed_divrem (division : bool) (w : width) (a b : sb_range)
    : list sb_range := Cost.value (sb_range_signed_divrem_c division w a b).

(** Signed quotient and remainder reuse unsigned magnitude bounds in each sign-homogeneous case. *)
Theorem sb_range_signed_divrem_sound : forall division w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_signed_divrem division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  intros division w a b x y Hx Hy Ha Hb.
  assert (Hresult : is_word w (if division then wsdiv w x y else wsrem w x y))
    by (destruct division; [apply wsdiv_is_word|apply wsrem_is_word]).
  unfold sb_range_signed_divrem, sb_range_signed_divrem_c.
  destruct (sb_range_sign w a) as [sa|] eqn:Hsa;
    destruct (sb_range_sign w b) as [sb|] eqn:Hsb.
  2,3,4: split; [exact Hresult|];
    exists (0, modulus w - 1); split; [now left|];
    unfold sb_range_gamma; cbn [fst snd]; unfold is_word in Hresult; lia.
  pose proof (sb_range_sign_sound w a x sa Hx Ha Hsa) as Hsignx.
  pose proof (sb_range_sign_sound w b y sb Hy Hb Hsb) as Hsigny.
  pose proof (sb_range_magnitude_sound w a x sa Hx Ha Hsa) as Hmagx.
  pose proof (sb_range_magnitude_sound w b y sb Hy Hb Hsb) as Hmagy.
  assert (Hnx : is_word w (wneg w x)) by (rewrite wneg_value; apply wrap_is_word).
  assert (Hny : is_word w (wneg w y)) by (rewrite wneg_value; apply wrap_is_word).
  destruct division; destruct sa, sb; cbn [xorb];
    rewrite ?wsdiv_value, ?wsrem_value, Hsignx, Hsigny;
    try apply sb_negate_ranges_sound;
    first [apply sb_range_udiv_sound|apply sb_range_urem_sound]; assumption.
Qed.
