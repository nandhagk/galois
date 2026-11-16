(** * Fixed-width words

    Words are integers reduced modulo a power of two.
    For example, wrapping 260 at width eight gives 4.
    Builds on: Stdlib integer arithmetic and Argent time derivation. *)

From Stdlib Require Import ZArith NArith Lia.
From Argent Require Import Time Tactics Std.

Open Scope Z_scope.

(** Widths are strictly positive binary integers. *)
Definition width := positive.

(** The modulus is the first integer outside the unsigned word range. *)
Definition modulus (w : width) : Z := 2 ^ Zpos w.

(** The word modulus is two raised to its positive bit width. *)
Theorem modulus_value : forall w, modulus w = 2 ^ Zpos w.
Proof.
  intro w. reflexivity.
Qed.

(** The binary logarithm of the word modulus is its bit width. *)
Theorem modulus_log2 : forall w, Z.log2 (modulus w) = Zpos w.
Proof.
  intro w. rewrite modulus_value. apply Z.log2_pow2. lia.
Qed.

(** Wrapping keeps the low bits of an integer by masking them. *)
Definition wrap (w : width) (z : Z) : Z := Z.land z (Z.ones (Zpos w)).

(** Wrapping is integer remainder modulo the word modulus for arbitrary integers. *)
Theorem wrap_mod : forall w z, wrap w z = z mod modulus w.
Proof.
  intros w z. unfold wrap, modulus. apply Z.land_ones. lia.
Qed.

(** An unsigned word lies between zero and the modulus. *)
Definition is_word (w : width) (z : Z) : Prop := 0 <= z < modulus w.

(** A dynamic word records its width and its integer value. *)
Definition word : Type := (width * Z)%type.

(** Half the modulus is the weight of the sign bit. *)
Definition half (w : width) : Z := 2 ^ (Zpos w - 1).

(** The most significant bit is read after wrapping. *)
Definition msb (w : width) (z : Z) : bool := Z.testbit (wrap w z) (Zpos w - 1).

(** The signed view interprets the highest bit as a negative weight. *)
Definition signed (w : width) (z : Z) : Z :=
  let z' := wrap w z in if z' <? half w then z' else z' - modulus w.

Module Pos.
  TimeFun Pos.testbit.
End Pos.

Module N.
  TimeFun N.testbit.
End N.

Module Z.
  TimeFun Z.ones.
  TimeFun Z.size_nat.
  TimeFun Z.odd.
  TimeFun Z.pow_pos.
  TimeFun Z.pow.
  TimeFun Z.testbit.
End Z.

TimeFun modulus.
TimeFun wrap.
TimeFun half.
TimeFun msb.
TimeFun signed.

(** Signed interpretation chooses its branch after normalizing an arbitrary integer. *)
Theorem signed_value : forall w x,
  signed w x = if wrap w x <? half w then wrap w x else wrap w x - modulus w.
Proof.
  intros w x. reflexivity.
Qed.

(** Every word modulus is positive. *)
Theorem modulus_pos : forall w, 0 < modulus w.
Proof.
  intros w. unfold modulus. apply Z.pow_pos_nonneg; lia.
Qed.

(** No word modulus is zero. *)
Theorem modulus_nonzero : forall w, modulus w <> 0.
Proof.
  intros w. pose proof (modulus_pos w). lia.
Qed.

(** The weight of the sign bit is positive. *)
Theorem half_pos : forall w, 0 < half w.
Proof.
  intros w. apply Z.pow_pos_nonneg; lia.
Qed.

(** The word modulus is twice the sign-bit weight. *)
Theorem modulus_half : forall w, modulus w = 2 * half w.
Proof.
  intros w. unfold modulus, half.
  replace (Zpos w) with (Z.succ (Zpos w - 1)) at 1 by lia.
  apply Z.pow_succ_r. lia.
Qed.

(** The bit width itself fits in an unsigned word. *)
Theorem width_lt_modulus : forall w, Zpos w < modulus w.
Proof.
  intros w. apply Z.pow_gt_lin_r; lia.
Qed.

(** Wrapping always produces an unsigned word. *)
Theorem wrap_is_word : forall w z, is_word w (wrap w z).
Proof.
  intros w z. rewrite wrap_mod. apply Z.mod_pos_bound. apply modulus_pos.
Qed.

(** Wrapping fixes every unsigned word. *)
Theorem wrap_id : forall w z, is_word w z -> wrap w z = z.
Proof.
  intros w z Hword. rewrite wrap_mod. apply Z.mod_small. exact Hword.
Qed.

(** Wrapping an already wrapped value has no effect. *)
Theorem wrap_wrap : forall w z, wrap w (wrap w z) = wrap w z.
Proof.
  intros w z. apply wrap_id. apply wrap_is_word.
Qed.

(** Zero fits in every word width. *)
Theorem zero_is_word : forall w, is_word w 0.
Proof.
  intros w. pose proof (modulus_pos w). unfold is_word. lia.
Qed.

(** One fits in every word width. *)
Theorem one_is_word : forall w, is_word w 1.
Proof.
  intros w. pose proof (width_lt_modulus w). unfold is_word. lia.
Qed.

(** Wrapping preserves zero. *)
Theorem wrap_0 : forall w, wrap w 0 = 0.
Proof.
  intros w. apply wrap_id. apply zero_is_word.
Qed.

(** Wrapping preserves one. *)
Theorem wrap_1 : forall w, wrap w 1 = 1.
Proof.
  intros w. apply wrap_id. apply one_is_word.
Qed.

(** Negation may normalize its operand before the final wrap. *)
Theorem wrap_opp : forall w x, wrap w (- wrap w x) = wrap w (- x).
Proof.
  intros w x. rewrite !wrap_mod. replace (- x) with (0 - x) by ring.
  rewrite Zminus_mod, Z.mod_0_l by apply modulus_nonzero.
  reflexivity.
Qed.

(** Subtraction may normalize both operands before the final wrap. *)
Theorem wrap_sub : forall w x y,
  wrap w (x - y) = wrap w (wrap w x - wrap w y).
Proof.
  intros w x y. rewrite !wrap_mod. apply Zminus_mod.
Qed.

(** Adding an integer multiple of the modulus does not change a wrapped value. *)
Theorem wrap_add_modulus : forall w x k, wrap w (x + k * modulus w) = wrap w x.
Proof.
  intros w x k. rewrite !wrap_mod. apply Z.mod_add. apply modulus_nonzero.
Qed.

(** Addition can wrap its operands before computing. *)
Theorem wrap_add : forall w x y,
  wrap w (x + y) = wrap w (wrap w x + wrap w y).
Proof.
  intros w x y. rewrite !wrap_mod. apply Z.add_mod. apply modulus_nonzero.
Qed.

(** Multiplication can wrap its operands before computing. *)
Theorem wrap_mul : forall w x y,
  wrap w (x * y) = wrap w (wrap w x * wrap w y).
Proof.
  intros w x y. rewrite !wrap_mod. apply Z.mul_mod. apply modulus_nonzero.
Qed.

(** Narrowing after a wider wrap keeps the same low bits. *)
Theorem wrap_narrow : forall w w2 z,
  (w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z.
Proof.
  intros w w2 z Hwidth.
  assert (Hle : Zpos w <= Zpos w2) by (apply Pos2Z.pos_le_pos; exact Hwidth).
  rewrite !wrap_mod. unfold modulus.
  replace (Zpos w2) with (Zpos w + (Zpos w2 - Zpos w)) at 1 by lia.
  rewrite Z.pow_add_r by lia.
  apply Z.mod_mod_divide.
  exists (2 ^ (Zpos w2 - Zpos w)). ring.
Qed.

(** * Time contracts *)

(** A nonnegative integer below a power of two has at most that many bits. *)
Theorem integer_size_le : forall z n,
  (0 <= z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
Proof.
  intros z n. destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
  apply Pos.size_nat_least. apply Nat2Z.inj_lt.
  rewrite positive_nat_Z, Nat2Z.inj_pow. exact (proj2 Hrange).
Qed.

(** The modulus needs one bit beyond the word width. *)
Theorem modulus_size_le : forall w, (Z.size_nat (modulus w) <= Pos.to_nat w + 1)%nat.
Proof.
  intro w. apply integer_size_le. split; [pose proof (modulus_pos w); lia|].
  unfold modulus. rewrite Nat2Z.inj_add, positive_nat_Z.
  apply Z.pow_lt_mono_r; lia.
Qed.

(** The width mask has no bits above the word width. *)
Theorem ones_size_le : forall w, (Z.size_nat (Z.ones (Zpos w)) <= Pos.to_nat w)%nat.
Proof.
  intro w. apply integer_size_le. rewrite positive_nat_Z, Z.ones_equiv, <- Z.sub_1_r.
  pose proof (modulus_pos w) as Hpos. unfold modulus in Hpos. lia.
Qed.

(** Doubling has constant cost, so a power of two is linear in its exponent. *)
Theorem pow_two_time_le : forall n, (0 <= n)%Z ->
  (Z.T_pow 2 n <= 5 * N.of_nat (Z.to_nat n) + 2)%N.
Proof.
  intros n Hnonnegative. destruct n as [|p|p]; [time_step| |lia].
  pose proof (Pos.T_iter_le (Z.mul 2) (fun x => Z.T_mul 2 x)
    (fun _ => True) 3 1 p (fun _ _ => I)
    (fun x _ => Z.T_mul_two_le x) I) as Hiter.
  time_unfold Z.T_pow. time_unfold Z.T_pow_pos.
  change (Z.to_nat (Zpos p)) with (Pos.to_nat p).
  rewrite positive_nat_N. time_cbn_all. lia.
Qed.

(** Constructing the word modulus takes linear time in the width. *)
Theorem modulus_time_le : forall w, (T_modulus w <= 8 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (pow_two_time_le (Zpos w) ltac:(lia)) as Hpow.
  time_unfold T_modulus. change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hpow.
  rewrite Nat2N.inj_add. time_cbn_all. lia.
Qed.

(** Building the width mask takes linear time in the width. *)
Theorem ones_time_le : forall w, (Z.T_ones (Zpos w) <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (Z.T_shiftl_le 1 (Zpos w)) as Hshift.
  pose proof (Z.T_pred_le (Z.shiftl 1 (Zpos w))) as Hpred.
  assert (Hsize : (N.of_nat (Z.size_nat (Z.shiftl 1 (Zpos w))) <=
    N.of_nat (Pos.to_nat w + 1))%N).
  { apply time_of_nat_le. rewrite Z.shiftl_1_l. apply modulus_size_le. }
  time_unfold Z.T_ones. rewrite Nat2N.inj_add in *.
  time_cbn_all. rewrite positive_nat_N in *. nia.
Qed.

(** Wrapping reads the width mask and the raw integer, so it is linear in both sizes. *)
Theorem wrap_time_le : forall w z,
  (T_wrap w z <= 32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z. pose proof (ones_time_le w) as Hmask.
  pose proof (Z.T_land_le z (Z.ones (Zpos w))) as Hland.
  pose proof (time_of_nat_le _ _ (ones_size_le w)) as Hsize.
  time_unfold T_wrap. rewrite ?Nat2N.inj_add in *. time_cbn_all. nia.
Qed.

(** Wrapping also fits the quadratic bound in the width and the raw integer size. *)
Theorem wrap_time_quad_le : forall w z,
  (T_wrap w z <= 64 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
Proof.
  intros w z. pose proof (wrap_time_le w z) as Hlinear.
  assert (Hsquare : (N.of_nat (Pos.to_nat w + Z.size_nat z + 1) <=
    N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N).
  { apply time_of_nat_le. rewrite Nat.pow_2_r. nia. }
  lia.
Qed.
