(** * Fixed-width words

    Words are integers reduced modulo a power of two.
    For example, wrapping 260 at width eight gives 4.
    Builds on: Stdlib integer arithmetic. *)

From Stdlib Require Import ZArith Lia.
From Argent Require Import Time Std.

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

(** Wrapping keeps the low bits of an integer. *)
Definition wrap (w : width) (z : Z) : Z := z mod modulus w.

(** Wrapping is integer remainder modulo the word modulus for arbitrary integers. *)
Theorem wrap_mod : forall w z, wrap w z = z mod modulus w.
Proof.
  intros w z. reflexivity.
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
  intros w z. apply Z.mod_pos_bound. apply modulus_pos.
Qed.

(** Wrapping fixes every unsigned word. *)
Theorem wrap_id : forall w z, is_word w z -> wrap w z = z.
Proof.
  intros w z Hword. apply Z.mod_small. exact Hword.
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
  intros w x. unfold wrap. replace (- x) with (0 - x) by ring.
  rewrite Zminus_mod, Z.mod_0_l by apply modulus_nonzero.
  reflexivity.
Qed.

(** Subtraction may normalize both operands before the final wrap. *)
Theorem wrap_sub : forall w x y,
  wrap w (x - y) = wrap w (wrap w x - wrap w y).
Proof.
  intros w x y. apply Zminus_mod.
Qed.

(** Adding an integer multiple of the modulus does not change a wrapped value. *)
Theorem wrap_add_modulus : forall w x k, wrap w (x + k * modulus w) = wrap w x.
Proof.
  intros w x k. apply Z.mod_add. apply modulus_nonzero.
Qed.

(** Addition can wrap its operands before computing. *)
Theorem wrap_add : forall w x y,
  wrap w (x + y) = wrap w (wrap w x + wrap w y).
Proof.
  intros w x y. apply Z.add_mod. apply modulus_nonzero.
Qed.

(** Multiplication can wrap its operands before computing. *)
Theorem wrap_mul : forall w x y,
  wrap w (x * y) = wrap w (wrap w x * wrap w y).
Proof.
  intros w x y. apply Z.mul_mod. apply modulus_nonzero.
Qed.

(** Narrowing after a wider wrap keeps the same low bits. *)
Theorem wrap_narrow : forall w w2 z,
  (w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z.
Proof.
  intros w w2 z Hwidth.
  assert (Hle : Zpos w <= Zpos w2) by (apply Pos2Z.pos_le_pos; exact Hwidth).
  unfold wrap, modulus.
  replace (Zpos w2) with (Zpos w + (Zpos w2 - Zpos w)) at 1 by lia.
  rewrite Z.pow_add_r by lia.
  apply Z.mod_mod_divide.
  exists (2 ^ (Zpos w2 - Zpos w)). ring.
Qed.
