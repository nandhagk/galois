(** * Bit-vector language

    Operators evaluate fixed-width words and literals retain their widths.
    For example, an eight-bit literal is wrapped before evaluation returns it.
    Builds on: LangSig and bit-vector operations. *)

From Stdlib Require Import List ZArith NArith Bool Lia Ring.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Fun Testbit Op Arith.
From Galois.Domains Require Import LangSig WordSig.
Import List.ListNotations.

Module WordAlgebra.
  Local Open Scope Z_scope.

  (** Bitwise conjunction with zero returns zero. *)
  Lemma const_zero_bits : forall w x, is_word w x -> wand w 0 x = 0.
  Proof.
    intros w x Hx. apply (word_ext w); [apply wand_is_word|apply zero_is_word|].
    intros i Hi. rewrite testbit_wand by (auto using zero_is_word; lia).
    now rewrite !Z.bits_0.
  Qed.

  (** Bitwise disjunction with the all-ones word returns that word. *)
  Lemma const_ones_bits : forall w x,
    is_word w x -> wor w (modulus w - 1) x = modulus w - 1.
  Proof.
    intros w x Hx. apply (word_ext w); [apply wor_is_word|apply ones_is_word|].
    intros i Hi. rewrite testbit_wor by (auto using ones_is_word; lia).
    rewrite all_ones_bits by exact Hi.
    destruct (i <? Zpos w) eqn:Hlow; cbn; [reflexivity|].
    apply Z.ltb_ge in Hlow. exact (word_bits_high w x i Hx Hlow).
  Qed.

  (** Multiplication, shifts and unsigned remainder preserve a zero left operand. *)
  Lemma const_zero_ops : forall w y, is_word w y ->
    wmul w 0 y = 0 /\ wshl w 0 y = 0 /\ wlshr w 0 y = 0 /\
    washr w 0 y = 0 /\ wurem w 0 y = 0.
  Proof.
    intros w y Hy.
    assert (Hpow : 2 ^ wrap w y <> 0).
    { pose proof (wrap_is_word w y) as [Hnonnegative Hupper].
      apply Z.pow_nonzero; lia. }
    rewrite wmul_value, wshl_value, wlshr_value, washr_value, wurem_mod.
    rewrite wrap_0, msb_zero, signed_zero, Z.mul_0_l, wrap_0.
    rewrite Z.div_0_l by exact Hpow. rewrite wrap_0.
    split; [reflexivity|].
    destruct (Zpos w <=? wrap w y); cbn; repeat split; try reflexivity.
    all: destruct (Z.eq_dec (wrap w y) 0) as [-> | Hz];
      [reflexivity|now apply Z.mod_0_l].
  Qed.

  (** Adding and then subtracting the same operand recovers a word. *)
  Lemma const_add_inverse : forall w x y,
    is_word w x -> wsub w (wadd w x y) y = x.
  Proof.
    intros w x y Hx. rewrite wsub_value, wadd_value, wrap_sub, wrap_wrap, <- wrap_sub.
    replace (x + y - y) with x by ring. now apply wrap_id.
  Qed.

  (** Adding back a subtracted operand recovers a word. *)
  Lemma const_sub_inverse_left : forall w x y,
    is_word w x -> wadd w (wsub w x y) y = x.
  Proof.
    intros w x y Hx. rewrite wadd_value, wsub_value, wrap_add, wrap_wrap, <- wrap_add.
    replace (x - y + y) with x by ring. now apply wrap_id.
  Qed.

  (** Subtracting the difference recovers the right operand. *)
  Lemma const_sub_inverse_right : forall w x y,
    is_word w y -> wsub w x (wsub w x y) = y.
  Proof.
    intros w x y Hy. rewrite !wsub_value, wrap_sub, wrap_wrap, <- wrap_sub.
    replace (x - (x - y)) with y by ring. now apply wrap_id.
  Qed.

  (** Applying xor with the same word twice recovers the first word. *)
  Lemma const_xor_inverse : forall w x y,
    is_word w x -> wxor w (wxor w x y) y = x.
  Proof.
    intros w x y Hx. rewrite <- wxor_assoc, wxor_self.
    apply (word_ext w); [apply wxor_is_word|exact Hx|].
    intros i Hi. rewrite testbit_wxor by (auto using zero_is_word; lia).
    now rewrite Z.bits_0, xorb_false_r.
  Qed.

  (** Word negation is an involution on normalized words. *)
  Lemma const_neg_inverse : forall w x,
    is_word w x -> wneg w (wneg w x) = x.
  Proof.
    intros w x Hx. rewrite !wneg_value, wrap_opp.
    replace (- - x) with x by ring. now apply wrap_id.
  Qed.

End WordAlgebra.

Module WordTime.

  (** A nonnegative integer below a power of two has at most that many bits. *)
  Lemma integer_size_bound z n :
    (0 <= z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
  Proof.
    destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
    apply Pos.size_nat_least. apply Nat2Z.inj_lt.
    rewrite positive_nat_Z, Nat2Z.inj_pow. exact (proj2 Hrange).
  Qed.

  (** Every normalized word fits its declared bit width. *)
  Lemma word_size_bound w z : is_word w z -> (Z.size_nat z <= Pos.to_nat w)%nat.
  Proof.
    intros Hword. apply integer_size_bound.
    rewrite positive_nat_Z. exact Hword.
  Qed.

  (** Wrapping always produces a word within its declared bit width. *)
  Lemma word_wrap_size_bound w z : (Z.size_nat (wrap w z) <= Pos.to_nat w)%nat.
  Proof.
    apply word_size_bound, wrap_is_word.
  Qed.

  (** The modulus needs one bit beyond the word width. *)
  Lemma word_modulus_size_bound w : (Z.size_nat (modulus w) <= Pos.to_nat w + 1)%nat.
  Proof.
    apply integer_size_bound. split; [pose proof (modulus_pos w); lia|].
    unfold modulus. rewrite Nat2Z.inj_add, positive_nat_Z.
    apply Z.pow_lt_mono_r; lia.
  Qed.

  (** Half the modulus fits within the declared word width. *)
  Lemma word_half_size_bound w : (Z.size_nat (half w) <= Pos.to_nat w)%nat.
  Proof.
    apply word_size_bound. unfold is_word.
    pose proof (half_pos w). pose proof (modulus_half w). lia.
  Qed.

  (** A symmetric power-of-two interval also bounds signed magnitudes. *)
  Lemma integer_abs_size_bound z n :
    (- (2 ^ Z.of_nat n) < z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
  Proof.
    destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
    - apply (integer_size_bound (Zpos p) n). lia.
    - apply (integer_size_bound (Zpos p) n). lia.
  Qed.

  (** Signed interpretations have at most the declared width many magnitude bits. *)
  Lemma word_signed_size_bound w z : (Z.size_nat (signed w z) <= Pos.to_nat w)%nat.
  Proof.
    apply integer_abs_size_bound. rewrite positive_nat_Z.
    fold (modulus w). pose proof (signed_range w z).
    pose proof (half_pos w). pose proof (modulus_half w). lia.
  Qed.

  (** Integer negation preserves magnitude bit length. *)
  Lemma integer_opp_size z : Z.size_nat (- z) = Z.size_nat z.
  Proof.
    destruct z; reflexivity.
  Qed.

  (** A positive integer's bit length does not exceed its numeric value. *)
  Lemma positive_size_value w : (Pos.size_nat w <= Pos.to_nat w)%nat.
  Proof.
    induction w as [w IH|w IH|]; cbn [Pos.size_nat];
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
  Qed.

  (** Doubling has constant cost, so constructing a power of two is linear in its exponent. *)
  Lemma word_pow_two_time_bound n : (0 <= n)%Z ->
    (Word.Z.T_pow 2 n <= 5 * N.of_nat (Z.to_nat n) + 2)%N.
  Proof.
    intros Hnonnegative. destruct n as [|p|p]; [time_step| |lia].
    pose proof (Pos.T_iter_le (Z.mul 2) (fun x => Z.T_mul 2 x)
      (fun _ => True) 3 1 p (fun _ _ => I)
      (fun x _ => Z.T_mul_two_le x) I) as Hiter.
    time_unfold Word.Z.T_pow. time_unfold Word.Z.T_pow_pos.
    change (Z.to_nat (Zpos p)) with (Pos.to_nat p).
    rewrite positive_nat_N. time_cbn_all. lia.
  Qed.

  (** Constructing the word modulus takes linear time in the width. *)
  Lemma word_modulus_time_bound w :
    (T_modulus w <= 8 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    pose proof (word_pow_two_time_bound (Zpos w) ltac:(lia)) as Hpow.
    time_unfold T_modulus. change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hpow.
    rewrite Nat2N.inj_add. time_cbn_all. lia.
  Qed.

  (** The half modulus charges subtraction of the width and a power-of-two construction. *)
  Lemma word_half_time_bound w :
    (T_half w <= 32 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    pose proof (word_pow_two_time_bound (Zpos w - 1) ltac:(lia)) as Hpow.
    pose proof (Z.T_sub_le (Zpos w) 1) as Hsub.
    assert (Hwidth : (N.of_nat (Pos.size_nat w) <= N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply positive_size_value. }
    assert (Hexponent : (N.of_nat (Z.to_nat (Zpos w - 1)) <=
      N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia. rewrite positive_nat_Z. lia. }
    time_unfold T_half. change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in Hsub.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  (** Modular wrapping charges the width and the raw integer's bit length quadratically. *)
  Lemma word_wrap_time_bound w z :
    (T_wrap w z <= 64 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_modulo_le z (modulus w)) as Hremainder.
    assert (Hsize : (N.of_nat (Z.size_nat (modulus w)) <=
      N.of_nat (Pos.to_nat w + 1))%N).
    { apply time_of_nat_le. apply word_modulus_size_bound. }
    time_unfold T_wrap. rewrite !Nat2N.inj_add, !Nat2N.inj_pow in *.
    time_cbn_all. nia.
  Qed.

  (** Signed interpretation adds only linear work to modular wrapping. *)
  Lemma word_signed_time_bound w z :
    (T_signed w z <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w z) as Hwrap.
    pose proof (word_half_time_bound w) as Hhalf.
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_ltb_le (wrap w z) (half w)) as Hcompare.
    pose proof (Z.T_sub_le (wrap w z) (modulus w)) as Hsubtract.
    assert (Hsize : (N.of_nat (Z.size_nat (wrap w z)) <=
      N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply word_wrap_size_bound. }
    assert (Hmodsize : (N.of_nat (Z.size_nat (modulus w)) <=
      N.of_nat (Pos.to_nat w + 1))%N).
    { apply time_of_nat_le. apply word_modulus_size_bound. }
    time_unfold T_signed. destruct (wrap w z <? half w)%Z;
      rewrite !Nat2N.inj_add, !Nat2N.inj_pow in *; time_cbn_all; nia.
  Qed.

End WordTime.


Inductive bop : Type :=
  | BConst (w : width) (z : Z)
  | BOp (o : Op.op).

Inductive bguard : Type :=
  | BTruth (b : bool).

(** Operator work charges its own widths and literal before operand widths. *)
Definition op_bits (o : bop) : nat :=
  match o with
  | BConst w z => Pos.to_nat w + Z.size_nat z
  | BOp o => Op.op_widths o
  end.

(** Word evaluation charges metadata, operand widths and raw integer sizes quadratically. *)
Definition work (o : bop) (vs : list word) : nat :=
  ((op_bits o + fold_right Nat.add 0
    (map (fun v => Pos.to_nat (fst v) + Z.size_nat (snd v)) vs) + 1) ^ 2)%nat.

Module Nat.
  TimeFun Nat.pow.
End Nat.

TimeFun op_bits.
TimeFun work.

Module BitsLangCode <: LANG_OPS.
  Definition op := bop.
  Definition guard := bguard.
  Definition val := word.
  Definition eval (o : op) (vs : list val) : option val :=
    match o, vs with
    | BConst w z, [] => Some (w, wrap w z)
    | BOp o, _ => eval_op o vs
    | _, _ => None
    end.
  Definition literal (o : op) : option Z :=
    match o with
    | BConst _ z => Some z
    | BOp _ => None
    end.
End BitsLangCode.

Module BitsLang <: LANG.
  Include BitsLangCode.
  Definition holds (g : guard) (vs : list val) : Prop :=
    match g, vs with
    | BTruth b, (w, z) :: nil => w = 1%positive /\ z = (if b then 1 else 0)%Z
    | _, _ => False
    end.
End BitsLang.

Module WordLanguageCode <: WORD_LANGUAGE_OPS.
  Definition op := Op.op.
  Definition wrap := Word.wrap.
  Definition signed := Word.signed.
  Definition eval_op := Op.eval_op.
  Definition result_width := Op.result_width.
End WordLanguageCode.

Module WordLanguage <: WORD_LANGUAGE.
  Include WordLanguageCode.
  Definition is_word := Word.is_word.
  Lemma wrap_is_word : forall w z, is_word w (wrap w z).
  Proof. exact Word.wrap_is_word. Qed.
  Lemma eval_op_is_word : forall o cs w z, eval_op o cs = Some (w, z) ->
    is_word w z /\ result_width o (map fst cs) = Some w.
  Proof.
    intros o cs w z Hresult. split.
    - exact (Op.eval_op_is_word o cs (w, z) Hresult).
    - exact (Op.eval_op_width o cs (w, z) Hresult).
  Qed.
End WordLanguage.

Module BitsLangT <: LANG_T.
  Include BitsLang.
  Definition work := work.
  TimeFun eval.
  TimeFun literal.
  Definition c_lang : N := 1%N. (* STUB *)
  Lemma T_eval_le : forall o vs,
    (T_eval o vs <= c_lang * N.of_nat (work o vs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_literal_le : forall o, (T_literal o <= c_lang)%N.
  Proof. Admitted. (* STUB *)
End BitsLangT.

Module WordLanguageT <: WORD_LANGUAGE_T.
  Include WordLanguage.
  TimeFun wrap.
  TimeFun signed.
  TimeFun eval_op.
  TimeFun result_width.
  Definition c_word : N := 1%N. (* STUB *)
  Lemma T_eval_op_le : forall o cs,
    (T_eval_op o cs <=
      c_word * N.of_nat (((Op.op_widths o +
        fold_right Nat.add 0
          (map (fun c => Pos.to_nat (fst c) + Z.size_nat (snd c)) cs) + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
End WordLanguageT.
