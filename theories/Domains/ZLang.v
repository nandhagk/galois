(** * Integer language

    Integer operators and guards expose the views used by interval transfer.
    For example, ZAdd evaluates two operands by integer addition.
    Builds on: IntervalSig. *)

From Stdlib Require Import List ZArith NArith Lia PeanoNat.
From Argent Require Import Time Tactics Std.
From Galois.Domains Require Import LangSig IntervalSig.

Module ZLangCode <: Z_LANGUAGE_OPS.
  Definition op := zview.
  Definition guard := zguardview.
  Definition val := Z.
  Definition eval := zview_eval.
  Definition literal (o : op) : option Z :=
    match o with
    | ZConst z => Some z
    | _ => None
    end.
  Definition view (o : op) := o.
  Definition gview (g : guard) := g.
End ZLangCode.

Module ZLang <: Z_LANGUAGE.
  Include ZLangCode.
  Definition holds := zguard_holds.

  Lemma view_eval : forall o xs,
    view o <> ZOther -> eval o xs = zview_eval (view o) xs.
  Proof. reflexivity. Qed.

  Lemma gview_holds : forall g xs,
    gview g <> ZGuardOther -> (holds g xs <-> zguard_holds (gview g) xs).
  Proof. reflexivity. Qed.
End ZLang.

Module ZLangT <: Z_LANGUAGE_T.
  Include ZLang.

  Definition operand_bits (xs : list val) : nat :=
    fold_right Nat.add 0 (map Z.size_nat xs).
  Definition quadratic_work (xs : list val) : nat :=
    (operand_bits xs + 1) ^ 2.
  Definition shift_work (xs : list val) : nat :=
    match xs with
    | x :: y :: _ =>
      operand_bits xs + (N.to_nat (Z.abs_N y) + 1) * (Z.size_nat x + 5) + 1
    | _ => operand_bits xs + 1
    end.
  Definition work (o : op) (xs : list val) : nat :=
    match o with
    | ZMul | ZDiv | ZRem => quadratic_work xs
    | ZShl => shift_work xs
    | _ => operand_bits xs + 1
    end.
  TimeFun eval.
  TimeFun literal.
  TimeFun view.
  TimeFun gview.

  Definition c_view : N := 1%N.
  (** Viewing an integer operator takes constant time. *)
  Lemma T_view_le : forall o, (T_view o <= c_view)%N.
  Proof.
    intro o. time_unfold T_view. unfold c_view. lia.
  Qed.
  (** Viewing an integer guard takes constant time. *)
  Lemma T_gview_le : forall g, (T_gview g <= c_view)%N.
  Proof.
    intro g. time_unfold T_gview. unfold c_view. lia.
  Qed.

  Definition c_lang : N := 128%N.
  Local Lemma constant_budget : forall ticks n,
    (ticks <= 128)%N -> (ticks <= c_lang * N.of_nat (n + 1))%N.
  Proof.
    intros ticks n Hticks. unfold c_lang. rewrite Nat2N.inj_add. lia.
  Qed.

  (** Integer evaluation charges the selected primitive on valid operand shapes. *)
  Lemma T_eval_le : forall o vs,
    (T_eval o vs <= c_lang * N.of_nat (work o vs + 1))%N.
  Proof.
    intros o xs. destruct xs as [|x [|y [|z xs]]].
    - apply constant_budget. destruct o; time_unfold T_eval;
        time_unfold T_zview_eval; time_cbn; lia.
    - apply constant_budget. destruct o; time_unfold T_eval;
        time_unfold T_zview_eval; time_cbn; lia.
    - destruct o; unfold c_lang, work, quadratic_work, shift_work, operand_bits;
        cbn [map fold_right]; time_unfold T_eval; time_unfold T_zview_eval;
        time_cbn; time_pose.
      all: repeat first [rewrite Nat2N.inj_add in * | rewrite Nat2N.inj_mul in * |
        rewrite Nat2N.inj_pow in * | rewrite N2Nat.id in *].
      all: time_cases; time_cbn_all; nia.
    - apply constant_budget. destruct o; time_unfold T_eval;
        time_unfold T_zview_eval; time_cbn; lia.
  Qed.
  (** Literal recognition reads only the operator constructor. *)
  Lemma T_literal_le : forall o, (T_literal o <= c_lang)%N.
  Proof.
    intro o. destruct o; time_unfold T_literal; unfold c_lang; time_cbn; lia.
  Qed.
End ZLangT.
