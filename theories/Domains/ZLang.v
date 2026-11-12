(** * Integer language

    Integer operators and guards expose the views used by interval transfer.
    For example, ZAdd evaluates two operands by integer addition.
    Builds on: IntervalSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Time Tactics Std.
From Galois.Domains Require Import LangSig IntervalSig.

Module Z.
  TimeFun Z.size_nat.
End Z.

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

  Definition work (o : op) (xs : list val) : nat :=
    S (fold_right Nat.add 0 (map Z.size_nat xs)).
  TimeFun work.
  TimeFun eval.
  TimeFun literal.

  Definition c_lang : N := 1%N.
  (** STUB: constant-factor cost obligation for viewed integer evaluation. *)
  Lemma T_eval_le : forall o vs,
    (T_eval o vs <= c_lang * N.of_nat (work o vs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** STUB: uniform literal-recognition cost obligation. *)
  Lemma T_literal_le : forall o, (T_literal o <= c_lang)%N.
  Proof. Admitted. (* STUB *)
End ZLangT.
