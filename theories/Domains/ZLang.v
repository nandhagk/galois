(** * Integer language

    Integer operators and guards expose the views used by interval transfer.
    For example, ZAdd evaluates two operands by integer addition.
    Builds on: IntervalSig. *)

From Stdlib Require Import List ZArith.
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
