(** * Bit-vector language

    Operators evaluate fixed-width words and literals retain their widths.
    For example, an eight-bit literal is wrapped before evaluation returns it.
    Builds on: LangSig and bit-vector operations. *)

From Stdlib Require Import List ZArith.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig.
Import List.ListNotations.

Inductive bop : Type :=
  | BConst (w : width) (z : Z)
  | BOp (o : Op.op).

Inductive bguard : Type :=
  | BTruth (b : bool).

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
