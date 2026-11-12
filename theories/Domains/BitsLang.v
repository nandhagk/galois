(** * Bit-vector language

    Operators evaluate fixed-width words and literals retain their widths.
    For example, an eight-bit literal is wrapped before evaluation returns it.
    Builds on: LangSig and bit-vector operations. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Std.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig.
Import List.ListNotations.

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

(** Word evaluation charges the combined metadata and operand widths quadratically. *)
Definition work (o : bop) (vs : list word) : nat :=
  ((op_bits o + fold_right Nat.add 0 (map (fun v => Pos.to_nat (fst v)) vs) + 1) ^ 2)%nat.

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
