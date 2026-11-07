(** * Differential word-value fixtures

    These observations compare point transfers with legacy constants on defined expressions.
    For example, true thirty-two-bit addition keeps the same concrete singleton operands.
    Builds on: DomainsPoint and the legacy numeric constant dictionary. *)

From Stdlib Require Import List ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsOp BitsExpr.
From Galois.Domains Require Import DomainsValue DomainsNumeric DomainsTagged DomainsPoint
  DomainsBitsValue.
From GaloisLegacy.Order Require Import OrderFlat.
From GaloisLegacy.Bits Require Import BitsOp BitsExpr.
From GaloisLegacy.Domains Require Import DomainsNumeric DomainsConst.
Import List.ListNotations.

Module NewOp := Galois.Bits.BitsOp.
Module OldOp := GaloisLegacy.Bits.BitsOp.

Definition new_numeric := DomainsTagged.tagged_domain point_word_domain.
Definition old_numeric := DomainsNumeric.tagged_domain const_domain.

Definition new_bridge : op_bridge BitsExpr.expr (positive * Z) :=
  {| op_expr_c := fun e => Cost.ret (Some e);
     to_word_c := fun w => Cost.ret (Some w);
     truth_words := true;
     differ_words_c := fun _ => Cost.ret false |}.

Definition new_values := bits_values new_numeric new_bridge DomainsTagged.TAny.

Definition observe_new (xs : list (DomainsTagged.tagged point)) : list (option Z) :=
  map (fun x =>
    match x with DomainsTagged.TVal _ (PVal z) => Some z | _ => None end) xs.

Definition observe_old (xs : list (DomainsNumeric.tagged (flat Z))) : list (option Z) :=
  map (fun x =>
    match x with DomainsNumeric.TVal _ (FVal z) => Some z | _ => None end) xs.

Definition old_truth (e : Bits.expr) (b : bool) xs :=
  map (DomainsNumeric.abs_assume old_numeric (fun i => nth i xs DomainsNumeric.TAny)
    (Bits.App OldOp.bvne [e; Bits.App OldOp.bvxor [e; e]])
    (DomainsNumeric.of_const old_numeric 1%positive (if b then 1%Z else 0%Z)))
    (seq 0 (length xs)).

Example truth_addition_differential :
  observe_new (ValueAbs.guard new_values
    (Test (Expr.App NewOp.bvadd [Expr.Var 0; Expr.Var 1]) true)
    [DomainsTagged.TVal 32%positive (PVal 1); DomainsTagged.TVal 32%positive (PVal 1)]) =
  observe_old (old_truth (Bits.App OldOp.bvadd [Bits.Var 0; Bits.Var 1]) true
    [DomainsNumeric.TVal 32%positive (FVal 1); DomainsNumeric.TVal 32%positive (FVal 1)]).
Proof. vm_compute. reflexivity. Qed.

Example truth_zero_differential :
  observe_new (ValueAbs.guard new_values (Truth false)
    [DomainsTagged.TVal 32%positive (PVal 0)]) =
  observe_old (old_truth (Bits.Var 0) false [DomainsNumeric.TVal 32%positive (FVal 0)]).
Proof. vm_compute. reflexivity. Qed.

Example truth_nonzero_differential :
  observe_new (ValueAbs.guard new_values (Truth true)
    [DomainsTagged.TVal 32%positive (PVal 7)]) =
  observe_old (old_truth (Bits.Var 0) true [DomainsNumeric.TVal 32%positive (FVal 7)]).
Proof. vm_compute. reflexivity. Qed.

Example truncation_truth_differential :
  observe_new (ValueAbs.guard new_values
    (Test (Expr.App (NewOp.bvtrunc 1%positive) [Expr.Var 0]) false)
    [DomainsTagged.TVal 32%positive (PVal 2)]) =
  observe_old (old_truth (Bits.App (OldOp.bvtrunc 1%positive) [Bits.Var 0]) false
    [DomainsNumeric.TVal 32%positive (FVal 2)]).
Proof. vm_compute. reflexivity. Qed.

Example comparison_truth_differential :
  observe_new (ValueAbs.guard new_values
    (Test (Expr.App NewOp.bvult [Expr.Var 0; Expr.Var 1]) true)
    [DomainsTagged.TVal 32%positive (PVal 1); DomainsTagged.TVal 32%positive (PVal 2)]) =
  observe_old (old_truth (Bits.App OldOp.bvult [Bits.Var 0; Bits.Var 1]) true
    [DomainsNumeric.TVal 32%positive (FVal 1); DomainsNumeric.TVal 32%positive (FVal 2)]).
Proof. vm_compute. reflexivity. Qed.

Example unknown_true_differential :
  observe_new (ValueAbs.guard new_values (Truth true) [DomainsTagged.TAny]) =
  observe_old (old_truth (Bits.Var 0) true [DomainsNumeric.TAny]).
Proof. vm_compute. reflexivity. Qed.

Example unknown_false_differential :
  observe_new (ValueAbs.guard new_values (Truth false) [DomainsTagged.TAny]) =
  observe_old (old_truth (Bits.Var 0) false [DomainsNumeric.TAny]).
Proof. vm_compute. reflexivity. Qed.
