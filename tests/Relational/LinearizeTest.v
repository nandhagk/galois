(** * Affine linearization observations

    These examples distinguish affine arithmetic from nonlinear or malformed syntax.
    For example, subtracting twice a second variable produces a negative coefficient.
    Builds on: Key, IntervalSig, ZLang, LinForm and Linearize. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig IntervalSig ZLang.
From Galois.Relational Require Import LinForm Linearize.
Import List.ListNotations.

Module Generic := LinearizeCode PosKeyCode ZLangCode.
Module Integers := ZLinearizeCode PosKeyCode.

(** The generic recognizer retains variable identity and its unit coefficient. *)
Example generic_variable :
  Generic.lin_of (Leaf 3%positive) =
    Some (Lin positive [(3%positive, 1%Z)] 0%Z, NoWrap).
Proof.
  vm_compute. reflexivity.
Qed.

(** Nested affine arithmetic preserves the expected coefficient signs and constant. *)
Example nested_affine :
  Integers.lin_of
    (Node ZSub
      [Node ZAdd [Leaf 1%positive; Node (ZConst 3%Z) []];
       Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]]) =
    Some (Lin positive [(1%positive, 1%Z); (2%positive, (-2)%Z)] 3%Z, NoWrap).
Proof.
  vm_compute. reflexivity.
Qed.

(** A compound constant form can scale a variable. *)
Example compound_constant_product :
  Integers.lin_of
    (Node ZMul
      [Node ZAdd [Node (ZConst 2%Z) []; Node (ZConst 3%Z) []]; Leaf 1%positive]) =
    Some (Lin positive [(1%positive, 5%Z)] 0%Z, NoWrap).
Proof.
  vm_compute. reflexivity.
Qed.

(** Products with two variable forms are rejected. *)
Example nonlinear_product :
  Integers.lin_of (Node ZMul [Leaf 1%positive; Leaf 2%positive]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** An incorrect operator arity cannot produce a form. *)
Example malformed_addition :
  Integers.lin_of (Node ZAdd [Leaf 1%positive]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** Greater-than reverses the two operands of the emitted strict comparison. *)
Example greater_guard :
  Integers.atoms_of (ZGuardCmp Gt) [Leaf 1%positive; Node (ZConst 7%Z) []] =
    [Atom positive (Lin positive [] 7%Z) NoWrap CLt
      (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap].
Proof.
  vm_compute. reflexivity.
Qed.

(** Equality preserves both affine operands in their original order. *)
Example equality_guard :
  Integers.atoms_of (ZGuardCmp Eq) [Leaf 1%positive; Leaf 2%positive] =
    [Atom positive (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap CEq
      (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap].
Proof.
  vm_compute. reflexivity.
Qed.

(** Unsupported arithmetic leaves the guard without an affine atom. *)
Example nonlinear_guard :
  Integers.atoms_of (ZGuardCmp Lt)
    [Node ZMul [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 7%Z) []] = [].
Proof.
  vm_compute. reflexivity.
Qed.
