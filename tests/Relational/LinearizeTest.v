(** * Affine linearization observations

    These examples distinguish affine arithmetic from nonlinear or malformed syntax.
    For example, subtracting twice a second variable produces a negative coefficient.
    Builds on: Key, IntervalSig, ZLang, LinForm and Linearize. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig IntervalSig ZLang BitsLang.
From Galois.Relational Require Import LinForm Linearize.
Import List.ListNotations.

Module Generic := LinearizeCode PosKeyCode ZLangCode.
Module Integers := ZLinearizeCode PosKeyCode.
Module Unsigned := BitsLinearizeUCode PosKeyCode.
Module Signed := BitsLinearizeSCode PosKeyCode.

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

(** Unsigned literals retain their raw integer and the exact output wrap interval. *)
Example unsigned_literal :
  Unsigned.lin_of (Node (BConst 8%positive 260%Z) []) =
    Some (Lin positive [] 260%Z, WrapTo 0%Z 255%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Signed literals use the inclusive two's complement interval. *)
Example signed_literal :
  Signed.lin_of (Node (BConst 8%positive 255%Z) []) =
    Some (Lin positive [] 255%Z, WrapTo (-128)%Z 127%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Nested additions at a literal's known width combine into one final wrap. *)
Example unsigned_nested_addition :
  Unsigned.lin_of
    (Node (BOp bvadd)
      [Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 250%Z) []];
       Node (BConst 8%positive 10%Z) []]) =
    Some (Lin positive [(1%positive, 1%Z)] 260%Z, WrapTo 0%Z 255%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** An unannotated pair of variables cannot determine its output wrap width. *)
Example unknown_width_addition :
  Unsigned.lin_of (Node (BOp bvadd) [Leaf 1%positive; Leaf 2%positive]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** A constant word provides both a scalar coefficient and the required result width. *)
Example unsigned_constant_product :
  Unsigned.lin_of
    (Node (BOp bvmul) [Node (BConst 8%positive 3%Z) []; Leaf 1%positive]) =
    Some (Lin positive [(1%positive, 3%Z)] 0%Z, WrapTo 0%Z 255%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A true unsigned comparison keeps the original operand order. *)
Example unsigned_less_guard :
  Unsigned.atoms_of (BTruth true)
    [Node (BOp bvult) [Leaf 1%positive; Leaf 2%positive]] =
    [Atom positive (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap CLt
      (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap].
Proof.
  vm_compute. reflexivity.
Qed.

(** A false strict comparison becomes the reversed non-strict inequality. *)
Example unsigned_false_less_guard :
  Unsigned.atoms_of (BTruth false)
    [Node (BOp bvult) [Leaf 1%positive; Leaf 2%positive]] =
    [Atom positive (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap CLe
      (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap].
Proof.
  vm_compute. reflexivity.
Qed.

(** Signed comparison uses the same affine syntax in the signed numeric view. *)
Example signed_less_guard :
  Signed.atoms_of (BTruth true)
    [Node (BOp bvslt) [Leaf 1%positive; Leaf 2%positive]] =
    [Atom positive (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap CLt
      (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap].
Proof.
  vm_compute. reflexivity.
Qed.

(** A signed comparison is not emitted in the unsigned numeric view. *)
Example mismatched_comparison_view :
  Unsigned.atoms_of (BTruth true)
    [Node (BOp bvslt) [Leaf 1%positive; Leaf 2%positive]] = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** False equality has no single affine comparison atom. *)
Example false_word_equality :
  Signed.atoms_of (BTruth false)
    [Node (BOp bveq) [Leaf 1%positive; Leaf 2%positive]] = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** Raw word stores are normalized consistently by concrete evaluation and the numeric view. *)
Example raw_word_guard :
  let st := fun x : positive =>
    if Pos.eqb x 1%positive then (8%positive, 260%Z) else (8%positive, 5%Z) in
  let e := Node (BOp bvult) [Leaf 1%positive; Leaf 2%positive] in
  let atoms := Unsigned.atoms_of (BTruth true) [e] in
  let v := fun x => BitsNumU.num (st x) in
  (eval_term BitsLang.eval st e,
   map (fun a =>
     (wrap_into (alw a) (eval_lin v (al a)),
      wrap_into (arw a) (eval_lin v (ar a)))) atoms) =
    (Some (1%positive, 1%Z), [(4%Z, 5%Z)]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Signed affine arithmetic preserves negative scalars and a final negative constant. *)
Example signed_scaled_subtraction :
  Signed.lin_of
    (Node (BOp bvsub)
      [Node (BOp bvmul) [Node (BConst 8%positive (-2)%Z) []; Leaf 1%positive];
       Node (BConst 8%positive 3%Z) []]) =
    Some (Lin positive [(1%positive, (-2)%Z)] (-3)%Z, WrapTo (-128)%Z 127%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A known width does not make a product of two variable forms affine. *)
Example known_width_nonlinear_product :
  Unsigned.lin_of
    (Node (BOp bvmul)
      [Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 0%Z) []];
       Leaf 2%positive]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** The smallest signed width uses the inclusive interval from minus one through zero. *)
Example signed_width_one_addition :
  Signed.lin_of
    (Node (BOp bvadd) [Leaf 1%positive; Node (BConst 1%positive 1%Z) []]) =
    Some (Lin positive [(1%positive, 1%Z)] 1%Z, WrapTo (-1)%Z 0%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A false non-strict word comparison reverses its operands into a strict inequality. *)
Example unsigned_false_le_guard :
  Unsigned.atoms_of (BTruth false)
    [Node (BOp bvule) [Leaf 1%positive; Leaf 2%positive]] =
    [Atom positive (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap CLt
      (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap].
Proof.
  vm_compute. reflexivity.
Qed.

Module IntegersTimed := ZLinearizeT PosKeyT.
Module UnsignedTimed := BitsLinearizeUT PosKeyT.
Module SignedTimed := BitsLinearizeST PosKeyT.

(** The derived integer clock charges recursive arithmetic beyond the variable leaf. *)
Example integer_clock_grows_with_syntax :
  N.ltb (IntegersTimed.T_lin_of (Leaf 1%positive))
    (IntegersTimed.T_lin_of
      (Node ZAdd [Leaf 1%positive; Node (ZConst 1%Z) []])) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Both word clocks charge the extra work needed to construct wider wrap intervals. *)
Example word_clocks_charge_width :
  (N.ltb
     (UnsignedTimed.T_lin_of (Node (BConst 8%positive 0%Z) []))
     (UnsignedTimed.T_lin_of (Node (BConst 16%positive 0%Z) [])),
   N.ltb
     (SignedTimed.T_lin_of (Node (BConst 8%positive 0%Z) []))
     (SignedTimed.T_lin_of (Node (BConst 16%positive 0%Z) []))) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.
