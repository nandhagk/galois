(** * Affine linearization observations

    These examples distinguish affine arithmetic from nonlinear or malformed syntax.
    For example, subtracting twice a second variable produces a negative coefficient.
    Builds on: Key, IntervalSig, ZLang, LinForm and Linearize.

    Groups:
    - [GenericTests] Recognizing variables in the generic language.
    - [IntegerLinearTests] Linearizing integer terms.
    - [IntegerGuardTests] Linearizing integer comparisons.
    - [UnsignedLinearTests] Linearizing unsigned words.
    - [UnsignedGuardTests] Linearizing unsigned comparisons.
    - [SignedLinearTests] Linearizing signed words.
    - [SignedGuardTests] Linearizing signed comparisons.
    - [ClockTests] The time charged for linearization. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig IntervalSig ZLang BitsLang.
From Galois.Relational Require Import LinForm Linearize.
Import List.ListNotations.

(** * Fixtures *)

Module Integers := ZLinearizeCode PosKeyCode.
Module Unsigned := BitsLinearizeUCode PosKeyCode.
Module Signed := BitsLinearizeSCode PosKeyCode.

(** * Generic *)

Module GenericTests.

  Module Generic := LinearizeCode PosKeyCode ZLangCode.

  (** A variable is recognized as itself with unit coefficient and no constant. *)
  Example variable_has_unit_coefficient :
    Generic.lin_of (Leaf 3%positive) =
      Some (Lin positive [(3%positive, 1%Z)] 0%Z, NoWrap).
  Proof.
    vm_compute. reflexivity.
  Qed.

End GenericTests.

(** * Integer linearization *)

Module IntegerLinearTests.

  (** Nested additions and subtractions keep the expected coefficient signs and constant. *)
  Example nested_affine_keeps_signs_and_constant :
    Integers.lin_of
      (Node ZSub
        [Node ZAdd [Leaf 1%positive; Node (ZConst 3%Z) []];
         Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]]) =
      Some (Lin positive [(1%positive, 1%Z); (2%positive, (-2)%Z)] 3%Z, NoWrap).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A product of two constant forms scales the variable by their total. *)
  Example constant_product_scales_variable :
    Integers.lin_of
      (Node ZMul
        [Node ZAdd [Node (ZConst 2%Z) []; Node (ZConst 3%Z) []]; Leaf 1%positive]) =
      Some (Lin positive [(1%positive, 5%Z)] 0%Z, NoWrap).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A product of two variables is not affine, so it is rejected. *)
  Example product_of_variables_is_rejected :
    Integers.lin_of (Node ZMul [Leaf 1%positive; Leaf 2%positive]) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An addition with one operand is malformed, so it produces no form. *)
  Example wrong_arity_addition_is_rejected :
    Integers.lin_of (Node ZAdd [Leaf 1%positive]) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End IntegerLinearTests.

(** * Integer guards *)

Module IntegerGuardTests.

  (** Greater-than reverses its two operands in the emitted strict comparison. *)
  Example greater_than_reverses_operands :
    Integers.atoms_of (ZGuardCmp Gt) [Leaf 1%positive; Node (ZConst 7%Z) []] =
      [Atom positive (Lin positive [] 7%Z) NoWrap CLt
        (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equality keeps both affine operands in their original order. *)
  Example equality_keeps_operand_order :
    Integers.atoms_of (ZGuardCmp Eq) [Leaf 1%positive; Leaf 2%positive] =
      [Atom positive (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap CEq
        (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A nonlinear operand leaves the guard without an affine atom. *)
  Example nonlinear_operand_gives_no_atom :
    Integers.atoms_of (ZGuardCmp Lt)
      [Node ZMul [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 7%Z) []] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End IntegerGuardTests.

(** * Unsigned linearization *)

Module UnsignedLinearTests.

  (** An unsigned literal keeps its raw integer and the exact output wrap interval. *)
  Example literal_keeps_raw_value_and_wrap :
    Unsigned.lin_of (Node (BConst 8%positive 260%Z) []) =
      Some (Lin positive [] 260%Z, WrapTo 0%Z 255%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Nested additions at a literal's known width combine into one final wrap. *)
  Example nested_addition_wraps_once :
    Unsigned.lin_of
      (Node (BOp bvadd)
        [Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 250%Z) []];
         Node (BConst 8%positive 10%Z) []]) =
      Some (Lin positive [(1%positive, 1%Z)] 260%Z, WrapTo 0%Z 255%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An addition of two variables has no known width, so its output wrap is undetermined. *)
  Example unknown_width_is_rejected :
    Unsigned.lin_of (Node (BOp bvadd) [Leaf 1%positive; Leaf 2%positive]) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant word gives both the scalar coefficient and the result width of a product. *)
  Example constant_product_scales_with_word_wrap :
    Unsigned.lin_of
      (Node (BOp bvmul) [Node (BConst 8%positive 3%Z) []; Leaf 1%positive]) =
      Some (Lin positive [(1%positive, 3%Z)] 0%Z, WrapTo 0%Z 255%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A product of two variable forms at a known width is still not affine. *)
  Example known_width_product_of_variables_is_rejected :
    Unsigned.lin_of
      (Node (BOp bvmul)
        [Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 0%Z) []];
         Leaf 2%positive]) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnsignedLinearTests.

(** * Unsigned guards *)

Module UnsignedGuardTests.

  (** The store that gives variable 1 the raw word 260 at width 8 and variable 2 the word 5. *)
  Definition raw_word_store (x : positive) : positive * Z :=
    if Pos.eqb x 1%positive then (8%positive, 260%Z) else (8%positive, 5%Z).

  (** The numeric view of the raw word store. *)
  Definition raw_word_values (x : positive) : Z := BitsNumU.num (raw_word_store x).

  (** The unsigned comparison 1 < 2, as a boolean term. *)
  Definition raw_word_comparison :=
    Node (BOp bvult) [Leaf 1%positive; Leaf 2%positive].

  (** A true unsigned comparison keeps the original operand order. *)
  Example true_less_keeps_operand_order :
    Unsigned.atoms_of (BTruth true)
      [Node (BOp bvult) [Leaf 1%positive; Leaf 2%positive]] =
      [Atom positive (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap CLt
        (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A false strict comparison becomes the reversed non-strict inequality. *)
  Example false_less_reverses_into_le :
    Unsigned.atoms_of (BTruth false)
      [Node (BOp bvult) [Leaf 1%positive; Leaf 2%positive]] =
      [Atom positive (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap CLe
        (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A false non-strict word comparison reverses its operands into a strict inequality. *)
  Example false_le_reverses_into_strict :
    Unsigned.atoms_of (BTruth false)
      [Node (BOp bvule) [Leaf 1%positive; Leaf 2%positive]] =
      [Atom positive (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap CLt
        (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A signed comparison produces no atom in the unsigned numeric view. *)
  Example signed_comparison_absent_in_unsigned_view :
    Unsigned.atoms_of (BTruth true)
      [Node (BOp bvslt) [Leaf 1%positive; Leaf 2%positive]] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Evaluating the raw word comparison on the store gives the boolean true. *)
  Example raw_word_comparison_evaluates_true :
    eval_term BitsLang.eval raw_word_store raw_word_comparison = Some (1%positive, 1%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The atom of the raw comparison, read through the numeric view, has the bounds 4 and 5. *)
  Example raw_word_atom_has_numeric_bounds :
    map (fun a =>
      (wrap_into (alw a) (eval_lin raw_word_values (al a)),
       wrap_into (arw a) (eval_lin raw_word_values (ar a))))
      (Unsigned.atoms_of (BTruth true) [raw_word_comparison]) = [(4%Z, 5%Z)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnsignedGuardTests.

(** * Signed linearization *)

Module SignedLinearTests.

  (** A signed literal uses the inclusive two's complement interval. *)
  Example literal_uses_signed_interval :
    Signed.lin_of (Node (BConst 8%positive 255%Z) []) =
      Some (Lin positive [] 255%Z, WrapTo (-128)%Z 127%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed subtraction of a scaled variable keeps negative scalars and a negative constant. *)
  Example scaled_subtraction_keeps_negative_scalars :
    Signed.lin_of
      (Node (BOp bvsub)
        [Node (BOp bvmul) [Node (BConst 8%positive (-2)%Z) []; Leaf 1%positive];
         Node (BConst 8%positive 3%Z) []]) =
      Some (Lin positive [(1%positive, (-2)%Z)] (-3)%Z, WrapTo (-128)%Z 127%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The smallest signed width covers the inclusive interval from minus one through zero. *)
  Example width_one_wraps_between_minus_one_and_zero :
    Signed.lin_of
      (Node (BOp bvadd) [Leaf 1%positive; Node (BConst 1%positive 1%Z) []]) =
      Some (Lin positive [(1%positive, 1%Z)] 1%Z, WrapTo (-1)%Z 0%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

End SignedLinearTests.

(** * Signed guards *)

Module SignedGuardTests.

  (** A signed less-than keeps its operand order in the signed numeric view. *)
  Example signed_less_keeps_operand_order :
    Signed.atoms_of (BTruth true)
      [Node (BOp bvslt) [Leaf 1%positive; Leaf 2%positive]] =
      [Atom positive (Lin positive [(1%positive, 1%Z)] 0%Z) NoWrap CLt
        (Lin positive [(2%positive, 1%Z)] 0%Z) NoWrap].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A false word equality has no single affine comparison atom. *)
  Example false_equality_gives_no_atom :
    Signed.atoms_of (BTruth false)
      [Node (BOp bveq) [Leaf 1%positive; Leaf 2%positive]] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End SignedGuardTests.

(** * Clocks *)

Module ClockTests.

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

  (** The unsigned clock charges the extra work of a wider wrap interval. *)
  Example unsigned_clock_charges_width :
    N.ltb
      (UnsignedTimed.T_lin_of (Node (BConst 8%positive 0%Z) []))
      (UnsignedTimed.T_lin_of (Node (BConst 16%positive 0%Z) [])) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The signed clock charges the extra work of a wider wrap interval. *)
  Example signed_clock_charges_width :
    N.ltb
      (SignedTimed.T_lin_of (Node (BConst 8%positive 0%Z) []))
      (SignedTimed.T_lin_of (Node (BConst 16%positive 0%Z) [])) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClockTests.
