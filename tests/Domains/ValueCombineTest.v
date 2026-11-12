(** * Value composition fixtures

    Product abstractions combine facts from their components.
    For example, a reducer can replace a product transfer result.
    Builds on: Product, Reduced and ValueOpenTest. *)

From Stdlib Require Import List Bool.
From Galois.Domains Require Import Product Reduced.
From Galois.Tests.Domains Require Import ValueOpenTest.
Import List.ListNotations.

Module ReachProduct := ProductCode UnitLanguage ReachCode ReachCode.
Module FixtureReducer.
  Definition reduce (_ : bool * bool) := (false, false).
End FixtureReducer.
Module OneRound.
  Definition rounds := 1%nat.
End OneRound.
Module ReachReduced := ReducedCode UnitLanguage ReachCode ReachCode FixtureReducer OneRound.

Example product_transfer :
  ReachProduct.forward tt [(false, true)] = (true, true).
Proof. vm_compute. reflexivity. Qed.

Example product_empty_guard : ReachProduct.guard tt [] = [].
Proof. vm_compute. reflexivity. Qed.

Example product_reducer : ReachReduced.forward tt [] = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* The old product-law client awaits conversion to module laws.
Example identity_product_laws :
  value_laws reach_product unit_sem (product_gamma bool_gamma bool_gamma).
Proof.
  apply product_laws; try exact reach_value_laws. intros p c H. exact H.
Qed.


*)
