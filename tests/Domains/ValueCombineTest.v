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

Example reduced_forward_two_operands :
  ReachReduced.forward tt [(true, true); (true, true)] = (false, false).
Proof. vm_compute. reflexivity. Qed.

Example reduced_backward_two_operands :
  ReachReduced.backward tt (true, true) [(true, true); (true, true)] =
    [(false, false); (false, false)].
Proof. vm_compute. reflexivity. Qed.

Example reduced_guard_two_operands :
  ReachReduced.guard tt [(true, true); (true, true)] = [(false, false); (false, false)].
Proof. vm_compute. reflexivity. Qed.

Module HeadReachCode.
  Definition t := bool.
  Definition leb := ReachCode.leb.
  Definition bot := ReachCode.bot.
  Definition is_bot := ReachCode.is_bot.
  Definition join := ReachCode.join.
  Definition top := ReachCode.top.
  Definition meet := ReachCode.meet.
  Definition wparam := unit.
  Definition widen := ReachCode.widen.
  Definition narrow := ReachCode.narrow.
  Definition forward (_ : unit) (xs : list bool) := hd false xs.
  Definition backward := ReachCode.backward.
  Definition guard := ReachCode.guard.
End HeadReachCode.

Module IdentityReducer.
  Definition reduce (x : bool * bool) := x.
End IdentityReducer.

Module ReachIdentity :=
  ReducedCode UnitLanguage ReachCode HeadReachCode IdentityReducer OneRound.

Example reduced_forward_nonbottom :
  ReachIdentity.forward tt [(true, true); (true, true)] = (true, true).
Proof. vm_compute. reflexivity. Qed.

Example reduced_forward_second_bottom :
  ReachIdentity.forward tt [(true, false); (true, true)] = (false, false).
Proof. vm_compute. reflexivity. Qed.

Example reduced_backward_nonbottom :
  ReachIdentity.backward tt (true, true) [(true, true); (true, true)] =
    [(true, true); (true, true)].
Proof. vm_compute. reflexivity. Qed.

Example reduced_backward_second_bottom :
  ReachIdentity.backward tt (true, true) [(true, false); (true, true)] =
    [(false, false); (true, true)].
Proof. vm_compute. reflexivity. Qed.

Example reduced_guard_nonbottom :
  ReachIdentity.guard tt [(true, true); (true, true)] = [(true, true); (true, true)].
Proof. vm_compute. reflexivity. Qed.

Example reduced_guard_second_bottom :
  ReachIdentity.guard tt [(true, false); (true, true)] = [(false, false); (true, true)].
Proof. vm_compute. reflexivity. Qed.

(* The old product-law client awaits conversion to module laws.
Example identity_product_laws :
  value_laws reach_product unit_sem (product_gamma bool_gamma bool_gamma).
Proof.
  apply product_laws; try exact reach_value_laws. intros p c H. exact H.
Qed.


*)

Inductive weak_fact : Type := WBot | WPoint | WTop.
Module WeakJoin.
  Definition bot := WBot.
  Definition join (_ _ : weak_fact) := WTop.
End WeakJoin.
Module OrderedJoin.
  Definition bot := 0%nat.
  Definition join (a b : nat) := (2 * a + b + 1)%nat.
End OrderedJoin.

Definition join_all {A} (bot : A) (join : A -> A -> A) (xs : list A) :=
  match xs with
  | [] => bot
  | x :: rest => fold_left join rest x
  end.

Example weak_singleton_keeps_point : join_all WeakJoin.bot WeakJoin.join [WPoint] = WPoint.
Proof. vm_compute. reflexivity. Qed.

Example weak_empty_uses_bottom : join_all WeakJoin.bot WeakJoin.join [] = WBot.
Proof. vm_compute. reflexivity. Qed.

Example ordered_join_is_left_fold : join_all OrderedJoin.bot OrderedJoin.join [1; 2; 3] = 14.
Proof. vm_compute. reflexivity. Qed.

Example ordered_join_retains_input_order :
  join_all OrderedJoin.bot OrderedJoin.join [3; 2; 1] = 20.
Proof. vm_compute. reflexivity. Qed.

Example product_join_all :
  join_all ReachProduct.bot ReachProduct.join [(false, true); (true, false)] = (true, true).
Proof. vm_compute. reflexivity. Qed.
