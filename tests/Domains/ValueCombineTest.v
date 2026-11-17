(** * Value composition fixtures

    Product abstractions combine facts from their components.
    For example, a reducer can replace a product transfer result.
    Builds on: Product, Reduced and ValueOpenTest. *)

(* Groups:
   - Product: forward, guard and reduced transfers of a product of reachability domains.
   - Reduced identity: reduced transfers with a reducer that keeps its input.
   - Join: left folds of joins over lists, with weak and ordered joins. *)

From Stdlib Require Import List Bool.
From Galois.Domains Require Import Product Reduced.
From Galois.Tests.Domains Require Import ValueOpenTest.
Import List.ListNotations.

(** * Product *)

Module ReachProduct := ProductCode UnitLanguage ReachCode ReachCode.
Module FixtureReducer.
  Definition reduce (_ : bool * bool) := (false, false).
End FixtureReducer.
Module OneRound.
  Definition rounds := 1%nat.
End OneRound.
Module ReachReduced := ReducedCode UnitLanguage ReachCode ReachCode FixtureReducer OneRound.

Module ProductTests.

  (** The product forward transfer combines the components of its single operand. *)
  Example product_forward_pair :
    ReachProduct.forward tt [(false, true)] = (true, true).
  Proof. vm_compute. reflexivity. Qed.

  (** The product guard on no operands gives no operands. *)
  Example product_guard_empty_is_empty : ReachProduct.guard tt [] = [].
  Proof. vm_compute. reflexivity. Qed.

  (** The reduced forward transfer of no operands gives the reduced bottom pair. *)
  Example reduced_forward_empty_is_reduced_bottom :
    ReachReduced.forward tt [] = (false, false).
  Proof. vm_compute. reflexivity. Qed.

  (** The reduced forward transfer of two operands gives the reduced bottom pair. *)
  Example reduced_forward_two_is_reduced_bottom :
    ReachReduced.forward tt [(true, true); (true, true)] = (false, false).
  Proof. vm_compute. reflexivity. Qed.

  (** The reduced backward transfer of two operands gives two reduced bottom pairs. *)
  Example reduced_backward_two_is_reduced_bottoms :
    ReachReduced.backward tt (true, true) [(true, true); (true, true)] =
      [(false, false); (false, false)].
  Proof. vm_compute. reflexivity. Qed.

  (** The reduced guard of two operands gives two reduced bottom pairs. *)
  Example reduced_guard_two_is_reduced_bottoms :
    ReachReduced.guard tt [(true, true); (true, true)] =
      [(false, false); (false, false)].
  Proof. vm_compute. reflexivity. Qed.

End ProductTests.

(** * Reduced identity *)

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

Module ReducedIdentityTests.

  (** A non-bottom first operand keeps the reduced forward result. *)
  Example forward_nonbottom_keeps_pair :
    ReachIdentity.forward tt [(true, true); (true, true)] = (true, true).
  Proof. vm_compute. reflexivity. Qed.

  (** A bottom second operand makes the reduced forward result bottom. *)
  Example forward_bottom_second_gives_bottom :
    ReachIdentity.forward tt [(true, false); (true, true)] = (false, false).
  Proof. vm_compute. reflexivity. Qed.

  (** Backward on non-bottom operands keeps every operand. *)
  Example backward_nonbottom_keeps_operands :
    ReachIdentity.backward tt (true, true) [(true, true); (true, true)] =
      [(true, true); (true, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** A bottom second operand is reduced in the backward result. *)
  Example backward_bottom_second_is_reduced :
    ReachIdentity.backward tt (true, true) [(true, false); (true, true)] =
      [(false, false); (true, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** The guard on non-bottom operands keeps every operand. *)
  Example guard_nonbottom_keeps_operands :
    ReachIdentity.guard tt [(true, true); (true, true)] = [(true, true); (true, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** A bottom second operand is reduced in the guard result. *)
  Example guard_bottom_second_is_reduced :
    ReachIdentity.guard tt [(true, false); (true, true)] = [(false, false); (true, true)].
  Proof. vm_compute. reflexivity. Qed.

End ReducedIdentityTests.

(* The old product-law client awaits conversion to module laws.
Example identity_product_laws :
  value_laws reach_product unit_sem (product_gamma bool_gamma bool_gamma).
Proof.
  apply product_laws; try exact reach_value_laws. intros p c H. exact H.
Qed.


*)

(** * Join *)

(** Facts with a weak join, which always gives the top fact. *)
Inductive weak_fact : Type := WBot | WPoint | WTop.
Module WeakJoin.
  Definition bot := WBot.
  Definition join (_ _ : weak_fact) := WTop.
End WeakJoin.
Module OrderedJoin.
  Definition bot := 0%nat.
  Definition join (a b : nat) := (2 * a + b + 1)%nat.
End OrderedJoin.

(** The left fold of join over a list, starting from the first element. *)
Definition join_all {A} (bot : A) (join : A -> A -> A) (xs : list A) :=
  match xs with
  | [] => bot
  | x :: rest => fold_left join rest x
  end.

Module JoinTests.

  (** Joining a single weak fact gives that fact. *)
  Example weak_singleton_keeps_point :
    join_all WeakJoin.bot WeakJoin.join [WPoint] = WPoint.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining no weak facts gives the bottom fact. *)
  Example weak_empty_is_bottom :
    join_all WeakJoin.bot WeakJoin.join [] = WBot.
  Proof. vm_compute. reflexivity. Qed.

  (** The ordered join folds from the left over its operands. *)
  Example ordered_join_folds_from_left :
    join_all OrderedJoin.bot OrderedJoin.join [1; 2; 3] = 14.
  Proof. vm_compute. reflexivity. Qed.

  (** The ordered join depends on the order of its operands. *)
  Example ordered_join_depends_on_order :
    join_all OrderedJoin.bot OrderedJoin.join [3; 2; 1] = 20.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining product facts componentwise gives the pair of joins. *)
  Example product_join_is_componentwise :
    join_all ReachProduct.bot ReachProduct.join [(false, true); (true, false)] =
      (true, true).
  Proof. vm_compute. reflexivity. Qed.

End JoinTests.
