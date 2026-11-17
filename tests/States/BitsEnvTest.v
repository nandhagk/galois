(** * Word term environment observations

    Bit-vector terms run through the tagged constant domain in an environment.
    For example, a nested arithmetic term evaluates to its wrapped singleton.
    Builds on: Env, BitsLang and Tagged.

    Groups:
    - [AssumeTests] Guards that refine the variables of a state.
    - [EvalTests] Evaluating a term over an abstract state.
    - [RefineTests] Refining a variable from the result of a term.
    - [EqualTests] Guards on equality with a constant.
    - [DifferTests] Guards on disequality with a constant. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import LangSig WordSig BitsLang Const ConstSig Tagged Harness.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Vars := TrieMapCode NatKeyCode.
Module Payload := ConstWordCode WordLanguageCode.
Module Table := ConstWordTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
Module State := EnvCode NatKeyCode Vars BitsLangCode Domain.

(** A tagged constant with width w and number z. *)
Definition p (w : positive) (z : Z) := TVal w (FVal z).

(** A state that binds variables 0 and 1 to the 32-bit value 1. *)
Definition input := Reached (Vars.set 1%nat (p 32 1) (Vars.set 0%nat (p 32 1) Vars.empty)).

(** The sum of variables 0 and 1. *)
Definition add_terms := Node (BOp bvadd) [Leaf 0%nat; Leaf 1%nat].

(** The value of variable x in a state, or bottom in the unreached state. *)
Definition observe x s := match s with Unreached => TBot | Reached m => State.read m x end.

(** A state that binds variable 0 to the 32-bit value z. *)
Definition one_value z := Reached (Vars.set 0%nat (p 32 z) Vars.empty).

Module AssumeTests.

  (** The state in which the sum of the two variables is true. *)
  Definition sum_true_state := State.assume (BTruth true) [add_terms] input.

  (** Assuming that a sum is true keeps the first operand at its value. *)
  Example sum_guard_keeps_first_operand : observe 0%nat sum_true_state = p 32 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming that a sum is true keeps the second operand at its value. *)
  Example sum_guard_keeps_second_operand : observe 1%nat sum_true_state = p 32 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The state in which the sum of the two variables is false. *)
  Definition sum_false_state := State.assume (BTruth false) [add_terms] input.

  (** Assuming that a sum is false keeps the first operand at its value. *)
  Example false_sum_guard_keeps_first_operand : observe 0%nat sum_false_state = p 32 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming that a sum is false keeps the second operand at its value. *)
  Example false_sum_guard_keeps_second_operand : observe 1%nat sum_false_state = p 32 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A guard list that is empty leaves the top state unchanged. *)
  Example empty_guard_list_keeps_state : State.assume (BTruth true) [] State.top = State.top.
  Proof. vm_compute. reflexivity. Qed.

  (** A truncation to one bit, assumed false, keeps the 32-bit value that it truncates. *)
  Definition truncation_term := Node (BOp (bvtrunc 1%positive)) [Leaf 0%nat].
  Example truncated_guard_keeps_value :
    observe 0%nat (State.assume (BTruth false) [truncation_term] (one_value 2)) = p 32 2.
  Proof. vm_compute. reflexivity. Qed.

  (** The state in which variable 1 is 2 and variable 0 is 1. *)
  Definition ordered_state :=
    Reached (Vars.set 1%nat (p 32 2) (Vars.set 0%nat (p 32 1) Vars.empty)).

  (** The state after assuming that variable 0 is less than variable 1. *)
  Definition less_than_state :=
    State.assume (BTruth true) [Node (BOp bvult) [Leaf 0%nat; Leaf 1%nat]] ordered_state.

  (** The smaller operand of a true less-than guard keeps its value. *)
  Example less_than_keeps_smaller_operand : observe 0%nat less_than_state = p 32 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The larger operand of a true less-than guard keeps its value. *)
  Example less_than_keeps_larger_operand : observe 1%nat less_than_state = p 32 2.
  Proof. vm_compute. reflexivity. Qed.

End AssumeTests.

Module EvalTests.

  (** A nested term evaluates to its wrapped singleton over an abstract state. *)
  Definition nested :=
    Node (BOp bvadd) [Node (BOp bvmul) [Leaf 0%nat; Node (BConst 8%positive 3) []];
                       Node (BConst 8%positive 250) []].
  Example nested_term_evaluates_abstractly :
    State.eval nested (Reached (Vars.set 0%nat (p 8 5) Vars.empty)) = p 8 9.
  Proof. vm_compute. reflexivity. Qed.

End EvalTests.

Module RefineTests.

  (** The term that adds 3 to variable 0. *)
  Definition add_three :=
    Node (BOp bvadd) [Leaf 0%nat; Node (BConst 8%positive 3) []].

  (** Refining the sum to 7 gives variable 0 the value 4. *)
  Example leaf_refined_through_addition :
    let m := Vars.set 0%nat (TVal 8%positive FTop) Vars.empty in
    State.read (State.refine (p 8 7) (State.annotate m add_three) m) 0%nat = p 8 4.
  Proof. vm_compute. reflexivity. Qed.

End RefineTests.

Module EqualTests.

  (** The term that tests whether variable 0 equals 7, as 32-bit words. *)
  Definition equal_seven :=
    Node (BOp bveq) [Leaf 0%nat; Node (BConst 32%positive 7) []].

  (** The term that tests whether variable 0 equals 1, as one-bit words. *)
  Definition equal_one := Node (BOp bveq) [Leaf 0%nat; Node (BConst 1%positive 1) []].

  (** A state that binds variable 0 to an unknown value. *)
  Definition unknown_input : State.t := Reached (Vars.set 0%nat TAny Vars.empty).

  (** A true equality guard keeps a matching value at its value. *)
  Example equal_assumption_keeps_matching_value :
    observe 0%nat (State.assume (BTruth true) [equal_seven] (one_value 7)) = p 32 7.
  Proof. vm_compute. reflexivity. Qed.

  (** A true equality guard leaves a value that differs from the constant unchanged. *)
  Example equal_assumption_keeps_other_value :
    observe 0%nat (State.assume (BTruth true) [equal_seven] (one_value 6)) = p 32 6.
  Proof. vm_compute. reflexivity. Qed.

  (** A true equality guard leaves an unknown value unknown. *)
  Example equal_assumption_keeps_unknown_value :
    observe 0%nat (State.assume (BTruth true) [equal_one] unknown_input) = TAny.
  Proof. vm_compute. reflexivity. Qed.

End EqualTests.

Module DifferTests.

  (** A one-bit state that binds variable 0 to the value z. *)
  Definition one_bit z := Reached (Vars.set 0%nat (p 1 z) Vars.empty).

  (** The term that tests whether variable 0 differs from 1, as one-bit words. *)
  Definition differs_one := Node (BOp bvne) [Leaf 0%nat; Node (BConst 1%positive 1) []].

  (** The term that tests whether variable 0 differs from 0, as one-bit words. *)
  Definition differs_zero := Node (BOp bvne) [Leaf 0%nat; Node (BConst 1%positive 0) []].

  (** The term that tests whether variable 0 differs from 7, as 32-bit words. *)
  Definition differs_seven :=
    Node (BOp bvne) [Leaf 0%nat; Node (BConst 32%positive 7) []].

  (** A true disequality guard keeps the value that differs from the constant. *)
  Example differ_from_one_keeps_zero :
    observe 0%nat (State.assume (BTruth true) [differs_one] (one_bit 0)) = p 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A true disequality guard leaves the constant value at its value. *)
  Example differ_from_one_keeps_one :
    observe 0%nat (State.assume (BTruth true) [differs_one] (one_bit 1)) = p 1 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A true disequality guard keeps the value 1 when it differs from 0. *)
  Example differ_from_zero_keeps_one :
    observe 0%nat (State.assume (BTruth true) [differs_zero] (one_bit 1)) = p 1 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A disequality of different widths keeps the value of the one-bit operand. *)
  Example mixed_width_differ_keeps_value :
    observe 0%nat (State.assume (BTruth true) [differs_seven] (one_bit 1)) = p 1 1.
  Proof. vm_compute. reflexivity. Qed.

End DifferTests.
