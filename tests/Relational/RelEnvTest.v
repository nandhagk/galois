(** * Relational environment observations

    Product states run both component updates and refine evaluated values by numeric ranges.
    For example, an integer constant has the same finite range in both components.
    The groups are:
    - Evaluation, which checks the value of an evaluated term.
    - Assignment, which checks both components after an update.
    - Narrowing, which checks that a bottom candidate is kept.
    Builds on: RelEnv, Env and interval operations. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import Product.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval Thresholds ZLang.
From Galois.States Require Import Env.
From Galois.Relational Require Import LinForm RelEnv.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module NatMap := TrieMapCode NatKeyCode.
Module Values := IntervalCode ZLangCode ThresholdsCode.
Module State := EnvCode NatKeyCode NatMap ZLangCode Values.

Module Linear.
  Definition lin_of (e : term ZLangCode.op nat) : option (lin nat * wrapr) :=
    match e with
    | Leaf x => Some (Lin nat [(x, 1)] 0, NoWrap)
    | Node (ZConst z) [] => Some (Lin nat [] z, NoWrap)
    | _ => None
    end.
  Definition atoms_of (_ : ZLangCode.guard) (_ : list (term ZLangCode.op nat))
      : list (atom nat) := [].
End Linear.

Module Numeric.
  Include State.
  Definition range (e : term ZLangCode.op nat) (s : t) : bnd * bnd :=
    match eval e s with
    | I lo hi => (lo, hi)
    | IBot => (NegInf, PosInf)
    end.
End Numeric.
Module Refinement.
  Definition refine_range (lo hi : bnd) (v : Values.t) := Values.meet (I lo hi) v.
End Refinement.
Module Pair := ProductCode Numeric State.
Module Composed := RelEnvCode NatKeyCode ZLangCode Values Linear Numeric State Refinement Pair.

(** The constant term 3, evaluated in both components of a product state. *)
Definition three : term ZLangCode.op nat := Node (ZConst 3) [].

(** * Evaluation *)

Module EvalTests.

  (** Evaluating the constant 3 on the unconstrained state gives the singleton interval 3. *)
  Example constant_is_its_own_range :
    Composed.eval three Composed.top = I (Fin 3) (Fin 3).
  Proof.
    vm_compute. reflexivity.
  Qed.

End EvalTests.

(** * Assignment *)

Module AssignTests.

  (** Assigning a constant updates the numeric and the environment component together. *)
  Example assign_updates_both_components :
    Composed.assign 1%nat three Composed.top =
      (Numeric.assign 1%nat three Numeric.top, State.assign 1%nat three State.top).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A variable read after its assignment evaluates to the assigned constant. *)
  Example assigned_variable_reads_back_its_value :
    Composed.eval (Leaf 1%nat) (Composed.assign 1%nat three Composed.top) =
      I (Fin 3) (Fin 3).
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssignTests.

(** * Narrowing *)

Module NarrowTests.

  (** Narrowing a top state by a bottom numeric candidate keeps that bottom candidate. *)
  Example keeps_bottom_numeric_candidate :
    Composed.narrow Composed.top (Numeric.bot, State.top) = (Numeric.bot, State.top).
  Proof.
    vm_compute. reflexivity.
  Qed.

End NarrowTests.
