(** * Relational environment observations

    Product states run both component updates and refine evaluated values by numeric ranges.
    For example, an integer constant has the same finite range in both components.
    Builds on: RelEnv, Env and interval operations. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import Product.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval Thresholds ZLang.
From Galois.States Require Import Env.
From Galois.Relational Require Import LinForm RelEnv.
Import List.ListNotations.
Local Open Scope Z_scope.

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
  Definition atoms_of (_ : ZLangCode.guard) (_ : list (term ZLangCode.op nat)) : list (atom nat) := [].
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

Definition three : term ZLangCode.op nat := Node (ZConst 3) [].
Example evaluates_constant : Composed.eval three Composed.top = I (Fin 3) (Fin 3).
Proof. vm_compute. reflexivity. Qed.
Example updates_both_components :
  Composed.assign 1%nat three Composed.top =
    (Numeric.assign 1%nat three Numeric.top, State.assign 1%nat three State.top).
Proof. vm_compute. reflexivity. Qed.
Example assigned_variable_evaluates :
  Composed.eval (Leaf 1%nat) (Composed.assign 1%nat three Composed.top) = I (Fin 3) (Fin 3).
Proof. vm_compute. reflexivity. Qed.

Example narrow_returns_bottom_candidate :
  Composed.narrow Composed.top (Numeric.bot, State.top) = (Numeric.bot, State.top).
Proof. vm_compute. reflexivity. Qed.
