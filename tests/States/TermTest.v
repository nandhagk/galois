(** * Generic term fixtures

    Terms support nested operand lists and pointwise refinements.
    For example, refining a leaf meets its current fact with the target.
    Builds on: Env and ValueOpenTest. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope nat_scope.

Module NatMap := TrieMapCode NatKeyCode.
Module UnitLanguage.
  Definition op := unit.
  Definition guard := unit.
  Definition val := unit.
  Definition eval (_ : op) (_ : list val) := Some tt.
  Definition literal (_ : op) : option Z := None.
End UnitLanguage.

Module ReachCode.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition top := true.
  Definition meet := andb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
  Definition forward (_ : unit) (_ : list bool) := true.
  Definition backward (_ : unit) (_ : bool) (xs : list bool) := xs.
  Definition guard (_ : unit) (xs : list bool) := xs.
End ReachCode.
Module ReachEnv := EnvCode NatKeyCode NatMap UnitLanguage ReachCode.

Example nested_term_evaluation :
  ReachEnv.eval (Node tt [Leaf 0; Node tt [Leaf 1]]) ReachEnv.top = true.
Proof. vm_compute. reflexivity. Qed.

Definition refined_leaf :=
  ReachEnv.refine false (ReachEnv.annotate NatMap.empty (Leaf 0)) NatMap.empty.

Example leaf_assumption_rejects : ReachEnv.read refined_leaf 0 = false.
Proof. vm_compute. reflexivity. Qed.

Example leaf_assumption_keeps_other : ReachEnv.read refined_leaf 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example empty_node_evaluation :
  eval_term (fun (_ : unit) (_ : list unit) => None)
    (fun _ : nat => tt) (Node tt []) = None.
Proof. vm_compute. reflexivity. Qed.


Module Type TARGETS.
  Parameter values : list (list nat).
End TARGETS.

Module TraceCode (T : TARGETS).
  Definition t := list nat.
  Definition leb (_ _ : t) := true.
  Definition bot : t := [].
  Definition is_bot (_ : t) := false.
  Definition join (a _ : t) := a.
  Definition top : t := [].
  Definition meet := @app nat.
  Definition wparam := unit.
  Definition widen (_ : unit) (a _ : t) := a.
  Definition narrow (a _ : t) := a.
  Definition forward (_ : unit) (_ : list t) : t := [].
  Definition backward (_ : unit) (_ : t) (_ : list t) := T.values.
  Definition guard (_ : unit) (xs : list t) := xs.
End TraceCode.

Module ForwardTargets.
  Definition values := [[1]; [2]].
End ForwardTargets.
Module ReverseTargets.
  Definition values := [[2]; [1]].
End ReverseTargets.
Module ForwardTrace := TraceCode ForwardTargets.
Module ReverseTrace := TraceCode ReverseTargets.
Module ForwardEnv := EnvCode NatKeyCode NatMap UnitLanguage ForwardTrace.
Module ReverseEnv := EnvCode NatKeyCode NatMap UnitLanguage ReverseTrace.

Definition forward_trace seed :=
  let m := NatMap.set 0 seed NatMap.empty in
  ForwardEnv.read (ForwardEnv.refine []
    (ForwardEnv.annotate m (Node tt [Leaf 0; Leaf 0])) m) 0.
Definition reverse_trace :=
  ReverseEnv.read (ReverseEnv.refine []
    (ReverseEnv.annotate NatMap.empty (Node tt [Leaf 0; Leaf 0])) NatMap.empty) 0.

Example node_assumptions_thread_left_to_right : forward_trace [] = [1; 2].
Proof. vm_compute. reflexivity. Qed.
Example node_assumptions_retain_earlier_environment : forward_trace [9] = [9; 1; 2].
Proof. vm_compute. reflexivity. Qed.
Example reversed_node_targets_are_observable : reverse_trace = [2; 1].
Proof. vm_compute. reflexivity. Qed.
