(** * Generic term fixtures

    Terms support nested operand lists and pointwise refinements.
    For example, refining a leaf meets its current fact with the target.
    Builds on: Env and ValueOpenTest.

    Groups:
    - [EvalTests] Evaluating terms with nested operands.
    - [RefineTests] Refining a leaf from an assumed value.
    - [TraceTests] Threading targets and environments through the operands of a node. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope nat_scope.

(** * Fixtures *)

Module NatMap := TrieMapCode NatKeyCode.

(** A language with one operator, no literals and a unit value. *)
Module UnitLanguage.
  Definition op := unit.
  Definition guard := unit.
  Definition val := unit.
  Definition eval (_ : op) (_ : list val) := Some tt.
  Definition literal (_ : op) : option Z := None.
End UnitLanguage.

(** Reachability values: the booleans, where true means reachable. *)
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

(** The target sequence that a trace domain reads back from its backward step. *)
Module Type TARGETS.
  Parameter values : list (list nat).
End TARGETS.

(** A trace domain whose values are lists of naturals and whose backward step
    returns the targets of the functor argument. *)
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

(** Targets listed in forward order: [1] then [2]. *)
Module ForwardTargets.
  Definition values := [[1]; [2]].
End ForwardTargets.

(** Targets listed in reverse order: [2] then [1]. *)
Module ReverseTargets.
  Definition values := [[2]; [1]].
End ReverseTargets.
Module ForwardTrace := TraceCode ForwardTargets.
Module ReverseTrace := TraceCode ReverseTargets.
Module ForwardEnv := EnvCode NatKeyCode NatMap UnitLanguage ForwardTrace.
Module ReverseEnv := EnvCode NatKeyCode NatMap UnitLanguage ReverseTrace.

Module EvalTests.

  (** A nested term evaluates to the top value when every leaf is reachable. *)
  Example nested_term_evaluates_to_top :
    ReachEnv.eval (Node tt [Leaf 0; Node tt [Leaf 1]]) ReachEnv.top = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A node with no operands evaluates to none when the language gives no result. *)
  Example operandless_node_without_result_is_none :
    eval_term (fun (_ : unit) (_ : list unit) => None)
      (fun _ : nat => tt) (Node tt []) = None.
  Proof. vm_compute. reflexivity. Qed.

End EvalTests.

Module RefineTests.

  (** A leaf refined by a false assumption reads as false. *)
  Definition refined_leaf :=
    ReachEnv.refine false (ReachEnv.annotate NatMap.empty (Leaf 0)) NatMap.empty.

  (** The leaf that the assumption refines reads as the assumed value. *)
  Example assumed_leaf_reads_false : ReachEnv.read refined_leaf 0 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A leaf that the assumption does not mention keeps the top value. *)
  Example other_leaf_keeps_top : ReachEnv.read refined_leaf 1 = true.
  Proof. vm_compute. reflexivity. Qed.

End RefineTests.

Module TraceTests.

  (** The operands of a node are visited from left to right. *)
  Definition forward_trace seed :=
    let m := NatMap.set 0 seed NatMap.empty in
    ForwardEnv.read (ForwardEnv.refine []
      (ForwardEnv.annotate m (Node tt [Leaf 0; Leaf 0])) m) 0.

  (** The targets of a node with no seed come out in forward order. *)
  Example operands_thread_left_to_right : forward_trace [] = [1; 2].
  Proof. vm_compute. reflexivity. Qed.

  (** A seed that the environment already holds stays in front of the new targets. *)
  Example earlier_bindings_are_kept : forward_trace [9] = [9; 1; 2].
  Proof. vm_compute. reflexivity. Qed.

  (** The reversed target list is observed in its own order. *)
  Definition reverse_trace :=
    ReverseEnv.read (ReverseEnv.refine []
      (ReverseEnv.annotate NatMap.empty (Node tt [Leaf 0; Leaf 0])) NatMap.empty) 0.
  Example reversed_targets_are_observed_in_order : reverse_trace = [2; 1].
  Proof. vm_compute. reflexivity. Qed.

End TraceTests.
