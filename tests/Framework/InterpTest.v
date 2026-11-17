(** * Ordered interpreter actions

    Assignment and guards run in the order supplied by an edge, and an unreachable state stays unreachable.
    For example, assigning two before testing the guard keeps the state reachable.

    Groups:
    - Actions: the order of the actions on an edge decides whether the guard rejects the state.
    - Havoc: havoc on an unreachable state leaves it unreachable.

    Builds on: Framework.Interp and States.Env. *)

From Stdlib Require Import List Bool ZArith PArith.
From Galois.Base Require Import KeySig Key Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ThresholdsSig Thresholds ZLang Interval.
From Galois.States Require Import Env.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import InterpSig Interp.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := bool. End Edge.

(** A CFG with one entry, whose two edges both run from node 1 to node 2. *)
Module Cfg <: CFG_OPS Prog PosKeyCode Edge.
  Definition entries (_ : unit) := [1%positive].
  Definition edges (_ : unit) := [true; false].
  Definition src (_ : unit) (_ : bool) := 1%positive.
  Definition dst (_ : unit) (_ : bool) := 2%positive.
End Cfg.

(** The edge true assigns x := 2 and then assumes x > 1, and the edge false does the reverse. *)
Module Actions <: ACTIONS_OPS Prog Edge PosKeyCode ZLangCode.
  Definition actions (_ : unit) (forward : bool) : list (action zview zguardview positive) :=
    let assign := Assign 1%positive (Node (ZConst 2) []) in
    let guard := Assume (ZGuardCmp Gt) [Leaf 1%positive; Node (ZConst 1) []] in
    if forward then [assign; guard] else [guard; assign].
End Actions.

Module M := TrieMapCode PosKeyCode.
Module V := IntervalCode ZLangCode ThresholdsCode.
Module D := EnvCode PosKeyCode M ZLangCode V.
Module S := InterpCode Prog PosKeyCode Edge Cfg PosKeyCode ZLangCode V Actions D.

(** The environment that assigns 0 to the variable 1. *)
Definition initial := D.assign 1%positive (Node (ZConst 0) []) D.top.

(** * Actions *)

Module ActionsTests.

  (** Running the assignment before the guard keeps x at 2, so the guard passes. *)
  Example assignment_then_guard_reachable :
    match S.resume tt true initial with
    | Ret s => D.eval (Leaf 1%positive) s
    | _ => IBot
    end = I (Fin 2) (Fin 2).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Running the guard before the assignment rejects the state. *)
  Example guard_then_assignment_rejects :
    match S.resume tt false initial with
    | Ret s => D.is_bot s
    | _ => false
    end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ActionsTests.

(** * Havoc *)

Module HavocTests.

  (** Havoc on the bottom environment leaves it at bottom. *)
  Example havoc_keeps_bottom : D.havoc 1%positive D.bot = D.bot.
  Proof.
    vm_compute; reflexivity.
  Qed.

End HavocTests.
