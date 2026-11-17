(** * Finite environment action observations

    A finite interval vocabulary distinguishes assignment, havoc and guard precision.
    For example, havoc changes a bounded fact to Any.

    Groups:
    - Terms: the term evaluator gives the operations' values, or None for an undefined operation.
    - Actions: assignment keeps a fact, havoc forgets it, and the empty list keeps the state.
    - Guards: an impossible guard is bottom under the precise state domain, and not under the coarse one.
    - Candidates: the hand candidate for the two-edge CFG is accepted, and a smaller one is rejected.

    Builds on: Framework.Interp and Domains.LangSig. *)

From Stdlib Require Import List Bool ZArith.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query Check.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import InterpSig Interp.
Import List.ListNotations.

(** * Fixtures *)

(** Operations of the finite language: a constant, an addition, and a less-than test. *)
Inductive op :=
  | Const (z : Z)
  | Add
  | Lt.

(** Guards of the finite language: below three, and never. *)
Inductive guard :=
  | Below3
  | Never.

(** Facts of the finite vocabulary: dead, the constants 0 to 3, and any value. *)
Inductive fact :=
  | Dead
  | U0
  | U1
  | U2
  | U3
  | Any.

(** The finite language, whose values are integers. *)
Module Lang <: LANG_OPS.
  Definition op := op.
  Definition guard := guard.
  Definition val := Z.
  Definition eval k cs :=
    match k, cs with
    | Const z, [] => Some z
    | Add, [x; y] => Some (x + y)%Z
    | Lt, [x; y] => Some (if (x <? y)%Z then 1%Z else 0%Z)
    | _, _ => None
    end.
  Definition literal k := match k with Const z => Some z | _ => None end.
End Lang.

(** The finite lattice of facts, ordered as a flat chain of constants below Any. *)
Module V <: VALUE_DOMAIN_OPS Lang.
  Definition t := fact.
  Definition leb a b :=
    match a, b with
    | Dead, _ | _, Any => true
    | U0, U0 | U0, U1 | U0, U2 | U0, U3 => true
    | U1, U1 | U1, U2 | U1, U3 => true
    | U2, U2 | U2, U3 | U3, U3 => true
    | _, _ => false
    end.
  Definition bot := Dead.
  Definition is_bot a := match a with Dead => true | _ => false end.
  Definition top := Any.
  Definition join a b := if leb a b then b else a.
  Definition meet a b := if leb a b then a else b.
  Definition wparam := unit.
  Definition widen (_ : unit) := join.
  Definition narrow (a _ : t) := a.
  Definition constant z :=
    if (z =? 0)%Z then U0 else if (z =? 1)%Z then U1 else
    if (z =? 2)%Z then U2 else if (z =? 3)%Z then U3 else Any.
  Definition plus a b :=
    match a, b with
    | U0, f | f, U0 => f
    | U1, U1 => U2
    | U1, U2 | U2, U1 => U3
    | _, _ => Any
    end.
  Definition forward k fs :=
    match k, fs with
    | Const z, [] => constant z
    | Add, [a; b] => plus a b
    | Lt, _ => U1
    | _, _ => Any
    end.
  Definition backward (_ : op) (_ : t) (fs : list t) := fs.
  Definition guard (_ : guard) (fs : list t) := fs.
End V.

(** The precise state domain, whose guards and assignments use the value domain. *)
Module D <: STATE_DOMAIN_OPS UnitKeyCode Lang V.
  Definition t := V.t.
  Definition leb := V.leb.
  Definition bot := V.bot.
  Definition is_bot := V.is_bot.
  Definition top := V.top.
  Definition join := V.join.
  Definition meet := V.meet.
  Definition wparam := V.wparam.
  Definition widen := V.widen.
  Definition narrow := V.narrow.
  Definition eval e a :=
    match eval_term (fun k fs => Some (V.forward k fs)) (fun _ : unit => a) e with
    | Some value => value
    | None => Any
    end.
  Definition assign (_ : unit) e a := match a with Dead => Dead | _ => eval e a end.
  Definition havoc (_ : unit) a := match a with Dead => Dead | _ => Any end.
  Definition assume g (ts : list (term op unit)) a :=
    match g, ts, a with
    | Never, _, _ => Dead
    | Below3, [Leaf _], U3 => U2
    | _, _, _ => a
    end.
End D.

(** The coarse state domain, which keeps every state under an assumption. *)
Module Coarse <: STATE_DOMAIN_OPS UnitKeyCode Lang V.
  Definition t := D.t.
  Definition leb := D.leb.
  Definition bot := D.bot.
  Definition is_bot := D.is_bot.
  Definition top := D.top.
  Definition join := D.join.
  Definition meet := D.meet.
  Definition wparam := D.wparam.
  Definition widen := D.widen.
  Definition narrow := D.narrow.
  Definition assign := D.assign.
  Definition havoc := D.havoc.
  Definition eval := D.eval.
  Definition assume (_ : guard) (_ : list (term op unit)) (a : t) := a.
End Coarse.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := list (action op guard unit). End Edge.

(** A CFG with one edge from false to true and no edges of its own. *)
Module Cfg <: CFG_OPS Prog BoolKeyCode Edge.
  Definition entries (_ : unit) := [false].
  Definition edges (_ : unit) : list Edge.t := [].
  Definition src (_ : unit) (_ : Edge.t) := false.
  Definition dst (_ : unit) (_ : Edge.t) := true.
End Cfg.

(** Each edge is its own list of actions. *)
Module Actions <: ACTIONS_OPS Prog Edge UnitKeyCode Lang.
  Definition actions (_ : unit) (e : Edge.t) := e.
End Actions.

Module S := InterpCode Prog BoolKeyCode Edge Cfg UnitKeyCode Lang V Actions D.

(** * Terms *)

Module TermTests.

  (** An undefined operation has no value. *)
  Example undefined_operation_is_none :
    eval_term Lang.eval (fun _ : unit => 2%Z) (Node Add []) = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A constant node with no operands evaluates to its value, whatever the environment. *)
  Example constant_node_evaluates :
    eval_term Lang.eval (fun _ : unit => 99%Z) (Node (Const 2) []) = Some 2%Z.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A nested sum of the leaf fact U2 and the constant 1 gives U3. *)
  Example nested_term_evaluates_to_u3 :
    D.eval (Node Add [Leaf tt; Node (Const 1) []]) U2 = U3.
  Proof.
    vm_compute; reflexivity.
  Qed.

End TermTests.

(** * Actions *)

Module ActionTests.

  (** Runs the actions on the state, and gives the state after them, or Dead when they do not return. *)
  Definition apply_actions acts a :=
    match S.resume tt acts a with Ret out => out | _ => Dead end.

  (** Assigning the constant 0 to a state U3 gives U0. *)
  Example assign_constant_zero :
    apply_actions [Assign tt (Node (Const 0) [])] U3 = U0.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Havoc on the state U3 gives Any. *)
  Example havoc_gives_any :
    apply_actions [Havoc tt] U3 = Any.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Havoc does not keep the bound of U3, so the result is not below U0. *)
  Example havoc_loses_bound :
    V.leb (apply_actions [Havoc tt] U3) U0 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** No actions keep the state U3. *)
  Example empty_actions_keep_fact :
    apply_actions [] U3 = U3.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ActionTests.

(** * Guards *)

Module GuardTests.

  (** Under the precise domain, the impossible guard Never makes the state Dead. *)
  Example precise_impossible_guard_is_bottom :
    D.assume Never [Leaf tt] U3 = Dead.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Under the coarse domain, the impossible guard Never leaves the state non-bottom. *)
  Example coarse_impossible_guard_not_bottom :
    D.is_bot (Coarse.assume Never [Leaf tt] U3) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End GuardTests.

(** * Candidates *)

Module CandidateTests.

  (** The two-edge CFG, whose edge false assigns 0 and whose edge true assumes below 3 and adds 1. *)
  Module CounterEdge <: TYPE. Definition t := bool. End CounterEdge.

  Module CounterCfg <: CFG_OPS Prog BoolKeyCode CounterEdge.
    Definition entries (_ : unit) := [false].
    Definition edges (_ : unit) := [false; true].
    Definition src (_ : unit) (e : bool) := e.
    Definition dst (_ : unit) (_ : bool) := true.
  End CounterCfg.

  Module CounterActions <: ACTIONS_OPS Prog CounterEdge UnitKeyCode Lang.
    Definition actions (_ : unit) (e : bool) : list (action op guard unit) :=
      if e then [Assume Below3 [Leaf tt]; Assign tt (Node Add [Leaf tt; Node (Const 1) []])]
      else [Assign tt (Node (Const 0) [])].
  End CounterActions.

  Module CS := InterpCode Prog BoolKeyCode CounterEdge CounterCfg UnitKeyCode Lang V CounterActions D.
  Module C := CheckCode D CS.

  (** The candidate that gives the entry Any and the other edge the fact a. *)
  Definition candidate a := PTrieCode.set (BoolKeyCode.encode false) (false, Any)
    (PTrieCode.set (BoolKeyCode.encode true) (true, a) PTrieCode.empty).

  (** The candidate with U3 on the second edge satisfies the checker. *)
  Example hand_candidate_accepted : C.check tt (candidate U3) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The candidate with U2 on the second edge is too small and is rejected. *)
  Example too_small_candidate_rejected : C.check tt (candidate U2) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CandidateTests.
