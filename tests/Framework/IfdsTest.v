(** * Balanced IFDS observations

    A call, internal edge and matching return exercise path-edge constraints.
    For example, an empty candidate misses an identity rule.
    Builds on: Framework.Ifds and Fixpoint.Query. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig Ifds.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Fact := OptionKeyCode UnitKeyCode.
Module Graph <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) := [0; 1; 2].
  Definition src (_ : unit) (e : nat) := e.
  Definition dst (_ : unit) (e : nat) := S e.
End Graph.
Module Icfg <: ICFG_OPS Prog NatKeyCode Edge Graph NatKeyCode.
  Definition kind (_ : unit) e := match e with 0 => Call 7 | 2 => Return 7 | _ => Intra end.
End Icfg.
Module Flow <: FLOW_FUN_OPS Prog NatKeyCode Edge Fact.
  Definition facts (_ : unit) := [None; Some tt].
  Definition flow (_ : unit) e d := match e, d with
    | 1, None => [None; Some tt]
    | _, _ => [d]
    end.
  Definition seeds (_ : unit) := [(0, None); (0, Some tt)].
End Flow.
Definition prepared_rules := Eval vm_compute in
  path_rules NatKeyCode.eqb (Icfg.kind tt) (Graph.dst tt) (Flow.facts tt) (Flow.flow tt)
    (Flow.seeds tt) (Graph.edges tt).
Module Rules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
  Definition rules (_ : unit) := prepared_rules.
End Rules.
Module A := IfdsCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact Flow Rules IfdsLatticeCode.
Definition look (k : A.key) :=
  existsb (A.key_eqb k)
    [(None, (0, None)); (Some tt, (0, Some tt));
     (None, (1, None)); (Some tt, (1, Some tt));
     (None, (2, None)); (None, (2, Some tt)); (Some tt, (2, Some tt));
     (None, (3, None)); (None, (3, Some tt)); (Some tt, (3, Some tt))].

Module UnsupportedGraph <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) := [0; 1].
  Definition src (_ : unit) (e : nat) := e.
  Definition dst (_ : unit) (e : nat) := S e.
End UnsupportedGraph.
Module UnsupportedIcfg <: ICFG_OPS Prog NatKeyCode Edge UnsupportedGraph NatKeyCode.
  Definition kind (_ : unit) (_ : nat) : edge_kind nat := Intra.
End UnsupportedIcfg.
Module UnsupportedFlow <: FLOW_FUN_OPS Prog NatKeyCode Edge Fact.
  Definition facts (_ : unit) : list (option unit) := [None].
  Definition flow (_ : unit) e d := match e, d with
    | 0, None => [Some tt]
    | 1, Some _ => [d]
    | _, _ => []
    end.
  Definition seeds (_ : unit) : list (nat * option unit) := [(0, None)].
End UnsupportedFlow.
Definition unsupported_rules := Eval vm_compute in
  path_rules NatKeyCode.eqb (UnsupportedIcfg.kind tt) (UnsupportedGraph.dst tt)
    (UnsupportedFlow.facts tt) (UnsupportedFlow.flow tt) (UnsupportedFlow.seeds tt)
    (UnsupportedGraph.edges tt).
Module UnsupportedRules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
  Definition rules (_ : unit) := unsupported_rules.
End UnsupportedRules.
Module Unsupported := IfdsCode Prog NatKeyCode Edge UnsupportedGraph NatKeyCode UnsupportedIcfg
  Fact UnsupportedFlow UnsupportedRules IfdsLatticeCode.
Definition unsupported_lookup k :=
  Unsupported.key_eqb k (None, (0, None)) || Unsupported.key_eqb k (None, (1, Some tt)).

Example unsupported_jump_passes_enumerated_checker : forallb (fun r =>
  row_ok IfdsLatticeCode.leb unsupported_lookup (Unsupported.target tt r)
    (eval_query (Unsupported.resume tt) unsupported_lookup
      (S (length (Unsupported.deps tt r))) (Unsupported.start tt r)))
  (Unsupported.rows tt) = true.
Proof. vm_compute; reflexivity. Qed.

Example unsupported_seed_rejected :
  existsb (Fact.eqb (Some tt)) (UnsupportedFlow.facts tt) = false.
Proof. vm_compute; reflexivity. Qed.

Example zero_seed_supported : existsb (Fact.eqb None) (UnsupportedFlow.facts tt) = true.
Proof. vm_compute; reflexivity. Qed.
