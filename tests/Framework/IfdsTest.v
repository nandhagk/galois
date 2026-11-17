(** * Balanced IFDS observations

    A call, internal edge and matching return exercise path-edge constraints.
    For example, an empty candidate misses an identity rule.

    Groups:
    - Prepared: the prepared path rules agree with the reference rules on the call graph.
    - Unsupported: an unsupported jump still passes the enumerated checker, and its seeds are checked.
    - Indexed: duplicated calls, returns and facts keep their occurrence order.

    Builds on: Framework.Ifds and Fixpoint.Query. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig Ifds.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.

(** Facts are options of unit, so the facts are None and Some tt. *)
Module Fact := OptionKeyCode UnitKeyCode.

(** A chain of three edges from node 0 to node 3, with the edge 0 a call and the edge 2 a return. *)
Module Graph <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) := [0; 1; 2].
  Definition src (_ : unit) (e : nat) := e.
  Definition dst (_ : unit) (e : nat) := S e.
End Graph.

(** The edge kinds of Graph: a call at edge 0, a return at edge 2, and internal edges otherwise. *)
Module Icfg <: ICFG_OPS Prog NatKeyCode Edge Graph NatKeyCode.
  Definition kind (_ : unit) e := match e with 0 => Call 7 | 2 => Return 7 | _ => Intra end.
End Icfg.

(** Flow where the edge 1 generates the fact Some tt from None, and every other fact is kept. *)
Module Flow <: FLOW_FUN_OPS Prog NatKeyCode Edge Fact.
  Definition facts (_ : unit) := [None; Some tt].
  Definition flow (_ : unit) e d := match e, d with
    | 1, None => [None; Some tt]
    | _, _ => [d]
    end.
  Definition seeds (_ : unit) := [(0, None); (0, Some tt)].
End Flow.

(** The path rules of Icfg and Flow, computed by the prepared solver. *)
Definition prepared_rules := Eval vm_compute in
  path_rules_fast NatKeyCode.encode (Icfg.kind tt) (Graph.dst tt) (Flow.facts tt) (Flow.flow tt)
    (Flow.seeds tt) (Graph.edges tt).

(** Rules of the prepared solver, which the analysis reads. *)
Module Rules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
  Definition rules (_ : unit) := prepared_rules.
End Rules.

Module A := IfdsCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact Flow Rules IfdsLatticeCode.

(** A lookup that holds for the listed keys of the path edges. *)
Definition look (k : A.key) :=
  existsb (A.key_eqb k)
    [(None, (0, None)); (Some tt, (0, Some tt));
     (None, (1, None)); (Some tt, (1, Some tt));
     (None, (2, None)); (None, (2, Some tt)); (Some tt, (2, Some tt));
     (None, (3, None)); (None, (3, Some tt)); (Some tt, (3, Some tt))].

(** * Prepared *)

Module PreparedTests.

  (** The prepared path rules equal the reference path rules. *)
  Example prepared_rules_match_reference :
    prepared_rules = path_rules NatKeyCode.eqb (Icfg.kind tt) (Graph.dst tt)
      (Flow.facts tt) (Flow.flow tt) (Flow.seeds tt) (Graph.edges tt).
  Proof.
    vm_compute; reflexivity.
  Qed.

End PreparedTests.

(** * Unsupported *)

Module UnsupportedTests.

  (** A graph whose edge 0 is intra-procedural and whose edge 1 is a plain jump. *)
  Module UnsupportedGraph <: CFG_OPS Prog NatKeyCode Edge.
    Definition entries (_ : unit) := [0].
    Definition edges (_ : unit) := [0; 1].
    Definition src (_ : unit) (e : nat) := e.
    Definition dst (_ : unit) (e : nat) := S e.
  End UnsupportedGraph.

  Module UnsupportedIcfg <: ICFG_OPS Prog NatKeyCode Edge UnsupportedGraph NatKeyCode.
    Definition kind (_ : unit) (_ : nat) : edge_kind nat := Intra.
  End UnsupportedIcfg.

  (** Flow that turns None into Some tt on edge 0 and keeps Some tt on edge 1. *)
  Module UnsupportedFlow <: FLOW_FUN_OPS Prog NatKeyCode Edge Fact.
    Definition facts (_ : unit) : list (option unit) := [None].
    Definition flow (_ : unit) e d := match e, d with
      | 0, None => [Some tt]
      | 1, Some _ => [d]
      | _, _ => []
      end.
    Definition seeds (_ : unit) : list (nat * option unit) := [(0, None)].
  End UnsupportedFlow.

  (** The path rules of the unsupported graph, computed by the prepared solver. *)
  Definition unsupported_rules := Eval vm_compute in
    path_rules_fast NatKeyCode.encode (UnsupportedIcfg.kind tt) (UnsupportedGraph.dst tt)
      (UnsupportedFlow.facts tt) (UnsupportedFlow.flow tt) (UnsupportedFlow.seeds tt)
      (UnsupportedGraph.edges tt).

  Module UnsupportedRules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
    Definition rules (_ : unit) := unsupported_rules.
  End UnsupportedRules.

  Module Unsupported := IfdsCode Prog NatKeyCode Edge UnsupportedGraph NatKeyCode UnsupportedIcfg
    Fact UnsupportedFlow UnsupportedRules IfdsLatticeCode.

  (** A lookup that holds for the two path edges that the jump reaches. *)
  Definition unsupported_lookup k :=
    Unsupported.key_eqb k (None, (0, None)) || Unsupported.key_eqb k (None, (1, Some tt)).

  (** The enumerated checker accepts the unsupported jump's rows against its lookup. *)
  Example enumerated_checker_accepts_jump : forallb (fun r =>
    row_ok IfdsLatticeCode.leb unsupported_lookup (Unsupported.target tt r)
      (eval_query (Unsupported.resume tt) unsupported_lookup
        (S (length (Unsupported.deps tt r))) (Unsupported.start tt r)))
    (Unsupported.rows tt) = true.
  Proof. vm_compute; reflexivity. Qed.

  (** The unsupported facts do not contain Some tt, so that seed is rejected. *)
  Example unsupported_facts_omit_some :
    existsb (Fact.eqb (Some tt)) (UnsupportedFlow.facts tt) = false.
  Proof. vm_compute; reflexivity. Qed.

  (** The unsupported facts contain the None fact. *)
  Example unsupported_facts_list_none :
    existsb (Fact.eqb None) (UnsupportedFlow.facts tt) = true.
  Proof. vm_compute; reflexivity. Qed.

  (** The unsupported rules agree with the reference path rules. *)
  Example unsupported_rules_match_reference :
    unsupported_rules = path_rules NatKeyCode.eqb
      (UnsupportedIcfg.kind tt) (UnsupportedGraph.dst tt) (UnsupportedFlow.facts tt)
      (UnsupportedFlow.flow tt) (UnsupportedFlow.seeds tt) (UnsupportedGraph.edges tt).
  Proof.
    vm_compute; reflexivity.
  Qed.

End UnsupportedTests.

(** * Indexed *)

Module IndexedTests.

  (** Duplicated calls, returns and facts retain their occurrence order. *)
  Definition indexed_test_kind (e : nat) : edge_kind nat :=
    match e with
    | 0 => Call 7
    | 1 => Return 9
    | 2 => CallToReturn 7
    | 3 => Return 7
    | _ => Intra
    end.

  (** Edge 3 duplicates its fact, and every other edge keeps the fact once. *)
  Definition indexed_test_flow (e x : nat) : list nat :=
    if Nat.eqb e 3 then [x; x] else [x].

  (** The fast indexed rules equal the reference rules, with duplicates kept. *)
  Example indexed_rules_match_reference :
    path_rules_fast NatKeyCode.encode indexed_test_kind S [0; 0; 1]
      indexed_test_flow [(0, 0)] [0; 3; 2; 0; 1; 3; 4] =
    path_rules NatKeyCode.eqb indexed_test_kind S [0; 0; 1]
      indexed_test_flow [(0, 0)] [0; 3; 2; 0; 1; 3; 4].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With no facts, the seed of the indexed rules is kept as a path identity. *)
  Example empty_facts_keep_seed :
    path_rules_fast NatKeyCode.encode indexed_test_kind S [] indexed_test_flow
      [(0, 0)] [0; 3; 2; 0; 1; 3; 4] = [PathIdentity 0 0].
  Proof.
    vm_compute; reflexivity.
  Qed.

End IndexedTests.
