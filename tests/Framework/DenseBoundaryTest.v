(** * Dense loop and boundary observations

    Loop, singleton and empty graphs exercise seeds in both directions.
    For example, an empty graph yields the bottom value.
    Builds on: Framework.Dense and Framework.DenseTest. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
From Galois.Tests.Framework Require Import DenseTest.
Import List.ListNotations.

Module Shape <: TYPE. Definition t := nat. End Shape.
Module Graph <: CFG_OPS Shape NatKeyCode Edge.
  Definition entries p := if Nat.eqb p 2 then [] else if Nat.eqb p 0 then [0; 1; 2] else [0].
  Definition edges p := if Nat.eqb p 0 then [0; 1; 2] else [].
  Definition src (_ : nat) e := if Nat.eqb e 0 then 0 else 1.
  Definition dst (_ : nat) e := if Nat.eqb e 2 then 2 else 1.
End Graph.
Module Forward <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : nat) (_ : nat) := true.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Forward.
Module Backward <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : nat) n := Nat.eqb n 1.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Backward.
Module F := DenseCode Shape NatKeyCode Edge Graph BoolOps Forward.
Module B := DenseCode Shape NatKeyCode Edge Graph BoolOps Backward.
Module FC := CheckCode BoolOps F.
Module BC := CheckCode BoolOps B.
Module FW := WorklistCode BoolOps F P HeapCode.
Module BW := WorklistCode BoolOps B P HeapCode.
Module FR := NarrowCode BoolOps F FC.
Module BR := NarrowCode BoolOps B BC.
Module FA := CertifiedCode BoolOps F FW FC FR.
Module BA := CertifiedCode BoolOps B BW BC BR.

Example loop_forward :
  match FA.analyze 0 flat 8%N with
  | Solved m => Some (map (FC.look m) [0; 1; 2])
  | _ => None
  end = Some [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_backward :
  match BA.analyze 0 flat 8%N with
  | Solved m => Some (map (BC.look m) [0; 1; 2])
  | _ => None
  end = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_seed :
  match FA.analyze 1 flat 2%N with
  | Solved m => Some (map (FC.look m) [0; 1])
  | _ => None
  end = Some [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(* At fuel 1 the old result was Some [false]. The new result is None. *)
Example no_boundary_singleton_old_fuel :
  match BA.analyze 1 flat 1%N with
  | Solved m => Some (map (BC.look m) [0])
  | _ => None
  end = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example no_boundary_singleton :
  match BA.analyze 1 flat 2%N with
  | Solved m => Some (map (BC.look m) [0])
  | _ => None
  end = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_rows :
  match FA.analyze 2 flat 1%N with
  | Solved m => Some (map (FC.look m) [0])
  | _ => None
  end = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Module Unlisted <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : nat) n := Nat.eqb n 99.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Unlisted.
Module U := DenseCode Shape NatKeyCode Edge Graph BoolOps Unlisted.
Module UC := CheckCode BoolOps U.

Example unlisted_boundary_is_not_a_row : UC.check 1 PTrieCode.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.

(* FrameworkDenseAgreementTest's absent_boundary observed (false, true) for the
   absent exit fact and its order check. no_boundary_singleton retains bottom at
   an unseeded node. listed_nonterminal_boundary checked true at a listed
   nonterminal seed. DenseTest.diamond_backward_nonterminal_boundary retains
   the seed value at node one and its propagation to node zero.

   agreement_positive and two_program_stuttering_positive are behaviour proofs.
   DENSE_SOUND exports forward covers, with no backward agreement or two-program
   simulation theorem. all_nonexit_premises and missing_exit_negative prove
   conjunctions involving those retired agreement interfaces.
   initial_agreement_boundary proves initial and agreement predicates.
   unmatched_stay_boundary proves the fixture rank inequality 0 < 1. No
   completion or stuttering-rank operation is exported by Dense or Cfg.

   FrameworkDenseForwardTest's counter_forward_positive and
   counter_history_positive are soundness proofs. counter_reads_solution obtained
   true from that soundness proof. DenseTest.diamond_forward retains true at
   reached nodes through a computed solver result. bad_transfer_negative proves
   a post-solution together with failure of the concrete gamma and local law.
   empty_history_boundary proves membership of (C0, []) in its fixture gamma.
   DENSE_SOUND has no history-indexed concretisation interface.

   FrameworkDenseWitnessTest's wrong_membership_law_negative refutes antitonicity.
   must_witness_positive and backward_witness_positive prove In tt [tt].
   may_cover_positive proves that the reached node's may fact is true.
   absent_entry_negative proves a post-solution, a false must fact, absence of
   In tt [] and failure of boundary coverage. terminal_seed_negative proves the
   analogous terminal post-solution and absence of In tt [].
   empty_history_boundary refutes the entry must predicate and In tt [].
   terminal_continuation_boundary refutes the terminal must predicate and In tt [].
   Dense exports no witness, cover, must-membership or backward-witness theorem.
   These are relational proof clients, outside task 3.9's computed-proof scope. *)
