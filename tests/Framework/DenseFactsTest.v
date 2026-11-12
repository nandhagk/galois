(** * Dense counter facts

    Boolean counter rows retain forward values and backward boundary facts.
    For example, an absent backward boundary evaluates to false.
    Builds on: Framework.Dense and Fixpoint.Worklist. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Heap Trie.
From Galois.Fixpoint Require Import Query PolicySig SolverSig Policy Check Worklist.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
From Galois.Tests.Framework Require Import DenseTest.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := unit. End Edge.
Module Cfg <: CFG_OPS Prog BoolKeyCode Edge.
  Definition entries (_ : unit) := [false; true].
  Definition edges (_ : unit) := [tt].
  Definition src (_ : unit) (_ : unit) := false.
  Definition dst (_ : unit) (_ : unit) := true.
End Cfg.
Module ForwardFlow <: FLOW_OPS Prog BoolKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : unit) (_ : bool) := false.
  Definition transfer (_ : unit) (_ : unit) (_ : bool) := true.
End ForwardFlow.
Module Absent <: FLOW_OPS Prog BoolKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : unit) (_ : bool) := false.
  Definition transfer (_ : unit) (_ : unit) (a : bool) := a.
End Absent.
Module Nonterminal <: FLOW_OPS Prog BoolKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : unit) n := negb n.
  Definition transfer (_ : unit) (_ : unit) (a : bool) := a.
End Nonterminal.
Module F := DenseCode Prog BoolKeyCode Edge Cfg BoolOps ForwardFlow.
Module B := DenseCode Prog BoolKeyCode Edge Cfg BoolOps Absent.
Module N := DenseCode Prog BoolKeyCode Edge Cfg BoolOps Nonterminal.
Module FC := CheckCode BoolOps F.
Module W := WorklistCode BoolOps F P HeapCode.

Example counter_reads_solution :
  match W.run tt flat 4%N with Solved m => FC.look m true | _ => false end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(* absent_boundary's old absent exit fact false is now an explicit bottom seed.
   The old pair of fact and order-test values was (false, true). *)
Example absent_boundary :
  match eval_query (B.resume tt) (fun _ => false) 1 (B.start tt (Seed true)) with
  | Some (a, _) => (a, BoolOps.leb a false)
  | None => (true, false)
  end = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example listed_nonterminal_boundary :
  match eval_query (N.resume tt) negb 1 (N.start tt (Seed false)) with
  | Some (a, _) => BoolOps.leb a (negb false)
  | None => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.
