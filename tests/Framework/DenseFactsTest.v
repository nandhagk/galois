(** * Dense counter facts

    Boolean counter rows retain forward values and backward boundary facts.
    For example, an absent backward boundary evaluates to false.

    Groups:
    - [ForwardTests] The worklist solution reads the forward value at node true.
    - [BoundaryTests] Absent and listed backward boundaries give their seeded facts.

    Builds on: Framework.Dense and Fixpoint.Worklist. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Heap Trie.
From Galois.Fixpoint Require Import Query PolicySig SolverSig Policy Check Worklist.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
From Galois.Tests.Framework Require Import DenseTest.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := unit. End Edge.

(** A CFG with entries false and true, one edge from false to true. *)
Module Cfg <: CFG_OPS Prog BoolKeyCode Edge.
  Definition entries (_ : unit) := [false; true].
  Definition edges (_ : unit) := [tt].
  Definition src (_ : unit) (_ : unit) := false.
  Definition dst (_ : unit) (_ : unit) := true.
End Cfg.

(** Forward flow whose boundary is false and whose transfer returns true. *)
Module ForwardFlow <: FLOW_OPS Prog BoolKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : unit) (_ : bool) := false.
  Definition transfer (_ : unit) (_ : unit) (_ : bool) := true.
End ForwardFlow.

(** Backward flow whose boundary is false and whose transfer is the identity. *)
Module Absent <: FLOW_OPS Prog BoolKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : unit) (_ : bool) := false.
  Definition transfer (_ : unit) (_ : unit) (a : bool) := a.
End Absent.

(** Backward flow whose boundary negates the node fact and whose transfer is the identity. *)
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

(** * Forward *)

Module ForwardTests.

  (** The worklist solution assigns true to node true. *)
  Example solution_reads_true_node :
    match W.run tt flat 4%N with Solved m => FC.look m true | _ => false end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ForwardTests.

(** * Boundary *)

Module BoundaryTests.

  (** An absent backward boundary seeded with true evaluates to false, which is below false. *)
  Example absent_boundary_is_false :
    match eval_query (B.resume tt) (fun _ => false) 1 (B.start tt (Seed true)) with
    | Some (a, _) => (a, BoolOps.leb a false)
    | None => (true, false)
    end = (false, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A listed nonterminal boundary is below the negation of its seed. *)
  Example listed_boundary_below_negation :
    match eval_query (N.resume tt) negb 1 (N.start tt (Seed false)) with
    | Some (a, _) => BoolOps.leb a (negb false)
    | None => false
    end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End BoundaryTests.
