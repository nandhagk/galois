(** * Dense dataflow observations

    A diamond graph exercises forward and backward rows and candidate checks.
    For example, a boundary at node one propagates backward to node zero.

    Groups:
    - [SeedsTests] The rows of each direction come out in their fixed order.
    - [DiamondTests] Forward and backward analyses of the diamond give their fixed values.
    - [CandidateTests] Candidates are accepted or rejected, and one step runs out of fuel.
    - [DuplicateTests] Duplicate listed edges give the rows and values that the listing implies.

    Builds on: Framework.Dense and Fixpoint.Worklist. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
Import List.ListNotations.

(** * Fixtures *)

(** Booleans as a widening lattice, ordered by implication and joined by or. *)
Module BoolOps <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
End BoolOps.

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.

(** A diamond with edges 0 to 1, 1 to 2, 2 to 3 and 3 to 3. *)
Module Diamond <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (backward : bool) := if backward then [0; 1; 2; 3] else [0].
  Definition edges (_ : bool) := [0; 1; 2; 3].
  Definition src (_ : bool) e := match e with 2 => 1 | 3 => 2 | _ => 0 end.
  Definition dst (_ : bool) e := match e with 0 => 1 | 1 => 2 | _ => 3 end.
End Diamond.

(** Forward flow with boundary true and identity transfer. *)
Module ForwardFlow <: FLOW_OPS Prog NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : bool) (_ : nat) := true.
  Definition transfer (_ : bool) (_ : nat) (a : bool) := a.
End ForwardFlow.

(** Backward flow whose boundary is true only at node 1, with identity transfer. *)
Module BackwardFlow <: FLOW_OPS Prog NatKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : bool) n := Nat.eqb n 1.
  Definition transfer (_ : bool) (_ : nat) (a : bool) := a.
End BackwardFlow.

Module F := DenseCode Prog NatKeyCode Edge Diamond BoolOps ForwardFlow.
Module B := DenseCode Prog NatKeyCode Edge Diamond BoolOps BackwardFlow.
Module P := PolicyCode BoolOps.
Module FC := CheckCode BoolOps F.
Module BC := CheckCode BoolOps B.
Module FW := WorklistCode BoolOps F P HeapCode.
Module BW := WorklistCode BoolOps B P HeapCode.
Module FR := NarrowCode BoolOps F FC.
Module BR := NarrowCode BoolOps B BC.
Module FA := CertifiedCode BoolOps F FW FC FR.
Module BA := CertifiedCode BoolOps B BW BC BR.

(** The policy that uses the empty trie and the unit widening parameter, with bound 0. *)
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** * Seeds *)

Module SeedsTests.

  (** Forward rows are the seed of node 0 followed by one flow row per node. *)
  Example forward_rows_order :
    F.rows false = [Seed 0; Flow 0; Flow 1; Flow 2; Flow 3].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Backward rows are the four seeds followed by one flow row per node. *)
  Example backward_rows_order :
    B.rows true = [Seed 0; Seed 1; Seed 2; Seed 3; Flow 0; Flow 1; Flow 2; Flow 3].
  Proof.
    vm_compute; reflexivity.
  Qed.

End SeedsTests.

(** * Diamond *)

Module DiamondTests.

  (** The forward analysis gives true at nodes 0 to 3, and false at the unknown node 99. *)
  Example forward_values :
    match FA.analyze false flat 8%N with
    | Solved m => Some (map (FC.look m) [0; 1; 2; 3; 99])
    | _ => None
    end = Some [true; true; true; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** At fuel 8 the backward analysis runs out, so it gives no solution. *)
  Example backward_stops_at_fuel_eight :
    match BA.analyze true flat 8%N with
    | Solved m => Some (map (BC.look m) [0; 1; 2; 3])
    | _ => None
    end = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** At fuel 12 the backward analysis gives true at nodes 0 and 1 and false at nodes 2 and 3. *)
  Example backward_values_at_fuel_twelve :
    match BA.analyze true flat 12%N with
    | Solved m => Some (map (BC.look m) [0; 1; 2; 3])
    | _ => None
    end = Some [true; true; false; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

End DiamondTests.

(** * Candidates *)

Module CandidateTests.

  (** The empty candidate is rejected by the forward check. *)
  Example empty_candidate_rejected : FC.check false PTrieCode.empty = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A candidate that sets nodes 0 and 1 to true satisfies the backward check. *)
  Example backward_candidate_accepted :
    BC.check true (PTrieCode.set (NatKeyCode.encode 1) (1, true)
      (PTrieCode.set (NatKeyCode.encode 0) (0, true) PTrieCode.empty)) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With fuel 1 the forward analysis runs out before it reaches a solution. *)
  Example one_step_runs_out_of_fuel :
    match FA.analyze false flat 1%N with OutOfFuel _ => true | _ => false end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CandidateTests.

(** * Duplicates *)

Module DuplicateTests.

  (** A CFG whose entry 0 is listed twice, and whose edges 0 and 1 both run from 0 to 1. *)
  Module Duplicate <: CFG_OPS Prog NatKeyCode Edge.
    Definition entries (_ : bool) := [0; 0].
    Definition edges (_ : bool) := [0; 1].
    Definition src (_ : bool) (_ : nat) := 0.
    Definition dst (_ : bool) (_ : nat) := 1.
  End Duplicate.

  Module Dup := DenseCode Prog NatKeyCode Edge Duplicate BoolOps ForwardFlow.
  Module DupC := CheckCode BoolOps Dup.
  Module DupR := NarrowCode BoolOps Dup DupC.
  Module DupW := WorklistCode BoolOps Dup P HeapCode.
  Module DupA := CertifiedCode BoolOps Dup DupW DupC DupR.

  (** The rows keep the listed entries and give one flow row for each listed edge. *)
  Example listed_duplicates_give_rows :
    Dup.rows false = [Seed 0; Seed 0; Flow 0; Flow 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The analysis of the duplicate listing gives true at nodes 0 and 1, and false at node 99. *)
  Example duplicate_edges_values :
    match DupA.analyze false flat 8%N with
    | Solved m => Some (map (DupC.look m) [0; 1; 99])
    | _ => None
    end = Some [true; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

End DuplicateTests.
