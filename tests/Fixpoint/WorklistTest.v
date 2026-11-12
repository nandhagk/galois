(** * Worklist and checker observations

    Boolean rows exercise repeated contributions, checking and fuel exhaustion.
    For example, the cycle obtains its seed through a side contribution.
    Builds on: Fixpoint.Worklist and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith PArith.
From Galois.Base Require Import Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Policy Check Narrow
  Worklist Certified.
Import List.ListNotations.

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

Module Cycle <: SYSTEM_OPS BoolOps.
  Definition prog := bool.
  Definition key := positive.
  Definition row := positive.
  Definition frame := unit.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (p : bool) := if p then [1; 2; 3; 1]%positive else [].
  Definition target (_ : bool) (r : positive) := r.
  Definition start (_ : bool) (r : positive) : query key bool unit :=
    if Pos.eqb r 1 then Ask 2%positive tt
    else if Pos.eqb r 2 then Ask 1%positive tt
    else Side 1%positive true (Side 1%positive false (Ret false)).
  Definition resume (_ : bool) (_ : unit) (a : bool) : query key bool unit := Ret a.
  Definition deps (_ : bool) (r : positive) :=
    if Pos.eqb r 1 then [2]%positive else if Pos.eqb r 2 then [1]%positive else [].
  Definition sides (_ : bool) (r : positive) :=
    if Pos.eqb r 3 then [1; 1]%positive else [].
End Cycle.

Module P := PolicyCode BoolOps.
Module C := CheckCode BoolOps Cycle.
Module R := NarrowCode BoolOps Cycle C.
Module W := WorklistCode BoolOps Cycle P HeapCode.
Module A := CertifiedCode BoolOps Cycle W C R.

Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.
Definition values := PTrieCode.set 2%positive (2%positive, true)
  (PTrieCode.set 1%positive (1%positive, true) PTrieCode.empty).
Definition observe result :=
  match result with
  | Solved m => Some (map (C.look m) [1; 2; 3; 100]%positive)
  | _ => None
  end.

Example full_accept : C.check true values = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example full_reject : C.check true PTrieCode.empty = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example full_empty : C.check false PTrieCode.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_one_probe : observe (W.run false flat 1%N) = Some [false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example cycle_with_repeated_row_and_side_targets :
  observe (W.run true flat 8%N) = Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example fuel_exhaustion_keeps_partial_assignment :
  match W.run true flat 1%N with
  | OutOfFuel m => map (C.look m) [1; 2; 3]%positive
  | _ => []
  end = [false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example certified_cycle : observe (A.analyze true flat 8%N) = Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.
