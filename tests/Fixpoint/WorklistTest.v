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

(* assignment_lookup_present_missing_ticks had (true, false, 3 ticks, 4 ticks).
   The lookup values stay the same after shifting the natural keys by one. *)
Example assignment_lookup_present_missing :
  let m := PTrieCode.set 1%positive (1%positive, true) PTrieCode.empty in
  (C.look m 1%positive, C.look m 2%positive) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(* FixpointCheckTest's full_accept, full_reject and full_empty run above.
   index_repeated_sides runs in IndexedTest and WorklistOrderTest.
   partial_accept, partial_reject_open_read, partial_empty and partial_visits_once
   use the deleted Partial family. cut_accept, cut_reject_order,
   cut_reject_duplicate, cut_reject_value and cut_empty use the deleted Cut family.

   FixpointAnalyzeTest's bad_candidate_rejected runs in IndexedTest.
   cycle_solved, cycle_exhausted, total_cycle, cycle_driver_preserves_support,
   unrelated_binding_is_not_supported, empty_solved and joining_unbounded_exhausts
   use the deleted Kleene reference or total-solver families.
   charged_certification_accepts and charged_certification_rejects observe the
   deleted certify_checked_c wrapper. CertifiedCode now accepts solver outcomes
   and assignments. It has no Boolean-to-subtype certification operation.

   FixpointWorklistTest's cycle_matches_reference compares against deleted Kleene.
   cycle_evaluation_prefix_bound, cycle_adequate, cycle_priority_least,
   counter_widening_adequate and counter_widening_prefix_bound are proof clients.
   cycle_eval_equation and cycle_sides_equation are universal query equations.
   The cycle run above retains their propagated values and ordered side effects.
   cycle_dependency_occurrences had ([0; 1; 2; 0; 0; 0], [1], [0; 0], 6).
   WorklistOrderTest retains the writes with keys shifted by one. Its reader lists
   [2] and [1; 4] identify distinct row occurrences. WorklistCode exposes no
   WorklistCost.dependency_count or WorklistCost.unknowns operation. *)
