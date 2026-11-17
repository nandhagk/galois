(** * Worklist and checker observations

    Boolean rows exercise repeated contributions, checking and fuel exhaustion.
    For example, the cycle obtains its seed through a side contribution.

    Groups:
    - Fixtures: a Boolean lattice, a cycle system, a policy and the solver instances.
    - Check: the checker accepts and rejects complete assignments.
    - Solver: the solver's results on the cycle, with and without enough fuel.
    - Lookup: a lookup of a bound key and of a missing key.
    - Step: one worklist step after a popped row is reused.
    - Wide: the update of a key whose number is 2^39.
    - Rows: the preparation of a system with 200 row occurrences.

    Builds on: Fixpoint.Worklist and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith PArith.
From Galois.Base Require Import Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Policy Check Narrow
  Worklist WorklistSig Certified.
Import List.ListNotations.

(** * Fixtures *)

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

(** Rows 1 and 2 read each other, and row 3 writes its side contributions to key 1. *)
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

(** A policy with no heads and no delays. *)
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** An assignment that binds keys 1 and 2 to true. *)
Definition values := PTrieCode.set 2%positive (2%positive, true)
  (PTrieCode.set 1%positive (1%positive, true) PTrieCode.empty).

(** The values of keys 1, 2, 3 and 100 in a solved result, and None otherwise. *)
Definition observe result :=
  match result with
  | Solved m => Some (map (C.look m) [1; 2; 3; 100]%positive)
  | _ => None
  end.

(** * Check *)

Module CheckTests.

  (** The seeded cycle accepts its complete assignment. *)
  Example seeded_cycle_accepts_full_assignment : C.check true values = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty assignment fails the seed row's side contribution. *)
  Example empty_assignment_fails_seed_side : C.check true PTrieCode.empty = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A system with no rows accepts the empty assignment. *)
  Example empty_system_accepts_empty_assignment : C.check false PTrieCode.empty = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CheckTests.

(** * Solver *)

Module SolverTests.

  (** Without any rows, the solver solves to all false values after one probe. *)
  Example system_without_rows_solves_all_false :
    observe (W.run false flat 1%N) = Some [false; false; false; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With enough fuel, the cycle solves to true for its seeded rows. *)
  Example cycle_with_repeated_row_solves :
    observe (W.run true flat 8%N) = Some [true; true; false; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With too little fuel, the solver returns the partial assignment it reached. *)
  Example fuel_exhaustion_keeps_partial_assignment :
    match W.run true flat 1%N with
    | OutOfFuel m => map (C.look m) [1; 2; 3]%positive
    | _ => []
    end = [false; false; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The certified analysis returns the same solved values as the solver. *)
  Example certified_cycle_keeps_solved_values :
    observe (A.analyze true flat 8%N) = Some [true; true; false; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

End SolverTests.

(** * Lookup *)

Module LookupTests.

  (** A bound key looks up as its stored true value. *)
  Example bound_key_looks_up_true :
    C.look (PTrieCode.set 1%positive (1%positive, true) PTrieCode.empty) 1%positive = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A key with no binding looks up as false. *)
  Example missing_key_looks_up_false :
    C.look (PTrieCode.set 1%positive (1%positive, true) PTrieCode.empty) 2%positive = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End LookupTests.

(** * Step *)

Module StepTests.

  (** The popped row is reused after its dependencies are cleared, and only those are cleared. *)
  Definition popped_state := W.arm 2%positive (W.arm 100%positive (W.prepare true flat)).

  (** The row that the step pops is no longer live. *)
  Example popped_row_is_not_live :
    match W.step true flat popped_state with
    | inl next => trie_get 1%positive (ws_live next)
    | inr _ => None
    end = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The armed dependency of the popped row is cleared. *)
  Example popped_row_clears_its_dependency :
    match W.step true flat popped_state with
    | inl next => trie_get 2%positive (ws_armed next)
    | inr _ => None
    end = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unrelated armed row keeps its mark. *)
  Example unrelated_armed_row_keeps_mark :
    match W.step true flat popped_state with
    | inl next => trie_get 100%positive (ws_armed next)
    | inr _ => None
    end = Some tt.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The step leaves the value of key 1 false. *)
  Example popped_step_keeps_false_value :
    match W.step true flat popped_state with
    | inl next => C.look (ws_store next) 1%positive
    | inr _ => true
    end = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The row at key 1 is the next row occurrence after the step. *)
  Example popped_step_row_at_one :
    match W.step true flat popped_state with
    | inl next => W.row_at next 1%positive
    | inr _ => None
    end = Some 1%positive.
  Proof.
    vm_compute; reflexivity.
  Qed.

End StepTests.

(** * Wide *)

Module WideTests.

  (** A key of 2^39 is a wide key that the cycle system uses as a constant row. *)
  Definition wide_key : positive := 549755813888%positive.

  (** A cycle system with the wide key as an extra constant row. *)
  Module WideCycle <: SYSTEM_OPS BoolOps.
    Definition prog := bool.
    Definition key := positive.
    Definition row := positive.
    Definition frame := unit.
    Definition key_code (x : positive) := x.
    Definition key_eqb := Pos.eqb.
    Definition rows (p : bool) := if p then [1; 2; 3; 1; wide_key]%positive else [].
    Definition target (_ : bool) (r : positive) := r.
    Definition start (_ : bool) (r : positive) : query key bool unit :=
      if Pos.eqb r 1 then Ask 2%positive tt
      else if Pos.eqb r 2 then Ask 1%positive tt
      else if Pos.eqb r wide_key then Ret true
      else Side 1%positive true (Side 1%positive false (Ret false)).
    Definition resume (_ : bool) (_ : unit) (a : bool) : query key bool unit := Ret a.
    Definition deps (_ : bool) (r : positive) :=
      if Pos.eqb r 1 then [2]%positive else if Pos.eqb r 2 then [1]%positive else [].
    Definition sides (_ : bool) (r : positive) :=
      if Pos.eqb r 3 then [1; 1]%positive else [].
  End WideCycle.

  Module WideW := WorklistCode BoolOps WideCycle P HeapCode.

  (** The state of the wide system with the wide key stored as the given value. *)
  Definition wide_state (b : bool) : WideW.state :=
    let s := WideW.prepare true flat in
    WorklistState (PTrieCode.set wide_key (wide_key, b) (ws_store s))
      (ws_counters s) (ws_queue s) (ws_live s) (ws_rows s) (ws_readers s)
      (ws_armed s) (ws_ranks s).

  (** The state after updating an already stored wide key with the same value. *)
  Definition wide_stable := WideW.update_one true flat (wide_state true) (wide_key, true).

  (** The state after writing a strictly larger value at the wide key. *)
  Definition wide_strict := WideW.update_one true flat (wide_state false) (wide_key, true).

  (** Updating the wide key with its stored value leaves the state unchanged. *)
  Example stable_wide_update_keeps_state : wide_stable = wide_state true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A strict wide update stores the new value at the wide key. *)
  Example strict_wide_update_stores_value :
    trie_get wide_key (ws_store wide_strict) = Some (wide_key, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A strict wide update starts the wide key's counter at zero. *)
  Example strict_wide_update_counts_zero :
    trie_get wide_key (ws_counters wide_strict) = Some 0%N.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A strict wide update arms the wide key. *)
  Example strict_wide_update_arms_key :
    trie_get wide_key (ws_armed wide_strict) = Some tt.
  Proof.
    vm_compute; reflexivity.
  Qed.

End WideTests.

(** * Rows *)

Module RowTests.

  (** A system whose rows are the given list, each reading key 1 and depending on keys 1 and 2. *)
  Module RowsProgram <: SYSTEM_OPS BoolOps.
    Definition prog := list positive.
    Definition key := positive.
    Definition row := positive.
    Definition frame := unit.
    Definition key_code (x : positive) := x.
    Definition key_eqb := Pos.eqb.
    Definition rows (p : prog) := map (fun r => r) p.
    Definition target (_ : prog) (r : row) := r.
    Definition start (_ : prog) (_ : row) : query key bool unit := Ask 1%positive tt.
    Definition resume (_ : prog) (_ : unit) (a : bool) : query key bool unit := Ret a.
    Definition deps (_ : prog) (_ : row) := [1; 2]%positive.
    Definition sides (_ : prog) (_ : row) : list positive := [].
  End RowsProgram.

  Module RowsW := WorklistCode BoolOps RowsProgram P HeapCode.

  (** Two hundred row occurrences, numbered from 1. *)
  Definition rows200 := wl_ids_from (2 * 100) 1%positive.

  (** The worklist state after preparing the two hundred rows. *)
  Definition rows200_state := RowsW.prepare rows200 flat.

  (** Preparing two hundred rows stores each of them. *)
  Example prepared_rows_are_all_stored :
    length (PTrieCode.elements (ws_rows rows200_state)) = (2 * 100)%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The readers of key 1 are the whole list of row occurrences. *)
  Example readers_of_key_one_are_all_rows :
    RowsW.readers rows200_state 1%positive = rows200.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The readers of key 2 are the whole list of row occurrences. *)
  Example readers_of_key_two_are_all_rows :
    RowsW.readers rows200_state 2%positive = rows200.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The queue holds all two hundred rows. *)
  Example queue_holds_all_rows :
    HeapCode.size (ws_queue rows200_state) = 200%N.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The last row occurrence is the row at position 200. *)
  Example last_row_is_at_position_200 :
    RowsW.row_at rows200_state 200%positive = Some 200%positive.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The last row has rank one. *)
  Example last_row_has_rank_one :
    trie_get 200%positive (ws_ranks rows200_state) = Some 1%positive.
  Proof.
    vm_compute; reflexivity.
  Qed.

End RowTests.
