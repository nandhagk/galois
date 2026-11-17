(** * Full solution checker observations

    A cycle exercises repeated rows, repeated side contributions and absent bindings.
    For example, the seed row rejects the empty assignment through its true side value.

    Groups:
    - Fixtures: a Boolean lattice, a cycle system and two assignments.
    - Full: the checker accepts or rejects a complete assignment.
    - Lookup: a lookup returns the stored value of a bound key and false for a missing key.

    Builds on: Fixpoint.Check and Base.Key. *)

From Stdlib Require Import List Bool Arith.
From Galois.Base Require Import Key Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig Check.
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

(** A cycle of rows 0 and 1, and a seed row 2 that writes row 0 twice. *)
Module Cycle <: SYSTEM_OPS BoolOps.
  Definition prog := bool.
  Definition key := nat.
  Definition row := nat.
  Definition frame := unit.
  Definition key_code := NatKeyCode.encode.
  Definition key_eqb := Nat.eqb.
  Definition rows (p : bool) := if p then [0; 1; 2; 0] else [].
  Definition target (_ : bool) (r : nat) := r.
  Definition start (p : bool) (r : nat) : query key bool unit :=
    if p then
      if Nat.eqb r 0 then Ask 1 tt
      else if Nat.eqb r 1 then Ask 0 tt
      else Side 0 true (Side 0 false (Ret false))
    else Ret true.
  Definition resume (_ : bool) (_ : unit) (a : bool) : query key bool unit := Ret a.
  Definition deps (p : bool) (r : nat) :=
    if p then if Nat.eqb r 0 then [1] else if Nat.eqb r 1 then [0] else [] else [].
  Definition sides (p : bool) (r : nat) :=
    if p then if Nat.eqb r 0 then [] else if Nat.eqb r 1 then [] else [0; 0] else [].
End Cycle.

Module C := CheckCode BoolOps Cycle.

(** An assignment that binds keys 0 and 1 to true. *)
Definition cycle_values := PTrieCode.set (Cycle.key_code 1) (1, true)
  (PTrieCode.set (Cycle.key_code 0) (0, true) PTrieCode.empty).

(** An assignment that binds only key 0, to true. *)
Definition only_zero_bound := PTrieCode.set (Cycle.key_code 0) (0, true) PTrieCode.empty.

(** * Full *)

Module FullTests.

  (** The seeded cycle accepts its complete assignment. *)
  Example seeded_cycle_accepts_full_assignment : C.check true cycle_values = true.
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

End FullTests.

(** * Lookup *)

Module LookupTests.

  (** A bound key returns its stored Boolean value. *)
  Example bound_key_looks_up_true : C.look only_zero_bound 0 = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A key with no binding looks up as false. *)
  Example missing_key_looks_up_false : C.look only_zero_bound 1 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End LookupTests.
