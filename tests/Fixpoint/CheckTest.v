(** * Full solution checker observations

    A cycle exercises repeated rows, repeated side contributions and absent bindings.
    For example, the seed row rejects the empty assignment through its true side value.
    Builds on: Fixpoint.Check and Base.Key. *)

From Stdlib Require Import List Bool Arith.
From Galois.Base Require Import Key Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig Check.
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

Definition cycle_values := PTrieCode.set (Cycle.key_code 1) (1, true)
  (PTrieCode.set (Cycle.key_code 0) (0, true) PTrieCode.empty).

(** The seeded cycle accepts its complete assignment. *)
Example full_accept : C.check true cycle_values = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The empty assignment fails the seed row's side contribution. *)
Example full_reject : C.check true PTrieCode.empty = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** A system with no rows accepts the empty assignment. *)
Example full_empty : C.check false PTrieCode.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Lookup retains the present and missing values of the old lookup fixture. *)
Example assignment_lookup_present_missing :
  let m := PTrieCode.set (Cycle.key_code 0) (0, true) PTrieCode.empty in
  (C.look m 0, C.look m 1) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.
