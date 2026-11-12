(** * Checked narrowing observations

    Each pass reads the previous assignment and checks the resulting candidate.
    For example, two passes propagate a decrease through a dependent row.
    Builds on: Fixpoint.Narrow and Fixpoint.Check. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig Check Narrow.
Import List.ListNotations.

Module BoolOps <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow (_ b : bool) := b.
End BoolOps.

Module Rows <: SYSTEM_OPS BoolOps.
  Definition prog := bool.
  Definition key := positive.
  Definition row := positive.
  Definition frame := bool.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : bool) := [1; 2]%positive.
  Definition target (_ : bool) (r : positive) := r.
  Definition start (rejected : bool) (r : positive) : query key bool frame :=
    if rejected then
      if Pos.eqb r 1 then Ask 2%positive true else Ret false
    else if Pos.eqb r 1 then Side 3%positive false (Ret false)
    else Ask 1%positive false.
  Definition resume (_ : bool) (invert a : bool) : query key bool frame :=
    Ret (if invert then negb a else a).
  Definition deps (_ : bool) (_ : positive) := [1; 2]%positive.
  Definition sides (_ : bool) (_ : positive) := [3]%positive.
End Rows.
Module C := CheckCode BoolOps Rows.
Module N := NarrowCode BoolOps Rows C.
Definition old := PTrieCode.set 1%positive (1%positive, true)
  (PTrieCode.set 2%positive (2%positive, true)
    (PTrieCode.set 3%positive (3%positive, true)
      (PTrieCode.set 100%positive (100%positive, true) PTrieCode.empty))).
Definition observe m := map (C.look m) [1; 2; 3; 100; 101]%positive.

Example simultaneous_old_reads :
  observe (N.narrow_candidate false old) = [false; true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example two_checked_passes :
  observe (N.refine false 2 old) = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example broken_candidate_is_discarded :
  (C.check true old, C.check true (N.narrow_candidate true old)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example discarded_candidate_keeps_old :
  N.narrow_pass true old = old.
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_rounds : N.refine false 0 old = old.
Proof.
  vm_compute; reflexivity.
Qed.
