(** * Prepared cycle indexes

    Preparation retains repeated rows and deduplicates each row's repeated writes.
    For example, the cycle seed contributes once per row occurrence.
    Builds on: Fixpoint.Indexed and Fixpoint.WorklistTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import MapSig Trie.
From Galois.Fixpoint Require Import Indexed PolicySig SolverSig Certified.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

Module I := IndexedCode BoolOps Cycle.

Definition cycle_index := I.prepare true.

Example index_repeated_sides :
  map snd (I.rows_of cycle_index 1%positive) = [1; 3; 1]%positive /\
  I.rows_of cycle_index 100%positive = [].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example index_empty : I.rows (I.prepare false) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Module BadSolver.
  Definition run (_ : bool) (_ : policy unit) (_ : N) : outcome (kmap positive bool) := Solved PTrieCode.empty.
End BadSolver.

Module BadAnalysis := CertifiedCode BoolOps Cycle BadSolver C R.

Example bad_candidate_rejected :
  BadAnalysis.analyze true flat 1%N = Rejected Check_failed.
Proof.
  vm_compute; reflexivity.
Qed.
