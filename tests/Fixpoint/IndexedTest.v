(** * Prepared cycle indexes

    Preparation retains repeated rows and deduplicates each row's repeated writes.
    For example, the cycle seed contributes once per row occurrence.

    Groups:
    - Fixtures: the prepared index of the cycle system.
    - Rows: the rows that the index returns for each key, and for an empty system.
    - Certification: a bad solver's candidate is rejected by the checker.

    Builds on: Fixpoint.Indexed and Fixpoint.WorklistTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import MapSig Trie.
From Galois.Fixpoint Require Import Indexed PolicySig SolverSig Certified.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

(** * Fixtures *)

Module I := IndexedCode BoolOps Cycle.

(** The index of the cycle system with its seed switched on. *)
Definition cycle_index := I.prepare true.

(** * Rows *)

Module RowTests.

  (** The row occurrences of key 1 keep their repeated rows in order. *)
  Example key_one_keeps_repeated_rows :
    map snd (I.rows_of cycle_index 1%positive) = [1; 3; 1]%positive.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A key that no row writes has no rows. *)
  Example absent_key_has_no_rows :
    I.rows_of cycle_index 100%positive = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Preparing a system with the seed switched off keeps no rows. *)
  Example empty_system_has_no_rows : I.rows (I.prepare false) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End RowTests.

(** * Certification *)

Module CertificationTests.

  (** A solver that returns the empty assignment is rejected by the checker. *)
  Module BadSolver.
    Definition run (_ : bool) (_ : policy unit) (_ : N) : outcome (kmap positive bool) :=
      Solved PTrieCode.empty.
  End BadSolver.

  Module BadAnalysis := CertifiedCode BoolOps Cycle BadSolver C R.

  (** The certified analysis rejects the bad solver's candidate with Check_failed. *)
  Example bad_candidate_rejected :
    BadAnalysis.analyze true flat 1%N = Rejected Check_failed.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CertificationTests.
