(** * Rejection of an unchecked solver candidate

    Certification checks a solver result before returning a solved assignment.
    For example, a solver that returns the empty cycle assignment fails certification.

    Groups:
    - [CandidateTests] The checker rejects the unchecked candidate.

    Builds on: Fixpoint.Certified, Fixpoint.Narrow and CheckTest. *)

From Stdlib Require Import NArith Bool.
From Galois.Base Require Import MapSig Trie.
From Galois.Fixpoint Require Import PolicySig SolverSig Narrow Certified.
From Galois.Tests.Fixpoint Require Import CheckTest.

(** * Fixtures *)

(** A solver that always returns the empty assignment as solved. *)
Module BadSource <: SOLVER_OPS BoolOps Cycle.
  Definition run (_ : bool) (_ : policy unit) (_ : N) : outcome (kmap nat bool) :=
    Solved PTrieCode.empty.
End BadSource.

Module R := NarrowCode BoolOps Cycle C.
Module A := CertifiedCode BoolOps Cycle BadSource C R.

(** A policy with no heads and no delays. *)
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** * Candidate *)

Module CandidateTests.

  (** The checker rejects the empty candidate of the bad solver with Check_failed. *)
  Example bad_candidate_rejected :
    match A.analyze true flat 1%N with
    | Rejected Check_failed => true
    | _ => false
    end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CandidateTests.
