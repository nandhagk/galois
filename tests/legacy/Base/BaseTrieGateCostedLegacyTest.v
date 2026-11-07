(** * Paired costed trie timing client

    This fresh compilation evaluates the complete real-trie workload observation.
    For example, specialized intersection and difference retain the expected half.
    Builds on: BaseTrieGateLegacyTest and CostMonad. *)

From Galois.Cost Require Import CostMonad.
From Galois.Tests.Legacy.Base Require Import BaseTrieGateLegacyTest.

Example measured_costed : Cost.value (costed_workload gate_size) = expected gate_size.
Proof.
  vm_compute. reflexivity.
Qed.
