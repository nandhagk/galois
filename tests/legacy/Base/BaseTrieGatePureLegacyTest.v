(** * Paired legacy trie timing client

    This fresh compilation evaluates the complete real-trie workload observation.
    For example, every inserted key is checked in its original input order.
    Builds on: BaseTrieGateLegacyTest. *)

From Galois.Tests.Legacy.Base Require Import BaseTrieGateLegacyTest.

Example measured_pure : pure_workload gate_size = expected gate_size.
Proof.
  vm_compute. reflexivity.
Qed.
