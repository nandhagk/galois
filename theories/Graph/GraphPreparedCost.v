(** * Costed preparation agreement

    The public preparation value is the value of its single costed implementation.
    For example, callback charges do not change a prepared graph's record values.
    Builds on: GraphPrepared. *)

From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel GraphPrepared.

Module PreparedCost.

(** Cost erasure returns the existing public preparation on its full arbitrary-input domain. *)
Theorem prepare_c_value {V E} enc (g : Graph.t V E) :
  Cost.value (Prepared.prepare_c enc g) = Prepared.prepare enc g.
Proof.
  reflexivity.
Qed.

End PreparedCost.
