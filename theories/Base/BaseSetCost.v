(** * One-sided finite-set traversal bounds

    Difference charges candidate keys and union charges the newly supplied right operand.
    For example, subtracting a singleton from any accumulated set has a singleton-width bound.
    Builds on: BaseSet, BaseMapCost and CostBound. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseMapCost BaseSet BaseTrieCost.

Module FinSetCost.

(** Raw-set emptiness inherits the Map owner's zero-tick root-observation price. *)
Theorem is_empty_cost {K} (s : FinSet.t K) : Cost.ticks (FinSet.is_empty_c s) = 0%N.
Proof.
  apply MapCost.is_empty_cost.
Qed.

(** Difference requires well-formedness and key widths only for its candidate operand. *)
Theorem diff_numeric_cost {K} (E : encoding K) (candidates accumulated : FinSet.t K) w :
  FinSet.wf E candidates ->
  (forall k, FinSet.mem E k candidates = true -> (key_bits E k <= w)%N) ->
  (Cost.ticks (FinSet.diff_c candidates accumulated) <=
    TrieCost.trie_k * (1 + N.of_nat (FinSet.size candidates) * w))%N.
Proof.
  intros Hwf Hwidth. rewrite FinSet.diff_backend, FinSet.size_backend.
  apply (MapCost.diff_numeric_cost E); [exact Hwf |].
  intros k [] Hget; apply Hwidth, FinSet.mem_spec, Hget.
Qed.

(** Union includes its actual unit callback and bounds only the newly inserted right operand. *)
Theorem union_numeric_cost_right {K} (E : encoding K) (accumulated fresh : FinSet.t K) w :
  FinSet.wf E fresh ->
  (forall k, FinSet.mem E k fresh = true -> (key_bits E k <= w)%N) ->
  (Cost.ticks (FinSet.union_c accumulated fresh) <=
    (TrieCost.trie_k + 1) * (1 + N.of_nat (FinSet.size fresh) * w))%N.
Proof.
  intros Hwf Hwidth. rewrite FinSet.union_backend, FinSet.size_backend.
  apply (MapCost.union_with_numeric_cost_right E).
  - exact Hwf.
  - intros k [] Hget; apply Hwidth, FinSet.mem_spec, Hget.
  - intros [] []; rewrite Cost.ticks_lift; reflexivity.
Qed.

(** Every family of valid candidate sets has a candidate-width difference bound. *)
Theorem diff_bigO {X K} (E : encoding K)
    (candidates accumulated : X -> FinSet.t K) (width : X -> N) :
  (forall x, FinSet.wf E (candidates x)) ->
  (forall x k, FinSet.mem E k (candidates x) = true -> (key_bits E k <= width x)%N) ->
  bigO (fun x => (N.of_nat (FinSet.size (candidates x)) * width x)%N)
    (fun x => Cost.ticks (FinSet.diff_c (candidates x) (accumulated x))).
Proof.
  intros Hwf Hwidth; exists TrieCost.trie_k; intro x.
  apply (diff_numeric_cost E _ _ _ (Hwf x)), Hwidth.
Qed.

(** Every family of valid new batches has a new-batch-width union bound. *)
Theorem union_bigO_right {X K} (E : encoding K)
    (accumulated fresh : X -> FinSet.t K) (width : X -> N) :
  (forall x, FinSet.wf E (fresh x)) ->
  (forall x k, FinSet.mem E k (fresh x) = true -> (key_bits E k <= width x)%N) ->
  bigO (fun x => (N.of_nat (FinSet.size (fresh x)) * width x)%N)
    (fun x => Cost.ticks (FinSet.union_c (accumulated x) (fresh x))).
Proof.
  intros Hwf Hwidth; exists (TrieCost.trie_k + 1)%N; intro x.
  apply (union_numeric_cost_right E _ _ _ (Hwf x)), Hwidth.
Qed.

End FinSetCost.
