(** * Importing one-sided set cost clients

    These clients discharge the candidate and batch duties on nonempty sets.
    For example, the same two candidates have the same bound against one or five old keys.
    Builds on: BaseSetCost and BaseEncoding. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet BaseSetCost BaseTrieCost
  BaseMap BaseMapCost.
Import List.ListNotations.

Definition small_candidates := FinSet.of_list positive_encoding [2; 3]%positive.
Definition old_small := FinSet.of_list positive_encoding [2]%positive.
Definition old_large := FinSet.of_list positive_encoding [1; 2; 3; 4; 5]%positive.

Lemma small_candidates_width k :
  FinSet.mem positive_encoding k small_candidates = true ->
  (key_bits positive_encoding k <= 2)%N.
Proof.
  unfold small_candidates; rewrite FinSet.mem_of_list, existsb_exists.
  intros [q [Hq Heq]]; apply (eqb_true_iff _ positive_encoding_laws) in Heq.
  subst k; destruct Hq as [<- | [<- | Hbad]]; [vm_compute; discriminate |
    vm_compute; discriminate | contradiction].
Qed.

(** The numerical difference theorem applies to any accumulated storage without its width duties. *)
Example difference_contract_client (old : FinSet.t positive) :
  (Cost.ticks (FinSet.diff_c small_candidates old) <=
    TrieCost.trie_k * (1 + N.of_nat (FinSet.size small_candidates) * 2))%N.
Proof.
  apply (FinSetCost.diff_numeric_cost positive_encoding).
  - apply FinSet.wf_of_list.
  - exact small_candidates_width.
Qed.

(** The union theorem needs no accumulated-set invariant or accumulated-size bound. *)
Example union_contract_client (old : FinSet.t positive) :
  (Cost.ticks (FinSet.union_c old small_candidates) <=
    (TrieCost.trie_k + 1) * (1 + N.of_nat (FinSet.size small_candidates) * 2))%N.
Proof.
  apply (FinSetCost.union_numeric_cost_right positive_encoding).
  - apply FinSet.wf_of_list.
  - exact small_candidates_width.
Qed.

Example difference_memberships :
  (FinSet.elements (FinSet.diff small_candidates old_small),
    FinSet.elements (FinSet.diff small_candidates old_large)) = ([3], [])%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example union_cardinalities :
  (FinSet.size (FinSet.union old_small small_candidates),
    FinSet.size (FinSet.union old_large small_candidates)) = (2, 5).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_difference_contract :
  (Cost.ticks (FinSet.diff_c (@FinSet.empty positive) old_large) <=
    TrieCost.trie_k)%N.
Proof.
  assert (Hwidth : forall k, FinSet.mem positive_encoding k FinSet.empty = true ->
    (key_bits positive_encoding k <= 0)%N).
  { intros k Hmem; rewrite FinSet.mem_empty in Hmem; discriminate. }
  pose proof (FinSetCost.diff_numeric_cost positive_encoding FinSet.empty old_large 0
    (FinSet.wf_empty positive_encoding) Hwidth) as Hcost.
  rewrite N.mul_0_r, N.add_0_r, N.mul_1_r in Hcost; exact Hcost.
Qed.

