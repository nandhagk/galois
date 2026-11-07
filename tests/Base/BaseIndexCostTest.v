(** * Index cost clients

    These clients use primitive cost contracts without unfolding an index.
    For example, reversal pays exactly the bucket length.
    Builds on: BaseIndex. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
Import List.ListNotations.

Example index_find_cost_client {K V} (E : encoding K) k (idx : Index.t K V) :
  Cost.ticks (Index.find_c E k idx) = Cost.ticks (Map.get_c E k idx).
Proof.
  apply Index.find_cost.
Qed.

Example index_reverse_counts :
  (Cost.ticks (Index.reverse_c [1; 2; 3]), Cost.ticks (Index.reverse_c ([] : list nat))) =
    (3, 0)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example index_empty_count :
  Cost.ticks (Index.group_by_c bool_encoding
    (Cost.lift (fun _ => 1%N) Nat.even) []) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.
