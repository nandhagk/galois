(** * Index cost clients

    These clients use primitive cost contracts without unfolding an index.
    For example, reversal pays exactly the bucket length.
    Builds on: BaseIndex. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMapCost BaseIndex BaseIndexCost.
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

Example index_grouping_counts :
  (Cost.ticks (Index.group_by_c bool_encoding
    (Cost.lift (fun _ => 1%N) Nat.even) [2; 1; 4; 3]),
    Cost.ticks (Index.group_by_c bool_encoding
    (Cost.lift (fun _ => 1%N) Nat.even) [2; 1; 4; 3; 6; 5; 8; 7])) = (52, 100)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example index_double_input :
  (Cost.ticks (Index.group_by_c bool_encoding
    (Cost.lift (fun _ => 1%N) Nat.even) [2; 1; 4; 3; 6; 5; 8; 7]%nat) <=
    2 * Cost.ticks (Index.group_by_c bool_encoding
      (Cost.lift (fun _ => 1%N) Nat.even) [2; 1; 4; 3]%nat))%N.
Proof.
  vm_compute. discriminate.
Qed.

Example map_skeleton_boundary :
  (MapCost.skeleton_nodes (Map.set positive_encoding 8%positive 7 Map.empty),
    Map.size (Map.set positive_encoding 8%positive 7 Map.empty)) = (4%N, 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example map_empty_mapping :
  Cost.ticks (Map.map_c (Cost.lift (fun _ => 100%N) S) (@Map.empty nat nat)) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_callback_count :
  Cost.ticks (Map.map_c (Cost.lift (fun _ => 100%N) S)
    (Map.set positive_encoding 8%positive 7 Map.empty)) = 105%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_update_callback_count :
  Cost.ticks (Map.update_c nat_encoding 0
    (fun _ => Cost.lift (fun _ => 100%N) (@Some nat) 7) Map.empty) = 107%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_remove_callback_count :
  Cost.ticks (Map.update_c nat_encoding 0
    (fun _ => Cost.lift (fun _ => 100%N) (fun _ => None) tt)
    (@Map.empty nat nat)) = 107%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example index_missing_lookup_ticks :
  (Index.find bool_encoding false
    (Index.group_by bool_encoding Nat.even [2; 4]),
    Cost.ticks (Index.find_c bool_encoding false
      (Index.group_by bool_encoding Nat.even [2; 4]))) = ([], 3%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example index_numeric_bound_client {K V} (E : encoding K) (HE : encoding_laws E)
    (key_c : V -> Cost.t K) xs e b c :
  (forall x, In x xs ->
    (Cost.ticks (key_c x) <= c)%N /\
    (Cost.ticks (encode_c E (Cost.value (key_c x))) <= e)%N /\
    (key_bits E (Cost.value (key_c x)) <= b)%N) ->
  (Cost.ticks (Index.group_by_c E key_c xs) <=
    1 + N.of_nat (length xs) * (6 + c + 2 * e + 4 * b))%N.
Proof.
  apply (IndexCost.group_by_cost Map.cost_laws_hold E HE).
Qed.

Example map_numeric_bound_client {K V W} (E : encoding K) (f_c : V -> Cost.t W)
    (m : Map.t K V) b :
  Map.wf E m ->
  (forall k v, Map.get E k m = Some v -> (key_bits E k <= b)%N) ->
  (Cost.ticks (Map.map_c f_c m) <= 1 + 2 * N.of_nat (Map.size m) * b +
    fold_right (fun kv n => Cost.ticks (f_c (snd kv)) + n)%N 0%N (Map.elements m))%N.
Proof.
  apply MapCost.map_numeric_cost.
Qed.
