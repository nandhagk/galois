(** * Collection traversal observations

    These computations retain the source fixtures for enumeration and set operations.
    For example, duplicate insertions enumerate one key through the counted traversal.
    Builds on: the collection traversal audit models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditUnion
  CollectionsAuditInter CollectionsAuditMapFold CollectionsAuditMapTraverse
  CollectionsAuditTraversalBudget.
Import List.ListNotations.

(** Duplicate insertions retain their count and the counted enumeration order. *)
Example audit_duplicate_set_observation :
  let built := audit_finset_of_list audit_positive_encode [1%positive; 1%positive] in
  length (snd built) = 5 /\ fst (audit_finset_elements (fst built)) = [1%positive].
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** An empty right union retains the left subtree. *)
Example audit_union_empty_observation :
  let singleton := FinSet.add positive_encoding 1%positive FinSet.empty in
  fst (audit_finset_union singleton FinSet.empty) = singleton /\
  length (snd (audit_finset_union singleton FinSet.empty)) = 2.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** An empty intersection records the one-sided filter traversal. *)
Example audit_intersection_empty_observation :
  let singleton := FinSet.add positive_encoding 1%positive FinSet.empty in
  let result := audit_finset_inter singleton FinSet.empty in
  fst result = FinSet.empty /\ length (snd result) = 5.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** Equal and distinct singleton intersections retain their actual results. *)
Example audit_intersection_singleton_observation :
  let one := FinSet.add positive_encoding 1%positive FinSet.empty in
  let two := FinSet.add positive_encoding 2%positive FinSet.empty in
  fst (audit_finset_inter one one) = FinSet.inter positive_encoding one one /\
  fst (audit_finset_inter one two) = FinSet.inter positive_encoding one two.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** Empty enumeration includes the terminating reverse and projection frames. *)
Example audit_empty_enumeration :
  fst (audit_finset_elements (@FinSet.empty positive)) = [] /\
  length (snd (audit_finset_elements (@FinSet.empty positive))) = 3.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Union retains both distinct input members and intersection rejects the missing member. *)
Example audit_union_and_intersection_members :
  let one := FinSet.add positive_encoding 1%positive FinSet.empty in
  let two := FinSet.add positive_encoding 2%positive FinSet.empty in
  let union := fst (audit_finset_union one two) in
  let inter := fst (audit_finset_inter one two) in
  (FinSet.mem positive_encoding 1%positive union,
   FinSet.mem positive_encoding 2%positive union,
   FinSet.mem positive_encoding 1%positive inter) = (true, true, false).
Proof.
  reflexivity.
Qed.

(** Map callbacks run for each stored value and fold threads their returned accumulator. *)
Example audit_map_traversal_callbacks :
  let input := Map.set positive_encoding 2%positive 4
    (Map.set positive_encoding 1%positive 3 Map.empty) in
  let transformed := audit_map_transform (fun v => (S v, [v])) input in
  let folded := audit_map_fold (fun acc _ v => (acc + v, [acc])) input 0 in
  (Map.get positive_encoding 1%positive (fst transformed),
   Map.get positive_encoding 2%positive (fst transformed), fst folded,
   length (snd folded)) = (Some 4, Some 5, 7, 4).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Overlapping union calls the combiner and retains disjoint entries from both sides. *)
Example audit_map_union_overlap :
  let left := Map.set positive_encoding 1%positive 3 Map.empty in
  let right := Map.set positive_encoding 2%positive 7
    (Map.set positive_encoding 1%positive 4 Map.empty) in
  let merged := audit_map_union (fun x y => (x + y, [x; y])) left right in
  (Map.get positive_encoding 1%positive (fst merged),
   Map.get positive_encoding 2%positive (fst merged),
   Map.get positive_encoding 3%positive (fst merged)) = (Some 7, Some 7, None).
Proof.
  reflexivity.
Qed.

(** Counted enumeration work stays within the input-derived bounds for two distinct keys. *)
Example audit_enumeration_work_observation :
  let input := fst (audit_finset_of_list audit_positive_encode [1%positive; 2%positive]) in
  Nat.leb (audit_set_elements_work (snd (audit_finset_elements input)))
    (19 * audit_trie_nodes input + audit_trie_output_bits input + 6) = true.
Proof.
  reflexivity.
Qed.

(** Intersection and union charge the empty and nonempty inputs within their source bounds. *)
Example audit_set_merge_work_observation :
  let one := FinSet.add positive_encoding 1%positive FinSet.empty in
  let two := FinSet.add positive_encoding 2%positive FinSet.empty in
  (Nat.leb (audit_finset_inter_source_work (snd (audit_finset_inter one two)))
     (2 + 30 * (audit_trie_nodes one + audit_trie_nodes two)),
   Nat.leb (audit_finset_union_source_work (snd (audit_finset_union one two)))
     (1 + 15 * audit_trie_nodes one)) = (true, true).
Proof.
  reflexivity.
Qed.

(** Callback work is bounded by actual input values, including an overlapping union. *)
Example audit_adapted_traversal_work_observation :
  let left := Map.set positive_encoding 1%positive 3 Map.empty in
  let right := Map.set positive_encoding 1%positive 4 Map.empty in
  let mapper := fun v => (S v, [v]) in
  let combiner := fun x y => (x + y, [x; y]) in
  let folder := fun acc (_ : positive) v => (acc + v, [acc]) in
  (Nat.leb (audit_map_transform_source_work (@length nat)
     (snd (audit_map_transform mapper left)))
     (audit_map_transform_input_budget (fun _ => 1) left),
   Nat.leb (audit_map_union_source_work (@length nat)
     (snd (audit_map_union combiner left right)))
     (audit_map_union_input_budget (fun _ => 2) left right),
   Nat.leb (audit_map_fold_source_work (@length nat) (snd (audit_map_fold folder left 0)))
     (audit_map_fold_input_budget folder (fun _ => 1) left 0)) = (true, true, true).
Proof.
  reflexivity.
Qed.

(** The callback trace records the actual input, result and retained body. *)
Example audit_transform_callback_source_observation :
  let input := Map.set positive_encoding 1%positive 3 Map.empty in
  let events := snd (audit_map_transform (fun v => (S v, [v])) input) in
  audit_map_transform_calls_source (@length nat)
    (fun value result body cost => result = S value /\ body = [value] /\ cost = 1) events.
Proof.
  vm_compute; repeat constructor; reflexivity.
Qed.
