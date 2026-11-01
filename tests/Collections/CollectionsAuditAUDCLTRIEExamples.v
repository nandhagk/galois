(** * Literal trie adequacy observations

    These computations distinguish empty paths, missing keys, duplicate insertions and
    strict update charges. For example, an absent width-three lookup still emits six events.
    Builds on: the trie, map, set, primitive and comparison audit adequacy modules. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost CollectionsAuditTrie CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditCompare
  CollectionsAuditTrieAdequacy CollectionsAuditFinSetAdequacy CollectionsAuditMapAdequacy
  CollectionsAuditPrimitiveAdequacy CollectionsAuditCompareAdequacy.
Import List.ListNotations.

(** The preserved canonical empty fixture follows all three key bits. *)
Example audit_empty_lookup_observation :
  fst (audit_trie_get 5%positive (@Trie.empty nat)) = None /\
  length (snd (audit_trie_get 5%positive (@Trie.empty nat))) = 6.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The preserved duplicate fixture keeps separate insertions but one enumerated member. *)
Example audit_duplicate_set_observation :
  let built := audit_finset_of_list audit_positive_encode [1%positive; 1%positive] in
  length (snd built) = 5 /\ FinSet.elements (fst built) = [1%positive].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audit_empty_set_fold :
  let built := audit_finset_of_list audit_positive_encode [] in
  fst built = (@FinSet.empty positive) /\ length (snd built) = 1 /\
  audit_finset_source_work (fun events => length events) (snd built) = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audit_trie_boundary_update_and_remove :
  let inserted := fst (audit_trie_set 1%positive 7 (@Trie.empty nat)) in
  (fst (audit_trie_get 1%positive inserted),
   fst (audit_trie_remove 1%positive inserted),
   fst (audit_trie_remove 2%positive inserted)) = (Some 7, Trie.empty, inserted).
Proof.
  reflexivity.
Qed.

Example audit_trie_duplicate_replacement :
  let first := fst (audit_trie_set 2%positive 7 (@Trie.empty nat)) in
  let second := fst (audit_trie_set 2%positive 9 first) in
  (fst (audit_trie_get 2%positive second), fst (audit_trie_get 3%positive second)) =
    (Some 9, None).
Proof.
  reflexivity.
Qed.

Example audit_trie_empty_source_charges :
  (audit_trie_get_source_work 1%positive (@Trie.empty nat),
   audit_trie_get_source_work 5%positive (@Trie.empty nat),
   audit_trie_update_source_work 1%positive None (@Trie.empty nat),
   audit_trie_update_source_work 1%positive (Some 7) Trie.empty) = (3, 11, 11, 12).
Proof.
  reflexivity.
Qed.

Example audit_trie_nonempty_source_charges :
  let input := Trie.node Trie.empty (Some 7) Trie.empty in
  (audit_trie_get_source_work 1%positive input,
   audit_trie_update_source_work 1%positive None input,
   audit_trie_update_trace_source_work (snd (audit_trie_remove 1%positive input))) = (4, 13, 13).
Proof.
  reflexivity.
Qed.

Example audit_primitive_accessors :
  let leaf := Trie.node Trie.empty (Some 7) Trie.empty in
  let input := Trie.node leaf (Some 9) leaf in
  (audit_trie_left_source input, audit_trie_right_source input,
   audit_trie_value_source input, audit_trie_value_source (@Trie.empty nat)) =
    ((leaf, 2), (leaf, 2), (Some 9, 2), (None, 1)).
Proof.
  reflexivity.
Qed.

Example audit_primitive_node_empty_boundary :
  (audit_trie_node_source (@Trie.empty nat) None Trie.empty,
   audit_trie_node_source Trie.empty (Some 7) Trie.empty) =
    ((Trie.empty, 4), (Trie.Nodes (Trie.N010 7), 5)).
Proof.
  reflexivity.
Qed.

Example audit_map_present_missing_and_duplicate :
  let first := fst (audit_map_set audit_positive_encode 2%positive 7 Map.empty) in
  let second := fst (audit_map_set audit_positive_encode 2%positive 9 first) in
  (fst (audit_map_get audit_positive_encode 2%positive second),
   fst (audit_map_get audit_positive_encode 3%positive second),
   fst (audit_map_remove audit_positive_encode 3%positive second)) =
    (Some 9, None, second).
Proof.
  reflexivity.
Qed.

Example audit_map_removal_threads_result :
  let first := fst (audit_map_set audit_positive_encode 3%positive 7 Map.empty) in
  let removed := fst (audit_map_remove audit_positive_encode 3%positive first) in
  fst (audit_map_get audit_positive_encode 3%positive removed) = None /\ removed = Map.empty.
Proof.
  split; reflexivity.
Qed.

Example audit_map_projection_preserves_actual_position :
  let malformed := Trie.set 2%positive (3%positive, 7) Trie.empty in
  fst (audit_map_code_get 2%positive malformed) = Some 7.
Proof.
  reflexivity.
Qed.

Example audit_finset_membership_all_outcomes :
  let input := fst (audit_finset_of_list audit_positive_encode [1%positive; 2%positive]) in
  let removed := fst (audit_finset_remove audit_positive_encode 1%positive input) in
  (fst (audit_finset_mem audit_positive_encode 1%positive FinSet.empty),
   fst (audit_finset_mem audit_positive_encode 1%positive input),
   fst (audit_finset_mem audit_positive_encode 3%positive input),
   fst (audit_finset_mem audit_positive_encode 1%positive removed),
   fst (audit_finset_mem audit_positive_encode 2%positive removed)) =
    (false, true, false, false, true).
Proof.
  reflexivity.
Qed.

Example audit_eqb_equal_distinct_and_boundary :
  (fst (audit_positive_eqb 1%positive 1%positive),
   fst (audit_positive_eqb 2%positive 3%positive),
   fst (audit_positive_eqb 5%positive 5%positive),
   length (snd (audit_positive_eqb 2%positive 3%positive)),
   length (snd (audit_positive_eqb 5%positive 5%positive))) = (true, false, true, 1, 3).
Proof.
  reflexivity.
Qed.

Example audit_order_equal_less_greater :
  (fst (audit_positive_ltb 1%positive 1%positive),
   fst (audit_positive_leb 1%positive 1%positive),
   fst (audit_positive_ltb 2%positive 3%positive),
   fst (audit_positive_leb 3%positive 2%positive),
   length (snd (CollectionsAuditCompare.audit_positive_compare 2%positive 3%positive))) =
    (false, true, true, false, 2).
Proof.
  reflexivity.
Qed.

Example audit_compare_continuation_boundary :
  (fst (CollectionsAuditCompare.audit_positive_compare_cont Gt 1%positive 1%positive),
   fst (CollectionsAuditCompare.audit_positive_compare_cont Lt 3%positive 3%positive)) = (Gt, Lt).
Proof.
  reflexivity.
Qed.

Example audit_empty_lookup_source_run :
  audit_trie_get_run 1%positive (@Trie.empty nat) None
    [AuditCall (AuditTrieKey 1%positive Trie.empty);
     AuditCall (AuditTrieValue Trie.empty None)] 3.
Proof.
  exact (@AuditGetHere nat Trie.empty).
Qed.

Example audit_nonempty_update_source_run :
  let input := Trie.node Trie.empty (Some 7) Trie.empty in
  let observed := audit_trie_update 2%positive (Some 9) input in
  audit_trie_update_run 2%positive (Some 9) input (fst observed) (snd observed) 28.
Proof.
  refine (@AuditUpdateLeft nat 1%positive (Some 9)
    (Trie.node Trie.empty (Some 7) Trie.empty) _ _ 12 _).
  exact (@AuditUpdateHere nat (Some 9) Trie.empty).
Qed.

Example audit_map_projection_source_run :
  let input := Trie.node Trie.empty (Some (3%positive, 7)) Trie.empty in
  let observed := audit_map_code_get 1%positive input in
  audit_map_code_get_run 1%positive input (fst observed) (snd observed) 8.
Proof.
  refine (@AuditMapCodeGet positive nat 1%positive
    (Trie.node Trie.empty (Some (3%positive, 7)) Trie.empty) (Some (3%positive, 7)) _ 4 _).
  exact (@AuditGetHere (positive * nat)%type
    (Trie.node Trie.empty (Some (3%positive, 7)) Trie.empty)).
Qed.
