(** * Collection family closure observations

    These examples connect the ten composed proofs to representative empty, populated and
    boundary collection observations. For example, duplicate insertion keeps one set member,
    while a missing map lookup remains absent.
    Builds on: collection family closure adequacy and fixed collection audit models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditEncoding CollectionsAuditTrie CollectionsAuditMap
  CollectionsAuditFinSet CollectionsAuditFamilyClosure
  CollectionsAuditFamilyClosureAdequacy.
Import List.ListNotations.

(** * Family closure and finite observations *)

(** Every exported family theorem is consumed at its exact public contract type. *)
Example audit_cl_family_roots :
  audit_cl_primitive_erasure_closure_statement /\
  audit_cl_source_work_closure_statement /\
  audit_cl_composite_union_find_closure_statement /\
  audit_cl_full_source_contract_statement /\
  audit_cl_literal_body_closure_statement /\
  audit_cl_whole_input_closure_statement /\
  audit_cl_complete_source_contract_statement /\
  audit_cl_adapted_source_contract_statement /\
  audit_cl_dense_whole_source_contract_statement /\
  audit_cl_public_source_contract_statement.
Proof.
  split; [exact audit_cl_primitive_erasure_closure |].
  split; [exact audit_cl_source_work_closure |].
  split; [exact audit_cl_composite_union_find_closure |].
  split; [exact audit_cl_full_source_contract |].
  split; [exact audit_cl_literal_body_closure |].
  split; [exact audit_cl_whole_input_closure |].
  split; [exact audit_cl_complete_source_contract |].
  split; [exact audit_cl_adapted_source_contract |].
  split; [exact audit_cl_dense_whole_source_contract |].
  exact audit_cl_public_source_contract.
Qed.

(** Empty and populated tries distinguish missing from present values at boundary keys. *)
Example audit_cl_trie_empty_nonempty_boundary :
  fst (audit_trie_get 1%positive (@Trie.empty nat)) = None /\
  fst (audit_trie_get 1%positive (fst (audit_trie_set 1%positive 7 Trie.empty))) = Some 7 /\
  fst (audit_trie_get 2%positive (fst (audit_trie_set 1%positive 7 Trie.empty))) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Duplicate set inputs preserve one member, while empty input stays empty. *)
Example audit_cl_duplicate_and_empty_sets :
  FinSet.elements (fst (audit_finset_of_list audit_positive_encode [])) = [] /\
  FinSet.elements
    (fst (audit_finset_of_list audit_positive_encode [1%positive; 1%positive])) =
    [1%positive].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A map overwrite updates the present key and leaves an absent boundary key missing. *)
Example audit_cl_map_duplicate_and_missing :
  let initial := Map.set positive_encoding 1%positive 7 (@Map.empty positive nat) in
  let overwritten := Map.set positive_encoding 1%positive 9 initial in
  (Map.get positive_encoding 1%positive overwritten,
   Map.get positive_encoding 2%positive overwritten,
   Map.get positive_encoding 1%positive (@Map.empty positive nat)) =
    (Some 9, None, None).
Proof.
  vm_compute; reflexivity.
Qed.

(** Zero and a binary carry boundary remain ordinary natural encoder inputs. *)
Example audit_cl_encoder_boundary :
  fst (audit_nat_encode 0) = 1%positive /\
  fst (audit_nat_encode 7) = 8%positive.
Proof.
  vm_compute; split; reflexivity.
Qed.
