(** * Persistent union-find source observations

    Finite computations exercise erasure, rank branches, compression and input-work budgets.
    For example, sibling histories start from one unchanged forest and retain distinct results.
    Builds on: all six union-find adequacy leaves and the fixed collection audit models. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsUnionFind
  CollectionsAuditEncoding CollectionsAuditCallback CollectionsAuditUnionFind
  CollectionsAuditUnionFindAdapters CollectionsAuditUnionFindWhole CollectionsAuditEncoderBudget
  CollectionsAuditMapTraverse CollectionsAuditUnion CollectionsAuditElements
  CollectionsAuditHistorical CollectionsAuditAdaptedUFAdequacy CollectionsAuditContractsUFAdequacy
  CollectionsAuditHistoricalUFAdequacy CollectionsAuditUnionFindAdaptersAdequacy
  CollectionsAuditUnionFindAdequacy CollectionsAuditUnionFindWholeAdequacy.
Import List.ListNotations.

(** * Preserved source fixtures *)

(** A nontrivial union returns the original forest and incurs positive modeled source work. *)
Example audit_uf_union_observation :
  let result := audit_uf_union audit_positive_encode 1%positive 2%positive UnionFind.make in
  fst result = UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make /\
  Nat.ltb 0 (audit_uf_source_work audit_basic_encoding_work (snd result)) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Sibling histories both begin at the unchanged initial persistent forest. *)
Example audit_uf_branch_observation :
  let branches := audit_uf_branches audit_positive_encode
    [AuditUFUnion 1%positive 2%positive] [AuditUFFind 1%positive] UnionFind.make in
  fst (fst branches) = UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make /\
  fst (snd branches) = snd (UnionFind.find positive_encoding 1%positive UnionFind.make).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Support enumeration and a sequence of unions agree with the original library. *)
Example audit_uf_support_observation :
  let original := UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make in
  fst (@audit_uf_keys positive unit original) = UnionFind.keys positive_encoding original /\
  fst (audit_uf_of_unions audit_positive_encode [(1%positive, 2%positive)]) = original.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Empty, missing, duplicate and fuel boundaries *)

Definition uf_initial : UnionFind.t positive := UnionFind.make.

Definition uf_linked :=
  fst (audit_uf_union audit_positive_encode 1%positive 2%positive uf_initial).

Definition uf_ranked :=
  UnionFind.Forest Map.empty
    (Map.set positive_encoding 2%positive 2
      (Map.set positive_encoding 1%positive 1 Map.empty)) 2.

Definition uf_chain :=
  UnionFind.Forest
    (Map.set positive_encoding 1%positive 2%positive
      (Map.set positive_encoding 2%positive 3%positive Map.empty)) Map.empty 2.

Example uf_empty_observations :
  fst (audit_uf_history audit_positive_encode [] uf_initial) = uf_initial /\
  fst (audit_uf_of_unions audit_positive_encode []) = uf_initial /\
  fst (@audit_uf_keys positive unit uf_initial) = [] /\
  audit_uf_source_work audit_basic_encoding_work
    (snd (audit_uf_history audit_positive_encode [] uf_initial)) = 4.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example uf_find_missing_and_zero_fuel :
  fst (audit_uf_find_fuel audit_positive_encode 0 1%positive uf_chain) = (1%positive, uf_chain) /\
  fst (fst (audit_uf_find audit_positive_encode 7%positive uf_chain)) = 7%positive /\
  length (snd (audit_uf_find_fuel audit_positive_encode 0 1%positive uf_chain)) = 1 /\
  length (snd (audit_uf_find audit_positive_encode 7%positive uf_chain)) = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example uf_compression_and_fuel_boundary :
  fst (fst (audit_uf_find_fuel audit_positive_encode 1 1%positive uf_chain)) = 2%positive /\
  fst (fst (audit_uf_find_fuel audit_positive_encode 2 1%positive uf_chain)) = 3%positive /\
  Map.get positive_encoding 1%positive
    (UnionFind.parents (snd (fst (audit_uf_find audit_positive_encode 1%positive uf_chain)))) =
    Some 3%positive /\
  Map.get positive_encoding 1%positive (UnionFind.parents uf_chain) = Some 2%positive.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example uf_touch_missing_then_present :
  let first := audit_uf_union audit_positive_encode 1%positive 1%positive uf_initial in
  let second := audit_uf_union audit_positive_encode 1%positive 1%positive (fst first) in
  (Map.get positive_encoding 1%positive (UnionFind.ranks (fst first)),
    length (snd first), length (snd second)) = (Some 0, 9, 8).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_duplicate_union_keeps_class :
  let result := audit_uf_of_unions audit_positive_encode
    [(1%positive, 2%positive); (1%positive, 2%positive)] in
  fst (fst (audit_uf_equivb audit_positive_encode 1%positive 2%positive (fst result))) = true /\
  fst (fst (audit_uf_equivb audit_positive_encode 1%positive 7%positive (fst result))) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Every selected rank branch *)

Example uf_equal_rank_raises :
  (UnionFind.max_rank uf_linked,
    Map.get positive_encoding 2%positive (UnionFind.parents uf_linked),
    Map.get positive_encoding 1%positive (UnionFind.ranks uf_linked)) =
    (1, Some 1%positive, Some 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_lower_rank_links_left :
  let result := fst (audit_uf_union audit_positive_encode 1%positive 2%positive uf_ranked) in
  (Map.get positive_encoding 1%positive (UnionFind.parents result),
    UnionFind.max_rank result) = (Some 2%positive, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_higher_rank_links_right :
  let result := fst (audit_uf_union audit_positive_encode 2%positive 1%positive uf_ranked) in
  (Map.get positive_encoding 1%positive (UnionFind.parents result),
    UnionFind.max_rank result) = (Some 2%positive, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_history_threads_returned_forest :
  let result := audit_uf_history audit_positive_encode
    [AuditUFUnion 1%positive 2%positive; AuditUFFind 2%positive;
      AuditUFUnion 2%positive 3%positive] uf_initial in
  (Map.get positive_encoding 2%positive (UnionFind.parents (fst result)),
    Map.get positive_encoding 3%positive (UnionFind.parents (fst result))) =
    (Some 1%positive, Some 1%positive).
Proof.
  vm_compute; reflexivity.
Qed.

(** * Computed input-budget checks *)

Definition uf_bound_checks (forest : UnionFind.t positive) : list bool :=
  [Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_find_fuel audit_positive_encode 0 1%positive forest)))
     (audit_uf_find_input_budget audit_positive_encode (fun _ => 1) 0 1%positive forest);
   Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_find audit_positive_encode 1%positive forest)))
     (audit_uf_find_input_budget audit_positive_encode (fun _ => 1)
       (S (UnionFind.max_rank forest)) 1%positive forest);
   Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_union audit_positive_encode 1%positive 2%positive forest)))
     (audit_uf_union_input_budget audit_positive_encode (fun _ => 1) 1%positive 2%positive forest);
   Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_equivb audit_positive_encode 1%positive 2%positive forest)))
     (audit_uf_equivb_input_budget audit_positive_encode (fun _ => 1)
       1%positive 2%positive forest)].

Example uf_budget_checks_all_rank_branches :
  (uf_bound_checks uf_initial, uf_bound_checks uf_linked, uf_bound_checks uf_ranked,
    uf_bound_checks uf_chain) =
  ([true; true; true; true], [true; true; true; true],
    [true; true; true; true], [true; true; true; true]).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_insufficient_budget_rejected :
  Nat.leb (audit_uf_source_work audit_basic_encoding_work
    (snd (audit_uf_find audit_positive_encode 1%positive uf_initial))) 0 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition uf_keys_input_check (forest : UnionFind.t positive) : bool :=
  let parents := fst (audit_map_transform (fun _ : positive => (tt, @nil unit))
    (UnionFind.parents forest)) in
  let ranks := fst (audit_map_transform (fun _ : nat => (tt, @nil unit))
    (UnionFind.ranks forest)) in
  let merged := fst (audit_finset_union parents ranks) in
  Nat.leb (audit_uf_source_work audit_basic_encoding_work
    (snd (@audit_uf_keys positive (audit_basic_encoding_event positive) forest)))
    (23 + 18 * (audit_trie_nodes (UnionFind.parents forest) +
      audit_trie_nodes (UnionFind.ranks forest)) + 15 * audit_trie_nodes parents +
      19 * audit_trie_nodes merged + audit_trie_output_bits merged).

Example uf_keys_empty_and_nonempty_input_bounds :
  (uf_keys_input_check uf_initial, uf_keys_input_check uf_linked,
    uf_keys_input_check uf_chain) = (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_pair_and_list_empty_and_duplicate_results :
  fst (audit_uf_pair_of_unions audit_positive_encode audit_positive_encode []) =
    (@UnionFind.make (positive * positive)) /\
  fst (audit_uf_list_of_unions audit_positive_encode []) = (@UnionFind.make (list positive)) /\
  fst (audit_uf_pair_of_unions audit_positive_encode audit_positive_encode
    [((1%positive, 2%positive), (2%positive, 1%positive))]) =
    UnionFind.of_unions (pair_encoding positive_encoding positive_encoding)
      [((1%positive, 2%positive), (2%positive, 1%positive))] /\
  fst (audit_uf_list_of_unions audit_positive_encode
    [([1%positive; 1%positive], []); ([1%positive; 1%positive], [])]) =
    UnionFind.of_unions (list_encoding positive_encoding)
      [([1%positive; 1%positive], []); ([1%positive; 1%positive], [])].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** * Genuine actual-call foreign laws *)

Definition uf_foreign_encode (key : positive) : positive * list positive := (key, [key]).

(** The foreign relation retains the invoked key, returned code, exact body and charged work. *)
Definition uf_foreign_source (key code : positive) (body : list positive) (charged : nat) : Prop :=
  code = key /\ body = [key] /\ charged = 1.

Example uf_foreign_adapter :
  audit_external_callback_adapter uf_foreign_encode (@length positive)
    uf_foreign_source (fun _ => 1).
Proof.
  constructor; intros key code body Hcall; inversion Hcall; subst.
  - repeat split; reflexivity.
  - reflexivity.
Qed.

Example uf_adapted_nonempty_history :
  audit_uf_source_work (@length positive)
    (snd (audit_uf_history uf_foreign_encode
      [AuditUFUnion 1%positive 2%positive; AuditUFFind 2%positive] uf_initial)) <=
  audit_uf_history_input_budget uf_foreign_encode (fun _ => 1)
    [AuditUFUnion 1%positive 2%positive; AuditUFFind 2%positive] uf_initial.
Proof.
  exact ((proj2 (proj2 (proj2 (audit_uf_whole_input_bound_adapted
    positive positive uf_foreign_encode (@length positive) (fun _ => 1)
    uf_foreign_source uf_foreign_adapter)))) _ _).
Qed.

(** Both same-key touch branches and the reverse rank comparison satisfy their input bounds. *)
Example uf_other_union_budget_branches :
  (Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_union audit_positive_encode 1%positive 1%positive uf_initial)))
     (audit_uf_union_input_budget audit_positive_encode (fun _ => 1)
       1%positive 1%positive uf_initial),
   Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_union audit_positive_encode 1%positive 1%positive uf_linked)))
     (audit_uf_union_input_budget audit_positive_encode (fun _ => 1)
       1%positive 1%positive uf_linked),
   Nat.leb (audit_uf_source_work audit_basic_encoding_work
     (snd (audit_uf_union audit_positive_encode 2%positive 1%positive uf_ranked)))
     (audit_uf_union_input_budget audit_positive_encode (fun _ => 1)
       2%positive 1%positive uf_ranked)) = (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_whole_composite_budget_checks :
  let pair_inputs := [((1%positive, 2%positive), (2%positive, 1%positive))] in
  let list_inputs := [([1%positive; 1%positive], []); ([1%positive; 1%positive], [])] in
  (Nat.leb (audit_uf_source_work
     (audit_uf_pair_encoder_work audit_basic_encoding_work audit_basic_encoding_work)
     (snd (audit_uf_pair_of_unions audit_positive_encode audit_positive_encode pair_inputs)))
     (audit_uf_history_input_budget
       (audit_uf_pair_encode audit_positive_encode audit_positive_encode)
       (audit_pair_input_budget audit_positive_encode audit_positive_encode
         (fun _ => 1) (fun _ => 1))
       (map (fun xy => AuditUFUnion (fst xy) (snd xy)) pair_inputs) UnionFind.make),
   Nat.leb (audit_uf_source_work (audit_uf_list_encoder_work audit_basic_encoding_work)
     (snd (audit_uf_list_of_unions audit_positive_encode list_inputs)))
     (audit_uf_history_input_budget (audit_uf_list_encode audit_positive_encode)
       (audit_list_input_budget audit_positive_encode (fun _ => 1))
       (map (fun xy => AuditUFUnion (fst xy) (snd xy)) list_inputs) UnionFind.make)) =
    (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_branches_whole_budget_check :
  let left := [AuditUFFind 1%positive; AuditUFUnion 1%positive 2%positive] in
  let right := [AuditUFFind 2%positive; AuditUFUnion 2%positive 3%positive] in
  let branches := audit_uf_branches audit_positive_encode left right uf_chain in
  Nat.leb (audit_uf_source_work audit_basic_encoding_work (snd (fst branches)) +
    audit_uf_source_work audit_basic_encoding_work (snd (snd branches)))
    (audit_uf_history_input_budget audit_positive_encode (fun _ => 1) left uf_chain +
      audit_uf_history_input_budget audit_positive_encode (fun _ => 1) right uf_chain) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example uf_historical_result_and_branch_counters :
  let left := [UnionAction 1%positive 2%positive; FindAction 2%positive] in
  let right := [FindAction 3%positive] in
  fst (trace_actions positive_encoding left uf_initial) =
    fst (audit_uf_history audit_positive_encode
      [AuditUFUnion 1%positive 2%positive; AuditUFFind 2%positive] uf_initial) /\
  Nat.eqb (event_key_bits positive_encoding
    (trace_branches positive_encoding uf_initial left right))
    (event_key_bits positive_encoding (snd (trace_actions positive_encoding left uf_initial)) +
      event_key_bits positive_encoding (snd (trace_actions positive_encoding right uf_initial))) =
    true /\
  Nat.eqb (event_unary_total (trace_branches positive_encoding uf_initial left right))
    (event_unary_total (snd (trace_actions positive_encoding left uf_initial)) +
      event_unary_total (snd (trace_actions positive_encoding right uf_initial))) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example uf_adapted_pair_history :
  let inputs := [((1%positive, 2%positive), (2%positive, 1%positive))] in
  audit_uf_source_work (audit_uf_pair_encoder_work (@length positive) (@length positive))
    (snd (audit_uf_pair_of_unions uf_foreign_encode uf_foreign_encode inputs)) <=
    audit_uf_history_input_budget (audit_uf_pair_encode uf_foreign_encode uf_foreign_encode)
      (audit_pair_input_budget uf_foreign_encode uf_foreign_encode (fun _ => 1) (fun _ => 1))
      (map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs) UnionFind.make.
Proof.
  apply (audit_uf_pair_whole_input_bound_adapted _ _ _ _ _ _ _ _ _ _ _
    uf_foreign_source uf_foreign_source); exact uf_foreign_adapter.
Qed.

Example uf_adapted_list_history :
  let inputs := [([1%positive; 1%positive], [])] in
  audit_uf_source_work (audit_uf_list_encoder_work (@length positive))
    (snd (audit_uf_list_of_unions uf_foreign_encode inputs)) <=
    audit_uf_history_input_budget (audit_uf_list_encode uf_foreign_encode)
      (audit_list_input_budget uf_foreign_encode (fun _ => 1))
      (map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs) UnionFind.make.
Proof.
  apply (audit_uf_list_whole_input_bound_adapted _ _ _ _ _ _ uf_foreign_source).
  exact uf_foreign_adapter.
Qed.

Example uf_adapted_independent_branches :
  let left := [AuditUFUnion 1%positive 2%positive] in
  let right := [AuditUFFind 2%positive] in
  let branches := audit_uf_branches uf_foreign_encode left right uf_initial in
  audit_uf_source_work (@length positive) (snd (fst branches)) +
    audit_uf_source_work (@length positive) (snd (snd branches)) <=
    audit_uf_history_input_budget uf_foreign_encode (fun _ => 1) left uf_initial +
    audit_uf_history_input_budget uf_foreign_encode (fun _ => 1) right uf_initial.
Proof.
  apply (audit_uf_branches_whole_input_bound_adapted _ _ _ _ _ _ _ _ uf_foreign_source).
  exact uf_foreign_adapter.
Qed.
