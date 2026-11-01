(** * Checked observations of shared exact source counters

    These examples inspect actual values, callback payloads, body receipts and selected branches.
    For example, repeated false inputs retain two separate false-result callback bodies.
    Builds on: AnalysesAuditSource, its adequacy proofs and canonical collection encodings. *)

From Stdlib Require Import Bool List NArith PArith ZArith.
From Galois.Analyses Require Import AnalysesAuditSource AnalysesAuditSourceAdequacy
  AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditEncoding
  CollectionsEncoding CollectionsFinSet CollectionsMap CollectionsTrie.
Import List.ListNotations.

Example audit_bool_or_adapter_closed : audit_external_adapter_laws audit_bool_or_adapter.
Proof.
  intros [[] y]; repeat split; try reflexivity; try discriminate; constructor.
Qed.

Definition source_or (input : bool * bool) : exact_counted ((bool * bool) * bool) bool :=
  exact_external_call audit_bool_or_adapter input (fun result => (input,result)).

Example source_or_false_body :
  exact_bodies (source_or (false,false)) =
    [(((false,false),false),[ExternalCase 0; ExternalReturn])].
Proof.
  reflexivity.
Qed.

Example source_or_true_body :
  exact_bodies (source_or (true,false)) =
    [(((true,false),true),[ExternalCase 1; ExternalReturn])].
Proof.
  reflexivity.
Qed.

Example source_or_actual_output : exact_value (source_or (false,true)) = true.
Proof.
  reflexivity.
Qed.

Example source_or_positive_charge : exact_units (source_or (false,false)) = 192.
Proof.
  reflexivity.
Qed.

Example source_or_empty_body_rejected :
  ~ audit_external_body audit_bool_or_adapter (false,false) false [].
Proof.
  intros [_ Hnonempty]. apply Hnonempty. reflexivity.
Qed.

Example source_or_wrong_result_rejected :
  ~ audit_external_body audit_bool_or_adapter (true,false) false
      [ExternalCase 1; ExternalReturn].
Proof.
  intros [Hsource _]. inversion Hsource.
Qed.

Example source_or_wrong_branch_rejected :
  ~ audit_external_body audit_bool_or_adapter (false,false) false
      [ExternalCase 1; ExternalReturn].
Proof.
  intros [Hsource _]. inversion Hsource.
Qed.

Example source_or_same_invocation :
  audit_external_same_call audit_bool_or_adapter (false,false) false
    [ExternalCase 0; ExternalReturn].
Proof.
  split; [reflexivity|]. split.
  - split; [constructor|discriminate].
  - reflexivity.
Qed.

Example source_append_empty :
  @exact_value unit (list nat) (exact_append 7 [] [2;1]) = [2;1].
Proof.
  reflexivity.
Qed.

Example source_append_repeated :
  @exact_value unit (list nat) (exact_append 7 [1;1] [2]) = [1;1;2].
Proof.
  reflexivity.
Qed.

Example source_map_empty : exact_value (exact_map 8 source_or []) = [].
Proof.
  reflexivity.
Qed.

Definition source_repeated := exact_map 8 source_or [(false,false);(false,false);(true,false)].

Example source_map_values : exact_value source_repeated = [false;false;true].
Proof.
  reflexivity.
Qed.

Example source_map_occurrences : audit_calls (exact_events source_repeated) =
  [((false,false),false);((false,false),false);((true,false),true)].
Proof.
  reflexivity.
Qed.

Example source_map_body_order : map fst (exact_bodies source_repeated) =
  [((false,false),false);((false,false),false);((true,false),true)].
Proof.
  reflexivity.
Qed.

Example source_map_body_traces : map snd (exact_bodies source_repeated) =
  [[ExternalCase 0;ExternalReturn];[ExternalCase 0;ExternalReturn];
   [ExternalCase 1;ExternalReturn]].
Proof.
  reflexivity.
Qed.

Example source_lift_body_order :
  map fst (exact_bodies (exact_lift (fun call => (3,call)) source_repeated)) =
  [(3,((false,false),false));(3,((false,false),false));(3,((true,false),true))].
Proof.
  reflexivity.
Qed.

Definition source_left := exact_fold_left 9 (fun acc x => source_or (acc,x)) [true;false] false.

Definition source_right := exact_fold_right 9 (fun x acc => source_or (x,acc)) false [true;false].

Example source_left_states : audit_calls (exact_events source_left) =
  [((false,true),true);((true,false),true)].
Proof.
  reflexivity.
Qed.

Example source_right_states : audit_calls (exact_events source_right) =
  [((false,false),false);((true,false),true)].
Proof.
  reflexivity.
Qed.

Example source_empty_left : exact_value
  (exact_fold_left 9 (fun acc x => source_or (acc,x)) [] false) = false.
Proof.
  reflexivity.
Qed.

Example source_empty_right : exact_value
  (exact_fold_right 9 (fun x acc => source_or (x,acc)) false []) = false.
Proof.
  reflexivity.
Qed.

Definition source_inject (call : exact_map_call positive nat) := call.

Definition source_table : Map.t positive nat :=
  Map.set positive_encoding 3%positive 9 (Map.set positive_encoding 1%positive 0 Map.empty).

Definition source_malformed : Map.t positive nat := Trie.set 1%positive (7%positive,0) Trie.empty.

Example source_missing_key : exact_value
  (exact_get source_inject positive_encoding (fun _ => 0) 2%positive source_table) = None.
Proof.
  reflexivity.
Qed.

Example source_reached_bottom : exact_value
  (exact_get source_inject positive_encoding (fun _ => 0) 1%positive source_table) = Some 0.
Proof.
  reflexivity.
Qed.

Example source_malformed_position : exact_value
  (exact_get source_inject positive_encoding (fun _ => 0) 1%positive source_malformed) = Some 0.
Proof.
  reflexivity.
Qed.

Example source_malformed_stored_key : exact_value
  (exact_get source_inject positive_encoding (fun _ => 0) 7%positive source_malformed) = None.
Proof.
  reflexivity.
Qed.

Example source_get_payload : audit_calls (exact_events
  (exact_get source_inject positive_encoding (fun _ => 0) 1%positive source_malformed)) =
  [ExactEncode 1%positive 1%positive;
   ExactGet 1%positive 1%positive source_malformed (Some 0)].
Proof.
  reflexivity.
Qed.

Example source_set_last_occurrence : Map.get positive_encoding 1%positive (exact_value
  (exact_set source_inject positive_encoding (fun _ => 0) 1%positive 4 source_table)) = Some 4.
Proof.
  reflexivity.
Qed.

Example source_remove_present : Map.get positive_encoding 1%positive (exact_value
  (exact_remove source_inject positive_encoding (fun _ => 0) 1%positive source_table)) = None.
Proof.
  reflexivity.
Qed.

Example source_remove_missing : exact_value
  (exact_remove source_inject positive_encoding (fun _ => 0) 2%positive source_table) =
  source_table.
Proof.
  reflexivity.
Qed.

Example source_elements_order : exact_value (exact_elements source_inject source_table) =
  [(1%positive,0);(3%positive,9)].
Proof.
  reflexivity.
Qed.

Example source_elements_malformed : exact_value (exact_elements source_inject source_malformed) =
  [(7%positive,0)].
Proof.
  reflexivity.
Qed.

Example source_elements_empty : exact_value (exact_elements source_inject Map.empty) = [].
Proof.
  reflexivity.
Qed.

Example source_filter_branches : exact_value
  (exact_filter 10 (fun x => source_or (x,false)) [true;false;true]) = [true;true].
Proof.
  reflexivity.
Qed.

Example source_all_reaches_later : audit_calls (exact_events
  (exact_all 11 (fun x => source_or (x,false)) [false;true])) =
  [((false,false),false);((true,false),true)].
Proof.
  reflexivity.
Qed.

Example source_reverse_order :
  @exact_value unit (list nat) (exact_rev 12 [1;2;1;3]) = [3;1;2;1].
Proof.
  reflexivity.
Qed.

Example source_flat_map_order : @exact_value unit (list nat)
  (exact_flat_map 13 (fun n => exact_return 13 [n;n]) [1;2]) = [1;1;2;2].
Proof.
  reflexivity.
Qed.

Example source_pair_code : fst (audit_pair_encode (pre_external_encode bool_encoding)
  (pre_external_encode bool_encoding) (false,true)) =
  encode (pair_encoding bool_encoding bool_encoding) (false,true).
Proof.
  reflexivity.
Qed.

Example source_pair_retains_components :
  firstn 2 (snd (audit_pair_encode (pre_external_encode bool_encoding)
    (pre_external_encode bool_encoding) (false,true))) =
  [AuditPairFirst false 1%positive [(false,1%positive)];
   AuditPairSecond true 2%positive [(true,2%positive)]].
Proof.
  reflexivity.
Qed.

Example source_triple_code : fst
  (pre_triple_source_encoding bool_encoding bool_encoding bool_encoding ((true,false),true)) =
  encode (pair_encoding (pair_encoding bool_encoding bool_encoding) bool_encoding)
    ((true,false),true).
Proof.
  reflexivity.
Qed.

Example source_frg_unavailable_code : fst
  (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding (FrUnavailable false)) =
  2%positive.
Proof.
  reflexivity.
Qed.

Example source_frg_initial_code : fst
  (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding (FrInitial false)) =
  5%positive.
Proof.
  reflexivity.
Qed.

Example source_frg_fresh_code : fst
  (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding (FrFresh true false)) =
  encode (frg_version_encoding bool_encoding bool_encoding bool_encoding) (FrFresh true false).
Proof.
  reflexivity.
Qed.

Example source_frg_phi_code : fst
  (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding (FrPhi false true)) =
  encode (frg_version_encoding bool_encoding bool_encoding bool_encoding) (FrPhi false true).
Proof.
  reflexivity.
Qed.

Example source_external_frame_branches :
  map audit_external_frame_work
    [ExternalReturn;ExternalCase 0;ExternalConstruct 1;ExternalBinary 0 0;
     ExternalMultiply 0 0;ExternalDivide 0 0;ExternalEmit 1%positive;ExternalUnary 0] =
  [64;64;64;67;66;69;66;65].
Proof.
  reflexivity.
Qed.

Example source_set_repeats :
  FinSet.elements (exact_value (exact_set_of_list (fun call => call)
    positive_encoding (fun _ => 0) [1%positive;3%positive;1%positive])) =
  [1%positive;3%positive].
Proof.
  reflexivity.
Qed.

Example source_set_present : exact_value (exact_set_mem (fun call => call)
  positive_encoding (fun _ => 0) 1%positive (FinSet.of_list positive_encoding [1%positive])) = true.
Proof.
  reflexivity.
Qed.

Example source_set_absent : exact_value (exact_set_mem (fun call => call)
  positive_encoding (fun _ => 0) 2%positive (FinSet.of_list positive_encoding [1%positive])) =
  false.
Proof.
  reflexivity.
Qed.

Definition source_all_shapes : Map.t positive nat :=
  Trie.Nodes
    (Trie.N111
      (Trie.N101
        (Trie.N100 (Trie.N010 (10%positive,1)))
        (Trie.N011 (11%positive,2) (Trie.N010 (12%positive,3))))
      (13%positive,4)
      (Trie.N110 (Trie.N001 (Trie.N010 (14%positive,5))) (15%positive,6))).

Example source_all_trie_shapes : exact_trie_nodes source_all_shapes = 10.
Proof.
  reflexivity.
Qed.

Example source_all_trie_shapes_order :
  exact_value (exact_elements source_inject source_all_shapes) =
  [(10%positive,1);(11%positive,2);(12%positive,3);(13%positive,4);(14%positive,5);(15%positive,6)].
Proof.
  reflexivity.
Qed.

Example source_frg_unavailable_receipt : snd
  (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding (FrUnavailable false)) =
  [AuditSumLeft false 1%positive [(false,1%positive)]].
Proof.
  reflexivity.
Qed.

Example source_frg_initial_receipt : snd
  (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding (FrInitial false)) =
  [AuditSumRight (inl false) 2%positive [AuditSumLeft false 1%positive [(false,1%positive)]]].
Proof.
  reflexivity.
Qed.

Example source_pair_work_observation :
  audit_pair_events_work (pre_external_encode_work (fun _ => 7))
    (pre_external_encode_work (fun _ => 11))
    (snd (audit_pair_encode (pre_external_encode bool_encoding)
      (pre_external_encode bool_encoding) (false,true))) = 53.
Proof.
  reflexivity.
Qed.

Example source_triple_work_observation :
  pre_triple_source_work (fun _ => 7) (fun _ => 11) (fun _ => 13)
    (snd (pre_triple_source_encoding bool_encoding bool_encoding bool_encoding
      ((true,false),true))) = 161.
Proof.
  reflexivity.
Qed.

Example source_frg_fresh_selected_work :
  pre_frg_source_work (fun _ => 1000) (fun _ => 7) (fun _ => 11)
    (snd (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding
      (FrFresh true false))) = 56.
Proof.
  reflexivity.
Qed.

Example source_frg_phi_selected_work :
  pre_frg_source_work (fun _ => 13) (fun _ => 1000) (fun _ => 11)
    (snd (pre_frg_source_encoding bool_encoding bool_encoding bool_encoding
      (FrPhi false true))) = 62.
Proof.
  reflexivity.
Qed.
