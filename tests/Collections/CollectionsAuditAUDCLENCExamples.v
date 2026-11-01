(** * Encoder adequacy observations

    These examples exercise concrete encoder traces, prepared keys and callback accounting.
    For example, duplicate list elements retain separate component calls.
    Builds on: collection encoder models and their adequacy proofs. *)

From Stdlib Require Import List NArith PArith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditState
  CollectionsAuditEncoding CollectionsAuditEncoderBudget CollectionsAuditCallback
  CollectionsAuditAdapted CollectionsAuditComposite CollectionsAuditEncodingAdequacy
  CollectionsAuditStateENCAdequacy CollectionsAuditCompositeAdequacy
  CollectionsAuditEncoderBudgetAdequacy CollectionsAuditCallbackAdequacy
  CollectionsAuditAdaptedENCAdequacy.
Import List.ListNotations.

(** * Primitive and composite observations *)

Example audit_encoder_boundary_observations :
  fst (audit_nat_encode 0) = 1%positive /\
  fst (audit_nat_encode 3) = 4%positive /\
  fst (audit_positive_succ 7%positive) = 8%positive /\
  length (snd (audit_positive_succ 7%positive)) = 3 /\
  fst (audit_N_encode 0%N) = 1%positive /\
  fst (audit_N_encode 7%N) = 8%positive /\
  fst (audit_z_encode (-1)%Z) = 3%positive.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_encoder_empty_and_duplicate_lists :
  fst (audit_list_encode audit_positive_encode []) = 1%positive /\
  length (snd (audit_list_encode audit_positive_encode [])) = 2 /\
  audit_encoded_bits audit_positive_encode [1%positive; 1%positive] = 2 /\
  length (snd (audit_list_encode audit_positive_encode [1%positive; 1%positive])) = 12 /\
  audit_list_input_budget audit_positive_encode (fun _ => 1)
    [1%positive; 1%positive] = 30.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_encoder_sum_option_branches :
  fst (audit_option_encode audit_positive_encode None) = 1%positive /\
  fst (audit_option_encode audit_positive_encode (Some 2%positive)) = 4%positive /\
  fst (audit_sum_encode audit_positive_encode audit_positive_encode (inl 2%positive)) =
    4%positive /\
  fst (audit_sum_encode audit_positive_encode audit_positive_encode (inr 2%positive)) =
    5%positive.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_encoder_pair_width_and_work :
  let key := prepare_key (pair_encoding positive_encoding positive_encoding)
    (1%positive, 8%positive) in
  prepared_key_bits key = 11 /\
  composite_stream_nodes
    (CollectionsAuditComposite.prepared_pair_work positive_encoding positive_encoding
      (CompositeCosts positive positive (fun _ => 1) (fun _ => 1)) 1%positive 8%positive) = 11 /\
  audit_pair_input_budget audit_positive_encode audit_positive_encode
    (fun _ => 1) (fun _ => 1) (1%positive, 8%positive) = 57.
Proof.
  repeat split; reflexivity.
Qed.

(** * Prepared map observations *)

Example audit_prepared_missing_and_overwrite :
  let key := prepare_key positive_encoding 2%positive in
  let missing := prepare_key positive_encoding 3%positive in
  let first := prepared_update key 7 (@Map.empty positive nat) in
  let second := prepared_update key 9 first in
  prepared_lookup key second = Some 9 /\
  prepared_lookup missing second = None /\
  prepared_lookup key (prepared_remove key second) = None.
Proof.
  repeat split; reflexivity.
Qed.

(** * Actual callback body *)

Definition sample_callback (p : positive) : positive * list positive := (p, [p]).

Definition sample_callback_source (p result : positive) (body : list positive) (work : nat) :
    Prop := result = p /\ body = [p] /\ work = 1.

Lemma sample_callback_adapter :
  audit_external_callback_adapter sample_callback (@length positive) sample_callback_source
    (fun _ => 1).
Proof.
  constructor.
  - intros argument result body Hcall. inversion Hcall. repeat split; reflexivity.
  - intros argument result body Hcall. inversion Hcall. simpl. lia.
Qed.

Example audit_callback_actual_observation :
  sample_callback_source 3%positive (fst (sample_callback 3%positive))
    (snd (sample_callback 3%positive)) (length (snd (sample_callback 3%positive))) /\
  length (snd (sample_callback 3%positive)) <= 1.
Proof.
  exact (audit_external_callback_observed _ _ _ _ _ _ _ sample_callback_adapter 3%positive).
Qed.

Example audit_adapted_pair_actual_budget :
  audit_pair_events_work (@length positive) (@length positive)
    (snd (audit_pair_encode sample_callback sample_callback (1%positive, 8%positive))) <=
  audit_pair_input_budget sample_callback sample_callback (fun _ => 1) (fun _ => 1)
    (1%positive, 8%positive).
Proof.
  apply audit_pair_input_bound_adapted with
    (first_source := sample_callback_source) (second_source := sample_callback_source);
    exact sample_callback_adapter.
Qed.

Example audit_adapted_duplicate_list_actual_budget :
  audit_list_events_work (@length positive)
    (snd (audit_list_encode sample_callback [1%positive; 1%positive])) <=
  audit_list_input_budget sample_callback (fun _ => 1) [1%positive; 1%positive].
Proof.
  apply audit_list_input_bound_adapted with (element_source := sample_callback_source).
  exact sample_callback_adapter.
Qed.

Example audit_adapted_computed_work :
  audit_pair_events_work (@length positive) (@length positive)
    (snd (audit_pair_encode sample_callback sample_callback (1%positive, 8%positive))) <= 57 /\
  audit_list_events_work (@length positive)
    (snd (audit_list_encode sample_callback [1%positive; 1%positive])) <= 30 /\
  audit_list_events_work (@length positive)
    (snd (audit_list_encode sample_callback [])) <= 4.
Proof.
  vm_compute. repeat split; lia.
Qed.

Example audit_encoder_order_and_absence :
  fst (audit_pair_encode audit_positive_encode audit_positive_encode (1%positive, 2%positive)) <>
    fst (audit_pair_encode audit_positive_encode audit_positive_encode (2%positive, 1%positive)) /\
  snd (audit_option_encode audit_positive_encode None) = [AuditOptionNone] /\
  composite_list_stream_nodes
    (CollectionsAuditComposite.prepared_list_work positive_encoding
      (CompositeListCosts positive (fun _ => 1)) [1%positive; 1%positive]) = 5.
Proof.
  repeat split; discriminate || reflexivity.
Qed.
