(** * Audit event examples

    These computations exercise trace folds and fixed abstract weights.
    For example, callback payloads are collected in their original order.
    Builds on: CollectionsAuditCost and Rocq Stdlib. *)

From Stdlib Require Import Lia.
From Stdlib.Lists Require Import List.
From Stdlib.NArith Require Import NArith.
From Stdlib.ZArith Require Import ZArith.
From Galois.Collections Require Import CollectionsAuditCost.

Import List.ListNotations.

Polymorphic Definition first_trace@{u v} : audit_trace@{u v} (nat * bool) :=
  [AuditCase 1 [2%N]; AuditCall (7, true); AuditKeyBit false;
   AuditConstruct 2 []; AuditArithmetic 1 [3%N]].

Polymorphic Definition second_trace@{u v} : audit_trace@{u v} (nat * bool) :=
  [AuditCall (8, false); AuditCase 2 []; AuditConstruct 1 [4%N];
   AuditArithmetic 2 []; AuditCase 1 []].

Example empty_trace_counts :
  audit_work (@nil (audit_event unit)) = 0 /\
  audit_calls (@nil (audit_event unit)) = [] /\
  audit_key_bits (@nil (audit_event unit)) = 0 /\
  audit_case_count 1 (@nil (audit_event unit)) = 0 /\
  audit_construct_count 1 (@nil (audit_event unit)) = 0 /\
  audit_arithmetic_count 1 (@nil (audit_event unit)) = 0.
Proof.
  repeat split; reflexivity.
Qed.

Example concatenated_trace_counts :
  audit_work (first_trace ++ second_trace) = 10 /\
  audit_calls (first_trace ++ second_trace) = [(7, true); (8, false)] /\
  audit_key_bits (first_trace ++ second_trace) = 1 /\
  audit_case_count 1 (first_trace ++ second_trace) = 2 /\
  audit_case_count 2 (first_trace ++ second_trace) = 1 /\
  audit_case_count 3 (first_trace ++ second_trace) = 0 /\
  audit_construct_count 1 (first_trace ++ second_trace) = 1 /\
  audit_construct_count 2 (first_trace ++ second_trace) = 1 /\
  audit_construct_count 3 (first_trace ++ second_trace) = 0 /\
  audit_arithmetic_count 1 (first_trace ++ second_trace) = 1 /\
  audit_arithmetic_count 2 (first_trace ++ second_trace) = 1 /\
  audit_arithmetic_count 3 (first_trace ++ second_trace) = 0.
Proof.
  repeat split; reflexivity.
Qed.

Example fixed_weight_values :
  audit_z_bits 0 = 1 /\ audit_z_bits 8 = 4 /\ audit_z_bits (-8) = 4 /\
  audit_key_bits_weight 1 = 1 /\ audit_key_bits_weight 8 = 4 /\
  audit_get_weight 8 = 5 /\ audit_set_weight 8 = 9 /\ audit_remove_weight 8 = 9 /\
  audit_encoding_weight 4 = 5 /\ audit_binary_weight 0 (-8) = 6 /\
  audit_multiply_weight 8 (-8) = 17 /\ audit_divide_weight 0 (-8) = 26 /\
  audit_shift_weight (-8) (-3) = 8 /\ audit_unary_conversion_weight 4 = 5.
Proof.
  repeat split; reflexivity.
Qed.

Example fixed_weight_positivity :
  0 < audit_get_weight 1 /\ 0 < audit_set_weight 8 /\ 0 < audit_remove_weight 1 /\
  0 < audit_encoding_weight 0 /\ 0 < audit_binary_weight 0 0 /\
  0 < audit_multiply_weight 0 0 /\ 0 < audit_divide_weight 0 0 /\
  0 < audit_shift_weight 0 0 /\ 0 < audit_unary_conversion_weight 0.
Proof.
  repeat apply conj; vm_compute; lia.
Qed.

Example signed_operands :
  count_zencode 0 = 0%N /\ count_zencode 3 = 6%N /\ count_zencode (-3) = 5%N /\
  count_zdecode 5%N = (-3)%Z /\ scalar_z 4 3 (-3) = AuditArithmetic 4 [6%N; 5%N].
Proof.
  repeat split; reflexivity.
Qed.
