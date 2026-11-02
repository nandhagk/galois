(** * Preparation callback observations

    These fixtures exercise actual nested and multiway preparation with nonempty rows.
    For example, two occurrences of one predicate retain two encoder invocations.
    Builds on: RulesAuditPrepareCallbacks and CollectionsAuditEncoding. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditNestedPrepare RulesAuditMultiwayPrepare RulesAuditPrepareCallbacks.
Import List.ListNotations.

(** * Concrete natural encoder receipts *)

Definition prepare_nat_source (p : nat) (code : positive)
    (body : list audit_nat_encoding_event) : Prop :=
  code = fst (audit_nat_encode p) /\ body = snd (audit_nat_encode p).

Definition prepare_test_relations : Map.t nat (list tuple) :=
  Map.set nat_encoding 1 [[2%positive]] Map.empty.

Definition prepare_test_atom : atom nat := Atom 1 [TVar 0].

Definition prepare_encode_count (events : list mat_frame) : nat :=
  length (filter (fun event =>
    match event with
    | MatEncode _ _ _ _ => true
    | _ => false
    end) events).

(** Nested preparation preserves both repeated predicate calls and their actual encoder bodies. *)
Example nested_duplicate_encoder_receipts :
  let events := snd (rules_prepare_nested_full nat_encoding prepare_test_relations
    [prepare_test_atom; prepare_test_atom] FinSet.empty) in
  prepare_encode_count events = 2 /\
  exists bodies, rules_predicate_trace_source nat_encoding prepare_nat_source events bodies.
Proof.
  vm_compute; split.
  - reflexivity.
  - repeat (first [solve [reflexivity] | progress eexists | progress constructor | progress split]).
Qed.

(** Multiway preparation visits the selected atom for its variable and keeps its encoder body. *)
Example multiway_encoder_receipt :
  let events := snd (rules_prepare_multiway_full nat_encoding prepare_test_relations
    [0; 1] FinSet.empty [prepare_test_atom]) in
  prepare_encode_count events = 1 /\
  exists bodies, rules_predicate_trace_source nat_encoding prepare_nat_source events bodies.
Proof.
  vm_compute; split.
  - reflexivity.
  - repeat (first [solve [reflexivity] | progress eexists | progress constructor | progress split]).
Qed.

(** A variable absent from the atom causes no predicate lookup. *)
Example multiway_absent_variable_has_no_callback :
  prepare_encode_count (snd (rules_prepare_multiway_full nat_encoding prepare_test_relations
    [1] FinSet.empty [prepare_test_atom])) = 0.
Proof.
  vm_compute; reflexivity.
Qed.

(** Both repeated atoms produce search indexes whose rows come from the nonempty relation. *)
Example nested_preparation_nonempty_result :
  length (fst (rules_prepare_nested_full nat_encoding prepare_test_relations
    [prepare_test_atom; prepare_test_atom] FinSet.empty)) = 2 /\
  fst (rules_prepare_nested_full nat_encoding prepare_test_relations
    [prepare_test_atom; prepare_test_atom] FinSet.empty) =
  prepare_nested [prepare_test_atom; prepare_test_atom] FinSet.empty
    (join_relation_rows nat_encoding prepare_test_relations).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The present and absent variables each produce their own multiway search. *)
Example multiway_preparation_nonempty_result :
  length (fst (rules_prepare_multiway_full nat_encoding prepare_test_relations
    [0; 1] FinSet.empty [prepare_test_atom])) = 2 /\
  fst (rules_prepare_multiway_full nat_encoding prepare_test_relations
    [0; 1] FinSet.empty [prepare_test_atom]) =
  prepare_multiway [0; 1] FinSet.empty [prepare_test_atom]
    (join_relation_rows nat_encoding prepare_test_relations).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The first prepared nested index contains the supplied nonempty relation row. *)
Example nested_preparation_indexes_the_relation_row :
  match fst (rules_prepare_nested_full nat_encoding prepare_test_relations
    [prepare_test_atom] FinSet.empty) with
  | [search] => index_get (nested_index search) [] = [[2%positive]]
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

(** The selected multiway index contains the value from the supplied relation row. *)
Example multiway_preparation_indexes_the_relation_value :
  match fst (rules_prepare_multiway_full nat_encoding prepare_test_relations
    [0] FinSet.empty [prepare_test_atom]) with
  | [search] =>
    match multiway_domains search with
    | [domain] => FinSet.mem positive_encoding 2%positive
        (variable_index_get (variable_table domain) []) = true
    | _ => False
    end
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.
