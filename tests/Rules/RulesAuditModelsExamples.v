(** * Source writer observations

    The strict traversal retains later callback frames after a false result.
    For example, testing [false; true] invokes both predicates.
    Builds on: RulesAuditMaterializePrelude, RulesAuditJoin and RulesRUL2a. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditEncoding.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditRelations RulesAuditRelationCallbacks RulesAuditFiring RulesAuditJoin.
From Galois.Tests.Rules Require Import RulesRUL2a.
Import List.ListNotations.

Definition materialize_boolean_probe (b : bool) : mat_run bool :=
  let '(_, first) := mat_emit (MatBlock (if b then 21 else 20)) in
  let '(result, second) := mat_return b in
  (result, first ++ second).

(** The strict all traversal retains the callback for both operands. *)
Example mat_all_strict_tail_observed :
  let '(out, events) := mat_all materialize_boolean_probe [false; true] in
  out = false /\ In (MatBlock 20) events /\ In (MatBlock 21) events.
Proof.
  vm_compute. repeat (first [left; reflexivity | right | split | reflexivity]).
Qed.

(** An empty traversal makes no predicate call. *)
Example mat_all_empty_observed :
  fst (mat_all materialize_boolean_probe []) = true /\
  ~ In (MatBlock 20) (snd (mat_all materialize_boolean_probe [])).
Proof.
  vm_compute. split; [reflexivity | intuition discriminate].
Qed.

(** Appending preserves both duplicate entries and their original order. *)
Example mat_append_duplicates_observed :
  fst (mat_append [1; 1] [2]) = [1; 1; 2].
Proof.
  vm_compute. reflexivity.
Qed.

(** Both recorded strategies retain accepted rows and exclude the negative match. *)
Example recorded_firing_both_strategies : forall strategy,
  let prog := join_test_program [repeated_join_rule] in
  let run := rules_join_firing_capture strategy prog join_test_facts
    repeated_join_rule join_test_env in
  let result := rules_firing_tail_result (rules_join_firing_tail run) in
  FinSet.mem tuple_encoding [2%positive] result = true /\
  FinSet.mem tuple_encoding [3%positive] result = false /\
  FinSet.mem tuple_encoding [4%positive] result = true.
Proof.
  intros []; vm_compute; repeat split; reflexivity.
Qed.

(** Both recorded strategies reject malformed relation rows. *)
Example recorded_firing_malformed_rows : forall strategy,
  let prog := join_test_program [repeated_join_rule] in
  let run := rules_join_firing_capture strategy prog join_test_facts
    repeated_join_rule malformed_join_env in
  FinSet.elements (rules_firing_tail_result (rules_join_firing_tail run)) = [].
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Definition model_receipt_body := (audit_nat_encoding_event + unit)%type.

Definition model_predicate_source (p : nat) (code : positive) (body : list model_receipt_body) :
    Prop :=
  code = fst (audit_nat_encode p) /\ body = map inl (snd (audit_nat_encode p)).

Definition model_environment (_ : nat) : FinSet.t tuple := FinSet.empty.

Definition model_environment_source (p : nat) (out : FinSet.t tuple)
    (body : list model_receipt_body) : Prop :=
  out = model_environment p /\ body = [inr tt].

Definition model_is_environment_event (event : rules_relation_event nat) : bool :=
  match event with
  | RulesRelationEnv _ _ => true
  | _ => false
  end.

(** Repeated predicates retain actual encoding receipts and share one environment call. *)
Example model_duplicate_predicate_receipts :
  let a := Atom 1 [TVar 0; TVar 0] in
  let '(_, events) := rules_join_relations_counted nat_encoding [a; a] model_environment in
  length (filter model_is_environment_event events) = 1 /\
  exists bodies, rules_relation_trace_source model_predicate_source model_environment_source
    events bodies.
Proof.
  vm_compute. split.
  - reflexivity.
  - repeat (first [solve [reflexivity] | progress eexists | progress constructor | progress split]).
Qed.
