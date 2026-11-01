(** * Relation callback receipts

    These computed fixtures inspect the actual predicate and environment operands.
    For example, a duplicate atom retains two encoder calls and one environment call.
    Builds on: RulesAuditRelationCallbacks. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesAuditRelations
  RulesAuditRelationCallbacks.
Import List.ListNotations.

Definition callback_environment (_ : nat) : FinSet.t tuple := FinSet.empty.

(** A predicate receipt records the actual encoded key and its predicate operand. *)
Definition callback_predicate_source (p : nat) (code : positive) (body : list nat) : Prop :=
  code = encode nat_encoding p /\ body = [p].

(** An environment receipt records its predicate operand and returned relation. *)
Definition callback_environment_source (p : nat) (out : FinSet.t tuple) (body : list nat) : Prop :=
  out = callback_environment p /\ body = [p].

Definition callback_receipt_operands (event : rules_relation_event nat) : list nat :=
  match event with
  | RulesRelationDistinct _ _ events =>
      map (fun entry =>
        match entry with
        | RulesEncodeEntry p _ => p
        end)
        (rules_relation_entries events)
  | RulesRelationEnv p _ => [p]
  | RulesRelationSet p _ _ _ _ _ => [p]
  | _ => []
  end.

(** An empty snapshot has no predicate or environment callback operands. *)
Example callback_empty_operands :
    flat_map callback_receipt_operands
      (snd (rules_join_relations_counted nat_encoding [] callback_environment)) = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** Duplicate calls retain separate source bodies with the actual operands and code. *)
Example callback_duplicate_source_receipts :
    let a := Atom 1 [TVar 0] in
    let events := snd (rules_join_relations_counted nat_encoding [a; a] callback_environment) in
    exists bodies,
      rules_relation_trace_source callback_predicate_source callback_environment_source
        events bodies.
Proof.
  vm_compute.
  repeat (first [solve [reflexivity] | progress eexists | progress constructor | progress split]).
Qed.

(** Duplicate predicate encoding occurs twice, followed by one environment and one write call. *)
Example callback_duplicate_operands :
    let a := Atom 1 [TVar 0] in
    flat_map callback_receipt_operands
      (snd (rules_join_relations_counted nat_encoding [a; a] callback_environment)) = [1; 1; 1; 1].
Proof.
  vm_compute. reflexivity.
Qed.
