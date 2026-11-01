(** * Relation snapshot callback source receipts

    Distinct predicate encodings, table writes and environment calls retain their own bodies.
    For example, duplicate atoms re-encode their predicate but share one environment lookup.
    Builds on: RulesAuditRelations and the predicate source model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesJoin RulesAuditRelations
  RulesAuditPrepareCallbacks.
Import List.ListNotations.

Definition rules_relation_entries {P}
    (events : list (audit_set_event P (rules_encode_entry P))) : list (rules_encode_entry P) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

(** An encoding entry retains a source body for its recorded predicate and code. *)
Definition rules_relation_entry_source {P B} (source : P -> positive -> list B -> Prop)
    (entry : rules_encode_entry P) (body : list B) : Prop :=
  match entry with
  | RulesEncodeEntry p code => source p code body
  end.

(** Each relation event retains the bodies of its actual external callbacks. *)
Definition rules_relation_event_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (event : rules_relation_event P)
    (bodies : list (list B)) : Prop :=
  match event with
  | RulesRelationDistinct _ _ events =>
      Forall2 (rules_relation_entry_source pred_source) (rules_relation_entries events) bodies
  | RulesRelationEnv p result => exists body, bodies = [body] /\ env_source p result body
  | RulesRelationSet p _ code _ _ _ => exists body, bodies = [body] /\ pred_source p code body
  | _ => bodies = []
  end.

(** Relation callback bodies correspond in order to the recorded events. *)
Definition rules_relation_trace_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (events : list (rules_relation_event P))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_relation_event_source pred_source env_source) events bodies.

(** Each environment callback has a source body bounded by its predicate allowance. *)
Definition rules_environment_source_laws {P B} (env : P -> FinSet.t tuple)
    (source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) :
  Prop :=
  (forall p, exists body, source p (env p) body) /\
  (forall p out body, source p out body ->
    fold_right (fun item n => weight item + n) 0 body <= bound p).

Definition rules_relation_external_input_budget {P} (E : encoding P) (atoms : list (atom P))
    (pred_bound env_bound : P -> nat) : nat :=
  let predicates := map pred atoms in
  let keys := FinSet.elements (FinSet.of_list E predicates) in
  fold_right (fun p n => pred_bound p + n) 0 predicates +
    fold_right (fun p n => pred_bound p + env_bound p + n) 0 keys.

(** One same-run relation snapshot preserves distinct and repeated callback calls. *)
Definition rules_relations_external_source_statement : Prop :=
  forall P B (E : encoding P) atoms (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound : P -> nat),
    rules_predicate_source_laws E pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    let '(out, events) := rules_join_relations_counted E atoms env in
    exists bodies, rules_relation_trace_source pred_source env_source events bodies /\
      out = prepare_join_relations E atoms env /\
      rules_relation_work events + rules_predicate_bodies_work weight bodies <=
        rules_join_relations_input_budget E atoms env +
          rules_relation_external_input_budget E atoms pred_bound env_bound.
