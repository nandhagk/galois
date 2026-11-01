(** * Whole indexed-nested binding selection

    One relation snapshot feeds the actual index preparation and binding probes.
    For example, repeated predicates share the snapshot while each atom builds its own index.
    Builds on: RulesAuditRelationCallbacks, RulesAuditNestedPrepare and RulesAuditNestedProbe. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditElements.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditJoinSyntax RulesAuditRelations RulesAuditNestedPrepare
  RulesAuditNestedProbe RulesAuditPrepareCallbacks RulesAuditRelationCallbacks.
Import List.ListNotations.

Record rules_nested_selection_run (P : Type) := RulesNestedSelectionRun {
  rules_nested_selection_result : list binding;
  rules_nested_selection_atoms : list (atom P);
  rules_nested_selection_atom_events : list mat_frame;
  rules_nested_selection_relation_events : list (rules_relation_event P);
  rules_nested_selection_prepare_events : list mat_frame;
  rules_nested_selection_probe_events : list rules_nested_probe_event
}.
Arguments rules_nested_selection_result {P} _.
Arguments rules_nested_selection_atoms {P} _.
Arguments rules_nested_selection_atom_events {P} _.
Arguments rules_nested_selection_relation_events {P} _.
Arguments rules_nested_selection_prepare_events {P} _.
Arguments rules_nested_selection_probe_events {P} _.

Definition rules_selected_nested_capture {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : rules_nested_selection_run P :=
  let '(atoms, atom_events) := mat_positive_atoms (body r) in
  let '(relations, relation_events) := rules_join_relations_counted (penc prog) atoms env in
  let '(searches, prepare_events) :=
    rules_prepare_nested_full (penc prog) relations atoms FinSet.empty in
  let '(result, probe_events) := rules_run_nested_counted searches [Map.empty] in
  RulesNestedSelectionRun P result atoms atom_events relation_events prepare_events probe_events.

Definition rules_nested_selection_work {P} (run : rules_nested_selection_run P) : nat :=
  mat_work (rules_nested_selection_atom_events run) +
    rules_relation_work (rules_nested_selection_relation_events run) +
    mat_work (rules_nested_selection_prepare_events run) +
    rules_nested_probe_work (rules_nested_selection_probe_events run) + 1.

Definition rules_nested_selection_input_size {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : nat :=
  2 + length (body r) +
    fold_right (fun a n =>
      1 + Pos.size_nat (encode (penc prog) (pred a)) + mat_index_terms_input (args a) +
      audit_trie_nodes (env (pred a)) + mat_index_rows_input (FinSet.elements (env (pred a))) + n)
      0 (positive_atoms (body r)).

Definition rules_nested_selection_input_budget {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : nat :=
  (1000 * 1000 * 1000) * Nat.pow (rules_nested_selection_input_size prog r env)
    (20 + 2 * length (positive_atoms (body r))).

(** The captured selection has the exact native result and input-derived internal allowance. *)
Definition rules_nested_selection_input_bound_statement : Prop :=
  forall P (prog : program P) r env,
    let run := rules_selected_nested_capture prog r env in
    rules_nested_selection_result run = selected_bindings IndexedNested prog r env /\
    rules_nested_selection_work run <= rules_nested_selection_input_budget prog r env.

(** Both external callbacks are related to the exact relation snapshot and preparation run. *)
Definition rules_nested_selection_source_statement : Prop :=
  forall P B (prog : program P) r (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    let run := rules_selected_nested_capture prog r env in
    exists relation_bodies prepare_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_nested_selection_relation_events run) relation_bodies /\
      rules_predicate_trace_source (penc prog) pred_source
        (rules_nested_selection_prepare_events run) prepare_bodies /\
      rules_nested_selection_result run = selected_bindings IndexedNested prog r env /\
      rules_nested_selection_work run + rules_predicate_bodies_work weight relation_bodies +
        rules_predicate_bodies_work weight prepare_bodies <=
        rules_nested_selection_input_budget prog r env +
          rules_relation_external_input_budget (penc prog) (positive_atoms (body r)) pred_bound
  env_bound +
          rules_predicate_input_budget pred_bound (positive_atoms (body r)).
