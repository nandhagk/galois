(** * Whole indexed-multiway binding selection

    One relation snapshot feeds variable indexes, intersections and strict positive filtering.
    For example, each candidate binding invokes every positive environment test.
    Builds on: RulesAuditMultiwayPrepare, RulesAuditMultiwayProbe and terminal callbacks. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditJoinSyntax RulesAuditRelations RulesAuditRelationCallbacks RulesAuditMultiwayPrepare
  RulesAuditMultiwayProbe RulesAuditTerminal RulesAuditTerminalCallbacks RulesAuditPrepareCallbacks
  RulesAuditNestedSelection.
Import List.ListNotations.

Record rules_multiway_selection_run (P : Type) := RulesMultiwaySelectionRun {
  rules_multiway_selection_result : list binding;
  rules_multiway_selection_candidates : list binding;
  rules_multiway_selection_atoms : list (atom P);
  rules_multiway_selection_atom_events : list mat_frame;
  rules_multiway_selection_relation_events : list (rules_relation_event P);
  rules_multiway_selection_variable_events : list mat_frame;
  rules_multiway_selection_prepare_events : list mat_frame;
  rules_multiway_selection_probe_events : list rules_multi_probe_event;
  rules_multiway_selection_terminal_events : list (list (rules_terminal_event P))
}.
Arguments rules_multiway_selection_result {P} _.
Arguments rules_multiway_selection_candidates {P} _.
Arguments rules_multiway_selection_atoms {P} _.
Arguments rules_multiway_selection_atom_events {P} _.
Arguments rules_multiway_selection_relation_events {P} _.
Arguments rules_multiway_selection_variable_events {P} _.
Arguments rules_multiway_selection_prepare_events {P} _.
Arguments rules_multiway_selection_probe_events {P} _.
Arguments rules_multiway_selection_terminal_events {P} _.

Definition rules_selected_multiway_capture {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : rules_multiway_selection_run P :=
  let '(atoms, atom_events) := mat_positive_atoms (body r) in
  let '(relations, relation_events) := rules_join_relations_counted (penc prog) atoms env in
  let '(vars, var_events) := mat_join_variables atoms in
  let '(searches, prepare_events) :=
    rules_prepare_multiway_full (penc prog) relations vars FinSet.empty atoms in
  let '(candidates, probe_events) := rules_run_multiway_counted searches [Map.empty] in
  let '(result, terminal_events) := rules_positive_filter_capture atoms env candidates in
  RulesMultiwaySelectionRun P result candidates atoms atom_events relation_events var_events
    prepare_events probe_events terminal_events.

Definition rules_multiway_selection_work {P} (run : rules_multiway_selection_run P) : nat :=
  mat_work (rules_multiway_selection_atom_events run) +
    rules_relation_work (rules_multiway_selection_relation_events run) +
    mat_work (rules_multiway_selection_variable_events run) +
    mat_work (rules_multiway_selection_prepare_events run) +
    rules_multi_probe_work (rules_multiway_selection_probe_events run) +
    rules_positive_filter_work (rules_multiway_selection_terminal_events run) + 1.

Definition rules_multiway_selection_input_budget {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : nat :=
  let atoms := positive_atoms (body r) in
  (1000 * 1000 * 1000) * Nat.pow (rules_nested_selection_input_size prog r env)
    (32 + 4 * length atoms + 4 * length (join_variables atoms)).

(** Same-run terminal groups correspond exactly to the actual candidate bindings. *)
Definition rules_multiway_selection_count_statement : Prop :=
  forall P (prog : program P) r env,
    let run := rules_selected_multiway_capture prog r env in
    length (rules_multiway_selection_terminal_events run) =
      length (rules_multiway_selection_candidates run).

(** The captured multiway selection returns the native result within the input allowance. *)
Definition rules_multiway_selection_input_bound_statement : Prop :=
  forall P (prog : program P) r env,
    let run := rules_selected_multiway_capture prog r env in
    rules_multiway_selection_result run = selected_bindings IndexedMultiway prog r env /\
    rules_multiway_selection_work run <= rules_multiway_selection_input_budget prog r env.

(** The relation, variable preparation and terminal filter retain every external callback body. *)
Definition rules_multiway_selection_source_statement : Prop :=
  forall P B (prog : program P) r (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    let run := rules_selected_multiway_capture prog r env in
    exists relation_bodies prepare_bodies terminal_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_multiway_selection_relation_events run) relation_bodies /\
      rules_predicate_trace_source (penc prog) pred_source
        (rules_multiway_selection_prepare_events run) prepare_bodies /\
      rules_positive_filter_source env_source
        (rules_multiway_selection_terminal_events run) terminal_bodies /\
      rules_multiway_selection_result run = selected_bindings IndexedMultiway prog r env /\
      rules_multiway_selection_work run + rules_predicate_bodies_work weight relation_bodies +
        rules_predicate_bodies_work weight prepare_bodies +
        rules_terminal_bodies_work weight terminal_bodies <=
        rules_multiway_selection_input_budget prog r env +
          rules_relation_external_input_budget (penc prog) (positive_atoms (body r)) pred_bound
  env_bound +
          length (join_variables (positive_atoms (body r))) *
            rules_predicate_input_budget pred_bound (positive_atoms (body r)) +
          length (rules_multiway_selection_candidates run) *
            rules_predicate_input_budget env_bound (positive_atoms (body r)).
