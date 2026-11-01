(** * Complete indexed rule firing account

    The selected strategy's actual bindings feed one negative, universe and output pipeline.
    For example, both strategies retain their own preparation while sharing the same tail model.
    Builds on: RulesAuditNestedSelection, RulesAuditMultiwaySelection and
    RulesAuditFiringCallbacks. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin
  RulesAuditPrepareCallbacks RulesAuditRelationCallbacks RulesAuditTerminalCallbacks
  RulesAuditNestedSelection RulesAuditMultiwaySelection RulesAuditFiring RulesAuditFiringCallbacks.
Import List.ListNotations.

Inductive rules_selection_capture (P : Type) :=
  | RulesNestedCapture (run : rules_nested_selection_run P)
  | RulesMultiwayCapture (run : rules_multiway_selection_run P).
Arguments RulesNestedCapture {P} _.
Arguments RulesMultiwayCapture {P} _.

Definition rules_select_capture {P} (strategy : join_strategy) (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : rules_selection_capture P :=
  match strategy with
  | IndexedNested => RulesNestedCapture (rules_selected_nested_capture prog r env)
  | IndexedMultiway => RulesMultiwayCapture (rules_selected_multiway_capture prog r env)
  end.

Definition rules_selection_result {P} (run : rules_selection_capture P) : list binding :=
  match run with
  | RulesNestedCapture nested => rules_nested_selection_result nested
  | RulesMultiwayCapture multiway => rules_multiway_selection_result multiway
  end.

Definition rules_selection_work {P} (run : rules_selection_capture P) : nat :=
  match run with
  | RulesNestedCapture nested => rules_nested_selection_work nested
  | RulesMultiwayCapture multiway => rules_multiway_selection_work multiway
  end.

Definition rules_selection_input_budget {P} (strategy : join_strategy) (prog : program P)
    (r : rule P) (env : P -> FinSet.t tuple) : nat :=
  match strategy with
  | IndexedNested => rules_nested_selection_input_budget prog r env
  | IndexedMultiway => rules_multiway_selection_input_budget prog r env
  end.

Record rules_join_firing_run (P : Type) := RulesJoinFiringRun {
  rules_join_firing_selection : rules_selection_capture P;
  rules_join_firing_tail : rules_firing_tail_run P
}.
Arguments rules_join_firing_selection {P} _.
Arguments rules_join_firing_tail {P} _.

Definition rules_join_firing_capture {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
    rules_join_firing_run P :=
  let selection := rules_select_capture strategy prog r env in
  let tail := rules_firing_tail_capture prog facts r env (rules_selection_result selection) in
  RulesJoinFiringRun P selection tail.

Definition rules_join_firing_work {P} (run : rules_join_firing_run P) : nat :=
  1 + rules_selection_work (rules_join_firing_selection run) +
    rules_firing_tail_work (rules_join_firing_tail run).

Definition rules_join_firing_input_budget {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple)
    (selected : list binding) : nat :=
  1 + rules_selection_input_budget strategy prog r env +
    rules_firing_tail_input_budget prog facts r selected.

(** The selected run returns the original firing output with a same-intermediate allowance. *)
Definition rules_join_firing_input_bound_statement : Prop :=
  forall P strategy (prog : program P) facts r env,
    let run := rules_join_firing_capture strategy prog facts r env in
    rules_firing_tail_result (rules_join_firing_tail run) = fire_rule_join strategy prog facts r
  env /\
    rules_join_firing_work run <= rules_join_firing_input_budget strategy prog facts r env
      (rules_selection_result (rules_join_firing_selection run)).

Definition rules_flat_body_work {B} (weight : B -> nat) (bodies : list (list B)) : nat :=
  fold_right (fun body n => fold_right (fun item total => weight item + total) 0 body + n) 0 bodies.

(** Selection receipts retain the callback bodies for the selected strategy. *)
Definition rules_selection_receipt_source {P B} (E : encoding P)
    (pred_source : P -> positive -> list B -> Prop) (env_source : P -> FinSet.t tuple -> list B
  -> Prop)
    (run : rules_selection_capture P) (bodies : list (list B)) : Prop :=
  match run with
  | RulesNestedCapture nested => exists relation_bodies prepare_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_nested_selection_relation_events nested) relation_bodies /\
      rules_predicate_trace_source E pred_source
        (rules_nested_selection_prepare_events nested) prepare_bodies /\
      bodies = concat relation_bodies ++ concat prepare_bodies
  | RulesMultiwayCapture multiway => exists relation_bodies prepare_bodies terminal_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_multiway_selection_relation_events multiway) relation_bodies /\
      rules_predicate_trace_source E pred_source
        (rules_multiway_selection_prepare_events multiway) prepare_bodies /\
      rules_positive_filter_source env_source
        (rules_multiway_selection_terminal_events multiway) terminal_bodies /\
      bodies = concat relation_bodies ++ concat prepare_bodies ++ concat (concat terminal_bodies)
  end.

(** Tail receipts retain the negative and universe callback bodies. *)
Definition rules_tail_receipt_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (arity_source : P -> nat -> list B -> Prop)
    (run : rules_firing_tail_run P) (bodies : list (list B)) : Prop :=
  exists negative_bodies universe_bodies,
    rules_negative_filter_source env_source (rules_firing_tail_negative_events run)
  negative_bodies /\
    rules_universe_trace_source pred_source arity_source
      (rules_firing_tail_universe_events run) universe_bodies /\
    bodies = concat (concat negative_bodies) ++ concat universe_bodies.

Definition rules_selection_external_budget {P} (prog : program P) (r : rule P)
    (pred_bound env_bound : P -> nat) (run : rules_selection_capture P) : nat :=
  let atoms := positive_atoms (body r) in
  rules_relation_external_input_budget (penc prog) atoms pred_bound env_bound +
  match run with
  | RulesNestedCapture _ => rules_predicate_input_budget pred_bound atoms
  | RulesMultiwayCapture multiway =>
      length (join_variables atoms) * rules_predicate_input_budget pred_bound atoms +
        length (rules_multiway_selection_candidates multiway) *
          rules_predicate_input_budget env_bound atoms
  end.

(** The complete firing run retains the exact external body of every invocation. *)
Definition rules_join_firing_source_statement : Prop :=
  forall P B strategy (prog : program P) facts (r : rule P) (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound arity_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    rules_arity_source_laws prog arity_source weight arity_bound ->
    let run := rules_join_firing_capture strategy prog facts r env in
    let selected := rules_join_firing_selection run in
    let tail := rules_join_firing_tail run in
    exists selection_bodies tail_bodies,
      rules_selection_receipt_source (penc prog) pred_source env_source selected selection_bodies /\
      rules_tail_receipt_source pred_source env_source arity_source tail tail_bodies /\
      rules_firing_tail_result tail = fire_rule_join strategy prog facts r env /\
      rules_join_firing_work run + rules_flat_body_work weight selection_bodies +
        rules_flat_body_work weight tail_bodies <=
        rules_join_firing_input_budget strategy prog facts r env (rules_selection_result selected) +
          rules_selection_external_budget prog r pred_bound env_bound selected +
          length (rules_selection_result selected) * rules_negative_input_budget env_bound r +
          rules_universe_external_input_budget prog facts (pred (head r)) pred_bound arity_bound.

(** Both existing strategies agree on final tuple membership under the original premises. *)
Definition rules_join_agrees : Prop :=
  forall P (prog : program P) (facts : list (ground_atom P)) (r : rule P)
    (env : P -> FinSet.t tuple),
    program_wf prog facts -> List.In r (rules prog) -> env_wf prog env ->
    forall ts,
      FinSet.mem tuple_encoding ts (fire_rule_join IndexedNested prog facts r env) = true <->
      FinSet.mem tuple_encoding ts (fire_rule_join IndexedMultiway prog facts r env) = true.
