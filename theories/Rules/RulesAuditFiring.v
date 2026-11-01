(** * Rule firing after indexed selection

    The same selected bindings pass through negative checks, head instantiation, the universe
    closure and final tuple-set construction. For example, rejected negatives do not produce rows.
    Builds on: RulesAuditTerminal, RulesAuditUniverse and the shared collection audits. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditNestedProbe RulesAuditTerminal RulesAuditUniverse.
Import List.ListNotations.

Fixpoint rules_negative_filter_capture {P} (r : rule P) (env : P -> FinSet.t tuple)
    (bindings : list binding) : list binding * list (list (rules_terminal_event P)) :=
  match bindings with
  | [] => ([], [])
  | b :: rest =>
      let '(keep, first) := rules_negative_literals_counted (body r) env b in
      let '(tail, later) := rules_negative_filter_capture r env rest in
      (if keep then b :: tail else tail, first :: later)
  end.

Fixpoint rules_head_rows_capture (terms : list term) (bindings : list binding) :
    list tuple * list (list rules_nested_probe_event) :=
  match bindings with
  | [] => ([], [])
  | b :: rest =>
      let '(row, first) := rules_probe_instantiate b terms in
      let '(tail, later) := rules_head_rows_capture terms rest in
      (row :: tail, first :: later)
  end.

Fixpoint rules_universe_filter_capture {P} (state : bool * nat * FinSet.t positive)
    (rows : list tuple) : list tuple * list (list (rules_universe_event P)) :=
  match rows with
  | [] => ([], [])
  | row :: rest =>
      let '(keep, first) := @rules_universe_check_counted P state row in
      let '(tail, later) := @rules_universe_filter_capture P state rest in
      (if keep then row :: tail else tail, first :: later)
  end.

Record rules_firing_tail_run (P : Type) := RulesFiringTailRun {
  rules_firing_tail_result : FinSet.t tuple;
  rules_firing_tail_negative_events : list (list (rules_terminal_event P));
  rules_firing_tail_head_events : list (list rules_nested_probe_event);
  rules_firing_tail_universe_events : list (rules_universe_event P);
  rules_firing_tail_filter_events : list (list (rules_universe_event P));
  rules_firing_tail_output_events : list (audit_set_event tuple
    (audit_list_event positive (audit_basic_encoding_event positive)))
}.
Arguments rules_firing_tail_result {P} _.
Arguments rules_firing_tail_negative_events {P} _.
Arguments rules_firing_tail_head_events {P} _.
Arguments rules_firing_tail_universe_events {P} _.
Arguments rules_firing_tail_filter_events {P} _.
Arguments rules_firing_tail_output_events {P} _.

Definition rules_firing_tail_capture {P} (prog : program P) (facts : list (ground_atom P))
    (r : rule P) (env : P -> FinSet.t tuple) (bindings : list binding) : rules_firing_tail_run P :=
  let '(negative, negative_events) := rules_negative_filter_capture r env bindings in
  let '(rows, head_events) := rules_head_rows_capture (args (head r)) negative in
  let '(universe, universe_events) := rules_universe_prepare_counted prog facts (pred (head r)) in
  let '(accepted, filter_events) := rules_universe_filter_capture universe rows in
  let '(output, output_events) :=
    audit_finset_of_list (audit_list_encode audit_positive_encode) accepted in
  RulesFiringTailRun P output negative_events head_events universe_events filter_events
  output_events.

Definition rules_firing_tail_work {P} (run : rules_firing_tail_run P) : nat :=
  4 + 2 * length (rules_firing_tail_negative_events run) +
    fold_right (fun events n => rules_terminal_work events + n) 0
  (rules_firing_tail_negative_events run) +
    2 * length (rules_firing_tail_head_events run) +
    fold_right (fun events n => rules_nested_probe_work events + n) 0
  (rules_firing_tail_head_events run) +
    rules_universe_work (rules_firing_tail_universe_events run) +
    2 * length (rules_firing_tail_filter_events run) +
    fold_right (fun events n => rules_universe_work events + n) 0
  (rules_firing_tail_filter_events run) +
    audit_finset_source_work (audit_list_events_work audit_basic_encoding_work)
      (rules_firing_tail_output_events run).

Definition rules_firing_binding_size (b : binding) : nat :=
  fold_right (fun entry n => 1 + fst entry + Pos.size_nat (snd entry) + n) 0 (Map.elements b).

Definition rules_firing_atom_size {P} (E : encoding P) (a : atom P) : nat :=
  1 + Pos.size_nat (encode E (pred a)) + mat_index_terms_input (args a).

Definition rules_firing_rule_size {P} (E : encoding P) (r : rule P) : nat :=
  rules_firing_atom_size E (head r) +
    fold_right (fun literal n => rules_firing_atom_size E (lit_atom literal) + n) 0 (body r).

Definition rules_firing_tail_input_size {P} (prog : program P) (facts : list (ground_atom P))
    (r : rule P) (bindings : list binding) : nat :=
  2 + arity prog (pred (head r)) + rules_firing_rule_size (penc prog) r +
    fold_right (fun rule n => rules_firing_rule_size (penc prog) rule + n) 0 (rules prog) +
    fold_right (fun fact n => 1 + Pos.size_nat (encode (penc prog) (fst fact)) +
      mat_tuple_size (snd fact) + n) 0 facts +
    fold_right (fun b n => 1 + rules_firing_binding_size b + n) 0 bindings.

Definition rules_firing_tail_input_budget {P} (prog : program P) (facts : list (ground_atom P))
    (r : rule P) (bindings : list binding) : nat :=
  (1000 * 1000 * 1000) * Nat.pow (rules_firing_tail_input_size prog facts r bindings) 12.

(** Tail construction agrees with the original rule firing pipeline for any selected bindings. *)
Definition rules_firing_tail_input_bound_statement : Prop :=
  forall P (prog : program P) facts (r : rule P) env bindings,
    let run := rules_firing_tail_capture prog facts r env bindings in
    rules_firing_tail_result run = FinSet.of_list tuple_encoding
      (filter (in_universe prog facts (pred (head r)))
        (map (fun b => map (inst (binding_value b)) (args (head r)))
          (filter (negative_ok r env) bindings))) /\
    rules_firing_tail_work run <= rules_firing_tail_input_budget prog facts r bindings.
