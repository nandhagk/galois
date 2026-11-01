(** * Rule firing callback receipts

    Negative tests and universe preparation retain environment, encoding and arity bodies.
    For example, each negative literal calls its environment even after a previous failure.
    Builds on: RulesAuditFiring and the relation and terminal callback sources. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin
  RulesAuditRelations
  RulesAuditRelationCallbacks RulesAuditPrepareCallbacks RulesAuditTerminal
  RulesAuditTerminalCallbacks
  RulesAuditUniverse RulesAuditFiring.
Import List.ListNotations.

(** Each arity callback has a source body bounded by its predicate allowance. *)
Definition rules_arity_source_laws {P B} (prog : program P)
    (source : P -> nat -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) : Prop :=
  (forall p, exists body, source p (arity prog p) body) /\
  (forall p out body, source p out body ->
    fold_right (fun item n => weight item + n) 0 body <= bound p).

(** Each universe event retains the bodies of its actual external callbacks. *)
Definition rules_universe_event_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (event : rules_universe_event P)
    (bodies : list (list B)) : Prop :=
  match event with
  | RuPredicatesSet _ _ events
  | RuPredicateMem _ _ _ events =>
      Forall2 (rules_relation_entry_source pred_source) (rules_relation_entries events) bodies
  | RuArity p out => exists body, bodies = [body] /\ arity_source p out body
  | _ => bodies = []
  end.

(** Universe callback bodies correspond in order to the recorded events. *)
Definition rules_universe_trace_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (events : list (rules_universe_event P))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_universe_event_source pred_source arity_source) events bodies.

(** Each negative-filter trace retains its environment callback bodies. *)
Definition rules_negative_filter_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (groups : list (list (rules_terminal_event P))) (bodies : list (list (list (list B)))) : Prop :=
  Forall2 (rules_terminal_trace_source source) groups bodies.

Definition rules_negative_input_budget {P} (bound : P -> nat) (r : rule P) : nat :=
  fold_right (fun literal n => match literal with
    | LPos _ => n
    | LNeg a => bound (pred a) + n
    end) 0 (body r).

Definition rules_universe_external_input_budget {P} (prog : program P) (facts : list
  (ground_atom P))
    (p : P) (pred_bound arity_bound : P -> nat) : nat :=
  let predicates := flat_map rule_predicates (rules prog) ++ map fst facts in
  fold_right (fun key n => pred_bound key + n) 0 predicates + pred_bound p + arity_bound p.

(** The actual tail has same-invocation callback receipts and an input-derived allowance. *)
Definition rules_firing_tail_source_statement : Prop :=
  forall P B (prog : program P) facts (r : rule P) (env : P -> FinSet.t tuple) bindings
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound arity_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    rules_arity_source_laws prog arity_source weight arity_bound ->
    let run := rules_firing_tail_capture prog facts r env bindings in
    exists negative_bodies universe_bodies,
      rules_negative_filter_source env_source (rules_firing_tail_negative_events run)
  negative_bodies /\
      rules_universe_trace_source pred_source arity_source
        (rules_firing_tail_universe_events run) universe_bodies /\
      rules_firing_tail_result run = FinSet.of_list tuple_encoding
        (filter (in_universe prog facts (pred (head r)))
          (map (fun b => map (inst (binding_value b)) (args (head r)))
            (filter (negative_ok r env) bindings))) /\
      rules_firing_tail_work run + rules_terminal_bodies_work weight negative_bodies +
        rules_predicate_bodies_work weight universe_bodies <=
        rules_firing_tail_input_budget prog facts r bindings +
          length bindings * rules_negative_input_budget env_bound r +
          rules_universe_external_input_budget prog facts (pred (head r)) pred_bound arity_bound.
