(** * Join terminal callback receipts

    Positive and negative checks retain each actual environment invocation.
    For example, strict conjunction still checks later atoms after an earlier failure.
    Builds on: RulesAuditTerminal and the environment source model. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditTerminal
  RulesAuditRelationCallbacks RulesAuditPrepareCallbacks.
Import List.ListNotations.

(** An environment event retains the source body for its recorded invocation. *)
Definition rules_terminal_event_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (event : rules_terminal_event P) (bodies : list (list B)) : Prop :=
  match event with
  | RtEnv p out => exists body, bodies = [body] /\ source p out body
  | _ => bodies = []
  end.

(** Terminal callback bodies correspond in order to the recorded events. *)
Definition rules_terminal_trace_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (events : list (rules_terminal_event P)) (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_terminal_event_source source) events bodies.

Fixpoint rules_positive_filter_capture {P} (atoms : list (atom P)) (env : P -> FinSet.t tuple)
    (bindings : list binding) : list binding * list (list (rules_terminal_event P)) :=
  match bindings with
  | [] => ([], [])
  | b :: rest =>
      let '(keep, first) := rules_positive_check_counted atoms env b in
      let '(tail, later) := rules_positive_filter_capture atoms env rest in
      (if keep then b :: tail else tail, first :: later)
  end.

Definition rules_positive_filter_work {P} (groups : list (list (rules_terminal_event P))) : nat :=
  1 + 2 * length groups + fold_right (fun events n => rules_terminal_work events + n) 0 groups.

(** Each positive-filter trace retains its environment callback bodies. *)
Definition rules_positive_filter_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (groups : list (list (rules_terminal_event P))) (bodies : list (list (list (list B)))) : Prop :=
  Forall2 (rules_terminal_trace_source source) groups bodies.

Definition rules_terminal_bodies_work {B} (weight : B -> nat)
    (groups : list (list (list (list B)))) : nat :=
  fold_right (fun bodies n => rules_predicate_bodies_work weight bodies + n) 0 groups.

(** Filtering runs the actual strict checks once per candidate binding. *)
Definition rules_positive_filter_erasure_statement : Prop :=
  forall P (atoms : list (atom P)) env bindings,
    fst (rules_positive_filter_capture atoms env bindings) = filter (positive_ok atoms env)
  bindings.
