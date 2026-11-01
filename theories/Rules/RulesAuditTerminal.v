(** * Strict positive and negative terminal filters

    All literal occurrences and environment snapshots are retained, even after a prior false
    result under strict evaluation.
    For example, a failed check does not skip later literal occurrences.
    Builds on: RulesJoin and the nested binding model. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditNestedProbe.
Import List.ListNotations.

Inductive rules_terminal_event (P : Type) : Type :=
  | RtInstantiate (terms : list term) (input : binding) (output : tuple)
      (events : list rules_nested_probe_event)
  | RtEnv (predicate : P) (result : FinSet.t tuple)
  | RtMember (row : tuple) (input : FinSet.t tuple) (answer : bool)
      (events : list (audit_set_event tuple (audit_list_event positive
  (audit_basic_encoding_event positive))))
  | RtNot (input output : bool)
  | RtAnd (lhs rhs output : bool)
  | RtCase (site : nat).
Arguments RtInstantiate {P} _ _ _ _.
Arguments RtEnv {P} _ _.
Arguments RtMember {P} _ _ _ _.
Arguments RtNot {P} _ _.
Arguments RtAnd {P} _ _ _.
Arguments RtCase {P} _.

Definition rules_terminal_atom_counted {P} (env : P -> FinSet.t tuple) (b : binding)
    (a : atom P) : bool * list (rules_terminal_event P) :=
  let '(row, inst_events) := rules_probe_instantiate b (args a) in
  let p := pred a in
  let set := env p in
  let '(found, mem_events) := audit_finset_mem (audit_list_encode audit_positive_encode) row set in
  (found, [RtInstantiate (args a) b row inst_events; RtEnv p set; RtMember row set found
  mem_events]).

Fixpoint rules_positive_check_counted {P} (atoms : list (atom P)) (env : P -> FinSet.t tuple)
    (b : binding) : bool * list (rules_terminal_event P) :=
  match atoms with
  | [] => (true, [RtCase 0])
  | a :: rest =>
      let '(head, first) := rules_terminal_atom_counted env b a in
      let '(tail, later) := rules_positive_check_counted rest env b in
      (andb head tail, RtCase 0 :: first ++ later ++ [RtAnd head tail (andb head tail)])
  end.

Fixpoint rules_negative_literals_counted {P} (literals : list (literal P))
    (env : P -> FinSet.t tuple) (b : binding) : bool * list (rules_terminal_event P) :=
  match literals with
  | [] => (true, [RtCase 1])
  | literal :: rest =>
      let '(head, first) := match literal with
        | LPos _ => (true, [RtCase 2])
        | LNeg a =>
            let '(found, events) := rules_terminal_atom_counted env b a in
            (negb found, RtCase 2 :: events ++ [RtNot found (negb found)])
        end in
      let '(tail, later) := rules_negative_literals_counted rest env b in
      (andb head tail, RtCase 1 :: first ++ later ++ [RtAnd head tail (andb head tail)])
  end.

(** Erasing terminal checks gives the original positive and negative filters. *)
Definition rules_terminal_erasure_statement : Prop :=
  (forall P (atoms : list (atom P)) env b,
    fst (rules_positive_check_counted atoms env b) = positive_ok atoms env b) /\
  (forall P (r : rule P) env b,
    fst (rules_negative_literals_counted (body r) env b) = negative_ok r env b).

Definition rules_terminal_event_work {P} (event : rules_terminal_event P) : nat :=
  match event with
  | RtInstantiate _ _ _ events => rules_nested_probe_work events
  | RtMember _ _ _ events =>
      audit_finset_source_work (audit_list_events_work audit_basic_encoding_work) events
  | _ => 1
  end.

Definition rules_terminal_event_budget {P} (event : rules_terminal_event P) : nat :=
  match event with
  | RtInstantiate _ _ _ events => rules_nested_probe_budget events
  | RtMember row _ _ _ =>
      20 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
        5 * Pos.size_nat (encode tuple_encoding row)
  | _ => 1
  end.

Definition rules_terminal_work {P} (events : list (rules_terminal_event P)) : nat :=
  fold_right (fun event n => rules_terminal_event_work event + n) 0 events.

Definition rules_terminal_budget {P} (events : list (rules_terminal_event P)) : nat :=
  fold_right (fun event n => rules_terminal_event_budget event + n) 0 events.

(** The selected event budget bounds terminal checking work. *)
Definition rules_terminal_selected_cost_statement : Prop :=
  (forall P (atoms : list (atom P)) env b,
    let '(out, events) := rules_positive_check_counted atoms env b in
    out = positive_ok atoms env b /\ rules_terminal_work events <= rules_terminal_budget events) /\
  (forall P (r : rule P) env b,
    let '(out, events) := rules_negative_literals_counted (body r) env b in
    out = negative_ok r env b /\ rules_terminal_work events <= rules_terminal_budget events).
