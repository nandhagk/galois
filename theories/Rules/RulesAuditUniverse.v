(** * Counted finite-universe preparation and membership

    Every rule literal and fact contributes its actual predicates and constants. The
    predicate set and constant set are prepared once before filtering all head tuples.
    For example, a fact contributes its predicate and tuple constants to the universe.
    Builds on: RulesCompile and the shared finite-set models. *)

From Stdlib Require Import List Bool PeanoNat PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditRelations.
Import List.ListNotations.

Inductive rules_universe_event (P : Type) : Type :=
  | RuCase (site : nat)
  | RuAppend (size : nat)
  | RuPredicatesSet (input : list P) (output : FinSet.t P)
      (events : list (audit_set_event P (rules_encode_entry P)))
  | RuConstantsSet (input : list positive) (output : FinSet.t positive)
      (events : list (audit_set_event positive (audit_basic_encoding_event positive)))
  | RuPredicateMem (p : P) (input : FinSet.t P) (output : bool)
      (events : list (audit_set_event P (rules_encode_entry P)))
  | RuConstantMem (c : positive) (input : FinSet.t positive) (output : bool)
      (events : list (audit_set_event positive (audit_basic_encoding_event positive)))
  | RuArity (p : P) (value : nat)
  | RuLength (row : tuple)
  | RuNatEq (lhs rhs : nat) (result : bool)
  | RuAnd (lhs rhs output : bool).
Arguments RuCase {P} _.
Arguments RuAppend {P} _.
Arguments RuPredicatesSet {P} _ _ _.
Arguments RuConstantsSet {P} _ _ _.
Arguments RuPredicateMem {P} _ _ _ _.
Arguments RuConstantMem {P} _ _ _ _.
Arguments RuArity {P} _ _.
Arguments RuLength {P} _.
Arguments RuNatEq {P} _ _ _.
Arguments RuAnd {P} _ _ _.

Fixpoint ru_literal_predicates {P} (items : list (literal P)) :
    list P * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 0])
  | item :: rest =>
      let p := pred (lit_atom item) in
      let '(tail, events) := ru_literal_predicates rest in
      (p :: tail, RuCase 0 :: RuCase 1 :: events ++ [RuCase 2])
  end.

Fixpoint ru_rule_predicates {P} (items : list (rule P)) :
    list P * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 3])
  | r :: rest =>
      let '(body_preds, first) := ru_literal_predicates (body r) in
      let head_preds := pred (head r) :: body_preds in
      let '(tail, events) := ru_rule_predicates rest in
      (head_preds ++ tail, RuCase 3 :: first ++ RuCase 4 :: events ++ [RuAppend (length
  head_preds)])
  end.

Fixpoint ru_fact_predicates {P} (facts : list (ground_atom P)) :
    list P * list (rules_universe_event P) :=
  match facts with
  | [] => ([], [RuCase 5])
  | (p, _) :: rest =>
      let '(tail, events) := ru_fact_predicates rest in
      (p :: tail, RuCase 5 :: events ++ [RuCase 6])
  end.

Fixpoint ru_term_constants {P} (terms : list term) :
    list positive * list (rules_universe_event P) :=
  match terms with
  | [] => ([], [RuCase 7])
  | t :: rest =>
      let current := match t with
      | TVar _ => []
      | TConst c => [c]
      end in
      let '(tail, events) := @ru_term_constants P rest in
      (current ++ tail, RuCase 7 :: RuCase 8 :: events ++ [RuAppend (length current)])
  end.

Fixpoint ru_literal_constants {P} (items : list (literal P)) :
    list positive * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 9])
  | item :: rest =>
      let '(head, first) := ru_term_constants (args (lit_atom item)) in
      let '(tail, events) := ru_literal_constants rest in
      (head ++ tail, RuCase 9 :: first ++ events ++ [RuAppend (length head)])
  end.

Fixpoint ru_rule_constants {P} (items : list (rule P)) :
    list positive * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 10])
  | r :: rest =>
      let '(head, head_events) := ru_term_constants (args (head r)) in
      let '(body, body_events) := ru_literal_constants (body r) in
      let rule_constants := head ++ body in
      let '(tail, tail_events) := ru_rule_constants rest in
      (rule_constants ++ tail, RuCase 10 :: head_events ++ body_events ++
        [RuAppend (length head)] ++ tail_events ++ [RuAppend (length rule_constants)])
  end.

Fixpoint ru_fact_constants {P} (facts : list (ground_atom P)) :
    list positive * list (rules_universe_event P) :=
  match facts with
  | [] => ([], [RuCase 11])
  | (_, row) :: rest =>
      let '(tail, events) := ru_fact_constants rest in
      (row ++ tail, RuCase 11 :: events ++ [RuAppend (length row)])
  end.

(** All three let bindings are evaluated once before the returned tuple predicate. *)
Definition rules_universe_prepare_counted {P} (prog : program P) (facts : list (ground_atom P))
  (p : P) :
    (bool * nat * FinSet.t positive) * list (rules_universe_event P) :=
  let '(rule_ps, rp_events) := ru_rule_predicates (rules prog) in
  let '(fact_ps, fp_events) := ru_fact_predicates facts in
  let ps := rule_ps ++ fact_ps in
  let '(pset, pset_events) := audit_finset_of_list (rules_encoder (penc prog)) ps in
  let '(present, present_events) := audit_finset_mem (rules_encoder (penc prog)) p pset in
  let n := arity prog p in
  let '(rule_cs, rc_events) := ru_rule_constants (rules prog) in
  let '(fact_cs, fc_events) := ru_fact_constants facts in
  let cs := rule_cs ++ fact_cs in
  let '(cset, cset_events) := audit_finset_of_list audit_positive_encode cs in
  ((present, n, cset), rp_events ++ fp_events ++ [RuAppend (length rule_ps);
    RuPredicatesSet ps pset pset_events; RuPredicateMem p pset present present_events;
    RuArity p n] ++ rc_events ++ fc_events ++ [RuAppend (length rule_cs);
    RuConstantsSet cs cset cset_events]).

Fixpoint ru_constants_check {P} (set : FinSet.t positive) (row : tuple) :
    bool * list (rules_universe_event P) :=
  match row with
  | [] => (true, [RuCase 12])
  | c :: rest =>
      let '(present, mem_events) := audit_finset_mem audit_positive_encode c set in
      let '(tail, events) := @ru_constants_check P set rest in
      (andb present tail, RuCase 12 :: RuConstantMem c set present mem_events :: events ++
        [RuAnd present tail (andb present tail)])
  end.

(** Nat.eqb recurses on the actual unary operands; each pair of constructors is an event. *)
Fixpoint ru_nat_eqb {P} (lhs rhs : nat) : bool * list (rules_universe_event P) :=
  match lhs, rhs with
  | O, O => (true, [RuNatEq O O true])
  | S a, S b =>
      let '(answer, events) := @ru_nat_eqb P a b in (answer, RuNatEq lhs rhs answer :: events)
  | _, _ => (false, [RuNatEq lhs rhs false])
  end.

Definition rules_universe_check_counted {P} (state : bool * nat * FinSet.t positive) (row : tuple) :
    bool * list (rules_universe_event P) :=
  let '(present, n, constants) := state in
  let '(arity_ok, arity_events) := @ru_nat_eqb P (length row) n in
  let first := andb present arity_ok in
  let '(constant_ok, constants_events) := @ru_constants_check P constants row in
  (andb first constant_ok, [RuCase 13; RuLength row] ++ arity_events ++ [RuAnd present arity_ok
  first] ++
    constants_events ++ [RuAnd first constant_ok (andb first constant_ok)]).

(** Erasing the universe model gives the original preparation and checks. *)
Definition rules_universe_erasure_statement : Prop :=
  forall P (prog : program P) facts p row,
    let '(state, _) := rules_universe_prepare_counted prog facts p in
    fst (@rules_universe_check_counted P state row) = in_universe prog facts p row.

Definition rules_universe_event_work {P} (event : rules_universe_event P) : nat :=
  match event with
  | RuPredicatesSet _ _ body
  | RuPredicateMem _ _ _ body =>
      1 + audit_finset_source_work (@length (rules_encode_entry P)) body
  | RuConstantsSet _ _ body
  | RuConstantMem _ _ _ body =>
      audit_finset_source_work audit_basic_encoding_work body
  | RuAppend size => 1 + size
  | RuLength row => 1 + length row
  | _ => 1
  end.

Definition rules_universe_event_budget {P} (E : encoding P) (event : rules_universe_event P) :
  nat :=
  match event with
  | RuPredicatesSet input _ _ =>
      12 + 12 * length input + 17 * fold_right (fun p n => Pos.size_nat (encode E p) + n) 0 input
  | RuPredicateMem p _ _ _ => 12 + 17 * Pos.size_nat (encode E p)
  | RuConstantsSet input _ _ =>
      audit_finset_of_list_budget audit_positive_encode audit_basic_encoding_work input
  | RuConstantMem c _ _ _ => 12 + 5 * Pos.size_nat c
  | RuAppend size => 1 + size
  | RuLength row => 1 + length row
  | _ => 1
  end.

Definition rules_universe_work {P} (events : list (rules_universe_event P)) : nat :=
  fold_right (fun event n => rules_universe_event_work event + n) 0 events.

Definition rules_universe_budget {P} (E : encoding P) (events : list (rules_universe_event P)) :
  nat :=
  fold_right (fun event n => rules_universe_event_budget E event + n) 0 events.

(** The selected event budget bounds universe preparation and checking work. *)
Definition rules_universe_selected_cost_statement : Prop :=
  forall P (prog : program P) facts p row,
    let '(state, prep_events) := rules_universe_prepare_counted prog facts p in
    let '(result, check_events) := @rules_universe_check_counted P state row in
    result = in_universe prog facts p row /\
    rules_universe_work (prep_events ++ check_events) <=
      rules_universe_budget (penc prog) (prep_events ++ check_events).
