(** * Strict shared join-relation snapshot

    This model retains each predicate, set construction, row enumeration and
    tail-first table update.
    For example, duplicate predicates trigger repeated insertion but share one row enumeration.
    Builds on: RulesJoin and collection models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditElements.
Import List.ListNotations.

Inductive rules_encode_entry (P : Type) : Type :=
  | RulesEncodeEntry (key : P) (code : positive).
Arguments RulesEncodeEntry {P} _ _.

Definition rules_encoder {P} (E : encoding P) (p : P) : positive * list (rules_encode_entry P) :=
  let code := encode E p in (code, [RulesEncodeEntry p code]).

Inductive rules_relation_event (P : Type) : Type :=
  | RulesRelationPredicate (atom : atom P) (predicate : P)
  | RulesRelationDistinct (keys : list P) (set : FinSet.t P)
      (body : list (audit_set_event P (rules_encode_entry P)))
  | RulesRelationKeys (set : FinSet.t P) (keys : list P)
      (body : list (audit_set_elements_event P))
  | RulesRelationEnv (predicate : P) (result : FinSet.t tuple)
  | RulesRelationRows (predicate : P) (input : FinSet.t tuple) (rows : list tuple)
      (body : list (audit_set_elements_event tuple))
  | RulesRelationSet (predicate : P) (rows : list tuple) (code : positive)
      (before after : Map.t P (list tuple)) (body : audit_trace (audit_trie_call (P * list tuple)))
  | RulesRelationCase (site : nat).
Arguments RulesRelationPredicate {P} _ _.
Arguments RulesRelationDistinct {P} _ _ _.
Arguments RulesRelationKeys {P} _ _ _.
Arguments RulesRelationEnv {P} _ _.
Arguments RulesRelationRows {P} _ _ _ _.
Arguments RulesRelationSet {P} _ _ _ _ _ _.
Arguments RulesRelationCase {P} _.

Fixpoint rules_relation_predicates {P} (atoms : list (atom P)) :
    list P * list (rules_relation_event P) :=
  match atoms with
  | [] => ([], [RulesRelationCase 0])
  | a :: rest =>
      let p := pred a in
      let '(tail, events) := rules_relation_predicates rest in
      (p :: tail, RulesRelationCase 0 :: RulesRelationPredicate a p :: events ++
        [RulesRelationCase 1])
  end.

Fixpoint rules_relation_rows_counted {P} (env : P -> FinSet.t tuple) (keys : list P) :
    list (list tuple) * list (rules_relation_event P) :=
  match keys with
  | [] => ([], [RulesRelationCase 2])
  | p :: rest =>
      let input := env p in
      let '(rows, body) := audit_finset_elements input in
      let '(tail, events) := rules_relation_rows_counted env rest in
      (rows :: tail, RulesRelationCase 2 :: RulesRelationEnv p input ::
        RulesRelationRows p input rows body :: events ++ [RulesRelationCase 3])
  end.

Fixpoint rules_relation_fill_counted {P} (E : encoding P) (keys : list P)
    (values : list (list tuple)) : Map.t P (list tuple) * list (rules_relation_event P) :=
  match keys, values with
  | p :: ps, rows :: vs =>
      let '(before, events) := rules_relation_fill_counted E ps vs in
      let code := encode E p in
      let '(after, body) := audit_trie_set code (p, rows) before in
      (after, RulesRelationCase 4 :: events ++ [RulesRelationSet p rows code before after body])
  | _, _ => (Map.empty, [RulesRelationCase 4])
  end.

Definition rules_join_relations_counted {P} (E : encoding P) (atoms : list (atom P))
    (env : P -> FinSet.t tuple) : Map.t P (list tuple) * list (rules_relation_event P) :=
  let '(predicates, pred_events) := rules_relation_predicates atoms in
  let '(distinct, set_events) := audit_finset_of_list (rules_encoder E) predicates in
  let '(keys, key_events) := audit_finset_elements distinct in
  let '(rows, row_events) := rules_relation_rows_counted env keys in
  let '(result, fill_events) := rules_relation_fill_counted E keys rows in
  (result, pred_events ++ [RulesRelationDistinct predicates distinct set_events;
    RulesRelationKeys distinct keys key_events] ++ row_events ++ fill_events).

(** Erasing the counted snapshot gives the original relation snapshot. *)
Definition rules_join_relations_erasure_statement : Prop :=
  forall P (E : encoding P) atoms env,
    fst (rules_join_relations_counted E atoms env) = prepare_join_relations E atoms env.

(** Each distinct relation is enumerated once in the snapshot. *)
Definition rules_join_relations_row_count_statement : Prop :=
  forall P (E : encoding P) atoms env,
    let '(result, events) := rules_join_relations_counted E atoms env in
    length (filter (fun e => match e with
    | RulesRelationEnv _ _ => true
    | _ => false
    end) events) =
      length (join_relation_keys E atoms).

(** The fixed set source fold counts the actual predicate encoder entry and trie body. *)
Definition rules_relation_set_event_work {P} (event : audit_set_event P (rules_encode_entry P))
  : nat :=
  match event with
  | AuditSetAdd _ _ _ _ enc body => length enc + audit_trie_update_trace_source_work body
  | AuditSetMem _ _ _ _ enc body => length enc + audit_trie_get_trace_source_work body
  | AuditSetRemove _ _ _ _ enc body => length enc + audit_trie_update_trace_source_work body
  | AuditSetFold _ _ => 1
  end.

Definition rules_relation_event_work {P} (event : rules_relation_event P) : nat :=
  match event with
  | RulesRelationDistinct _ _ body =>
      1 + audit_finset_source_work (@length (rules_encode_entry P)) body
  | RulesRelationKeys _ _ body => 1 + audit_set_elements_work body
  | RulesRelationRows _ _ _ body => 1 + audit_set_elements_work body
  | RulesRelationSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | _ => 1
  end.

Definition rules_relation_event_budget {P} (E : encoding P) (event : rules_relation_event P) :
  nat :=
  match event with
  | RulesRelationDistinct keys _ _ =>
      12 + 12 * length keys + 17 * fold_right (fun p n => Pos.size_nat (encode E p) + n) 0 keys
  | RulesRelationKeys set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | RulesRelationRows _ set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | RulesRelationSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | _ => 1
  end.

Definition rules_relation_work {P} (events : list (rules_relation_event P)) : nat :=
  fold_right (fun event n => rules_relation_event_work event + n) 0 events.

Definition rules_relation_budget {P} (E : encoding P) (events : list (rules_relation_event P)) :
  nat :=
  fold_right (fun event n => rules_relation_event_budget E event + n) 0 events.

(** The selected event budget bounds relation snapshot work. *)
Definition rules_join_relations_selected_cost_statement : Prop :=
  forall P (E : encoding P) atoms env,
    let '(result, events) := rules_join_relations_counted E atoms env in
    result = prepare_join_relations E atoms env /\
    rules_relation_work events <= rules_relation_budget E events.

(** A semantic-input recurrence bounds source blocks without consulting the emitted trace.
    External predicate-encoder and environment bodies require separate concrete adapters. *)
Fixpoint rules_relation_predicate_bits {P} (E : encoding P) (keys : list P) : nat :=
  match keys with
  | [] => 0
  | p :: tail => Pos.size_nat (encode E p) + rules_relation_predicate_bits E tail
  end.

Fixpoint rules_relation_input_rows_budget {P} (E : encoding P) (env : P -> FinSet.t tuple)
    (keys : list P) : nat :=
  match keys with
  | [] => 2
  | p :: tail =>
      let rows := env p in
      4 + (7 + 19 * audit_trie_nodes rows + audit_trie_output_bits rows) +
      (2 + 17 * Pos.size_nat (encode E p)) + rules_relation_input_rows_budget E env tail
  end.

Definition rules_join_relations_input_budget {P} (E : encoding P) (atoms : list (atom P))
    (env : P -> FinSet.t tuple) : nat :=
  let predicates := map pred atoms in
  let distinct := FinSet.of_list E predicates in
  let keys := FinSet.elements distinct in
  1 + 3 * length atoms +
    (12 + 12 * length predicates + 17 * rules_relation_predicate_bits E predicates) +
    (7 + 19 * audit_trie_nodes distinct + audit_trie_output_bits distinct) +
    rules_relation_input_rows_budget E env keys.

(** The input budget bounds relation snapshot work. *)
Definition rules_join_relations_input_bound_statement : Prop :=
  forall P (E : encoding P) atoms env,
    let '(out, events) := rules_join_relations_counted E atoms env in
    out = prepare_join_relations E atoms env /\
    rules_relation_work events <= rules_join_relations_input_budget E atoms env.
