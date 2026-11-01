(** * Counted multiway candidate intersection and enumeration

    The model retains each table lookup, concrete shared set intersection and each value
    binding in the original order.
    For example, an empty intersection still executes the remaining probes.
    Builds on: RulesJoin and the frozen collection intersection model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditElements CollectionsAuditInter.
From Galois.Rules Require Import RulesAuditNestedProbe.
Import List.ListNotations.

Inductive rules_multi_probe_event : Type :=
  | RmProbeKey (events : list rules_nested_probe_event)
  | RmTableGet (key : tuple) (code : positive) (input : variable_index)
      (raw : option (FinSet.t positive))
      (encoding_body : list (audit_list_event positive (audit_basic_encoding_event positive)))
      (body : audit_trace (audit_trie_call (tuple * FinSet.t positive)))
  | RmIntersect (lhs rhs out : FinSet.t positive) (body : list (audit_inter_event positive))
  | RmElements (input : FinSet.t positive) (values : list positive)
      (body : list (audit_set_elements_event positive))
  | RmBind (events : list rules_nested_probe_event)
  | RmAppend (size : nat)
  | RmCase (site : nat).

Definition rules_variable_probe_counted (bound : FinSet.t nat) (b : binding)
    (search : variable_search) : FinSet.t positive * list rules_multi_probe_event :=
  let '(key, key_events) := rules_bound_key_counted bound b (variable_terms search) in
  let '(code, encoding_body) := audit_list_encode audit_positive_encode key in
  let '(raw, get_events) := audit_map_code_get code (variable_table search) in
  (match raw with
  | Some result => result
  | None => FinSet.empty
  end,
   [RmProbeKey key_events; RmTableGet key code (variable_table search) raw encoding_body get_events;
    RmCase 0]).

Fixpoint rules_intersect_domains_counted (bound : FinSet.t nat) (b : binding)
    (first : FinSet.t positive) (searches : list variable_search) :
    FinSet.t positive * list rules_multi_probe_event :=
  match searches with
  | [] => (first, [RmCase 1])
  | search :: rest =>
      let '(next, probe_events) := rules_variable_probe_counted bound b search in
      let '(intersection, inter_events) := audit_finset_inter first next in
      let '(out, tail) := rules_intersect_domains_counted bound b intersection rest in
      (out, RmCase 1 :: probe_events ++ RmIntersect first next intersection inter_events :: tail)
  end.

Definition rules_variable_candidates_counted (bound : FinSet.t nat) (b : binding)
    (searches : list variable_search) : FinSet.t positive * list rules_multi_probe_event :=
  match searches with
  | [] => (FinSet.empty, [RmCase 2])
  | search :: rest =>
      let '(first, probe_events) := rules_variable_probe_counted bound b search in
      let '(out, later) := rules_intersect_domains_counted bound b first rest in
      (out, RmCase 2 :: probe_events ++ later)
  end.

Fixpoint rules_multiway_values_counted (v : nat) (b : binding) (values : list positive) :
    list binding * list rules_multi_probe_event :=
  match values with
  | [] => ([], [RmCase 3])
  | value :: rest =>
      let '(candidate, bind_events) := rules_bind_term_counted b (TVar v) value in
      let head := match candidate with
      | Some result => [result]
      | None => []
      end in
      let '(tail, events) := rules_multiway_values_counted v b rest in
      (head ++ tail, RmCase 3 :: RmBind bind_events :: RmCase 4 :: events ++ [RmAppend (length
  head)])
  end.

Fixpoint rules_multiway_bindings_counted (search : multiway_search) (bindings : list binding) :
    list binding * list rules_multi_probe_event :=
  match bindings with
  | [] => ([], [RmCase 5])
  | b :: rest =>
      let '(set, candidate_events) := rules_variable_candidates_counted
        (multiway_bound search) b (multiway_domains search) in
      let '(values, element_events) := audit_finset_elements set in
      let '(head, value_events) := rules_multiway_values_counted (multiway_variable search) b
  values in
      let '(tail, tail_events) := rules_multiway_bindings_counted search rest in
      (head ++ tail, RmCase 5 :: candidate_events ++ RmElements set values element_events ::
        value_events ++ tail_events ++ [RmAppend (length head)])
  end.

Fixpoint rules_run_multiway_counted (searches : list multiway_search) (bindings : list binding) :
    list binding * list rules_multi_probe_event :=
  match searches with
  | [] => (bindings, [RmCase 6])
  | search :: rest =>
      let '(next, first) := rules_multiway_bindings_counted search bindings in
      let '(out, tail) := rules_run_multiway_counted rest next in
      (out, RmCase 6 :: first ++ tail)
  end.

(** Erasing multiway probing gives the original binding results. *)
Definition rules_multiway_probe_erasure_statement : Prop :=
  (forall bound b search, fst (rules_variable_probe_counted bound b search) = variable_probe
  bound b search) /\
  (forall bound b first searches, fst (rules_intersect_domains_counted bound b first searches) =
    intersect_variable_domains bound b first searches) /\
  (forall bound b searches, fst (rules_variable_candidates_counted bound b searches) =
    variable_candidates bound b searches) /\
  (forall search bindings, fst (rules_multiway_bindings_counted search bindings) =
    multiway_step search bindings) /\
  (forall searches bindings, fst (rules_run_multiway_counted searches bindings) =
    run_multiway searches bindings).

Definition rules_multi_probe_event_work (event : rules_multi_probe_event) : nat :=
  match event with
  | RmProbeKey events
  | RmBind events => rules_nested_probe_work events
  | RmTableGet _ _ _ _ encoding_body body =>
      1 + audit_list_events_work audit_basic_encoding_work encoding_body +
        audit_trie_get_trace_source_work body
  | RmIntersect _ _ _ body => audit_finset_inter_source_work body
  | RmElements _ _ body => audit_set_elements_work body
  | RmAppend size => 1 + size
  | RmCase _ => 1
  end.

Definition rules_multi_probe_event_budget (event : rules_multi_probe_event) : nat :=
  match event with
  | RmProbeKey events
  | RmBind events => rules_nested_probe_budget events
  | RmTableGet key code _ _ _ _ =>
      10 + 10 * length key + 20 * audit_encoded_bits audit_positive_encode key + 5 *
  Pos.size_nat code
  | RmIntersect lhs rhs _ _ => 2 + 30 * (audit_trie_nodes lhs + audit_trie_nodes rhs)
  | RmElements set _ _ => 6 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | RmAppend size => 1 + size
  | RmCase _ => 1
  end.

Definition rules_multi_probe_work (events : list rules_multi_probe_event) : nat :=
  fold_right (fun event n => rules_multi_probe_event_work event + n) 0 events.

Definition rules_multi_probe_budget (events : list rules_multi_probe_event) : nat :=
  fold_right (fun event n => rules_multi_probe_event_budget event + n) 0 events.

(** The selected event budget bounds multiway probing work. *)
Definition rules_run_multiway_selected_cost_statement : Prop :=
  forall searches bindings,
    let '(out, events) := rules_run_multiway_counted searches bindings in
    out = run_multiway searches bindings /\
    rules_multi_probe_work events <= rules_multi_probe_budget events.
