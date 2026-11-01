(** * Counted nested-join probing

    This candidate fixes the actual bound-key, trie lookup, repeated-variable binding and
    flat-map source branches, preserving the selected rows and their original order.
    For example, a repeated variable is checked against its earlier binding.
    Builds on: RulesJoin and the shared finite-set, trie and encoding models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditPrimitive.
Import List.ListNotations.

Inductive rules_nested_probe_event : Type :=
  | RprobeBoundMem (variable : nat) (bound : FinSet.t nat) (result : bool)
      (body : list (audit_set_event nat audit_nat_encoding_event))
  | RprobeBindingGet (variable : nat) (code : positive) (binding : binding)
      (raw : option positive) (encoding_body : list audit_nat_encoding_event)
      (body : audit_trace (audit_trie_call (nat * positive)))
  | RprobeBindingSet (variable : nat) (value : positive) (code : positive)
      (before after : binding) (encoding_body : list audit_nat_encoding_event)
      (body : audit_trace (audit_trie_call (nat * positive)))
  | RprobeIndexGet (key : tuple) (code : positive) (index : tuple_index) (raw : option (list tuple))
      (encoding_body : list (audit_list_event positive (audit_basic_encoding_event positive)))
      (body : audit_trace (audit_trie_call (tuple * list tuple)))
  | RprobeEqual (left right : positive) (result : bool) (body : list audit_positive_eqb_event)
  | RprobeAppend (left_length : nat)
  | RprobeCase (site : nat).

Definition rules_probe_bound_term (bound : FinSet.t nat) (t : term) :
    bool * list rules_nested_probe_event :=
  match t with
  | TConst _ => (true, [RprobeCase 0])
  | TVar v =>
      let '(result, body) := audit_finset_mem audit_nat_encode v bound in
      (result, [RprobeCase 0; RprobeBoundMem v bound result body])
  end.

Fixpoint rules_probe_filter (bound : FinSet.t nat) (terms : list term) :
    list term * list rules_nested_probe_event :=
  match terms with
  | [] => ([], [RprobeCase 1])
  | t :: ts =>
      let '(keep, head) := rules_probe_bound_term bound t in
      let '(tail, events) := rules_probe_filter bound ts in
      (if keep then t :: tail else tail, RprobeCase 1 :: head ++ [RprobeCase 2] ++ events ++
        if keep then [RprobeCase 3] else [])
  end.

Definition rules_probe_value (b : binding) (v : nat) : positive * list rules_nested_probe_event :=
  let '(code, encoding_body) := audit_nat_encode v in
  let '(raw, body) := audit_map_code_get code b in
  (match raw with
  | Some value => value
  | None => 1%positive
  end,
   [RprobeBindingGet v code b raw encoding_body body; RprobeCase 4]).

Fixpoint rules_probe_instantiate (b : binding) (terms : list term) :
    tuple * list rules_nested_probe_event :=
  match terms with
  | [] => ([], [RprobeCase 5])
  | t :: ts =>
      let '(value, first) := match t with
        | TConst c => (c, [RprobeCase 6])
        | TVar v => let '(value, body) := rules_probe_value b v in
            (value, RprobeCase 6 :: body)
        end in
      let '(tail, events) := rules_probe_instantiate b ts in
      (value :: tail, RprobeCase 5 :: first ++ events ++ [RprobeCase 7])
  end.

Definition rules_bound_key_counted (bound : FinSet.t nat) (b : binding) (terms : list term) :
    tuple * list rules_nested_probe_event :=
  let '(selected, filtering) := rules_probe_filter bound terms in
  let '(key, instantiation) := rules_probe_instantiate b selected in
  (key, filtering ++ instantiation).

Definition rules_bind_term_counted (b : binding) (t : term) (value : positive) :
    option binding * list rules_nested_probe_event :=
  match t with
  | TConst expected =>
      let '(equal, body) := audit_positive_eqb value expected in
      (if equal then Some b else None,
       [RprobeCase 8; RprobeEqual value expected equal body; RprobeCase 9])
  | TVar v =>
      let '(code, encoding_body) := audit_nat_encode v in
      let '(raw, body) := audit_map_code_get code b in
      let prefix := [RprobeCase 8; RprobeBindingGet v code b raw encoding_body body; RprobeCase
  10] in
      match raw with
      | Some old =>
          let '(equal, equal_body) := audit_positive_eqb value old in
          (if equal then Some b else None,
           prefix ++ [RprobeEqual value old equal equal_body; RprobeCase 11])
      | None =>
          let '(write_code, write_encoding) := audit_nat_encode v in
          let '(after, set_body) := audit_trie_set write_code (v, value) b in
          (Some after, prefix ++ [RprobeBindingSet v value write_code b after write_encoding
  set_body])
      end
  end.

Fixpoint rules_bind_terms_counted (terms : list term) (row : tuple) (b : binding) :
    option binding * list rules_nested_probe_event :=
  match terms, row with
  | [], [] => (Some b, [RprobeCase 12])
  | t :: ts, value :: rest =>
      let '(next, first) := rules_bind_term_counted b t value in
      match next with
      | None => (None, RprobeCase 12 :: first ++ [RprobeCase 13])
      | Some updated =>
          let '(out, events) := rules_bind_terms_counted ts rest updated in
          (out, RprobeCase 12 :: first ++ RprobeCase 13 :: events)
      end
  | _, _ => (None, [RprobeCase 12])
  end.

Fixpoint rules_probe_rows (terms : list term) (b : binding) (rows : list tuple) :
    list binding * list rules_nested_probe_event :=
  match rows with
  | [] => ([], [RprobeCase 14])
  | row :: rest =>
      let '(candidate, first) := rules_bind_terms_counted terms row b in
      let prefix := match candidate with
      | Some result => [result]
      | None => []
      end in
      let '(tail, events) := rules_probe_rows terms b rest in
      (prefix ++ tail, RprobeCase 14 :: first ++ RprobeCase 15 :: events ++
        [RprobeAppend (length prefix)])
  end.

Fixpoint rules_probe_bindings (search : nested_search) (bindings : list binding) :
    list binding * list rules_nested_probe_event :=
  match bindings with
  | [] => ([], [RprobeCase 16])
  | b :: rest =>
      let '(key, key_events) := rules_bound_key_counted (nested_bound search) b (nested_terms
  search) in
      let '(code, encoding_body) := audit_list_encode audit_positive_encode key in
      let '(raw, get_body) := audit_map_code_get code (nested_index search) in
      let rows := match raw with
      | Some found => found
      | None => []
      end in
      let '(head, row_events) := rules_probe_rows (nested_terms search) b rows in
      let '(tail, tail_events) := rules_probe_bindings search rest in
      (head ++ tail, RprobeCase 16 :: key_events ++
        [RprobeIndexGet key code (nested_index search) raw encoding_body get_body; RprobeCase 17] ++
        row_events ++ tail_events ++ [RprobeAppend (length head)])
  end.

Fixpoint rules_run_nested_counted (searches : list nested_search) (bindings : list binding) :
    list binding * list rules_nested_probe_event :=
  match searches with
  | [] => (bindings, [RprobeCase 18])
  | search :: rest =>
      let '(next, first) := rules_probe_bindings search bindings in
      let '(result, events) := rules_run_nested_counted rest next in
      (result, RprobeCase 18 :: first ++ events)
  end.

(** Erasing nested probing gives the original binding results. *)
Definition rules_nested_probe_erasure_statement : Prop :=
  (forall bound b terms, fst (rules_bound_key_counted bound b terms) = bound_key bound b terms) /\
  (forall b term value, fst (rules_bind_term_counted b term value) = bind_term b term value) /\
  (forall terms row b, fst (rules_bind_terms_counted terms row b) = bind_terms terms row b) /\
  (forall search bindings, fst (rules_probe_bindings search bindings) = nested_probe search
  bindings) /\
  (forall searches bindings, fst (rules_run_nested_counted searches bindings) =
    run_nested searches bindings).

(** Each nonconstant library body is the actual nested frozen collection derivation. *)
Definition rules_nested_probe_event_work (event : rules_nested_probe_event) : nat :=
  match event with
  | RprobeBoundMem _ _ _ body => audit_finset_source_work audit_nat_events_work body
  | RprobeBindingGet _ _ _ _ encoding_body body =>
      1 + audit_nat_events_work encoding_body + audit_trie_get_trace_source_work body
  | RprobeBindingSet _ _ _ _ _ encoding_body body =>
      1 + audit_nat_events_work encoding_body + audit_trie_update_trace_source_work body
  | RprobeIndexGet _ _ _ _ encoding_body body =>
      1 + audit_list_events_work audit_basic_encoding_work encoding_body +
        audit_trie_get_trace_source_work body
  | RprobeEqual _ _ _ body => audit_positive_eqb_source_work body
  | RprobeAppend size => 1 + size
  | RprobeCase _ => 1
  end.

Definition rules_nat_encoder_budget (v : nat) : nat :=
  2 * S v * S (Pos.size_nat (encode nat_encoding v)).

Definition rules_nested_probe_event_budget (event : rules_nested_probe_event) : nat :=
  match event with
  | RprobeBoundMem v _ _ _ => 7 + rules_nat_encoder_budget v + 5 * Pos.size_nat (encode
  nat_encoding v)
  | RprobeBindingGet v code _ _ _ _ => 2 + rules_nat_encoder_budget v + 5 * Pos.size_nat code
  | RprobeBindingSet v _ code _ _ _ _ => 2 + rules_nat_encoder_budget v + 16 * Pos.size_nat code
  | RprobeIndexGet key code _ _ _ _ =>
      10 + 10 * length key + 20 * audit_encoded_bits audit_positive_encode key + 5 *
  Pos.size_nat code
  | RprobeEqual lhs rhs _ _ => 2 * Nat.min (Pos.size_nat lhs) (Pos.size_nat rhs)
  | RprobeAppend size => 1 + size
  | RprobeCase _ => 1
  end.

Definition rules_nested_probe_work (events : list rules_nested_probe_event) : nat :=
  fold_right (fun event n => rules_nested_probe_event_work event + n) 0 events.

Definition rules_nested_probe_budget (events : list rules_nested_probe_event) : nat :=
  fold_right (fun event n => rules_nested_probe_event_budget event + n) 0 events.

(** The selected event budget bounds nested probing work. *)
Definition rules_run_nested_selected_cost_statement : Prop :=
  forall searches bindings,
    let '(result, events) := rules_run_nested_counted searches bindings in
    result = run_nested searches bindings /\
    rules_nested_probe_work events <= rules_nested_probe_budget events.
