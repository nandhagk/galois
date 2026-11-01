(** * Counted nested-plan syntax phases

    The bounded parser and the head/member traversals preserve component order and stacks.
    For example, an open component parses its body before its following siblings.
    Builds on: FixpointNested and the counted collection models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointNested.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditNarrowDiscovery.
Import List.ListNotations.

Inductive fx_nested_plan_event (X C : Type) : Type :=
  | FnpParse (bound : nat) (remaining : wto X)
  | FnpRows (stack : list X) (code : nested_code X)
  | FnpHeads (code : nested_code X)
  | FnpLength (size : nat)
  | FnpAppend (size : nat)
  | FnpTarget (constraint : C) (out : X)
  | FnpMembersSet (x : X) (stack : list X) (code : positive) (before after : Map.t X (list X))
      (body : audit_trace (audit_trie_call (X * list X)))
  | FnpTargetRead (x : X) (code : positive) (before : Map.t X (list C)) (raw : option (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FnpTargetWrite (x : X) (code : positive) (value : list C) (before after : Map.t X (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FnpHeadsSet (heads : list X) (out : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FnpCase (site : nat).

Arguments FnpParse {X C} _ _.

Arguments FnpRows {X C} _ _.

Arguments FnpHeads {X C} _.

Arguments FnpLength {X C} _.

Arguments FnpAppend {X C} _.

Arguments FnpTarget {X C} _ _.

Arguments FnpMembersSet {X C} _ _ _ _ _ _.

Arguments FnpTargetRead {X C} _ _ _ _ _.

Arguments FnpTargetWrite {X C} _ _ _ _ _ _.

Arguments FnpHeadsSet {X C} _ _ _.

Arguments FnpCase {X C} _.

Fixpoint fx_nested_parse {X C} (bound : nat) (tokens : wto X) :
    (nested_code X * wto X) * list (fx_nested_plan_event X C) :=
  let here := [FnpParse bound tokens] in
  match bound with
  | 0 => ((NestedEnd, tokens), here)
  | S smaller =>
      match tokens with
      | [] => ((NestedEnd, []), here ++ [FnpCase 0])
      | WClose :: rest => ((NestedEnd, rest), here ++ [FnpCase 0])
      | WVertex x :: rest =>
          let '(result, events) := @fx_nested_parse X C smaller rest in
          let '(code, after) := result in
          ((NestedVisit x code, after), here ++ FnpCase 0 :: events ++ [FnpCase 1])
      | WOpen h :: rest =>
          let '(first, body_events) := @fx_nested_parse X C smaller rest in
          let '(body, after_body) := first in
          let '(second, tail_events) := @fx_nested_parse X C smaller after_body in
          let '(tail, after) := second in
          ((NestedComponent h body tail, after), here ++ FnpCase 0 :: body_events ++
            tail_events ++ [FnpCase 2])
      end
  end.

Definition fx_nested_tree {X C} (tokens : wto X) :
    nested_code X * list (fx_nested_plan_event X C) :=
  let '(out, events) := @fx_nested_parse X C (S (length tokens)) (tokens ++ [WClose]) in
  (fst out, FnpLength (length tokens) :: FnpAppend (length tokens) :: events).

Fixpoint fx_nested_rows {X C} (stack : list X) (code : nested_code X) :
    list (X * list X) * list (fx_nested_plan_event X C) :=
  match code with
  | NestedEnd => ([], [FnpRows stack code])
  | NestedVisit x rest =>
      let '(tail, events) := @fx_nested_rows X C stack rest in
      ((x, stack) :: tail, FnpRows stack code :: events ++ [FnpCase 3])
  | NestedComponent h body rest =>
      let '(first, body_events) := @fx_nested_rows X C (h :: stack) body in
      let '(second, rest_events) := @fx_nested_rows X C stack rest in
      ((h, h :: stack) :: first ++ second,
       FnpRows stack code :: body_events ++ rest_events ++ [FnpAppend (length first); FnpCase 4])
  end.

Fixpoint fx_nested_heads {X C} (code : nested_code X) :
    list X * list (fx_nested_plan_event X C) :=
  match code with
  | NestedEnd => ([], [FnpHeads code])
  | NestedVisit _ rest =>
      let '(tail, events) := @fx_nested_heads X C rest in (tail, FnpHeads code :: events)
  | NestedComponent h body rest =>
      let '(first, body_events) := @fx_nested_heads X C body in
      let '(second, rest_events) := @fx_nested_heads X C rest in
      (h :: first ++ second, FnpHeads code :: body_events ++ rest_events ++
        [FnpAppend (length first); FnpCase 5])
  end.

Fixpoint fx_nested_member_fold {X C} (EX : encoding X) (rows : list (X * list X)) :
    Map.t X (list X) * list (fx_nested_plan_event X C) :=
  match rows with
  | [] => (Map.empty, [FnpCase 6])
  | (x, stack) :: rest =>
      let '(before, tail) := @fx_nested_member_fold X C EX rest in
      let code := encode EX x in
      let '(after, body) := audit_trie_set code (x, stack) before in
      (after, FnpCase 6 :: tail ++ [FnpMembersSet x stack code before after body])
  end.

Definition fx_nested_members {X C} (EX : encoding X) (code : nested_code X) :
    Map.t X (list X) * list (fx_nested_plan_event X C) :=
  let '(rows, row_events) := @fx_nested_rows X C [] code in
  let '(members, fold_events) := @fx_nested_member_fold X C EX rows in
  (members, row_events ++ fold_events).

Fixpoint fx_nested_target_fold {X C A} (EX : encoding X) (S : System.t X C A) (cs : list C) :
    Map.t X (list C) * list (fx_nested_plan_event X C) :=
  match cs with
  | [] => (Map.empty, [FnpCase 7])
  | c :: rest =>
      let '(before, tail) := fx_nested_target_fold EX S rest in
      let x := System.target S c in
      let read_code := encode EX x in
      let '(raw, read_body) := audit_map_code_get read_code before in
      let old :=
        match raw with
        | Some values => values
        | None => []
        end in
      let value := c :: old in
      let write_code := encode EX x in
      let '(after, write_body) := audit_trie_set write_code (x, value) before in
      (after, FnpCase 7 :: tail ++
        [FnpTarget c x; FnpTargetRead x read_code before raw read_body; FnpCase 8;
         FnpTargetWrite x write_code value before after write_body])
  end.

Definition fx_nested_targets {X C A} (EX : encoding X) (S : System.t X C A) :
    Map.t X (list C) * list (fx_nested_plan_event X C) :=
  fx_nested_target_fold EX S (System.constraints S).

Definition fx_nested_plan_from_tokens {X C A} (EX : encoding X) (S : System.t X C A)
    (tokens : wto X) : NestedPlan.t X C * list (fx_nested_plan_event X C) :=
  let '(code, parse_events) := @fx_nested_tree X C tokens in
  let '(members, member_events) := @fx_nested_members X C EX code in
  let '(targets, target_events) := fx_nested_targets EX S in
  let '(heads, head_events) := @fx_nested_heads X C code in
  let '(head_set, set_events) := audit_finset_of_list (fx_index_encoder EX) heads in
  (NestedPlan.Make code members targets head_set,
    parse_events ++ member_events ++ target_events ++ head_events ++ [FnpHeadsSet heads head_set
  set_events]).

(** Erasing preparation events recovers the parsing, tree, membership, target and plan
    operations. *)
Definition fx_nested_plan_semantic_statement : Prop :=
  (forall X C bound tokens, fst (@fx_nested_parse X C bound tokens) = nested_parse bound tokens) /\
  (forall X C tokens, fst (@fx_nested_tree X C tokens) = nested_tree tokens) /\
  (forall X C stack code, fst (@fx_nested_rows X C stack code) = nested_rows stack code) /\
  (forall X C code, fst (@fx_nested_heads X C code) = nested_heads code) /\
  (forall X C (EX : encoding X) code, fst (@fx_nested_members X C EX code) = nested_members EX
  code) /\
  (forall X C A (EX : encoding X) (S : System.t X C A),
    fst (fx_nested_targets EX S) = nested_targets EX S) /\
  (forall X C A (EX : encoding X) (S : System.t X C A) tokens,
    fst (fx_nested_plan_from_tokens EX S tokens) =
      let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
        (nested_targets EX S) (FinSet.of_list EX (nested_heads code))).

Definition fx_nested_plan_event_work {X C} (event : fx_nested_plan_event X C) : nat :=
  match event with
  | FnpLength n
  | FnpAppend n => 1 + n
  | FnpMembersSet _ _ code _ _ body
  | FnpTargetWrite _ code _ _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FnpTargetRead _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FnpHeadsSet _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | _ => 1
  end.

Definition fx_nested_plan_event_budget {X C} (EX : encoding X) (event : fx_nested_plan_event X
  C) : nat :=
  match event with
  | FnpLength n
  | FnpAppend n => 1 + n
  | FnpMembersSet _ _ code _ _ _
  | FnpTargetWrite _ code _ _ _ _ => 2 + 17 * Pos.size_nat code
  | FnpTargetRead _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FnpHeadsSet heads _ _ =>
      12 + 12 * length heads + 17 * fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 heads
  | _ => 1
  end.

Definition fx_nested_plan_work {X C} (events : list (fx_nested_plan_event X C)) : nat :=
  fold_right (fun event n => fx_nested_plan_event_work event + n) 0 events.

Definition fx_nested_plan_budget {X C} (EX : encoding X) (events : list (fx_nested_plan_event X
  C)) : nat :=
  fold_right (fun event n => fx_nested_plan_event_budget EX event + n) 0 events.

(** Counted plan preparation returns the original plan and its selected work fits the trace
    budget. *)
Definition fx_nested_plan_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (S : System.t X C A) tokens,
    let '(result, events) := fx_nested_plan_from_tokens EX S tokens in
    result = (let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
      (nested_targets EX S) (FinSet.of_list EX (nested_heads code))) /\
    fx_nested_plan_work events <= fx_nested_plan_budget EX events.

(** This bound is computed from the original token list, code-derived rows and actual
    constraint targets, independently of the observer's event list. *)

Definition fx_nested_plan_input_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (tokens : wto X) : nat :=
  let code := nested_tree tokens in
  let rows := nested_rows [] code in
  let heads := nested_heads code in
  let targets := map (System.target S) (System.constraints S) in
  let size := 1 + length tokens + length (System.constraints S) in
  200 * size * size * size +
  40 * (fx_index_input_bits EX (map fst rows) + fx_index_input_bits EX heads +
        fx_index_input_bits EX targets).

(** Counted plan preparation returns the original plan and its work fits an input-derived budget. *)
Definition fx_nested_plan_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (S : System.t X C A) tokens,
    let '(result, events) := fx_nested_plan_from_tokens EX S tokens in
    result = (let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
      (nested_targets EX S) (FinSet.of_list EX (nested_heads code))) /\
    fx_nested_plan_work events <= fx_nested_plan_input_budget EX S tokens.
