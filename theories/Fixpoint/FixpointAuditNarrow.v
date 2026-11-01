(** * Checked simultaneous narrowing model

    Output discovery is computed once, passes read their original input, and the final
    full checker decides whether the candidate or original map is returned.
    For example, a failed final check returns the original assignment.
    Builds on: FixpointNarrow and the counted index, query and checker models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointNarrow.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditNarrowCheck FixpointAuditNarrowDiscovery.
Import List.ListNotations.

Inductive fx_narrow_event (X C A : Type) : Type :=
  | FnarrowDep (body : list (fx_dependency_event X C))
  | FnarrowQuery (body : audit_trace (fx_declared_call X C A))
  | FnarrowCheck (body : list (fx_fullcheck_event X C A))
  | FnarrowRhs (c : C) (out : Query.t X A)
  | FnarrowTarget (c : C) (out : X)
  | FnarrowJoin (lhs rhs out : A)
  | FnarrowLeb (lhs rhs : A) (out : bool)
  | FnarrowNarrow (lhs rhs out : A)
  | FnarrowIndexGet (x : X) (code : positive) (input : Map.t X (list C)) (raw : option (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FnarrowSet (x : X) (value : A) (code : positive) (input output : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FnarrowCase (site : nat).

Arguments FnarrowDep {X C A} _.

Arguments FnarrowQuery {X C A} _.

Arguments FnarrowCheck {X C A} _.

Arguments FnarrowRhs {X C A} _ _.

Arguments FnarrowTarget {X C A} _ _.

Arguments FnarrowJoin {X C A} _ _ _.

Arguments FnarrowLeb {X C A} _ _ _.

Arguments FnarrowNarrow {X C A} _ _ _.

Arguments FnarrowIndexGet {X C A} _ _ _ _ _.

Arguments FnarrowSet {X C A} _ _ _ _ _ _.

Arguments FnarrowCase {X C A} _.

Section Narrow.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Definition fx_narrow_write (x : X) (value : A) (before : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  let code := encode EX x in
  let '(after, body) := audit_trie_set code (x, value) before in
  (after, [FnarrowSet x value code before after body]).

Fixpoint fx_narrow_collect (updates : list (X * A)) (acc : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match updates with
  | [] => (acc, [FnarrowCase 0])
  | (x, value) :: rest =>
      let '(old, read_events) := @fx_model_lookup X C A EX L acc x in
      let joined := join L old value in
      let '(next, write_events) := fx_narrow_write x joined acc in
      let '(out, events) := fx_narrow_collect rest next in
      (out, FnarrowCase 0 :: FnarrowQuery read_events :: FnarrowJoin old value joined ::
        write_events ++ events)
  end.

Fixpoint fx_narrow_constraints (input : assignment X A) (cs : list C) (acc : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match cs with
  | [] => (acc, [FnarrowCase 1])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs input in
      let '(value, _, sides) := answer in
      let target := System.target S c in
      let '(next, collect_events) := fx_narrow_collect ((target, value) :: sides) acc in
      let '(out, tail) := fx_narrow_constraints input rest next in
      (out, FnarrowCase 1 :: FnarrowRhs c rhs :: FnarrowQuery query_events :: FnarrowTarget c
  target ::
        collect_events ++ tail)
  end.

Definition fx_narrow_output (input sums acc : assignment X A) (x : X) :
    assignment X A * list (fx_narrow_event X C A) :=
  let '(old, old_events) := @fx_model_lookup X C A EX L input x in
  let '(value, value_events) := @fx_model_lookup X C A EX L sums x in
  let below := leb L value old in
  let result := if below then narrow L old value else old in
  let branch := if below then [FnarrowNarrow old value result] else [] in
  let '(out, write_events) := fx_narrow_write x result acc in
  (out, FnarrowQuery old_events :: FnarrowQuery value_events :: FnarrowLeb value old below ::
    FnarrowCase 2 :: branch ++ write_events).

Fixpoint fx_narrow_outputs (input sums : assignment X A) (outputs : list X) (acc : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match outputs with
  | [] => (acc, [FnarrowCase 3])
  | x :: rest =>
      let code := encode EX x in
      let '(raw, body) := audit_map_code_get code (contributors ix) in
      let cs :=
        match raw with
        | Some found => found
        | None => []
        end in
      let '(next, events) :=
        match cs with
        | [] => (acc, [FnarrowCase 4])
        | _ :: _ => let '(out, body) := fx_narrow_output input sums acc x in
            (out, FnarrowCase 4 :: body)
        end in
      let '(out, tail) := fx_narrow_outputs input sums rest next in
      (out, FnarrowCase 3 :: FnarrowIndexGet x code (contributors ix) raw body :: events ++ tail)
  end.

Definition fx_narrow_pass (outputs : list X) (input : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  let '(sums, sum_events) := fx_narrow_constraints input (System.constraints S) Map.empty in
  let '(out, output_events) := fx_narrow_outputs input sums outputs input in
  (out, sum_events ++ output_events).

Fixpoint fx_narrow_iter (rounds : nat) (outputs : list X) (input : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match rounds with
  | 0 => (input, [FnarrowCase 5])
  | Datatypes.S rest =>
      let '(before, events) := fx_narrow_iter rest outputs input in
      let '(out, pass_events) := fx_narrow_pass outputs before in
      (out, FnarrowCase 5 :: events ++ pass_events)
  end.

Definition fx_narrow_checked_counted (rounds : nat) (input : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  let '(all, all_events) := fx_dependency_outputs_input S SS (System.constraints S) in
  let '(outputs, distinct_events) := @fx_dependency_distinct X C EX all in
  let '(candidate, pass_events) := fx_narrow_iter rounds outputs input in
  let '(accepted, check_events) := fx_fullcheck_counted EX L S candidate in
  (if accepted then candidate else input,
   FnarrowDep all_events :: FnarrowDep distinct_events :: pass_events ++
    [FnarrowCheck check_events; FnarrowCase 6]).

(** Discarding counted narrowing events yields the original checked narrowing result. *)
Definition fx_narrow_checked_erasure_statement : Prop :=
  forall rounds input, fst (fx_narrow_checked_counted rounds input) =
    narrow_checked EX L S SS ix rounds input.

End Narrow.

Definition fx_narrow_event_work {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_narrow_event X C A) : nat :=
  match event with
  | FnarrowDep body => fx_dependency_work EX body
  | FnarrowQuery body => fx_declared_model_work EC body
  | FnarrowCheck body => fx_fullcheck_work EC body
  | FnarrowIndexGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FnarrowSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | _ => 1
  end.

Definition fx_narrow_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_narrow_event X C A) : nat :=
  match event with
  | FnarrowDep body => fx_dependency_budget EX body
  | FnarrowQuery body => audit_work body + fx_declared_primitive_budget EC body
  | FnarrowCheck body => fx_fullcheck_budget EC body
  | FnarrowIndexGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FnarrowSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | _ => 1
  end.

Definition fx_narrow_work {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_narrow_event X C A)) : nat :=
  fold_right (fun e n => fx_narrow_event_work EX EC e + n) 0 events.

Definition fx_narrow_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_narrow_event X C A)) : nat :=
  fold_right (fun e n => fx_narrow_event_budget EX EC e + n) 0 events.

(** Checked narrowing returns the original result and its selected work fits the trace-derived
    budget. *)
Definition fx_narrow_checked_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix rounds input,
    let '(out, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    out = narrow_checked EX L S SS ix rounds input /\
    fx_narrow_work EX EC events <= fx_narrow_budget EX EC events.

(** Input and intermediate-state recurrences below do not consume an observed event list.
    Evaluation of these mathematical budget functions is not part of the source claim. *)

Fixpoint fx_narrow_discovery_rows_budget {X C A} (S : System.t X C A) (SS : System.static S)
    (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 4 + length (System.target S c :: side_targets SS c) +
      fx_narrow_discovery_rows_budget S SS rest
  end.

Definition fx_narrow_discovery_input_budget {X C A} (EX : encoding X)
    (S : System.t X C A) (SS : System.static S) : nat :=
  let rows := flat_map (fun c => System.target S c :: side_targets SS c) (System.constraints S) in
  let set := FinSet.of_list EX rows in
  fx_narrow_discovery_rows_budget S SS (System.constraints S) +
    20 + 12 * length rows + 17 * fx_index_input_bits EX rows +
      19 * audit_trie_nodes set + audit_trie_output_bits set.

Fixpoint fx_narrow_collect_input_budget {X A} (EX : encoding X) (updates : list (X * A)) : nat :=
  match updates with
  | [] => 1
  | (x, _) :: rest => 4 + fx_fullcheck_lookup_input_budget EX x +
      17 * Pos.size_nat (encode EX x) + fx_narrow_collect_input_budget EX rest
  end.

Fixpoint fx_narrow_constraints_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (input : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L input) in
      3 + fx_fullcheck_query_input_budget EX L input rhs +
      fx_narrow_collect_input_budget EX ((System.target S c, value) :: sides) +
      fx_narrow_constraints_input_budget EX L S input rest
  end.

Fixpoint fx_narrow_outputs_input_budget {X C} (EX : encoding X) (ix : sys_index X C)
    (outputs : list X) : nat :=
  match outputs with
  | [] => 1
  | x :: rest =>
      2 + (2 + 6 * Pos.size_nat (encode EX x)) +
      (
        match contributors_of EX ix x with
        | [] => 0
        | _ :: _ => 3 + 2 * fx_fullcheck_lookup_input_budget EX x +
           (2 + 17 * Pos.size_nat (encode EX x))
        end) + fx_narrow_outputs_input_budget EX ix rest
  end.

Definition fx_narrow_pass_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (outputs : list X) (input : assignment X A) : nat :=
  fx_narrow_constraints_input_budget EX L S input (System.constraints S) +
  fx_narrow_outputs_input_budget EX ix outputs.

Fixpoint fx_narrow_rounds_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (outputs : list X) (rounds : nat) (input : assignment X A) : nat :=
  match rounds with
  | 0 => 1
  | Datatypes.S rest =>
      let before := Nat.iter rest (narrow_pass EX L S SS ix) input in
      1 + fx_narrow_rounds_input_budget EX L S SS ix outputs rest input +
        fx_narrow_pass_input_budget EX L S ix outputs before
  end.

Definition fx_narrow_checked_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (rounds : nat) (input : assignment X A) : nat :=
  let outputs := distinct_unknowns EX (flat_map (fun c =>
    System.target S c :: side_targets SS c) (System.constraints S)) in
  let candidate := Nat.iter rounds (narrow_pass EX L S SS ix) input in
  1 + fx_narrow_discovery_input_budget EX S SS +
    fx_narrow_rounds_input_budget EX L S SS ix outputs rounds input +
    fx_fullcheck_input_budget EX L S candidate.

(** Checked narrowing returns the original result and its work fits an input-derived budget. *)
Definition fx_narrow_checked_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix rounds input,
    let '(out, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    out = narrow_checked EX L S SS ix rounds input /\
    fx_narrow_work EX EC events <= fx_narrow_checked_input_budget EX L S SS ix rounds input.

(** A source-shaped derivation explicitly composes the actual output-discovery calls,
    pass iteration, checker and selected branch on one candidate. *)

Inductive fx_narrow_checked_run {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (rounds : nat) (input : assignment X A) : assignment X A -> list (fx_narrow_event X C A) ->
  Prop :=
  | FxNarrowCheckedRun : forall all all_events outputs distinct_events candidate pass_events
  accepted check_events,
      fx_dependency_outputs_input S SS (System.constraints S) = (all, all_events) ->
      @fx_dependency_distinct X C EX all = (outputs, distinct_events) ->
      fx_narrow_iter EX L S ix rounds outputs input = (candidate, pass_events) ->
      fx_fullcheck_counted EX L S candidate = (accepted, check_events) ->
      fx_narrow_checked_run EX L S SS ix rounds input (if accepted then candidate else input)
        (FnarrowDep all_events :: FnarrowDep distinct_events :: pass_events ++
          [FnarrowCheck check_events; FnarrowCase 6]).

(** The result and events of each counted narrowing execution satisfy the narrowing run relation. *)
Definition fx_narrow_run_total_statement : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix rounds input,
    let '(result, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    fx_narrow_checked_run EX L S SS ix rounds input result events.

(** Every narrowing run returns the uncounted checked result within the input-derived work
    budget. *)
Definition fx_narrow_run_correct_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix rounds input result events,
    fx_narrow_checked_run EX L S SS ix rounds input result events ->
    result = narrow_checked EX L S SS ix rounds input /\
    fx_narrow_work EX EC events <= fx_narrow_checked_input_budget EX L S SS ix rounds input.
