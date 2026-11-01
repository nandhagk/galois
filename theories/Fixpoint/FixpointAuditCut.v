(** * Counted cut-certificate expansion

    Each validation, query, contributor lookup and output write retains its concrete input,
    result and nested library execution.
    For example, an output write retains its concrete input and nested execution.
    Builds on: FixpointCut and the shared models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCut.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditPrimitive.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

Definition fx_cut_set_nested_work {X} (event : audit_set_event X (fx_encoder_entry X)) : nat :=
  match event with
  | AuditSetAdd _ _ _ _ enc trie
  | AuditSetRemove _ _ _ _ enc trie =>
      List.length enc + audit_trie_update_trace_source_work trie
  | AuditSetMem _ _ _ _ enc trie => List.length enc + audit_trie_get_trace_source_work trie
  | AuditSetFold _ _ => 0
  end.

Inductive fx_cut_event (X C A : Type) : Type :=
  | FxCutSetMem (x : X) (set : FinSet.t X) (out : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxCutSetAdd (x : X) (before after : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxCutMapGet (x : X) (code : positive) (before : assignment X A) (raw : option A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxCutMapSet (x : X) (value : A) (code : positive) (before after : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxCutIndexGet (x : X) (code : positive) (before : Map.t X (list C)) (raw : option (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FxCutElements (set : FinSet.t X) (items : list X) (body : list (audit_set_elements_event X))
  | FxCutQuery (body : audit_trace (fx_declared_call X C A))
  | FxCutRhs (c : C) (out : Query.t X A)
  | FxCutTarget (c : C) (out : X)
  | FxCutSides (c : C) (out : list X)
  | FxCutEqual (x y : X) (cx cy : positive) (out : bool) (body : list audit_positive_eqb_event)
  | FxCutJoin (lhs rhs out : A)
  | FxCutLeb (lhs rhs : A) (out : bool)
  | FxCutBool (lhs rhs out : bool)
  | FxCutCase (site : nat).

Arguments FxCutSetMem {X C A} _ _ _ _.

Arguments FxCutSetAdd {X C A} _ _ _ _.

Arguments FxCutMapGet {X C A} _ _ _ _ _.

Arguments FxCutMapSet {X C A} _ _ _ _ _ _.

Arguments FxCutIndexGet {X C A} _ _ _ _ _.

Arguments FxCutElements {X C A} _ _ _.

Arguments FxCutQuery {X C A} _.

Arguments FxCutRhs {X C A} _ _.

Arguments FxCutTarget {X C A} _ _.

Arguments FxCutSides {X C A} _ _.

Arguments FxCutEqual {X C A} _ _ _ _ _ _.

Arguments FxCutJoin {X C A} _ _ _.

Arguments FxCutLeb {X C A} _ _ _.

Arguments FxCutBool {X C A} _ _ _.

Arguments FxCutCase {X C A} _.

Section CutModel.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Definition fx_cut_map_mem (m : assignment X A) (x : X) : bool * list (fx_cut_event X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code m in
  (
    match raw with
    | Some _ => true
    | None => false
    end, [FxCutMapGet x code m raw body; FxCutCase 0]).

Definition fx_cut_index_get (x : X) : list C * list (fx_cut_event X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code (contributors ix) in
  (
    match raw with
    | Some cs => cs
    | None => []
    end,
   [FxCutIndexGet x code (contributors ix) raw body; FxCutCase 1]).

Definition fx_cut_equal (x y : X) : bool * list (fx_cut_event X C A) :=
  let cx := encode EX x in
  let cy := encode EX y in
  let '(out, body) := audit_positive_eqb cx cy in
  (out, [FxCutEqual x y cx cy out body]).

Definition fx_cut_store (m : assignment X A) (x : X) (a : A) :
    assignment X A * list (fx_cut_event X C A) :=
  let code := encode EX x in
  let '(out, body) := audit_trie_set code (x, a) m in
  (out, [FxCutMapSet x a code m out body]).

Fixpoint fx_cut_seed (xs : list X) (stored_values : assignment X A) :
    assignment X A * list (fx_cut_event X C A) :=
  match xs with
  | [] => (Map.empty, [FxCutCase 2])
  | x :: rest =>
      let '(value, get_events) := @fx_model_lookup X C A EX L stored_values x in
      let '(before, tail) := fx_cut_seed rest stored_values in
      let '(out, set_events) := fx_cut_store before x value in
      (out, FxCutCase 2 :: FxCutQuery get_events :: tail ++ set_events)
  end.

Fixpoint fx_cut_prepare (xs : list X) (seen : FinSet.t X) :
    option (FinSet.t X) * list (fx_cut_event X C A) :=
  match xs with
  | [] => (Some seen, [FxCutCase 3])
  | x :: rest =>
      let '(present, mem_body) := audit_finset_mem (fx_index_encoder EX) x seen in
      let prefix := [FxCutCase 3; FxCutSetMem x seen present mem_body; FxCutCase 4] in
      if present then (None, prefix)
      else let '(next, add_body) := audit_finset_add (fx_index_encoder EX) x seen in
        let '(out, events) := fx_cut_prepare rest next in
        (out, prefix ++ FxCutSetAdd x seen next add_body :: events)
  end.

Fixpoint fx_cut_coverage_outputs (covered : FinSet.t X) (xs : list X) :
    bool * list (fx_cut_event X C A) :=
  match xs with
  | [] => (true, [FxCutCase 5])
  | x :: rest =>
      let '(head, body) := audit_finset_mem (fx_index_encoder EX) x covered in
      let '(tail, events) := fx_cut_coverage_outputs covered rest in
      (andb head tail, FxCutCase 5 :: FxCutSetMem x covered head body :: events ++
        [FxCutBool head tail (andb head tail)])
  end.

Fixpoint fx_cut_coverage_constraints (covered : FinSet.t X) (cs : list C) :
    bool * list (fx_cut_event X C A) :=
  match cs with
  | [] => (true, [FxCutCase 6])
  | c :: rest =>
      let target := System.target S c in
      let sides := side_targets SS c in
      let '(head, first) := fx_cut_coverage_outputs covered (target :: sides) in
      let '(tail, events) := fx_cut_coverage_constraints covered rest in
      (andb head tail, FxCutCase 6 :: FxCutTarget c target :: FxCutSides c sides ::
        first ++ events ++ [FxCutBool head tail (andb head tail)])
  end.

Definition fx_cut_ready (cur : assignment X A) (y : X) : bool * list (fx_cut_event X C A) :=
  let '(present, mem_events) := fx_cut_map_mem cur y in
  let '(contributors, index_events) := fx_cut_index_get y in
  let empty :=
    match contributors with
    | [] => true
    | _ :: _ => false
    end in
  (orb present empty, mem_events ++ index_events ++ [FxCutCase 7; FxCutBool present empty (orb
    present empty)]).

Fixpoint fx_cut_ready_all (cur : assignment X A) (reads : list X) :
    bool * list (fx_cut_event X C A) :=
  match reads with
  | [] => (true, [FxCutCase 8])
  | x :: rest =>
      let '(head, first) := fx_cut_ready cur x in
      let '(tail, events) := fx_cut_ready_all cur rest in
      (andb head tail, FxCutCase 8 :: first ++ events ++ [FxCutBool head tail (andb head tail)])
  end.

Fixpoint fx_cut_join (x : X) (updates : list (X * A)) (acc : A) :
    A * list (fx_cut_event X C A) :=
  match updates with
  | [] => (acc, [FxCutCase 9])
  | (y, value) :: rest =>
      let '(equal, eq_events) := fx_cut_equal x y in
      let next := if equal then join L acc value else acc in
      let branch := if equal then [FxCutJoin acc value next] else [] in
      let '(out, tail) := fx_cut_join x rest next in
      (out, FxCutCase 9 :: eq_events ++ FxCutCase 10 :: branch ++ tail)
  end.

Fixpoint fx_cut_gather (x : X) (cs : list C) (cur : assignment X A) (acc : A) :
    option A * list (fx_cut_event X C A) :=
  match cs with
  | [] => (Some acc, [FxCutCase 11])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs cur in
      let '(value, reads, sides) := answer in
      let '(ready, ready_events) := fx_cut_ready_all cur reads in
      let prefix := [FxCutCase 11; FxCutRhs c rhs; FxCutQuery query_events] ++
        ready_events ++ [FxCutCase 12] in
      if ready then
        let target := System.target S c in
        let '(next, join_events) := fx_cut_join x ((target, value) :: sides) acc in
        let '(out, events) := fx_cut_gather x rest cur next in
        (out, prefix ++ FxCutTarget c target :: join_events ++ events)
      else (None, prefix)
  end.

Fixpoint fx_cut_compute (xs : list X) (cur : assignment X A) :
    option (assignment X A) * list (fx_cut_event X C A) :=
  match xs with
  | [] => (Some cur, [FxCutCase 13])
  | x :: rest =>
      let '(present, mem_events) := fx_cut_map_mem cur x in
      let prefix := FxCutCase 13 :: mem_events ++ [FxCutCase 14] in
      if present then (None, prefix)
      else
        let '(cs, index_events) := fx_cut_index_get x in
        let '(value, gather_events) := fx_cut_gather x cs cur (bot L) in
        match value with
        | None => (None, prefix ++ index_events ++ gather_events ++ [FxCutCase 15])
        | Some a =>
            let '(next, write_events) := fx_cut_store cur x a in
            let '(out, later) := fx_cut_compute rest next in
            (out, prefix ++ index_events ++ gather_events ++ FxCutCase 15 :: write_events ++ later)
        end
  end.

Definition fx_cut_compare_value (m : assignment X A) (x y : X) (value : A) :
    bool * list (fx_cut_event X C A) :=
  let '(equal, eq_events) := fx_cut_equal x y in
  if equal then
    let '(old, read_events) := @fx_model_lookup X C A EX L m x in
    let le := leb L value old in
    (le, eq_events ++ [FxCutCase 16; FxCutQuery read_events; FxCutLeb value old le])
  else (true, eq_events ++ [FxCutCase 16]).

Fixpoint fx_cut_check_sides (m : assignment X A) (x : X) (sides : list (X * A)) :
    bool * list (fx_cut_event X C A) :=
  match sides with
  | [] => (true, [FxCutCase 17])
  | (y, value) :: rest =>
      let '(head, first) := fx_cut_compare_value m x y value in
      let '(tail, later) := fx_cut_check_sides m x rest in
      (andb head tail, FxCutCase 17 :: first ++ later ++ [FxCutBool head tail (andb head tail)])
  end.

Fixpoint fx_cut_check_constraints (m : assignment X A) (x : X) (cs : list C) :
    bool * list (fx_cut_event X C A) :=
  match cs with
  | [] => (true, [FxCutCase 18])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs m in
      let '(value, _, sides) := answer in
      let target := System.target S c in
      let '(head, compare_events) := fx_cut_compare_value m x target value in
      let '(side_ok, side_events) := fx_cut_check_sides m x sides in
      let current := andb head side_ok in
      let '(tail, later) := fx_cut_check_constraints m x rest in
      (andb current tail, FxCutCase 18 :: FxCutRhs c rhs :: FxCutQuery query_events ::
        FxCutTarget c target :: compare_events ++ side_events ++
        FxCutBool head side_ok current :: later ++ [FxCutBool current tail (andb current tail)])
  end.

Definition fx_cut_check_at (m : assignment X A) (x : X) : bool * list (fx_cut_event X C A) :=
  let '(cs, index_events) := fx_cut_index_get x in
  let '(out, events) := fx_cut_check_constraints m x cs in
  (out, index_events ++ events).

Fixpoint fx_cut_check_all (m : assignment X A) (xs : list X) : bool * list (fx_cut_event X C A) :=
  match xs with
  | [] => (true, [FxCutCase 19])
  | x :: rest =>
      let '(head, first) := fx_cut_check_at m x in
      let '(tail, events) := fx_cut_check_all m rest in
      (andb head tail, FxCutCase 19 :: first ++ events ++ [FxCutBool head tail (andb head tail)])
  end.

Definition fx_cut_expand_counted (cert : cut_certificate X A) :
    option (assignment X A) * list (fx_cut_event X C A) :=
  let '(covered, prepare_events) := fx_cut_prepare (plan cert) (cuts cert) in
  match covered with
  | None => (None, prepare_events ++ [FxCutCase 20])
  | Some cover =>
      let '(complete, coverage_events) := fx_cut_coverage_constraints cover (System.constraints S)
        in
      let prefix := prepare_events ++ FxCutCase 20 :: coverage_events ++ [FxCutCase 21] in
      if complete then
        let '(xs, elements_body) := audit_finset_elements (cuts cert) in
        let '(seed, seed_events) := fx_cut_seed xs (stored cert) in
        let '(computed, compute_events) := fx_cut_compute (plan cert) seed in
        let mid := prefix ++ FxCutElements (cuts cert) xs elements_body :: seed_events ++
          compute_events ++ [FxCutCase 22] in
        match computed with
        | None => (None, mid)
        | Some m =>
            let '(checks, check_elements) := audit_finset_elements (cuts cert) in
            let '(ok, check_events) := fx_cut_check_all m checks in
            (if ok then Some m else None,
             mid ++ FxCutElements (cuts cert) checks check_elements :: check_events ++ [FxCutCase
               23])
        end
      else (None, prefix)
  end.

(** Erasing each counted cut phase recovers its corresponding uncounted operation, including
    expansion. *)
Definition fx_cut_model_erasure_statement : Prop :=
  (forall xs m, fst (fx_cut_seed xs m) = cut_seed EX xs (lookup EX L m)) /\
  (forall xs seen, fst (fx_cut_prepare xs seen) = cut_prepare EX xs seen) /\
  (forall covered, fst (fx_cut_coverage_constraints covered (System.constraints S)) =
    cut_coverage EX S SS covered) /\
  (forall cur y, fst (fx_cut_ready cur y) = cut_ready EX ix cur y) /\
  (forall x ups a, fst (fx_cut_join x ups a) = cut_join EX L x ups a) /\
  (forall x cs cur a, fst (fx_cut_gather x cs cur a) = cut_gather EX L S ix x cs cur a) /\
  (forall xs cur, fst (fx_cut_compute xs cur) = cut_compute EX L S ix xs cur) /\
  (forall m x, fst (fx_cut_check_at m x) = cut_check_at EX L S ix m x) /\
  forall cert, fst (fx_cut_expand_counted cert) = expand EX L S SS ix cert.

End CutModel.

(** Selected fixed source-block allowances retain each nested primitive derivation. *)

Definition fx_cut_event_work {X C A} (EC : encoding C) (event : fx_cut_event X C A) : nat :=
  match event with
  | FxCutSetMem _ _ _ body
  | FxCutSetAdd _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxCutMapGet _ code _ _ body
  | FxCutIndexGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FxCutMapSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FxCutElements _ _ body => 1 + audit_set_elements_work body
  | FxCutQuery body => fx_declared_model_work EC body
  | FxCutEqual _ _ cx cy _ body =>
      audit_encoding_weight (Pos.size_nat cx) + audit_encoding_weight (Pos.size_nat cy) +
      audit_positive_eqb_source_work body
  | _ => 1
  end.

Definition fx_cut_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_cut_event X C A) : nat :=
  match event with
  | FxCutSetMem x _ _ _ => 12 + 5 * Pos.size_nat (encode EX x)
  | FxCutSetAdd x _ _ _ => 12 + 17 * Pos.size_nat (encode EX x)
  | FxCutMapGet _ code _ _ _
  | FxCutIndexGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FxCutMapSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | FxCutElements set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxCutQuery events => audit_work events + fx_declared_primitive_budget EC events
  | FxCutEqual _ _ cx cy _ _ =>
      2 + Pos.size_nat cx + Pos.size_nat cy + 2 * Nat.min (Pos.size_nat cx) (Pos.size_nat cy)
  | _ => 1
  end.

Definition fx_cut_work {X C A} (EC : encoding C) (events : list (fx_cut_event X C A)) : nat :=
  fold_right (fun e n => fx_cut_event_work EC e + n) 0 events.

Definition fx_cut_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_cut_event X C A)) : nat :=
  fold_right (fun e n => fx_cut_event_budget EX EC e + n) 0 events.

(** Cut expansion returns the original result and its recorded work fits the trace-based budget. *)
Definition fx_cut_expand_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) cert,
    let '(result, events) := fx_cut_expand_counted EX L S SS ix cert in
    result = expand EX L S SS ix cert /\
    fx_cut_work EC events <= fx_cut_budget EX EC events.

(** Input-only recurrences are mathematical bounds, not part of the execution being charged. *)

Definition fx_cut_key_budget {X} (EX : encoding X) (x : X) : nat :=
  2 + 6 * Pos.size_nat (encode EX x).

Definition fx_cut_write_budget {X} (EX : encoding X) (x : X) : nat :=
  2 + 17 * Pos.size_nat (encode EX x).

Definition fx_cut_equal_budget {X} (EX : encoding X) (x y : X) : nat :=
  let cx := encode EX x in let cy := encode EX y in
  2 + Pos.size_nat cx + Pos.size_nat cy + 2 * Nat.min (Pos.size_nat cx) (Pos.size_nat cy).

Fixpoint fx_cut_seed_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 1 + (3 + 7 * Pos.size_nat (encode EX x)) +
      fx_cut_seed_budget EX rest + fx_cut_write_budget EX x
  end.

Fixpoint fx_cut_prepare_budget {X} (EX : encoding X) (xs : list X) (seen : FinSet.t X) : nat :=
  match xs with
  | [] => 1
  | x :: rest =>
      2 + (12 + 5 * Pos.size_nat (encode EX x)) +
      if FinSet.mem EX x seen then 0
      else 12 + 17 * Pos.size_nat (encode EX x) +
        fx_cut_prepare_budget EX rest (FinSet.add EX x seen)
  end.

Fixpoint fx_cut_coverage_outputs_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 2 + (12 + 5 * Pos.size_nat (encode EX x)) + fx_cut_coverage_outputs_budget EX rest
  end.

Fixpoint fx_cut_coverage_constraints_budget {X C A} (EX : encoding X)
    (S : System.t X C A) (SS : System.static S) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 4 + fx_cut_coverage_outputs_budget EX (System.target S c :: side_targets SS c) +
      fx_cut_coverage_constraints_budget EX S SS rest
  end.

Fixpoint fx_cut_ready_budget {X} (EX : encoding X) (reads : list X) : nat :=
  match reads with
  | [] => 1
  | x :: rest => 6 + 2 * fx_cut_key_budget EX x + fx_cut_ready_budget EX rest
  end.

Fixpoint fx_cut_join_budget {X A} (EX : encoding X) (x : X) (updates : list (X * A)) : nat :=
  match updates with
  | [] => 1
  | (y, _) :: rest => 3 + fx_cut_equal_budget EX x y + fx_cut_join_budget EX x rest
  end.

Fixpoint fx_cut_gather_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (x : X) (cs : list C)
    (cur : assignment X A) (acc : A) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, reads, sides) := Query.run rhs (lookup EX L cur) in
      3 + fx_fullcheck_query_input_budget EX L cur rhs + fx_cut_ready_budget EX reads +
      if forallb (cut_ready EX ix cur) reads then
        let updates := (System.target S c, value) :: sides in
        1 + fx_cut_join_budget EX x updates +
          fx_cut_gather_budget EX L S ix x rest cur (cut_join EX L x updates acc)
      else 0
  end.

Fixpoint fx_cut_compute_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (xs : list X) (cur : assignment X A) : nat :=
  match xs with
  | [] => 1
  | x :: rest =>
      3 + fx_cut_key_budget EX x +
      if Map.mem EX x cur then 0
      else let cs := contributors_of EX ix x in
        2 + fx_cut_key_budget EX x + fx_cut_gather_budget EX L S ix x cs cur (bot L) +
        match cut_gather EX L S ix x cs cur (bot L) with
        | None => 0
        | Some value => fx_cut_write_budget EX x +
            fx_cut_compute_budget EX L S ix rest (Map.set EX x value cur)
        end
  end.

Definition fx_cut_compare_budget {X} (EX : encoding X) (x y : X) : nat :=
  1 + fx_cut_equal_budget EX x y + (3 + 7 * Pos.size_nat (encode EX x)) + 1.

Fixpoint fx_cut_check_sides_budget {X A} (EX : encoding X) (x : X) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 1
  | (y, _) :: rest => 2 + fx_cut_compare_budget EX x y + fx_cut_check_sides_budget EX x rest
  end.

Fixpoint fx_cut_check_constraints_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (x : X) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(_, _, sides) := Query.run rhs (lookup EX L m) in
      5 + fx_fullcheck_query_input_budget EX L m rhs +
        fx_cut_compare_budget EX x (System.target S c) + fx_cut_check_sides_budget EX x sides +
        fx_cut_check_constraints_budget EX L S m x rest
  end.

Fixpoint fx_cut_check_all_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (m : assignment X A) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 3 + fx_cut_key_budget EX x +
      fx_cut_check_constraints_budget EX L S m x (contributors_of EX ix x) +
      fx_cut_check_all_budget EX L S ix m rest
  end.

Definition fx_cut_elements_budget {X} (set : FinSet.t X) : nat :=
  7 + 19 * audit_trie_nodes set + audit_trie_output_bits set.

Definition fx_cut_expand_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cert : cut_certificate X A) : nat :=
  fx_cut_prepare_budget EX (plan cert) (cuts cert) + 1 +
  match cut_prepare EX (plan cert) (cuts cert) with
  | None => 0
  | Some cover =>
      fx_cut_coverage_constraints_budget EX S SS (System.constraints S) + 1 +
      if cut_coverage EX S SS cover then
        let xs := FinSet.elements (cuts cert) in
        let seed := cut_seed EX xs (lookup EX L (stored cert)) in
        fx_cut_elements_budget (cuts cert) + fx_cut_seed_budget EX xs +
        fx_cut_compute_budget EX L S ix (plan cert) seed + 1 +
        match cut_compute EX L S ix (plan cert) seed with
        | None => 0
        | Some m => fx_cut_elements_budget (cuts cert) +
            fx_cut_check_all_budget EX L S ix m xs + 1
        end
      else 0
  end.

(** Cut expansion returns the original result and its work fits a budget computed from its
    inputs. *)
Definition fx_cut_expand_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) cert,
    let '(result, events) := fx_cut_expand_counted EX L S SS ix cert in
    result = expand EX L S SS ix cert /\
    fx_cut_work EC events <= fx_cut_expand_input_budget EX L S SS ix cert.
