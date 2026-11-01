(** * Recorded-reader worklist input budget

    The recurrence follows the actual recorded map, intermediate states and duplicate reads;
    its evaluation is a mathematical observation outside the claimed source operation.
    For example, repeated reads contribute to the recorded-reader input budget.
    Builds on: FixpointAuditRecorded and the declared queue/query budgets. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklistBudget FixpointAuditRecorded.
Import List.ListNotations.

Fixpoint fx_record_reads_input_budget {X C} (EX : encoding X) (EC : encoding C) (c : C)
    (reads : list X) : nat :=
  match reads with
  | [] => 1
  | x :: rest => 21 + 23 * Pos.size_nat (encode EX x) + 16 * Pos.size_nat (encode EC c) +
      fx_record_reads_input_budget EX EC c rest
  end.

Definition fx_recorded_update_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (recorded : Map.t X (FinSet.t C)) (update : X * A) (state : assignment X A * PQueue.t C) : nat
      :=
  let '(x, value) := update in let '(m, q) := state in
  let old := lookup EX L m x in
  fx_fullcheck_lookup_input_budget EX x + 2 +
  if leb L value old then 0 else
    let set := recorded_at EX recorded x in
    4 + (2 + 17 * Pos.size_nat (encode EX x)) +
      (8 + 6 * Pos.size_nat (encode EX x) + 19 * audit_trie_nodes set + audit_trie_output_bits set)
        +
      fx_declared_enqueue_input_budget EC sch S (FinSet.elements set) q.

Fixpoint fx_recorded_updates_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (recorded : Map.t X (FinSet.t C)) (updates : list (X * A))
    (state : assignment X A * PQueue.t C) : nat :=
  match updates with
  | [] => 1
  | update :: rest =>
      1 + fx_recorded_update_input_budget EX EC L sch mode S recorded update state +
      fx_recorded_updates_input_budget EX EC L sch mode S recorded rest
        (engine_update EX EC L sch mode S Recorded recorded update state)
  end.

Definition fx_recorded_step_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (state : Engine.t X C A) : nat :=
  fx_declared_pop_input_budget EC (Engine.queue state) + 1 +
  match PQueue.pop EC (Engine.queue state) with
  | None => 0
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(value, reads, sides) := Query.run rhs (lookup EX L (Engine.current state)) in
      let recorded := record_reads EX EC c reads (Engine.recorded state) in
      3 + fx_fullcheck_query_input_budget EX L (Engine.current state) rhs +
        fx_record_reads_input_budget EX EC c reads +
        fx_recorded_updates_input_budget EX EC L sch mode S recorded
          ((System.target S c, value) :: sides) (Engine.current state, queue)
  end.

Fixpoint fx_recorded_loop_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (fuel : positive) (state : Engine.t X C A) : nat :=
  let step := step_outcome EX EC L sch mode S Recorded in
  match fuel with
  | xH => 1 + fx_recorded_step_input_budget EX EC L sch mode S state
  | xO smaller =>
      2 + fx_recorded_loop_input_budget EX EC L sch mode S smaller state +
      match loop step smaller state with
      | Done _ => 0
      | Pending next => fx_recorded_loop_input_budget EX EC L sch mode S smaller next
      end
  | xI smaller =>
      let first := loop step smaller state in
      let second :=
        match first with
        | Done values => Done values
        | Pending next => loop step smaller
          next
        end in
      3 + fx_recorded_loop_input_budget EX EC L sch mode S smaller state +
      (
        match first with
        | Done _ => 0
        | Pending next =>
          fx_recorded_loop_input_budget EX EC L sch mode S smaller next
        end) +
      match second with
      | Done _ => 0
      | Pending next => fx_recorded_step_input_budget EX EC L sch mode
        S next
      end
  end.

Definition fx_recorded_run_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A) (fuel : positive) :
      nat :=
  let queue := enqueue EC sch S (System.constraints S) PQueue.empty in
  fx_declared_enqueue_input_budget EC sch S (System.constraints S) PQueue.empty +
    2 + fx_recorded_loop_input_budget EX EC L sch mode S fuel (Engine.State Map.empty queue
      Map.empty).

(** The recorded worklist returns the original result and its work fits an input-derived budget. *)
Definition fx_recorded_run_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) fuel,
    let '(out, events) := run_worklist_recorded_model EX EC L sch mode S fuel in
    out = run_worklist EX EC L sch mode S Recorded fuel /\
    fx_recorded_work EC events <= fx_recorded_run_input_budget EX EC L sch mode S fuel.
