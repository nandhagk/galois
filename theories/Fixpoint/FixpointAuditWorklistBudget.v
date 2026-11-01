(** * Input/intermediate-state budgets for declared worklist execution

    These mathematical recurrences inspect source intermediate states and do not consume
    returned model event lists. Their evaluation is excluded from the source-work claim.
    For example, a query lookup budget depends on the input assignment.
    Builds on: FixpointWorklist, the shared queue bounds and counted declared execution. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditQueue.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
Import List.ListNotations.

Definition fx_fullcheck_lookup_input_budget {X} (EX : encoding X) (x : X) : nat :=
  3 + 7 * Pos.size_nat (encode EX x).

Fixpoint fx_fullcheck_query_input_budget {X A} (EX : encoding X) (L : lattice A)
    (m : assignment X A) (q : Query.t X A) : nat :=
  match q with
  | Query.Ret _ => 1
  | Query.Ask x k =>
      3 + fx_fullcheck_lookup_input_budget EX x +
        fx_fullcheck_query_input_budget EX L m (k (lookup EX L m x))
  | Query.Side _ _ next => 2 + fx_fullcheck_query_input_budget EX L m next
  end.

Definition fx_declared_push_input_budget {C} (EC : encoding C) (priority : positive)
    (c : C) (q : PQueue.t C) : nat :=
  let heap := PQueue.pending q in
  1 + audit_queue_full_input_budget EC 1 heap (PQueue.live q) [c] [priority] +
    2 * audit_queue_input_event_bound 1 heap.

Definition fx_declared_pop_input_budget {C} (EC : encoding C) (q : PQueue.t C) : nat :=
  let heap := PQueue.pending q in
  let fuel := PQueue.pending_count q in
  1 + audit_queue_full_input_budget EC fuel heap (PQueue.live q) [] [] +
    2 * audit_queue_input_event_bound fuel heap.

Fixpoint fx_declared_enqueue_input_budget {X C A} (EC : encoding C) (sch : scheduler X)
    (S : System.t X C A) (cs : list C) (q : PQueue.t C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let priority := priority sch (System.target S c) in
      3 + fx_declared_push_input_budget EC priority c q +
        fx_declared_enqueue_input_budget EC sch S rest (PQueue.push EC priority c q)
  end.

Definition fx_declared_update_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (ix : sys_index X C) (update : X * A) (state : assignment X A * PQueue.t C) : nat :=
  let '(x, value) := update in let '(m, q) := state in
  let old := lookup EX L m x in
  fx_fullcheck_lookup_input_budget EX x + 2 +
  if leb L value old then 0 else
    6 + (2 + 19 * Pos.size_nat (encode EX x)) + (2 + 7 * Pos.size_nat (encode EX x)) +
      fx_declared_enqueue_input_budget EC sch S (readers_of EX ix x) q.

Fixpoint fx_declared_updates_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (updates : list (X * A))
    (state : assignment X A * PQueue.t C) : nat :=
  match updates with
  | [] => 1
  | update :: rest =>
      1 + fx_declared_update_input_budget EX EC L sch mode S ix update state +
      fx_declared_updates_input_budget EX EC L sch mode S SS ix rest
        (engine_update EX EC L sch mode S (Declared SS ix) Map.empty update state)
  end.

Definition fx_declared_step_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (state : Engine.t X C A) : nat :=
  fx_declared_pop_input_budget EC (Engine.queue state) + 1 +
  match PQueue.pop EC (Engine.queue state) with
  | None => 0
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L (Engine.current state)) in
      3 + fx_fullcheck_query_input_budget EX L (Engine.current state) rhs +
      fx_declared_updates_input_budget EX EC L sch mode S SS ix
        ((System.target S c, value) :: sides) (Engine.current state, queue)
  end.

Fixpoint fx_declared_loop_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (fuel : positive) (state : Engine.t X C A) : nat :=
  let step := step_outcome EX EC L sch mode S (Declared SS ix) in
  match fuel with
  | xH => 1 + fx_declared_step_input_budget EX EC L sch mode S SS ix state
  | xO smaller =>
      2 + fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller state +
      match loop step smaller state with
      | Done _ => 0
      | Pending next => fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller next
      end
  | xI smaller =>
      let first := loop step smaller state in
      let second :=
        match first with
        | Done values => Done values
        | Pending next => loop step smaller
          next
        end in
      3 + fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller state +
      (
        match first with
        | Done _ => 0
        | Pending next =>
          fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller next
        end) +
      match second with
      | Done _ => 0
      | Pending next => fx_declared_step_input_budget EX EC L sch mode
        S SS ix next
      end
  end.

Definition fx_declared_run_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (fuel : positive) : nat :=
  let queue := enqueue EC sch S (System.constraints S) PQueue.empty in
  fx_declared_enqueue_input_budget EC sch S (System.constraints S) PQueue.empty +
    2 + fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel (Engine.State Map.empty queue
      Map.empty).

(** The declared worklist returns the original result and its counted work fits an input-derived
    budget. *)
Definition fx_declared_run_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) (SS : System.static S) ix fuel,
    let '(out, events) := run_worklist_declared_model EX EC L sch mode S ix fuel in
    out = run_worklist EX EC L sch mode S (Declared SS ix) fuel /\
    fx_declared_model_work EC events <= fx_declared_run_input_budget EX EC L sch mode S SS ix fuel.
