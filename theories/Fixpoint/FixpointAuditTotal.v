(** * FixpointAuditTotal model

    Total solver with the concrete indexed producer and source-witness worklist phases.
    This is a declaration-only candidate; no native-runtime or observer-evaluation cost is claimed.
    For example, a target call's source relation requires a witness accepted by the target source.
    Builds on: FixpointWorklist and the counted index and callback models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointCycles FixpointWorklist
  FixpointTotal.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Fixpoint Require Import FixpointAuditIndex FixpointAuditWorklist
  FixpointAuditWorklistBudget FixpointAuditWorklistCallbacks.
Import List.ListNotations.

Definition fx_total_weight_bound (n r : nat) : nat :=
  1 + n * Nat.pow (2 + r * n) (S n).

Definition fx_total_queue_bound (n r : nat) : nat :=
  r * (1 + n * fx_total_weight_bound n r).

Definition fx_total_join_step_bound {X C A} {S : System.t X C A}
    (L : lattice A) (H : height L) (SS : System.static S) : nat :=
  let n := length (total_unknowns SS) in
  let r := length (System.constraints S) in
  (1 + n * bound H) * (1 + r).

Definition fx_total_widen_step_bound {X C A} {S : System.t X C A}
    (L : lattice A) (W : widening_rank L) (SS : System.static S) : nat :=
  let n := length (total_unknowns SS) in
  let r := length (System.constraints S) in
  (1 + n * wrank W (bot L)) * (1 + fx_total_queue_bound n r).

(** A total callback run composes the actual index build, initial enqueue and total engine run. *)
Inductive fx_total_callbacks_run {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (cb : fx_index_external_model X C B) : assignment X A -> list (fx_index_nested_event X C B) ->
    audit_trace (fx_declared_call X C A) -> audit_trace (fx_declared_call X C A) -> Prop :=
  | FxTotalCallbacksRun : forall ix index_events queue init_events values engine_events,
      fx_index_nested_counted S cb = (ix, index_events) ->
      fx_model_enqueue EC sch S (System.constraints S) PQueue.empty = (queue, init_events) ->
      fx_declared_total_engine_run EX EC L sch mode S ix
        (Engine.State Map.empty queue Map.empty) values engine_events ->
      fx_total_callbacks_run EX EC L sch mode S cb values index_events init_events engine_events.

(** With lattice laws, termination and index erasure, the total solver has a callback run with
    concrete phase events. *)
Definition fx_total_callbacks_realization_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S)
    (HT : terminates L SS sch mode) (cb : fx_index_external_model X C B),
    fx_index_external_erases EX S SS cb ->
    exists index_events init_events engine_events,
      fx_total_callbacks_run EX EC L sch mode S cb
        (proj1_sig (total_solver_map EX EC L HL sch mode S SS HT)) index_events init_events
          engine_events.

(** With lattice laws, termination and index callback erasure, a total callback run returns the
    original solver result. *)
Definition fx_total_callbacks_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S)
    (HT : terminates L SS sch mode) (cb : fx_index_external_model X C B)
    result index_events init_events engine_events,
    fx_index_external_erases EX S SS cb ->
    fx_total_callbacks_run EX EC L sch mode S cb result index_events init_events engine_events ->
    result = proj1_sig (total_solver_map EX EC L HL sch mode S SS HT).

(** Index trace adequacy is a premise for relating initialization and engine body witnesses. *)

(** Given index callback erasure, adequate index receipts, declared source laws and a total run,
    the initialization and engine traces have source bodies. *)
Definition fx_total_callbacks_source_statement : Prop :=
  forall X C A BI BW (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C BI) (index_source : fx_index_external_source X C BI)
    (source : fx_declared_callback_source X C A BW)
    result index_events init_events engine_events,
    fx_index_external_erases EX S SS cb ->
    fx_index_external_trace_adequacy index_source index_events ->
    fx_declared_source_laws EX EC L sch S source ->
    fx_total_callbacks_run EX EC L sch mode S cb result index_events init_events engine_events ->
    exists init_bodies engine_bodies,
      fx_declared_trace_source source init_events init_bodies /\
      fx_declared_trace_source source engine_events engine_bodies.

(** With lattice laws, finite height, index erasure and bounds, declared callback bounds and
    initialization and engine trace-source premises, a joining run has the original total-solver
    result and stated work bound. *)
Definition fx_total_callbacks_join_work_statement : Prop :=
  forall X C A BI BW (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (H : height L) (sch : scheduler X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C BI) (index_budget : fx_index_external_budget X C BI)
    (source : fx_declared_callback_source X C A BW) (budget : fx_declared_callback_budget X C A BW)
    result index_events init_events engine_events init_bodies engine_bodies,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb index_budget ->
    fx_declared_callback_bounded source budget ->
    fx_total_callbacks_run EX EC L sch Joining S cb result index_events init_events engine_events ->
    fx_declared_trace_source source init_events init_bodies ->
    fx_declared_trace_source source engine_events engine_bodies ->
    let ix := fst (fx_index_nested_counted S cb) in
    let fuel := Pos.of_succ_nat (fx_total_join_step_bound L H SS) in
    result = proj1_sig (total_solver_map EX EC L HL sch Joining S SS (inhabits H)) /\
    fx_index_adapter_work index_budget index_events + fx_declared_model_work EC init_events +
      fx_declared_model_work EC engine_events + fx_declared_body_work (fx_body_weight budget)
        init_bodies +
      fx_declared_body_work (fx_body_weight budget) engine_bodies <=
      fx_index_nested_input_budget EX S SS index_budget +
      fx_declared_run_input_budget EX EC L sch Joining S SS ix fuel +
      fx_declared_external_trace_budget budget init_events + fx_declared_external_trace_budget
        budget engine_events.

(** With lattice laws, widening rank, a cycle cut, index erasure and bounds, declared callback
    bounds and initialization and engine trace-source premises, a widening run has the original
    total-solver result and stated work bound. *)
Definition fx_total_callbacks_widen_work_statement : Prop :=
  forall X C A BI BW (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (W : widening_rank L) (sch : scheduler X) (S : System.t X C A) (SS : System.static S)
    (Hcut : cuts_every_cycle SS (widening_point sch))
    (cb : fx_index_external_model X C BI) (index_budget : fx_index_external_budget X C BI)
    (source : fx_declared_callback_source X C A BW) (budget : fx_declared_callback_budget X C A BW)
    result index_events init_events engine_events init_bodies engine_bodies,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb index_budget ->
    fx_declared_callback_bounded source budget ->
    fx_total_callbacks_run EX EC L sch Widening S cb result index_events init_events engine_events
      ->
    fx_declared_trace_source source init_events init_bodies ->
    fx_declared_trace_source source engine_events engine_bodies ->
    let ix := fst (fx_index_nested_counted S cb) in
    let fuel := Pos.of_succ_nat (fx_total_widen_step_bound L W SS) in
    result = proj1_sig (total_solver_map EX EC L HL sch Widening S SS (conj (inhabits W) Hcut)) /\
    fx_index_adapter_work index_budget index_events + fx_declared_model_work EC init_events +
      fx_declared_model_work EC engine_events + fx_declared_body_work (fx_body_weight budget)
        init_bodies +
      fx_declared_body_work (fx_body_weight budget) engine_bodies <=
      fx_index_nested_input_budget EX S SS index_budget +
      fx_declared_run_input_budget EX EC L sch Widening S SS ix fuel +
      fx_declared_external_trace_budget budget init_events + fx_declared_external_trace_budget
        budget engine_events.
