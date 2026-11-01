(** * Same-step dense solver receipts

    The total-engine derivation attaches callback bodies to the step that actually invokes them.
    For example, a flow continuation and its transfer body appear in the same captured step.
    Builds on: FixpointAuditTotal and the declared callback-source relation. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap
  CollectionsAuditCost.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointAuditIndex
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditTotal.
Import List.ListNotations.

(** * Same-step dense solver receipts *)

(** Each constructor binds the actual step output and that same step's source bodies. *)
Inductive audit_dense_annotated_engine {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (system : System.t X C A)
    (ix : sys_index X C) (source : fx_declared_callback_source X C A B) :
    Engine.t X C A -> assignment X A -> audit_trace (fx_declared_call X C A) ->
      list (list (list B)) -> Prop :=
  | DenseAnnotatedStop : forall state result events bodies,
      fx_model_step EX EC L sch mode system ix state = (Done result, events) ->
      fx_declared_trace_source source events bodies ->
      audit_dense_annotated_engine EX EC L sch mode system ix source state result events bodies
  | DenseAnnotatedContinue : forall state next result events later bodies later_bodies,
      fx_model_step EX EC L sch mode system ix state = (Pending next, events) ->
      fx_declared_trace_source source events bodies ->
      audit_dense_annotated_engine EX EC L sch mode system ix source next result later
        later_bodies ->
      audit_dense_annotated_engine EX EC L sch mode system ix source state result
        (events ++ later) (bodies ++ later_bodies).

(** Index and initial queue receipts feed the same annotated engine and final assignment. *)
Inductive audit_dense_annotated_total {X C A BI BW} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (system : System.t X C A)
    (cb : fx_index_external_model X C BI) (index_source : fx_index_external_source X C BI)
    (source : fx_declared_callback_source X C A BW) : assignment X A ->
    list (fx_index_nested_event X C BI) -> audit_trace (fx_declared_call X C A) ->
    audit_trace (fx_declared_call X C A) -> list (list (list BW)) -> list (list (list BW)) ->
    Prop :=
  | DenseAnnotatedTotal : forall ix index_events queue init_events result engine_events
      init_bodies engine_bodies,
      fx_index_nested_counted system cb = (ix, index_events) ->
      fx_index_external_trace_adequacy index_source index_events ->
      fx_model_enqueue EC sch system (System.constraints system) PQueue.empty = (queue,
        init_events) ->
      fx_declared_trace_source source init_events init_bodies ->
      audit_dense_annotated_engine EX EC L sch mode system ix source
        (Engine.State Map.empty queue Map.empty) result engine_events engine_bodies ->
      audit_dense_annotated_total EX EC L sch mode system cb index_source source
        result index_events init_events engine_events init_bodies engine_bodies.

(** The annotated witness projects to the original total-engine execution and source traces. *)
Definition audit_dense_annotated_total_erasure_statement : Prop :=
  forall (X C A BI BW : Type) (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (mode : strategy) (system : System.t X C A)
    (cb : fx_index_external_model X C BI) (index_source : fx_index_external_source X C BI)
    (source : fx_declared_callback_source X C A BW) result index_events init_events engine_events
    init_bodies engine_bodies,
    audit_dense_annotated_total EX EC L sch mode system cb index_source source
      result index_events init_events engine_events init_bodies engine_bodies ->
    fx_total_callbacks_run EX EC L sch mode system cb result index_events init_events
      engine_events /\
    fx_declared_trace_source source init_events init_bodies /\
    fx_declared_trace_source source engine_events engine_bodies.
