(** * Fallback callback receipts

    Fallback source relations connect recorded or nested solver events to body witnesses.
    For example, exhaustion selects top without performing a later lookup.
    Builds on: FixpointAuditFallback and the recorded and nested source adapters. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks FixpointAuditRecordedBudget FixpointAuditRecordedCallbacks
  FixpointAuditNested FixpointAuditScheduleWrapper FixpointAuditNestedCallbacks
  FixpointAuditFallback.
Import List.ListNotations.

(** Recorded and nested events require their respective trace-source relations and concatenated
    body groups, while case events require an empty body list. *)
Definition fx_fallback_event_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_fallback_event X C A B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxFallbackRecorded events => exists groups,
      fx_recorded_trace_source source events groups /\ bodies = concat groups
  | FxFallbackNested events => exists groups,
      fx_nested_trace_source index_source source events groups /\ bodies = concat groups
  | FxFallbackCase _ => bodies = []
  end.

(** Fallback events and their grouped source bodies correspond in order. *)
Definition fx_fallback_trace_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (events : list (fx_fallback_event X C A B))
    (bodies : list (list (list D))) : Prop :=
  Forall2 (fx_fallback_event_source index_source source) events bodies.

Definition fx_fallback_external_trace_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (events : list (fx_fallback_event X C A B)) :
  nat :=
  fold_right (fun event total => total +
    match event with
    | FxFallbackRecorded nested => fx_recorded_external_trace_budget budget nested
    | FxFallbackNested nested => fx_nested_external_trace_budget budget nested
    | FxFallbackCase _ => 0
    end) 0 events.

(** The recorded source statement relates event-body witnesses to supplied callback sources. *)

(** With declared source laws and callback bounds, recorded fallback has its original result,
    source receipts and a work bound. *)
Definition fx_recorded_fallback_external_source_statement : Prop :=
  forall X C A B D (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) (ib : fx_index_external_budget X C B) fuel
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D),
    fx_declared_source_laws EX EC L sch S source -> fx_declared_callback_bounded source budget ->
    let '(out, events) := @fx_recorded_fallback_counted X C A B EX EC L sch mode S fuel in
    exists bodies, fx_fallback_trace_source index_source source events bodies /\
      out = run_worklist EX EC L sch mode S Recorded fuel /\
      fx_fallback_work EC ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_recorded_run_input_budget EX EC L sch mode S fuel + 1 +
          fx_fallback_external_trace_budget budget events.

(** The nested source statement relates graph and solver events to supplied callback sources. *)

(** With index erasure and bounds and dependency and machine source laws, nested fallback has its
    original result, source receipts and a work bound. *)
Definition fx_nested_fallback_external_source_statement : Prop :=
  forall X C A B D (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_nested_fallback_counted EX L mode S SS cb fuel in
    exists bodies, fx_fallback_trace_source index_source source events bodies /\
      out = nested_run EX EC L mode S SS fuel /\
      fx_fallback_work EC ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_nested_run_input_budget EX L mode S SS ib fuel + 1 +
          fx_fallback_external_trace_budget budget events.

(** A later closure application retains its own encoder body, separately from construction. *)

(** With encoder source witnesses and bounds, applying a fallback returns the original value with
    source receipts and a work bound. *)
Definition fx_fallback_apply_external_source_statement : Prop :=
  forall X C A D (EX : encoding X) (EC : encoding C) (L : lattice A) (T : top L)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    result x,
    (forall key, exists body, fx_source_encode_x source key (encode EX key) body) ->
    (forall key out body, fx_source_encode_x source key out body ->
      fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget key) ->
    let '(out, events) := @fx_fallback_apply_counted X C A EX L T result x in
    exists bodies, fx_declared_trace_source source events bodies /\
      out = fx_fallback_result EX L T result x /\
      fx_declared_model_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        1 + fx_fullcheck_lookup_input_budget EX x + fx_declared_external_trace_budget budget events.
