(** * FixpointAuditLocalCallbacks model

    Same-run local solver callback receipts, including closure and partial checking.
    For example, a local closure event retains the corresponding source receipt.
    Builds on: FixpointAuditLocal and the closure and partial callback models. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointLocal
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditCheckCallbacks FixpointAuditPartialCallbacks
  FixpointAuditLocalPartial FixpointAuditLocalClosure FixpointAuditLocal.
Import List.ListNotations.

(** Set encodings, contributor lookups and dependency events relate their bodies to their
    sources; other closure events require no bodies. *)
Definition fx_local_closure_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (event : fx_local_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxLocalUnknownMem _ _ _ events
  | FxLocalUnknownAdd _ _ _ events =>
      Forall2 (fx_local_x_entry_source source) (fx_local_set_entries events) bodies
  | FxLocalConstraintMem _ _ _ events
  | FxLocalConstraintAdd _ _ _ events =>
      Forall2 (fx_local_c_entry_source source) (fx_local_set_entries events) bodies
  | FxLocalContributors x code _ _ _ => exists body, bodies = [body] /\ fx_source_encode_x source x
    code body
  | FxLocalDeps c out => exists body, bodies = [body] /\ fxi_deps_source index_source c out body
  | _ => bodies = []
  end.

(** Closure, engine, partial-check and region-set events relate their bodies to their sources;
    other local-solve events require no bodies. *)
Definition fx_local_full_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (event : fx_local_full_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxLocalClosureTrace events => exists groups,
      Forall2 (fx_local_closure_event_source source index_source) events groups /\ bodies = concat
        groups
  | FxLocalEngineTrace events => exists groups, fx_declared_trace_source source events groups /\
    bodies = concat groups
  | FxLocalPartialTrace events => exists groups,
      Forall2 (fx_local_partial_event_source source) events groups /\ bodies = concat groups
  | FxLocalRegionBuild _ _ events
  | FxLocalRootMem _ _ _ events =>
      Forall2 (fx_local_x_entry_source source) (fx_local_set_entries events) bodies
  | _ => bodies = []
  end.

(** Local solve events and their source-body groups correspond in order. *)
Definition fx_local_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (events : list (fx_local_full_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_local_full_event_source source index_source) events bodies.

(** Every static dependency callback has a source witness and its accepted bodies fit the
    supplied bound. *)
Definition fx_local_deps_laws {X C A B} (S : System.t X C A) (SS : System.static S)
    (source : fx_index_external_source X C B) (ib : fx_index_external_budget X C B)
    (weight : B -> nat) : Prop :=
  (forall c, exists body, fxi_deps_source source c (deps SS c) body) /\
  (forall c out body, fxi_deps_source source c out body -> fx_one_body_work weight body <=
    fxi_deps_bound ib c).

Definition fx_local_closure_event_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (event : fx_local_event X C) : nat :=
  match event with
  | FxLocalUnknownMem _ _ _ e
  | FxLocalUnknownAdd _ _ _ e => fx_local_x_entries_budget wb
    (fx_local_set_entries e)
  | FxLocalConstraintMem _ _ _ e
  | FxLocalConstraintAdd _ _ _ e => fx_local_c_entries_budget wb
    (fx_local_set_entries e)
  | FxLocalContributors x _ _ _ _ => fx_budget_encode_x wb x
  | FxLocalDeps c _ => fxi_deps_bound ib c
  | _ => 0
  end.

Definition fx_local_full_event_external_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (event : fx_local_full_event X C A) : nat :=
  match event with
  | FxLocalClosureTrace events => fold_right (fun e n => fx_local_closure_event_budget wb ib e + n)
    0 events
  | FxLocalEngineTrace events => fx_declared_external_trace_budget wb events
  | FxLocalPartialTrace events => fold_right (fun e n => fx_local_partial_event_budget wb e + n) 0
    events
  | FxLocalRegionBuild _ _ e
  | FxLocalRootMem _ _ _ e => fx_local_x_entries_budget wb
    (fx_local_set_entries e)
  | _ => 0
  end.

Definition fx_local_external_trace_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (events : list (fx_local_full_event X C A)) : nat :=
  fold_right (fun e n => fx_local_full_event_external_budget wb ib e + n) 0 events.

(** With index laws and declared and dependency source laws and bounds, checked local solving has
    its original result, source receipts and a work bound. *)
Definition fx_local_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix roots fuel
    (source : fx_declared_callback_source X C A B) (wb : fx_declared_callback_budget X C A B)
    (index_source : fx_index_external_source X C B) (ib : fx_index_external_budget X C B),
    sys_index_laws EX S SS ix ->
    fx_declared_source_laws EX EC L sch S source -> fx_declared_callback_bounded source wb ->
    fx_local_deps_laws S SS index_source ib (fx_body_weight wb) ->
    let '(out, events) := local_checked_counted EX EC L sch mode S SS ix roots fuel in
    exists bodies, fx_local_trace_source source index_source events bodies /\
      out = local_checked EX EC L sch mode S SS ix roots fuel /\
      fx_local_full_work EC events + fx_declared_body_work (fx_body_weight wb) bodies <=
        fx_local_checked_input_budget EX EC L sch mode S SS ix roots fuel +
          fx_local_external_trace_budget wb ib events.
