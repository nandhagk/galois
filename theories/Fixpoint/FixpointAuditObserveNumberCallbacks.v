(** * Numbered observation callback closures

    Target and RHS closures first look up an occurrence label, then invoke the original system.
    For example, an absent index uses the original fallback constraint.
    Builds on: FixpointAuditObserveNumber and FixpointAuditWorklistCallbacks. *)

From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsMap CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointObserve
  FixpointAuditWorklistCallbacks FixpointAuditObserveNumber.
Import List.ListNotations.

(** One closure invocation retains its concrete label lookup and original target call. *)

Definition fx_observe_numbered_target {X C A} (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (i : nat) : X * C * list (audit_map_event nat C
    audit_nat_encoding_event) :=
  let '(label, events) := fx_observe_label fallback table i in
  (System.target S label, label, events).

(** One closure invocation retains its concrete label lookup and original RHS call. *)

Definition fx_observe_numbered_rhs {X C A} (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (i : nat) :
    Query.t X A * C * list (audit_map_event nat C audit_nat_encoding_event) :=
  let '(label, events) := fx_observe_label fallback table i in
  (System.rhs S label, label, events).

(** The supplied target and RHS relations admit bodies for the original system results and bound
    every body they accept. *)

Definition fx_observe_numbered_source_laws {X C A B} (S : System.t X C A)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c).

(** The numbered target statement relates a body witness to the supplied target source. *)

(** With numbered target and right-hand-side source laws and bounds, target lookup returns its
    original label and target, admits a source-related body witness and meets a combined work
    bound. *)
Definition fx_observe_numbered_target_source_statement : Prop :=
  forall (X C A B : Type) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (i : nat),
    fx_observe_numbered_source_laws S source budget ->
    let '(out, label, events) := fx_observe_numbered_target S fallback table i in
    exists body, fx_source_target source label out body /\
      label = observation_label fallback table i /\
      out = System.target S (observation_label fallback table i) /\
      audit_map_source_work audit_nat_events_work events +
        fx_one_body_work (fx_body_weight budget) body <=
        fx_observe_label_budget i + fx_budget_target budget (observation_label fallback table i).

(** The numbered RHS statement relates a body witness to the supplied RHS source. *)

(** With numbered target and right-hand-side source laws and bounds, right-hand-side lookup
    returns its original label and result, admits a source-related body witness and meets a combined
    work bound. *)
Definition fx_observe_numbered_rhs_source_statement : Prop :=
  forall (X C A B : Type) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (i : nat),
    fx_observe_numbered_source_laws S source budget ->
    let '(out, label, events) := fx_observe_numbered_rhs S fallback table i in
    exists body, fx_source_rhs source label out body /\
      label = observation_label fallback table i /\
      out = System.rhs S (observation_label fallback table i) /\
      audit_map_source_work audit_nat_events_work events +
        fx_one_body_work (fx_body_weight budget) body <=
        fx_observe_label_budget i + fx_budget_rhs budget (observation_label fallback table i).
