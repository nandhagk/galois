(** * Observation preparation

    Preparation checks side targets and roots before constructing an SCC order and lifetimes.
    For example, both checks run even when the side-target check returns false.
    Builds on: FixpointAuditObserveOrder and FixpointAuditObserveExpiry. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditObserveOrder FixpointAuditObserveExpiry.
Import List.ListNotations.

Inductive fx_observe_prepare_event (X C B : Type) : Type :=
  | FxPrepareDependency (events : list (fx_dep_event X C B))
  | FxPrepareIndex (events : list (fx_index_nested_event X C B))
  | FxPrepareSet (events : list (audit_set_event X B))
  | FxPrepareOrder (events : list (fx_observe_order_event X C B))
  | FxPrepareExpiry (events : list (fx_observe_expiry_event X C))
  | FxPrepareCase.

Arguments FxPrepareDependency {X C B} _.

Arguments FxPrepareIndex {X C B} _.

Arguments FxPrepareSet {X C B} _.

Arguments FxPrepareOrder {X C B} _.

Arguments FxPrepareExpiry {X C B} _.

Arguments FxPrepareCase {X C B}.

(** Side-target checking traverses every listed constraint. *)

Fixpoint fx_observe_side_free {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    bool * list (fx_observe_prepare_event X C B) :=
  match cs with
  | [] => (true, [FxPrepareCase])
  | c :: rest =>
      let '(sides, body) := fxi_sides cb c in
      let '(later, events) := fx_observe_side_free cb rest in
      ((
        match sides with
        | [] => true
        | _ => false
        end) && later,
        FxPrepareCase :: FxPrepareIndex [FxiSides c sides body] :: events)
  end.

(** Root checking tests every root, preserving duplicates and all boolean tails. *)

Fixpoint fx_observe_roots_mem {X C B} (cb : fx_index_external_model X C B)
    (universe : FinSet.t X) (roots : list X) : bool * list (fx_observe_prepare_event X C B) :=
  match roots with
  | [] => (true, [FxPrepareCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x universe in
      let '(later, events) := fx_observe_roots_mem cb universe rest in
      (present && later, FxPrepareCase :: FxPrepareSet mem :: events)
  end.

(** Root preparation captures unknowns and the rebuilt universe before the root scan. *)

Definition fx_observe_roots_check {X C A B} (S : System.t X C A)
    (cb : fx_index_external_model X C B) (roots : list X) :
    bool * list (fx_observe_prepare_event X C B) :=
  let '(input, calls) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, distinct) := fxi_distinct_counted cb input in
  let '(universe, set) := audit_finset_of_list (fxi_encode cb) unknown in
  let '(result, members) := fx_observe_roots_mem cb universe roots in
  (result, [FxPrepareDependency calls; FxPrepareIndex distinct; FxPrepareSet set] ++ members).

(** Counted preparation records the selected branch and its phase events. *)

Definition fx_observe_prepare {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (cb : fx_index_external_model X C B)
    (roots : list X) : option (observation_plan X) * list (fx_observe_prepare_event X C B) :=
  let '(side, side_events) := fx_observe_side_free cb (System.constraints S) in
  let '(root, root_events) := fx_observe_roots_check S cb roots in
  if side && root then
    let '(order, order_events) := fx_observe_order EX S SS cb in
    let '(input, input_events) := fx_dep_unknowns_input cb (System.constraints S) in
    let '(unknown, distinct_events) := fxi_distinct_counted cb input in
    let '(expiration, expiry_events) := fx_observe_expiry_fold EX S ix order unknown in
    (Some (ObservationPlan order expiration),
      side_events ++ root_events ++ [FxPrepareOrder order_events;
        FxPrepareDependency input_events; FxPrepareIndex distinct_events;
        FxPrepareExpiry expiry_events])
  else (None, side_events ++ root_events ++ [FxPrepareCase]).

(** The side and root costs use actual input keys and callback-specific budgets. *)

Fixpoint fx_observe_roots_mem_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (roots : list X) : nat :=
  match roots with
  | [] => 1
  | x :: rest => 8 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_observe_roots_mem_budget EX ib rest
  end.

(** The full frame budget follows the real preparation acceptance branch. *)

Definition fx_observe_prepare_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B)
    (roots : list X) : nat :=
  let cs := System.constraints S in
  let input := fx_dep_unknowns_native S SS in
  let unknown := unknowns EX S SS in
  32 * (1 + length cs + length input) + fx_dep_callback_budget ib cs +
    fx_dep_build_budget EX S SS ib + fxi_distinct_input_budget EX ib input +
    fxi_set_input_budget EX ib unknown + fx_observe_roots_mem_budget EX ib roots +
    if observation_side_free S SS && observation_roots_check EX S SS roots then
      let order := observation_order EX S SS in
      fx_observe_order_budget EX S SS ib + fx_dep_build_budget EX S SS ib +
        fx_observe_expiry_fold_budget EX S ix order unknown
    else 1.

(** The preparation frame work includes each captured child phase and collection traversal. *)

Definition fx_observe_prepare_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_prepare_event X C B) : nat :=
  match event with
  | FxPrepareDependency events => fx_dep_events_work ib events
  | FxPrepareIndex events => fx_index_adapter_work ib events
  | FxPrepareSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxPrepareOrder events => fx_observe_order_work ib events
  | FxPrepareExpiry events => fx_observe_expiry_work events
  | FxPrepareCase => 1
  end.

(** The source work folds exactly the events returned by one preparation. *)

Definition fx_observe_prepare_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_prepare_event X C B)) : nat :=
  fold_right (fun e n => fx_observe_prepare_event_work ib e + n) 0 events.

(** Dependency, index, set and order events use embedded index sources and empty body groups,
    expiry events use their source groups, and case events require none. *)

Definition fx_observe_prepare_event_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_prepare_event X C B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxPrepareDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FxPrepareIndex events => fx_index_external_trace_adequacy index_source events /\ bodies = []
  | FxPrepareSet events => fxi_set_external_adequacy index_source events /\ bodies = []
  | FxPrepareOrder events => Forall (fx_observe_order_event_source index_source) events /\
    bodies = []
  | FxPrepareExpiry events => exists groups,
      Forall2 (fx_observe_expiry_event_source source) events groups /\ bodies = concat groups
  | FxPrepareCase => bodies = []
  end.

(** External expiry bodies are charged only at actual selected callback invocations. *)

Definition fx_observe_prepare_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_prepare_event X C B) : nat :=
  match event with
  | FxPrepareExpiry events =>
      fold_right (fun e n => fx_observe_expiry_external_budget budget e + n) 0 events
  | _ => 0
  end.

(** One captured preparation supplies its source receipts, result and independent frame bound. *)

(** With index erasure and bounds, dependency source laws and expiry source laws, observation
    preparation has its original result, source receipts and a work bound. *)
Definition fx_observe_prepare_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_prepare EX S SS ix cb roots in
    exists bodies, Forall2 (fx_observe_prepare_event_source index_source source) events bodies /\
      out = observation_prepare EX S SS ix roots /\
      fx_observe_prepare_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_prepare_budget EX S SS ix ib roots +
        fold_right (fun e n => fx_observe_prepare_external_budget budget e + n) 0 events.
