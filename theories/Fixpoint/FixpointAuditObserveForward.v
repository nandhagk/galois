(** * Observation forward-boundary checking

    Every constraint target is checked against the current component.
    For example, only a target inside the component causes its dependencies to be inspected.
    Builds on: FixpointObserve and the counted finite-set operations. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointObserve FixpointAuditIndex.
Import List.ListNotations.

Inductive fx_observe_forward_event (X C B : Type) : Type :=
  | FxForwardIndex (events : list (fx_index_nested_event X C B))
  | FxForwardSet (events : list (audit_set_event X B))
  | FxForwardConcat (suffix : list (list X))
  | FxForwardBuild (size : nat)
  | FxForwardCase.

Arguments FxForwardIndex {X C B} _.

Arguments FxForwardSet {X C B} _.

Arguments FxForwardConcat {X C B} _.

Arguments FxForwardBuild {X C B} _.

Arguments FxForwardCase {X C B}.

(** A dependency scan evaluates every finite-set lookup, including after a failed test. *)

Fixpoint fx_forward_deps {X C B} (cb : fx_index_external_model X C B)
    (later : FinSet.t X) (deps : list X) : bool * list (fx_observe_forward_event X C B) :=
  match deps with
  | [] => (true, [FxForwardCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x later in
      let '(out, events) := fx_forward_deps cb later rest in
      (negb present && out, FxForwardCase :: FxForwardSet mem :: events)
  end.

(** Target membership selects dependency evaluation, but all constraint tails execute. *)

Fixpoint fx_forward_constraints {X C B} (cb : fx_index_external_model X C B)
    (members later : FinSet.t X) (cs : list C) : bool * list (fx_observe_forward_event X C B) :=
  match cs with
  | [] => (true, [FxForwardCase])
  | c :: rest =>
      let '(target, target_body) := fxi_target cb c in
      let '(present, target_mem) := audit_finset_mem (fxi_encode cb) target members in
      let '(current, here) :=
        if present then
          let '(deps, deps_body) := fxi_deps cb c in
          let '(out, events) := fx_forward_deps cb later deps in
          (out, FxForwardIndex [FxiDeps c deps deps_body] :: events)
        else (true, []) in
      let '(out, tail) := fx_forward_constraints cb members later rest in
      (current && out, FxForwardCase :: FxForwardIndex [FxiTarget c target target_body] ::
        FxForwardSet target_mem :: here ++ tail)
  end.

(** A boundary constructs both sets and the actual concatenation of later components. *)

Definition fx_forward_boundary {X C B} (cb : fx_index_external_model X C B)
    (cs : list C) (component : list X) (suffix : list (list X)) :
    bool * list (fx_observe_forward_event X C B) :=
  let '(members, member_events) := audit_finset_of_list (fxi_encode cb) component in
  let later_list := concat suffix in
  let '(later, later_events) := audit_finset_of_list (fxi_encode cb) later_list in
  let '(out, events) := fx_forward_constraints cb members later cs in
  (out, FxForwardSet member_events :: FxForwardConcat suffix :: FxForwardSet later_events ::
    events).

(** Each boundary receives exactly the unprocessed component suffix. *)

Fixpoint fx_observe_forward {X C B} (cb : fx_index_external_model X C B) (cs : list C)
    (order : list (list X)) : bool * list (fx_observe_forward_event X C B) :=
  match order with
  | [] => (true, [FxForwardCase])
  | component :: rest =>
      let '(here, events) := fx_forward_boundary cb cs component rest in
      let '(later, tail) := fx_observe_forward cb cs rest in
      (here && later, FxForwardCase :: events ++ tail)
  end.

(** Captured frame work includes the actual concatenation lengths and callback bodies. *)

Definition fx_observe_forward_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_forward_event X C B) : nat :=
  match event with
  | FxForwardIndex events => fx_index_adapter_work ib events
  | FxForwardSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxForwardConcat suffix => 2 + length suffix + length (concat suffix)
  | FxForwardBuild size => 2 + 2 * size
  | FxForwardCase => 1
  end.

(** The frame work folds the selected events from one traversal. *)

Definition fx_observe_forward_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_forward_event X C B)) : nat :=
  fold_right (fun e n => fx_observe_forward_event_work ib e + n) 0 events.

(** The dependency bound charges each actual declared read. *)

Fixpoint fx_forward_deps_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (deps : list X) : nat :=
  match deps with
  | [] => 1
  | x :: rest => 8 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_forward_deps_budget EX ib rest
  end.

(** The constraint budget follows target membership and includes only selected deps callbacks. *)

Fixpoint fx_forward_constraints_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B)
    (members : FinSet.t X) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let target := System.target S c in
      12 + fxi_target_bound ib c + fxi_encode_bound ib target +
        5 * Pos.size_nat (encode EX target) +
        (if FinSet.mem EX target members then
          3 + fxi_deps_bound ib c + fx_forward_deps_budget EX ib (System.deps SS c) else 0) +
        fx_forward_constraints_budget EX S SS ib members rest
  end.

(** The bound pays for both constructed sets and the source concatenation. *)

Definition fx_forward_boundary_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B)
    (component : list X) (suffix : list (list X)) : nat :=
  let later := concat suffix in
  2 + length suffix + length later + fxi_set_input_budget EX ib component +
    fxi_set_input_budget EX ib later +
    fx_forward_constraints_budget EX S SS ib (FinSet.of_list EX component) (System.constraints S).

(** Each source boundary contributes its own input-derived charge. *)

Fixpoint fx_observe_forward_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (order : list (list X)) : nat :=
  match order with
  | [] => 1
  | component :: rest => 1 + fx_forward_boundary_budget EX S SS ib component rest +
      fx_observe_forward_budget EX S SS ib rest
  end.

(** Constructing observation_boundaries contributes its own list frames. *)

Definition fx_observe_forward_run {X C B} (cb : fx_index_external_model X C B) (cs : list C)
    (order : list (list X)) : bool * list (fx_observe_forward_event X C B) :=
  let '(out, events) := fx_observe_forward cb cs order in
  (out, FxForwardBuild (length order) :: events).

(** Index and set events require their respective source adequacy relations; other forward events
    impose no source condition. *)

Definition fx_observe_forward_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_observe_forward_event X C B) : Prop :=
  match event with
  | FxForwardIndex events => fx_index_external_trace_adequacy source events
  | FxForwardSet events => fxi_set_external_adequacy source events
  | _ => True
  end.

(** The captured boundary check retains its source result, callbacks and input-derived work. *)

(** With index erasure and bounds and source relations for the actual encoder, target and
    dependency callbacks, forward checking preserves its result, source evidence and a work
    bound. *)
Definition fx_observe_forward_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B) (order : list (list X)),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    (forall x, let '(out, body) := fxi_encode cb x in fxi_encode_source source x out body) ->
    (forall c, let '(out, body) := fxi_target cb c in fxi_target_source source c out body) ->
    (forall c, let '(out, body) := fxi_deps cb c in fxi_deps_source source c out body) ->
    let '(out, events) := fx_observe_forward_run cb (System.constraints S) order in
    Forall (fx_observe_forward_event_source source) events /\
      out = observation_forward_check EX S SS order /\
      fx_observe_forward_work ib events <=
        2 + 2 * length order + fx_observe_forward_budget EX S SS ib order.
