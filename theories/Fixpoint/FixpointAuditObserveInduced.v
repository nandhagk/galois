(** * Observation induced-graph callbacks

    Each component graph filters the dependency graph by its concrete member set.
    For example, an outgoing edge is retained only after checking its actual target.
    Builds on: FixpointAuditScheduleWrapper and the counted set model. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphAuditBase GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointAuditIndex
  FixpointAuditScheduleWrapper.
Import List.ListNotations.

Inductive fx_induced_event (X C B : Type) : Type :=
  | FxInducedDependency (events : list (fx_dep_event X C B))
  | FxInducedSet (events : list (audit_set_event X B))
  | FxInducedEncode (x : X) (code : positive) (body : list B)
  | FxInducedCase.

Arguments FxInducedDependency {X C B} _.

Arguments FxInducedSet {X C B} _.

Arguments FxInducedEncode {X C B} _ _ _.

Arguments FxInducedCase {X C B}.

(** Every input vertex is checked, including repeated vertices. *)

Fixpoint fx_induced_filter_vertices {X C B} (cb : fx_index_external_model X C B)
    (keep : FinSet.t X) (vertices : list X) : list X * list (fx_induced_event X C B) :=
  match vertices with
  | [] => ([], [FxInducedCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x keep in
      let '(later, events) := fx_induced_filter_vertices cb keep rest in
      (if present then x :: later else later, FxInducedCase :: FxInducedSet mem :: events)
  end.

(** Every edge checks its actual target and keeps the original pair and order. *)

Fixpoint fx_induced_filter_edges {X C B} (cb : fx_index_external_model X C B)
    (keep : FinSet.t X) (edges : list (X * X)) :
    list (X * X) * list (fx_induced_event X C B) :=
  match edges with
  | [] => ([], [FxInducedCase])
  | edge :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) (snd edge) keep in
      let '(later, events) := fx_induced_filter_edges cb keep rest in
      (if present then edge :: later else later, FxInducedCase :: FxInducedSet mem :: events)
  end.

(** The graph's outgoing closure first invokes the concrete dependency-graph closure. *)

Definition fx_induced_out {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C)
    (keep : FinSet.t X) (x : X) : list (X * X) * list (fx_induced_event X C B) :=
  let '(edges, dependency) := fx_dep_out cb ix x in
  let '(out, filtered) := fx_induced_filter_edges cb keep edges in
  (out, FxInducedDependency dependency :: filtered).

(** The induced encoder records the modeled encoder's returned code and body. *)

Definition fx_induced_encoder {X C B} (cb : fx_index_external_model X C B) (x : X) :
    positive * list (fx_induced_event X C B) :=
  let '(code, body) := fxi_encode cb x in (code, [FxInducedEncode x code body]).

(** Graph preparation uses the induced out closure and concrete pair projections. *)

Definition fx_induced_prepare_cb {X C B} (cb : fx_index_external_model X C B)
    (ix : sys_index X C) (keep : FinSet.t X) :
    audit_prepare_callback_model X (X * X) (fx_induced_event X C B) :=
  AuditPrepareCallbackModel X (X * X) (fx_induced_event X C B)
    (fx_induced_out cb ix keep) (fun edge => (snd edge, [FxInducedCase])) (fx_induced_encoder cb).

(** WTO graph traversals use the same encoder and concrete target projection. *)

Definition fx_induced_dfs_cb {X C B} (cb : fx_index_external_model X C B) :
    audit_dfs_callback_model X (X * X) (fx_induced_event X C B) :=
  AuditDfsCallbackModel X (X * X) (fx_induced_event X C B)
    (fun edge => (snd edge, [FxInducedCase])) (fx_induced_encoder cb).

(** A captured induced event charges its selected dependency or finite-set child body. *)

Definition fx_induced_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_induced_event X C B) : nat :=
  8 +
    match event with
    | FxInducedDependency events => fx_dep_events_work ib events
    | FxInducedSet events => audit_finset_source_work (fxi_body_work ib) events
    | FxInducedEncode _ _ body => fxi_body_work ib body
    | FxInducedCase => 0
    end.

(** Work folds a concrete induced-closure body. *)

Definition fx_induced_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_induced_event X C B)) : nat :=
  fold_right (fun event n => fx_induced_event_work ib event + n) 0 events.

(** Filtering budgets use every input endpoint and the original encoder's actual input budget. *)

Fixpoint fx_induced_vertices_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (vertices : list X) : nat :=
  match vertices with
  | [] => 8
  | x :: rest => 32 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_induced_vertices_budget EX ib rest
  end.

(** Outgoing work includes the dependency callback and all filtered edge targets. *)

Definition fx_induced_out_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B) (x : X) :
    nat :=
  fx_dep_out_budget EX S SS ix ib x + 8 +
    fx_induced_vertices_budget EX ib
      (distinct_unknowns EX (fx_dep_out_values_native EX S SS ix x)).

(** Dependency, set and encoder events require their respective source relations; induced-case
    events impose no source condition. *)

Definition fx_induced_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_induced_event X C B) : Prop :=
  match event with
  | FxInducedDependency events => fx_dep_body_source source events
  | FxInducedSet events => fxi_set_external_adequacy source events
  | FxInducedEncode x code body => fxi_encode_source source x code body
  | FxInducedCase => True
  end.

(** The actual induced out closure preserves selected edges and has an input-derived bound. *)

(** With index erasure and bounds and dependency source laws, induced output retains its filtered
    edges, source evidence and a work bound. *)
Definition fx_induced_out_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B) (keep : FinSet.t X) (x : X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb source ->
    let '(out, events) := fx_induced_out cb ix keep x in
    Forall (fx_induced_event_source source) events /\
      out = filter (fun edge => FinSet.mem EX (snd edge) keep)
        (map (fun y => (x, y)) (distinct_unknowns EX
          (flat_map (fun c => System.target S c :: System.side_targets SS c) (readers_of EX ix
    x)))) /\
      fx_induced_work ib events <= fx_induced_out_budget EX S SS ix ib x.
