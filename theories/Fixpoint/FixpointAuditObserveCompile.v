(** * Observation component compilation

    Compilation builds the dependency graph and root set once, then each induced component.
    For example, each local WTO sees its own filtered outgoing-closure bodies.
    Builds on: FixpointAuditObserveInduced and the nested-plan and WTO models. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphWto GraphAuditBase GraphAuditDfs
  GraphAuditWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointNested
  FixpointObserve FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklist
  FixpointAuditNestedPlan FixpointAuditNestedCallbacks FixpointAuditWorklistCallbacks
  FixpointAuditNarrowDiscovery FixpointAuditObserveExecute FixpointAuditObserveInduced
  FixpointAuditObserveCompare.
Import List.ListNotations.

Inductive fx_observe_compile_event (X C D B : Type) : Type :=
  | FxCompileDependency (events : list (fx_dep_event X C B))
  | FxCompileSet (events : list (audit_set_event X B))
  | FxCompileInduced (events : list (fx_induced_event X C B))
  | FxCompilePrepare (events : list (audit_prepare_source_event X (X * X) (fx_induced_event X C B)))
  | FxCompileWto (events : list (audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_induced_event X C B))))
  | FxCompilePlan (events : list (fx_nested_plan_event X D))
  | FxCompileHeads (events : list (audit_set_event X (fx_encoder_entry X)))
  | FxCompileTargets (events : list (audit_map_event X (list D) (fx_encoder_entry X)))
  | FxCompileExpiry (events : list (audit_map_event X (list X) (fx_encoder_entry X)))
  | FxCompileCase.

Arguments FxCompileDependency {X C D B} _.

Arguments FxCompileSet {X C D B} _.

Arguments FxCompileInduced {X C D B} _.

Arguments FxCompilePrepare {X C D B} _.

Arguments FxCompileWto {X C D B} _.

Arguments FxCompilePlan {X C D B} _.

Arguments FxCompileHeads {X C D B} _.

Arguments FxCompileTargets {X C D B} _.

Arguments FxCompileExpiry {X C D B} _.

Arguments FxCompileCase {X C D B}.

(** Every requested target key captures both its input lookup and output write. *)

Fixpoint fx_compile_restrict {X C D B} (EX : encoding X) (targets : Map.t X (list D))
    (members : list X) : Map.t X (list D) * list (fx_observe_compile_event X C D B) :=
  match members with
  | [] => (Map.empty, [FxCompileCase])
  | x :: rest =>
      let '(before, later) := @fx_compile_restrict X C D B EX targets rest in
      let '(found, read) := audit_map_get (fx_index_encoder EX) x targets in
      let values :=
        match found with
        | Some values => values
        | None => []
        end in
      let '(after, write) := audit_map_set (fx_index_encoder EX) x values before in
      (after, FxCompileCase :: later ++ [FxCompileTargets read; FxCompileTargets write])
  end.

(** Output filtering checks each component member against the once-built root set. *)

Fixpoint fx_compile_outputs {X C D B} (cb : fx_index_external_model X C B)
    (roots : FinSet.t X) (members : list X) : list X * list (fx_observe_compile_event X C D B) :=
  match members with
  | [] => ([], [FxCompileCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x roots in
      let '(later, events) := @fx_compile_outputs X C D B cb roots rest in
      (if present then x :: later else later, FxCompileCase :: FxCompileSet mem :: events)
  end.

(** One local component captures its induced graph, WTO, nested plan, outputs and expiry. *)

Definition fx_compile_component {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (graph : Graph.t X (X * X))
    (ix : sys_index X C) (targets : Map.t X (list D)) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) :
    ObservationComponent.t X D * list (fx_observe_compile_event X C D B) :=
  let '(keep, keep_events) := audit_finset_of_list (fxi_encode cb) members in
  let '(nodes, node_events) := fx_induced_filter_vertices cb keep (Graph.nodes graph) in
  let local := {| Graph.entries := members; Graph.nodes := nodes;
    Graph.out := Graph.out (induced EX keep graph); Graph.source := fst; Graph.target := snd |} in
  let '(prepared, prepare_events) := audit_prepare_source_counted EX local
    (fx_induced_prepare_cb cb ix keep) in
  let '(tokens, wto_events) := audit_wto_source_counted prepared (fx_induced_dfs_cb cb) in
  let '(code, parse_events) := @fx_nested_tree X D tokens in
  let '(nest_members, member_events) := @fx_nested_members X D EX code in
  let '(restrict, restrict_events) := @fx_compile_restrict X C D B EX targets members in
  let '(heads, head_events) := @fx_nested_heads X D code in
  let '(head_set, set_events) := audit_finset_of_list (fx_index_encoder EX) heads in
  let plan := NestedPlan.Make code nest_members restrict head_set in
  let '(outputs, output_events) := @fx_compile_outputs X C D B cb roots members in
  let '(expires, expire_events) :=
    match members with
    | [] => ([], [])
    | h :: _ =>
        let '(found, events) := audit_map_get (fx_index_encoder EX) h expiration in
        (
          match found with
          | Some xs => xs
          | None => []
          end, [FxCompileExpiry events])
    end in
  (ObservationComponent.Make members plan outputs expires,
    [FxCompileSet keep_events; FxCompileInduced node_events; FxCompilePrepare prepare_events;
     FxCompileWto wto_events; FxCompilePlan (parse_events ++ member_events)] ++ restrict_events ++
     [FxCompilePlan head_events; FxCompileHeads set_events] ++ output_events ++ expire_events).

(** Each component runs against the same dependency graph and root-set witness. *)

Fixpoint fx_compile_components {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (graph : Graph.t X (X * X))
    (ix : sys_index X C) (targets : Map.t X (list D)) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (order : list (list X)) :
    list (ObservationComponent.t X D) * list (fx_observe_compile_event X C D B) :=
  match order with
  | [] => ([], [FxCompileCase])
  | members :: rest =>
      let '(component, events) := fx_compile_component EX S SS cb graph ix targets roots
    expiration members in
      let '(later, tail) := fx_compile_components EX S SS cb graph ix targets roots expiration
    rest in
      (component :: later, FxCompileCase :: events ++ tail)
  end.

(** Targets compilation builds its graph and selected root set exactly once. *)

Definition fx_observe_compile_targets {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (targets : Map.t X (list D))
    (roots : list X) (p : observation_plan X) :
    list (ObservationComponent.t X D) * list (fx_observe_compile_event X C D B) :=
  let '(graph, ix, graph_events) := fx_dep_graph_build EX S SS cb in
  let '(selected, set_events) := audit_finset_of_list (fxi_encode cb) roots in
  let '(components, events) := fx_compile_components EX S SS cb graph ix targets selected
    (observation_expire p) (observation_components p) in
  (components, FxCompileDependency graph_events :: FxCompileSet set_events :: events).

(** Captured work includes the induced graph closures and every local-plan operation. *)

Definition fx_observe_compile_event_work {X C D B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_compile_event X C D B) : nat :=
  match event with
  | FxCompileDependency events => fx_dep_events_work ib events
  | FxCompileSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxCompileInduced events => fx_induced_work ib events
  | FxCompilePrepare events => audit_prepare_source_work (fx_induced_event_work ib) events
  | FxCompileWto events => audit_wto_source_work (fx_induced_event_work ib) events
  | FxCompilePlan events => fx_nested_plan_work events
  | FxCompileHeads events => audit_finset_source_work (@length (fx_encoder_entry X)) events
  | FxCompileTargets events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxCompileExpiry events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxCompileCase => 1
  end.

(** Compile work is a fold over the one captured component schedule. *)

Definition fx_observe_compile_work {X C D B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_compile_event X C D B)) : nat :=
  fold_right (fun event n => fx_observe_compile_event_work ib event + n) 0 events.

(** Every member incurs a target lookup/write and an output-membership test. *)

Fixpoint fx_compile_members_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (members : list X) : nat :=
  match members with
  | [] => 2
  | x :: rest => 20 + 26 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_compile_members_budget EX ib rest
  end.

(** This finite maximum covers actual graph vertices and all observed edge endpoints. *)

Definition fx_compile_callback_max {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (members : list X) : nat :=
  let graph := dependency_graph EX S SS in
  let ix := index_system EX S SS in
  let vertices := Graph.nodes graph ++ members ++
    flat_map (fun x => map snd (Graph.out graph x)) (Graph.nodes graph) in
  64 + fold_right (fun x n => Nat.max n
    (fx_induced_out_budget EX S SS ix ib x + fxi_encode_bound ib x)) 0 vertices.

(** This code bound covers parsing, nested members, head enumeration and head-set construction. *)

Definition fx_compile_code_budget {X} (EX : encoding X) (tokens : wto X) : nat :=
  let code := nested_tree tokens in
  let rows := nested_rows [] code in
  let heads := nested_heads code in
  let size := S (length tokens) in
  200 * size * size * size +
    40 * (fx_index_input_bits EX (map fst rows) + fx_index_input_bits EX heads).

(** Each component budget uses its actual induced graph, prepared graph and WTO. *)

Definition fx_compile_component_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (members : list X) : nat :=
  let graph := dependency_graph EX S SS in
  let local := observation_graph EX S SS members in
  let prepared := prepare EX local in
  let tokens := wto_total prepared in
  let count := audit_graph_prepare_full_event_bound local + audit_wto_input_event_bound prepared in
  fxi_set_input_budget EX ib members + fx_induced_vertices_budget EX ib (Graph.nodes graph) +
    audit_prepare_source_budget EX local + audit_wto_source_budget EX local prepared +
    64 * (1 + count) * fx_compile_callback_max EX S SS ib members +
    fx_compile_code_budget EX tokens + fx_compile_members_budget EX ib members +
    match members with
    | [] => 0
    | h :: _ => 6 + 5 * Pos.size_nat (encode EX h)
    end.

(** Component budgets sum over the actual plan order. *)

Fixpoint fx_compile_components_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (order : list (list X)) : nat :=
  match order with
  | [] => 1
  | members :: rest => 1 + fx_compile_component_budget EX S SS ib members +
      fx_compile_components_budget EX S SS ib rest
  end.

(** One graph and one root set precede the component budgets. *)

Definition fx_observe_compile_targets_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (roots : list X)
    (p : observation_plan X) : nat :=
  fx_dep_build_budget EX S SS ib + fxi_set_input_budget EX ib roots +
    fx_compile_components_budget EX S SS ib (observation_components p).

(** Output, target and map preparation events require their embedded induced-event source
    relations; other preparation events impose no condition. *)

Definition fx_compile_prepare_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_prepare_source_event X (X * X) (fx_induced_event X C B)) : Prop :=
  match event with
  | PrepareSourceOut _ _ body
  | PrepareSourceTarget _ _ body =>
      Forall (fx_induced_event_source source) body
  | PrepareSourceMap e =>
      match e with
      | AuditMapGet _ _ _ _ body _
      | AuditMapSet _ _ _ _ _ body _
      | AuditMapRemove _ _ _ _ body _ => Forall (fx_induced_event_source source) body
      end
  | _ => True
  end.

(** Each graph target or encoder capture requires its induced-event body to satisfy the supplied
    source relation. *)

Definition fx_compile_wto_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_induced_event X C B))) : Prop :=
  Forall (fun capture =>
    match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body
    | AuditGraphEncodeCapture _ _ _ _ _ body =>
        Forall (fx_induced_event_source source) body
    end) (snd event).

(** Dependency, set, induced graph, preparation and WTO events use embedded index sources and
    empty body groups; plan, head, target and expiry events use their source groups, while a case
    event requires none. *)

Definition fx_observe_compile_event_source {X C D A B E}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X D A E) (event : fx_observe_compile_event X C D B)
    (bodies : list (list E)) : Prop :=
  match event with
  | FxCompileDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FxCompileSet events => fxi_set_external_adequacy index_source events /\ bodies = []
  | FxCompileInduced events => Forall (fx_induced_event_source index_source) events /\ bodies = []
  | FxCompilePrepare events => Forall (fx_compile_prepare_source index_source) events /\ bodies = []
  | FxCompileWto events => Forall (fx_compile_wto_source index_source) events /\ bodies = []
  | FxCompilePlan events => exists groups,
      Forall2 (fx_nested_plan_event_source source) events groups /\ bodies = concat groups
  | FxCompileHeads events => Forall2 (fx_nested_entry_source source) (fx_nested_entries events)
    bodies
  | FxCompileTargets events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxCompileExpiry events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxCompileCase => bodies = []
  end.

(** Only actual nested-plan encoder calls contribute declared callback budgets. *)

Definition fx_observe_compile_external_budget {X C D A B E}
    (budget : fx_declared_callback_budget X D A E) (event : fx_observe_compile_event X C D B) :
    nat :=
  match event with
  | FxCompilePlan events =>
      fold_right (fun e n => fx_nested_plan_external_budget budget e + n) 0 events
  | FxCompileHeads events => fx_nested_entries_budget budget (fx_nested_entries events)
  | FxCompileTargets events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries
    events)
  | FxCompileExpiry events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries
    events)
  | _ => 0
  end.

(** The target-compilation statement gives its original result and source-related body witnesses. *)

(** With index erasure and bounds, dependency source laws and comparison source laws, target
    compilation preserves its original result with source receipts and a work bound. *)
Definition fx_observe_compile_targets_source_statement : Prop :=
  forall (X C D A B E : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X D A E)
    (budget : fx_declared_callback_budget X D A E) (targets : Map.t X (list D))
    (roots : list X) (p : observation_plan X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_compile_targets EX S SS cb targets roots p in
    exists bodies, Forall2 (fx_observe_compile_event_source index_source source) events bodies /\
      out = observation_compile_targets EX S SS targets roots p /\
      fx_observe_compile_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_compile_targets_budget EX S SS ib roots p +
        fold_right (fun e n => fx_observe_compile_external_budget budget e + n) 0 events.
