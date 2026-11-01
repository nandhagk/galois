(** * FixpointAuditScheduleWrapper model

    RPO scheduler preparation using the actual counted index, dependency out bodies,
    graph preparation, DFS, positions and retreating-edge traversal.
    For example, scheduler preparation records dependency graph traversal events.
    Builds on: FixpointSchedule and the counted graph and index models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditSchedule.
Import List.ListNotations.

Inductive fx_dep_event (X C B : Type) :=
  | FxDepIndexEvent (event : fx_index_nested_event X C B)
  | FxDepEncode (input : X) (code : positive) (body : list B)
  | FxDepCase (site : nat)
  | FxDepListWork (size : nat).

Arguments FxDepIndexEvent {X C B} _.

Arguments FxDepEncode {X C B} _ _ _.

Arguments FxDepCase {X C B} _.

Arguments FxDepListWork {X C B} _.

Fixpoint fx_dep_unknowns_input {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    list X * list (fx_dep_event X C B) :=
  match cs with
  | [] => ([], [FxDepCase 0])
  | c :: rest =>
      let '(target, tb) := fxi_target cb c in let '(deps, db) := fxi_deps cb c in
      let '(sides, sb) := fxi_sides cb c in
      let '(tail, events) := fx_dep_unknowns_input cb rest in
      (target :: deps ++ sides ++ tail,
       FxDepCase 0 :: FxDepIndexEvent (FxiTarget c target tb) ::
       FxDepIndexEvent (FxiDeps c deps db) :: FxDepIndexEvent (FxiSides c sides sb) ::
       FxDepListWork (length deps) :: events ++ [FxDepListWork (1 + length deps + length sides)])
  end.

Fixpoint fx_dep_outputs_input {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    list X * list (fx_dep_event X C B) :=
  match cs with
  | [] => ([], [FxDepCase 1])
  | c :: rest =>
      let '(target, tb) := fxi_target cb c in let '(sides, sb) := fxi_sides cb c in
      let '(tail, events) := fx_dep_outputs_input cb rest in
      (target :: sides ++ tail, FxDepCase 1 :: FxDepIndexEvent (FxiTarget c target tb) ::
        FxDepIndexEvent (FxiSides c sides sb) :: events ++ [FxDepListWork (1 + length sides)])
  end.

Definition fx_dep_out {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C) (y : X) :
    list (X * X) * list (fx_dep_event X C B) :=
  let '(code, encbody) := fxi_encode cb y in
  let '(raw, triebody) := audit_map_code_get code (readers ix) in
  let constraints :=
    match raw with
    | Some found => found
    | None => []
    end in
  let '(values, bodies) := fx_dep_outputs_input cb constraints in
  let '(distinct, distinct_events) := fxi_distinct_counted cb values in
  (map (fun x => (y, x)) distinct,
    FxDepCase 2 :: FxDepIndexEvent (FxiRead y code (readers ix) raw encbody triebody) ::
      bodies ++ map FxDepIndexEvent distinct_events ++ [FxDepListWork (length distinct); FxDepCase
        3]).

Definition fx_dep_graph_build {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
    Graph.t X (X * X) * sys_index X C * list (fx_dep_event X C B) :=
  let '(input, input_events) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(vertices, distinct_events) := fxi_distinct_counted cb input in
  let '(ix, index_events) := fx_index_nested_counted S cb in
  ({| Graph.entries := vertices; Graph.nodes := vertices;
      Graph.out := fun y => map (fun x => (y, x)) (distinct_unknowns EX
        (flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y)));
      Graph.source := fst; Graph.target := snd |}, ix,
   input_events ++ map FxDepIndexEvent distinct_events ++ map FxDepIndexEvent index_events).

Definition fx_dep_encoder {X C B} (cb : fx_index_external_model X C B) (x : X) :
    positive * list (fx_dep_event X C B) :=
  let '(code, body) := fxi_encode cb x in (code, [FxDepEncode x code body]).

Definition fx_dep_prepare_cb {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C) :
    audit_prepare_callback_model X (X * X) (fx_dep_event X C B) :=
  AuditPrepareCallbackModel X (X * X) (fx_dep_event X C B)
    (fx_dep_out cb ix) (fun e => (snd e, [FxDepCase 4])) (fx_dep_encoder cb).

Definition fx_dep_dfs_cb {X C B} (cb : fx_index_external_model X C B) :
    audit_dfs_callback_model X (X * X) (fx_dep_event X C B) :=
  AuditDfsCallbackModel X (X * X) (fx_dep_event X C B)
    (fun e => (snd e, [FxDepCase 5])) (fx_dep_encoder cb).

Definition fx_dep_rpo_cb {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C) :
    audit_rpo_graph_callbacks X (X * X) (fx_dep_event X C B) :=
  AuditRpoGraphCallbacks X (X * X) (fx_dep_event X C B) (fx_dep_encoder cb)
    (fx_dep_out cb ix) (fun e => (fst e, [FxDepCase 6])) (fun e => (snd e, [FxDepCase 7])).

Definition fx_dep_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_dep_event X C B) : nat :=
  16 +
    match event with
    | FxDepIndexEvent nested => fxi_event_work ib nested
    | FxDepEncode _ _ body => fxi_body_work ib body
    | FxDepCase _ => 0
    | FxDepListWork size => 1 + size
    end.

Definition fx_dep_events_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_dep_event X C B)) : nat :=
  fold_right (fun event n => fx_dep_event_work ib event + n) 0 events.

(** With index callback erasure, dependency preparation returns the original graph and system
    index. *)
Definition fx_dep_build_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let '(g, ix, _) := fx_dep_graph_build EX S SS cb in
    g = dependency_graph EX S SS /\ ix = index_system EX S SS.

(** With index callback erasure, dependency output contains edges from the queried key to
    distinct indexed-reader targets and side targets. *)
Definition fx_dep_out_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) ix y,
    fx_index_external_erases EX S SS cb ->
    fst (fx_dep_out cb ix y) =
      map (fun x => (y, x)) (distinct_unknowns EX
        (flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y))).

Record fx_rpo_result (X C B : Type) := FxRpoResult {
  fx_rpo_positions : Map.t X positive;
  fx_rpo_heads : FinSet.t X;
  fx_rpo_reverse_input : list X;
  fx_rpo_reverse_output : list X;
  fx_rpo_reverse_work : nat;
  fx_rpo_build_events : list (fx_dep_event X C B);
  fx_rpo_prepare_events : list (audit_prepare_source_event X (X * X) (fx_dep_event X C B));
  fx_rpo_dfs_events : list (audit_dfs_nested_event X (X * X)
    (audit_graph_callback_capture X (X * X) (fx_dep_event X C B)));
  fx_rpo_position_events : list (audit_rpo_schedule_event X (fx_dep_event X C B));
  fx_rpo_retreat_events : list (audit_rpo_graph_event X (X * X) (fx_dep_event X C B))
}.

Arguments FxRpoResult {X C B} _ _ _ _ _ _ _ _ _ _.

Arguments fx_rpo_positions {X C B} _.

Arguments fx_rpo_heads {X C B} _.

Arguments fx_rpo_reverse_input {X C B} _.

Arguments fx_rpo_reverse_output {X C B} _.

Arguments fx_rpo_reverse_work {X C B} _.

Arguments fx_rpo_build_events {X C B} _.

Arguments fx_rpo_prepare_events {X C B} _.

Arguments fx_rpo_dfs_events {X C B} _.

Arguments fx_rpo_position_events {X C B} _.

Arguments fx_rpo_retreat_events {X C B} _.

Definition fx_rpo_scheduler_counted {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) : fx_rpo_result X C B :=
  let '(g, ix, build) := fx_dep_graph_build EX S SS cb in
  let '(p, prepare_events) := audit_prepare_source_counted EX g (fx_dep_prepare_cb cb ix) in
  let '(search, dfs_events) := audit_dfs_source_counted p (fx_dep_dfs_cb cb) FinSet.empty
    (Graph.entries g) in
  let '(order, reverse_work) := audit_graph_reverse_fast_counted (postorder search) [] in
  let '(positions, position_events) := audit_rpo_schedule_positions (fx_dep_encoder cb) order 1 in
  let '(heads, retreat_events) := audit_rpo_schedule_retreats (fx_dep_rpo_cb cb ix) g search in
  FxRpoResult positions heads (postorder search) order reverse_work
    build prepare_events dfs_events position_events retreat_events.

(** With index callback erasure, scheduler priority and widening queries agree with the original
    scheduler. *)
Definition fx_rpo_scheduler_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    forall x,
      fst (audit_rpo_schedule_priority (fx_dep_encoder cb) (fx_rpo_positions result) x) =
        priority (rpo_scheduler EX S SS) x /\
      fst (audit_rpo_schedule_widening (fx_dep_encoder cb) (fx_rpo_heads result) x) =
        widening_point (rpo_scheduler EX S SS) x.

Definition fx_rpo_scheduler_work {X C B} (ib : fx_index_external_budget X C B)
    (result : fx_rpo_result X C B) : nat :=
  fx_dep_events_work ib (fx_rpo_build_events result) + fx_rpo_reverse_work result +
  audit_prepare_source_work (fx_dep_event_work ib) (fx_rpo_prepare_events result) +
  audit_dfs_source_work (fx_dep_event_work ib) (fx_rpo_dfs_events result) +
  audit_rpo_schedule_work (fx_dep_event_work ib) (fx_rpo_position_events result) +
  audit_rpo_graph_work (fx_dep_event_work ib) (fx_rpo_retreat_events result).

(** Source-intermediate budgets use the real operands, not a caller-supplied global bound. *)

Definition fx_dep_unknowns_native {X C A} (S : System.t X C A) (SS : System.static S) : list X :=
  flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c) (System.constraints S).

Definition fx_dep_out_values_native {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (y : X) : list X :=
  flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y).

Definition fx_dep_callback_budget {X C B} (ib : fx_index_external_budget X C B) (cs : list C) : nat
  :=
  fold_right (fun c n => fxi_target_bound ib c + fxi_deps_bound ib c + fxi_sides_bound ib c + n) 0
    cs.

Definition fx_dep_build_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let cs := System.constraints S in let input := fx_dep_unknowns_native S SS in
  1024 * (1 + length cs + length input) + fx_dep_callback_budget ib cs +
    fxi_distinct_input_budget EX ib input + fx_index_nested_input_budget EX S SS ib.

Definition fx_dep_out_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B) (y : X) : nat
      :=
  let cs := readers_of EX ix y in let values := fx_dep_out_values_native EX S SS ix y in
  1024 * (1 + length cs + length values) + fx_dep_callback_budget ib cs +
    32 * Pos.size_nat (encode EX y) + fxi_encode_bound ib y + fxi_distinct_input_budget EX ib
      values.

(** With index callback erasure and bounds, dependency graph construction fits its input-derived
    budget. *)
Definition fx_dep_build_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(_, _, events) := fx_dep_graph_build EX S SS cb in
    fx_dep_events_work ib events <= fx_dep_build_budget EX S SS ib.

(** With index callback erasure and bounds, a dependency output query fits the budget for its
    index and queried vertex. *)
Definition fx_dep_out_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B) ix y,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_events_work ib (snd (fx_dep_out cb ix y)) <= fx_dep_out_budget EX S SS ix ib y.

Definition fx_rpo_callback_max {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let g := dependency_graph EX S SS in let ix := index_system EX S SS in
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map fst edges ++ map snd edges in
  64 + fold_right (fun x n => Nat.max n
    (fx_dep_out_budget EX S SS ix ib x + fxi_encode_bound ib x)) 0 vertices.

Definition fx_rpo_receipt_count_limit {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : nat :=
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let search := dfs p FinSet.empty (Graph.entries g) in
  audit_graph_prepare_full_event_bound g + audit_dfs_full_input_event_bound p (Graph.entries g) +
    16 * (1 + length (postorder search)) + audit_rpo_graph_budget EX g search.

Definition fx_rpo_scheduler_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let search := dfs p FinSet.empty (Graph.entries g) in
  let receipt_count := fx_rpo_receipt_count_limit EX S SS in
  fx_dep_build_budget EX S SS ib + audit_prepare_source_budget EX g +
    audit_dfs_source_budget EX g p (Graph.entries g) +
    audit_graph_reverse_fast_work (length (postorder search)) +
    audit_rpo_positions_budget EX (rpo search) 1 +
    audit_rpo_graph_budget EX g search + 64 * (1 + receipt_count) * fx_rpo_callback_max EX S SS ib.

(** With index callback erasure and bounds, the complete counted scheduler preparation fits its
    input-derived budget. *)
Definition fx_rpo_scheduler_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    fx_rpo_scheduler_work ib result <= fx_rpo_scheduler_budget EX S SS ib.

(** The modeled encoder, target, side and dependency callbacks each produce a result and body
    satisfying its source relation. *)

Definition fx_dep_source_laws {X C B} (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) : Prop :=
  (forall x, let '(out, body) := fxi_encode cb x in fxi_encode_source source x out body) /\
  (forall c, let '(out, body) := fxi_target cb c in fxi_target_source source c out body) /\
  (forall c, let '(out, body) := fxi_sides cb c in fxi_sides_source source c out body) /\
  (forall c, let '(out, body) := fxi_deps cb c in fxi_deps_source source c out body).

(** Index and encoding events satisfy their corresponding callback source relations; other events
    need no receipt. *)
Definition fx_dep_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_dep_event X C B) : Prop :=
  match event with
  | FxDepIndexEvent e => fx_index_external_trace_adequacy source [e]
  | FxDepEncode x code body => fxi_encode_source source x code body
  | _ => True
  end.

(** Every dependency event in the body satisfies its callback source relation. *)
Definition fx_dep_body_source {X C B} (source : fx_index_external_source X C B)
    (body : list (fx_dep_event X C B)) : Prop := Forall (fx_dep_event_source source) body.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.

(** Each map operation's embedded dependency events satisfy the callback source relation. *)
Definition fx_dep_map_source {X C B A} (source : fx_index_external_source X C B)
    (event : audit_map_event X A (fx_dep_event X C B)) : Prop :=
  match event with
  | AuditMapGet _ _ _ _ body _
  | AuditMapSet _ _ _ _ _ body _
  | AuditMapRemove _ _ _ _ body _ => fx_dep_body_source source body
  end.

(** Set updates and membership operations satisfy their embedded dependency source relation;
    folds need none. *)
Definition fx_dep_set_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_set_event X (fx_dep_event X C B)) : Prop :=
  match event with
  | AuditSetAdd _ _ _ _ body _
  | AuditSetMem _ _ _ _ body _
  | AuditSetRemove _ _ _ _ body _ => fx_dep_body_source source body
  | AuditSetFold _ _ => True
  end.

(** Output, target and map preparation events require their embedded dependency source relations;
    other preparation events impose no condition. *)
Definition fx_dep_prepare_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_prepare_source_event X (X * X) (fx_dep_event X C B)) : Prop :=
  match event with
  | PrepareSourceOut _ _ body
  | PrepareSourceTarget _ _ body => fx_dep_body_source source body
  | PrepareSourceMap e => fx_dep_map_source source e
  | _ => True
  end.

(** Every target or encoder capture in the DFS event satisfies the dependency callback source
    relation. *)
Definition fx_dep_dfs_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_dfs_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))) : Prop :=
  Forall (fun capture =>
    match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body
    | AuditGraphEncodeCapture _ _ _ _ _ body =>
        fx_dep_body_source source body
    end) (snd event).

(** Map and set scheduler-position events require their embedded source relations; other position
    events impose no condition. *)
Definition fx_dep_positions_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_rpo_schedule_event X (fx_dep_event X C B)) : Prop :=
  match event with
  | RpoScheduleMap e => fx_dep_map_source source e
  | RpoScheduleSet e => fx_dep_set_source source e
  | _ => True
  end.

(** Graph-callback, rank-map and set retreat events require their embedded source relations;
    other retreat events impose no condition. *)
Definition fx_dep_retreat_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_rpo_graph_event X (X * X) (fx_dep_event X C B)) : Prop :=
  match event with
  | RpoGraphOut _ _ body
  | RpoGraphSource _ _ body
  | RpoGraphTarget _ _ body => fx_dep_body_source
    source body
  | RpoGraphRank e => fx_dep_map_source source e
  | RpoGraphSet e => fx_dep_set_source source e
  | _ => True
  end.

(** If the dependency callbacks satisfy their source laws, scheduler construction and its
    preparation, DFS, position and retreat events satisfy their respective source relations. *)
Definition fx_rpo_scheduler_source_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (source : fx_index_external_source X C B),
    fx_dep_source_laws cb source ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    fx_dep_body_source source (fx_rpo_build_events result) /\
    Forall (fx_dep_prepare_source source) (fx_rpo_prepare_events result) /\
    Forall (fx_dep_dfs_source source) (fx_rpo_dfs_events result) /\
    Forall (fx_dep_positions_source source) (fx_rpo_position_events result) /\
    Forall (fx_dep_retreat_source source) (fx_rpo_retreat_events result).

(** With index callback erasure, the combined preparation, DFS, position and retreat receipt
    count fits its limit. *)
Definition fx_rpo_receipt_count_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    length (fx_rpo_prepare_events result) + length (fx_rpo_dfs_events result) +
      length (fx_rpo_position_events result) + length (fx_rpo_retreat_events result) <=
      fx_rpo_receipt_count_limit EX S SS.

(** Prospective source boundary: AUD-GR-DFS implements the equivalent fast `rpo` reverse.
    The unchanged baseline uses `rev`; this model makes no claim that the refactor has landed. *)

(** With index callback erasure, scheduler construction records DFS postorder and RPO, a
    fast-reverse run between them and its exact work. *)
Definition fx_rpo_fast_reverse_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    let g := dependency_graph EX S SS in let p := prepare EX g in
    let search := dfs p FinSet.empty (Graph.entries g) in
    fx_rpo_reverse_input result = postorder search /\
    fx_rpo_reverse_output result = rpo search /\
    audit_graph_reverse_fast_run (fx_rpo_reverse_input result) []
      (fx_rpo_reverse_output result) (fx_rpo_reverse_work result) /\
    fx_rpo_reverse_work result = audit_graph_reverse_fast_work (length (postorder search)).
