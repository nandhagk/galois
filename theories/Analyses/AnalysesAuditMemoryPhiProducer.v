(** * End-to-end counted phi producer candidate

    This file joins actual prepared inputs, dependency SCCs, ordered representative
    updates, and the returned memory graph in one source-shaped execution. The
    result retains every intermediate trace rather than pricing an opaque producer.
    For example, dependency-row events remain available in the returned run.
    Builds on: AnalysesAuditMemoryPhiState and the counted row, preparation and resolution models.
      *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphDfs GraphAuditBase
  GraphAuditDfs GraphAuditScc.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiRows AnalysesAuditMemoryPhiPrepare
  AnalysesAuditMemoryPhiResolve.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditEncoding CollectionsAuditPrimitive.
From Galois.Analyses Require Import AnalysesAuditMemoryIndex.
Import List.ListNotations.

Definition audit_phi_producer_rep {N E} (EN : encoding N) (EE : encoding E)
    (reps : Map.t (memory_version N E) (memory_version N E))
    (v : memory_version N E) : memory_version N E :=
  match Map.get (memory_version_encoding EN EE) v reps with
  | Some representative => representative
  | None => v
  end.

Inductive audit_phi_graph_callback_event (N E CN : Type) : Type :=
  | AuditPhiGraphEncodeBody (events : list CN)
  | AuditPhiGraphOutBody
      (events : list (audit_map_event N (list (phi_dependency_edge N E)) CN)).
Arguments AuditPhiGraphEncodeBody {N E CN} _.
Arguments AuditPhiGraphOutBody {N E CN} _.

Definition audit_phi_graph_callback_work {N E CN} (node_work : list CN -> nat)
    (event : audit_phi_graph_callback_event N E CN) : nat :=
  match event with
  | AuditPhiGraphEncodeBody calls => node_work calls
  | AuditPhiGraphOutBody calls => audit_map_source_work node_work calls
  end.

Definition audit_phi_prepare_callbacks {N E CN} (node_enc : N -> positive * list CN)
    (rows : Map.t N (list (phi_dependency_edge N E)))
    (dep : Graph.t N (phi_dependency_edge N E)) :
    audit_prepare_callback_model N (phi_dependency_edge N E) (audit_phi_graph_callback_event N E
      CN) :=
  @AuditPrepareCallbackModel N (phi_dependency_edge N E) (audit_phi_graph_callback_event N E CN)
    (fun n => let '(found, calls) := audit_map_get node_enc n rows in
      (
        match found with
        | Some edges => edges
        | None => []
        end, [AuditPhiGraphOutBody calls]))
    (fun edge => (Graph.target dep edge, []))
    (fun n => let '(code, events) := node_enc n in (code, [AuditPhiGraphEncodeBody events])).

Definition audit_phi_scc_callbacks {N E CN} (node_enc : N -> positive * list CN)
    (dep : Graph.t N (phi_dependency_edge N E)) :
    audit_dfs_callback_model N (phi_dependency_edge N E) (audit_phi_graph_callback_event N E CN) :=
  @AuditDfsCallbackModel N (phi_dependency_edge N E) (audit_phi_graph_callback_event N E CN)
    (fun edge => (Graph.target dep edge, []))
    (fun n => let '(code, events) := node_enc n in (code, [AuditPhiGraphEncodeBody events])).

(** The output constructor records actual mapped fields and the stable kept-phi
    filter. Non-phi versions retain their source order and identity. *)
Definition audit_phi_producer_output {N E} (EN : encoding N) (EE : encoding E)
    (old : memory_graph N E) (reps : Map.t (memory_version N E) (memory_version N E))
    : memory_graph N E :=
  let rep := audit_phi_producer_rep EN EE reps in
  let kept := filter (fun n =>
    Pos.eqb (encode (memory_version_encoding EN EE) (MemoryPhi n)) (encode
      (memory_version_encoding EN EE) (rep (MemoryPhi n))))
    (memory_phis old) in
  let kept_set := FinSet.of_list EN kept in
  MemoryGraph
    (filter (fun n => FinSet.mem EN n kept_set) (memory_phis old))
    (filter (fun v =>
      match v with
      | MemoryPhi n => FinSet.mem EN n kept_set
      | _ => true
      end) (memory_versions old))
    (fun n => rep (memory_in old n))
    (fun e i => option_map rep (memory_before old e i))
    (fun e => rep (memory_out old e))
    (fun n key => option_map rep (memory_operand old n key)).

Inductive audit_phi_output_event (N E CN CV : Type) : Type :=
  | AuditPhiOutputPhiCase (remaining : list N)
  | AuditPhiOutputRepRead (node : N) (found : option (memory_version N E))
      (calls : list (audit_map_event (memory_version N E) (memory_version N E) CV))
  | AuditPhiOutputRepEncode (version : memory_version N E) (code : positive) (body : list CV)
  | AuditPhiOutputRepCompare (node : N) (result : bool) (calls : list audit_positive_eqb_event)
  | AuditPhiOutputSetBuild (calls : list (audit_set_event N CN))
  | AuditPhiOutputPhiProbe (node : N) (result : bool) (calls : list (audit_set_event N CN))
  | AuditPhiOutputVersionCase (remaining : list (memory_version N E))
  | AuditPhiOutputVersionProbe (version : memory_version N E) (result : bool)
      (calls : list (audit_set_event N CN)).
Arguments AuditPhiOutputPhiCase {N E CN CV} _.
Arguments AuditPhiOutputRepRead {N E CN CV} _ _ _.
Arguments AuditPhiOutputRepEncode {N E CN CV} _ _ _.
Arguments AuditPhiOutputRepCompare {N E CN CV} _ _ _.
Arguments AuditPhiOutputSetBuild {N E CN CV} _.
Arguments AuditPhiOutputPhiProbe {N E CN CV} _ _ _.
Arguments AuditPhiOutputVersionCase {N E CN CV} _.
Arguments AuditPhiOutputVersionProbe {N E CN CV} _ _ _.

Fixpoint audit_phi_output_keep_phis {N E CN CV} (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (reps : Map.t (memory_version N E) (memory_version N E)) (nodes : list N)
    : list N * list (audit_phi_output_event N E CN CV) :=
  match nodes with
  | [] => ([], [AuditPhiOutputPhiCase nodes])
  | n :: rest =>
      let '(found, read_events) := audit_map_get version_enc (MemoryPhi n) reps in
      let representative :=
        match found with
        | Some v => v
        | None => MemoryPhi n
        end in
      let '(left_code, left_body) := version_enc (MemoryPhi n) in
      let '(right_code, right_body) := version_enc representative in
      let '(same, eq_events) := audit_positive_eqb left_code right_code in
      let '(kept, tail_events) := audit_phi_output_keep_phis EN EE node_enc version_enc reps rest in
      (if same then n :: kept else kept,
        [AuditPhiOutputPhiCase nodes; AuditPhiOutputRepRead n found read_events;
         AuditPhiOutputRepEncode (MemoryPhi n) left_code left_body;
         AuditPhiOutputRepEncode representative right_code right_body;
         AuditPhiOutputRepCompare n same eq_events] ++ tail_events)
  end.

Fixpoint audit_phi_output_filter_nodes {N E CN CV} (node_enc : N -> positive * list CN)
    (kept : FinSet.t N) (nodes : list N) : list N * list (audit_phi_output_event N E CN CV) :=
  match nodes with
  | [] => ([], [AuditPhiOutputPhiCase nodes])
  | n :: rest =>
      let '(found, calls) := audit_finset_mem node_enc n kept in
      let '(tail, tail_events) := audit_phi_output_filter_nodes node_enc kept rest in
      (if found then n :: tail else tail,
        AuditPhiOutputPhiProbe n found calls :: tail_events)
  end.

Fixpoint audit_phi_output_filter_versions {N E CN CV}
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    (kept : FinSet.t N) (versions : list (memory_version N E))
    : list (memory_version N E) * list (audit_phi_output_event N E CN CV) :=
  match versions with
  | [] => ([], [AuditPhiOutputVersionCase versions])
  | v :: rest =>
      let '(keep, events) :=
        match v with
        | MemoryLive | MemoryDef _ _ => (true, [])
        | MemoryPhi n => let '(found, calls) := audit_finset_mem node_enc n kept in
            (found, [AuditPhiOutputVersionProbe v found calls])
      end in
      let '(tail, tail_events) := audit_phi_output_filter_versions node_enc version_enc kept rest in
      (if keep then v :: tail else tail,
        AuditPhiOutputVersionCase versions :: events ++ tail_events)
  end.

(** The output is assembled from the same representatives and the actual filter
    probes captured here. Function-valued fields remain closures and cost only
    when consumers call them. *)
Definition audit_phi_producer_output_counted {N E CN CV}
    (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (old : memory_graph N E) (reps : Map.t (memory_version N E) (memory_version N E))
    : memory_graph N E * list (audit_phi_output_event N E CN CV) :=
  let '(kept, reps_events) := audit_phi_output_keep_phis EN EE node_enc version_enc reps
    (memory_phis old) in
  let '(kept_set, set_events) := audit_finset_of_list node_enc kept in
  let '(phis, phi_events) := audit_phi_output_filter_nodes node_enc kept_set (memory_phis old) in
  let '(versions, version_events) := audit_phi_output_filter_versions node_enc version_enc kept_set
    (memory_versions old) in
  let rep := audit_phi_producer_rep EN EE reps in
  (MemoryGraph phis versions (fun n => rep (memory_in old n))
    (fun e i => option_map rep (memory_before old e i))
    (fun e => rep (memory_out old e))
    (fun n key => option_map rep (memory_operand old n key)),
   reps_events ++ [AuditPhiOutputSetBuild set_events] ++ phi_events ++ version_events).

Fixpoint audit_phi_output_source_work {N E CN CV}
    (node_work : list CN -> nat) (version_work : list CV -> nat)
    (events : list (audit_phi_output_event N E CN CV)) : nat :=
  match events with
  | [] => 0
  | AuditPhiOutputPhiCase _ :: rest => 2 + audit_phi_output_source_work node_work version_work rest
  | AuditPhiOutputRepRead _ _ calls :: rest => 2 + audit_map_source_work version_work calls +
      audit_phi_output_source_work node_work version_work rest
  | AuditPhiOutputRepEncode _ _ body :: rest => 1 + version_work body +
      audit_phi_output_source_work node_work version_work rest
  | AuditPhiOutputRepCompare _ _ calls :: rest => 2 + audit_positive_eqb_source_work calls +
      audit_phi_output_source_work node_work version_work rest
  | AuditPhiOutputSetBuild calls :: rest => 2 + audit_finset_source_work node_work calls +
      audit_phi_output_source_work node_work version_work rest
  | AuditPhiOutputPhiProbe _ _ calls :: rest => 2 + audit_finset_source_work node_work calls +
      audit_phi_output_source_work node_work version_work rest
  | AuditPhiOutputVersionCase _ :: rest => 2 + audit_phi_output_source_work node_work version_work
    rest
  | AuditPhiOutputVersionProbe _ _ calls :: rest => 2 + audit_finset_source_work node_work calls +
      audit_phi_output_source_work node_work version_work rest
  end.

Inductive audit_phi_dependency_row_event (N E CN : Type) : Type :=
  | AuditPhiDependencyRowGet (node : N)
      (found : option (list (option E * memory_version N E)))
      (calls : list (audit_map_event N (list (option E * memory_version N E)) CN))
  | AuditPhiDependencyRowCase (remaining : list (option E * memory_version N E))
  | AuditPhiDependencyEdgeKeep (node : N) (key : option E) (target : N).
Arguments AuditPhiDependencyRowGet {N E CN} _ _ _.
Arguments AuditPhiDependencyRowCase {N E CN} _.
Arguments AuditPhiDependencyEdgeKeep {N E CN} _ _ _.

Fixpoint audit_phi_dependency_row_entries {N E CN} (node : N)
    (row : list (option E * memory_version N E))
    : list (phi_dependency_edge N E) * list (audit_phi_dependency_row_event N E CN) :=
  match row with
  | [] => ([], [AuditPhiDependencyRowCase row])
  | (key, value) :: rest =>
      let '(tail, events) := audit_phi_dependency_row_entries node rest in
      match value with
      | MemoryPhi target =>
          (PhiDependencyEdgeData node key target :: tail,
            [AuditPhiDependencyRowCase row; AuditPhiDependencyEdgeKeep node key target] ++ events)
      | MemoryLive | MemoryDef _ _ =>
          (tail, AuditPhiDependencyRowCase row :: events)
      end
  end.

Definition audit_phi_dependency_row {N E CN}
    (node_enc : N -> positive * list CN)
    (inputs : Map.t N (list (option E * memory_version N E))) (node : N)
    : list (phi_dependency_edge N E) * list (audit_phi_dependency_row_event N E CN) :=
  let '(found, calls) := audit_map_get node_enc node inputs in
  let row :=
    match found with
    | Some xs => xs
    | None => []
    end in
  let '(edges, events) := audit_phi_dependency_row_entries node row in
  (edges, AuditPhiDependencyRowGet node found calls :: events).

Definition audit_phi_dependency_rows_counted {N E CN}
    (node_enc : N -> positive * list CN) (mg : memory_graph N E)
    (inputs : Map.t N (list (option E * memory_version N E))) :=
  audit_memory_result_index node_enc (audit_phi_dependency_row node_enc inputs)
    (memory_phis mg).

Definition audit_phi_dependency_graph_counted {N E CN}
    (EN : encoding N) (node_enc : N -> positive * list CN) (mg : memory_graph N E)
    (inputs : Map.t N (list (option E * memory_version N E)))
    : Graph.t N (phi_dependency_edge N E) * Map.t N (list (phi_dependency_edge N E)) *
      list (audit_memory_index_event N (list (phi_dependency_edge N E)) CN
        (audit_phi_dependency_row_event N E CN)) :=
  let '(rows, events) := audit_phi_dependency_rows_counted node_enc mg inputs in
  ({| Graph.entries := memory_phis mg; Graph.nodes := memory_phis mg;
      Graph.out := index_edges EN rows; Graph.source := dependency_source;
      Graph.target := dependency_target |}, rows, events).

Fixpoint audit_phi_dependency_row_work {N E CN}
    (node_work : list CN -> nat)
    (events : list (audit_phi_dependency_row_event N E CN)) : nat :=
  match events with
  | [] => 0
  | AuditPhiDependencyRowGet _ _ calls :: rest => audit_map_source_work node_work calls +
      audit_phi_dependency_row_work node_work rest
  | AuditPhiDependencyRowCase _ :: rest => 2 + audit_phi_dependency_row_work node_work rest
  | AuditPhiDependencyEdgeKeep _ _ _ :: rest => 2 + audit_phi_dependency_row_work node_work rest
  end.

Definition audit_phi_dependency_rows_work {N E CN}
    (node_work : list CN -> nat)
    (events : list (audit_memory_index_event N (list (phi_dependency_edge N E)) CN
      (audit_phi_dependency_row_event N E CN))) : nat :=
  audit_memory_index_work node_work (audit_phi_dependency_row_work node_work) events.

Inductive audit_phi_cycle_event (N E CN : Type) : Type :=
  | AuditPhiCycleComponent (component : list N) (cyclic : bool)
  | AuditPhiCycleSuccessors (node : N) (edges : option (list (phi_dependency_edge N E)))
      (calls : list (audit_map_event N (list (phi_dependency_edge N E)) CN))
  | AuditPhiCycleEdgeCase (remaining : list (phi_dependency_edge N E))
  | AuditPhiCycleTarget (edge : phi_dependency_edge N E) (target : N)
  | AuditPhiCycleEncode (node : N) (code : positive) (body : list CN)
  | AuditPhiCycleCompare (node : N) (target : N) (result : bool)
      (calls : list audit_positive_eqb_event)
  | AuditPhiCycleMark (node : N) (calls : list (audit_set_event N CN)).
Arguments AuditPhiCycleComponent {N E CN} _ _.
Arguments AuditPhiCycleSuccessors {N E CN} _ _ _.
Arguments AuditPhiCycleEdgeCase {N E CN} _.
Arguments AuditPhiCycleTarget {N E CN} _ _.
Arguments AuditPhiCycleEncode {N E CN} _ _ _.
Arguments AuditPhiCycleCompare {N E CN} _ _ _ _.
Arguments AuditPhiCycleMark {N E CN} _ _.

Fixpoint audit_phi_cycle_self_edges {N E CN} (node_enc : N -> positive * list CN)
    (dep : Graph.t N (phi_dependency_edge N E)) (node : N)
    (edges : list (phi_dependency_edge N E)) : bool * list (audit_phi_cycle_event N E CN) :=
  match edges with
  | [] => (false, [AuditPhiCycleEdgeCase edges])
  | edge :: rest =>
      let target := Graph.target dep edge in
      let '(target_code, target_body) := node_enc target in
      let '(node_code, node_body) := node_enc node in
      let '(same, compare_events) := audit_positive_eqb target_code node_code in
      let '(later, tail_events) := audit_phi_cycle_self_edges node_enc dep node rest in
      (orb same later,
        [AuditPhiCycleEdgeCase edges; AuditPhiCycleTarget edge target;
          AuditPhiCycleEncode target target_code target_body;
          AuditPhiCycleEncode node node_code node_body;
          AuditPhiCycleCompare node target same compare_events] ++ tail_events)
  end.

Definition audit_phi_component_cyclic_counted {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E))
    (prepared_dep : prepared EN dep) (component : list N)
    : bool * list (audit_phi_cycle_event N E CN) :=
  match component with
  | [] => (false, [AuditPhiCycleComponent component false])
  | [node] =>
      let '(found, calls) := audit_map_get node_enc node (out_index prepared_dep) in
      let edges :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(cyclic, cycle_events) := audit_phi_cycle_self_edges node_enc dep node edges in
      (cyclic, [AuditPhiCycleComponent component cyclic;
        AuditPhiCycleSuccessors node found calls] ++ cycle_events)
  | _ :: _ :: _ => (true, [AuditPhiCycleComponent component true])
  end.

Fixpoint audit_phi_cycle_mark_nodes {N E CN} (node_enc : N -> positive * list CN)
    (nodes : list N) (marked : FinSet.t N)
    : FinSet.t N * list (audit_phi_cycle_event N E CN) :=
  match nodes with
  | [] => (marked, [])
  | node :: rest =>
      let '(next, calls) := audit_finset_add node_enc node marked in
      let '(final, tail) := audit_phi_cycle_mark_nodes node_enc rest next in
      (final, AuditPhiCycleMark node calls :: tail)
  end.

Fixpoint audit_phi_cycle_flags_from {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E))
    (prepared_dep : prepared EN dep) (components : list (list N)) (marked : FinSet.t N)
    : FinSet.t N * list (audit_phi_cycle_event N E CN) :=
  match components with
  | [] => (marked, [])
  | component :: rest =>
      let '(cyclic, cycle_events) := audit_phi_component_cyclic_counted EN node_enc dep
        prepared_dep component in
      let '(next, mark_events) := if cyclic then audit_phi_cycle_mark_nodes node_enc component
        marked
        else (marked, []) in
      let '(final, tail) := audit_phi_cycle_flags_from EN node_enc dep prepared_dep rest next in
      (final, cycle_events ++ mark_events ++ tail)
  end.

Definition audit_phi_cycle_flags_counted {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E))
    (prepared_dep : prepared EN dep) (result : scc_result N)
    : FinSet.t N * list (audit_phi_cycle_event N E CN) :=
  audit_phi_cycle_flags_from EN node_enc dep prepared_dep (components result) FinSet.empty.

Fixpoint audit_phi_cycle_source_work {N E CN} (node_work : list CN -> nat)
    (events : list (audit_phi_cycle_event N E CN)) : nat :=
  match events with
  | [] => 0
  | AuditPhiCycleComponent _ _ :: rest => 2 + audit_phi_cycle_source_work node_work rest
  | AuditPhiCycleSuccessors _ _ calls :: rest => 2 + audit_map_source_work node_work calls +
    audit_phi_cycle_source_work node_work rest
  | AuditPhiCycleEdgeCase _ :: rest => 2 + audit_phi_cycle_source_work node_work rest
  | AuditPhiCycleTarget _ _ :: rest => 2 + audit_phi_cycle_source_work node_work rest
  | AuditPhiCycleEncode _ _ body :: rest => 2 + node_work body + audit_phi_cycle_source_work
    node_work rest
  | AuditPhiCycleCompare _ _ _ calls :: rest => 2 + audit_positive_eqb_source_work calls +
    audit_phi_cycle_source_work node_work rest
  | AuditPhiCycleMark _ calls :: rest => 2 + audit_finset_source_work node_work calls +
    audit_phi_cycle_source_work node_work rest
  end.

(** Matching node codes recover the cycle flags computed from the prepared components. *)
Definition audit_phi_cycle_flags_erases_statement : Prop :=
  forall N E CN (EN : encoding N) (node_enc : N -> positive * list CN)
    (dep : Graph.t N (phi_dependency_edge N E)) (prepared_dep : prepared EN dep) result,
    (forall n, fst (node_enc n) = encode EN n) ->
    fst (audit_phi_cycle_flags_counted EN node_enc dep prepared_dep result) =
      phi_cycle_flags EN dep prepared_dep result.

(** Matching encoders recover the producer output built from the same representative map. *)
Definition audit_phi_output_counted_erases_statement : Prop :=
  forall N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (old : memory_graph N E) reps,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    fst (audit_phi_producer_output_counted EN EE node_enc version_enc old reps) =
      audit_phi_producer_output EN EE old reps.

Record audit_phi_producer_run {N E T CN CE PE OE CV}
    (EN : encoding N) : Type := AuditPhiProducerRun {
  audit_phi_run_index : phi_dependency_index (E := E) EN;
  audit_phi_run_order : list N;
  audit_phi_run_representatives : Map.t (memory_version N E) (memory_version N E);
  audit_phi_run_output : memory_graph N E;
  audit_phi_run_output_events : list (audit_phi_output_event N E CN CV);
  audit_phi_run_rows : list (audit_phi_row_event N E CN CE PE OE);
  audit_phi_run_dependency_rows : list
    (audit_memory_index_event N (list (phi_dependency_edge N E)) CN
      (audit_phi_dependency_row_event N E CN));
  audit_phi_run_preparation : list (@audit_phi_prepare_event N E T EN);
  audit_phi_run_graph_preparation :
    list (audit_prepare_source_event N (phi_dependency_edge N E)
      (audit_phi_graph_callback_event N E CN));
  audit_phi_run_scc_events :
    list (audit_tarjan_nested_event N (phi_dependency_edge N E)
      (audit_graph_callback_capture N (phi_dependency_edge N E)
        (audit_phi_graph_callback_event N E CN)));
  audit_phi_run_cycle_events : list (audit_phi_cycle_event N E CN);
  audit_phi_run_resolution : list (audit_phi_resolve_event N E CN CV)
}.
Arguments AuditPhiProducerRun {N E T CN CE PE OE CV EN}.

(** Source call adapters are inputs, and their captured traces remain attached to
    the run. SCC nodes are resolved in the exact concatenated component order. *)
Definition audit_phi_produce {N E T CN CE PE OE CV}
    (EN : encoding N) (EE : encoding E) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (version_enc : memory_version N E -> positive * list CV)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    : audit_phi_producer_run EN :=
  let '(inputs, row_events) := audit_phi_input_rows node_enc edge_enc pred operand
    (memory_phis mg) in
  let '(dep, dependency_rows, dependency_events) := audit_phi_dependency_graph_counted EN node_enc
    mg inputs in
  let '(prep, graph_prep_events) := audit_prepare_source_counted EN dep
    (audit_phi_prepare_callbacks node_enc dependency_rows dep) in
  let '(component_result, scc_events) := audit_scc_source_counted prep
    (audit_phi_scc_callbacks node_enc dep) (Graph.nodes dep) in
  let '(cycles, cycle_events) := audit_phi_cycle_flags_counted EN node_enc dep prep
    component_result in
  let index := PhiDependencyIndex inputs dep prep component_result cycles in
  let order := concat (components component_result) in
  let '(representatives, resolution_events) :=
    audit_phi_resolve_all EN node_enc version_enc index order Map.empty in
  let preparation_events :=
    [AuditPhiInputs g effects mg inputs; AuditPhiGraph inputs dep;
     AuditPhiPrepared dep prep; AuditPhiScc component_result; AuditPhiCycles cycles] in
  let '(output, output_events) := audit_phi_producer_output_counted EN EE node_enc version_enc
    mg representatives in
  AuditPhiProducerRun index order representatives output output_events row_events
    dependency_events preparation_events graph_prep_events scc_events cycle_events
      resolution_events.

(** Matching node and version encoders make the producer representatives follow the recorded
    resolution trace. *)
Definition audit_phi_producer_resolution_statement : Prop :=
  forall N E T CN CE PE OE CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (version_enc : memory_version N E -> positive * list CV)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    let run := audit_phi_produce EN EE node_enc edge_enc pred operand version_enc g effects mg in
    phi_resolve_trace EN EE (audit_phi_run_index EN run) (audit_phi_run_order EN run) Map.empty
      (audit_phi_run_representatives EN run).

(** Matching encoders, predecessor and operand callbacks make the producer index agree with the
    dependency graph, preparation, SCCs and cycle flags. *)
Definition audit_phi_producer_index_source_statement : Prop :=
  forall N E T CN CE PE OE CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (version_enc : memory_version N E -> positive * list CV)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (pred n) = pred_edges (prepare EN g) n) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    let run := audit_phi_produce EN EE node_enc edge_enc pred operand version_enc g effects mg in
    phi_index_graph (audit_phi_run_index EN run) = phi_dependency_graph_from_inputs EN mg
      (phi_input_rows EN EE g effects mg) /\
    phi_index_prepared (audit_phi_run_index EN run) =
      prepare EN (phi_index_graph (audit_phi_run_index EN run)) /\
    phi_index_scc (audit_phi_run_index EN run) =
      scc (phi_index_prepared (audit_phi_run_index EN run)) /\
    phi_index_cycles (audit_phi_run_index EN run) =
      phi_cycle_flags EN (phi_index_graph (audit_phi_run_index EN run))
        (phi_index_prepared (audit_phi_run_index EN run))
        (phi_index_scc (audit_phi_run_index EN run)).

(** The producer output filters retained phis and rewrites each memory field. *)
Definition audit_phi_producer_output_shape_statement : Prop :=
  forall N E (EN : encoding N) (EE : encoding E) old reps,
    let output := audit_phi_producer_output EN EE old reps in
    let rep := audit_phi_producer_rep EN EE reps in
    let kept := filter (fun n =>
      Pos.eqb (encode (memory_version_encoding EN EE) (MemoryPhi n))
        (encode (memory_version_encoding EN EE) (rep (MemoryPhi n)))) (memory_phis old) in
    memory_phis output = filter (fun n => FinSet.mem EN n (FinSet.of_list EN kept))
      (memory_phis old) /\
    memory_versions output = filter (fun v =>
      match v with
      | MemoryPhi n => FinSet.mem EN n (FinSet.of_list EN (memory_phis output))
      | _ => true
      end) (memory_versions old) /\
    (forall n, memory_in output n = rep (memory_in old n)) /\
    (forall e, memory_out output e = rep (memory_out old e)) /\
    (forall e i, memory_before output e i = option_map rep (memory_before old e i)) /\
    (forall n key, memory_operand output n key = option_map rep (memory_operand old n key)).

(** Input-derived outer blocks charge every node row and every actual resolution
    row; internal calls retain their captured child traces in the family costs. *)
Definition audit_phi_producer_work {N E T CN CE PE OE CV}
    (node_work : list CN -> nat) (edge_work : list CE -> nat)
    (pred_work : list PE -> nat) (operand_work : list OE -> nat)
    (version_work : list CV -> nat)
    (EN : encoding N) (run : @audit_phi_producer_run N E T CN CE PE OE CV EN) : nat :=
  audit_phi_rows_source_work node_work edge_work pred_work operand_work
    (audit_phi_run_rows EN run) +
  audit_phi_dependency_rows_work node_work (audit_phi_run_dependency_rows EN run) +
  5 + 5 + 6 + (* dependency graph, dependency index, returned memory graph records *)
  3 + length (audit_phi_run_order EN run) +
    length (components (phi_index_scc (audit_phi_run_index EN run))) +
    fold_right (fun component total => length component + total) 0
      (components (phi_index_scc (audit_phi_run_index EN run))) +
  audit_prepare_source_work (audit_phi_graph_callback_work node_work)
    (audit_phi_run_graph_preparation EN run) +
  audit_scc_source_work (audit_phi_graph_callback_work node_work)
    (audit_phi_run_scc_events EN run) +
  audit_phi_cycle_source_work node_work (audit_phi_run_cycle_events EN run) +
  audit_phi_resolve_source_work node_work version_work (audit_phi_run_resolution EN run) +
  audit_phi_output_source_work node_work version_work (audit_phi_run_output_events EN run).

(** The counted producer records five preparation phases. *)
Definition audit_phi_producer_phase_counts_statement : Prop :=
  forall N E T CN CE PE OE CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (version_enc : memory_version N E -> positive * list CV)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    length (audit_phi_run_preparation EN
      (audit_phi_produce EN EE node_enc edge_enc pred operand version_enc g effects mg)) = 5.

Example audit_phi_singleton_cycle_scans_later_edge :
  let edges := [PhiDependencyEdgeData 1%positive (@None positive) 1%positive;
    PhiDependencyEdgeData 1%positive None 2%positive] in
  let dep := {| Graph.entries := [1%positive]; Graph.nodes := [1%positive];
    Graph.out := fun _ => edges; Graph.source := dependency_source;
    Graph.target := dependency_target |} in
  let run := audit_phi_cycle_self_edges audit_positive_encode dep 1%positive edges in
  fst run = true /\ length (snd run) = 11.
Proof.
  vm_compute.
  split; reflexivity.
Qed.
