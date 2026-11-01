(** * Whole memory-phi operand budgets

    These recurrences follow actual rows, dependency components and persistent representatives.
    For example, a false operand comparison still pays every remaining strict operand comparison.
    Builds on: full graph source models and the concrete memory-phi producer phases. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase GraphAuditDfs
  GraphAuditScc.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditEncoding CollectionsAuditEncoderBudget.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget
  AnalysesAuditMemorySharedBudget AnalysesAuditMemoryPhiRows AnalysesAuditMemoryPhiResolve
  AnalysesAuditMemoryPhiProducer.
Import List.ListNotations.

Definition audit_phi_get_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) : nat := 5 + budget key + 5 * Pos.size_nat (fst (enc key)).

Definition audit_phi_set_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) : nat := 2 + budget key + 16 * Pos.size_nat (fst (enc key)).

Fixpoint audit_phi_operand_input_budget {N E} (budget : N -> option E -> nat)
    (node : N) (keys : list (option E)) : nat :=
  match keys with
  | [] => 0
  | key :: rest => 2 + budget node key + audit_phi_operand_input_budget budget node rest
  end.

Fixpoint audit_phi_rows_input_budget {N E CN CE PE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE) (node_budget : N -> nat) (edge_budget : E -> nat)
    (pred_budget : N -> nat) (operand_budget : N -> option E -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 1
  | n :: rest =>
      let edges := fst (pred n) in
      let keys := None :: map Some edges in
      let distinct := fst (audit_phi_distinct_from (audit_option_encode edge_enc) FinSet.empty
        keys) in
      2 + length edges + pred_budget n +
      2 + audit_memory_distinct_input_budget (audit_option_encode edge_enc)
        (audit_option_input_budget edge_budget) keys +
      audit_phi_operand_input_budget operand_budget n distinct +
      2 + audit_phi_set_input_budget node_enc node_budget n +
      audit_phi_rows_input_budget node_enc edge_enc pred node_budget edge_budget
        pred_budget operand_budget rest
  end.

Definition audit_phi_dependency_row_input_budget {N E CN}
    (node_enc : N -> positive * list CN) (node_budget : N -> nat)
    (inputs : Map.t N (list (option E * memory_version N E))) (node : N) : nat :=
  let row :=
    match fst (audit_map_get node_enc node inputs) with
    | Some xs => xs
    | None => []
    end in
  audit_phi_get_input_budget node_enc node_budget node + 2 + 4 * length row.

Fixpoint audit_phi_self_edges_input_budget {N E CN}
    (node_enc : N -> positive * list CN) (node_budget : N -> nat)
    (dep : Graph.t N (phi_dependency_edge N E)) (node : N)
    (edges : list (phi_dependency_edge N E)) : nat :=
  match edges with
  | [] => 2
  | edge :: rest =>
      let target := Graph.target dep edge in
      10 + node_budget target + node_budget node +
      2 * Nat.min (Pos.size_nat (fst (node_enc target))) (Pos.size_nat (fst (node_enc node))) +
      audit_phi_self_edges_input_budget node_enc node_budget dep node rest
  end.

Fixpoint audit_phi_mark_input_budget {N CN} (node_enc : N -> positive * list CN)
    (node_budget : N -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | node :: rest => 2 + audit_phi_set_input_budget node_enc node_budget node +
      audit_phi_mark_input_budget node_enc node_budget rest
  end.

Definition audit_phi_component_input_budget {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (node_budget : N -> nat)
    (dep : Graph.t N (phi_dependency_edge N E)) (prepared : prepared EN dep)
    (component : list N) : nat :=
  match component with
  | [] => 2
  | [node] =>
      let edges :=
        match fst (audit_map_get node_enc node (out_index prepared)) with
        | Some xs => xs
        | None => []
        end in
      4 + audit_phi_get_input_budget node_enc node_budget node +
      audit_phi_self_edges_input_budget node_enc node_budget dep node edges
  | _ :: _ :: _ => 2
  end.

Fixpoint audit_phi_cycles_input_budget {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (node_budget : N -> nat)
    (dep : Graph.t N (phi_dependency_edge N E)) (prepared : prepared EN dep)
    (components : list (list N)) : nat :=
  match components with
  | [] => 0
  | component :: rest =>
      audit_phi_component_input_budget EN node_enc node_budget dep prepared component +
      (if fst (audit_phi_component_cyclic_counted EN node_enc dep prepared component)
       then audit_phi_mark_input_budget node_enc node_budget component else 0) +
      audit_phi_cycles_input_budget EN node_enc node_budget dep prepared rest
  end.

Definition audit_phi_rep_input_budget {N E CV}
    (enc : memory_version N E -> positive * list CV)
    (budget : memory_version N E -> nat) (v : memory_version N E) : nat :=
  2 + audit_phi_get_input_budget enc budget v.

Definition audit_phi_compare_input_budget {N E CV}
    (enc : memory_version N E -> positive * list CV)
    (budget : memory_version N E -> nat) (left right : memory_version N E) : nat :=
  6 + budget left + budget right +
    2 * Nat.min (Pos.size_nat (fst (enc left))) (Pos.size_nat (fst (enc right))).

Fixpoint audit_phi_all_same_input_budget {N E CV}
    (enc : memory_version N E -> positive * list CV) (budget : memory_version N E -> nat)
    (reps : Map.t (memory_version N E) (memory_version N E))
    (candidate : memory_version N E) (row : list (option E * memory_version N E)) : nat :=
  match row with
  | [] => 2
  | (_, v) :: rest =>
      let representative := fst (@audit_phi_rep N E unit CV enc reps v) in
      2 + audit_phi_rep_input_budget enc budget v +
      audit_phi_compare_input_budget enc budget candidate representative +
      audit_phi_all_same_input_budget enc budget reps candidate rest
  end.

Definition audit_phi_resolve_step_input_budget {N E CN CV} (EN : encoding N)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (node_budget : N -> nat) (version_budget : memory_version N E -> nat)
    (index : phi_dependency_index (E := E) EN)
    (reps : Map.t (memory_version N E) (memory_version N E)) (node : N) : nat :=
  8 + node_budget node + 5 * Pos.size_nat (fst (node_enc node)) +
  if fst (audit_finset_mem node_enc node (phi_index_cycles index)) then 0 else
    2 + audit_phi_get_input_budget node_enc node_budget node +
    match fst (audit_map_get node_enc node (phi_index_inputs index)) with
    | None | Some [] => 0
    | Some ((_, v) :: rest) =>
        let candidate := fst (@audit_phi_rep N E CN CV version_enc reps v) in
        let self := fst (@audit_phi_compare N E CN CV version_enc candidate (MemoryPhi node)) in
        let all_same := fst (@audit_phi_all_same N E CN CV version_enc reps candidate rest) in
        audit_phi_rep_input_budget version_enc version_budget v +
        audit_phi_compare_input_budget version_enc version_budget candidate (MemoryPhi node) +
        audit_phi_all_same_input_budget version_enc version_budget reps candidate rest +
        if andb (negb self) all_same then
          2 + audit_phi_set_input_budget version_enc version_budget (MemoryPhi node)
        else 0
    end.

Fixpoint audit_phi_resolve_pass_input_budget {N E CN CV} (EN : encoding N)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (node_budget : N -> nat) (version_budget : memory_version N E -> nat)
    (index : phi_dependency_index (E := E) EN) (nodes : list N)
    (reps : Map.t (memory_version N E) (memory_version N E)) : nat :=
  match nodes with
  | [] => 0
  | node :: rest =>
      let next := fst (audit_phi_resolve_step EN node_enc version_enc index reps node) in
      audit_phi_resolve_step_input_budget EN node_enc version_enc node_budget version_budget
        index reps node +
      audit_phi_resolve_pass_input_budget EN node_enc version_enc node_budget version_budget
        index rest next
  end.

Fixpoint audit_phi_output_keep_input_budget {N E CV}
    (version_enc : memory_version N E -> positive * list CV)
    (version_budget : memory_version N E -> nat)
    (reps : Map.t (memory_version N E) (memory_version N E)) (nodes : list N) : nat :=
  match nodes with
  | [] => 2
  | n :: rest =>
      let v := MemoryPhi n in
      let representative :=
        match fst (audit_map_get version_enc v reps) with
        | Some r => r
        | None => v
        end in
      8 + audit_phi_get_input_budget version_enc version_budget v +
      version_budget v + version_budget representative +
      2 * Nat.min (Pos.size_nat (fst (version_enc v)))
        (Pos.size_nat (fst (version_enc representative))) +
      audit_phi_output_keep_input_budget version_enc version_budget reps rest
  end.

Fixpoint audit_phi_filter_nodes_input_budget {N CN} (node_enc : N -> positive * list CN)
    (node_budget : N -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 2
  | node :: rest => 8 + node_budget node + 5 * Pos.size_nat (fst (node_enc node)) +
      audit_phi_filter_nodes_input_budget node_enc node_budget rest
  end.

Fixpoint audit_phi_filter_versions_input_budget {N E CN}
    (node_enc : N -> positive * list CN) (node_budget : N -> nat)
    (versions : list (memory_version N E)) : nat :=
  match versions with
  | [] => 2
  | version :: rest =>
      2 + (
      match version with
      | MemoryPhi node => 8 + node_budget node + 5 * Pos.size_nat (fst (node_enc node))
      | _ => 0
      end) + audit_phi_filter_versions_input_budget node_enc node_budget rest
  end.

Definition audit_phi_output_input_budget {N E CN CV} (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (node_budget : N -> nat) (version_budget : memory_version N E -> nat)
    (old : memory_graph N E) (reps : Map.t (memory_version N E) (memory_version N E)) : nat :=
  let kept := fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis old)) in
  audit_phi_output_keep_input_budget version_enc version_budget reps (memory_phis old) +
  2 + audit_memory_distinct_input_budget node_enc node_budget kept +
  audit_phi_filter_nodes_input_budget node_enc node_budget (memory_phis old) +
  audit_phi_filter_versions_input_budget node_enc node_budget (memory_versions old).

Fixpoint audit_phi_graph_targets_input_budget {N E}
    (node_budget : N -> nat) (edges : list (phi_dependency_edge N E)) : nat :=
  match edges with
  | [] => 0
  | edge :: rest => node_budget (dependency_target edge) +
      audit_phi_graph_targets_input_budget node_budget rest
  end.

Fixpoint audit_phi_graph_callback_envelope {N E CN}
    (node_enc : N -> positive * list CN) (node_budget : N -> nat)
    (dep : Graph.t N (phi_dependency_edge N E)) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | n :: rest => node_budget n + audit_phi_get_input_budget node_enc node_budget n +
      audit_phi_graph_targets_input_budget node_budget (Graph.out dep n) +
      audit_phi_graph_callback_envelope node_enc node_budget dep rest
  end.

Definition audit_phi_producer_input_budget {N E T CN CE PE OE}
    (EN : encoding N) (EE : encoding E) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (node_budget : N -> nat) (edge_budget : E -> nat)
    (pred_budget : N -> nat) (operand_budget : N -> option E -> nat)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E) : nat :=
  let version_enc := audit_memory_version_encode node_enc edge_enc in
  let version_budget := audit_memory_version_input_budget node_enc edge_enc node_budget
    edge_budget in
  let inputs := fst (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg)) in
  let '(dep, rows, _) := audit_phi_dependency_graph_counted EN node_enc mg inputs in
  let cb := audit_phi_prepare_callbacks node_enc rows dep in
  let prep := fst (audit_prepare_source_counted EN dep cb) in
  let components := fst (audit_scc_source_counted prep (audit_phi_scc_callbacks node_enc dep)
    (Graph.nodes dep)) in
  let cycles := fst (audit_phi_cycle_flags_counted EN node_enc dep prep components) in
  let index := PhiDependencyIndex inputs dep prep components cycles in
  let order := concat (GraphScc.components components) in
  let reps := fst (audit_phi_resolve_all EN node_enc version_enc index order Map.empty) in
  let envelope := audit_phi_graph_callback_envelope node_enc node_budget dep (Graph.nodes dep) in
  audit_phi_rows_input_budget node_enc edge_enc pred node_budget edge_budget pred_budget
    operand_budget
    (memory_phis mg) +
  audit_memory_index_input_budget node_enc node_budget
    (audit_phi_dependency_row_input_budget node_enc node_budget inputs) (memory_phis mg) +
  19 + length order + length (GraphScc.components components) +
  fold_right (fun component total => length component + total) 0 (GraphScc.components components) +
  audit_prepare_source_budget EN dep + audit_graph_prepare_full_event_bound dep * envelope +
  audit_scc_source_budget EN dep prep (Graph.nodes dep) +
    2 * audit_tarjan_input_event_bound prep (Graph.nodes dep) * envelope +
  audit_phi_cycles_input_budget EN node_enc node_budget dep prep (GraphScc.components components) +
  audit_phi_resolve_pass_input_budget EN node_enc version_enc node_budget version_budget
    index order Map.empty +
  audit_phi_output_input_budget EN EE node_enc version_enc node_budget version_budget mg reps.

(** Matching node codes and callback budgets bound the producer's concrete source work. *)
Definition audit_phi_producer_whole_input_bound_statement : Prop :=
  forall N E T CN CE PE OE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (pred : N -> list E * list PE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      node_work edge_work pred_work operand_work node_budget edge_budget pred_budget operand_budget
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall n, pred_work (snd (pred n)) <= pred_budget n) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    audit_phi_producer_work node_work edge_work pred_work operand_work
      (audit_memory_version_work node_work edge_work) EN
      (audit_phi_produce EN EE node_enc edge_enc pred operand
        (audit_memory_version_encode node_enc edge_enc) g effects mg) <=
    audit_phi_producer_input_budget EN EE node_enc edge_enc pred operand
      node_budget edge_budget pred_budget operand_budget g effects mg.
