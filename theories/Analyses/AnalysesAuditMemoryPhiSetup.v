(** * Input preparation and concrete phi predecessor reads

    The complete counted prune prepares the input graph once before any phi input row query.
    For example, each predecessor callback performs one read in that same prepared incoming map.
    Builds on: full graph preparation, concrete map reads and the full phi producer. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryPhiProducer
  AnalysesAuditMemoryPhiInputBudget AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiState.
Import List.ListNotations.

Inductive audit_phi_input_graph_body (CN OE TE : Type) : Type :=
  | AuditPhiInputNodeBody (events : list CN)
  | AuditPhiInputOutBody (events : list OE)
  | AuditPhiInputTargetBody (events : list TE).
Arguments AuditPhiInputNodeBody {CN OE TE} _.
Arguments AuditPhiInputOutBody {CN OE TE} _.
Arguments AuditPhiInputTargetBody {CN OE TE} _.

Definition audit_phi_input_graph_body_work {CN OE TE} (node_work : list CN -> nat)
    (out_work : list OE -> nat) (target_work : list TE -> nat)
    (body : audit_phi_input_graph_body CN OE TE) : nat :=
  match body with
  | AuditPhiInputNodeBody events => node_work events
  | AuditPhiInputOutBody events => out_work events
  | AuditPhiInputTargetBody events => target_work events
  end.

Definition audit_phi_input_graph_callbacks {N E CN OE TE}
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) :
    audit_prepare_callback_model N E (audit_phi_input_graph_body CN OE TE) :=
  @AuditPrepareCallbackModel N E (audit_phi_input_graph_body CN OE TE)
    (fun n => let '(edges, body) := out n in (edges, [AuditPhiInputOutBody body]))
    (fun e => let '(n, body) := target e in (n, [AuditPhiInputTargetBody body]))
    (fun n => let '(code, body) := node_enc n in (code, [AuditPhiInputNodeBody body])).

Definition audit_phi_predecessors_counted {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (g : Graph.t N E) (base : prepared EN g) (node : N) :=
  let '(found, events) := audit_map_get node_enc node (in_index base) in
  (
    match found with
    | Some edges => edges
    | None => []
    end, events).

Definition audit_memory_phi_prune_counted {N E T CN CE OE TE PE}
    (EN : encoding N) (EE : encoding E) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (target : E -> N * list TE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :=
  let '(base, preparation) := audit_prepare_source_counted EN g
    (audit_phi_input_graph_callbacks node_enc out target) in
  let run := audit_phi_produce EN EE node_enc edge_enc
    (audit_phi_predecessors_counted EN node_enc g base) operand
    (audit_memory_version_encode node_enc edge_enc) g effects mg in
  (base, preparation, run).

Fixpoint audit_phi_input_targets_envelope {N E TE} (target : E -> N * list TE)
    (node_budget : N -> nat) (target_budget : E -> nat) (edges : list E) : nat :=
  match edges with
  | [] => 0
  | e :: rest => target_budget e + node_budget (fst (target e)) +
      audit_phi_input_targets_envelope target node_budget target_budget rest
  end.

Fixpoint audit_phi_input_graph_envelope {N E OE TE}
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (node_budget out_budget : N -> nat) (target_budget : E -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | n :: rest => node_budget n + out_budget n +
      audit_phi_input_targets_envelope target node_budget target_budget (fst (out n)) +
      audit_phi_input_graph_envelope out target node_budget out_budget target_budget rest
  end.

(** Matching node, outgoing and target callbacks and callback budgets bound setup and phi
    producer work. *)
Definition audit_memory_phi_prune_whole_input_bound_statement : Prop :=
  forall N E T CN CE OE TE PE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      node_work edge_work out_work target_work operand_work
      node_budget edge_budget out_budget target_budget operand_budget
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    let '(base, preparation, run) := audit_memory_phi_prune_counted EN EE node_enc edge_enc
      out target operand g effects mg in
    audit_prepare_source_work (audit_phi_input_graph_body_work node_work out_work target_work)
      preparation +
    audit_phi_producer_work node_work edge_work (audit_map_source_work node_work) operand_work
      (audit_memory_version_work node_work edge_work) EN run <=
    audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
      audit_phi_input_graph_envelope out target node_budget out_budget target_budget (Graph.nodes
        g) +
    audit_phi_producer_input_budget EN EE node_enc edge_enc
      (audit_phi_predecessors_counted EN node_enc g base) operand node_budget edge_budget
      (audit_phi_get_input_budget node_enc node_budget) operand_budget g effects mg.

(** Matching encoders and graph and operand callbacks yield the original preparation, pruning
    graph and representative table. *)
Definition audit_memory_phi_prune_counted_erases_statement : Prop :=
  forall N E T CN CE OE TE PE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    let '(base, _, run) := audit_memory_phi_prune_counted EN EE node_enc edge_enc out target operand
      g effects mg in
    base = prepare EN g /\
    let original := audit_memory_phi_prune N E T EN EE g effects mg in
    audit_phi_run_output EN run = phi_graph original /\
    audit_phi_run_representatives EN run = phi_representatives original.
