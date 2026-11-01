(** * Liveness fact extraction source

    Fact extraction visits original graph occurrences and encodes every tuple argument.
    For example, repeated edge occurrences yield repeated use and successor facts.
    Builds on: liveness views and the sparse source callback dictionary. *)
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Rules Require Import RulesSyntax.
From Galois.Analyses Require Import AnalysesLiveness AnalysesRules AnalysesAuditSsaSparse.
Import List.ListNotations.

(** * Liveness fact extraction source *)

Inductive audit_live_fact_event (N E V B : Type) : Type :=
  | LiveFactCase : nat -> audit_live_fact_event N E V B
  | LiveFactList : nat -> audit_live_fact_event N E V B
  | LiveFactOut : N -> list E -> list B -> audit_live_fact_event N E V B
  | LiveFactTarget : E -> N -> list B -> audit_live_fact_event N E V B
  | LiveFactUse : E -> list V -> list B -> audit_live_fact_event N E V B
  | LiveFactDef : E -> list V -> list B -> audit_live_fact_event N E V B
  | LiveFactExit : N -> list V -> list B -> audit_live_fact_event N E V B
  | LiveFactNode : N -> positive -> list B -> audit_live_fact_event N E V B
  | LiveFactEdge : E -> positive -> list B -> audit_live_fact_event N E V B
  | LiveFactValue : V -> positive -> list B -> audit_live_fact_event N E V B.

Arguments LiveFactCase {N E V B} _.

Arguments LiveFactList {N E V B} _.

Arguments LiveFactOut {N E V B} _ _ _.

Arguments LiveFactTarget {N E V B} _ _ _.

Arguments LiveFactUse {N E V B} _ _ _.

Arguments LiveFactDef {N E V B} _ _ _.

Arguments LiveFactExit {N E V B} _ _ _.

Arguments LiveFactNode {N E V B} _ _ _.

Arguments LiveFactEdge {N E V B} _ _ _.

Arguments LiveFactValue {N E V B} _ _ _.

Fixpoint audit_live_fact_edges {N E V B} (cb : audit_live_sparse_callbacks N E V B) (nodes : list N)
    : list E * list (audit_live_fact_event N E V B) :=
  match nodes with
  | [] => ([], [LiveFactCase 0])
  | n :: rest => let '(edges, body) := sl_out cb n in
    let '(later, events) := audit_live_fact_edges cb rest in
    (edges ++ later, LiveFactOut n edges body :: events ++ [LiveFactList (length edges)])
  end.

Fixpoint audit_live_fact_edge_values {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (tag : pred) (e : E) (values : list V)
    : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  match values with
  | [] => ([], [LiveFactCase 1])
  | x :: rest =>
    let '(ec, eb) := sl_edge_encode cb e in let '(xc, xb) := sl_value_encode cb x in
    let '(later, events) := audit_live_fact_edge_values cb tag e rest in
    ((tag, [ec; xc]) :: later, LiveFactEdge e ec eb :: LiveFactValue x xc xb :: events)
  end.

Fixpoint audit_live_fact_rows {N E V B} (cb : audit_live_sparse_callbacks N E V B) (edges : list E)
    : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  match edges with
  | [] => ([], [LiveFactCase 2])
  | e :: rest =>
    let '(uses, ub) := sl_use cb e in
    let '(use_rows, ue) := audit_live_fact_edge_values cb PUse e uses in
    let '(defs, db) := sl_def cb e in
    let '(def_rows, de) := audit_live_fact_edge_values cb PDef e defs in
    let '(later, events) := audit_live_fact_rows cb rest in
    (use_rows ++ def_rows ++ later, LiveFactUse e uses ub :: ue ++ LiveFactDef e defs db :: de ++
      [LiveFactList (length use_rows)] ++ events ++ [LiveFactList (length use_rows + length
        def_rows)])
  end.

Fixpoint audit_live_fact_succ_edges {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (n : N) (edges : list E) : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  match edges with
  | [] => ([], [LiveFactCase 3])
  | e :: rest =>
    let '(target, tb) := sl_target cb e in
    let '(nc, nb) := sl_node_encode cb n in let '(ec, eb) := sl_edge_encode cb e in
    let '(tc, tcb) := sl_node_encode cb target in
    let '(later, events) := audit_live_fact_succ_edges cb n rest in
    ((PSucc, [nc; ec; tc]) :: later,
      LiveFactTarget e target tb :: LiveFactNode n nc nb :: LiveFactEdge e ec eb ::
      LiveFactNode target tc tcb :: events)
  end.

Fixpoint audit_live_fact_succ_nodes {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (nodes : list N)
    : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  match nodes with
  | [] => ([], [LiveFactCase 4])
  | n :: rest => let '(edges, body) := sl_out cb n in
    let '(here, calls) := audit_live_fact_succ_edges cb n edges in
    let '(later, events) := audit_live_fact_succ_nodes cb rest in
    (here ++ later, LiveFactOut n edges body :: calls ++ events ++ [LiveFactList (length here)])
  end.

Fixpoint audit_live_fact_exit_values {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (n : N) (values : list V) : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  match values with
  | [] => ([], [LiveFactCase 5])
  | x :: rest => let '(nc, nb) := sl_node_encode cb n in let '(xc, xb) := sl_value_encode cb x in
    let '(later, calls) := audit_live_fact_exit_values cb n rest in
    ((PExitUse, [nc; xc]) :: later, LiveFactNode n nc nb :: LiveFactValue x xc xb :: calls)
  end.

Fixpoint audit_live_fact_exit_nodes {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (nodes : list N)
    : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  match nodes with
  | [] => ([], [LiveFactCase 6])
  | n :: rest => let '(values, body) := sl_exit cb n in
    let '(here, calls) := audit_live_fact_exit_values cb n values in
    let '(later, events) := audit_live_fact_exit_nodes cb rest in
    (here ++ later, LiveFactExit n values body :: calls ++ events ++ [LiveFactList (length here)])
  end.

Definition audit_live_facts_counted {N E V B} (g : Graph.t N E)
    (cb : audit_live_sparse_callbacks N E V B)
    : list (ground_atom pred) * list (audit_live_fact_event N E V B) :=
  let '(edges, edge_events) := audit_live_fact_edges cb (Graph.nodes g) in
  let '(operands, operand_events) := audit_live_fact_rows cb edges in
  let '(successors, succ_events) := audit_live_fact_succ_nodes cb (Graph.nodes g) in
  let '(exits, exit_events) := audit_live_fact_exit_nodes cb (Graph.nodes g) in
  (operands ++ successors ++ exits, edge_events ++ operand_events ++ succ_events ++ exit_events ++
    [LiveFactList (length successors); LiveFactList (length operands)]).

(** Source work charges all tuple frames and actual supplied callback bodies. *)
Definition audit_live_fact_event_work {N E V B} (weight : B -> nat)
    (event : audit_live_fact_event N E V B) : nat :=
  let body := fun xs => fold_right (fun item total => weight item + total) 0 xs in
  64 + match event with
  | LiveFactOut _ _ xs | LiveFactTarget _ _ xs | LiveFactUse _ _ xs |
    LiveFactDef _ _ xs | LiveFactExit _ _ xs | LiveFactNode _ _ xs |
    LiveFactEdge _ _ xs | LiveFactValue _ _ xs => body xs
  | LiveFactList size => size
  | LiveFactCase _ => 0
  end.

Definition audit_live_facts_work {N E V B} (weight : B -> nat)
    (events : list (audit_live_fact_event N E V B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event total => audit_live_fact_event_work weight event + total) 0 events.

(** Each captured input selects its supplied callback's allowance. *)
Definition audit_live_fact_event_budget {N E V B} (node_budget out_budget exit_budget : N -> nat)
    (edge_budget target_budget use_budget def_budget : E -> nat) (value_budget : V -> nat)
    (event : audit_live_fact_event N E V B) : nat :=
  match event with
  | LiveFactOut n _ _ => out_budget n
  | LiveFactExit n _ _ => exit_budget n
  | LiveFactTarget e _ _ => target_budget e
  | LiveFactUse e _ _ => use_budget e
  | LiveFactDef e _ _ => def_budget e
  | LiveFactNode n _ _ => node_budget n
  | LiveFactEdge e _ _ => edge_budget e
  | LiveFactValue x _ _ => value_budget x
  | _ => 0
  end.

(** Fact extraction agrees exactly and is bounded by original graph and occurrence inputs. *)
Definition audit_live_facts_adapted_statement : Prop :=
  forall S O N E V C B (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (vv : var_view S O N E V C) (cb : audit_live_sparse_callbacks N E V B) (weight : B -> nat)
    node_source edge_source value_source out_source target_source use_source def_source exit_source
    node_budget edge_budget value_budget out_budget target_budget use_budget def_budget exit_budget,
    audit_live_sparse_callbacks_erase EN EE EV (var_point_uses vv) cb ->
    audit_graph_external_callback_adapter (sl_node_encode cb) weight node_source node_budget ->
    audit_graph_external_callback_adapter (sl_edge_encode cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sl_value_encode cb) weight value_source value_budget ->
    audit_graph_external_callback_adapter (sl_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sl_target cb) weight target_source target_budget ->
    audit_graph_external_callback_adapter (sl_use cb) weight use_source use_budget ->
    audit_graph_external_callback_adapter (sl_def cb) weight def_source def_budget ->
    audit_graph_external_callback_adapter (sl_exit cb) weight exit_source exit_budget ->
    let '(facts, events) := audit_live_facts_counted (cfg (gview vv)) cb in
    facts = extract_live_facts EN EE EV vv /\
      audit_live_facts_work weight events <=
        (N.to_nat 65536%N) * Nat.pow (audit_live_sparse_input_scale EN EE EV (var_point_uses vv))
          16 +
        fold_right (fun event total => audit_live_fact_event_budget node_budget out_budget
          exit_budget
          edge_budget target_budget use_budget def_budget value_budget event + total) 0 events.
