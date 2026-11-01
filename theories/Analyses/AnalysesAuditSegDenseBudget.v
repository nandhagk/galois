(** * Dense SEG callback input budgets

    Budgets use original graph, callback operands and actual finite-set intermediate inputs.
    For example, a continuation is bounded over the system's actual flow constraints.
    Builds on: AnalysesAuditSegDenseCallbacks and the Fixpoint callback contracts. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditElements.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditIndex
  FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder
  AnalysesAuditSegDenseUniverse AnalysesAuditSegDenseTransfer AnalysesAuditSegDenseSystem
  AnalysesAuditSegDenseCallbacks.
Import List.ListNotations.

(** * Dense SEG callback input budgets *)

(** Each field prices one genuine external client callback at its own input. *)
Record audit_dense_client_budget (N E U : Type) : Type := AuditDenseClientBudget {
  dense_node_budget : N -> nat;
  dense_edge_budget : E -> nat;
  dense_expr_budget : U -> nat;
  dense_out_budget : N -> nat;
  dense_target_budget : E -> nat;
  dense_source_budget : E -> nat;
  dense_gen_budget : E -> nat;
  dense_kill_budget : E * U -> nat
}.

Arguments dense_node_budget {N E U} _ _.

Arguments dense_edge_budget {N E U} _ _.

Arguments dense_expr_budget {N E U} _ _.

Arguments dense_out_budget {N E U} _ _.

Arguments dense_target_budget {N E U} _ _.

Arguments dense_source_budget {N E U} _ _.

Arguments dense_gen_budget {N E U} _ _.

Arguments dense_kill_budget {N E U} _ _.

(** The external universe bound counts actual listed out, gen and expression-encoding calls. *)
Definition audit_dense_universe_external_budget {S O N E U C} (gk : genkill_view S O N E U C)
    (costs : audit_dense_client_budget N E U) : nat :=
  let g := cfg (gkview gk) in let edges := edges_of g in
  fold_right (fun n total => dense_out_budget costs n + total) 0 (Graph.nodes g) +
    fold_right (fun e total => dense_gen_budget costs e + total) 0 edges +
    fold_right (fun u total => dense_expr_budget costs u + total) 0 (flat_map (gen gk) edges).

(** A transfer pays every actual kill, generation and finite-set encoding call. *)
Definition audit_dense_transfer_external_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (costs : audit_dense_client_budget N E U)
    (edge : E) (input : FinSet.t U) : nat :=
  let items := FinSet.elements input in
  let generated := gen gk edge in
  let universe := expr_universe EU gk in
  audit_dense_universe_external_budget gk costs + dense_gen_budget costs edge +
    fold_right (fun u n => dense_kill_budget costs (edge, u) + n) 0 items +
    fold_right (fun u n => dense_expr_budget costs u + n) 0 (items ++ generated) +
    2 * fold_right (fun u n => dense_expr_budget costs u + n) 0 universe.

(** Seed construction includes its own fresh universe and selected set rebuild. *)
Definition audit_dense_seed_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (costs : audit_dense_client_budget N E U)
    (direction : audit_seg_direction) (node : N) : nat :=
  let universe := expr_universe EU gk in
  512 + audit_dense_universe_budget EU gk + audit_dense_universe_external_budget gk costs +
    audit_dense_clamp_budget EU universe FinSet.empty +
    2 * fold_right (fun u n => dense_expr_budget costs u + n) 0 universe +
    match direction with
    AuditAvailable => 0
    | AuditBusy => dense_out_budget costs node
    end.

(** A finite maximum ranges over actual flow occurrences and the actual input set. *)
Definition audit_dense_continuation_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (costs : audit_dense_client_budget N E U)
    (direction : audit_seg_direction) (input : avail_set EU gk) : nat :=
  fold_right (fun constraint n => match constraint with
    | Seed _ => n
    | Flow e => Nat.max n (512 + audit_dense_transfer_budget EU gk e (proj1_sig input) +
      audit_dense_transfer_external_budget EU gk costs e (proj1_sig input))
    end) 256 (System.constraints (audit_dense_fx_system EU gk direction)).

(** Every solver callback has a concrete per-input bound, including finite-set operations. *)
Definition audit_dense_declared_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (costs : audit_dense_client_budget N E U)
    (weight : B -> nat) (direction : audit_seg_direction) :
    fx_declared_callback_budget N (dense_constraint N E) (avail_set EU gk)
      (audit_dense_fx_event N E U B) :=
  let node := fun n => 4096 + 64 * Pos.size_nat (encode EN n) + dense_node_budget costs n in
  let endpoint := fun e => 512 + dense_target_budget costs e + dense_source_budget costs e in
  FxDeclaredCallbackBudget _ _ _ _ (audit_dense_fx_event_work weight) node
    (fun c => match c with
      Seed n => node n
      | Flow e =>
        512 + dense_edge_budget costs e + 16 * Pos.size_nat (encode EE e)
      end)
    (fun c => match c with
      Seed _ => 256
      | Flow e =>
        endpoint e
      end)
    node node
    (fun c => match c with
      Seed n => audit_dense_seed_budget EU gk costs direction n
      | Flow e => endpoint e
      end)
    (fun _ input => audit_dense_continuation_budget EU gk costs direction input)
    (fun a b => 256 + 32 * audit_trie_nodes (proj1_sig b))
    (fun a b => 256 + 64 * (audit_trie_nodes (proj1_sig a) + audit_trie_nodes (proj1_sig b)))
    (fun a b => 256 + 64 * (audit_trie_nodes (proj1_sig a) + audit_trie_nodes (proj1_sig b))).

(** Actual client adapters instantiate the generated index, scheduler and every solver callback. *)
Definition audit_dense_callback_instantiation_statement : Prop :=
  forall (S O N E U C B : Type) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (weight : B -> nat) (costs : audit_dense_client_budget N E U)
    node_source edge_source expr_source out_source target_source source_source gen_source
    kill_source,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      (dense_node_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      (dense_edge_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      (dense_expr_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source
      (dense_out_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      (dense_target_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      (dense_source_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source
      (dense_gen_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_kill cb) weight kill_source
      (dense_kill_budget costs) ->
    let sys := audit_dense_fx_system EU gk direction in
    let static := audit_dense_fx_static EU gk direction in
    let model := audit_dense_index_model cb direction in
    let index_budget := audit_dense_fx_index_budget EN EE weight (dense_node_budget costs)
      (dense_edge_budget costs) (dense_target_budget costs) (dense_source_budget costs) in
    let schedule := fx_rpo_scheduler_counted EN sys static model in
    let source := audit_dense_declared_source EN EE EU gk cb direction schedule in
    let budget := audit_dense_declared_budget EN EE EU gk costs weight direction in
    fx_index_external_erases EN sys static model /\ fx_index_external_bounded model index_budget /\
    fx_dep_source_laws model (audit_dense_index_source cb direction) /\
    fx_declared_source_laws EN (dense_constraint_encoding EN EE) (avail_lattice EU gk)
      (rpo_scheduler EN sys static) sys source /\ fx_declared_callback_bounded source budget.
