(** * Dense SEG client callback laws

    Client source relations describe actual per-input calls and bodies.
    For example, an edge-generation body is tied to that exact edge and returned list.
    Builds on: the graph callback adapter and dense client budget. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditMap
  CollectionsAuditFinSet.
From Galois.Graph Require Import GraphAuditBase.
From Galois.Fixpoint Require Import FixpointAuditIndex.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse
  AnalysesAuditSegDenseTransfer AnalysesAuditSegDenseSystem AnalysesAuditSegDenseBudget.
Import List.ListNotations.

(** * Dense SEG client callback laws *)

(** Sources describe real client callback bodies at their exact inputs and results. *)
Record audit_dense_client_source (N E U B : Type) : Type := AuditDenseClientSource {
  dense_node_source : N -> positive -> list B -> nat -> Prop;
  dense_edge_source : E -> positive -> list B -> nat -> Prop;
  dense_expr_source : U -> positive -> list B -> nat -> Prop;
  dense_out_source : N -> list E -> list B -> nat -> Prop;
  dense_target_source : E -> N -> list B -> nat -> Prop;
  dense_source_source : E -> N -> list B -> nat -> Prop;
  dense_gen_source : E -> list U -> list B -> nat -> Prop;
  dense_kill_source : E * U -> bool -> list B -> nat -> Prop
}.

Arguments dense_node_source {N E U B} _ _ _ _ _.

Arguments dense_edge_source {N E U B} _ _ _ _ _.

Arguments dense_expr_source {N E U B} _ _ _ _ _.

Arguments dense_out_source {N E U B} _ _ _ _ _.

Arguments dense_target_source {N E U B} _ _ _ _ _.

Arguments dense_source_source {N E U B} _ _ _ _ _.

Arguments dense_gen_source {N E U B} _ _ _ _ _.

Arguments dense_kill_source {N E U B} _ _ _ _ _.

(** The laws match callbacks to the view and bound each actual client invocation. *)
Definition audit_dense_client_laws {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (weight : B -> nat) (costs : audit_dense_client_budget N E U)
    (source : audit_dense_client_source N E U B) : Prop :=
  audit_seg_full_callbacks_erase EN EE EU gk cb /\
  audit_graph_external_callback_adapter (seg_build_node_encode cb) weight (dense_node_source source)
    (dense_node_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight (dense_edge_source source)
    (dense_edge_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight (dense_expr_source source)
    (dense_expr_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_out cb) weight (dense_out_source source)
    (dense_out_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_target cb) weight (dense_target_source source)
    (dense_target_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_source cb) weight (dense_source_source source)
    (dense_source_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_gen cb) weight (dense_gen_source source)
    (dense_gen_budget costs) /\
  audit_graph_external_callback_adapter (seg_build_kill cb) weight (dense_kill_source source)
    (dense_kill_budget costs).

(** The exact event body determines the work argument passed to a client source relation. *)
Definition audit_dense_client_body_work {B} (weight : B -> nat) (body : list B) : nat :=
  fold_right (fun item n => weight item + n) 0 body.

(** Every expression-set event preserves the actual key, code and client encoder body. *)
Definition audit_dense_expr_set_source {N E U B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B) (event : audit_set_event U B) : Prop :=
  match event with
  | AuditSetAdd u code _ _ body _ | AuditSetMem u code _ _ body _ |
    AuditSetRemove u code _ _ body _ =>
    dense_expr_source source u code body (audit_dense_client_body_work weight body)
  | AuditSetFold _ _ => True
  end.

(** Every universe event links its actual callback body to the client source. *)
Definition audit_dense_universe_client_source {N E U B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B) (event : audit_seg_universe_event N E U B) :
    Prop :=
  match event with
  | SegUniverseOut n out body => dense_out_source source n out body
    (audit_dense_client_body_work weight body)
  | SegUniverseGen e out body => dense_gen_source source e out body
    (audit_dense_client_body_work weight body)
  | SegUniverseSet call => audit_dense_expr_set_source weight source call
  | _ => True
  end.

(** Every transfer event retains the original generation, kill and expression encoder source. *)
Definition audit_dense_transfer_client_source {N E U B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B) (event : audit_dense_transfer_event N E U B) :
    Prop :=
  match event with
  | DenseTransferUniverse events => Forall (audit_dense_universe_client_source weight source) events
  | DenseTransferSet events => Forall (audit_dense_expr_set_source weight source) events
  | DenseTransferGen e out body => dense_gen_source source e out body
    (audit_dense_client_body_work weight body)
  | DenseTransferKill e u out body =>
    dense_kill_source source (e, u) out body (audit_dense_client_body_work weight body)
  | _ => True
  end.

(** Nested scheduler and finite-set source events expose their actual client bodies. *)
Definition audit_dense_fx_client_source {N E U B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B) (event : audit_dense_fx_event N E U B) : Prop :=
  match event with
  | DenseFxNodeEncode n out body => dense_node_source source n out body
    (audit_dense_client_body_work weight body)
  | DenseFxEdgeEncode e out body => dense_edge_source source e out body
    (audit_dense_client_body_work weight body)
  | DenseFxOut n out body => dense_out_source source n out body (audit_dense_client_body_work
    weight body)
  | DenseFxTarget e out body => dense_target_source source e out body
    (audit_dense_client_body_work weight body)
  | DenseFxSource e out body => dense_source_source source e out body
    (audit_dense_client_body_work weight body)
  | DenseFxUniverse events => Forall (audit_dense_universe_client_source weight source) events
  | DenseFxTransfer events => Forall (audit_dense_transfer_client_source weight source) events
  | DenseFxNodeMap e => match e with
    | AuditMapGet n code _ _ body _ | AuditMapSet n _ code _ _ body _ |
      AuditMapRemove n code _ _ body _ =>
      dense_node_source source n code body (audit_dense_client_body_work weight body)
    end
  | DenseFxNodeSet e => match e with
    | AuditSetAdd n code _ _ body _ | AuditSetMem n code _ _ body _ |
      AuditSetRemove n code _ _ body _ =>
      dense_node_source source n code body (audit_dense_client_body_work weight body)
    | AuditSetFold _ _ => True
    end
  | _ => True
  end.

(** The body of each set operation retains every generated dense callback source event. *)
Definition audit_dense_index_set_client_source {N E U B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B) (event : audit_set_event N
    (audit_dense_fx_event N E U B)) : Prop :=
  match event with
  | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
    AuditSetRemove _ _ _ _ body _ => Forall (audit_dense_fx_client_source weight source) body
  | AuditSetFold _ _ => True
  end.

(** Index receipts expose client bodies nested inside each actual dictionary call. *)
Definition audit_dense_index_client_source {N E U B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B)
    (event : fx_index_nested_event N (dense_constraint N E) (audit_dense_fx_event N E U B)) :
    Prop :=
  match event with
  | FxiTarget _ _ body | FxiSides _ _ body | FxiDeps _ _ body |
    FxiRead _ _ _ _ body _ | FxiWrite _ _ _ _ _ body _ =>
    Forall (audit_dense_fx_client_source weight source) body
  | FxiDistinctBuild _ _ events => Forall (audit_dense_index_set_client_source weight source) events
  | _ => True
  end.
