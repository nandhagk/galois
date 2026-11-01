(** * Dense and sparse SEG portfolio source

    The portfolio selects one dense or expression-specific sparse producer and reuses its result.
    For example, a fixed expression can be probed at several nodes with one sparse build.
    Builds on: the dense and sparse same-solve batch source contracts. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse AnalysesAuditSegBatch AnalysesAuditSegDenseBudget
  AnalysesAuditSegDenseBatch.
Import List.ListNotations.

(** * Dense and sparse SEG portfolio source *)

(** One selected dense solve or one expression-specific sparse build receives the node batch. *)
Definition audit_seg_portfolio_input_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (choice : audit_seg_choice) (u : U) (nodes : list N)
    (weight : B -> nat) (costs : audit_dense_client_budget N E U) : nat :=
  match choice with
  | AuditDense => audit_dense_batch_budget EN EE EU gk cb direction weight costs
    (map (fun n => (n, u)) nodes)
  | AuditSparse => audit_seg_universe_input_budget EU gk u +
    if FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk)) then
      audit_seg_sparse_batch_input_budget EN EE EU gk direction u nodes weight
        (dense_node_budget costs) (dense_edge_budget costs) (dense_target_budget costs)
        (dense_source_budget costs)
    else 0
  end.

(** Both choices agree at the original listed graph nodes under the published readiness premise. *)
Definition audit_dense_portfolio_answers_statement : Prop :=
  forall (S O N E U C : Type) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (direction : audit_seg_direction) (u : U) (nodes : list N),
    ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
    (forall n, In n nodes -> In n (Graph.nodes (cfg (gkview gk)))) ->
    map (audit_seg_select EN EE EU gk direction AuditDense u) nodes =
      map (audit_seg_select EN EE EU gk direction AuditSparse u) nodes.

(** The selection budget records the actual absent-expression branch without a sparse build. *)
Definition audit_dense_portfolio_budget_statement : Prop :=
  forall (S O N E U C B : Type) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (u : U) (nodes : list N) (weight : B -> nat)
    (costs : audit_dense_client_budget N E U),
    audit_seg_portfolio_input_budget EN EE EU gk cb direction AuditDense u nodes weight costs =
      audit_dense_batch_budget EN EE EU gk cb direction weight costs (map (fun n => (n, u))
        nodes) /\
    audit_seg_portfolio_input_budget EN EE EU gk cb direction AuditSparse u nodes weight costs =
      audit_seg_universe_input_budget EU gk u +
      (if FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk)) then
        audit_seg_sparse_batch_input_budget EN EE EU gk direction u nodes weight
          (dense_node_budget costs) (dense_edge_budget costs) (dense_target_budget costs)
          (dense_source_budget costs)
      else 0).

(** Selecting a branch exposes that branch’s complete same-run source contract. *)
Definition audit_dense_portfolio_selected_source_statement : Prop :=
  forall choice, match choice with
  | AuditDense => audit_dense_batch_source_statement
  | AuditSparse => audit_seg_sparse_batch_adapted_statement
  end.

(** The portfolio requires both actual branch source contracts and their exact-result boundary. *)
Definition audit_dense_portfolio_contract_statement : Prop :=
  audit_dense_portfolio_selected_source_statement /\
    audit_dense_portfolio_answers_statement /\ audit_dense_portfolio_budget_statement.
