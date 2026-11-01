(** * Analysis portfolio source-cost facade

    The facade combines liveness and expression-availability choice contracts.
    For example, dense and sparse expression queries retain their own same-solve batches.
    Builds on: liveness, sparse SEG and dense SEG source models. *)
From Galois.Analyses Require Export AnalysesAuditSsaPortfolio AnalysesAuditSegQuery
  AnalysesAuditSegBatch AnalysesAuditSegDensePortfolio.

(** * Portfolio source contract *)

(** Both analysis families retain their source boundaries and exact choice semantics. *)
Definition analyses_portfolio_source_contract_statement : Prop :=
  audit_live_portfolio_contract_statement /\ audit_seg_query_contract_statement /\
  audit_seg_sparse_batch_adapted_statement /\ audit_dense_portfolio_contract_statement.
