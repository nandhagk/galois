(** * Complete naive and semi-naive source boundaries

    The proposition types account for predicate callback bodies at their actual occurrences.
    For example, a cached arity read has one source receipt for the supplied arity implementation.
    Builds on: the concrete Delta and naive total runs and per-call predicate receipts. *)

From Stdlib Require Import List.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta
  RulesAuditMaterializePrelude RulesAuditMaterializeDeltaTotal RulesAuditMaterializeReceipts
  RulesAuditMaterializeNaiveTotal.

(** * Whole-source proposition types *)

(** The proposed Delta receipt condition covers external occurrences in a completed run. *)
Definition mat_delta_program_callback_receipts_statement : Prop :=
  forall P strategy (prog : program P) facts B (source : mat_predicate_callback_source prog B)
      encode_budget arity_budget output events rounds,
    mat_predicate_callback_receipts_statement prog B source ->
    mat_program_run strategy prog facts output events rounds ->
    exists receipts,
      mat_external_trace_receipts prog B source encode_budget arity_budget events receipts.

(** The proposed Delta result requires a matching run, receipts and their combined work bound. *)
Definition rules_delta_materialization_full_source_statement : Prop :=
  forall P strategy (prog : program P) facts B (source : mat_predicate_callback_source prog B)
      encode_budget arity_budget,
    mat_predicate_callback_receipts_statement prog B source ->
    mat_predicate_callback_input_bounds_statement prog B source encode_budget arity_budget ->
    exists output events rounds receipts,
      mat_program_run strategy prog facts output events rounds /\
      output = solve_program_delta strategy prog facts /\
      mat_external_trace_receipts prog B source encode_budget arity_budget events receipts /\
      mat_work events + mat_external_body_work prog B source receipts <=
        mat_whole_budget (mat_input_dimension prog facts) (mat_program_loop_budget prog facts)
          (mat_width events) + mat_external_trace_allowance B receipts.

(** This conjunction names the proposed bounds for both fixed algorithms. *)
Definition rules_materialization_full_source_statement : Prop :=
  rules_delta_materialization_full_source_statement /\
  rules_naive_materialization_full_source_statement.
