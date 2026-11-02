(** * Predicate callback receipt bounds

    This file bounds the body work of occurrence-matched predicate receipts.
    For example, an internal frame contributes no body work or allowance.
    Builds on: RulesAuditMaterializeReceipts. *)

From Stdlib Require Import List Lia.
From Galois.Rules Require Import RulesSyntax RulesAuditMaterializeDeltaTotal
  RulesAuditMaterializeReceipts.

(** * Callback receipt bound *)

(** The sum of actual callback body work fits the corresponding input allowances. *)
Theorem mat_external_trace_bound :
  forall (P : Type) (prog : program P) (B : Type)
    (source : @mat_predicate_callback_source P prog B) (encode_budget arity_budget : P -> nat),
    @mat_predicate_callback_input_bounds_statement P prog B source encode_budget arity_budget ->
    forall frames receipts,
      @mat_external_trace_receipts P prog B source encode_budget arity_budget frames receipts ->
      @mat_external_body_work P prog B source receipts <= mat_external_trace_allowance B receipts.
Proof.
  intros P prog B source encode_budget arity_budget [Hencode Harity] frames receipts Hreceipts.
  induction Hreceipts as [|frame receipt frames receipts Hreceipt Hreceipts IH].
  - reflexivity.
  - destruct Hreceipt as [frame Hinternal | p code body Hbody | p value body Hbody].
    + exact IH.
    + specialize (Hencode p code body Hbody).
      simpl in *.
      lia.
    + specialize (Harity p value body Hbody).
      simpl in *.
      lia.
Qed.
