(** * Genuine predicate callback body receipts

    These receipts model predicate encoder and arity evidence for captured-level program runs.
    External level callbacks also require evidence; this relation has no level receipt constructor.
    For example, an encoder receipt retains the actual predicate and returned positive code.
    Builds on: the concrete materialization frames and predicate source interface. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Rules Require Import RulesSyntax RulesAuditMaterializePrelude
  RulesAuditMaterializeDeltaTotal.
Import List.ListNotations.

(** * Predicate callback receipts *)

(** Encoding, arity and external-level frames require callback evidence. *)
Definition mat_frame_needs_callback (frame : mat_frame) : bool :=
  match frame with
  | MatEncode _ _ _ _ | MatArity _ _ _ _ | MatLevel _ _ _ _ => true
  | _ => false
  end.

Section PredicateBodies.
Context {P : Type} (prog : program P) (B : Type) (source : mat_predicate_callback_source prog B)
  (encode_budget arity_budget : P -> nat).

(** A receipt identifies an internal frame or a predicate callback body and its allowance. *)
Inductive mat_external_frame_receipt : mat_frame -> list B * nat -> Prop :=
  | MatInternalFrameReceipt : forall frame,
      mat_frame_needs_callback frame = false -> mat_external_frame_receipt frame ([], 0)
  | MatPredicateEncodeReceipt : forall p code body,
      mat_predicate_encoder_body prog B source p code body ->
      mat_external_frame_receipt (MatEncode P (penc prog) p code) (body, encode_budget p)
  | MatPredicateArityReceipt : forall p n body,
      mat_predicate_arity_body prog B source p n body ->
      mat_external_frame_receipt (MatArity P prog p n) (body, arity_budget p).

(** Every receipt belongs to the corresponding occurrence in this same frame sequence. *)
Definition mat_external_trace_receipts (frames : list mat_frame) (receipts : list (list B * nat))
    : Prop := Forall2 mat_external_frame_receipt frames receipts.

Definition mat_external_body_work (receipts : list (list B * nat)) : nat :=
  fold_right (fun receipt n =>
    fold_right (fun frame m => mat_predicate_body_frame_weight prog B source frame + m)
      0 (fst receipt) + n) 0 receipts.

Definition mat_external_trace_allowance (receipts : list (list B * nat)) : nat :=
  fold_right (fun receipt n => snd receipt + n) 0 receipts.

(** The proposed bound sums per-input allowances for the corresponding frame receipts. *)
Definition mat_external_trace_bound_statement : Prop :=
  mat_predicate_callback_input_bounds_statement prog B source encode_budget arity_budget ->
  forall frames receipts, mat_external_trace_receipts frames receipts ->
    mat_external_body_work receipts <= mat_external_trace_allowance receipts.

End PredicateBodies.
