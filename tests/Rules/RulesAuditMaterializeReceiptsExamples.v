(** * Predicate callback receipt examples

    These examples exercise supplied body receipts and materialization inputs.
    For example, two encoder frames retain two separate body allowances.
    Builds on: RulesAuditMaterializeReceiptsCorrectness and RulesAuditMaterializeStratify. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesJoin RulesSolve
  RulesAuditMaterializePrelude
  RulesAuditMaterializeDeltaTotal RulesAuditMaterializeReceipts
  RulesAuditMaterializeReceiptsCorrectness RulesAuditMaterializeStratify
  RulesAuditMaterializeRounds.
Import List.ListNotations.

(** * Callback fixtures *)

Definition receipt_rule : rule unit := Rule (Atom tt []) [].

Definition receipt_program : program unit :=
  Program unit_encoding (fun _ => 0) [receipt_rule].

Definition receipt_source : mat_predicate_callback_source receipt_program nat :=
  @MatPredicateCallbackSource unit receipt_program nat
    (fun _ code body => code = 1%positive /\ body = [2; 3])
    (fun _ value body => value = 0 /\ body = [4])
    (fun frame => S frame).

(** * Receipt observations *)

(** The supplied bodies account for both repeated encoder calls and the arity call. *)
Example receipt_duplicate_bodies :
  let frames := [MatEncode unit (penc receipt_program) tt 1%positive;
    MatEncode unit (penc receipt_program) tt 1%positive;
    MatArity unit receipt_program tt 0; MatBlock 80] in
  let receipts := [([2; 3], 8); ([2; 3], 8); ([4], 6); ([], 0)] in
  mat_external_trace_receipts receipt_program nat receipt_source (fun _ => 8) (fun _ => 6)
    frames receipts /\
  mat_external_body_work receipt_program nat receipt_source receipts = 19 /\
  mat_external_trace_allowance nat receipts = 22.
Proof.
  cbn zeta.
  unfold mat_external_trace_receipts.
  split.
  - constructor.
    + refine (@MatPredicateEncodeReceipt unit receipt_program nat receipt_source
        (fun _ => 8) (fun _ => 6) tt 1%positive [2; 3] _). split; reflexivity.
    + constructor.
      * refine (@MatPredicateEncodeReceipt unit receipt_program nat receipt_source
        (fun _ => 8) (fun _ => 6) tt 1%positive [2; 3] _). split; reflexivity.
      * constructor.
        -- refine (@MatPredicateArityReceipt unit receipt_program nat receipt_source
            (fun _ => 8) (fun _ => 6) tt 0 [4] _). split; reflexivity.
        -- constructor.
           ++ apply MatInternalFrameReceipt. reflexivity.
           ++ constructor.
  - split; reflexivity.
Qed.

(** An empty trace has no body work and no allowance. *)
Example receipt_empty :
  mat_external_trace_receipts receipt_program nat receipt_source (fun _ => 8) (fun _ => 6)
    [] [] /\
  mat_external_body_work receipt_program nat receipt_source [] = 0 /\
  mat_external_trace_allowance nat [] = 0.
Proof.
  repeat split; constructor.
Qed.

(** * Stratification observations *)

Definition receipt_negative : program unit :=
  Program unit_encoding (fun _ => 0) [Rule (Atom tt []) [LNeg (Atom tt [])]].

Definition receipt_malformed : program unit :=
  Program unit_encoding (fun _ => 2) [receipt_rule].

Definition receipt_two_levels : program bool :=
  Program bool_encoding (fun _ => 0) [Rule (Atom true []) [LNeg (Atom false [])]].

(** A valid program generates a nonempty trace and accepts. *)
Example receipt_positive_run :
  match mat_stratify receipt_program with
  | (Some _, _ :: _) => true
  | _ => false
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A malformed arity retains the stratifier's accepted behavior and a nonempty trace. *)
Example receipt_malformed_run :
  match mat_stratify receipt_malformed with
  | (Some _, _ :: _) => true
  | _ => false
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A negative self-dependency rejects after emitting a nonempty trace. *)
Example receipt_rejected_run :
  match mat_stratify receipt_negative with
  | (None, _ :: _) => true
  | _ => false
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A negative dependency produces two levels on the accepted run. *)
Example receipt_multilevel_run :
  match fst (mat_stratify receipt_two_levels) with
  | Some context =>
    (count (mat_native_levels context), level (mat_native_levels context) true,
      level (mat_native_levels context) false) = (2, 1, 0)
  | None => False
  end.
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty edge pass finishes with an empty final round. *)
Example receipt_final_empty_round :
  fst (mat_program_edges receipt_program) = [] /\
  snd (fst (mat_stratify_tick receipt_program (CollectionsMap.Map.empty, false))) = true.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** * Callback laws and materializer observations *)

(** These concrete callback implementations satisfy the per-input bounds. *)
Example receipt_source_bounds :
  mat_predicate_callback_input_bounds_statement receipt_program nat receipt_source
    (fun _ => 8) (fun _ => 6).
Proof.
  split.
  - intros p code body [_ Hbody]. subst body. cbn. reflexivity.
  - intros p value body [_ Hbody]. subst body. cbn. reflexivity.
Qed.

(** The bound applies to the actual supplied receipt sequence. *)
Example receipt_bound_consumer :
  mat_external_body_work receipt_program nat receipt_source
    [([2; 3], 8); ([4], 6)] <= mat_external_trace_allowance nat [([2; 3], 8); ([4], 6)].
Proof.
  eapply (mat_external_trace_bound unit receipt_program nat receipt_source
    (fun _ => 8) (fun _ => 6) receipt_source_bounds
    [MatEncode unit (penc receipt_program) tt 1%positive; MatArity unit receipt_program tt 0]).
  unfold mat_external_trace_receipts.
  constructor.
  - refine (@MatPredicateEncodeReceipt unit receipt_program nat receipt_source
      (fun _ => 8) (fun _ => 6) tt 1%positive [2; 3] _).
    split; reflexivity.
  - constructor.
    + refine (@MatPredicateArityReceipt unit receipt_program nat receipt_source
        (fun _ => 8) (fun _ => 6) tt 0 [4] _).
      split; reflexivity.
    + constructor.
Qed.

(** The real stratifier trace contains the encoder occurrence used in the receipt. *)
Example receipt_actual_encoder_occurrence :
  In (MatEncode unit (penc receipt_program) tt 1%positive) (snd (mat_stratify receipt_program)).
Proof.
  vm_compute. tauto.
Qed.

(** Duplicate rules are accepted and produce a nonempty trace. *)
Example receipt_duplicate_run :
  match mat_stratify (Program unit_encoding (fun _ => 0) [receipt_rule; receipt_rule]) with
  | (Some _, _ :: _) => true
  | _ => false
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The empty program is accepted and emits a nonempty trace. *)
Example receipt_empty_run :
  match mat_stratify (Program unit_encoding (fun _ => 0) []) with
  | (Some _, _ :: _) => true
  | _ => false
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The accepted bounded materializer produces the ground tuple and its encoder event. *)
Example receipt_actual_materialization :
  match mat_bounded_program IndexedNested receipt_program [] 2%positive with
  | (Some db, events) =>
    db_holds receipt_program db tt [] = true /\
    In (MatEncode unit (penc receipt_program) tt 1%positive) events
  | (None, _) => False
  end.
Proof.
  vm_compute. split; [reflexivity | tauto].
Qed.

(** The encoder event from the same materializer run has a genuine body receipt. *)
Example receipt_actual_materialization_body :
  In (MatEncode unit (penc receipt_program) tt 1%positive)
    (snd (mat_bounded_program IndexedNested receipt_program [] 2%positive)) /\
  mat_external_frame_receipt receipt_program nat receipt_source (fun _ => 8) (fun _ => 6)
    (MatEncode unit (penc receipt_program) tt 1%positive) ([2; 3], 8).
Proof.
  split.
  - vm_compute. tauto.
  - refine (@MatPredicateEncodeReceipt unit receipt_program nat receipt_source
      (fun _ => 8) (fun _ => 6) tt 1%positive [2; 3] _).
    split; reflexivity.
Qed.

(** The materializer's final checked step observes an empty batch after producing the seed. *)
Example receipt_materializer_final_empty :
  match fst (mat_stratify receipt_program) with
  | None => False
  | Some st =>
    let lower := mat_rel receipt_program CollectionsMap.Map.empty in
    let initial := fst (mat_initial IndexedNested receipt_program [] st 0 lower) in
    let observed := fst (mat_observe receipt_program [] st 0 lower 2%positive initial) in
    match mat_step receipt_program [] st 0 lower observed with
    | (None, events) => In (MatBlock 71) events
    | (Some _, _) => False
    end
  end.
Proof.
  vm_compute. tauto.
Qed.

(** The concrete callback source returns the actual results and has positive frame weights. *)
Example receipt_source_laws :
  mat_predicate_callback_receipts_statement receipt_program nat receipt_source.
Proof.
  repeat split.
  - intros frame. cbn. lia.
  - intros []. exists [2; 3]. split; reflexivity.
  - intros []. exists [4]. split; reflexivity.
  - intros [] code body [Hcode _]. exact Hcode.
  - intros [] value body [Hvalue _]. exact Hvalue.
Qed.
