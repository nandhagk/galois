(** * Observation plan-checking examples

    These examples check a nonempty cyclic system and retain its actual callback receipts.
    For example, a missing root is rejected while the remaining checker phases still run.
    Builds on: FixpointAuditObservePlanCheckAdequacy and FixpointAuditNestedExamples. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditEncoding
  CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointObserve
  FixpointAuditIndex
  FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks FixpointAuditObserveExpiry
  FixpointAuditObservePrepare FixpointAuditObserveComponents FixpointAuditObservePlanCheck
  FixpointAuditObservePlanCheckAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointAuditNestedExamples.
Import List.ListNotations.

(** * Nonempty plans and strict branches *)

Definition fx_check_index :=
  index_system nat_encoding fx_nested_client_cycle fx_nested_client_static.

Definition fx_check_plan :=
  observation_canonical nat_encoding fx_nested_client_cycle fx_nested_client_static fx_check_index.

Definition fx_check_run roots plan :=
  fx_observe_plan_check nat_encoding fx_nested_client_cycle fx_nested_client_static fx_check_index
    fx_nested_test_index_callbacks roots plan.

(** A self-loop plan accepts repeated valid roots and rejects a missing root. *)
Example fx_check_accepted_and_missing_root :
  observation_components fx_check_plan = [[3]] /\
  fst (fx_check_run [3; 3] fx_check_plan) = true /\
  fst (fx_check_run [4] fx_check_plan) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Repeating a component or omitting its expiration rejects otherwise nonempty plans. *)
Example fx_check_duplicate_and_expiration_rejected :
  let duplicate := ObservationPlan [[3]; [3]] (observation_expire fx_check_plan) in
  let no_expiration := ObservationPlan [[3]] Map.empty in
  fst (fx_check_run [3] duplicate) = false /\ fst (fx_check_run [3] no_expiration) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition fx_check_strict_phases
    (events : list (fx_observe_check_event nat nat (audit_nat_encoding_event + unit))) : bool :=
  match events with
  | [FxCheckPrepare side; FxCheckPrepare roots; FxCheckComponents components;
      FxCheckPrepare [FxPrepareDependency deps; FxPrepareIndex distinct]; FxCheckExpiry expiry;
      FxCheckCompare compare; FxCheckCase] =>
    negb (Nat.eqb (length side) 0) && negb (Nat.eqb (length roots) 0) &&
      negb (Nat.eqb (length components) 0) && negb (Nat.eqb (length deps) 0) &&
      negb (Nat.eqb (length distinct) 0) && negb (Nat.eqb (length expiry) 0) &&
      negb (Nat.eqb (length compare) 0)
  | _ => false
  end.

(** A rejected root still records all component and expiration phases and the rebuilt unknowns. *)
Example fx_check_rejection_keeps_later_phases :
  let '(out, events) := fx_check_run [4] fx_check_plan in
  out = false /\ fx_check_strict_phases events = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition fx_check_expiry_laws :
    fx_observe_expiry_source_laws nat_encoding fx_nested_client_cycle fx_nested_test_source
      fx_nested_test_budget.
Proof.
  unfold fx_observe_expiry_source_laws; repeat split.
  - exact fx_nested_test_encode_source_total.
  - intro c; exists [inr tt]; split; reflexivity.
  - exact fx_nested_test_encode_source_bound.
  - intros c out body [_ ->]; reflexivity.
Qed.

(** The full theorem applies to the real recursive encoder and target callback on this plan. *)
Example fx_check_source_client :
  let '(out, events) := fx_check_run [3; 3] fx_check_plan in
  exists groups, Forall2 (fx_observe_check_event_source fx_nested_test_index_source
    fx_nested_test_source) events groups /\
    out = observation_plan_check nat_encoding fx_nested_client_cycle fx_nested_client_static
      fx_check_index [3; 3] fx_check_plan /\
    fx_observe_check_work fx_nested_test_index_budget events +
      fx_declared_body_work fx_nested_test_weight groups <=
      fx_observe_plan_check_budget nat_encoding fx_nested_client_cycle fx_nested_client_static
        fx_check_index fx_nested_test_index_budget [3; 3] fx_check_plan +
      fold_right (fun event n => fx_observe_check_external_budget fx_nested_test_budget event + n)
        0 events.
Proof.
  unfold fx_check_run.
  apply (fx_observe_plan_check_source nat nat _ _ _ nat_encoding fx_nested_client_cycle
    fx_nested_client_static fx_check_index fx_nested_test_index_callbacks
    fx_nested_test_index_budget
    fx_nested_test_index_source fx_nested_test_source fx_nested_test_budget [3; 3] fx_check_plan
    fx_nested_test_index_erases fx_nested_test_index_bounded fx_nested_test_index_source_laws
    fx_check_expiry_laws).
Qed.

Definition fx_check_key_three_body (body : list (audit_nat_encoding_event + unit)) : bool :=
  match body with
  | [inl (AuditNatFrame 3); inl (AuditNatFrame 2); inl (AuditNatFrame 1);
      inl (AuditNatFrame 0); inl (AuditPositiveSuccFrame 1%positive 2%positive);
      inl (AuditPositiveSuccFrame 2%positive 3%positive);
      inl (AuditPositiveSuccFrame 3%positive 4%positive);
      inl (AuditPositiveSuccFrame 1%positive 2%positive)] => true
  | _ => false
  end.

Definition fx_check_target_call
    (event : fx_observe_check_event nat nat (audit_nat_encoding_event + unit)) : bool :=
  match event with
  | FxCheckPrepare events => existsb (fun item =>
      match item with
      | FxPrepareDependency calls => existsb (fun call =>
          match call with
          | FxDepIndexEvent (FxiTarget 3 3 [inr tt]) => true
          | _ => false
          end) calls
      | _ => false
      end) events
  | _ => false
  end.

Definition fx_check_encoder_call
    (event : fx_observe_check_event nat nat (audit_nat_encoding_event + unit)) : bool :=
  match event with
  | FxCheckPrepare events => existsb (fun item =>
      match item with
      | FxPrepareIndex calls => existsb (fun call =>
          match call with
          | FxiDistinctBuild _ _ entries => existsb (fun entry =>
              match entry with
              | AuditSetAdd 3 4%positive _ _ body _ => fx_check_key_three_body body
              | _ => false
              end) entries
          | _ => false
          end) calls
      | _ => false
      end) events
  | _ => false
  end.

(** The checker reaches target 3 and retains the complete recursive and carry encoder body. *)
Example fx_check_actual_callback_bodies :
  let '(_, events) := fx_check_run [3; 3] fx_check_plan in
  existsb fx_check_target_call events = true /\ existsb fx_check_encoder_call events = true /\
  fx_one_body_work fx_nested_test_weight (snd (fx_nested_test_encode 3)) = 16.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Empty roots are allowed, but an empty component list cannot cover a nonempty system. *)
Example fx_check_empty_roots_and_missing_components :
  fst (fx_check_run [] fx_check_plan) = true /\
  fst (fx_check_run [] (ObservationPlan [] Map.empty)) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition fx_check_empty_system : System.t nat nat bool :=
  System.Make [] (fun c => c) (fun _ => Query.Ret false).

Definition fx_check_empty_static : System.static fx_check_empty_system.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _); intros c state x Hin; exact Hin.
Defined.

Definition fx_check_empty_callbacks :
    fx_index_external_model nat nat (audit_nat_encoding_event + unit) :=
  FxIndexExternalModel nat nat (audit_nat_encoding_event + unit) fx_nested_test_encode
    (fun c => (c, [inr tt])) (fun _ => ([], [inr tt])) (fun _ => ([], [inr tt])).

(** An empty system accepts its empty canonical plan and rejects a nonempty root. *)
Example fx_check_empty_system_boundary :
  let ix := index_system nat_encoding fx_check_empty_system fx_check_empty_static in
  let plan := observation_canonical nat_encoding fx_check_empty_system fx_check_empty_static ix in
  fst (fx_observe_plan_check nat_encoding fx_check_empty_system fx_check_empty_static ix
    fx_check_empty_callbacks [] plan) = true /\
  fst (fx_observe_plan_check nat_encoding fx_check_empty_system fx_check_empty_static ix
    fx_check_empty_callbacks [0] plan) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * A forward boundary between distinct components *)

Definition fx_check_forward_system : System.t nat nat bool :=
  System.Make [0; 1] (fun c => c)
    (fun c =>
    match c with
    | 1 => Query.Ask 0 Query.Ret
    | _ => Query.Ret false
    end).

Definition fx_check_forward_static : System.static fx_check_forward_system.
Proof.
  refine (System.Static (fun c =>
    match c with
    | 1 => [0]
    | _ => []
    end) (fun _ => []) _ _).
  - intros [|[|c]] state x Hin; exact Hin.
  - intros [|[|c]] state x Hin; exact Hin.
Defined.

Definition fx_check_forward_callbacks :
    fx_index_external_model nat nat (audit_nat_encoding_event + unit) :=
  FxIndexExternalModel nat nat (audit_nat_encoding_event + unit) fx_nested_test_encode
    (fun c => (c, [inr tt])) (fun _ => ([], [inr tt]))
    (fun c => (System.deps fx_check_forward_static c, [inr tt])).

(** A dependency on an earlier component is accepted; reversing the boundary is rejected. *)
Example fx_check_forward_component_boundary :
  fst (fx_observe_components nat_encoding fx_check_forward_system fx_check_forward_static
    fx_check_forward_callbacks [[0]; [1]]) = true /\
  fst (fx_observe_components nat_encoding fx_check_forward_system fx_check_forward_static
    fx_check_forward_callbacks [[1]; [0]]) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.
