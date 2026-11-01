(** * Fixpoint model observations

    A cyclic system exercises the counted index producer and its input budget.
    For example, the sample has two constraints and repeated side targets.
    Builds on: FixpointFIX1, FixpointAuditIndex and CollectionsAuditEncoding. *)

From Stdlib Require Import List Arith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointAuditIndex.
From Galois.Tests.Fixpoint Require Import FixpointFIX1.
Import List.ListNotations.

Definition fx_models_callbacks :
    fx_index_external_model nat bool (audit_nat_encoding_event + unit) :=
  FxIndexExternalModel nat bool (audit_nat_encoding_event + unit)
    (fun x => let '(code, body) := audit_nat_encode x in (code, map inl body))
    (fun c => (System.target sample_system c, [inr tt]))
    (fun c => (side_targets sample_static c, [inr tt]))
    (fun c => (deps sample_static c, [inr tt])).

Definition fx_models_budget :
    fx_index_external_budget nat bool (audit_nat_encoding_event + unit) :=
  FxIndexExternalBudget nat bool (audit_nat_encoding_event + unit)
    (fun _ => 1) (fun x => 2 * S x * S (Pos.size_nat (encode nat_encoding x)))
    (fun _ => 1) (fun _ => 1) (fun _ => 1).

(** The cyclic sample produces its original index, a nonempty trace and work within the budget. *)
Example fx_models_index_nonempty :
  let '(out, events) := fx_index_nested_counted sample_system fx_models_callbacks in
  out = sample_index /\ events <> [] /\
  Nat.leb (fx_index_adapter_work fx_models_budget events)
    (fx_index_nested_input_budget nat_encoding sample_system sample_static fx_models_budget) = true.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

(** Distinct construction orders the sample keys and removes the duplicate two. *)
Example fx_models_distinct_nonempty :
  fst (fxi_distinct_counted fx_models_callbacks [2; 0; 2]) = [0; 2].
Proof.
  vm_compute; reflexivity.
Qed.

(** Distinct construction does not introduce key one into the sample. *)
Example fx_models_distinct_absent :
  existsb (Nat.eqb 1) (fst (fxi_distinct_counted fx_models_callbacks [2; 0; 2])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** Distinct construction returns no keys on empty input. *)
Example fx_models_distinct_empty : fst (fxi_distinct_counted fx_models_callbacks []) = [].
Proof.
  vm_compute; reflexivity.
Qed.
