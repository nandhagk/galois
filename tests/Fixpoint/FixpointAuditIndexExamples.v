(** * Indexed preparation examples

    These computations inspect repeated destinations, repeated constraints and empty systems.
    For example, a repeated side target contributes once per constraint occurrence.
    Builds on: FixpointAuditIndexAdequacy and FixpointAuditModelsExamples. *)

From Stdlib Require Import List Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding
  CollectionsAuditEncodingAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointAuditIndex
  FixpointAuditIndexAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX1 FixpointAuditModelsExamples.
Import List.ListNotations.

(** * Callback receipts *)

Definition fx_index_fixture_source :
    fx_index_external_source nat bool (audit_nat_encoding_event + unit) :=
  FxIndexExternalSource nat bool (audit_nat_encoding_event + unit)
    (fun x code body => fxi_encode fx_models_callbacks x = (code, body))
    (fun c out body => fxi_target fx_models_callbacks c = (out, body))
    (fun c out body => fxi_sides fx_models_callbacks c = (out, body))
    (fun c out body => fxi_deps fx_models_callbacks c = (out, body)).

Lemma fx_index_fixture_body_work body :
  fxi_body_work fx_models_budget body = length body.
Proof.
  induction body as [|event rest IH].
  - reflexivity.
  - change (1 + fxi_body_work fx_models_budget rest = S (length rest)).
    rewrite IH; lia.
Qed.

(** Each sample callback returns the corresponding original system value. *)
Lemma fx_index_fixture_erases :
  fx_index_external_erases nat_encoding sample_system sample_static fx_models_callbacks.
Proof.
  unfold fx_index_external_erases; repeat split.
  - intro x; unfold fx_models_callbacks; cbn [fxi_encode].
    destruct (audit_nat_encode x) as [code body] eqn:Hencode.
    pose proof (audit_nat_encode_erases x) as Herase.
    rewrite Hencode in Herase; exact Herase.
Qed.

(** Each callback receipt fits its separate budget, including the counted natural encoder. *)
Lemma fx_index_fixture_bounded : fx_index_external_bounded fx_models_callbacks fx_models_budget.
Proof.
  unfold fx_index_external_bounded; repeat split.
  - intro event; destruct event; reflexivity.
  - intro x; unfold fx_models_callbacks; cbn [fxi_encode].
    destruct (audit_nat_encode x) as [code body] eqn:Hencode.
    cbn [snd]; rewrite fx_index_fixture_body_work, length_map.
    pose proof (audit_nat_encode_count x) as Hcount.
    rewrite Hencode in Hcount; cbn in Hcount.
    unfold fx_models_budget; cbn [fxi_encode_bound encode nat_encoding] in *; nia.
  - intro c; reflexivity.
  - intro c; reflexivity.
  - intro c; reflexivity.
Qed.

(** The nonempty sample's trace records the actual callback outputs and bodies. *)
Example fx_index_fixture_receipts :
  fx_index_external_trace_adequacy fx_index_fixture_source
    (snd (fx_index_nested_counted sample_system fx_models_callbacks)).
Proof.
  vm_compute; repeat constructor; reflexivity.
Qed.

(** The concrete callback laws and receipts instantiate the external-source theorem. *)
Example fx_index_fixture_source_bound :
  let '(ix, events) := fx_index_nested_counted sample_system fx_models_callbacks in
  ix = sample_index /\
  fx_index_adapter_work fx_models_budget events <=
    fx_index_nested_input_budget nat_encoding sample_system sample_static fx_models_budget.
Proof.
  pose proof (fx_index_external_source_holds nat bool bool _ nat_encoding sample_system
    sample_static fx_models_callbacks fx_models_budget fx_index_fixture_source
    fx_index_fixture_erases fx_index_fixture_bounded) as Hsource.
  destruct (fx_index_nested_counted sample_system fx_models_callbacks) as [ix events] eqn:Hrun.
  apply Hsource; pose proof fx_index_fixture_receipts as Hreceipt.
  rewrite Hrun in Hreceipt; exact Hreceipt.
Qed.

(** The repeated side target is stored once, while the other destination is absent. *)
Example fx_index_repeated_side :
  let ix := fst (fx_index_nested_counted sample_system fx_models_callbacks) in
  contributors_of nat_encoding ix 2 = [false] /\
  contributors_of nat_encoding ix 3 = [].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Duplicate and empty constraint lists *)

Definition fx_index_duplicate_system : System.t nat bool bool :=
  System.Make [false; false] (System.target sample_system) (System.rhs sample_system).

Definition fx_index_empty_system : System.t nat bool bool :=
  System.Make [] (System.target sample_system) (System.rhs sample_system).

(** Duplicate constraints remain duplicate entries even when their side lists are deduplicated. *)
Example fx_index_duplicate_constraints :
  let ix := fst (fx_index_nested_counted fx_index_duplicate_system fx_models_callbacks) in
  contributors_of nat_encoding ix 0 = [false; false] /\
  contributors_of nat_encoding ix 2 = [false; false] /\
  readers_of nat_encoding ix 0 = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Duplicate occurrences each have their own actual callback receipts. *)
Example fx_index_duplicate_receipts :
  fx_index_external_trace_adequacy fx_index_fixture_source
    (snd (fx_index_nested_counted fx_index_duplicate_system fx_models_callbacks)).
Proof.
  vm_compute; repeat constructor; reflexivity.
Qed.

(** Empty constraints return empty maps and emit just the terminal fold frame. *)
Example fx_index_empty :
  let '(ix, events) := fx_index_nested_counted fx_index_empty_system fx_models_callbacks in
  contributors_of nat_encoding ix 0 = [] /\
  readers_of nat_encoding ix 0 = [] /\
  events = [FxiCase 2].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
