(** * Numbered observation table examples

    Occurrence numbering preserves duplicates and the fallback for missing indices.
    For example, two equal constraints have separate numbered table entries.
    Builds on: FixpointAuditObserveNumberAdequacy and unary encoder adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditEncoding
  CollectionsAuditEncodingAdequacy CollectionsAuditEncoderBudget.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditObserveNumber
  FixpointAuditObserveNumberAdequacy.
Import List.ListNotations.

(** * Occurrence and unary encoding boundaries *)

(** Duplicate values remain addressable at both distinct occurrence indices. *)
Example fx_number_duplicate_occurrences :
  let '(table, _) := fx_observe_number 2 [7; 7; 9] in
  (Map.get nat_encoding 2 table, Map.get nat_encoding 3 table, Map.get nat_encoding 4 table,
    Map.get nat_encoding 5 table) = (Some 7, Some 7, Some 9, None).
Proof.
  vm_compute; reflexivity.
Qed.

(** Missing indices select the original fallback while retaining their real map lookup events. *)
Example fx_number_missing_label :
  let '(table, _) := fx_observe_number 0 [7; 7] in
  let '(label, events) := fx_observe_label 9 table 3 in
  label = 9 /\ events <> [] /\ 0 < audit_map_source_work audit_nat_events_work events.
Proof.
  vm_compute; repeat split; try reflexivity; try discriminate; lia.
Qed.

(** An empty table retains its fallback and the same unary encoding semantics. *)
Example fx_number_empty_table :
  fst (fx_observe_number 0 ([] : list nat)) = Map.empty /\
  fst (fx_observe_label 9 Map.empty 0) = 9.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The lookup's key three has a genuine recursive unary and positive-carry derivation. *)
Example fx_number_three_encoder_source :
  exists work, audit_nat_encode_run 3 (fst (audit_nat_encode 3)) (snd (audit_nat_encode 3)) work /\
    work = audit_nat_events_work (snd (audit_nat_encode 3)) /\ work = 16.
Proof.
  destruct (audit_nat_encode_run_total 3) as [code [events [work Hrun]]].
  pose proof (audit_nat_encode_run_correct 3 code events work Hrun) as [_ [Hresult [Hwork _]]].
  rewrite <- Hresult; cbn [fst snd]; exists work; split; [exact Hrun|].
  split; [unfold audit_nat_events_work; exact Hwork|].
  assert (Hactual : audit_nat_events_work (snd (audit_nat_encode 3)) = 16) by (vm_compute;
    reflexivity).
  rewrite <- Hresult in Hactual; cbn [snd] in Hactual; unfold audit_nat_events_work in Hactual.
  lia.
Qed.
