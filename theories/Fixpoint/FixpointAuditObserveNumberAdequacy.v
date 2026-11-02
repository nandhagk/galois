(** * Numbered observation table adequacy

    The counted table and label operations preserve the original occurrence lookup.
    For example, a missing label retains the supplied fallback and its lookup cost.
    Builds on: FixpointAuditObserveNumber and collection source adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditMapAdequacy CollectionsAuditEncoding CollectionsAuditEncodingAdequacy
  CollectionsAuditEncoderBudget CollectionsAuditEncoderBudgetAdequacy.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditObserveNumber.
Import List.ListNotations.

(** * Persistent table and lookup costs *)

Lemma fx_number_map_work_app C (left right : list (audit_map_event nat C
  audit_nat_encoding_event)) :
  audit_map_source_work audit_nat_events_work (left ++ right) =
    audit_map_source_work audit_nat_events_work left + audit_map_source_work audit_nat_events_work
      right.
Proof.
  induction left as [|event rest IH]; cbn [app audit_map_source_work]; [reflexivity|].
  destruct event; cbn [audit_map_source_work]; rewrite IH; lia.
Qed.

(** Numbering preserves every occurrence and charges its actual recursive map write. *)
Theorem fx_observe_number_source : fx_observe_number_source_statement.
Proof.
  intros C next cs; revert next; induction cs as [|c rest IH]; intro next.
  - cbn [fx_observe_number observation_number audit_map_source_work fx_observe_number_budget];
      split; [reflexivity|lia].
  - specialize (IH (S next)).
    destruct (fx_observe_number (S next) rest) as [table later] eqn:Htail.
    cbn in IH; destruct IH as [Htable Hlater].
    pose proof (audit_nat_encode_erases next) as Hencode.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 audit_base_encoder_input_bound)))) next) as Hnat.
    pose proof (audit_map_set_erases nat C audit_nat_encoding_event audit_nat_encode nat_encoding
      next c table Hencode) as Hset.
    pose proof (audit_map_set_source_work_bound nat C audit_nat_encoding_event audit_nat_encode
      audit_nat_events_work next c table) as Hwork.
    destruct (audit_map_set audit_nat_encode next c table) as [out events] eqn:Hrun.
    cbn in Hset, Hwork.
    cbn [fx_observe_number fx_observe_number_budget observation_number]; rewrite Htail, Hrun.
    split.
    + now rewrite Hset, Htable.
    + rewrite fx_number_map_work_app.
      rewrite Hencode in Hwork; unfold audit_nat_events_work in Hnat; lia.
Qed.

(** Label lookup preserves fallback and pays for the actual unary encoding and trie traversal. *)
Theorem fx_observe_label_source : fx_observe_label_source_statement.
Proof.
  intros C fallback table i.
  pose proof (audit_nat_encode_erases i) as Hencode.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 audit_base_encoder_input_bound)))) i) as Hnat.
  pose proof (audit_map_get_erases nat C audit_nat_encoding_event audit_nat_encode nat_encoding
    i table Hencode) as Hget.
  pose proof (audit_map_get_source_work_bound nat C audit_nat_encoding_event audit_nat_encode
    audit_nat_events_work i table) as Hwork.
  destruct (audit_map_get audit_nat_encode i table) as [out events] eqn:Hrun.
  cbn in Hget, Hwork; rewrite Hencode in Hwork.
  unfold fx_observe_label, observation_label; rewrite Hrun, <- Hget.
  unfold audit_nat_events_work, audit_nat_input_budget in Hnat;
    unfold fx_observe_label_budget; destruct out; cbn in *; split; try reflexivity; nia.
Qed.
