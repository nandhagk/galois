(** * Rewrite audit model examples

    These computed examples exercise positive decisions, rebuild receipts, and pending queues.
    For example, inserting the pair (1, 2) twice leaves one pair to pop.
    Builds on: Rewrite audit queue models and Collections maps. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Rewrite Require Import RewriteSyntax RewriteEgraph RewriteAuditQueueReference
  RewriteAuditQueueKernel RewriteAuditQueuePositive RewriteAuditQueueRebuild.
Import List.ListNotations.

Definition models_fixture_adapter : rw_queue_encoder_adapter positive :=
  RwQueueEncoderAdapter (fun p => (p, 1)).

Definition models_fixture_graph : rw_graph positive positive positive :=
  RwGraph [1%positive] [1%positive]
    (Map.set positive_encoding 1%positive 1%positive Map.empty)
    (Map.set positive_encoding 1%positive 1%positive Map.empty)
    (Map.set positive_encoding 1%positive (1%positive, RWNVar 1%positive 1%positive) Map.empty).

Example models_positive_decision_mismatch :
  fst (rw_rq_decision_atomic 7%positive 2%positive) = false /\
  length (snd (rw_rq_decision_build 7%positive)) = 8.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

Example models_rebuild_nonempty :
  let source := rw_rq_rebuild_source models_fixture_adapter models_fixture_adapter
    models_fixture_adapter models_fixture_graph in
  rw_roots (rw_rq_value source) = [1%positive] /\
  0 < length (rw_rq_receipts source) /\
  rw_rq_receipts_work (rw_rq_receipts source) <= rw_rq_receipts_budget (rw_rq_receipts source).
Proof.
  vm_compute.
  repeat split; try reflexivity.
  all: lia.
Qed.

Example models_pending_insert_and_pop :
  let pair := (1%positive, 2%positive) in
  let queue := rw_pending_insert pair (rw_pending_insert pair rw_pending_empty) in
  rw_pending_sequence queue = [pair] /\
  option_map (fun result => (fst result, rw_pending_sequence (snd result)))
    (rw_pending_pop queue) = Some (pair, []).
Proof.
  vm_compute.
  split; reflexivity.
Qed.
