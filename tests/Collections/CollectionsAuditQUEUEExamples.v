(** * Queue trace examples

    These examples exercise recorded priority-queue operations and encoder receipts.
    For example, zero fuel records a step without returning an entry.
    Builds on: CollectionsAuditQueue and CollectionsHeap. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsHeap CollectionsAuditQueue
  CollectionsAuditQueueAdequacy.
Import List.ListNotations.

(** * Captured queue executions *)

Definition receipt_encoder (key : nat) : positive * list nat :=
  (encode nat_encoding key, [key]).

(** Zero fuel returns no entry and records one step. *)
Example queue_zero_fuel_trace :
  queue_pop_fuel nat_encoding 0 [] (PQueue.live (@PQueue.empty nat)) 0 =
    (None, [QFuelStep]).
Proof.
  reflexivity.
Qed.

(** Insertion into an empty queue captures the three actual encoder calls. *)
Example queue_new_key_receipts :
  let '(_, events) := audit_queue_recorded_push receipt_encoder 3%positive 0
    (@PQueue.empty nat) in
  map (fun event => snd (snd event)) events =
    [[(1%positive, [0])]; [(1%positive, [0])]; []; [(1%positive, [0])]].
Proof.
  reflexivity.
Qed.

(** A repeated worse priority leaves the original queue unchanged. *)
Example queue_worse_priority_retained :
  let first := fst (queue_push nat_encoding 1%positive 0 (@PQueue.empty nat)) in
  fst (queue_push nat_encoding 3%positive 0 first) = first.
Proof.
  reflexivity.
Qed.

(** A stale entry consumes one unit of fuel without returning an entry. *)
Example queue_stale_boundary_fuel :
  let first := fst (queue_push nat_encoding 3%positive 0 (@PQueue.empty nat)) in
  let lowered := fst (queue_push nat_encoding 1%positive 0 first) in
  let popped := fst (queue_pop nat_encoding lowered) in
  match popped with
  | Some (_, _, rest) => fst (queue_pop_fuel nat_encoding 1 (PQueue.pending rest)
      (PQueue.live rest) (PQueue.live_count rest)) = None
  | None => False
  end.
Proof.
  reflexivity.
Qed.

(** A live pop returns its priority and key and records both encoder receipts. *)
Example queue_pop_receipts :
  let state := fst (queue_push nat_encoding 2%positive 0 (@PQueue.empty nat)) in
  let '(result, events) := audit_queue_recorded_pop receipt_encoder state in
  match result with
  | Some (priority, key, _) =>
    priority = 2%positive /\ key = 0 /\
    map (fun event => snd (snd event)) events =
      [[]; []; []; []; []; []; [(1%positive, [0])]; []; []; [(1%positive, [0])]]
  | None => False
  end.
Proof.
  repeat split; reflexivity.
Qed.

(** Both recorded encoder calls have positive body work on a successful pop. *)
Example queue_pop_body_work :
  let state := fst (queue_push nat_encoding 2%positive 0 (@PQueue.empty nat)) in
  let '(_, events) := audit_queue_recorded_pop receipt_encoder state in
  audit_queue_recorded_body_work (fun _ => 1) events = 4.
Proof.
  reflexivity.
Qed.

(** The actual successful-pop receipt charges nonzero internal source work. *)
Example queue_pop_source_work :
  let state := fst (queue_push nat_encoding 2%positive 0 (@PQueue.empty nat)) in
  let '(_, events) := audit_queue_recorded_pop receipt_encoder state in
  0 < audit_queue_recorded_internal_source_work events.
Proof.
  vm_compute; lia.
Qed.

(** A second insertion records the two actual entries passed to the heap comparison. *)
Example queue_link_comparison_operands :
  let first := fst (queue_push nat_encoding 3%positive 0 (@PQueue.empty nat)) in
  let '(_, events) := queue_push nat_encoding 2%positive 1 first in
  queue_compare_calls events =
    [(2%positive, 3%positive); (2%positive, 3%positive); (2%positive, 1%positive)].
Proof.
  reflexivity.
Qed.

(** A stale entry uses the only fuel step before another live key can be returned. *)
Example queue_stale_then_live_boundary :
  let first := fst (queue_push nat_encoding 3%positive 0 (@PQueue.empty nat)) in
  let lowered := fst (queue_push nat_encoding 1%positive 0 first) in
  let two_keys := fst (queue_push nat_encoding 5%positive 1 lowered) in
  match fst (queue_pop nat_encoding two_keys) with
  | Some (_, _, rest) =>
    fst (queue_pop_fuel nat_encoding 1 (PQueue.pending rest)
      (PQueue.live rest) (PQueue.live_count rest)) = None /\
    match fst (queue_pop_fuel nat_encoding 2 (PQueue.pending rest)
      (PQueue.live rest) (PQueue.live_count rest)) with
    | Some (priority, key, _) => priority = 5%positive /\ key = 1
    | None => False
    end
  | None => False
  end.
Proof.
  repeat split; reflexivity.
Qed.

(** The external callback exposes its actual body and charges one unit for it. *)
Definition receipt_source (key : nat) (code : positive) (body : list nat) (work : nat) : Prop :=
  code = encode nat_encoding key /\ body = [key] /\ work = 1.

(** The receipt encoder satisfies the external adapter on every key. *)
Lemma receipt_encoder_adapter :
  audit_queue_external_encoder_adapter nat_encoding receipt_encoder (fun _ => 1)
    receipt_source (fun _ => 1).
Proof.
  constructor.
  - intros key; reflexivity.
  - intros key code body Hencode; unfold receipt_encoder in Hencode.
    inversion Hencode; subst code body; cbn; repeat split; reflexivity.
Qed.

(** The external push contract applies to a nonempty queue and actual callback. *)
Example queue_external_push_nonempty :
  let first := fst (queue_push nat_encoding 3%positive 0 (@PQueue.empty nat)) in
  let '(result, events) := audit_queue_push_nested (audit_queue_capture_encoder receipt_encoder)
    2%positive 1 first in
  result = PQueue.push nat_encoding 2%positive 1 first /\
  audit_queue_recorded_full_source_work (fun _ => 1) events <=
    audit_queue_full_input_budget nat_encoding 1 (PQueue.pending first) (PQueue.live first)
      [1] [2%positive] + audit_queue_recorded_encoder_budget (fun _ => 1) events.
Proof.
  exact (audit_queue_external_encoder_push_correct nat nat nat_encoding receipt_encoder
    (fun _ => 1) receipt_source (fun _ => 1) 2%positive 1
    (fst (queue_push nat_encoding 3%positive 0 (@PQueue.empty nat))) receipt_encoder_adapter).
Qed.

(** The external pop contract applies to a nonempty queue with an actual receipt encoder. *)
Example queue_external_pop_nonempty :
  let state := fst (queue_push nat_encoding 2%positive 0 (@PQueue.empty nat)) in
  let '(result, events) := audit_queue_pop_nested
    (audit_queue_capture_encoder receipt_encoder) state in
  result = PQueue.pop nat_encoding state /\
  audit_queue_recorded_full_source_work (fun _ => 1) events <=
    audit_queue_full_input_budget nat_encoding (PQueue.pending_count state) (PQueue.pending state)
      (PQueue.live state) [] [] + audit_queue_recorded_encoder_budget (fun _ => 1) events.
Proof.
  exact (audit_queue_external_encoder_pop_correct nat nat nat_encoding receipt_encoder
    (fun _ => 1) receipt_source (fun _ => 1)
    (fst (queue_push nat_encoding 2%positive 0 (@PQueue.empty nat))) receipt_encoder_adapter).
Qed.
