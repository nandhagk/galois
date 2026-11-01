(** * Candidate dense preparation and slot observations

    These finite checks compare preparation and nested conversion with the source operations.
    For example, an absent abstract value skips the universe lookup.
    Builds on: CollectionsAuditDense, CollectionsAuditDenseSlots and their input budgets. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsDenseSet
  CollectionsAuditState CollectionsAuditEncoding CollectionsAuditDense
  CollectionsAuditDenseSlots CollectionsAuditDenseInput CollectionsAuditPrepared.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** Preparation preserves first occurrence order and the original numeric index. *)
Example audit_dense_prepare_observation :
  let input := [1%positive; 2%positive; 1%positive] in
  let result := audit_dense_prepare audit_positive_encode input in
  fst result = dense_prepare positive_encoding input /\
  dense_keys (fst result) = [1%positive; 2%positive].
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** Count the universe lookups retained in a slot event list. *)
Fixpoint audit_slot_universe_reads {K V CE} (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotUniverseGet _ _ _ :: rest => S (audit_slot_universe_reads rest)
  | _ :: rest => audit_slot_universe_reads rest
  end.

(** A missing abstract binding skips the second lookup in the actual nested match. *)
Example audit_dense_strict_conversion_observation :
  let universe := dense_prepare positive_encoding [1%positive] in
  let result := audit_slot_of_map audit_positive_encode universe (@Map.empty positive nat) in
  fst result = slot_of_map positive_encoding universe (@Map.empty positive nat) /\
  audit_slot_universe_reads (snd result) = 0.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** Empty preparation preserves its empty universe and zero length. *)
Example audit_dense_empty_observation :
  let u := fst (audit_dense_prepare audit_positive_encode []) in
  dense_keys u = [] /\ dense_length u = 0%N.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Numeric conversion crosses zero and a binary carry without changing the result. *)
Example audit_dense_numeric_boundaries :
  fst (audit_dense_N_succ 0%N) = 1%N /\ fst (audit_dense_N_succ 7%N) = 8%N /\
  fst (audit_dense_N_of_nat 0) = 0%N /\ fst (audit_dense_N_of_nat 8) = 8%N.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Present, missing and duplicate keys retain their order through preparation and reads. *)
Example audit_dense_batch_observation :
  let u := dense_prepare positive_encoding [1%positive; 2%positive; 1%positive] in
  let m := Map.set N_encoding 0%N 42 (@Map.empty N nat) in
  let slots := fst (@audit_prepare_slots positive nat (audit_basic_encoding_event positive)
    audit_positive_encode u
    [1%positive; 3%positive; 1%positive; 2%positive]) in
  slots = [Some 0%N; None; Some 0%N; Some 1%N] /\
  fst (@audit_read_slots positive nat (audit_basic_encoding_event positive) m slots) =
    [Some 42; None; Some 42; None].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Updating and removing a present key threads the returned persistent slot maps. *)
Example audit_dense_update_remove_observation :
  let u := dense_prepare positive_encoding [1%positive] in
  let empty := @Map.empty N nat in
  match audit_slot_update audit_positive_encode u empty 1%positive 17 with
  | (Some updated, _) =>
      fst (audit_slot_lookup audit_positive_encode u updated 1%positive) = Some 17 /\
      match audit_slot_remove audit_positive_encode u updated 1%positive with
      | (Some removed, _) =>
          fst (audit_slot_lookup audit_positive_encode u removed 1%positive) = None /\
          fst (audit_slot_update audit_positive_encode u removed 2%positive 9) = None
      | _ => False
      end
  | _ => False
  end.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Conversions preserve a present binding and omit a missing one. *)
Example audit_dense_conversion_observation :
  let u := dense_prepare positive_encoding [1%positive; 2%positive] in
  let original := Map.set positive_encoding 1%positive 42 (@Map.empty positive nat) in
  let slots := fst (audit_slot_of_map audit_positive_encode u original) in
  let restored := fst (audit_slot_to_map audit_positive_encode u slots) in
  Map.get positive_encoding 1%positive restored = Some 42 /\
  Map.get positive_encoding 2%positive restored = None /\
  fst (audit_slot_elements audit_positive_encode u slots) = [(1%positive, 42)].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Preparing a key once and reusing it performs no subsequent encoding. *)
Example audit_prepared_reuse_observation :
  let key := fst (@audit_prepare_key positive nat (audit_basic_encoding_event positive)
    audit_positive_encode 2%positive) in
  let m := fst (@audit_prepared_update positive nat (audit_basic_encoding_event positive)
    key 19 Map.empty) in
  fst (@audit_prepared_lookup positive nat (audit_basic_encoding_event positive) key m) = Some 19 /\
  audit_prepared_encoder_calls
    (snd (@audit_prepared_lookup positive nat (audit_basic_encoding_event positive) key m)) = 0 /\
  fst (@audit_prepared_lookup positive nat (audit_basic_encoding_event positive) key
    (fst (@audit_prepared_remove positive nat (audit_basic_encoding_event positive) key m))) = None.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Concrete work checks cover empty, duplicate, missing and present inputs. *)
Example audit_dense_work_checks :
  let u := dense_prepare positive_encoding [1%positive; 2%positive; 1%positive] in
  let m := Map.set N_encoding 0%N 42 (@Map.empty N nat) in
  let enc := audit_positive_encode in
  let work := audit_basic_encoding_work in
  Nat.leb (audit_dense_prepare_work work (snd (audit_dense_prepare enc [])))
    (audit_dense_prepare_input_budget enc (fun _ => 1) []) = true /\
  Nat.leb (audit_dense_prepare_work work (snd (audit_dense_prepare enc [1%positive; 1%positive])))
    (audit_dense_prepare_input_budget enc (fun _ => 1) [1%positive; 1%positive]) = true /\
  Nat.leb (audit_slot_source_work work (snd (audit_slot_lookup enc u m 3%positive)))
    (audit_slot_lookup_input_budget enc (fun _ => 1) u 3%positive) = true /\
  Nat.leb (audit_slot_source_work work (snd (audit_slot_lookup enc u m 1%positive)))
    (audit_slot_lookup_input_budget enc (fun _ => 1) u 1%positive) = true /\
  Nat.leb (audit_slot_source_work work (snd (audit_slot_update enc u m 1%positive 7)))
    (audit_slot_update_input_budget enc (fun _ => 1) u 1%positive) = true /\
  Nat.leb (audit_slot_source_work work (snd (audit_slot_remove enc u m 1%positive)))
    (audit_slot_update_input_budget enc (fun _ => 1) u 1%positive) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Token preparation and reading use the actual stored index and reject missing keys. *)
Example audit_dense_token_observation :
  let u := dense_prepare positive_encoding [1%positive] in
  let m := Map.set N_encoding 0%N 42 (@Map.empty N nat) in
  match @audit_dense_token_prepare positive nat (audit_basic_encoding_event positive)
    audit_positive_encode positive_encoding u 1%positive with
  | (Some token, _) =>
      fst (@audit_dense_token_read positive nat (audit_basic_encoding_event positive)
        positive_encoding u token m) = Some 42 /\
      fst (@audit_dense_token_prepare positive nat (audit_basic_encoding_event positive)
        audit_positive_encode positive_encoding u 2%positive) = None
  | _ => False
  end.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Input-budget checks cover conversions, batches, direct reads and key preparation. *)
Example audit_dense_additional_work_checks :
  let u := dense_prepare positive_encoding [1%positive; 2%positive] in
  let m := Map.set N_encoding 0%N 42 (@Map.empty N nat) in
  let abstract := Map.set positive_encoding 1%positive 42 (@Map.empty positive nat) in
  let enc := audit_positive_encode in
  let work := audit_basic_encoding_work in
  let budget := fun _ : positive => 1 in
  let keys := [1%positive; 3%positive; 1%positive] in
  let slots := [Some 0%N; None; Some 1%N] in
  Nat.leb (audit_slot_source_work work (snd (audit_slot_elements enc u m)))
    (audit_slot_elements_input_budget enc budget u (dense_keys u)) = true /\
  Nat.leb (audit_slot_source_work work (snd (audit_slot_of_map enc u abstract)))
    (audit_slot_of_map_input_budget enc budget u (dense_keys u)) = true /\
  Nat.leb (audit_slot_source_work work (snd (audit_slot_to_map enc u m)))
    (audit_slot_elements_input_budget enc budget u (dense_keys u) +
      audit_slot_bindings_input_budget enc budget (fst (audit_slot_elements enc u m))) = true /\
  Nat.leb (audit_slot_source_work work
    (snd (@audit_prepare_slots positive nat (audit_basic_encoding_event positive) enc u keys)))
    (audit_prepare_slots_input_budget enc budget keys) = true /\
  Nat.leb (audit_slot_source_work work
    (snd (@audit_read_slots positive nat (audit_basic_encoding_event positive) m slots)))
    (audit_read_slots_input_budget slots) = true /\
  Nat.leb (audit_slot_source_work work
    (snd (@audit_prepare_slot positive nat (audit_basic_encoding_event positive) enc u 1%positive)))
    (audit_slot_key_get_input_budget enc budget 1%positive) = true /\
  Nat.leb (audit_slot_source_work work
    (snd (@audit_slot_read positive nat (audit_basic_encoding_event positive) m 0%N)))
    (audit_slot_index_get_input_budget 0%N) = true /\
  Nat.leb (audit_prepared_source_work work
    (snd (@audit_prepare_key positive nat (audit_basic_encoding_event positive) enc 1%positive)))
    (1 + budget 1%positive) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Token work checks cover both present and missing keys and a numeric read. *)
Example audit_dense_token_work_checks :
  let u := dense_prepare positive_encoding [1%positive] in
  let m := Map.set N_encoding 0%N 42 (@Map.empty N nat) in
  let work := audit_basic_encoding_work in
  let budget := fun _ : positive => 1 in
  let prepared := @audit_dense_token_prepare positive nat (audit_basic_encoding_event positive)
    audit_positive_encode positive_encoding u 1%positive in
  Nat.leb (audit_slot_source_work work (snd prepared))
    (audit_slot_key_get_input_budget audit_positive_encode budget 1%positive) = true /\
  Nat.leb (audit_slot_source_work work
    (snd (@audit_dense_token_prepare positive nat (audit_basic_encoding_event positive)
      audit_positive_encode positive_encoding u 2%positive)))
    (audit_slot_key_get_input_budget audit_positive_encode budget 2%positive) = true /\
  match fst prepared with
  | Some token =>
      Nat.leb (audit_slot_source_work work
        (snd (@audit_dense_token_read positive nat (audit_basic_encoding_event positive)
          positive_encoding u token m)))
        (audit_slot_index_get_input_budget (dense_token_index token)) = true
  | None => False
  end.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.
