(** * Counted prepared dense-map slots

    These observers retain exact universe lookups, numeric slot accesses and updates.
    For example, an outside key is looked up and rejected without modifying the slot map.
    Builds on: G4 collections semantics and shared map and encoding observers. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsDenseSet
  CollectionsAuditState
  CollectionsAuditEncoding
  CollectionsAuditMap.
Import List.ListNotations.

Inductive audit_slot_event (K V CE : Type) : Type :=
  | AuditSlotUniverseGet (key : K) (index : option N) (calls : list (audit_map_event K N CE))
  | AuditSlotAbstractGet (key : K) (value : option V) (calls : list (audit_map_event K V CE))
  | AuditSlotRead (index : N) (value : option V)
      (calls : list (audit_map_event N V audit_n_encoding_event))
  | AuditSlotWrite (index : N) (value : V) (calls : list (audit_map_event N V
    audit_n_encoding_event))
  | AuditSlotRemove (index : N) (calls : list (audit_map_event N V audit_n_encoding_event))
  | AuditSlotMapWrite (key : K) (value : V) (calls : list (audit_map_event K V CE))
  | AuditSlotCase (remaining : list K)
  | AuditSlotBatchIndex (remaining : list (option N))
  | AuditSlotEmit (key : K) (value : V).

Arguments AuditSlotUniverseGet {K V CE} _ _ _.
Arguments AuditSlotAbstractGet {K V CE} _ _ _.
Arguments AuditSlotRead {K V CE} _ _ _.
Arguments AuditSlotWrite {K V CE} _ _ _.
Arguments AuditSlotRemove {K V CE} _ _.
Arguments AuditSlotMapWrite {K V CE} _ _ _.
Arguments AuditSlotCase {K V CE} _.
Arguments AuditSlotBatchIndex {K V CE} _.
Arguments AuditSlotEmit {K V CE} _ _.

(** Direct prepared-slot lookup retains its one encoded-key map read. *)
Definition audit_prepare_slot {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (key : K) : option N * list (audit_slot_event K V CE) :=
  let '(index, calls) := audit_map_get enc key (dense_index u) in
  (index, [AuditSlotUniverseGet key index calls]).

Definition audit_slot_read {K V CE} (m : slot_map V) (index : N)
    : option V * list (audit_slot_event K V CE) :=
  let '(value, calls) := audit_map_get audit_N_encode index m in
  (value, [AuditSlotRead index value calls]).

(** Slot lookup reads the numeric map only after a successful universe lookup. *)
Definition audit_slot_lookup {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (m : slot_map V) (key : K) : option V * list (audit_slot_event K V CE) :=
  let '(index, universe_calls) := audit_map_get enc key (dense_index u) in
  match index with
  | None => (None, [AuditSlotUniverseGet key index universe_calls])
  | Some i =>
      let '(value, slot_calls) := audit_map_get audit_N_encode i m in
      (value, [AuditSlotUniverseGet key index universe_calls; AuditSlotRead i value slot_calls])
  end.

Definition audit_slot_update {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (m : slot_map V) (key : K) (value : V) : option (slot_map V) * list (audit_slot_event K V CE) :=
  let '(index, universe_calls) := audit_map_get enc key (dense_index u) in
  match index with
  | None => (None, [AuditSlotUniverseGet key index universe_calls])
  | Some i =>
      let '(out, calls) := audit_map_set audit_N_encode i value m in
      (Some out, [AuditSlotUniverseGet key index universe_calls; AuditSlotWrite i value calls])
  end.

Definition audit_slot_remove {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (m : slot_map V) (key : K) : option (slot_map V) * list (audit_slot_event K V CE) :=
  let '(index, universe_calls) := audit_map_get enc key (dense_index u) in
  match index with
  | None => (None, [AuditSlotUniverseGet key index universe_calls])
  | Some i =>
      let '(out, calls) := audit_map_remove audit_N_encode i m in
      (Some out, [AuditSlotUniverseGet key index universe_calls; AuditSlotRemove i calls])
  end.

(** Each key in the source universe is visited, including absent or malformed slots. *)
Fixpoint audit_slot_elements_from {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (m : slot_map V) (keys : list K)
    : list (K * V) * list (audit_slot_event K V CE) :=
  match keys with
  | [] => ([], [AuditSlotCase keys])
  | key :: rest =>
      let '(value, calls) := audit_slot_lookup enc u m key in
      let '(tail, events) := audit_slot_elements_from enc u m rest in
      match value with
      | None => (tail, AuditSlotCase keys :: calls ++ events)
      | Some v => ((key, v) :: tail, AuditSlotCase keys :: calls ++ AuditSlotEmit key v :: events)
      end
  end.

Definition audit_slot_elements {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (m : slot_map V) := audit_slot_elements_from enc u m (dense_keys u).

(** Batches preserve order, repeated keys and every optional-slot branch. *)
Fixpoint audit_prepare_slots {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (keys : list K) : list (option N) * list (audit_slot_event K V CE) :=
  match keys with
  | [] => ([], [AuditSlotCase keys])
  | key :: rest =>
      let '(index, calls) := @audit_prepare_slot K V CE enc u key in
      let '(tail, events) := audit_prepare_slots enc u rest in
      (index :: tail, AuditSlotCase keys :: calls ++ events)
  end.

Fixpoint audit_read_slots {K V CE} (m : slot_map V) (slots : list (option N))
    : list (option V) * list (audit_slot_event K V CE) :=
  match slots with
  | [] => ([], [AuditSlotBatchIndex slots])
  | None :: rest =>
      let '(tail, events) := audit_read_slots m rest in
      (None :: tail, AuditSlotBatchIndex slots :: events)
  | Some index :: rest =>
      let '(value, calls) := @audit_slot_read K V CE m index in
      let '(tail, events) := audit_read_slots m rest in
      (value :: tail, AuditSlotBatchIndex slots :: calls ++ events)
  end.

(** Conversion inspects the abstract lookup first and skips the universe read on a miss. *)
Fixpoint audit_slot_of_map_from {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (abstract : Map.t K V) (keys : list K) (state : slot_map V)
    : slot_map V * list (audit_slot_event K V CE) :=
  match keys with
  | [] => (state, [AuditSlotCase keys])
  | key :: rest =>
      let '(value, value_calls) := audit_map_get enc key abstract in
      let prefix := [AuditSlotCase keys; AuditSlotAbstractGet key value value_calls] in
      match value with
      | None =>
          let '(out, events) := audit_slot_of_map_from enc u abstract rest state in
          (out, prefix ++ events)
      | Some v =>
          let '(index, index_calls) := audit_map_get enc key (dense_index u) in
          let prefix := prefix ++ [AuditSlotUniverseGet key index index_calls] in
          match index with
          | None =>
              let '(out, events) := audit_slot_of_map_from enc u abstract rest state in
              (out, prefix ++ events)
          | Some i =>
              let '(next, writes) := audit_map_set audit_N_encode i v state in
              let '(out, events) := audit_slot_of_map_from enc u abstract rest next in
              (out, prefix ++ [AuditSlotWrite i v writes] ++ events)
          end
      end
  end.

Definition audit_slot_of_map {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (abstract : Map.t K V) :=
  audit_slot_of_map_from enc u abstract (dense_keys u) Map.empty.

(** Conversion to a standard map processes each emitted binding in source list order. *)
Fixpoint audit_slot_bindings_to_map {K V CE} (enc : K -> positive * list CE)
    (bindings : list (K * V)) (state : Map.t K V) : Map.t K V * list (audit_slot_event K V CE) :=
  match bindings with
  | [] => (state, [])
  | (key, value) :: rest =>
      let '(next, calls) := audit_map_set enc key value state in
      let '(out, events) := audit_slot_bindings_to_map enc rest next in
      (out, AuditSlotMapWrite key value calls :: events)
  end.

Definition audit_slot_to_map {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (m : slot_map V) : Map.t K V * list (audit_slot_event K V CE) :=
  let '(bindings, first) := audit_slot_elements enc u m in
  let '(result, second) := audit_slot_bindings_to_map enc bindings Map.empty in
  (result, first ++ second).

(** A token records the actual key and index returned by its single universe lookup. *)
Definition audit_dense_token_prepare {K V CE} (enc : K -> positive * list CE)
    (original : encoding K) (u : dense_universe K) (key : K)
    : option (dense_slot_token original u) * list (audit_slot_event K V CE) :=
  let '(index, calls) := audit_map_get enc key (dense_index u) in
  (match index with
  | None => None
  | Some i => Some (DenseSlotToken key i)
  end,
    [AuditSlotUniverseGet key index calls]).

Definition audit_dense_token_read {K V CE} (original : encoding K) (u : dense_universe K)
    (token : dense_slot_token original u) (m : slot_map V)
    : option V * list (audit_slot_event K V CE) :=
  let index := dense_token_index token in
  let '(value, calls) := audit_map_get audit_N_encode index m in
  (value, [AuditSlotRead index value calls]).

(** * Future exact-result obligations *)

Definition audit_slot_lookup_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V) key,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_lookup enc u m key) = slot_lookup original u m key.

(** Discarding the prepare slot events recovers the corresponding original operation under its
  premises. *)
Definition audit_prepare_slot_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u key,
    fst (enc key) = encode original key ->
    fst (@audit_prepare_slot K V CE enc u key) = prepare_slot original u key.

(** Discarding the slot read events recovers the corresponding original operation under its
  premises. *)
Definition audit_slot_read_erases_statement : Prop :=
  forall K V CE (m : slot_map V) index, fst (@audit_slot_read K V CE m index) = slot_read m index.

(** Discarding the prepare slots events recovers the corresponding original operation under its
  premises. *)
Definition audit_prepare_slots_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u keys,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (@audit_prepare_slots K V CE enc u keys) = prepare_slots original u keys.

(** Discarding the read slots events recovers the corresponding original operation under its
  premises. *)
Definition audit_read_slots_erases_statement : Prop :=
  forall K V CE (m : slot_map V) slots, fst (@audit_read_slots K V CE m slots) = read_slots m slots.

(** Discarding the slot update events recovers the corresponding original operation under its
  premises. *)
Definition audit_slot_update_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V) key
    value,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_update enc u m key value) = slot_update original u m key value.

(** Discarding the slot remove events recovers the corresponding original operation under its
  premises. *)
Definition audit_slot_remove_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V) key,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_remove enc u m key) = slot_remove original u m key.

(** Discarding the slot elements events recovers the corresponding original operation under its
  premises. *)
Definition audit_slot_elements_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V),
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_elements enc u m) = slot_elements original u m.

(** Discarding the slot of map events recovers the corresponding original operation under its
  premises. *)
Definition audit_slot_of_map_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (abstract : Map.t K V),
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_of_map enc u abstract) = slot_of_map original u abstract.

(** Discarding the slot to map events recovers the corresponding original operation under its
  premises. *)
Definition audit_slot_to_map_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V),
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_to_map enc u m) = slot_to_map original u m.

(** Discarding the dense token prepare events recovers the corresponding original operation
  under its premises. *)
Definition audit_dense_token_prepare_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u key,
    fst (enc key) = encode original key ->
    fst (@audit_dense_token_prepare K V CE enc original u key) = dense_token_prepare original u key.

(** Discarding the dense token read events recovers the corresponding original operation under
  its premises. *)
Definition audit_dense_token_read_erases_statement : Prop :=
  forall K V CE (original : encoding K) u (token : dense_slot_token original u) (m : slot_map V),
    fst (@audit_dense_token_read K V CE original u token m) = dense_token_read original u token m.

(** * Fixed nested source work and input-derived operation budgets *)

Fixpoint audit_slot_source_work {K V CE} (enc_work : list CE -> nat)
    (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotUniverseGet _ _ calls :: rest => 1 + audit_map_source_work enc_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotAbstractGet _ _ calls :: rest => 1 + audit_map_source_work enc_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotRead _ _ calls :: rest => 1 + audit_map_source_work audit_N_encoding_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotWrite _ _ calls :: rest => 1 + audit_map_source_work audit_N_encoding_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotRemove _ calls :: rest => 1 + audit_map_source_work audit_N_encoding_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotMapWrite _ _ calls :: rest => 2 + audit_map_source_work enc_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotCase _ :: rest => 1 + audit_slot_source_work enc_work rest
  | AuditSlotBatchIndex _ :: rest => 1 + audit_slot_source_work enc_work rest
  | AuditSlotEmit _ _ :: rest => 1 + audit_slot_source_work enc_work rest
  end.

Definition audit_slot_key_get_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (key : K) : nat :=
  6 + enc_work (snd (enc key)) + 5 * Pos.size_nat (fst (enc key)).

Definition audit_slot_index_get_budget (index : N) : nat :=
  6 + audit_N_encoding_work (snd (audit_N_encode index)) +
    5 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_index_update_budget (index : N) : nat :=
  3 + audit_N_encoding_work (snd (audit_N_encode index)) +
    16 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_lookup_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_budget enc enc_work key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_get_budget i
    end.

Definition audit_slot_update_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_budget enc enc_work key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_update_budget i
    end.

(** The slot lookup work is bounded by [audit_slot_lookup_budget]. *)
Definition audit_slot_lookup_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V) key,
    audit_slot_source_work enc_work (snd (audit_slot_lookup enc u m key)) <=
      audit_slot_lookup_budget enc enc_work u key.

(** The slot update work is bounded by [audit_slot_update_budget]. *)
Definition audit_slot_update_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V) key value,
    audit_slot_source_work enc_work (snd (audit_slot_update enc u m key value)) <=
      audit_slot_update_budget enc enc_work u key.

(** The slot remove work is bounded by [audit_slot_update_budget]. *)
Definition audit_slot_remove_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V) key,
    audit_slot_source_work enc_work (snd (audit_slot_remove enc u m key)) <=
      audit_slot_update_budget enc enc_work u key.

Fixpoint audit_slot_elements_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 2 + audit_slot_lookup_budget enc enc_work u key +
      audit_slot_elements_budget enc enc_work u rest
  end.

(** The slot elements work is bounded by [audit_slot_elements_budget]. *)
Definition audit_slot_elements_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V),
    audit_slot_source_work enc_work (snd (audit_slot_elements enc u m)) <=
      audit_slot_elements_budget enc enc_work u (dense_keys u).

(** This input bound permits both probes; the source skips the second on a miss. *)
Fixpoint audit_slot_of_map_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      1 + 2 * audit_slot_key_get_budget enc enc_work key +
      (match fst (audit_map_get enc key (dense_index u)) with
       | None => 0
       | Some i => audit_slot_index_update_budget i
       end) + audit_slot_of_map_budget enc enc_work u rest
  end.

(** The slot of map work is bounded by [audit_slot_of_map_budget]. *)
Definition audit_slot_of_map_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (abstract : Map.t K V),
    audit_slot_source_work enc_work (snd (audit_slot_of_map enc u abstract)) <=
      audit_slot_of_map_budget enc enc_work u (dense_keys u).

Fixpoint audit_slot_bindings_budget {K V CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (bindings : list (K * V)) : nat :=
  match bindings with
  | [] => 0
  | (key, _) :: rest => 4 + enc_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
      audit_slot_bindings_budget enc enc_work rest
  end.

(** Slot-to-map work is bounded by the element and resulting binding budgets. *)
Definition audit_slot_to_map_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V),
    audit_slot_source_work enc_work (snd (audit_slot_to_map enc u m)) <=
      audit_slot_elements_budget enc enc_work u (dense_keys u) +
      audit_slot_bindings_budget enc enc_work (fst (audit_slot_elements enc u m)).

(** The dense token prepare work is bounded by [audit_slot_key_get_budget]. *)
Definition audit_dense_token_prepare_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work (original : encoding K) u key,
    audit_slot_source_work enc_work (snd (@audit_dense_token_prepare K V CE enc original u key)) <=
      audit_slot_key_get_budget enc enc_work key.

(** The dense token read work is bounded by [audit_slot_index_get_budget]. *)
Definition audit_dense_token_read_source_bound_statement : Prop :=
  forall K V CE enc_work (original : encoding K) u (token : dense_slot_token original u) (m :
    slot_map V),
    audit_slot_source_work enc_work (snd (@audit_dense_token_read K V CE original u token m)) <=
      audit_slot_index_get_budget (dense_token_index token).

(** The prepare slot work is bounded by [audit_slot_key_get_budget]. *)
Definition audit_prepare_slot_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u key,
    audit_slot_source_work enc_work (snd (@audit_prepare_slot K V CE enc u key)) <=
      audit_slot_key_get_budget enc enc_work key.

(** The slot read work is bounded by [audit_slot_index_get_budget]. *)
Definition audit_slot_read_source_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) index,
    audit_slot_source_work enc_work (snd (@audit_slot_read K V CE m index)) <=
      audit_slot_index_get_budget index.

Fixpoint audit_prepare_slots_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 1 + audit_slot_key_get_budget enc enc_work key +
      audit_prepare_slots_budget enc enc_work rest
  end.

Fixpoint audit_read_slots_budget (slots : list (option N)) : nat :=
  match slots with
  | [] => 1
  | None :: rest => 1 + audit_read_slots_budget rest
  | Some index :: rest => 1 + audit_slot_index_get_budget index + audit_read_slots_budget rest
  end.

(** The prepare slots work is bounded by [audit_prepare_slots_budget]. *)
Definition audit_prepare_slots_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u keys,
    audit_slot_source_work enc_work (snd (@audit_prepare_slots K V CE enc u keys)) <=
      audit_prepare_slots_budget enc enc_work keys.

(** The read slots work is bounded by [audit_read_slots_budget]. *)
Definition audit_read_slots_source_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) slots,
    audit_slot_source_work enc_work (snd (@audit_read_slots K V CE m slots)) <=
      audit_read_slots_budget slots.

(** The original batch contract counts every present slot and its actual binary code. *)
Fixpoint audit_slot_read_calls {K V CE} (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotRead _ _ _ :: rest => S (audit_slot_read_calls rest)
  | _ :: rest => audit_slot_read_calls rest
  end.

Fixpoint audit_slot_read_key_bits {K V CE} (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotRead index _ _ :: rest =>
      Pos.size_nat (encode N_encoding index) + audit_slot_read_key_bits rest
  | _ :: rest => audit_slot_read_key_bits rest
  end.

(** Counted batch reads preserve slot order and count the present slots. *)
Definition audit_read_slots_observation_statement : Prop :=
  forall K V CE (m : slot_map V) slots,
    let '(out, events) := @audit_read_slots K V CE m slots in
    out = read_slots m slots /\ length out = length slots /\
    audit_slot_read_calls events =
      length (filter (fun slot => match slot with
      | Some _ => true
      | None => false
      end) slots) /\
    audit_slot_read_key_bits events =
      fold_right (fun slot bits => match slot with
        | Some i => Pos.size_nat (encode N_encoding i) + bits
        | None => bits
        end) 0 slots.
