(** * Whole dense and prepared-key input budgets

    These recurrences close every internal binary and unary encoder at its original operand.
    For example, a successful conversion pays both probes and its fixed numeric slot write.
    Builds on: dense source bodies, concrete encoder budgets and actual foreign callback
      adapters. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet
  CollectionsAuditState
  CollectionsAuditCallback
  CollectionsAuditEncoding
  CollectionsAuditEncoderBudget
  CollectionsAuditMap
  CollectionsAuditPrepared
  CollectionsAuditDense
  CollectionsAuditDenseSlots.
Import List.ListNotations.

Fixpoint audit_dense_unique_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 10 + 2 * encoder_budget key + 21 * Pos.size_nat (fst (enc key)) +
      audit_dense_unique_input_budget enc encoder_budget rest
  end.

Fixpoint audit_dense_number_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) (index : N) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      let next := N.succ index in
      5 + audit_N_input_budget index + encoder_budget key + 16 * Pos.size_nat (fst (enc key)) +
        audit_dense_number_input_budget enc encoder_budget rest next
  end.

Definition audit_dense_prepare_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) : nat :=
  let unique := fst (audit_dense_unique enc FinSet.empty keys) in
  audit_dense_unique_input_budget enc encoder_budget keys + audit_dense_number_input_budget enc
    encoder_budget unique 0%N +
    2 + List.length unique +
    (match length unique with
    | 0 => 0
    | S rest => audit_nat_input_budget rest
    end).

Definition audit_slot_key_get_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (key : K) : nat :=
  6 + encoder_budget key + 5 * Pos.size_nat (fst (enc key)).

Definition audit_slot_index_get_input_budget (index : N) : nat :=
  6 + audit_N_input_budget index +
    5 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_index_update_input_budget (index : N) : nat :=
  3 + audit_N_input_budget index +
    16 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_lookup_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_input_budget enc encoder_budget key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_get_input_budget i
    end.

Definition audit_slot_update_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_input_budget enc encoder_budget key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_update_input_budget i
    end.

Fixpoint audit_slot_elements_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 2 + audit_slot_lookup_input_budget enc encoder_budget u key +
      audit_slot_elements_input_budget enc encoder_budget u rest
  end.

Fixpoint audit_slot_of_map_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      1 + 2 * audit_slot_key_get_input_budget enc encoder_budget key +
      (match fst (audit_map_get enc key (dense_index u)) with
       | None => 0
       | Some i => audit_slot_index_update_input_budget i
       end) + audit_slot_of_map_input_budget enc encoder_budget u rest
  end.

Fixpoint audit_slot_bindings_input_budget {K V CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (bindings : list (K * V)) : nat :=
  match bindings with
  | [] => 0
  | (key, _) :: rest => 4 + encoder_budget key + 16 * Pos.size_nat (fst (enc key)) +
      audit_slot_bindings_input_budget enc encoder_budget rest
  end.

Fixpoint audit_prepare_slots_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 1 + audit_slot_key_get_input_budget enc encoder_budget key +
      audit_prepare_slots_input_budget enc encoder_budget rest
  end.

Fixpoint audit_read_slots_input_budget (slots : list (option N)) : nat :=
  match slots with
  | [] => 1
  | None :: rest => 1 + audit_read_slots_input_budget rest
  | Some index :: rest => 1 + audit_slot_index_get_input_budget index +
    audit_read_slots_input_budget rest
  end.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_dense_prepare_whole_input_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source keys,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_dense_prepare_work enc_work (snd (audit_dense_prepare enc keys)) <=
      audit_dense_prepare_input_budget enc encoder_budget keys.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_lookup_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V) key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_lookup enc u m key)) <=
      audit_slot_lookup_input_budget enc encoder_budget u key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_update_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V) key value,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_update enc u m key value)) <=
      audit_slot_update_input_budget enc encoder_budget u key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_remove_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V) key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_remove enc u m key)) <=
      audit_slot_update_input_budget enc encoder_budget u key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_elements_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V),
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_elements enc u m)) <=
      audit_slot_elements_input_budget enc encoder_budget u (dense_keys u).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_of_map_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (abstract :
    Map.t K V),
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_of_map enc u abstract)) <=
      audit_slot_of_map_input_budget enc encoder_budget u (dense_keys u).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_to_map_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V),
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_to_map enc u m)) <=
      audit_slot_elements_input_budget enc encoder_budget u (dense_keys u) +
      audit_slot_bindings_input_budget enc encoder_budget (fst (audit_slot_elements enc u m)).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_dense_token_prepare_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source (original :
    encoding K) u key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (@audit_dense_token_prepare K V CE enc original u key)) <=
      audit_slot_key_get_input_budget enc encoder_budget key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_dense_token_read_whole_input_bound_statement : Prop :=
  forall K V CE enc_work (original : encoding K) u (token : dense_slot_token original u) (m :
    slot_map V),
    audit_slot_source_work enc_work (snd (@audit_dense_token_read K V CE original u token m)) <=
      audit_slot_index_get_input_budget (dense_token_index token).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_prepare_slot_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (@audit_prepare_slot K V CE enc u key)) <=
      audit_slot_key_get_input_budget enc encoder_budget key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_read_whole_input_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) index,
    audit_slot_source_work enc_work (snd (@audit_slot_read K V CE m index)) <=
      audit_slot_index_get_input_budget index.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_prepare_slots_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u keys,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (@audit_prepare_slots K V CE enc u keys)) <=
      audit_prepare_slots_input_budget enc encoder_budget keys.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_read_slots_whole_input_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) slots,
    audit_slot_source_work enc_work (snd (@audit_read_slots K V CE m slots)) <=
      audit_read_slots_input_budget slots.

(** Preparing a key pays its sole genuine external encoder call before all later direct trie
  reuse. *)
Definition audit_prepare_key_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) work source budget key,
    audit_external_callback_adapter enc work source budget ->
    audit_prepared_source_work work (snd (@audit_prepare_key K V CE enc key)) <= 1 + budget key.
