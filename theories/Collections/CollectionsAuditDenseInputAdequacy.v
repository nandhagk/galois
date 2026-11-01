(** * Dense slot whole-input bounds

    These bounds close library-owned numeric encoders and price each actual foreign key call.
    For example, a missing key incurs no numeric slot access.
    Builds on: dense source bounds and concrete encoder budgets. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet CollectionsAuditState CollectionsAuditCallback CollectionsAuditEncoding
  CollectionsAuditEncoderBudget CollectionsAuditEncoderBudgetAdequacy CollectionsAuditMap
  CollectionsAuditPrepared CollectionsAuditDense CollectionsAuditDenseAdequacy
  CollectionsAuditDenseSlots CollectionsAuditDenseSlotsAdequacy CollectionsAuditDenseInput.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** The adapter bounds the body returned by the very same call. *)
Lemma dense_external_bound K CE (enc : K -> positive * list CE) work source budget :
  audit_external_callback_adapter enc work source budget ->
  forall key, work (snd (enc key)) <= budget key.
Proof.
  intros Hadapter key. destruct (enc key) as [code events] eqn:Hcall.
  cbn. eapply audit_external_callback_input_bound; eassumption.
Qed.

(** The internal binary encoder fits its original input budget. *)
Lemma dense_N_input_bound index :
  audit_N_encoding_work (snd (audit_N_encode index)) <= audit_N_input_budget index.
Proof.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 audit_base_encoder_input_bound)))) index).
Qed.

(** The internal unary encoder fits its original input budget. *)
Lemma dense_nat_input_bound index :
  audit_nat_events_work (snd (audit_nat_encode index)) <= audit_nat_input_budget index.
Proof.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 audit_base_encoder_input_bound)))) index).
Qed.

(** A key-read budget replaces the retained foreign body with its per-input bound. *)
Lemma dense_key_budget K CE (enc : K -> positive * list CE) work budget key :
  work (snd (enc key)) <= budget key ->
  audit_slot_key_get_budget enc work key <= audit_slot_key_get_input_budget enc budget key.
Proof.
  unfold audit_slot_key_get_budget, audit_slot_key_get_input_budget. lia.
Qed.

(** Numeric reads are bounded using the concrete encoder on the same index. *)
Lemma dense_index_get_budget index :
  audit_slot_index_get_budget index <= audit_slot_index_get_input_budget index.
Proof.
  unfold audit_slot_index_get_budget, audit_slot_index_get_input_budget.
  pose proof (dense_N_input_bound index). lia.
Qed.

(** Numeric writes are bounded using the concrete encoder on the same index. *)
Lemma dense_index_update_budget index :
  audit_slot_index_update_budget index <= audit_slot_index_update_input_budget index.
Proof.
  unfold audit_slot_index_update_budget, audit_slot_index_update_input_budget.
  pose proof (dense_N_input_bound index). lia.
Qed.

(** A lookup budget covers the actual key read and conditional numeric read. *)
Lemma dense_lookup_budget K CE (enc : K -> positive * list CE) work budget u key :
  work (snd (enc key)) <= budget key ->
  audit_slot_lookup_budget enc work u key <= audit_slot_lookup_input_budget enc budget u key.
Proof.
  intro Henc. unfold audit_slot_lookup_budget, audit_slot_lookup_input_budget.
  pose proof (dense_key_budget K CE enc work budget key Henc).
  destruct (fst (audit_map_get enc key (dense_index u))) as [index|];
    [pose proof (dense_index_get_budget index)|]; lia.
Qed.

(** An update budget covers the actual key read and conditional numeric write. *)
Lemma dense_update_budget K CE (enc : K -> positive * list CE) work budget u key :
  work (snd (enc key)) <= budget key ->
  audit_slot_update_budget enc work u key <= audit_slot_update_input_budget enc budget u key.
Proof.
  intro Henc. unfold audit_slot_update_budget, audit_slot_update_input_budget.
  pose proof (dense_key_budget K CE enc work budget key Henc).
  destruct (fst (audit_map_get enc key (dense_index u))) as [index|];
    [pose proof (dense_index_update_budget index)|]; lia.
Qed.

(** Under the foreign encoder adapter, slot lookup work is bounded by its original-input budget. *)
Theorem audit_slot_lookup_whole_input_bound : audit_slot_lookup_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u m key Hadapter.
  pose proof (audit_slot_lookup_source_bound K V CE enc work u m key).
  pose proof (dense_lookup_budget K CE enc work budget u key
    (dense_external_bound K CE enc work source budget Hadapter key)). lia.
Qed.

(** Under the foreign encoder adapter, slot update work is bounded by its original-input budget. *)
Theorem audit_slot_update_whole_input_bound : audit_slot_update_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u m key value Hadapter.
  pose proof (audit_slot_update_source_bound K V CE enc work u m key value).
  pose proof (dense_update_budget K CE enc work budget u key
    (dense_external_bound K CE enc work source budget Hadapter key)). lia.
Qed.

(** Under the foreign encoder adapter, slot removal work is bounded by its original-input
    budget. *)
Theorem audit_slot_remove_whole_input_bound : audit_slot_remove_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u m key Hadapter.
  pose proof (audit_slot_remove_source_bound K V CE enc work u m key).
  pose proof (dense_update_budget K CE enc work budget u key
    (dense_external_bound K CE enc work source budget Hadapter key)). lia.
Qed.

(** Under the foreign encoder adapter, slot preparation work is bounded by the key-input budget. *)
Theorem audit_prepare_slot_whole_input_bound : audit_prepare_slot_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u key Hadapter.
  pose proof (audit_prepare_slot_source_bound K V CE enc work u key).
  pose proof (dense_key_budget K CE enc work budget key
    (dense_external_bound K CE enc work source budget Hadapter key)). lia.
Qed.

(** Under the foreign encoder adapter, token preparation work is bounded by the key-input
    budget. *)
Theorem audit_dense_token_prepare_whole_input_bound :
  audit_dense_token_prepare_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source original u key Hadapter.
  pose proof (audit_dense_token_prepare_source_bound K V CE enc work original u key).
  pose proof (dense_key_budget K CE enc work budget key
    (dense_external_bound K CE enc work source budget Hadapter key)). lia.
Qed.

(** A slot read's work is bounded using the concrete numeric encoder's input budget. *)
Theorem audit_slot_read_whole_input_bound : audit_slot_read_whole_input_bound_statement.
Proof.
  intros K V CE work m index.
  pose proof (audit_slot_read_source_bound K V CE work m index).
  pose proof (dense_index_get_budget index). lia.
Qed.

(** A token read's work is bounded using the concrete numeric encoder's input budget. *)
Theorem audit_dense_token_read_whole_input_bound :
  audit_dense_token_read_whole_input_bound_statement.
Proof.
  intros K V CE work original u token m.
  pose proof (audit_dense_token_read_source_bound K V CE work original u token m).
  pose proof (dense_index_get_budget (dense_token_index token)). lia.
Qed.

(** Under the foreign encoder adapter, key preparation work is at most one plus its input
    budget. *)
Theorem audit_prepare_key_whole_input_bound : audit_prepare_key_whole_input_bound_statement.
Proof.
  intros K V CE enc work source budget key Hadapter.
  pose proof (dense_external_bound K CE enc work source budget Hadapter key) as Hbound.
  unfold audit_prepare_key. destruct (enc key) as [code events]; cbn [snd] in Hbound.
  cbn [snd audit_prepared_source_work]. lia.
Qed.

(** Enumerating keys composes the individual lookup budget comparisons. *)
Lemma dense_elements_budget K CE (enc : K -> positive * list CE) work budget u keys :
  (forall key, work (snd (enc key)) <= budget key) ->
  audit_slot_elements_budget enc work u keys <= audit_slot_elements_input_budget enc budget u keys.
Proof.
  intro Henc. induction keys as [|key rest IH]; [reflexivity|].
  cbn [audit_slot_elements_budget audit_slot_elements_input_budget].
  pose proof (dense_lookup_budget K CE enc work budget u key (Henc key)). lia.
Qed.

(** Converting from a map composes the two possible key reads and numeric write. *)
Lemma dense_of_map_budget K CE (enc : K -> positive * list CE) work budget u keys :
  (forall key, work (snd (enc key)) <= budget key) ->
  audit_slot_of_map_budget enc work u keys <= audit_slot_of_map_input_budget enc budget u keys.
Proof.
  intro Henc. induction keys as [|key rest IH]; [reflexivity|].
  cbn [audit_slot_of_map_budget audit_slot_of_map_input_budget].
  pose proof (dense_key_budget K CE enc work budget key (Henc key)).
  destruct (fst (audit_map_get enc key (dense_index u))) as [index|];
    [pose proof (dense_index_update_budget index)|]; lia.
Qed.

(** Binding-write budgets replace each retained foreign call body. *)
Lemma dense_bindings_budget K V CE (enc : K -> positive * list CE) work budget
    (bindings : list (K * V)) :
  (forall key, work (snd (enc key)) <= budget key) ->
  audit_slot_bindings_budget enc work bindings <=
    audit_slot_bindings_input_budget enc budget bindings.
Proof.
  intro Henc. induction bindings as [|[key value] rest IH]; [reflexivity|].
  cbn [audit_slot_bindings_budget audit_slot_bindings_input_budget]. pose proof (Henc key). lia.
Qed.

(** Under the foreign encoder adapter, enumeration work is bounded by the universe-key input
    budget. *)
Theorem audit_slot_elements_whole_input_bound : audit_slot_elements_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u m Hadapter.
  pose proof (audit_slot_elements_source_bound K V CE enc work u m).
  pose proof (dense_elements_budget K CE enc work budget u (dense_keys u)
    (dense_external_bound K CE enc work source budget Hadapter)). lia.
Qed.

(** Under the foreign encoder adapter, map-to-slot work is bounded by the universe-key input
    budget. *)
Theorem audit_slot_of_map_whole_input_bound : audit_slot_of_map_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u abstract Hadapter.
  pose proof (audit_slot_of_map_source_bound K V CE enc work u abstract).
  pose proof (dense_of_map_budget K CE enc work budget u (dense_keys u)
    (dense_external_bound K CE enc work source budget Hadapter)). lia.
Qed.

(** Under the foreign encoder adapter, slot-to-map work is bounded by enumeration and binding
    budgets. *)
Theorem audit_slot_to_map_whole_input_bound : audit_slot_to_map_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u m Hadapter.
  pose proof (audit_slot_to_map_source_bound K V CE enc work u m).
  pose proof (dense_elements_budget K CE enc work budget u (dense_keys u)
    (dense_external_bound K CE enc work source budget Hadapter)).
  pose proof (dense_bindings_budget K V CE enc work budget (fst (audit_slot_elements enc u m))
    (dense_external_bound K CE enc work source budget Hadapter)). lia.
Qed.

(** Under the foreign encoder adapter, batch preparation work is bounded by its key-input
    budgets. *)
Theorem audit_prepare_slots_whole_input_bound : audit_prepare_slots_whole_input_bound_statement.
Proof.
  intros K V CE enc work budget source u keys Hadapter.
  pose proof (audit_prepare_slots_source_bound K V CE enc work u keys) as Hwork.
  assert (Hbudget : audit_prepare_slots_budget enc work keys <=
    audit_prepare_slots_input_budget enc budget keys).
  { clear Hwork. induction keys as [|key rest IH]; [reflexivity|].
    cbn [audit_prepare_slots_budget audit_prepare_slots_input_budget].
    pose proof (dense_key_budget K CE enc work budget key
      (dense_external_bound K CE enc work source budget Hadapter key)). lia. }
  lia.
Qed.

(** Batch read work is bounded by the concrete numeric input budgets for present slots. *)
Theorem audit_read_slots_whole_input_bound : audit_read_slots_whole_input_bound_statement.
Proof.
  intros K V CE work m slots.
  pose proof (audit_read_slots_source_bound K V CE work m slots) as Hwork.
  assert (Hbudget : audit_read_slots_budget slots <= audit_read_slots_input_budget slots).
  { clear Hwork. induction slots as [|[index|] rest IH];
      cbn [audit_read_slots_budget audit_read_slots_input_budget];
      try lia. pose proof (dense_index_get_budget index). lia. }
  lia.
Qed.

(** Distinctness work replaces each retained key-call body with its input budget. *)
Lemma dense_unique_input_budget K CE (enc : K -> positive * list CE) work budget keys :
  (forall key, work (snd (enc key)) <= budget key) ->
  audit_dense_unique_budget enc work keys <= audit_dense_unique_input_budget enc budget keys.
Proof.
  intro Henc. induction keys as [|key rest IH]; [reflexivity|].
  cbn [audit_dense_unique_budget audit_dense_unique_input_budget]. pose proof (Henc key). lia.
Qed.

(** Numbering uses each actual successor and the concrete binary encoder bound. *)
Lemma dense_number_input_budget K CE (enc : K -> positive * list CE) work budget keys :
  (forall key, work (snd (enc key)) <= budget key) -> forall index,
  audit_dense_number_budget enc work keys index <=
    audit_dense_number_input_budget enc budget keys index.
Proof.
  intro Henc. induction keys as [|key rest IH]; intro index; [reflexivity|].
  cbn [audit_dense_number_budget audit_dense_number_input_budget].
  pose proof (audit_dense_N_succ_erases index) as Hnext.
  pose proof (dense_N_input_bound index) as Hnumeric.
  unfold audit_dense_N_succ in *.
  destruct (audit_N_encode index) as [code events]; cbn [fst snd] in *.
  specialize (IH (Npos code)). rewrite <- Hnext. cbn.
  unfold audit_N_encoding_work in Hnumeric. pose proof (Henc key). lia.
Qed.

(** Under the foreign encoder adapter, dense preparation work is bounded by its original-input
    budget. *)
Theorem audit_dense_prepare_whole_input_bound : audit_dense_prepare_whole_input_bound_statement.
Proof.
  intros K CE enc work budget source keys Hadapter.
  pose proof (audit_dense_prepare_source_bound K CE enc work keys) as Hwork.
  assert (Henc := dense_external_bound K CE enc work source budget Hadapter).
  pose proof (dense_unique_input_budget K CE enc work budget keys Henc) as Hunique.
  unfold audit_dense_prepare_budget in Hwork.
  unfold audit_dense_prepare_input_budget.
  destruct (audit_dense_unique enc FinSet.empty keys) as [unique events]; cbn [fst] in *.
  pose proof (dense_number_input_budget K CE enc work budget unique Henc 0%N) as Hnumber.
  destruct (length unique) as [|n] eqn:Hlength.
  - cbn [audit_dense_N_of_nat snd] in Hwork.
    change (audit_nat_events_work []) with 0 in Hwork. lia.
  - pose proof (dense_nat_input_bound n) as Hnumeric.
    cbn [audit_dense_N_of_nat] in Hwork.
    destruct (audit_nat_encode n) as [code numeric]; cbn [fst snd] in *. lia.
Qed.
