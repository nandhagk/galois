(** * Dense slot observer adequacy

    Counted slot operations retain the original persistent map observations.
    For example, a missing key skips the numeric slot read.
    Builds on: CollectionsAuditDenseSlots and map and encoding adequacy. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsDenseSet
  CollectionsAuditState CollectionsAuditEncoding CollectionsAuditEncodingAdequacy
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditDenseSlots.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** If the encoder agrees at the key, discarding events returns the original prepared slot. *)
Theorem audit_prepare_slot_erases : audit_prepare_slot_erases_statement.
Proof.
  intros K V CE enc original u key Henc.
  pose proof (audit_map_get_erases K N CE enc original key (dense_index u) Henc) as Hget.
  unfold audit_prepare_slot, prepare_slot.
  destruct (audit_map_get enc key (dense_index u)); exact Hget.
Qed.

(** Discarding slot-read events returns the original numeric map lookup. *)
Theorem audit_slot_read_erases : audit_slot_read_erases_statement.
Proof.
  intros K V CE m index.
  pose proof (audit_map_get_erases N V audit_n_encoding_event audit_N_encode N_encoding index m
    (audit_N_encode_erases index)) as Hget.
  unfold audit_slot_read, slot_read.
  destruct (audit_map_get audit_N_encode index m); exact Hget.
Qed.

(** If the encoder agrees on every key, discarding lookup events preserves the slot result. *)
Theorem audit_slot_lookup_erases : audit_slot_lookup_erases_statement.
Proof.
  intros K V CE enc original u m key Henc.
  pose proof (audit_map_get_erases K N CE enc original key (dense_index u) (Henc key)) as Hget.
  unfold audit_slot_lookup, slot_lookup.
  destruct (audit_map_get enc key (dense_index u)) as [[index|] calls]; cbn in Hget;
    rewrite <- Hget; [|reflexivity].
  pose proof (audit_slot_read_erases K V CE m index) as Hread.
  unfold audit_slot_read, slot_read in Hread.
  destruct (audit_map_get audit_N_encode index m); exact Hread.
Qed.

(** If the encoder agrees on every key, discarding update events preserves the returned slot
    map. *)
Theorem audit_slot_update_erases : audit_slot_update_erases_statement.
Proof.
  intros K V CE enc original u m key value Henc.
  pose proof (audit_map_get_erases K N CE enc original key (dense_index u) (Henc key)) as Hget.
  unfold audit_slot_update, slot_update.
  destruct (audit_map_get enc key (dense_index u)) as [[index|] calls]; cbn in Hget;
    rewrite <- Hget; [|reflexivity].
  pose proof (audit_map_set_erases N V audit_n_encoding_event audit_N_encode N_encoding index
    value m (audit_N_encode_erases index)) as Hset.
  destruct (audit_map_set audit_N_encode index value m); cbn in *. now rewrite Hset.
Qed.

(** If the encoder agrees on every key, discarding removal events preserves the returned slot
    map. *)
Theorem audit_slot_remove_erases : audit_slot_remove_erases_statement.
Proof.
  intros K V CE enc original u m key Henc.
  pose proof (audit_map_get_erases K N CE enc original key (dense_index u) (Henc key)) as Hget.
  unfold audit_slot_remove, slot_remove, prepare_slot.
  destruct (audit_map_get enc key (dense_index u)) as [[index|] calls]; cbn in Hget;
    rewrite <- Hget; [|reflexivity].
  pose proof (audit_map_remove_erases N V audit_n_encoding_event audit_N_encode N_encoding index
    m (audit_N_encode_erases index)) as Hremove.
  destruct (audit_map_remove audit_N_encode index m); cbn in *. now rewrite Hremove.
Qed.

(** If the encoder agrees at the key, discarding events preserves the token-preparation result. *)
Theorem audit_dense_token_prepare_erases : audit_dense_token_prepare_erases_statement.
Proof.
  intros K V CE enc original u key Henc.
  pose proof (audit_map_get_erases K N CE enc original key (dense_index u) Henc) as Hget.
  unfold audit_dense_token_prepare, dense_token_prepare, prepare_slot.
  destruct (audit_map_get enc key (dense_index u)) as [index calls]; cbn in Hget.
  now rewrite <- Hget.
Qed.

(** Discarding token-read events returns the original token's numeric slot lookup. *)
Theorem audit_dense_token_read_erases : audit_dense_token_read_erases_statement.
Proof.
  intros K V CE original u token m.
  exact (audit_slot_read_erases K V CE m (dense_token_index token)).
Qed.

(** If the encoders agree on the input keys, batch preparation erases to the original ordered
    slots. *)
Theorem audit_prepare_slots_erases : audit_prepare_slots_erases_statement.
Proof.
  intros K V CE enc original u keys.
  induction keys as [|key rest IH]; intro Henc; [reflexivity|].
  cbn [audit_prepare_slots prepare_slots map].
  pose proof (audit_prepare_slot_erases K V CE enc original u key
    (Henc key (or_introl eq_refl))) as Hslot.
  destruct (audit_prepare_slot enc u key) as [index calls]; cbn in Hslot.
  specialize (IH (fun k Hin => Henc k (or_intror Hin))).
  destruct (audit_prepare_slots enc u rest) as [tail events]; cbn [fst snd] in IH.
  now rewrite Hslot, IH.
Qed.

(** Discarding batch-read events preserves the ordered results, including missing slots. *)
Theorem audit_read_slots_erases : audit_read_slots_erases_statement.
Proof.
  intros K V CE m slots. induction slots as [|[index|] rest IH]; [reflexivity| |].
  - cbn [audit_read_slots read_slots map].
    pose proof (audit_slot_read_erases K V CE m index) as Hread.
    destruct (audit_slot_read m index) as [value calls]; cbn [fst snd] in Hread.
    destruct (audit_read_slots m rest) as [tail events]; cbn [fst snd] in IH.
    now rewrite Hread, IH.
  - cbn [audit_read_slots read_slots map].
    destruct (audit_read_slots m rest) as [tail events]; cbn [fst snd] in IH. now rewrite IH.
Qed.

(** Enumeration preserves every observed key-value pair in universe order. *)
Lemma audit_slot_elements_from_erases K V CE (enc : K -> positive * list CE)
    (original : encoding K) u (m : slot_map V) keys :
  (forall k, fst (enc k) = encode original k) ->
  fst (audit_slot_elements_from enc u m keys) =
    flat_map (fun k =>
      match slot_lookup original u m k with
      | Some v => [(k, v)]
      | None => []
      end) keys.
Proof.
  intro Henc. induction keys as [|key rest IH]; [reflexivity|].
  cbn [audit_slot_elements_from flat_map].
  pose proof (audit_slot_lookup_erases K V CE enc original u m key Henc) as Hlookup.
  destruct (audit_slot_lookup enc u m key) as [value calls]; cbn in Hlookup.
  destruct (audit_slot_elements_from enc u m rest) as [tail events]; cbn [fst snd] in IH.
  rewrite <- Hlookup. destruct value; cbn; now rewrite IH.
Qed.

(** If the encoders agree on every key, enumeration erases to the original ordered bindings. *)
Theorem audit_slot_elements_erases : audit_slot_elements_erases_statement.
Proof.
  intros K V CE enc original u m Henc.
  apply audit_slot_elements_from_erases; exact Henc.
Qed.

(** Converting a list of keys threads each returned numeric map through the fold. *)
Lemma audit_slot_of_map_from_erases K V CE (enc : K -> positive * list CE)
    (original : encoding K) u (abstract : Map.t K V) keys :
  (forall k, fst (enc k) = encode original k) -> forall state,
  fst (audit_slot_of_map_from enc u abstract keys state) =
    fold_left (fun result k =>
      match Map.get original k abstract, prepare_slot original u k with
      | Some value, Some i => Map.set N_encoding i value result
      | _, _ => result
      end) keys state.
Proof.
  intro Henc. induction keys as [|key rest IH]; intro state; [reflexivity|].
  cbn [audit_slot_of_map_from fold_left].
  pose proof (audit_map_get_erases K V CE enc original key abstract (Henc key)) as Hvalue.
  destruct (audit_map_get enc key abstract) as [[value|] vcalls]; cbn in Hvalue.
  - pose proof (audit_map_get_erases K N CE enc original key (dense_index u) (Henc key))
      as Hindex.
    destruct (audit_map_get enc key (dense_index u)) as [[index|] icalls]; cbn in Hindex;
      unfold prepare_slot; rewrite <- Hvalue, <- Hindex.
    + pose proof (audit_map_set_erases N V audit_n_encoding_event audit_N_encode N_encoding
        index value state (audit_N_encode_erases index)) as Hset.
      destruct (audit_map_set audit_N_encode index value state) as [next writes]; cbn in Hset.
      specialize (IH next).
      destruct (audit_slot_of_map_from enc u abstract rest next); cbn in *.
      now rewrite IH, Hset.
    + specialize (IH state). destruct (audit_slot_of_map_from enc u abstract rest state).
      exact IH.
  - rewrite <- Hvalue. destruct (Map.get original key (dense_index u));
      specialize (IH state); destruct (audit_slot_of_map_from enc u abstract rest state); exact IH.
Qed.

(** If the encoders agree on every key, map-to-slot conversion erases to the original result. *)
Theorem audit_slot_of_map_erases : audit_slot_of_map_erases_statement.
Proof.
  intros K V CE enc original u abstract Henc.
  unfold audit_slot_of_map, slot_of_map.
  apply audit_slot_of_map_from_erases; exact Henc.
Qed.

(** Binding writes thread the returned map through the ordinary list fold. *)
Lemma audit_slot_bindings_erases K V CE (enc : K -> positive * list CE)
    (original : encoding K) (bindings : list (K * V)) :
  (forall k, fst (enc k) = encode original k) -> forall state,
  fst (audit_slot_bindings_to_map enc bindings state) =
    fold_left (fun m kv => Map.set original (fst kv) (snd kv) m) bindings state.
Proof.
  intro Henc. induction bindings as [|[key value] rest IH]; intro state; [reflexivity|].
  cbn [audit_slot_bindings_to_map fold_left].
  pose proof (audit_map_set_erases K V CE enc original key value state (Henc key)) as Hset.
  destruct (audit_map_set enc key value state) as [next calls]; cbn in Hset.
  specialize (IH next). destruct (audit_slot_bindings_to_map enc rest next); cbn in *.
  now rewrite IH, Hset.
Qed.

(** If the encoders agree on every key, slot-to-map conversion erases to the original result. *)
Theorem audit_slot_to_map_erases : audit_slot_to_map_erases_statement.
Proof.
  intros K V CE enc original u m Henc.
  pose proof (audit_slot_elements_erases K V CE enc original u m Henc) as Helements.
  unfold audit_slot_to_map, slot_to_map, Map.of_list.
  destruct (audit_slot_elements enc u m) as [bindings first]; cbn in Helements.
  pose proof (audit_slot_bindings_erases K V CE enc original bindings Henc Map.empty) as Hbindings.
  destruct (audit_slot_bindings_to_map enc bindings Map.empty); cbn in Hbindings.
  now rewrite Hbindings, Helements.
Qed.

(** Slot work is additive over adjacent event lists. *)
Lemma audit_slot_work_app K V CE (work : list CE -> nat)
    (left right : list (audit_slot_event K V CE)) :
  audit_slot_source_work work (left ++ right) =
    audit_slot_source_work work left + audit_slot_source_work work right.
Proof.
  induction left as [|event rest IH]; [reflexivity|].
  destruct event; cbn [app audit_slot_source_work]; rewrite IH; lia.
Qed.

(** Slot-preparation source work is at most the key lookup budget. *)
Theorem audit_prepare_slot_source_bound : audit_prepare_slot_source_bound_statement.
Proof.
  intros K V CE enc work u key.
  pose proof (audit_map_get_source_work_bound K N CE enc work key (dense_index u)) as Hbound.
  unfold audit_prepare_slot, audit_slot_key_get_budget.
  destruct (audit_map_get enc key (dense_index u)) as [index calls]; cbn in *; lia.
Qed.

(** Slot-read source work is at most the numeric lookup budget. *)
Theorem audit_slot_read_source_bound : audit_slot_read_source_bound_statement.
Proof.
  intros K V CE work m index.
  pose proof (audit_map_get_source_work_bound N V audit_n_encoding_event audit_N_encode
    audit_N_encoding_work index m) as Hbound.
  unfold audit_slot_read, audit_slot_index_get_budget.
  destruct (audit_map_get audit_N_encode index m) as [value calls]; cbn in *; lia.
Qed.

(** Token-preparation source work is at most the key lookup budget. *)
Theorem audit_dense_token_prepare_source_bound : audit_dense_token_prepare_source_bound_statement.
Proof.
  intros K V CE enc work original u key.
  pose proof (audit_prepare_slot_source_bound K V CE enc work u key) as Hbound.
  unfold audit_prepare_slot, audit_dense_token_prepare in *.
  destruct (audit_map_get enc key (dense_index u)); exact Hbound.
Qed.

(** Token-read source work is at most the numeric lookup budget for its index. *)
Theorem audit_dense_token_read_source_bound : audit_dense_token_read_source_bound_statement.
Proof.
  intros K V CE work original u token m.
  exact (audit_slot_read_source_bound K V CE work m (dense_token_index token)).
Qed.

(** Slot-lookup source work is at most the key budget plus the conditional numeric read budget. *)
Theorem audit_slot_lookup_source_bound : audit_slot_lookup_source_bound_statement.
Proof.
  intros K V CE enc work u m key.
  pose proof (audit_prepare_slot_source_bound K V CE enc work u key) as Hkey.
  unfold audit_prepare_slot in Hkey.
  unfold audit_slot_lookup, audit_slot_lookup_budget.
  destruct (audit_map_get enc key (dense_index u)) as [[index|] calls]; cbn in *; [|lia].
  pose proof (audit_slot_read_source_bound K V CE work m index) as Hread.
  unfold audit_slot_read in Hread.
  destruct (audit_map_get audit_N_encode index m) as [value reads]; cbn in *; lia.
Qed.

(** Slot-update source work is at most the key budget plus the conditional numeric write budget. *)
Theorem audit_slot_update_source_bound : audit_slot_update_source_bound_statement.
Proof.
  intros K V CE enc work u m key value.
  pose proof (audit_prepare_slot_source_bound K V CE enc work u key) as Hkey.
  unfold audit_prepare_slot in Hkey.
  unfold audit_slot_update, audit_slot_update_budget.
  destruct (audit_map_get enc key (dense_index u)) as [[index|] calls]; cbn in *; [|lia].
  pose proof (audit_map_set_source_work_bound N V audit_n_encoding_event audit_N_encode
    audit_N_encoding_work index value m) as Hwrite.
  unfold audit_slot_index_update_budget.
  destruct (audit_map_set audit_N_encode index value m); cbn in *; lia.
Qed.

(** Slot-removal source work is at most the key budget plus the conditional numeric update
    budget. *)
Theorem audit_slot_remove_source_bound : audit_slot_remove_source_bound_statement.
Proof.
  intros K V CE enc work u m key.
  pose proof (audit_prepare_slot_source_bound K V CE enc work u key) as Hkey.
  unfold audit_prepare_slot in Hkey.
  unfold audit_slot_remove, audit_slot_update_budget.
  destruct (audit_map_get enc key (dense_index u)) as [[index|] calls]; cbn in *; [|lia].
  pose proof (audit_map_remove_source_work_bound N V audit_n_encoding_event audit_N_encode
    audit_N_encoding_work index m) as Hremove.
  unfold audit_slot_index_update_budget.
  destruct (audit_map_remove audit_N_encode index m); cbn in *; lia.
Qed.

(** Enumeration charges each actual lookup and emitted binding. *)
Lemma audit_slot_elements_from_bound K V CE (enc : K -> positive * list CE) work u
    (m : slot_map V) keys :
  audit_slot_source_work work (snd (audit_slot_elements_from enc u m keys)) <=
    audit_slot_elements_budget enc work u keys.
Proof.
  induction keys as [|key rest IH]; [reflexivity|].
  cbn [audit_slot_elements_from audit_slot_elements_budget].
  pose proof (audit_slot_lookup_source_bound K V CE enc work u m key) as Hlookup.
  destruct (audit_slot_lookup enc u m key) as [value calls]; cbn [snd] in Hlookup.
  destruct (audit_slot_elements_from enc u m rest) as [tail events]; cbn [fst snd] in IH.
  destruct value; cbn [snd audit_slot_source_work]; rewrite audit_slot_work_app;
    cbn [audit_slot_source_work]; lia.
Qed.

(** Enumeration source work is at most the budget over the universe's stored keys. *)
Theorem audit_slot_elements_source_bound : audit_slot_elements_source_bound_statement.
Proof.
  intros K V CE enc work u m. apply audit_slot_elements_from_bound.
Qed.

(** Batch-preparation source work is at most the budget for its ordered key list. *)
Theorem audit_prepare_slots_source_bound : audit_prepare_slots_source_bound_statement.
Proof.
  intros K V CE enc work u keys. induction keys as [|key rest IH]; [reflexivity|].
  cbn [audit_prepare_slots audit_prepare_slots_budget].
  pose proof (audit_prepare_slot_source_bound K V CE enc work u key) as Hkey.
  destruct (audit_prepare_slot enc u key) as [index calls]; cbn [snd] in Hkey.
  destruct (audit_prepare_slots enc u rest) as [tail events]; cbn [fst snd] in IH.
  cbn [snd audit_slot_source_work]. rewrite audit_slot_work_app. lia.
Qed.

(** Batch-read source work is at most the budget for its optional slot list. *)
Theorem audit_read_slots_source_bound : audit_read_slots_source_bound_statement.
Proof.
  intros K V CE work m slots. induction slots as [|[index|] rest IH]; [reflexivity| |].
  - cbn [audit_read_slots audit_read_slots_budget].
    pose proof (audit_slot_read_source_bound K V CE work m index) as Hread.
    destruct (audit_slot_read m index) as [value calls]; cbn [fst snd] in Hread.
    destruct (audit_read_slots m rest) as [tail events]; cbn [fst snd] in IH.
    cbn [snd audit_slot_source_work]. rewrite audit_slot_work_app. lia.
  - cbn [audit_read_slots audit_read_slots_budget].
    destruct (audit_read_slots m rest) as [tail events]; cbn in *. lia.
Qed.

(** Batch reading returns the original results and length and counts present slots and their
    code bits. *)
Theorem audit_read_slots_observation : audit_read_slots_observation_statement.
Proof.
  intros K V CE m slots. induction slots as [|[index|] rest IH]; [repeat split; reflexivity| |].
  - cbn [audit_read_slots read_slots map].
    pose proof (audit_slot_read_erases K V CE m index) as Hread.
    unfold audit_slot_read in *.
    destruct (audit_map_get audit_N_encode index m) as [value calls]; cbn [fst snd] in Hread.
    destruct (audit_read_slots m rest) as [tail events]; cbn [fst snd] in IH.
    destruct IH as [Hout [Hlen [Hcalls Hbits]]].
    cbn [audit_slot_read_calls audit_slot_read_key_bits length filter fold_right].
    cbn [app audit_slot_read_calls audit_slot_read_key_bits].
    unfold read_slots in Hout.
    rewrite Hlen, Hcalls, Hbits, Hread, Hout. repeat split; reflexivity.
  - cbn [audit_read_slots read_slots map].
    destruct (audit_read_slots m rest) as [tail events]; cbn [fst snd] in IH.
    destruct IH as [Hout [Hlen [Hcalls Hbits]]].
    cbn [audit_slot_read_calls audit_slot_read_key_bits length filter fold_right].
    rewrite Hlen, Hcalls, Hbits, Hout. repeat split; reflexivity.
Qed.

(** Map-to-slot conversion charges both possible probes and every actual write. *)
Lemma audit_slot_of_map_from_bound K V CE (enc : K -> positive * list CE) work u
    (abstract : Map.t K V) keys : forall state,
  audit_slot_source_work work (snd (audit_slot_of_map_from enc u abstract keys state)) <=
    audit_slot_of_map_budget enc work u keys.
Proof.
  induction keys as [|key rest IH]; intro state; [reflexivity|].
  cbn [audit_slot_of_map_from audit_slot_of_map_budget].
  pose proof (audit_map_get_source_work_bound K V CE enc work key abstract) as Hvalue.
  destruct (audit_map_get enc key abstract) as [[value|] vcalls]; cbn [snd] in Hvalue.
  - pose proof (audit_prepare_slot_source_bound K V CE enc work u key) as Hindex.
    unfold audit_prepare_slot in Hindex.
    destruct (audit_map_get enc key (dense_index u)) as [[index|] icalls]; cbn [snd] in Hindex.
    + pose proof (audit_map_set_source_work_bound N V audit_n_encoding_event audit_N_encode
        audit_N_encoding_work index value state) as Hwrite.
      destruct (audit_map_set audit_N_encode index value state) as [next writes].
      cbn [snd] in Hwrite.
      specialize (IH next). destruct (audit_slot_of_map_from enc u abstract rest next)
        as [out events]; cbn [snd] in IH.
      cbn [snd app audit_slot_source_work]. unfold audit_slot_key_get_budget,
        audit_slot_index_update_budget in *. cbn [fst audit_slot_source_work] in *. lia.
    + specialize (IH state). destruct (audit_slot_of_map_from enc u abstract rest state)
        as [out events]; cbn [snd] in IH.
      cbn [snd app audit_slot_source_work]. unfold audit_slot_key_get_budget in *.
      cbn [fst audit_slot_source_work] in *. lia.
  - specialize (IH state). destruct (audit_slot_of_map_from enc u abstract rest state)
      as [out events]; cbn [snd] in IH.
    cbn [snd app audit_slot_source_work]. unfold audit_slot_key_get_budget in *.
    destruct (fst (audit_map_get enc key (dense_index u))); lia.
Qed.

(** Map-to-slot source work is at most the budget over the universe's stored keys. *)
Theorem audit_slot_of_map_source_bound : audit_slot_of_map_source_bound_statement.
Proof.
  intros K V CE enc work u abstract. apply audit_slot_of_map_from_bound.
Qed.

(** Each binding write charges the actual source map and returned state. *)
Lemma audit_slot_bindings_bound K V CE (enc : K -> positive * list CE) work
    (bindings : list (K * V)) : forall state,
  audit_slot_source_work work (snd (audit_slot_bindings_to_map enc bindings state)) <=
    audit_slot_bindings_budget enc work bindings.
Proof.
  induction bindings as [|[key value] rest IH]; intro state; [reflexivity|].
  cbn [audit_slot_bindings_to_map audit_slot_bindings_budget].
  pose proof (audit_map_set_source_work_bound K V CE enc work key value state) as Hwrite.
  destruct (audit_map_set enc key value state) as [next calls]; cbn [snd] in Hwrite.
  specialize (IH next). destruct (audit_slot_bindings_to_map enc rest next) as [out events].
  cbn [snd] in IH. cbn [snd audit_slot_source_work]. lia.
Qed.

(** Slot-to-map source work is at most the enumeration and actual resulting binding budgets. *)
Theorem audit_slot_to_map_source_bound : audit_slot_to_map_source_bound_statement.
Proof.
  intros K V CE enc work u m.
  pose proof (audit_slot_elements_source_bound K V CE enc work u m) as Helements.
  unfold audit_slot_to_map.
  destruct (audit_slot_elements enc u m) as [bindings first]; cbn [snd] in Helements.
  pose proof (audit_slot_bindings_bound K V CE enc work bindings Map.empty) as Hbindings.
  destruct (audit_slot_bindings_to_map enc bindings Map.empty) as [out second].
  cbn [snd] in Hbindings. cbn [fst snd]. rewrite audit_slot_work_app. lia.
Qed.
