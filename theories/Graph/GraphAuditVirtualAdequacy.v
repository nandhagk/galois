(** * Virtual-root graph adequacy

    The counted virtual callbacks preserve the original graph observations.
    For example, a synthetic entry edge has the fresh root as its source.
    Builds on: the virtual graph audit model and its source operations. *)

From Stdlib Require Import List PArith Lia PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditElements
  CollectionsAuditElementsAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphSemiDominators
  GraphAuditBase GraphAuditDfs
  GraphAuditVirtual GraphAuditBaseAdequacy GraphAuditDfsAdequacy.

(** * Callback erasure *)

(** Counted entry traversal retains the same entries as the ordinary traversal. *)
Lemma audit_virtual_entries_erases V E (EV : encoding V) entries seen :
  fst (@audit_virtual_entries_counted V E EV seen entries) =
    virtual_entries_from EV seen entries.
Proof.
  revert seen.
  induction entries as [|v rest IH]; intro seen; cbn.
  - reflexivity.
  - destruct (FinSet.mem EV v seen); cbn.
    + destruct (audit_virtual_entries_counted EV seen rest) as [result events] eqn:Hrun.
      specialize (IH seen); rewrite Hrun in IH; exact IH.
    + destruct (audit_virtual_entries_counted EV (FinSet.add EV v seen) rest)
        as [result events] eqn:Hrun.
      specialize (IH (FinSet.add EV v seen)); rewrite Hrun in IH; cbn in IH.
      now rewrite IH.
Qed.

(** Virtual callbacks preserve the source graph operations and the entry traversal. *)
Theorem audit_virtual_callbacks_correct : audit_virtual_callbacks_statement.
Proof.
  intros V E EV g.
  unfold audit_prepare_callbacks_erase, audit_dfs_callbacks_erase.
  repeat split.
  - intros [v|[]]; cbn [audit_virtual_prepare_callbacks audit_virtual_out_counted
      virtual_graph virtual_entries].
    + reflexivity.
    + pose proof (audit_virtual_entries_erases V E EV (Graph.entries g) FinSet.empty) as H.
      cbn [audit_prepare_out_model audit_virtual_prepare_callbacks audit_virtual_out_counted
        virtual_graph virtual_entries].
      destruct (audit_virtual_entries_counted EV FinSet.empty (Graph.entries g))
        as [result events] eqn:Hrun.
      cbn in H |- *; now rewrite H.
  - intros [e|v]; reflexivity.
  - intros [v|[]]; reflexivity.
  - intros [e|v]; reflexivity.
  - intros [v|[]]; reflexivity.
  - intros [e|v]; reflexivity.
  - intros seen entries; apply audit_virtual_entries_erases.
Qed.

(** The full source wrapper returns the original source or the synthetic root. *)
Theorem audit_virtual_full_source_correct : audit_virtual_full_source_statement.
Proof.
  intros V E B EV g source Hsource [edge|vertex].
  - specialize (Hsource edge).
    unfold audit_virtual_full_source.
    destruct (source edge) as [value body]; cbn in *.
    now rewrite Hsource.
  - reflexivity.
Qed.

(** Full entry traversal retains the same persistent set at each recursive step. *)
Lemma audit_virtual_entries_full_erases V B (EV : encoding V)
    (enc : V -> positive * list B) entries :
  (forall v, fst (enc v) = encode EV v) ->
  forall seen, fst (audit_virtual_entries_full_counted enc seen entries) =
    virtual_entries_from EV seen entries.
Proof.
  intros Henc; induction entries as [|v rest IH]; intro seen; cbn.
  - reflexivity.
  - pose proof (audit_finset_mem_erases V B enc EV v seen (Henc v)) as Hmem.
    destruct (audit_finset_mem enc v seen) as [found reads] eqn:Hread; cbn in Hmem.
    rewrite <- Hmem.
    destruct found.
    + specialize (IH seen).
      destruct (audit_virtual_entries_full_counted enc seen rest) as [result events].
      cbn in *; exact IH.
    + pose proof (audit_finset_add_erases V B enc EV v seen (Henc v)) as Hadd.
      destruct (audit_finset_add enc v seen) as [next writes] eqn:Hwrite; cbn in Hadd.
      specialize (IH next).
      destruct (audit_virtual_entries_full_counted enc next rest) as [result events].
      cbn in *; rewrite <- Hadd; now rewrite IH.
Qed.

(** Lifted callbacks preserve graph and encoder results for the original and synthetic cases. *)
Theorem audit_virtual_full_callbacks_correct : audit_virtual_full_callbacks_statement.
Proof.
  intros V E B EV g cb [Hout [Htarget Hencode]].
  unfold audit_prepare_callbacks_erase, audit_dfs_callbacks_erase.
  repeat split.
  - intros [v|[]].
    + specialize (Hout v).
      cbn [audit_prepare_out_model audit_virtual_full_prepare_callbacks audit_virtual_full_out
        virtual_graph].
      destruct (audit_virtual_base_out cb v) as [edges body]; cbn in *; now rewrite Hout.
    + pose proof (audit_virtual_entries_full_erases V B EV (audit_virtual_base_encode cb)
        (Graph.entries g) Hencode FinSet.empty) as Hentries.
      cbn [audit_prepare_out_model audit_virtual_full_prepare_callbacks audit_virtual_full_out
        virtual_graph virtual_entries].
      destruct (audit_virtual_entries_full_counted (audit_virtual_base_encode cb) FinSet.empty
        (Graph.entries g)) as [entries events]; cbn in *; now rewrite Hentries.
  - intros [e|v]; cbn [audit_prepare_target_model audit_virtual_full_prepare_callbacks
      audit_virtual_full_target virtual_graph]; [|reflexivity].
    specialize (Htarget e); destruct (audit_virtual_base_target cb e);
      cbn in *; now rewrite Htarget.
  - intros [v|[]]; cbn [audit_prepare_encode_model audit_virtual_full_prepare_callbacks
      audit_virtual_full_encode virtual_encoding]; [|reflexivity].
    specialize (Hencode v); destruct (audit_virtual_base_encode cb v);
      cbn in *; now rewrite Hencode.
  - intros [e|v]; cbn [audit_dfs_target_model audit_virtual_full_dfs_callbacks
      audit_virtual_full_target virtual_graph]; [|reflexivity].
    specialize (Htarget e); destruct (audit_virtual_base_target cb e);
      cbn in *; now rewrite Htarget.
  - intros [v|[]]; cbn [audit_dfs_encode_model audit_virtual_full_dfs_callbacks
      audit_virtual_full_encode virtual_encoding]; [|reflexivity].
    specialize (Hencode v); destruct (audit_virtual_base_encode cb v);
      cbn in *; now rewrite Hencode.
Qed.

(** * Search erasure *)

(** Nested preparation and DFS retain the result of the ordinary virtual search. *)
Lemma audit_virtual_nested_search_erases V E B (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (pcb : audit_prepare_callback_model (V + unit) (E + V) B)
    (dcb : audit_dfs_callback_model (V + unit) (E + V) B) :
  audit_prepare_callbacks_erase (virtual_encoding EV) (virtual_graph EV g) pcb ->
  audit_dfs_callbacks_erase (virtual_encoding EV) (virtual_graph EV g) dcb ->
  let '(vp, _) := audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    pcb in
  fst (audit_dfs_nested_counted vp dcb FinSet.empty (inr tt :: nil)) = virtual_dfs p.
Proof.
  intros Hprepare Hdfs.
  pose proof (audit_graph_prepare_nested_correct _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    pcb Hprepare) as Hprepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g) pcb)
    as [vp events].
  cbn in Hprepared |- *.
  destruct Hprepared as [Hprepared _]; subst vp.
  change (fst (audit_dfs_nested_counted (virtual_prepared p) dcb FinSet.empty
    (inr tt :: nil)) = virtual_dfs p).
  pose proof (audit_dfs_nested_correct _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) dcb FinSet.empty (inr tt :: nil) Hdfs) as Hresult.
  destruct (audit_dfs_nested_counted (virtual_prepared p) dcb FinSet.empty (inr tt :: nil))
    as [result trace].
  exact (proj1 Hresult).
Qed.

(** Counted virtual search returns the ordinary virtual DFS result. *)
Theorem audit_virtual_search_correct : audit_virtual_search_statement.
Proof.
  intros V E EV g p.
  destruct (audit_virtual_callbacks_correct V E EV g) as [Hprepare [Hdfs _]].
  pose proof (audit_virtual_nested_search_erases V E _ EV g p
    (audit_virtual_prepare_callbacks EV g) (audit_virtual_dfs_callbacks EV g) Hprepare Hdfs)
    as Hsearch.
  unfold audit_virtual_search_counted, audit_virtual_search_with_prepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_prepare_callbacks EV g)) as [vp events].
  destruct (audit_dfs_nested_counted vp (audit_virtual_dfs_callbacks EV g) FinSet.empty
    (inr tt :: nil)) as [result trace]; exact Hsearch.
Qed.

(** Full virtual search returns the ordinary virtual DFS result. *)
Theorem audit_virtual_full_search_correct : audit_virtual_full_search_statement.
Proof.
  intros V E B EV g cb p Hcallbacks.
  destruct (audit_virtual_full_callbacks_correct V E B EV g cb Hcallbacks) as [Hprepare Hdfs].
  pose proof (audit_virtual_nested_search_erases V E _ EV g p
    (audit_virtual_full_prepare_callbacks g cb) (audit_virtual_full_dfs_callbacks cb) Hprepare Hdfs)
    as Hsearch.
  unfold audit_virtual_full_search_counted, audit_virtual_full_search_with_prepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as [vp events].
  destruct (audit_dfs_nested_counted vp (audit_virtual_full_dfs_callbacks cb) FinSet.empty
    (inr tt :: nil)) as [result trace]; exact Hsearch.
Qed.

(** * Entry traversal bounds *)

(** Every counted entry costs at most four events at the input's largest key width. *)
Lemma audit_virtual_entries_bounds V E (EV : encoding V) entries :
  forall seen,
    let '(_, events) := @audit_virtual_entries_counted V E EV seen entries in
    length events <= 1 + 4 * length entries /\
    audit_virtual_entries_work EV events <= audit_virtual_entries_budget EV entries.
Proof.
  induction entries as [|v rest IH]; intro seen.
  - cbn [audit_virtual_entries_counted]; split;
      cbv [audit_virtual_entries_work audit_virtual_entries_budget audit_virtual_entries_width
        audit_virtual_event_work List.fold_right List.map List.length]; lia.
  - cbn [audit_virtual_entries_counted].
    destruct (FinSet.mem EV v seen) eqn:Hmem.
    + specialize (IH seen).
      destruct (audit_virtual_entries_counted EV seen rest) as [result events] eqn:Hrun.
      cbn in IH.
      destruct IH as [Hcount Hwork].
      unfold audit_virtual_entries_budget, audit_virtual_entries_width in *.
      split; [cbn; lia|].
      change (64 + ((64 + (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
        audit_get_weight (encode EV v))) + (64 + audit_virtual_entries_work EV events)) <=
        (1 + 4 * S (length rest)) * (70 + 3 *
          Nat.max (audit_key_bits_weight (encode EV v))
            (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) rest)))).
      unfold audit_encoding_weight, audit_get_weight, audit_set_weight in *.
      pose proof (Nat.le_max_l (audit_key_bits_weight (encode EV v))
        (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) rest))) as Hkey0.
      pose proof (Nat.le_max_r (audit_key_bits_weight (encode EV v))
        (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) rest))) as Hwidth.
      nia.
    + specialize (IH (FinSet.add EV v seen)).
      destruct (audit_virtual_entries_counted EV (FinSet.add EV v seen) rest)
        as [result events] eqn:Hrun.
      cbn in IH.
      destruct IH as [Hcount Hwork].
      unfold audit_virtual_entries_budget, audit_virtual_entries_width in *.
      split; [cbn; lia|].
      change (64 + ((64 + (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
        audit_get_weight (encode EV v))) + (64 + ((64 +
        (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
        audit_set_weight (encode EV v))) + audit_virtual_entries_work EV events))) <=
        (1 + 4 * S (length rest)) * (70 + 3 *
          Nat.max (audit_key_bits_weight (encode EV v))
            (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) rest)))).
      unfold audit_encoding_weight, audit_get_weight, audit_set_weight in *.
      pose proof (Nat.le_max_l (audit_key_bits_weight (encode EV v))
        (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) rest))) as Hkey0.
      pose proof (Nat.le_max_r (audit_key_bits_weight (encode EV v))
        (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) rest))) as Hwidth.
      nia.
Qed.

(** Counted entries preserve their result and satisfy their event and work budgets. *)
Theorem audit_virtual_entries_correct : audit_virtual_entries_statement.
Proof.
  intros V E EV seen entries.
  pose proof (audit_virtual_entries_erases V E EV entries seen) as Herase.
  pose proof (audit_virtual_entries_bounds V E EV entries seen) as Hbounds.
  destruct (audit_virtual_entries_counted EV seen entries) as [result events].
  cbn in Herase, Hbounds |- *; auto.
Qed.

(** One entry's lookup and optional update fit the larger of the head and tail key widths. *)
Lemma audit_virtual_entries_full_step_budget count key width read write tail :
  read <= 5 * key -> write <= 16 * key ->
  tail <= 128 + count * (512 + 32 * width) ->
  64 + ((64 + (5 + read)) + (64 + ((64 + (5 + write)) + tail))) <=
    128 + S count * (512 + 32 * Nat.max key width).
Proof.
  intros Hread Hwrite Htail.
  pose proof (Nat.le_max_l key width) as Hkey.
  pose proof (Nat.le_max_r key width) as Hwidth.
  nia.
Qed.

(** Primitive set reads and updates bound the full entry traversal at the input key width. *)
Lemma audit_virtual_entries_full_bounds V B (EV : encoding V)
    (enc : V -> positive * list B) entries :
  (forall v, fst (enc v) = encode EV v) ->
  forall seen,
    let '(_, events) := audit_virtual_entries_full_counted enc seen entries in
    length events <= 1 + 4 * length entries /\
    audit_virtual_entries_full_internal_work events <= audit_virtual_entries_full_budget EV entries.
Proof.
  intros Henc; induction entries as [|v rest IH]; intro seen.
  - cbn [audit_virtual_entries_full_counted]; split;
      cbv [audit_virtual_entries_full_internal_work audit_virtual_entries_full_budget
        audit_virtual_entries_full_internal_event_work List.fold_right List.length]; lia.
  - cbn [audit_virtual_entries_full_counted].
    pose proof (Henc v) as Hcode.
    unfold audit_finset_mem.
    destruct (enc v) as [code body] eqn:Henc_v; cbn in Hcode.
    pose proof (audit_trie_get_source_work_bound (V * unit)%type code seen) as Hget.
    unfold audit_map_code_get.
    destruct (audit_trie_get code seen) as [found trace] eqn:Hget_run.
    destruct found as [[key value]|].
    + specialize (IH seen).
      destruct (audit_virtual_entries_full_counted enc seen rest) as [result events].
      cbn in IH; destruct IH as [Hcount Hwork].
      split; [cbn; lia|].
      unfold audit_virtual_entries_full_budget, audit_virtual_entries_full_width in *.
      cbn [List.length List.map] in *.
      change (64 + ((64 + (5 + audit_trie_get_source_work code seen)) +
        (64 + audit_virtual_entries_full_internal_work events)) <=
        128 + S (length rest) * (512 + 32 *
          Nat.max (Pos.size_nat (encode EV v))
            (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) rest)))).
      rewrite Hcode in Hget |- *.
      change (audit_virtual_entries_full_internal_work events <=
        128 + length rest * (512 + 32 *
          fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) rest))) in Hwork.
      pose proof (audit_virtual_entries_full_step_budget (length rest)
        (Pos.size_nat (encode EV v))
        (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) rest))
        (audit_trie_get_source_work (encode EV v) seen) 0
        (audit_virtual_entries_full_internal_work events) Hget (Nat.le_0_l _) Hwork) as Hstep.
      lia.
    + unfold audit_finset_add; rewrite Henc_v.
      pose proof (audit_trie_update_source_work_bound (V * unit)%type code (Some (v, tt)) seen)
        as Hupdate.
      unfold audit_trie_set.
      destruct (audit_trie_update code (Some (v, tt)) seen) as [next updates] eqn:Hupdate_run.
      specialize (IH next).
      destruct (audit_virtual_entries_full_counted enc next rest) as [result events].
      cbn in IH; destruct IH as [Hcount Hwork].
      split; [cbn; lia|].
      unfold audit_virtual_entries_full_budget, audit_virtual_entries_full_width in *.
      cbn [List.length List.map] in *.
      change (64 + ((64 + (5 + audit_trie_get_source_work code seen)) +
        (64 + ((64 + (5 + audit_trie_update_source_work code (Some (v, tt)) seen)) +
          audit_virtual_entries_full_internal_work events))) <=
        128 + S (length rest) * (512 + 32 *
          Nat.max (Pos.size_nat (encode EV v))
            (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) rest)))).
      rewrite Hcode in Hget, Hupdate |- *.
      change (audit_virtual_entries_full_internal_work events <=
        128 + length rest * (512 + 32 *
          fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) rest))) in Hwork.
      now apply audit_virtual_entries_full_step_budget.
Qed.

(** Full entries preserve the result and bound both events and primitive work. *)
Theorem audit_virtual_entries_full_correct : audit_virtual_entries_full_statement.
Proof.
  intros V B EV enc seen entries Henc.
  pose proof (audit_virtual_entries_full_erases V B EV enc entries Henc seen) as Herase.
  pose proof (audit_virtual_entries_full_bounds V B EV enc entries Henc seen) as Hbounds.
  destruct (audit_virtual_entries_full_counted enc seen entries) as [result events].
  cbn in Herase, Hbounds |- *; auto.
Qed.

(** Total entry work includes the exact recorded callback-body costs. *)
Theorem audit_virtual_entries_full_total_holds : audit_virtual_entries_full_total_statement.
Proof.
  intros V B EV enc weight seen entries Henc.
  pose proof (audit_virtual_entries_full_correct V B EV enc seen entries Henc) as Hbounds.
  destruct (audit_virtual_entries_full_counted enc seen entries) as [result events].
  cbn in Hbounds |- *; destruct Hbounds as [Herase [_ Hwork]].
  split; [exact Herase|lia].
Qed.

(** * Parent erasure *)

(** A row-event fold with an accumulator equals its zero-based sum plus that accumulator. *)
Lemma audit_erase_fold_offset V (EV : encoding V) events offset :
  fold_right (fun event total => audit_erase_event_work EV event + total) offset events =
    fold_right (fun event total => audit_erase_event_work EV event + total) 0 events + offset.
Proof.
  induction events as [|event rest IH]; cbn [List.fold_right]; lia.
Qed.

(** The row trace charges each retained parent write at its actual encoded key. *)
Lemma audit_erase_rows_adequate V (EV : encoding V) rows :
  let '(result, events) := audit_erase_rows_counted EV rows in
  result = fold_right (fun binding acc =>
    match binding with
    | (inl v, inl parent) => Map.set EV v parent acc
    | _ => acc
    end) Map.empty rows /\
  length events <= 1 + 3 * length rows /\
  fold_right (fun event total => audit_erase_event_work EV event + total) 0 events <=
    (1 + 3 * length rows) * (80 + 4 *
      fold_right (fun row n =>
        match fst row with
        | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
        | inr _ => n
        end) 0 rows).
Proof.
  induction rows as [|[key value] rest IH].
  - cbn [audit_erase_rows_counted]; repeat split;
      cbv [audit_erase_event_work List.length List.fold_right]; lia.
  - cbn [audit_erase_rows_counted].
    destruct (audit_erase_rows_counted EV rest) as [middle events] eqn:Hrun.
    cbn in IH; destruct IH as [Herase [Hcount Hwork]].
    change (fold_right (fun event total => audit_erase_event_work EV event + total) 0 events <=
      (1 + 3 * length rest) * (80 + 4 *
        fold_right (fun row n =>
          match fst row with
          | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
          | inr _ => n
          end) 0 rest)) in Hwork.
    destruct key as [key|[]], value as [value|[]];
      cbn [List.length List.fold_right fst];
      repeat rewrite List.length_app; cbn [List.length].
    all: repeat rewrite fold_right_app; cbn [List.fold_right audit_erase_event_work].
    all: try (split; [now rewrite Herase|]; split; [lia|]).
    all: try (unfold audit_encoding_weight, audit_set_weight in *).
    all: try (pose proof (Nat.le_max_l (audit_key_bits_weight (encode EV key))
      (fold_right (fun row n =>
        match fst row with
        | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
        | inr _ => n
        end) 0 rest)) as Hkey).
    all: try (pose proof (Nat.le_max_r (audit_key_bits_weight (encode EV key))
      (fold_right (fun row n =>
        match fst row with
        | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
        | inr _ => n
        end) 0 rest)) as Hwidth).
    all: rewrite audit_erase_fold_offset.
    all: cbv beta iota zeta delta [audit_erase_event_work audit_encoding_weight
      audit_set_weight] in Hwork |- *.
    all: nia.
Qed.

(** Parent erasure preserves real bindings and bounds its complete model trace. *)
Theorem audit_erase_virtual_correct : audit_erase_virtual_statement.
Proof.
  intros V EV m.
  pose proof (audit_erase_rows_adequate V EV (Map.elements m)) as Hrows.
  unfold audit_erase_virtual_counted.
  destruct (audit_erase_rows_counted EV (Map.elements m)) as [result events] eqn:Hrun.
  cbn in Hrows; destruct Hrows as [Herase [Hcount Hwork]].
  split; [exact Herase|].
  split.
  - unfold audit_erase_event_bound; cbn; lia.
  - unfold audit_erase_virtual_work, audit_erase_virtual_budget, audit_erase_event_bound,
      audit_erase_width.
    cbn [List.length List.fold_right audit_erase_event_work].
    change (128 * S (S (length events)) * S (S (length events)) +
      (64 + 64 * Nat.pow (S (audit_erase_nodes m)) 3 +
        fold_right (fun event total => audit_erase_event_work EV event + total) 0 events) <=
      256 * Nat.pow (S (audit_erase_nodes m)) 3 +
      256 * S (2 + 3 * length (Map.elements m)) * S (2 + 3 * length (Map.elements m)) +
      (2 + 3 * length (Map.elements m)) *
        (80 + 4 * fold_right (fun row n =>
          match fst row with
          | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
          | inr _ => n
          end) 0 (Map.elements m))).
    change (fold_right (fun event total => audit_erase_event_work EV event + total) 0 events <=
      (1 + 3 * length (Map.elements m)) *
        (80 + 4 * fold_right (fun row n =>
          match fst row with
          | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
          | inr _ => n
          end) 0 (Map.elements m))) in Hwork.
    pose proof (Nat.pow_nonzero (S (audit_erase_nodes m)) 3 ltac:(lia)) as Hpow.
    nia.
Qed.

(** Enumeration frames each contribute at least one unit of the element traversal work. *)
Lemma audit_erase_elements_count A (events : list (audit_elements_event A)) :
  length events <= audit_elements_work events.
Proof.
  induction events as [|event rest IH]; cbn [List.length audit_elements_work].
  - lia.
  - destruct event; cbn [audit_elements_frame_work] in *; lia.
Qed.

(** Wrapped enumeration contributes its frame overhead and the original element work. *)
Lemma audit_erase_elements_work V B (weight : B -> nat)
    (events : list (audit_elements_event ((V + unit) * (V + unit)))) :
  audit_erase_nested_work weight (map (@EraseNestedElements V B) events) =
    64 * length events + audit_elements_work events /\
  audit_erase_nested_body_work weight (map (@EraseNestedElements V B) events) = 0.
Proof.
  induction events as [|event rest IH].
  - split; reflexivity.
  - destruct IH as [Hwork Hbody]; split.
    + change (64 + audit_elements_frame_work event +
        audit_erase_nested_work weight (map (@EraseNestedElements V B) rest) =
        64 * S (length rest) + (audit_elements_frame_work event + audit_elements_work rest)).
      rewrite Hwork; lia.
    + change (audit_erase_nested_body_work weight (map (@EraseNestedElements V B) rest) = 0).
      exact Hbody.
Qed.

(** Concatenating nested erasure traces adds their complete and callback-body work. *)
Lemma audit_erase_nested_work_app V B (weight : B -> nat)
    (left right : list (audit_erase_nested_event V B)) :
  audit_erase_nested_work weight (left ++ right) =
    audit_erase_nested_work weight left + audit_erase_nested_work weight right /\
  audit_erase_nested_body_work weight (left ++ right) =
    audit_erase_nested_body_work weight left + audit_erase_nested_body_work weight right.
Proof.
  induction left as [|event rest IH].
  - split; reflexivity.
  - destruct IH as [Hwork Hbody]; split.
    + change (audit_erase_nested_event_work weight event +
        audit_erase_nested_work weight (rest ++ right) =
        (audit_erase_nested_event_work weight event + audit_erase_nested_work weight rest) +
          audit_erase_nested_work weight right).
      rewrite Hwork; lia.
    + change (audit_erase_nested_body_event_work weight event +
        audit_erase_nested_body_work weight (rest ++ right) =
        (audit_erase_nested_body_event_work weight event +
          audit_erase_nested_body_work weight rest) +
          audit_erase_nested_body_work weight right).
      rewrite Hbody; lia.
Qed.

(** Each actual map write is charged to its returned code and its captured encoder body. *)
Lemma audit_erase_nested_set_bound V B (EV : encoding V) (enc : V -> positive * list B)
    (weight : B -> nat) key value middle :
  fst (enc key) = encode EV key ->
  let '(_, events) := audit_map_set enc key value middle in
  audit_erase_nested_work weight (map (@EraseNestedSet V B) events) <=
    66 + 16 * Pos.size_nat (encode EV key) +
      audit_erase_nested_body_work weight (map (@EraseNestedSet V B) events).
Proof.
  intro Henc.
  pose proof (audit_map_set_source_work_bound V V B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key value middle) as Hbound.
  unfold audit_map_set in Hbound |- *.
  destruct (enc key) as [code body] eqn:Hcode; cbn in Henc.
  unfold audit_trie_set in Hbound |- *.
  destruct (audit_trie_update code (Some (key, value)) middle) as [output trace] eqn:Hrun.
  cbn [fst snd] in Hbound |- *.
  cbv beta iota zeta delta [audit_erase_nested_work audit_erase_nested_event_work
    audit_erase_nested_body_work audit_erase_nested_body_event_work audit_map_source_work
    List.map List.fold_right] in Hbound |- *.
  rewrite Henc in Hbound; lia.
Qed.

(** Adding a retained row combines its actual write cost with the tail's key-width bound. *)
Lemma audit_erase_nested_set_step_budget V B (EV : encoding V) (weight : B -> nat)
    key (rest : list ((V + unit) * (V + unit)))
    (events writes : list (audit_erase_nested_event V B)) :
  let width := fold_right (fun row n =>
    match fst row with
    | inl v => Nat.max (Pos.size_nat (encode EV v)) n
    | inr _ => n
    end) 0 rest in
  audit_erase_nested_work weight events <=
    64 + length rest * (256 + 16 * width) + audit_erase_nested_body_work weight events ->
  audit_erase_nested_work weight writes <= 66 + 16 * Pos.size_nat (encode EV key) +
    audit_erase_nested_body_work weight writes ->
  64 + (audit_erase_nested_work weight events + (64 + audit_erase_nested_work weight writes)) <=
    64 + S (length rest) * (256 + 16 * Nat.max (Pos.size_nat (encode EV key)) width) +
      (audit_erase_nested_body_work weight events + audit_erase_nested_body_work weight writes).
Proof.
  cbv beta iota zeta; intros Htail Hwrite.
  pose proof (Nat.le_max_l (Pos.size_nat (encode EV key))
    (fold_right (fun row n =>
      match fst row with
      | inl v => Nat.max (Pos.size_nat (encode EV v)) n
      | inr _ => n
      end) 0 rest)) as Hkey.
  pose proof (Nat.le_max_r (Pos.size_nat (encode EV key))
    (fold_right (fun row n =>
      match fst row with
      | inl v => Nat.max (Pos.size_nat (encode EV v)) n
      | inr _ => n
      end) 0 rest)) as Hwidth.
  nia.
Qed.

(** Nested row erasure preserves its map and charges each actual write and encoder body. *)
Lemma audit_erase_nested_rows_adequate V B (EV : encoding V)
    (enc : V -> positive * list B) (weight : B -> nat) rows :
  (forall v, fst (enc v) = encode EV v) ->
  let '(result, events) := audit_erase_nested_rows enc rows in
  result = fold_right (fun binding acc =>
    match binding with
    | (inl v, inl parent) => Map.set EV v parent acc
    | _ => acc
    end) Map.empty rows /\
  audit_erase_nested_work weight events <=
    64 + length rows * (256 + 16 *
      fold_right (fun row n =>
        match fst row with
        | inl v => Nat.max (Pos.size_nat (encode EV v)) n
        | inr _ => n
        end) 0 rows) + audit_erase_nested_body_work weight events.
Proof.
  intro Henc; induction rows as [|[key value] rest IH].
  - cbn [audit_erase_nested_rows]; split; [reflexivity|].
    cbv [audit_erase_nested_work audit_erase_nested_event_work audit_erase_nested_body_work
      audit_erase_nested_body_event_work List.fold_right List.length]; lia.
  - cbn [audit_erase_nested_rows].
    destruct (audit_erase_nested_rows enc rest) as [middle events] eqn:Hrun.
    cbn in IH; destruct IH as [Herase Hwork].
    change (audit_erase_nested_work weight events <=
      64 + length rest * (256 + 16 * fold_right (fun row n =>
        match fst row with
        | inl v => Nat.max (Pos.size_nat (encode EV v)) n
        | inr _ => n
        end) 0 rest) + audit_erase_nested_body_work weight events) in Hwork.
    destruct key as [key|[]], value as [value|[]].
    + pose proof (audit_map_set_erases V V B enc EV key value middle (Henc key)) as Hset.
      pose proof (audit_erase_nested_set_bound V B EV enc weight key value middle (Henc key))
        as Hsetwork.
      destruct (audit_map_set enc key value middle) as [result writes] eqn:Hwrite.
      cbn in Hset, Hsetwork.
      split; [cbn; now rewrite Hset, Herase|].
      repeat rewrite (proj1 (audit_erase_nested_work_app V B weight _ _)).
      repeat rewrite (proj2 (audit_erase_nested_work_app V B weight _ _)).
      exact (audit_erase_nested_set_step_budget V B EV weight key rest events
        (map EraseNestedSet writes) Hwork Hsetwork).
    + split; [cbn; exact Herase|].
      repeat rewrite (proj1 (audit_erase_nested_work_app V B weight _ _)).
      repeat rewrite (proj2 (audit_erase_nested_work_app V B weight _ _)).
      cbn [List.length fst].
      pose proof (Nat.le_max_r (Pos.size_nat (encode EV key))
        (fold_right (fun row n =>
          match fst row with
          | inl v => Nat.max (Pos.size_nat (encode EV v)) n
          | inr _ => n
          end) 0 rest)) as Hwidth.
      cbv beta iota zeta delta [audit_erase_nested_work audit_erase_nested_event_work
        audit_erase_nested_body_work audit_erase_nested_body_event_work List.fold_right]
        in Hwork |- *; cbn [fst]; nia.
    + split; [cbn; exact Herase|].
      repeat rewrite (proj1 (audit_erase_nested_work_app V B weight _ _)).
      repeat rewrite (proj2 (audit_erase_nested_work_app V B weight _ _)).
      cbv beta iota zeta delta [audit_erase_nested_work audit_erase_nested_event_work
        audit_erase_nested_body_work audit_erase_nested_body_event_work List.fold_right]
        in Hwork |- *; cbn in *; nia.
    + split; [cbn; exact Herase|].
      repeat rewrite (proj1 (audit_erase_nested_work_app V B weight _ _)).
      repeat rewrite (proj2 (audit_erase_nested_work_app V B weight _ _)).
      cbv beta iota zeta delta [audit_erase_nested_work audit_erase_nested_event_work
        audit_erase_nested_body_work audit_erase_nested_body_event_work List.fold_right]
        in Hwork |- *; cbn in *; nia.
Qed.

(** Nested parent erasure preserves real bindings and charges actual writes and encoder bodies. *)
Theorem audit_erase_nested_correct : audit_erase_nested_statement.
Proof.
  intros V B EV enc weight m Henc.
  pose proof (audit_map_elements_erases (V + unit)%type (V + unit)%type m) as Helements.
  pose proof (audit_map_elements_quantitative (V + unit)%type (V + unit)%type m) as Hquant.
  unfold audit_erase_virtual_nested.
  destruct (audit_map_elements m) as [rows element_events] eqn:Helements_run.
  cbn in Helements, Hquant; destruct Hquant as [Hlength Helement_work].
  pose proof (audit_erase_nested_rows_adequate V B EV enc weight rows Henc) as Hrows.
  destruct (audit_erase_nested_rows enc rows) as [result events] eqn:Hrun.
  cbn in Hrows; destruct Hrows as [Hresult Hwork].
  split.
  - unfold erase_virtual_parents; rewrite <- Helements; exact Hresult.
  - rewrite (proj1 (audit_erase_nested_work_app V B weight _ _)).
    rewrite (proj2 (audit_erase_nested_work_app V B weight _ _)).
    destruct (audit_erase_elements_work V B weight element_events) as [Hew Heb].
    rewrite Hew, Heb.
    pose proof (audit_erase_elements_count _ element_events) as Hcount.
    unfold audit_erase_nested_budget, audit_erase_nested_width.
    rewrite <- Helements.
    change (audit_erase_nested_work weight events <=
      64 + length rows * (256 + 16 * fold_right (fun row n =>
        match fst row with
        | inl v => Nat.max (Pos.size_nat (encode EV v)) n
        | inr _ => n
        end) 0 rows) + audit_erase_nested_body_work weight events) in Hwork.
    set (nodes := audit_trie_nodes m) in *.
    set (bits := audit_trie_output_bits m) in *.
    set (width := fold_right (fun row n =>
      match fst row with
      | inl v => Nat.max (Pos.size_nat (encode EV v)) n
      | inr _ => n
      end) 0 rows) in *.
    nia.
Qed.

(** * Original callback receipts *)

(** A virtual event retains the exact original callback return for its actual operand. *)
Definition audit_virtual_body_receipt V E B (cb : audit_virtual_base_callbacks V E B)
    (event : audit_virtual_full_call V E B) : Prop :=
  match event with
  | VirtualFullOut v result body => audit_virtual_base_out cb v = (result, body)
  | VirtualFullTarget e result body => audit_virtual_base_target cb e = (result, body)
  | VirtualFullEncode v result body => audit_virtual_base_encode cb v = (result, body)
  | VirtualFullSource _ _ _ => False
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v code _ _ body _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetMem v code _ _ body _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v code _ _ body _)) =>
      audit_virtual_base_encode cb v = (code, body)
  | _ => True
  end.

(** Every entry-traversal set event records the encoder call made at that occurrence. *)
Lemma audit_virtual_entries_receipts V E B (cb : audit_virtual_base_callbacks V E B) entries :
  forall seen,
    Forall (fun item => audit_virtual_body_receipt V E B cb (VirtualFullEntry item))
      (snd (audit_virtual_entries_full_counted (audit_virtual_base_encode cb) seen entries)).
Proof.
  induction entries as [|v rest IH]; intro seen.
  - repeat constructor.
  - cbn [audit_virtual_entries_full_counted].
    unfold audit_finset_mem.
    destruct (audit_virtual_base_encode cb v) as [code body] eqn:Hencode.
    unfold audit_map_code_get.
    destruct (audit_trie_get code seen) as [found trace].
    destruct found as [[key value]|].
    + specialize (IH seen).
      destruct (audit_virtual_entries_full_counted (audit_virtual_base_encode cb) seen rest)
        as [result events].
      cbn [snd List.map List.app] in *.
      constructor; [exact I|].
      constructor; [exact Hencode|].
      constructor; [exact I|exact IH].
    + unfold audit_finset_add; rewrite Hencode.
      unfold audit_trie_set.
      destruct (audit_trie_update code (Some (v, tt)) seen) as [next updates].
      specialize (IH next).
      destruct (audit_virtual_entries_full_counted (audit_virtual_base_encode cb) next rest)
        as [result events].
      cbn [snd List.map List.app] in *.
      constructor; [exact I|].
      constructor; [exact Hencode|].
      constructor; [exact I|].
      constructor; [exact Hencode|exact IH].
Qed.

(** Lifted output callbacks retain each original output or entry encoder receipt. *)
Lemma audit_virtual_out_receipts V E B (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) vertex :
  Forall (audit_virtual_body_receipt V E B cb) (snd (audit_virtual_full_out g cb vertex)).
Proof.
  destruct vertex as [vertex|[]].
  - unfold audit_virtual_full_out.
    destruct (audit_virtual_base_out cb vertex) as [edges body] eqn:Hout.
    repeat constructor; exact Hout.
  - unfold audit_virtual_full_out.
    pose proof (audit_virtual_entries_receipts V E B cb (Graph.entries g) FinSet.empty) as Hentries.
    destruct (audit_virtual_entries_full_counted (audit_virtual_base_encode cb) FinSet.empty
      (Graph.entries g)) as [entries events].
    cbn in Hentries |- *.
    constructor; [exact I|].
    apply Forall_app; split.
    + apply Forall_map; exact Hentries.
    + repeat constructor.
Qed.

(** Lifted target and encoder callbacks retain the actual original return. *)
Lemma audit_virtual_target_encode_receipts V E B (cb : audit_virtual_base_callbacks V E B) :
  (forall edge,
    Forall (audit_virtual_body_receipt V E B cb) (snd (audit_virtual_full_target cb edge))) /\
  (forall vertex,
    Forall (audit_virtual_body_receipt V E B cb) (snd (audit_virtual_full_encode cb vertex))).
Proof.
  split.
  - intros [edge|vertex]; cbn [audit_virtual_full_target].
    + destruct (audit_virtual_base_target cb edge) as [target body] eqn:Htarget.
      repeat constructor; exact Htarget.
    + repeat constructor.
  - intros [vertex|[]]; cbn [audit_virtual_full_encode].
    + destruct (audit_virtual_base_encode cb vertex) as [code body] eqn:Hencode.
      repeat constructor; exact Hencode.
    + repeat constructor.
Qed.

(** The preparation event body is the callback trace attached to the same source operation. *)
Definition audit_virtual_prepare_body V E B
    (event : audit_prepare_source_event (V + unit) (E + V) (audit_virtual_full_call V E B)) :=
  match event with
  | PrepareSourceOut _ _ body
  | PrepareSourceTarget _ _ body
  | PrepareSourceMap (AuditMapGet _ _ _ _ body _)
  | PrepareSourceMap (AuditMapSet _ _ _ _ _ body _)
  | PrepareSourceMap (AuditMapRemove _ _ _ _ body _) => body
  | _ => nil
  end.

(** A preparation receipt exposes original callback receipts in its attached body. *)
Lemma audit_virtual_prepare_event_receipts V E B (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) event :
  audit_source_receipt (audit_virtual_full_prepare_callbacks g cb) event ->
  Forall (audit_virtual_body_receipt V E B cb) (audit_virtual_prepare_body V E B event).
Proof.
  intro Hreceipt.
  destruct (audit_virtual_target_encode_receipts V E B cb) as [Htarget Hencode].
  destruct event as [site|v outgoing body|edge target body|item|amount|nodes edges fuel];
    cbn [audit_source_receipt audit_virtual_prepare_body audit_virtual_full_prepare_callbacks
      audit_prepare_out_model audit_prepare_target_model audit_prepare_encode_model] in *;
    try constructor.
  - pose proof (audit_virtual_out_receipts V E B g cb v) as Hbody.
    rewrite Hreceipt in Hbody; exact Hbody.
  - specialize (Htarget edge); rewrite Hreceipt in Htarget; exact Htarget.
  - destruct item as [key code input output body trace|key value code input output body trace|
      key code input output body trace];
      cbn [audit_source_receipt audit_virtual_prepare_body audit_virtual_full_prepare_callbacks
        audit_prepare_encode_model] in *;
      specialize (Hencode key); rewrite Hreceipt in Hencode; exact Hencode.
Qed.

(** A DFS capture receipt exposes original callback receipts in its attached body. *)
Lemma audit_virtual_dfs_capture_receipts V E B (cb : audit_virtual_base_callbacks V E B) capture :
  audit_dfs_capture_receipt (audit_virtual_full_dfs_callbacks cb) capture ->
  Forall (audit_virtual_body_receipt V E B cb)
    (match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body
    | AuditGraphEncodeCapture _ _ _ _ _ body => body
    end).
Proof.
  intro Hreceipt.
  destruct (audit_virtual_target_encode_receipts V E B cb) as [Htarget Hencode].
  destruct capture as [edge target body|vertex code body];
    cbn [audit_dfs_capture_receipt audit_virtual_full_dfs_callbacks audit_dfs_target_model
      audit_dfs_encode_model] in Hreceipt |- *.
  - specialize (Htarget edge); rewrite Hreceipt in Htarget; exact Htarget.
  - specialize (Hencode vertex); rewrite Hreceipt in Hencode; exact Hencode.
Qed.

(** * Original input envelopes *)

(** Removing repeated virtual entries cannot increase the length of the input list. *)
Lemma audit_virtual_entries_length V (EV : encoding V) entries :
  forall seen, length (virtual_entries_from EV seen entries) <= length entries.
Proof.
  induction entries as [|v rest IH]; intro seen; cbn.
  - lia.
  - destruct (FinSet.mem EV v seen); cbn.
    + specialize (IH seen); lia.
    + specialize (IH (FinSet.add EV v seen)); lia.
Qed.

(** Each original entry key is bounded by the prepared virtual graph's input width. *)
Lemma audit_virtual_entry_input_width V E (EV : encoding V) (g : Graph.t V E) v :
  In v (Graph.entries g) -> Pos.size_nat (encode EV v) <=
    audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g).
Proof.
  intro Hin.
  assert (Hroot : In (inr tt) (Graph.nodes (virtual_graph EV g))).
  { cbn [virtual_graph]; apply in_or_app; right; cbn; auto. }
  assert (Hedge : In (inr v) (Graph.out (virtual_graph EV g) (inr tt))).
  { cbn [virtual_graph]; apply in_map; apply (proj2 (proj2 (virtual_entries_exact EV g) v));
      exact Hin. }
  pose proof (audit_input_width_edge _ _ (virtual_encoding EV) (virtual_graph EV g)
    (inr tt) (inr v) Hroot Hedge) as Hwidth.
  change (audit_key_bits_weight (encode (virtual_encoding EV) (inl v)) <=
    audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) in Hwidth.
  unfold audit_key_bits_weight in Hwidth.
  change (S (Pos.size_nat (encode EV v)) <=
    audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) in Hwidth.
  lia.
Qed.

(** The full entry width is bounded by the virtual graph preparation width. *)
Lemma audit_virtual_entries_input_width V E (EV : encoding V) (g : Graph.t V E) :
  audit_virtual_entries_full_width EV (Graph.entries g) <=
    audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g).
Proof.
  unfold audit_virtual_entries_full_width.
  set (width := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)).
  assert (Hall : forall v, In v (Graph.entries g) -> Pos.size_nat (encode EV v) <= width).
  { intros v Hin; apply audit_virtual_entry_input_width; exact Hin. }
  generalize (Graph.entries g) Hall; intros entries Hentries.
  induction entries as [|v rest IH]; cbn [List.map List.fold_right].
  - lia.
  - apply Nat.max_lub.
    + apply Hentries; left; reflexivity.
    + apply IH; intros item Hin; apply Hentries; now right.
Qed.

(** Mapping entry events into full callbacks adds one outer frame per event. *)
Lemma audit_virtual_entry_outer_work V E B (events : list (audit_virtual_entries_full_event V B)) :
  fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0
    (map (@VirtualFullEntry V E B) events) =
  64 * length events + audit_virtual_entries_full_internal_work events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - change (64 + audit_virtual_entries_full_internal_event_work event +
      fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0
        (map (@VirtualFullEntry V E B) rest) =
      64 * S (length rest) +
        (audit_virtual_entries_full_internal_event_work event +
          audit_virtual_entries_full_internal_work rest)).
    rewrite IH; lia.
Qed.

(** Every virtual node's outgoing list is bounded by original nodes, entries, and edges. *)
Lemma audit_virtual_out_size V E (EV : encoding V) (g : Graph.t V E) vertex :
  In vertex (Graph.nodes (virtual_graph EV g)) ->
  length (Graph.out (virtual_graph EV g) vertex) <=
    1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g.
Proof.
  destruct vertex as [v|[]]; intro Hin.
  - cbn [virtual_graph] in Hin |- *.
    apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + apply in_map_iff in Hin; destruct Hin as [u [Heq Hin]]; inversion Heq; subst u.
      pose proof (audit_edge_count_member V E g (Graph.nodes g) v Hin) as Hedges.
      change (length (map (@inl E V) (Graph.out g v)) <=
        1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g).
      rewrite length_map; unfold edge_count in *; lia.
    + cbn in Hin; destruct Hin as [Heq|Hin]; [discriminate|contradiction].
  - change (length (map (@inr E V) (virtual_entries EV g)) <=
      1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g).
    rewrite length_map.
    unfold virtual_entries; pose proof (audit_virtual_entries_length V EV (Graph.entries g)
      FinSet.empty) as Hentries; lia.
Qed.

(** A virtual-event fold adds an arbitrary tail charge to its zero-based sum. *)
Lemma audit_virtual_full_fold_offset V E B
    (events : list (audit_virtual_full_call V E B)) offset :
  fold_right (fun item n => audit_virtual_full_internal_event_work item + n) offset events =
    fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0 events + offset.
Proof.
  induction events as [|event rest IH]; cbn [List.fold_right]; lia.
Qed.

(** A lifted output callback's internal work is bounded by the original graph input. *)
Lemma audit_virtual_full_out_internal_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) vertex :
  audit_virtual_base_callbacks_erase EV g cb ->
  In vertex (Graph.nodes (virtual_graph EV g)) ->
  fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0
    (snd (audit_virtual_full_out g cb vertex)) <=
    8 * S (length (Graph.entries g)) *
      (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV)
        (virtual_graph EV g)) + 1 + length (Graph.nodes g) +
          length (Graph.entries g) + edge_count g).
Proof.
  intros [Hout [_ Hencode]] Hnode.
  pose proof (audit_virtual_out_size V E EV g vertex Hnode) as Hsize.
  destruct vertex as [v|[]].
  - specialize (Hout v); unfold audit_virtual_full_out.
    destruct (audit_virtual_base_out cb v) as [edges body]; cbn in Hout.
    change (length (map (@inl E V) (Graph.out g v)) <=
      1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g) in Hsize.
    rewrite length_map, <- Hout in Hsize.
    cbv beta iota zeta delta [snd List.fold_right audit_virtual_full_internal_event_work].
    nia.
  - pose proof (audit_virtual_entries_full_correct V B EV (audit_virtual_base_encode cb)
      FinSet.empty (Graph.entries g) Hencode) as Hentries.
    pose proof (audit_virtual_entries_input_width V E EV g) as Hwidth.
    pose proof (audit_virtual_entries_length V EV (Graph.entries g) FinSet.empty) as Hlength.
    unfold audit_virtual_full_out.
    destruct (audit_virtual_entries_full_counted (audit_virtual_base_encode cb) FinSet.empty
      (Graph.entries g)) as [entries events] eqn:Hrun.
    cbv beta iota zeta in Hentries; destruct Hentries as [Herase [Hcount Hwork]].
    rewrite <- Herase in Hlength.
    change (64 + fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0
      (map (@VirtualFullEntry V E B) events ++ (VirtualFullMap (length entries) :: nil)) <=
      8 * S (length (Graph.entries g)) *
        (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV)
          (virtual_graph EV g)) + 1 + length (Graph.nodes g) + length (Graph.entries g) +
          edge_count g)).
    rewrite fold_right_app, audit_virtual_full_fold_offset, audit_virtual_entry_outer_work.
    cbn [List.fold_right audit_virtual_full_internal_event_work].
    unfold audit_virtual_entries_full_budget in Hwork.
    change (64 + (64 * length events + audit_virtual_entries_full_internal_work events +
      ((64 + S (length entries)) + 0)) <=
      8 * S (length (Graph.entries g)) *
        (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV)
          (virtual_graph EV g)) + 1 + length (Graph.nodes g) + length (Graph.entries g) +
          edge_count g)).
    set (n := length (Graph.entries g)) in *.
    set (w := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) in *.
    set (ew := audit_virtual_entries_full_width EV (Graph.entries g)) in *.
    set (c := length events) in *.
    set (actual := length entries) in *.
    set (work := audit_virtual_entries_full_internal_work events) in *.
    assert (Hproduct : n * (512 + 32 * ew) <= n * (512 + 32 * w)).
    { apply Nat.mul_le_mono_l; lia. }
    clear - Hcount Hwork Hwidth Hlength Hproduct.
    nia.
Qed.

(** * Preparation callback domains *)

(** A preparation output event names a node from the traversed input list. *)
Definition audit_prepare_out_in_nodes V E B (nodes : list V)
    (event : audit_prepare_source_event V E B) : Prop :=
  match event with
  | PrepareSourceOut v _ _ => In v nodes
  | _ => True
  end.

(** Set and lookup event wrappers do not introduce preparation output calls. *)
Lemma audit_prepare_map_events_in_nodes V E B nodes (items : list (audit_map_event V (list E) B)) :
  Forall (audit_prepare_out_in_nodes V E B nodes) (map PrepareSourceMap items).
Proof.
  apply Forall_forall; intros event Hin.
  apply in_map_iff in Hin; destruct Hin as [item [Heq _]]; subst event; exact I.
Qed.

(** Source edge traversal emits no output callback events. *)
Lemma audit_prepare_edges_out_in_nodes V E B (cb : audit_prepare_callback_model V E B)
    nodes edges :
  forall initial,
    Forall (audit_prepare_out_in_nodes V E B nodes)
      (snd (audit_prepare_source_edges cb edges initial)).
Proof.
  induction edges as [|edge rest IH]; intro initial.
  - repeat constructor.
  - cbn [audit_prepare_source_edges].
    specialize (IH initial).
    destruct (audit_prepare_source_edges cb rest initial) as [middle later].
    destruct (audit_prepare_target_model cb edge) as [target target_body].
    destruct (audit_map_get (audit_prepare_encode_model cb) target middle) as [found reads].
    destruct (audit_map_set (audit_prepare_encode_model cb) target
      (edge :: match found with
        | Some xs => xs
        | None => nil
        end) middle) as [result writes].
    cbn [snd] in IH |- *.
    constructor; [exact I|].
    repeat rewrite Forall_app; repeat split; try exact IH;
      try apply audit_prepare_map_events_in_nodes;
      repeat constructor.
Qed.

(** Source output construction only calls output on nodes in its original list. *)
Lemma audit_prepare_out_out_in_nodes V E B (cb : audit_prepare_callback_model V E B)
    all nodes :
  (forall v, In v nodes -> In v all) ->
  forall initial, Forall (audit_prepare_out_in_nodes V E B all)
    (snd (audit_prepare_source_out cb nodes initial)).
Proof.
  intro Hinclusion; induction nodes as [|v rest IH]; intro initial.
  - repeat constructor.
  - cbn [audit_prepare_source_out].
    specialize (IH (fun x Hin => Hinclusion x (or_intror Hin)) initial).
    destruct (audit_prepare_source_out cb rest initial) as [middle events].
    destruct (audit_prepare_out_model cb v) as [out body].
    destruct (audit_map_set (audit_prepare_encode_model cb) v out middle) as [result writes].
    cbn [snd] in IH |- *.
    constructor; [exact I|].
    repeat rewrite Forall_app; repeat split; try exact IH;
      try apply audit_prepare_map_events_in_nodes.
    constructor; [apply Hinclusion; now left|constructor].
Qed.

(** Incoming-index construction only calls output on nodes in its original list. *)
Lemma audit_prepare_in_out_in_nodes V E B (cb : audit_prepare_callback_model V E B) all nodes :
  (forall v, In v nodes -> In v all) ->
  forall initial, Forall (audit_prepare_out_in_nodes V E B all)
    (snd (audit_prepare_source_in cb nodes initial)).
Proof.
  intro Hinclusion; induction nodes as [|v rest IH]; intro initial.
  - repeat constructor.
  - cbn [audit_prepare_source_in].
    specialize (IH (fun x Hin => Hinclusion x (or_intror Hin)) initial).
    destruct (audit_prepare_source_in cb rest initial) as [middle events].
    destruct (audit_prepare_out_model cb v) as [out body].
    pose proof (audit_prepare_edges_out_in_nodes V E B cb all out middle) as Hedges.
    destruct (audit_prepare_source_edges cb out middle) as [result edge_events] eqn:Hedges_run.
    cbn [snd] in IH, Hedges |- *.
    constructor; [exact I|].
    repeat rewrite Forall_app; repeat split; try exact IH; try exact Hedges.
    constructor; [apply Hinclusion; now left|constructor].
Qed.

(** Edge counting only calls output on nodes in its original list. *)
Lemma audit_prepare_count_out_in_nodes V E B (cb : audit_prepare_callback_model V E B) all nodes :
  (forall v, In v nodes -> In v all) ->
  Forall (audit_prepare_out_in_nodes V E B all) (snd (audit_prepare_source_edge_count cb nodes)).
Proof.
  intro Hinclusion; induction nodes as [|v rest IH].
  - repeat constructor.
  - cbn [audit_prepare_source_edge_count].
    specialize (IH (fun x Hin => Hinclusion x (or_intror Hin))).
    destruct (audit_prepare_source_edge_count cb rest) as [count events].
    destruct (audit_prepare_out_model cb v) as [out body].
    cbn [snd] in IH |- *.
    constructor; [exact I|].
    apply Forall_app; split; [exact IH|].
    constructor; [apply Hinclusion; now left|].
    repeat constructor.
Qed.

(** Every preparation output callback is made at a node of the original graph input. *)
Lemma audit_prepare_source_out_in_nodes V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) :
  Forall (audit_prepare_out_in_nodes V E B (Graph.nodes g))
    (snd (audit_prepare_source_counted EV g cb)).
Proof.
  pose proof (audit_prepare_out_out_in_nodes V E B cb (Graph.nodes g) (Graph.nodes g)
    (fun _ H => H) Map.empty) as Hout.
  pose proof (audit_prepare_in_out_in_nodes V E B cb (Graph.nodes g) (Graph.nodes g)
    (fun _ H => H) Map.empty) as Hin.
  pose proof (audit_prepare_count_out_in_nodes V E B cb (Graph.nodes g) (Graph.nodes g)
    (fun _ H => H)) as Hcount.
  unfold audit_prepare_source_counted.
  destruct (audit_prepare_source_out cb (Graph.nodes g) Map.empty) as [out out_events].
  destruct (audit_prepare_source_in cb (Graph.nodes g) Map.empty) as [incoming in_events].
  destruct (audit_prepare_source_edge_count cb (Graph.nodes g)) as [edges edge_events].
  cbn [snd] in Hout, Hin, Hcount |- *.
  repeat rewrite Forall_app; repeat split; try assumption; repeat constructor.
Qed.

(** Target and encoder wrappers have fixed internal frame costs. *)
Lemma audit_virtual_target_encode_internal_bound V E B (cb : audit_virtual_base_callbacks V E B) :
  (forall edge, fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0
    (snd (audit_virtual_full_target cb edge)) <= 128) /\
  (forall vertex, fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0
    (snd (audit_virtual_full_encode cb vertex)) <= 128).
Proof.
  split.
  - intros [edge|v]; unfold audit_virtual_full_target.
    + destruct (audit_virtual_base_target cb edge); reflexivity.
    + cbv [snd List.fold_right audit_virtual_full_internal_event_work]; lia.
  - intros [v|[]]; unfold audit_virtual_full_encode.
    + destruct (audit_virtual_base_encode cb v); reflexivity.
    + cbv [snd List.fold_right audit_virtual_full_internal_event_work]; lia.
Qed.

(** A preparation receipt charges internal callback work at a bounded actual operand. *)
Lemma audit_virtual_prepare_event_internal_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) event :
  audit_virtual_base_callbacks_erase EV g cb ->
  audit_source_receipt (audit_virtual_full_prepare_callbacks g cb) event ->
  audit_prepare_out_in_nodes _ _ _ (Graph.nodes (virtual_graph EV g)) event ->
  audit_prepare_source_body_event_work audit_virtual_full_internal_event_work event <=
    8 * S (length (Graph.entries g)) *
      (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV)
        (virtual_graph EV g)) + 1 + length (Graph.nodes g) +
          length (Graph.entries g) + edge_count g).
Proof.
  intros Hcallbacks Hreceipt Hnode.
  destruct (audit_virtual_target_encode_internal_bound V E B cb) as [Htarget Hencode].
  destruct event as [site|v outgoing body|edge target body|item|amount|nodes edges fuel];
    cbn [audit_source_receipt audit_prepare_source_body_event_work audit_prepare_out_in_nodes
      audit_virtual_full_prepare_callbacks audit_prepare_out_model audit_prepare_target_model
      audit_prepare_encode_model] in *; try nia.
  - pose proof (audit_virtual_full_out_internal_bound V E B EV g cb v Hcallbacks Hnode) as Hbody.
    rewrite Hreceipt in Hbody; cbn [snd] in Hbody; exact Hbody.
  - specialize (Htarget edge); rewrite Hreceipt in Htarget; cbn [snd] in Htarget; nia.
  - destruct item as [key code input output body trace|key value code input output body trace|
      key code input output body trace];
      cbn [audit_source_receipt audit_prepare_source_body_event_work
        audit_virtual_full_prepare_callbacks audit_prepare_encode_model] in *;
      specialize (Hencode key); rewrite Hreceipt in Hencode; cbn [snd] in Hencode; nia.
Qed.

(** Preparation's complete internal callback work is bounded by its event count. *)
Lemma audit_virtual_prepare_internal_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) events :
  audit_virtual_base_callbacks_erase EV g cb ->
  Forall (audit_source_receipt (audit_virtual_full_prepare_callbacks g cb)) events ->
  Forall (audit_prepare_out_in_nodes _ _ _ (Graph.nodes (virtual_graph EV g))) events ->
  audit_prepare_source_body_work audit_virtual_full_internal_event_work events <=
    length events * (8 * S (length (Graph.entries g)) *
      (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV)
        (virtual_graph EV g)) + 1 + length (Graph.nodes g) +
          length (Graph.entries g) + edge_count g)).
Proof.
  intros Hcallbacks Hreceipts Hnodes.
  induction Hreceipts as [|event rest Hreceipt Htail IH].
  - reflexivity.
  - inversion Hnodes as [|? ? Hnode Hnodes_tail]; subst.
    specialize (IH Hnodes_tail).
    pose proof (audit_virtual_prepare_event_internal_bound V E B EV g cb event
      Hcallbacks Hreceipt Hnode) as Hbound.
    change (audit_prepare_source_body_event_work audit_virtual_full_internal_event_work event +
      audit_prepare_source_body_work audit_virtual_full_internal_event_work rest <=
      length (event :: rest) * (8 * S (length (Graph.entries g)) *
        (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV)
          (virtual_graph EV g)) + 1 + length (Graph.nodes g) + length (Graph.entries g) +
          edge_count g))).
    cbn [List.length]; nia.
Qed.

(** A well-formed DFS source event contains at most one callback capture. *)
Lemma audit_virtual_dfs_capture_count V E B
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) :
  audit_dfs_source_event_wellformed item -> length (snd item) <= 1.
Proof.
  destruct item as [event body]; destruct event as [site|edge target|v input found|
    v input found|v via before after|v before after|detail|pre post];
    cbn [audit_dfs_source_event_wellformed snd]; intro Hshape;
    try (subst body; cbn; lia).
  all: try (destruct detail; cbn [audit_dfs_source_event_wellformed] in Hshape;
    try (subst body; cbn; lia)).
  all: destruct Hshape as [code [trace Hbody]] || destruct Hshape as [trace Hbody];
    subst body; cbn; lia.
Qed.

(** A same-run DFS capture's internal wrapper work costs at most two fixed frames. *)
Lemma audit_virtual_dfs_capture_internal_bound V E B (cb : audit_virtual_base_callbacks V E B)
    capture :
  audit_dfs_capture_receipt (audit_virtual_full_dfs_callbacks cb) capture ->
  audit_graph_capture_work audit_virtual_full_internal_event_work capture <= 128.
Proof.
  intro Hreceipt.
  destruct (audit_virtual_target_encode_internal_bound V E B cb) as [Htarget Hencode].
  destruct capture as [edge target body|vertex code body];
    cbn [audit_dfs_capture_receipt audit_virtual_full_dfs_callbacks audit_dfs_target_model
      audit_dfs_encode_model] in Hreceipt.
  - specialize (Htarget edge); rewrite Hreceipt in Htarget; exact Htarget.
  - specialize (Hencode vertex); rewrite Hreceipt in Hencode; exact Hencode.
Qed.

(** A well-formed DFS event's captured wrapper costs at most two fixed frames. *)
Lemma audit_virtual_dfs_event_internal_bound V E B (cb : audit_virtual_base_callbacks V E B) item :
  audit_dfs_source_event_wellformed item ->
  audit_dfs_event_receipts (audit_virtual_full_dfs_callbacks cb) item ->
  fold_right (fun capture n => audit_graph_capture_work audit_virtual_full_internal_event_work
    capture + n) 0 (snd item) <= 128.
Proof.
  intros Hshape Hreceipts.
  pose proof (audit_virtual_dfs_capture_count (V + unit)%type (E + V)%type
    (audit_virtual_full_call V E B) item Hshape)
    as Hcount.
  unfold audit_dfs_event_receipts in Hreceipts.
  destruct (snd item) as [|capture rest] eqn:Hbody.
  - cbn; lia.
  - destruct rest as [|next rest]; cbn in Hcount; [|lia].
    inversion Hreceipts as [|? ? Hreceipt Htail].
    cbn [List.fold_right]; pose proof (audit_virtual_dfs_capture_internal_bound V E B cb capture
      Hreceipt); lia.
Qed.

(** DFS's complete internal callback work is bounded by its event count. *)
Lemma audit_virtual_dfs_internal_bound V E B (cb : audit_virtual_base_callbacks V E B) events :
  Forall audit_dfs_source_event_wellformed events ->
  Forall (audit_dfs_event_receipts (audit_virtual_full_dfs_callbacks cb)) events ->
  audit_dfs_source_body_work audit_virtual_full_internal_event_work events <= 128 * length events.
Proof.
  intros Hshape Hreceipts; induction Hshape as [|item rest Hitem Htail IH].
  - reflexivity.
  - inversion Hreceipts as [|? ? Hreceipt Hrest]; subst.
    specialize (IH Hrest).
    pose proof (audit_virtual_dfs_event_internal_bound V E B cb item Hitem Hreceipt) as Hbound.
    change (fold_right (fun capture n => audit_graph_capture_work
      audit_virtual_full_internal_event_work capture + n) 0 (snd item) +
      audit_dfs_source_body_work audit_virtual_full_internal_event_work rest <=
        128 * length (item :: rest)).
    cbn [List.length]; lia.
Qed.

(** Summing two per-item prices preserves both components of the same trace. *)
Lemma audit_virtual_fold_add A (first second : A -> nat) items :
  fold_right (fun item n => first item + second item + n) 0 items =
    fold_right (fun item n => first item + n) 0 items +
    fold_right (fun item n => second item + n) 0 items.
Proof.
  induction items as [|item rest IH]; cbn [List.fold_right]; lia.
Qed.

(** Preparation source body sums split internal and external prices on the same events. *)
Lemma audit_virtual_prepare_body_add V E X Y B (weight : B -> nat)
    (events : list (audit_prepare_source_event V E (audit_virtual_full_call X Y B))) :
  audit_prepare_source_body_work
    (fun item => audit_virtual_full_internal_event_work item +
      audit_virtual_full_body_event_work weight item) events =
  audit_prepare_source_body_work audit_virtual_full_internal_event_work events +
  audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - change (audit_prepare_source_body_event_work
      (fun item => audit_virtual_full_internal_event_work item +
        audit_virtual_full_body_event_work weight item) event +
      audit_prepare_source_body_work
        (fun item => audit_virtual_full_internal_event_work item +
          audit_virtual_full_body_event_work weight item) rest =
      (audit_prepare_source_body_event_work audit_virtual_full_internal_event_work event +
        audit_prepare_source_body_work audit_virtual_full_internal_event_work rest) +
      (audit_prepare_source_body_event_work (audit_virtual_full_body_event_work weight) event +
        audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) rest)).
    rewrite IH.
    destruct event as [site|v outgoing body|edge target body|item|amount|nodes edges fuel];
      cbn [audit_prepare_source_body_event_work]; try lia;
      try (rewrite audit_virtual_fold_add; lia).
    destruct item; cbn [audit_prepare_source_body_event_work]; rewrite audit_virtual_fold_add; lia.
Qed.

(** DFS source body sums split internal and external prices on the same captures. *)
Lemma audit_virtual_dfs_body_add V E X Y B (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E
      (audit_graph_callback_capture V E (audit_virtual_full_call X Y B)))) :
  audit_dfs_source_body_work
    (fun item => audit_virtual_full_internal_event_work item +
      audit_virtual_full_body_event_work weight item) events =
  audit_dfs_source_body_work audit_virtual_full_internal_event_work events +
  audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) events.
Proof.
  induction events as [|[event captures] rest IH].
  - reflexivity.
  - assert (Hcaptures : fold_right (fun capture n => audit_graph_capture_work
        (fun item => audit_virtual_full_internal_event_work item +
          audit_virtual_full_body_event_work weight item) capture + n) 0 captures =
      fold_right (fun capture n => audit_graph_capture_work
        audit_virtual_full_internal_event_work capture + n) 0 captures +
      fold_right (fun capture n => audit_graph_capture_work
        (audit_virtual_full_body_event_work weight) capture + n) 0 captures).
    { induction captures as [|capture tail IHcapture]; cbn [List.fold_right]; [reflexivity|].
      destruct capture; cbn [audit_graph_capture_work]; rewrite audit_virtual_fold_add, IHcapture;
        lia. }
    change (fold_right (fun capture n => audit_graph_capture_work
      (fun item => audit_virtual_full_internal_event_work item +
        audit_virtual_full_body_event_work weight item) capture + n) 0 captures +
      audit_dfs_source_body_work
        (fun item => audit_virtual_full_internal_event_work item +
          audit_virtual_full_body_event_work weight item) rest =
      (fold_right (fun capture n => audit_graph_capture_work
        audit_virtual_full_internal_event_work capture + n) 0 captures +
        audit_dfs_source_body_work audit_virtual_full_internal_event_work rest) +
      (fold_right (fun capture n => audit_graph_capture_work
        (audit_virtual_full_body_event_work weight) capture + n) 0 captures +
        audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) rest)).
    rewrite Hcaptures, IH; lia.
Qed.

(** Input event limits cover all preparation and DFS callback wrapper work. *)
Lemma audit_virtual_internal_input_budget V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) prepcalls dfscalls :
  prepcalls <= audit_graph_prepare_full_event_bound (virtual_graph EV g) ->
  dfscalls <= audit_dfs_full_input_event_bound (virtual_prepared p) (inr tt :: nil) ->
  prepcalls * (8 * S (length (Graph.entries g)) *
    (1024 + 128 * S (audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) +
      1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g)) + 128 * dfscalls <=
    audit_virtual_full_search_input_budget EV g.
Proof.
  intros Hprep_count Hdfs_count.
  unfold audit_virtual_full_search_input_budget; fold (virtual_prepared p).
  set (prep_count := audit_graph_prepare_full_event_bound (virtual_graph EV g)) in *.
  set (dfs_count := audit_dfs_full_input_event_bound (virtual_prepared p) (inr tt :: nil)) in *.
  set (pwidth := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) in *.
  set (dwidth := audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (inr tt :: nil)) in *.
  set (n := length (Graph.entries g)) in *.
  set (size := 1 + length (Graph.nodes g) + n + edge_count g) in *.
  replace (1024 + 128 * S pwidth + 1 + length (Graph.nodes g) + n + edge_count g)
    with (1024 + 128 * S pwidth + size) by (unfold size; lia).
  set (unit_budget := 8 * S n * (1024 + 128 * S (Nat.max pwidth dwidth) + size)).
  assert (Hbudget : 8 * S n * (1024 + 128 * S pwidth + size) <= unit_budget).
  { unfold unit_budget; apply Nat.mul_le_mono_l.
    pose proof (Nat.le_max_l pwidth dwidth); lia. }
  assert (Hbudget128 : 128 <= unit_budget) by (unfold unit_budget; clear; nia).
  assert (Hprep_total : prepcalls * (8 * S n * (1024 + 128 * S pwidth + size)) <=
    prep_count * unit_budget) by (apply Nat.mul_le_mono; assumption).
  assert (Hdfs_total : 128 * dfscalls <= dfs_count * unit_budget).
  { replace (128 * dfscalls) with (dfscalls * 128) by lia.
    apply Nat.mul_le_mono; assumption. }
  fold unit_budget; rewrite Nat.mul_add_distr_r; lia.
Qed.

(** Source search preserves its prepared graph and DFS result and prices actual callback bodies. *)
Theorem audit_virtual_source_search_holds : audit_virtual_source_search_statement.
Proof.
  intros V E B EV g p cb weight Hcallbacks.
  destruct (audit_virtual_full_callbacks_correct V E B EV g cb Hcallbacks) as [Hprepare Hdfs].
  set (body_weight := fun item => audit_virtual_full_internal_event_work item +
    audit_virtual_full_body_event_work weight item).
  pose proof (audit_prepare_source_with_receipts _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb) body_weight Hprepare) as Hprep_run.
  pose proof (audit_prepare_source_out_in_nodes _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as Hnodes.
  unfold audit_virtual_source_search.
  destruct (audit_prepare_source_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as [vp prepare_events] eqn:Hprepare_run.
  cbv beta iota zeta in Hprep_run, Hnodes |- *.
  destruct Hprep_run as [Hvp [Hprep_count [Hprep_work Hprep_receipts]]].
  pose proof (audit_virtual_prepare_internal_bound V E B EV g cb prepare_events Hcallbacks
    Hprep_receipts Hnodes) as Hprep_internal.
  subst vp.
  pose proof (audit_dfs_source_correct _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (audit_virtual_full_dfs_callbacks cb) body_weight FinSet.empty
    (inr tt :: nil) Hdfs) as Hdfs_run.
  pose proof (audit_dfs_source_receipts (virtual_prepared p) (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty (inr tt :: nil)) as Hdfs_receipts.
  fold (virtual_prepared p).
  destruct (audit_dfs_source_counted (virtual_prepared p) (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty (inr tt :: nil)) as [result dfs_events] eqn:Hdfs_run_eq.
  cbv beta iota zeta in Hdfs_run, Hdfs_receipts |- *.
  destruct Hdfs_run as [Hresult [Hshape [Hdfs_count Hdfs_work]]].
  pose proof (audit_virtual_dfs_internal_bound V E B cb dfs_events Hshape Hdfs_receipts)
    as Hdfs_internal.
  split; [reflexivity|].
  split; [exact Hresult|].
  change (audit_prepare_source_work body_weight prepare_events +
    audit_dfs_source_work body_weight dfs_events <= audit_virtual_source_search_budget EV g +
    audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
    audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events).
  unfold body_weight in Hprep_work, Hdfs_work.
  rewrite audit_virtual_prepare_body_add in Hprep_work.
  rewrite audit_virtual_dfs_body_add in Hdfs_work.
  pose proof (audit_virtual_internal_input_budget V E EV g p (length prepare_events)
    (length dfs_events) Hprep_count Hdfs_count) as Hbudget.
  unfold audit_virtual_source_search_budget.
  fold (virtual_prepared p).
  fold body_weight in Hprep_work, Hdfs_work.
  lia.
Qed.

(** * Model callback costs *)

(** The simple and full entry-width functions measure the same original keys. *)
Lemma audit_virtual_entry_widths_agree V (EV : encoding V) entries :
  audit_virtual_entries_width EV entries = audit_virtual_entries_full_width EV entries.
Proof.
  reflexivity.
Qed.

(** Appending model callback events adds their work. *)
Lemma audit_virtual_entries_work_app V E (EV : encoding V)
    (left right : list (audit_virtual_call V E)) :
  audit_virtual_entries_work EV (left ++ right) =
    audit_virtual_entries_work EV left + audit_virtual_entries_work EV right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - change (audit_virtual_event_work EV event + audit_virtual_entries_work EV (rest ++ right) =
      (audit_virtual_event_work EV event + audit_virtual_entries_work EV rest) +
        audit_virtual_entries_work EV right).
    rewrite IH; lia.
Qed.

(** The model output callback is priced using the original virtual graph input. *)
Lemma audit_virtual_out_model_bound V E (EV : encoding V) (g : Graph.t V E) vertex :
  In vertex (Graph.nodes (virtual_graph EV g)) ->
  audit_virtual_entries_work EV (snd (audit_virtual_out_counted EV g vertex)) <=
    8 * S (length (Graph.entries g)) *
      (256 + 6 * audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) +
        1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g).
Proof.
  intro Hnode; pose proof (audit_virtual_out_size V E EV g vertex Hnode) as Hsize.
  destruct vertex as [v|[]].
  - change (length (map (@inl E V) (Graph.out g v)) <=
      1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g) in Hsize.
    rewrite length_map in Hsize.
    unfold audit_virtual_out_counted.
    cbv beta iota zeta delta [snd audit_virtual_entries_work audit_virtual_event_work
      List.fold_right].
    nia.
  - pose proof (audit_virtual_entries_correct V E EV FinSet.empty (Graph.entries g)) as Hentries.
    pose proof (audit_virtual_entries_input_width V E EV g) as Hwidth.
    pose proof (audit_virtual_entries_length V EV (Graph.entries g) FinSet.empty) as Hlength.
    unfold audit_virtual_out_counted.
    destruct (audit_virtual_entries_counted EV FinSet.empty (Graph.entries g)) as [entries events].
    cbv beta iota zeta in Hentries; destruct Hentries as [Herase [Hcount Hwork]].
    rewrite <- Herase in Hlength.
    change (audit_virtual_entries_work EV (AuditVirtualCase 5 ::
      events ++ (AuditVirtualMap (length entries) :: nil)) <=
      8 * S (length (Graph.entries g)) *
        (256 + 6 * audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) +
          1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g)).
    change (64 + audit_virtual_entries_work EV (events ++ (AuditVirtualMap (length entries) :: nil))
      <= 8 * S (length (Graph.entries g)) *
        (256 + 6 * audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) +
          1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g)).
    rewrite audit_virtual_entries_work_app.
    change (64 + (audit_virtual_entries_work EV events + ((64 + S (length entries)) + 0)) <=
      8 * S (length (Graph.entries g)) *
        (256 + 6 * audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) +
          1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g)).
    unfold audit_virtual_entries_budget in Hwork.
    rewrite audit_virtual_entry_widths_agree in Hwork.
    set (n := length (Graph.entries g)) in *.
    set (w := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) in *.
    set (ew := audit_virtual_entries_full_width EV (Graph.entries g)) in *.
    set (actual := length entries) in *.
    set (work := audit_virtual_entries_work EV events) in *.
    assert (Hproduct : (1 + 4 * n) * (70 + 3 * ew) <= (1 + 4 * n) * (70 + 3 * w)).
    { apply Nat.mul_le_mono_l; lia. }
    clear - Hwork Hwidth Hlength Hproduct.
    nia.
Qed.

(** Target wrappers use at most two constant model frames. *)
Lemma audit_virtual_target_model_bound V E (EV : encoding V) (g : Graph.t V E) edge :
  audit_virtual_entries_work EV (snd (audit_virtual_target_counted g edge)) <= 128.
Proof.
  destruct edge; cbv [audit_virtual_target_counted audit_virtual_entries_work
    audit_virtual_event_work snd List.fold_right]; lia.
Qed.

(** Encoder wrapper work is linear in the actual virtual vertex code width. *)
Lemma audit_virtual_encode_model_bound V E (EV : encoding V) vertex :
  audit_virtual_entries_work EV (snd (@audit_virtual_encode_counted V E EV vertex)) <=
    130 + audit_key_bits_weight (encode (virtual_encoding EV) vertex).
Proof.
  destruct vertex as [v|[]];
    cbv [audit_virtual_encode_counted audit_virtual_entries_work audit_virtual_event_work snd
      List.fold_right audit_encoding_weight audit_key_bits_weight virtual_encoding sum_encoding
      encode]; cbn [Pos.size_nat]; lia.
Qed.

(** A nested preparation event has a bounded actual callback body. *)
Definition audit_virtual_prepare_model_bounded V E (EV : encoding V) budget
    (event : audit_prepare_nested_event (V + unit) (E + V) (audit_virtual_call V E)) : Prop :=
  audit_virtual_entries_work EV (snd event) <= budget.

(** Preparation edge callbacks remain bounded when actual target keys lie in the input width. *)
Lemma audit_virtual_prepare_edges_model_bound V E (EV : encoding V) (g : Graph.t V E)
    budget width edges :
  128 <= budget -> 130 + width <= budget ->
  (forall edge, In edge edges ->
    audit_key_bits_weight (encode (virtual_encoding EV) (Graph.target (virtual_graph EV g) edge))
      <= width) ->
  forall initial,
    Forall (audit_virtual_prepare_model_bounded V E EV budget)
      (snd (audit_prepare_nested_edges (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
        edges initial)).
Proof.
  intros Htarget Hbudget Hwidth; induction edges as [|edge rest IH]; intro initial.
  - repeat constructor; cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia.
  - cbn [audit_prepare_nested_edges].
    specialize (IH (fun e Hin => Hwidth e (or_intror Hin)) initial).
    destruct (audit_prepare_nested_edges (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
      rest initial) as [middle events].
    cbv beta iota zeta delta [audit_virtual_prepare_callbacks audit_prepare_target_model
      audit_virtual_target_counted] in *.
    destruct edge as [edge|vertex].
    + destruct (@audit_virtual_encode_counted V E EV (inl (Graph.target g edge))) as [code body]
        eqn:Hencode.
      destruct (Map.code_get code middle) as [found|] eqn:Hfound;
        cbn [snd] in IH |- *; constructor;
        try (cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
          List.fold_right]; lia).
      all: apply Forall_app; split; [exact IH|].
      all: pose proof (audit_virtual_encode_model_bound V E EV (inl (Graph.target g edge))) as Henc.
      all: rewrite Hencode in Henc; cbn [snd] in Henc.
      all: specialize (Hwidth (inl edge) (or_introl eq_refl)).
      all: change (S (audit_key_bits_weight (encode EV (Graph.target g edge))) <= width)
        in Hwidth.
      all: repeat (constructor; [unfold audit_virtual_prepare_model_bounded;
        cbv [snd audit_virtual_entries_work audit_virtual_event_work audit_encoding_weight
          List.fold_right]; lia|]); constructor.
    + destruct (@audit_virtual_encode_counted V E EV (inl vertex)) as [code body] eqn:Hencode.
      destruct (Map.code_get code middle) as [found|] eqn:Hfound;
        cbn [snd] in IH |- *; constructor;
        try (cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
          List.fold_right]; lia).
      all: apply Forall_app; split; [exact IH|].
      all: pose proof (audit_virtual_encode_model_bound V E EV (inl vertex)) as Henc.
      all: rewrite Hencode in Henc; cbn [snd] in Henc.
      all: specialize (Hwidth (inr vertex) (or_introl eq_refl)).
      all: change (S (audit_key_bits_weight (encode EV vertex)) <= width) in Hwidth.
      all: repeat (constructor; [unfold audit_virtual_prepare_model_bounded;
        cbv [snd audit_virtual_entries_work audit_virtual_event_work audit_encoding_weight
          List.fold_right]; lia|]); constructor.
Qed.

(** Output-index callbacks remain bounded for nodes in the original virtual graph. *)
Lemma audit_virtual_prepare_out_model_bound V E (EV : encoding V) (g : Graph.t V E)
    budget width nodes :
  130 + width <= budget ->
  (forall v, In v nodes -> In v (Graph.nodes (virtual_graph EV g))) ->
  (forall v, In v nodes ->
    audit_key_bits_weight (encode (virtual_encoding EV) v) <= width) ->
  (forall v, In v nodes -> audit_virtual_entries_work EV
    (snd (audit_virtual_out_counted EV g v)) <= budget) ->
  forall initial, Forall (audit_virtual_prepare_model_bounded V E EV budget)
    (snd (audit_prepare_nested_out (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
      nodes initial)).
Proof.
  intros Hbudget Hnodes Hwidth Hout; induction nodes as [|v rest IH]; intro initial.
  - repeat constructor; cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia.
  - cbn [audit_prepare_nested_out].
    specialize (IH (fun x Hin => Hnodes x (or_intror Hin))
      (fun x Hin => Hwidth x (or_intror Hin)) (fun x Hin => Hout x (or_intror Hin)) initial).
    destruct (audit_prepare_nested_out (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
      rest initial) as [middle events].
    destruct (audit_virtual_out_counted EV g v) as [out body] eqn:Hout_run.
    destruct (@audit_virtual_encode_counted V E EV v) as [code enc_body] eqn:Hencode.
    pose proof (audit_virtual_encode_model_bound V E EV v) as Henc.
    specialize (Hwidth v (or_introl eq_refl)).
    specialize (Hout v (or_introl eq_refl)).
    rewrite Hout_run in Hout; rewrite Hencode in Henc; cbn [snd] in Hout, Henc, IH.
    cbn [audit_virtual_prepare_callbacks audit_prepare_out_model audit_prepare_encode_model].
    rewrite Hout_run, Hencode; cbn [snd].
    constructor; [cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia|].
    apply Forall_app; split; [exact IH|].
    repeat (constructor; [unfold audit_virtual_prepare_model_bounded; cbn [snd]; lia|]);
      constructor.
Qed.

(** Incoming-index callbacks remain bounded for actual outgoing edges of original nodes. *)
Lemma audit_virtual_prepare_in_model_bound V E (EV : encoding V) (g : Graph.t V E)
    budget width nodes :
  128 <= budget -> 130 + width <= budget ->
  (forall v, In v nodes ->
    forall edge, In edge (Graph.out (virtual_graph EV g) v) ->
      audit_key_bits_weight (encode (virtual_encoding EV) (Graph.target (virtual_graph EV g) edge))
        <= width) ->
  (forall v, In v nodes -> audit_virtual_entries_work EV
    (snd (audit_virtual_out_counted EV g v)) <= budget) ->
  forall initial, Forall (audit_virtual_prepare_model_bounded V E EV budget)
    (snd (audit_prepare_nested_in (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
      nodes initial)).
Proof.
  intros Htarget Hbudget Hedge Hout; induction nodes as [|v rest IH]; intro initial.
  - repeat constructor; cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia.
  - cbn [audit_prepare_nested_in].
    specialize (IH (fun x Hin => Hedge x (or_intror Hin))
      (fun x Hin => Hout x (or_intror Hin)) initial).
    destruct (audit_prepare_nested_in (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
      rest initial) as [middle events].
    pose proof (audit_virtual_callbacks_correct V E EV g) as [[Herase _] _].
    specialize (Herase v).
    destruct (audit_virtual_out_counted EV g v) as [out body] eqn:Hout_run.
    cbn [audit_virtual_prepare_callbacks audit_prepare_out_model] in Herase.
    rewrite Hout_run in Herase; cbn [fst] in Herase.
    pose proof (audit_virtual_prepare_edges_model_bound V E EV g budget width out Htarget Hbudget)
      as Hedges.
    assert (Hedge_width : forall edge, In edge out ->
      audit_key_bits_weight (encode (virtual_encoding EV) (Graph.target (virtual_graph EV g) edge))
        <= width).
    { intros edge Hin; apply (Hedge v (or_introl eq_refl)); now rewrite <- Herase. }
    specialize (Hedges Hedge_width middle).
    destruct (audit_prepare_nested_edges (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
      out middle) as [result edge_events] eqn:Hedges_run.
    specialize (Hout v (or_introl eq_refl)); rewrite Hout_run in Hout.
    cbn [snd] in IH, Hedges, Hout.
    cbn [audit_virtual_prepare_callbacks audit_prepare_out_model].
    rewrite Hout_run, Hedges_run; cbn [snd].
    constructor; [cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia|].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [exact Hout|constructor].
Qed.

(** Edge-count callbacks remain bounded for nodes in the original virtual graph. *)
Lemma audit_virtual_prepare_count_model_bound V E (EV : encoding V) (g : Graph.t V E)
    budget nodes :
  (forall v, In v nodes -> audit_virtual_entries_work EV
    (snd (audit_virtual_out_counted EV g v)) <= budget) ->
  Forall (audit_virtual_prepare_model_bounded V E EV budget)
    (snd (audit_prepare_nested_edge_count (virtual_graph EV g)
      (audit_virtual_prepare_callbacks EV g) nodes)).
Proof.
  intro Hout; induction nodes as [|v rest IH].
  - repeat constructor; cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia.
  - cbn [audit_prepare_nested_edge_count].
    specialize (IH (fun x Hin => Hout x (or_intror Hin))).
    destruct (audit_prepare_nested_edge_count (virtual_graph EV g)
      (audit_virtual_prepare_callbacks EV g)
      rest) as [count events].
    destruct (audit_virtual_out_counted EV g v) as [out body] eqn:Hout_run.
    specialize (Hout v (or_introl eq_refl)); rewrite Hout_run in Hout; cbn [snd] in IH, Hout.
    cbn [audit_virtual_prepare_callbacks audit_prepare_out_model]; rewrite Hout_run; cbn [snd].
    constructor; [cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia|].
    apply Forall_app; split; [exact IH|].
    constructor; [exact Hout|].
    repeat constructor; cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia.
Qed.

(** Every preparation model callback body is bounded by the graph input envelope. *)
Lemma audit_virtual_prepare_model_bodies V E (EV : encoding V) (g : Graph.t V E) :
  let width := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) in
  let budget := 8 * S (length (Graph.entries g)) *
    (256 + 6 * width + 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g) in
  Forall (audit_virtual_prepare_model_bounded V E EV budget)
    (snd (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_prepare_callbacks EV g))).
Proof.
  set (width := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)).
  set (budget := 8 * S (length (Graph.entries g)) *
    (256 + 6 * width + 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g)).
  assert (Hbudget : 130 + width <= budget) by (unfold budget; clear; nia).
  assert (Htarget : 128 <= budget) by lia.
  assert (Hout : forall v, In v (Graph.nodes (virtual_graph EV g)) ->
    audit_virtual_entries_work EV (snd (audit_virtual_out_counted EV g v)) <= budget).
  { intros v Hin; unfold budget, width; now apply audit_virtual_out_model_bound. }
  assert (Hnode : forall v, In v (Graph.nodes (virtual_graph EV g)) ->
    audit_key_bits_weight (encode (virtual_encoding EV) v) <= width).
  { intros v Hin; unfold width; now apply audit_input_width_node. }
  assert (Hedge : forall v, In v (Graph.nodes (virtual_graph EV g)) ->
    forall edge, In edge (Graph.out (virtual_graph EV g) v) ->
      audit_key_bits_weight (encode (virtual_encoding EV) (Graph.target (virtual_graph EV g) edge))
        <= width).
  { intros v Hin edge Hedge; unfold width; eapply audit_input_width_edge; eassumption. }
  pose proof (audit_virtual_prepare_out_model_bound V E EV g budget width
    (Graph.nodes (virtual_graph EV g)) Hbudget (fun _ H => H) Hnode Hout Map.empty) as Hprep_out.
  pose proof (audit_virtual_prepare_in_model_bound V E EV g budget width
    (Graph.nodes (virtual_graph EV g)) Htarget Hbudget Hedge Hout Map.empty) as Hprep_in.
  pose proof (audit_virtual_prepare_count_model_bound V E EV g budget
    (Graph.nodes (virtual_graph EV g)) Hout) as Hcount.
  unfold audit_graph_prepare_nested_counted.
  destruct (audit_prepare_nested_out (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
    (Graph.nodes (virtual_graph EV g)) Map.empty) as [out out_events].
  destruct (audit_prepare_nested_in (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g)
    (Graph.nodes (virtual_graph EV g)) Map.empty) as [incoming in_events].
  destruct (audit_prepare_nested_edge_count (virtual_graph EV g)
      (audit_virtual_prepare_callbacks EV g)
    (Graph.nodes (virtual_graph EV g))) as [edges edge_events].
  cbv beta iota zeta in Hprep_out, Hprep_in, Hcount |- *.
  cbn [snd] in Hprep_out, Hprep_in, Hcount |- *.
  fold budget.
  repeat rewrite Forall_app; repeat split; try assumption;
    repeat constructor; cbv [audit_virtual_prepare_model_bounded audit_virtual_entries_work snd
      List.fold_right]; lia.
Qed.

(** Summing bounded preparation callback bodies charges at most one budget per event. *)
Lemma audit_virtual_prepare_model_sum V E (EV : encoding V) budget events :
  Forall (audit_virtual_prepare_model_bounded V E EV budget) events ->
  audit_prepare_nested_body_work (audit_virtual_event_work EV) events <= length events * budget.
Proof.
  intro Hbounded; induction Hbounded as [|[event body] rest Hbody Htail IH].
  - reflexivity.
  - unfold audit_virtual_prepare_model_bounded in Hbody; cbn [snd] in Hbody.
    change (audit_virtual_entries_work EV body +
      audit_prepare_nested_body_work (audit_virtual_event_work EV) rest <=
      length ((event, body) :: rest) * budget).
    cbn [List.length]; rewrite Nat.mul_succ_l, Nat.add_comm.
    apply Nat.add_le_mono; assumption.
Qed.

(** * Model DFS callback receipts *)

(** A nested DFS event retains the body from its own target or encoder callback. *)
Definition audit_virtual_dfs_model_receipt V E B (cb : audit_dfs_callback_model V E B)
    (item : audit_dfs_nested_event V E B) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditDfsFullTarget edge target => audit_dfs_target_model cb edge = (target, body)
  | AuditDfsFullMember v _ _
  | AuditDfsFullSuccessors v _ _ => snd (audit_dfs_encode_model cb v) = body
  | AuditDfsFullDetail (AuditDfsParentSet v _ _)
  | AuditDfsFullDetail (AuditDfsNumSet v _ _)
  | AuditDfsFullDetail (AuditDfsSeenAdd v _) => snd (audit_dfs_encode_model cb v) = body
  | _ => body = nil
  end.

(** Discovery's nested write events retain the encoder body for the discovered vertex. *)
Lemma audit_virtual_dfs_discover_receipts V E B (cb : audit_dfs_callback_model V E B) v via st :
  Forall (audit_virtual_dfs_model_receipt V E B cb) (snd (audit_dfs_nested_discover cb v via st)).
Proof.
  unfold audit_dfs_nested_discover, audit_dfs_nested_set.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall.
  destruct via; cbn; repeat constructor; cbn [audit_virtual_dfs_model_receipt];
    rewrite ?Hcall; reflexivity.
Qed.

(** Finishing's nested write event retains the encoder body for the finished vertex. *)
Lemma audit_virtual_dfs_finish_receipts V E B (cb : audit_dfs_callback_model V E B) v st :
  Forall (audit_virtual_dfs_model_receipt V E B cb) (snd (audit_dfs_nested_finish cb v st)).
Proof.
  unfold audit_dfs_nested_finish, audit_dfs_nested_set.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall.
  cbn; repeat constructor; cbn [audit_virtual_dfs_model_receipt]; rewrite ?Hcall; reflexivity.
Qed.

(** Each nested DFS step retains its actual target and encoder callback bodies. *)
Lemma audit_virtual_dfs_step_receipts V E B {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked work :
  Forall (audit_virtual_dfs_model_receipt V E B cb) (snd (audit_dfs_nested_step p cb blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_nested_step].
  - repeat constructor.
  - destruct edges as [|edge edges].
    + pose proof (audit_virtual_dfs_finish_receipts V E B cb v st) as Hfinish.
      destruct (audit_dfs_nested_finish cb v st) as [next details].
      cbn in Hfinish |- *; constructor; [reflexivity|].
      apply Forall_app; split; [exact Hfinish|repeat constructor].
    + destruct (audit_dfs_target_model cb edge) as [target target_body] eqn:Htarget.
      unfold audit_dfs_nested_get.
      destruct (audit_dfs_encode_model cb target) as [code body] eqn:Hencode.
      destruct (Map.code_get code blocked), (Map.code_get code (DfsState.seen st)); cbn;
        try (repeat constructor; cbn [audit_virtual_dfs_model_receipt]; rewrite ?Hencode;
          try exact Htarget; reflexivity; fail).
      pose proof (audit_virtual_dfs_discover_receipts V E B cb target (Some edge) st) as Hdiscover.
      destruct (audit_dfs_nested_discover cb target (Some edge) st) as [next details]
        eqn:Hdiscover_run.
      cbn [snd] in Hdiscover |- *.
      repeat constructor; cbn [audit_virtual_dfs_model_receipt]; rewrite ?Hencode;
        try exact Htarget; try reflexivity.
      apply Forall_app; split; [exact Hdiscover|repeat constructor].
Qed.

(** Both halves of a nested binary-fuel run retain same-call model receipts. *)
Lemma audit_virtual_dfs_run_receipts V E B {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked fuel work :
  Forall (audit_virtual_dfs_model_receipt V E B cb)
    (snd (audit_dfs_nested_run p cb blocked fuel work)).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intro work;
    destruct work as [stack st], stack as [|frame stack]; cbn [audit_dfs_nested_run].
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p cb blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p cb blocked fuel middle) as [last second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    pose proof (audit_virtual_dfs_step_receipts V E B p cb blocked last) as Hstep.
    destruct (audit_dfs_nested_step p cb blocked last) as [result events] eqn:Hstep_run;
      cbn in Hstep |- *.
    change (Forall (audit_virtual_dfs_model_receipt V E B cb)
      (snd (let '(middle, first) := audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_nested_run p cb blocked fuel middle in
        let '(result, events) := audit_dfs_nested_step p cb blocked last in
        (result, (AuditDfsFullCase 7, nil) :: first ++ second ++ events)))).
    rewrite Hfirst_run, Hsecond_run, Hstep_run; cbn.
    constructor; [reflexivity|]. apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p cb blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p cb blocked fuel middle) as [result second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    change (Forall (audit_virtual_dfs_model_receipt V E B cb)
      (snd (let '(middle, first) := audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_nested_run p cb blocked fuel middle in
        (result, (AuditDfsFullCase 6, nil) :: first ++ second)))).
    rewrite Hfirst_run, Hsecond_run; cbn.
    constructor; [reflexivity|]. apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    pose proof (audit_virtual_dfs_step_receipts V E B p cb blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_nested_step p cb blocked (frame :: stack, st))
      as [result events] eqn:Hstep_run; cbn in Hstep.
    change (Forall (audit_virtual_dfs_model_receipt V E B cb)
      (snd (let '(result, events) := audit_dfs_nested_step p cb blocked (frame :: stack, st) in
        (result, (AuditDfsFullCase 5, nil) :: events)))).
    rewrite Hstep_run; cbn; constructor; [reflexivity|exact Hstep].
Qed.

(** A nested DFS root retains the actual membership, discovery, and recursive receipts. *)
Lemma audit_virtual_dfs_root_receipts V E B {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked st v :
  Forall (audit_virtual_dfs_model_receipt V E B cb) (snd (audit_dfs_nested_root p cb blocked st v)).
Proof.
  unfold audit_dfs_nested_root, audit_dfs_nested_get.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hencode.
  destruct (Map.code_get code blocked), (Map.code_get code (DfsState.seen st)); cbn;
    try (repeat constructor; cbn [audit_virtual_dfs_model_receipt]; rewrite ?Hencode;
      reflexivity; fail).
  pose proof (audit_virtual_dfs_discover_receipts V E B cb v None st) as Hdiscover.
  destruct (audit_dfs_nested_discover cb v None st) as [next details] eqn:Hdiscover_run.
  cbn in Hdiscover.
  pose proof (audit_virtual_dfs_run_receipts V E B p cb blocked (fuel p)
    (((v, match Map.code_get code (out_index p) with
      | Some xs => xs
      | None => nil
      end) :: nil),
      next)) as Hrun.
  destruct (audit_dfs_nested_run p cb blocked (fuel p)
    (((v, match Map.code_get code (out_index p) with
      | Some xs => xs
      | None => nil
      end) :: nil),
      next)) as [result events] eqn:Hrun_eq.
  cbn in Hrun.
  cbn [audit_dfs_nested_discover]; cbn.
  cbn [audit_dfs_nested_discover] in Hdiscover_run; cbn in Hdiscover_run.
  rewrite Hdiscover_run, Hrun_eq; cbn.
  repeat constructor; cbn [audit_virtual_dfs_model_receipt]; rewrite ?Hencode; try reflexivity.
  apply Forall_app; split; [exact Hdiscover|].
  constructor; [reflexivity|exact Hrun].
Qed.

(** The root fold retains receipts for every nested traversal it performs. *)
Lemma audit_virtual_dfs_roots_receipts V E B {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots st :
  Forall (audit_virtual_dfs_model_receipt V E B cb)
    (snd (audit_dfs_nested_roots p cb blocked roots st)).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_nested_roots].
  - repeat constructor.
  - pose proof (audit_virtual_dfs_root_receipts V E B p cb blocked st root) as Hroot.
    destruct (audit_dfs_nested_root p cb blocked st root) as [next here] eqn:Hroot_run.
    cbn in Hroot; specialize (IH next).
    destruct (audit_dfs_nested_roots p cb blocked roots next) as [result later] eqn:Hroots_run.
    cbn in IH.
    constructor; [reflexivity|]. apply Forall_app; split; assumption.
Qed.

(** Every nested DFS event retains the body of its actual callback invocation. *)
Lemma audit_virtual_dfs_nested_receipts V E B {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
  Forall (audit_virtual_dfs_model_receipt V E B cb)
    (snd (audit_dfs_nested_counted p cb blocked roots)).
Proof.
  unfold audit_dfs_nested_counted.
  pose proof (audit_virtual_dfs_roots_receipts V E B p cb blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_nested_roots p cb blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** A DFS model receipt is priced using the width of its actual full-event operand. *)
Lemma audit_virtual_dfs_model_event_bound V E (EV : encoding V) (g : Graph.t V E) item width :
  audit_virtual_dfs_model_receipt (V + unit)%type (E + V)%type (audit_virtual_call V E)
    (audit_virtual_dfs_callbacks EV g) item ->
  audit_dfs_full_event_width (virtual_encoding EV) (fst item) <= width ->
  audit_virtual_entries_work EV (snd item) <= 130 + width.
Proof.
  intros Hreceipt Hwidth; destruct item as [event body].
  assert (Hencoder : forall vertex,
    snd (audit_virtual_encode_counted EV vertex) = body ->
    audit_key_bits_weight (encode (virtual_encoding EV) vertex) <= width ->
    audit_virtual_entries_work EV body <= 130 + width).
  { intros vertex Hbody Hkey.
    pose proof (audit_virtual_encode_model_bound V E EV vertex) as Hbound.
    rewrite Hbody in Hbound; lia. }
  destruct event as [site|edge target|v input found|v input found|v via before after|
      v before after|detail|pre post];
    cbn [audit_virtual_dfs_model_receipt audit_virtual_dfs_callbacks audit_dfs_target_model
      audit_dfs_encode_model audit_dfs_full_event_width fst snd] in Hreceipt, Hwidth |- *;
    try (subst body; cbv [audit_virtual_entries_work List.fold_right]; lia).
  - pose proof (audit_virtual_target_model_bound V E EV g edge) as Hbound.
    rewrite Hreceipt in Hbound; cbn [snd] in Hbound; lia.
  - eapply Hencoder; eassumption.
  - eapply Hencoder; eassumption.
  - destruct detail; cbn [audit_virtual_dfs_model_receipt audit_virtual_dfs_callbacks
      audit_dfs_encode_model audit_dfs_full_event_width] in Hreceipt, Hwidth;
      try (subst body; cbv [audit_virtual_entries_work List.fold_right]; lia);
      eapply Hencoder; eassumption.
Qed.

(** The nested DFS callback sum is bounded by its full-event widths and event count. *)
Lemma audit_virtual_dfs_model_sum V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared (virtual_encoding EV) (virtual_graph EV g)) :
  let '(_, events) := audit_dfs_nested_counted p (audit_virtual_dfs_callbacks EV g)
    FinSet.empty (inr tt :: nil) in
  audit_dfs_nested_body_work (audit_virtual_event_work EV) events <=
    length events * (130 + audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g) p
      (inr tt :: nil)).
Proof.
  destruct (audit_virtual_callbacks_correct V E EV g) as [_ [Hcallbacks _]].
  pose proof (audit_virtual_dfs_nested_receipts _ _ _ p (audit_virtual_dfs_callbacks EV g)
    FinSet.empty (inr tt :: nil)) as Hreceipts.
  pose proof (audit_dfs_nested_correct _ _ _ (virtual_encoding EV) (virtual_graph EV g) p
    (audit_virtual_dfs_callbacks EV g) FinSet.empty (inr tt :: nil) Hcallbacks) as Hnested.
  pose proof (audit_dfs_full_counted_event_width p FinSet.empty (inr tt :: nil)) as Hwidth.
  destruct (audit_dfs_nested_counted p (audit_virtual_dfs_callbacks EV g) FinSet.empty
    (inr tt :: nil)) as [result events].
  cbv beta iota zeta in Hreceipts, Hnested |- *.
  cbn [snd] in Hreceipts, Hnested.
  destruct Hnested as [_ [Htrace _]].
  rewrite <- Htrace in Hwidth; apply Forall_map in Hwidth.
  clear Htrace.
  induction Hreceipts as [|[event body] rest Hreceipt Htail IH].
  - reflexivity.
  - inversion Hwidth as [|? ? Hwidth_one Hwidth_tail]; subst.
    specialize (IH Hwidth_tail).
    pose proof (audit_virtual_dfs_model_event_bound V E EV g (event, body)
      (audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g) p (inr tt :: nil))
      Hreceipt Hwidth_one) as Hbound.
    change (audit_virtual_entries_work EV body +
      audit_dfs_nested_body_work (audit_virtual_event_work EV) rest <=
      length ((event, body) :: rest) *
        (130 + audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g) p
          (inr tt :: nil))).
    cbn [List.length]; rewrite Nat.mul_succ_l, Nat.add_comm.
    apply Nat.add_le_mono; assumption.
Qed.

(** Virtual search model work obeys the budget derived from the original graph. *)
Theorem audit_virtual_search_bound : audit_virtual_search_bound_statement.
Proof.
  intros V E EV g.
  destruct (audit_virtual_callbacks_correct V E EV g) as [Hprepare [Hdfs _]].
  pose proof (audit_graph_prepare_nested_correct _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_prepare_callbacks EV g) Hprepare) as Hprep_run.
  pose proof (audit_virtual_prepare_model_bodies V E EV g) as Hprep_bodies.
  unfold audit_virtual_search_work, audit_virtual_search_counted,
    audit_virtual_search_with_prepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_prepare_callbacks EV g)) as [vp prepare_events] eqn:Hprepare_run.
  cbv beta iota zeta in Hprep_run, Hprep_bodies |- *; cbn [snd] in Hprep_bodies.
  destruct Hprep_run as [Hvp [_ [Hprep_count Hprep_work]]].
  pose proof (audit_virtual_prepare_model_sum V E EV _ prepare_events Hprep_bodies) as Hprep_body.
  subst vp.
  set (vp := prepare (virtual_encoding EV) (virtual_graph EV g)).
  pose proof (audit_dfs_nested_correct _ _ _ (virtual_encoding EV) (virtual_graph EV g) vp
    (audit_virtual_dfs_callbacks EV g) FinSet.empty (inr tt :: nil) Hdfs) as Hdfs_run.
  pose proof (audit_virtual_dfs_model_sum V E EV g vp) as Hdfs_body.
  destruct (audit_dfs_nested_counted vp (audit_virtual_dfs_callbacks EV g) FinSet.empty
    (inr tt :: nil)) as [result dfs_events] eqn:Hdfs_run_eq.
  cbv beta iota zeta in Hdfs_run, Hdfs_body |- *.
  destruct Hdfs_run as [_ [_ [Hdfs_count Hdfs_work]]].
  unfold audit_graph_prepare_nested_total_work, audit_dfs_nested_total_work.
  unfold audit_virtual_search_budget; fold vp.
  set (prep_count := audit_graph_prepare_full_event_bound (virtual_graph EV g)) in *.
  set (dfs_count := audit_dfs_full_input_event_bound vp (inr tt :: nil)) in *.
  set (pwidth := audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g)) in *.
  set (dwidth := audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g) vp
    (inr tt :: nil)) in *.
  set (n := length (Graph.entries g)) in *.
  set (size := 1 + length (Graph.nodes g) + n + edge_count g) in *.
  set (prepcalls := length prepare_events) in *.
  set (dfscalls := length dfs_events) in *.
  replace (256 + 6 * pwidth + 1 + length (Graph.nodes g) + n + edge_count g)
    with (256 + 6 * pwidth + size) in Hprep_body by (unfold size; lia).
  set (unit_budget := 8 * S n * (256 + 6 * Nat.max pwidth dwidth + size)).
  assert (Hbudget : 8 * S n * (256 + 6 * pwidth + size) <= unit_budget).
  { unfold unit_budget; apply Nat.mul_le_mono_l.
    pose proof (Nat.le_max_l pwidth dwidth); lia. }
  assert (Hdfs_budget : 130 + dwidth <= unit_budget).
  { unfold unit_budget; pose proof (Nat.le_max_r pwidth dwidth); clear - H; nia. }
  assert (Hprep_total : prepcalls * (8 * S n * (256 + 6 * pwidth + size)) <=
    prep_count * unit_budget) by (apply Nat.mul_le_mono; assumption).
  assert (Hdfs_total : dfscalls * (130 + dwidth) <= dfs_count * unit_budget)
    by (apply Nat.mul_le_mono; assumption).
  fold unit_budget; rewrite Nat.mul_add_distr_r.
  clear - Hprep_work Hdfs_work Hprep_body Hdfs_body Hprep_total Hdfs_total.
  lia.
Qed.
