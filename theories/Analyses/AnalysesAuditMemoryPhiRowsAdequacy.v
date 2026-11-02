(** * Phi input row adequacy

    These proofs preserve first-occurrence keys, actual optional operands and tail-first stores.
    For example, repeated predecessor keys are retained only at their first position.
    Builds on: AnalysesAuditMemoryPhiRows and collection encoding and finite-set adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditEncoding CollectionsAuditEncodingAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominance.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiRows.
Import List.ListNotations.

(** Matching codes retain exactly the first occurrences relative to the supplied seen set. *)
Theorem audit_phi_distinct_erases : audit_phi_distinct_erases_statement.
Proof.
  intros K CE enc EK seen input.
  revert seen.
  induction input as [|key rest IH]; intros seen Henc.
  - reflexivity.
  - cbn [audit_phi_distinct_from virtual_entries_from].
    pose proof (audit_finset_mem_erases K CE enc EK key seen (Henc key (or_introl eq_refl)))
      as Hmem.
    destruct (audit_finset_mem enc key seen) as [found probes]; cbn in Hmem.
    rewrite <- Hmem.
    destruct found.
    + specialize (IH seen (fun k Hin => Henc k (or_intror Hin))).
      destruct (audit_phi_distinct_from enc seen rest); cbn in *; exact IH.
    + pose proof (audit_finset_add_erases K CE enc EK key seen (Henc key (or_introl eq_refl)))
        as Hadd.
      destruct (audit_finset_add enc key seen) as [next adds]; cbn in Hadd.
      rewrite <- Hadd.
      specialize (IH next (fun k Hin => Henc k (or_intror Hin))).
      destruct (audit_phi_distinct_from enc next rest); cbn in *; now rewrite IH.
Qed.

Lemma audit_phi_distinct_length K CE (enc : K -> positive * list CE) input :
  forall seen, length (fst (audit_phi_distinct_from enc seen input)) <= length input.
Proof.
  induction input as [|key rest IH]; intro seen.
  - reflexivity.
  - cbn [audit_phi_distinct_from].
    destruct (audit_finset_mem enc key seen) as [found probes].
    destruct found.
    + specialize (IH seen).
      destruct (audit_phi_distinct_from enc seen rest); cbn in *; lia.
    + destruct (audit_finset_add enc key seen) as [next adds].
      specialize (IH next).
      destruct (audit_phi_distinct_from enc next rest); cbn in *; lia.
Qed.

Lemma audit_phi_row_operands_erases N E CN CE PE OE
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (original : N -> option E -> option (memory_version N E)) n keys :
  (forall key, fst (operand n key) = original n key) ->
  fst (@audit_phi_row_operands N E CN CE PE OE operand n keys) =
    flat_map (fun key =>
      match original n key with
      | Some v =>
        [(key, v)]
      | None =>
        []
      end) keys.
Proof.
  intro Hoperand.
  induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_phi_row_operands flat_map].
    specialize (Hoperand key) as Hhead.
    destruct (operand n key) as [result calls]; cbn in Hhead.
    destruct (@audit_phi_row_operands N E CN CE PE OE operand n rest) as [tail events].
    cbn in IH |- *.
    rewrite <- Hhead.
    destruct result; cbn; now rewrite IH.
Qed.

Lemma audit_phi_input_row_erases N E CN CE PE OE (EE : encoding E)
    (edge_enc : E -> positive * list CE) (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE) n :
  (forall e, fst (edge_enc e) = encode EE e) ->
  fst (@audit_phi_input_row N E CN CE PE OE edge_enc pred operand n) =
    flat_map (fun key =>
      match fst (operand n key) with
      | Some v =>
        [(key, v)]
      | None =>
        []
      end) (memory_distinct (option_encoding EE) (None :: map Some (fst (pred n)))).
Proof.
  intro Hedge.
  unfold audit_phi_input_row.
  destruct (pred n) as [edges calls].
  pose proof (audit_phi_distinct_erases (option E) (audit_option_event E CE)
    (audit_option_encode edge_enc) (option_encoding EE) FinSet.empty (None :: map Some edges)
    (fun key _ => audit_option_encode_erases E CE edge_enc EE key (fun e _ => Hedge e)))
    as Hkeys.
  destruct (audit_phi_distinct_from (audit_option_encode edge_enc) FinSet.empty
    (None :: map Some edges)) as [keys events]; cbn [fst snd] in Hkeys |- *.
  unfold memory_distinct.
  rewrite <- Hkeys.
  pose proof (audit_phi_row_operands_erases N E CN CE PE OE operand
    (fun node key => fst (operand node key)) n keys (fun _ => eq_refl)) as Hrow.
  destruct (@audit_phi_row_operands N E CN CE PE OE operand n keys).
  exact Hrow.
Qed.

(** Matching encoders and callbacks preserve the complete tail-first input index. *)
Theorem audit_phi_input_rows_erases : audit_phi_input_rows_erases_statement.
Proof.
  intros N E T CN CE PE OE EN EE g effects mg node_enc edge_enc pred operand
    Hnode Hedge Hpred Hoperand.
  unfold phi_input_rows, memory_result_index.
  induction (memory_phis mg) as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_input_rows fold_right].
    pose proof (audit_phi_input_row_erases N E CN CE PE OE EE edge_enc pred operand n Hedge)
      as Hrow.
    destruct (audit_phi_input_rows node_enc edge_enc pred operand rest) as [tail tail_events].
    destruct (@audit_phi_input_row N E CN CE PE OE edge_enc pred operand n) as [row row_events].
    pose proof (audit_map_set_erases N _ CN node_enc EN n row tail (Hnode n)) as Hset.
    destruct (audit_map_set node_enc n row tail) as [output stores].
    cbn in IH, Hrow, Hset |- *.
    rewrite Hset, IH, Hrow, Hpred, (Hoperand n None).
    f_equal.
    f_equal.
    apply flat_map_ext.
    intro key; now rewrite Hoperand.
Qed.

Lemma audit_phi_row_operands_count N E CN CE PE OE
    (operand : N -> option E -> option (memory_version N E) * list OE) n keys :
  length (snd (@audit_phi_row_operands N E CN CE PE OE operand n keys)) = length keys.
Proof.
  induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_phi_row_operands].
    destruct (operand n key) as [result calls].
    destruct (@audit_phi_row_operands N E CN CE PE OE operand n rest) as [tail events].
    cbn in IH |- *; now rewrite IH.
Qed.

Lemma audit_phi_input_row_count N E CN CE PE OE (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE) n :
  length (snd (@audit_phi_input_row N E CN CE PE OE edge_enc pred operand n)) <=
    3 + length (fst (pred n)).
Proof.
  unfold audit_phi_input_row.
  destruct (pred n) as [edges calls].
  pose proof (audit_phi_distinct_length (option E) (audit_option_event E CE)
    (audit_option_encode edge_enc) (None :: map Some edges) FinSet.empty) as Hkeys.
  destruct (audit_phi_distinct_from (audit_option_encode edge_enc) FinSet.empty
    (None :: map Some edges)) as [keys events].
  pose proof (audit_phi_row_operands_count N E CN CE PE OE operand n keys) as Hoperands.
  destruct (@audit_phi_row_operands N E CN CE PE OE operand n keys) as [row operands].
  cbn in Hkeys, Hoperands |- *.
  rewrite length_map in Hkeys.
  lia.
Qed.

(** Every input row pays its predecessor, distinctness, operand and store frames. *)
Theorem audit_phi_input_rows_count : audit_phi_input_rows_count_statement.
Proof.
  intros N E CN CE PE OE node_enc edge_enc pred operand nodes.
  induction nodes as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_input_rows audit_phi_rows_budget].
    pose proof (audit_phi_input_row_count N E CN CE PE OE edge_enc pred operand n) as Hrow.
    destruct (audit_phi_input_rows node_enc edge_enc pred operand rest) as [tail tail_events].
    destruct (@audit_phi_input_row N E CN CE PE OE edge_enc pred operand n) as [row row_events].
    destruct (audit_map_set node_enc n row tail) as [output stores].
    cbn in IH, Hrow |- *.
    rewrite !length_app; cbn; lia.
Qed.

(** The row count bounds outer source frames while retaining all primitive work. *)
Theorem audit_phi_input_rows_source_bound : audit_phi_input_rows_source_bound_statement.
Proof.
  intros N E CN CE PE OE node_enc edge_enc pred operand nodes
    node_work edge_work pred_work operand_work.
  pose proof (audit_phi_input_rows_count N E CN CE PE OE node_enc edge_enc pred operand nodes)
    as Hcount.
  unfold audit_phi_rows_source_work.
  lia.
Qed.
