(** * Adequacy of counted memory result indexing

    These proofs relate the recorded tail-first insertion to the original index and its work.
    For example, two identical keys still produce two insertion events.
    Builds on: AnalysesAuditMemoryIndex and CollectionsAuditMap CollectionsAuditMapAdequacy. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditMapAdequacy.
From Galois.Analyses Require Import AnalysesMemoryFrontier AnalysesAuditMemoryIndex.
Import List.ListNotations.

(** Matching encodings and values yield the same tail-first index. *)
Theorem audit_memory_result_index_erases : audit_memory_result_index_erases_statement.
Proof.
  intros K A CE VE enc original_enc value original_value keys Henc Hvalue.
  unfold memory_result_index.
  induction keys as [|key rest IH]; cbn [audit_memory_result_index fold_right].
  - reflexivity.
  - specialize (IH (fun k H => Henc k (or_intror H))
      (fun k H => Hvalue k (or_intror H))).
    pose proof (audit_map_set_erases K A CE enc original_enc key (fst (value key))
      (fst (audit_memory_result_index enc value rest)) (Henc key (or_introl eq_refl))) as Hset.
    destruct (audit_memory_result_index enc value rest) as [tail events] eqn:Htail.
    destruct (value key) as [v ve] eqn:Hval.
    cbn in IH, Hset, Hval.
    destruct (audit_map_set enc key v tail) as [output calls] eqn:Hput.
    cbn in Hset; rewrite Hset, IH.
    specialize (Hvalue key (or_introl eq_refl)); rewrite Hval in Hvalue.
    cbn in Hvalue; rewrite Hvalue; reflexivity.
Qed.

(** Each key contributes one event in addition to the terminal event. *)
Theorem audit_memory_result_index_count : audit_memory_result_index_count_statement.
Proof.
  intros K A CE VE enc value keys.
  induction keys as [|key rest IH]; cbn [audit_memory_result_index].
  - reflexivity.
  - destruct (audit_memory_result_index enc value rest) as [tail events] eqn:Htail.
    destruct (value key) as [v ve].
    destruct (audit_map_set enc key v tail) as [output calls] eqn:Hput.
    cbn in IH |- *; rewrite length_app; cbn; lia.
Qed.

(** Index work distributes over consecutive event sequences. *)
Lemma audit_memory_index_work_app K A CE VE encoder_work value_work
    (left right : list (audit_memory_index_event K A CE VE)) :
  audit_memory_index_work encoder_work value_work (left ++ right) =
    audit_memory_index_work encoder_work value_work left +
      audit_memory_index_work encoder_work value_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; simpl; lia.
Qed.

(** Each insertion is charged for its actual encoder, value callback and trie update. *)
Theorem audit_memory_result_index_work_bound : audit_memory_result_index_work_bound_statement.
Proof.
  intros K A CE VE enc value encoder_work value_work keys.
  induction keys as [|key rest IH]; cbn [audit_memory_result_index audit_memory_index_budget].
  - reflexivity.
  - pose proof (audit_map_set_source_work_bound K A CE enc encoder_work key (fst (value key))
      (fst (audit_memory_result_index enc value rest))) as Hset.
    destruct (audit_memory_result_index enc value rest) as [tail events].
    destruct (value key) as [v ve].
    destruct (audit_map_set enc key v tail) as [output calls] eqn:Hput.
    cbn in IH, Hset |- *.
    rewrite Hput in Hset; cbn in Hset.
    rewrite audit_memory_index_work_app; cbn [audit_memory_index_work].
    lia.
Qed.
