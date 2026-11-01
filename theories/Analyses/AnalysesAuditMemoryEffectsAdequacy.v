(** * Adequacy of counted memory effect rows

    These proofs relate tail-first row construction and lookup to their plain counterparts.
    For example, a missing edge stops before the numeric-index lookup.
    Builds on: AnalysesAuditMemoryEffects and collection adequacy proofs. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditMapAdequacy CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditEncoding CollectionsAuditEncodingAdequacy.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryWalk AnalysesAuditMemoryEffects.
Import List.ListNotations.

(** Tail-first insertion preserves the plain effect row. *)
Theorem audit_memory_effects_from_erases : audit_memory_effects_from_erases_statement.
Proof.
  intros T start input; revert start.
  induction input as [|effect rest IH]; intro start.
  - reflexivity.
  - cbn [audit_memory_effects_from memory_walk_effects_from].
    pose proof (IH (S start)) as Htail.
    pose proof (audit_map_set_erases nat _ _ audit_nat_encode nat_encoding start effect
      (fst (audit_memory_effects_from (S start) rest)) (audit_nat_encode_erases start)) as Hset.
    destruct (audit_memory_effects_from (S start) rest) as [tail events].
    destruct (audit_map_set audit_nat_encode start effect tail) as [output calls] eqn:Hput.
    cbn in Htail, Hset |- *.
    rewrite Hput in Hset; cbn in Hset; rewrite Hset, Htail; reflexivity.
Qed.

(** The trace contains one terminal and two events per effect. *)
Theorem audit_memory_effects_from_count : audit_memory_effects_from_count_statement.
Proof.
  intros T start input; revert start.
  induction input as [|effect rest IH]; intro start.
  - reflexivity.
  - cbn [audit_memory_effects_from].
    specialize (IH (S start)).
    destruct (audit_memory_effects_from (S start) rest) as [tail events].
    destruct (audit_map_set audit_nat_encode start effect tail) as [output calls] eqn:Hput.
    cbn in IH |- *; rewrite length_app; cbn; lia.
Qed.

(** Lookup erasure preserves both missing-edge and indexed-row outcomes. *)
Theorem audit_memory_effect_get_erases : audit_memory_effect_get_erases_statement.
Proof.
  intros E T CE edge_enc EE table edge index Henc.
  unfold audit_memory_effect_get, memory_walk_effect_get.
  pose proof (audit_map_get_erases E _ CE edge_enc EE edge table Henc) as Hedge.
  destruct (audit_map_get edge_enc edge table) as [row first].
  cbn in Hedge |- *; rewrite <- Hedge.
  destruct row as [actual|].
  - pose proof (audit_map_get_erases nat _ _ audit_nat_encode nat_encoding index actual
      (audit_nat_encode_erases index)) as Hindex.
    destruct (audit_map_get audit_nat_encode index actual); exact Hindex.
  - reflexivity.
Qed.

(** A lookup emits one event for a missing edge and two for a present edge. *)
Theorem audit_memory_effect_get_count : audit_memory_effect_get_count_statement.
Proof.
  intros E T CE edge_enc table edge index.
  unfold audit_memory_effect_get.
  destruct (audit_map_get edge_enc edge table) as [row first].
  destruct row as [actual|].
  - destruct (audit_map_get audit_nat_encode index actual); cbn; lia.
  - cbn; lia.
Qed.

(** Effect-row work adds over consecutive event sequences. *)
Lemma audit_memory_effect_events_work_app T (left right : list (audit_memory_effect_event T)) :
  audit_memory_effect_events_work (left ++ right) =
    audit_memory_effect_events_work left + audit_memory_effect_events_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; simpl; lia.
Qed.

(** A numeric map insertion is charged for its actual encoding and trie update. *)
Lemma audit_memory_effect_set_bound T start (effect : memory_effect T)
    (tail : Map.t nat (memory_effect T)) :
  audit_memory_effect_map_work (snd (audit_map_set audit_nat_encode start effect tail)) <=
    1 + 2 * (S start * S (Pos.size_nat (encode nat_encoding start))) +
      16 * Pos.size_nat (encode nat_encoding start).
Proof.
  pose proof (audit_nat_encode_count start) as Hcount.
  pose proof (audit_nat_encode_erases start) as Hencode.
  unfold audit_map_set.
  destruct (audit_nat_encode start) as [code events] eqn:Henc.
  cbn in Hcount, Hencode.
  pose proof (audit_trie_update_source_work_bound (nat * _)%type code (Some (start, effect)) tail)
    as Htrie.
  unfold audit_trie_set.
  destruct (audit_trie_update code (Some (start, effect)) tail) as [output calls].
  cbn [snd audit_memory_effect_map_work].
  rewrite Hencode in Htrie |- *.
  cbn [encode nat_encoding] in *; nia.
Qed.

(** The row budget bounds every numeric encoding and actual trie insertion. *)
Theorem audit_memory_effects_work_bound : audit_memory_effects_work_bound_statement.
Proof.
  intros T start input; revert start.
  induction input as [|effect rest IH]; intro start.
  - reflexivity.
  - cbn [audit_memory_effects_from audit_memory_effects_budget].
    specialize (IH (S start)).
    pose proof (audit_memory_effect_set_bound T start effect
      (fst (audit_memory_effects_from (S start) rest))) as Hset.
    destruct (audit_memory_effects_from (S start) rest) as [tail events].
    destruct (audit_map_set audit_nat_encode start effect tail) as [output calls] eqn:Hput.
    cbn in IH, Hset |- *; rewrite Hput in Hset; cbn in Hset.
    cbn [audit_memory_effect_events_work].
    rewrite audit_memory_effect_events_work_app; cbn [audit_memory_effect_events_work]; lia.
Qed.
