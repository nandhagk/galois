(** * Memory encoding adequacy

    These proofs connect counted memory encoders to canonical encodings and bound scope work.
    For example, a live version emits its fixed tag without calling a node or edge encoder.
    Builds on: memory encoders and composite encoding adequacy. *)

From Stdlib Require Import List PArith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding
  CollectionsAuditEncodingAdequacy CollectionsAuditEncoderBudget
  CollectionsAuditEncoderBudgetAdequacy.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding.
Import List.ListNotations.

(** * Encoding erasure *)

(** Discarding events preserves the version tag and the actual node or edge code. *)
Theorem audit_memory_version_encode_erases : audit_memory_version_encode_erases_statement.
Proof.
  unfold audit_memory_version_encode_erases_statement.
  intros N E CN CE EN EE node_enc edge_enc input Hnode Hedge.
  destruct input as [|n|e i]; cbn [audit_memory_version_encode memory_version_encoding
    memory_frontier_version_encoding].
  - reflexivity.
  - specialize (Hnode n). destruct (node_enc n); simpl in *; now rewrite Hnode.
  - pose proof (audit_pair_encode_erases E nat CE audit_nat_encoding_event edge_enc
      audit_nat_encode EE nat_encoding e i (Hedge e) (audit_nat_encode_erases i)) as Hpair.
    destruct (audit_pair_encode edge_enc audit_nat_encode (e, i)); simpl in *; now rewrite Hpair.
Qed.

(** Discarding footprint events preserves the site and both signed endpoint encodings. *)
Theorem audit_memory_footprint_encode_erases : audit_memory_footprint_encode_erases_statement.
Proof.
  unfold audit_memory_footprint_encode_erases_statement, audit_memory_footprint_encode.
  intros T CE ET site_enc [site lo hi] Hsite.
  change (fst (audit_pair_encode site_enc (audit_pair_encode audit_z_encode audit_z_encode)
    (site, (lo, hi))) = encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding))
    (site, (lo, hi))).
  apply audit_pair_encode_erases; [apply Hsite|].
  apply audit_pair_encode_erases; apply audit_z_encode_erases.
Qed.

(** Both scope branches erase to their canonical sum and footprint-list codes. *)
Theorem audit_memory_scope_encode_erases : audit_memory_scope_encode_erases_statement.
Proof.
  unfold audit_memory_scope_encode_erases_statement, audit_memory_scope_encode, scope_code.
  intros T CE ET site_enc [fs|] Hsite.
  - apply audit_sum_encode_erases.
    + intros a H; discriminate.
    + intros b H; inversion H; subst b.
      apply audit_list_encode_erases. intros fp Hin.
      apply audit_memory_footprint_encode_erases; exact Hsite.
  - apply audit_sum_encode_erases.
    + intros a H; apply audit_unit_encode_erases.
    + intros b H; discriminate.
Qed.

(** A memo-key encoding erases to the canonical pair of scope code and version. *)
Theorem audit_memory_memo_key_encode_erases : audit_memory_memo_key_encode_erases_statement.
Proof.
  unfold audit_memory_memo_key_encode_erases_statement, audit_memory_memo_key_encode, memo_key.
  intros N E CN CE EN EE node_enc edge_enc [scope version] Hnode Hedge.
  apply audit_pair_encode_erases.
  - apply audit_positive_encode_erases.
  - apply audit_memory_version_encode_erases; assumption.
Qed.

(** * Scope work *)

(** Summing actual footprint work preserves each list occurrence, including duplicates. *)
Lemma audit_memory_footprint_child_budget : forall T CE
    (site_enc : T -> positive * list CE) site_work fs,
  audit_child_input_budget
    (fun fp => audit_memory_footprint_work site_work
      (snd (audit_memory_footprint_encode site_enc fp))) fs =
  audit_memory_footprint_list_work site_enc site_work fs.
Proof.
  intros T CE site_enc site_work fs. induction fs as [|fp rest IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** Scope work is bounded by actual footprint codes and their captured child work. *)
Theorem audit_memory_scope_work_bound : audit_memory_scope_work_bound_statement.
Proof.
  unfold audit_memory_scope_work_bound_statement.
  intros T CE site_enc site_work [fs|].
  - pose proof (audit_list_input_bound (footprint T) (audit_memory_footprint_event T CE)
      (audit_memory_footprint_encode site_enc) (audit_memory_footprint_work site_work)
      (fun fp => audit_memory_footprint_work site_work
        (snd (audit_memory_footprint_encode site_enc fp))) fs (fun _ => le_n _)) as Hbound.
    cbn beta in Hbound.
    unfold audit_list_input_budget in Hbound.
    rewrite audit_memory_footprint_child_budget in Hbound.
    change (audit_list_events_work (audit_memory_footprint_work site_work)
      (snd (audit_list_encode (audit_memory_footprint_encode site_enc) fs)) <=
      4 + 2 * length fs + 10 * audit_encoded_bits (audit_memory_footprint_encode site_enc) fs +
        audit_memory_footprint_list_work site_enc site_work fs) in Hbound.
    unfold audit_memory_scope_work, audit_memory_scope_encode, audit_memory_scope_budget.
    cbn [audit_sum_encode].
    remember (audit_list_encode (audit_memory_footprint_encode site_enc) fs) as result
      eqn:Hlist in *.
    destruct result as [code events]. simpl in *. lia.
  - reflexivity.
Qed.
