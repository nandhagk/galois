(** * Adequacy of the legacy slice node scan

    The scan preserves both membership tests and the selected footprint checks.
    For example, a missing forward membership still records a backward probe.
    Builds on: AnalysesAuditMemoryLegacySlice and overlap adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditFinSetAdequacy.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacyOverlap
  AnalysesAuditMemoryLegacyOverlapAdequacy AnalysesAuditMemoryLegacySlice.
Import List.ListNotations.

(** * Scan agreement and cost *)

(** Matching node and site encodings recover the source scan Boolean. *)
Theorem audit_legacy_slice_nodes_erases : audit_legacy_slice_nodes_erases_statement.
Proof.
  intros N T CN CT W EN ET node_enc site_enc writes read forward backward nodes Hnode Hsite.
  induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_legacy_slice_nodes forallb].
    pose proof (audit_finset_mem_erases N CN node_enc EN node forward (Hnode node)) as Hforward.
    pose proof (audit_finset_mem_erases N CN node_enc EN node backward (Hnode node)) as Hbackward.
    destruct (audit_finset_mem node_enc node forward) as [f fe].
    destruct (audit_finset_mem node_enc node backward) as [b be]; cbn in *.
    rewrite <- Hforward, <- Hbackward.
    destruct (audit_legacy_slice_nodes node_enc site_enc writes read forward backward rest)
      as [tail events]; cbn in IH.
    destruct (andb f b) eqn:Hboth.
    + pose proof (audit_legacy_disjoint_erases T CT site_enc ET (fst (writes node)) read Hsite)
        as Hdisjoint.
      destruct (writes node) as [footprints we].
      destruct (audit_legacy_disjoint site_enc footprints read) as [answer checks] eqn:Hcall;
        cbn in *.
      rewrite Hcall in Hdisjoint; cbn in Hdisjoint.
      rewrite Hdisjoint, IH; reflexivity.
    + cbn; rewrite IH; reflexivity.
Qed.

(** Selected writes and overlap checks fit the budget for the same scan decisions. *)
Theorem audit_legacy_slice_nodes_source_bound : audit_legacy_slice_nodes_source_bound_statement.
Proof.
  intros N T CN CT W node_enc site_enc writes node_work site_work writes_work
    read forward backward nodes.
  induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_legacy_slice_nodes audit_legacy_slice_budget].
    destruct (audit_finset_mem node_enc node forward) as [f fe].
    destruct (audit_finset_mem node_enc node backward) as [b be].
    destruct (audit_legacy_slice_nodes node_enc site_enc writes read forward backward rest)
      as [tail events]; cbn in IH.
    destruct (andb f b) eqn:Hboth.
    + pose proof (audit_legacy_overlap_source_bound T CT site_enc site_work
        (fst (writes node)) read)
        as Hbound.
      destruct (writes node) as [footprints we].
      destruct (audit_legacy_disjoint site_enc footprints read) as [answer checks] eqn:Hcall;
        cbn in *.
      rewrite Hcall in Hbound; cbn in Hbound.
      lia.
    + cbn [snd app audit_legacy_slice_source_work]; lia.
Qed.
