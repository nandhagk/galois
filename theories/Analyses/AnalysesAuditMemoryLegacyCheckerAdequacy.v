(** * Adequacy of the legacy pair and node checkers

    These proofs connect the strict recorded checker to the original Boolean decisions.
    For example, a false candidate still leaves a trace of the next node.
    Builds on: AnalysesAuditMemoryLegacyChecker, full-slice and collection adequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacySliceFull
  AnalysesAuditMemoryLegacySliceFullAdequacy AnalysesAuditMemoryLegacyChecker.
Import List.ListNotations.

(** * Pair and node agreement *)

(** Pointwise agreement of writes preserves the scan result. *)
Lemma audit_legacy_slice_writes_agree N E T (EN : encoding N) (ET : encoding T)
    (g : Graph.t N E) (p : prepared EN g) (left right : N -> list (footprint T)) read roots load :
    (forall n, left n = right n) ->
    legacy_slice EN ET g p left read roots load = legacy_slice EN ET g p right read roots load.
Proof.
  intro Hagree; unfold legacy_slice.
  induction (Graph.nodes g) as [|n rest IH].
  - reflexivity.
  - cbn [forallb].
    rewrite Hagree, IH; reflexivity.
Qed.

(** Matching callbacks recover the original pair decision for both definition constructors. *)
Theorem audit_legacy_pair_check_erases : audit_legacy_pair_check_erases_statement.
Proof.
  intros F N E T CN CF CT CS CR CW EN EF ET node_enc function_enc site_enc successors reads writes
    original_reads original_writes g p reached n d f Hnode Hfunction Hsite Hsucc Hread Hwrite.
  unfold audit_legacy_pair_check_full, legacy_pair_check.
  pose proof (audit_finset_mem_erases N CN node_enc EN n reached (Hnode n)) as Hload.
  destruct (audit_finset_mem node_enc n reached) as [load_ok load_events] eqn:Hload_call;
    cbn in Hload.
  destruct d as [owner def_node|owner].
  - pose proof (audit_positive_eqb_erases (fst (function_enc owner)) (fst (function_enc f)))
      as Hequal.
    destruct (function_enc owner) as [owner_code owner_body] eqn:Howner.
    destruct (function_enc f) as [function_code function_body] eqn:Hfunction_call.
    cbn in Hequal.
    destruct (audit_positive_eqb owner_code function_code) as [same calls] eqn:Hequal_call.
    cbn in Hequal.
    pose proof (audit_finset_mem_erases N CN node_enc EN def_node reached (Hnode def_node)) as Hdef.
    destruct (audit_finset_mem node_enc def_node reached) as [def_ok def_events] eqn:Hdef_call;
      cbn in Hdef.
    pose proof (audit_legacy_slice_full_erases N E T CN CT CW EN ET node_enc site_enc g p writes
      (fst (reads n)) (fst (successors def_node)) n Hnode Hsite) as Hslice.
    destruct (reads n) as [read read_events] eqn:Hread_call.
    destruct (successors def_node) as [roots succ_events] eqn:Hsucc_call; cbn in Hslice.
    destruct (audit_legacy_slice_full EN ET node_enc site_enc g p writes read roots n)
      as [answer slice_events] eqn:Hslice_call; cbn in Hslice.
    cbn in Hslice.
    rewrite (audit_legacy_slice_writes_agree N E T EN ET g p _ original_writes
      read roots n Hwrite) in Hslice.
    specialize (Hfunction owner) as Howner_code; rewrite Howner in Howner_code; cbn in Howner_code.
    specialize (Hfunction f) as Hfunction_code; rewrite Hfunction_call in Hfunction_code;
      cbn in Hfunction_code.
    specialize (Hread n); rewrite Hread_call in Hread; cbn in Hread.
    specialize (Hsucc def_node); rewrite Hsucc_call in Hsucc; cbn in Hsucc.
    rewrite Hload, Hequal, Howner_code, Hfunction_code, Hdef, Hslice, Hread, Hsucc.
    destruct (FinSet.mem EN n reached), (Pos.eqb (encode EF owner) (encode EF f)),
      (FinSet.mem EN def_node reached); reflexivity.
  - pose proof (audit_positive_eqb_erases (fst (function_enc owner)) (fst (function_enc f)))
      as Hequal.
    destruct (function_enc owner) as [owner_code owner_body] eqn:Howner.
    destruct (function_enc f) as [function_code function_body] eqn:Hfunction_call; cbn in Hequal.
    destruct (audit_positive_eqb owner_code function_code) as [same calls] eqn:Hequal_call.
    cbn in Hequal.
    pose proof (audit_legacy_slice_full_erases N E T CN CT CW EN ET node_enc site_enc g p writes
      (fst (reads n)) (Graph.entries g) n Hnode Hsite) as Hslice.
    destruct (reads n) as [read read_events] eqn:Hread_call; cbn in Hslice.
    destruct (audit_legacy_slice_full EN ET node_enc site_enc g p writes read (Graph.entries g) n)
      as [answer slice_events] eqn:Hslice_call; cbn in Hslice.
    cbn in Hslice.
    rewrite (audit_legacy_slice_writes_agree N E T EN ET g p _ original_writes
      read (Graph.entries g) n Hwrite) in Hslice.
    specialize (Hfunction owner) as Howner_code; rewrite Howner in Howner_code; cbn in Howner_code.
    specialize (Hfunction f) as Hfunction_code; rewrite Hfunction_call in Hfunction_code;
      cbn in Hfunction_code.
    specialize (Hread n); rewrite Hread_call in Hread; cbn in Hread.
    rewrite Hload, Hequal, Howner_code, Hfunction_code, Hslice, Hread; reflexivity.
Qed.

(** Matching definition and callback results recover the original all-node Boolean. *)
Theorem audit_legacy_check_nodes_erases : audit_legacy_check_nodes_erases_statement.
Proof.
  intros F N E T CN CF CT CS CR CW CD EN EF ET node_enc function_enc site_enc successors reads
    writes definitions original_reads original_writes original_definitions g p reached f nodes
    Hnode Hfunction Hsite Hsucc Hread Hwrite Hdefinitions.
  induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_legacy_check_nodes forallb].
    specialize (Hdefinitions node).
    destruct (definitions node) as [candidate calls] eqn:Hcandidate; cbn in Hdefinitions.
    rewrite <- Hdefinitions.
    destruct candidate as [definition|].
    + pose proof (audit_legacy_pair_check_erases F N E T CN CF CT CS CR CW EN EF ET node_enc
        function_enc site_enc successors reads writes original_reads original_writes g p reached
        node definition f Hnode Hfunction Hsite Hsucc Hread Hwrite) as Hpair.
      destruct (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
        successors reads writes g p reached node definition f) as [answer events].
      destruct (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc successors reads
        writes g p reached definitions f rest) as [tail tail_events]; cbn in *.
      rewrite Hpair, IH; reflexivity.
    + destruct (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc successors reads
        writes g p reached definitions f rest) as [tail events]; cbn in *.
      exact IH.
Qed.

(** A failed load probe retains the selected read and slice calls. *)
Theorem audit_legacy_false_load_fixture_retains_body :
    audit_legacy_false_load_fixture_retains_body_statement.
Proof.
  unfold audit_legacy_false_load_fixture_retains_body_statement.
  vm_compute; repeat eexists; intuition.
Qed.

(** A failed owner comparison retains the selected read and slice calls. *)
Theorem audit_legacy_false_owner_fixture_retains_body :
    audit_legacy_false_owner_fixture_retains_body_statement.
Proof.
  unfold audit_legacy_false_owner_fixture_retains_body_statement.
  vm_compute; repeat eexists; intuition.
Qed.

(** A failed first candidate does not omit the second node's pair trace. *)
Theorem audit_legacy_false_head_two_nodes_fixture_retains_tail :
    audit_legacy_false_head_two_nodes_fixture_retains_tail_statement.
Proof.
  unfold audit_legacy_false_head_two_nodes_fixture_retains_tail_statement.
  vm_compute; repeat eexists; intuition.
Qed.
