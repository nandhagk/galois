(** * AnalysesAuditRewriteFacadeCheckedMaterialize

    This module checks provenance shape before relating a root to replay steps and work.
    For example, a missing root makes the shape check return false.
    Builds on: AnalysesAuditRewriteFacadeMaterialize and
    RewriteAuditProofCarrier. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeMaterialize.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditSharedCompare.
Import List.ListNotations.

Fixpoint rw_facade_references_valid {K} (proof : rw_provenance K unit nat nat) (parent : positive)
    (references : list positive) : bool * nat :=
  match references with
  | nil => (true, 64)
  | child :: rest =>
    let '(order, comparison_work) := rw_rd_positive_compare_cont Eq child parent in
    let '(found, lookup) := audit_map_get audit_positive_encode child (rw_provenance_nodes proof) in
    let '(tail, tail_work) := rw_facade_references_valid proof parent rest in
    let earlier :=
      match order with
      | Lt => true
      | _ => false
      end in
    let present :=
      match found with
      | Some _ => true
      | None => false
      end in
    (earlier && present && tail, 64 + comparison_work +
      audit_map_source_work audit_basic_encoding_work lookup + tail_work)
  end.

Fixpoint rw_facade_provenance_entries_valid {K} (proof : rw_provenance K unit nat nat)
    (entries : list (positive * (positive * rw_evidence_node K unit nat nat))) : bool * nat :=
  match entries with
  | nil => (true, 64)
  | (position, (stored, node)) :: rest =>
    let '(same_key, key_trace) := audit_positive_eqb position stored in
    let '(references, references_work) := rw_facade_references_valid proof position
      (rw_reason_references (rw_evidence_reason_of node)) in
    let '(tail, tail_work) := rw_facade_provenance_entries_valid proof rest in
    (same_key && references && tail, 128 + audit_positive_eqb_source_work key_trace +
      references_work + tail_work)
  end.

Definition rw_facade_materialize_shape_atomic {K} (proof : rw_provenance K unit nat nat)
    (root : positive) : bool * nat :=
  let '(found, lookup) := audit_map_get audit_positive_encode root (rw_provenance_nodes proof) in
  let '(entries, enumeration) := audit_trie_elements (rw_provenance_nodes proof) in
  let '(valid, validation_work) := rw_facade_provenance_entries_valid proof entries in
  let present :=
    match found with
    | Some _ => true
    | None => false
    end in
  (present && valid, 64 + audit_map_source_work audit_basic_encoding_work lookup +
    audit_elements_work enumeration + validation_work).

(** Checked materialization relates a proof and root to either rejected shape or replay
    steps, together with the observed work. *)
Inductive rw_facade_checked_materialize_run {K} (proof : rw_provenance K unit nat nat)
    (root : positive) : option (list (rewrite_step K)) -> nat -> Prop :=
  | RPFCheckedMaterializeReject : forall work,
      rw_facade_materialize_shape_atomic proof root = (false, work) ->
      rw_facade_checked_materialize_run proof root None (64 + work)
  | RPFCheckedMaterializeAccept : forall validation_work steps materialization_work,
      rw_facade_materialize_shape_atomic proof root = (true, validation_work) ->
      rw_facade_materialize_run proof root steps materialization_work ->
      rw_facade_checked_materialize_run proof root (Some steps)
        (64 + validation_work + materialization_work).

(** Checked materialization has a result and work observation for every proof and root. *)
Definition rw_facade_checked_materialize_total_statement : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root, exists result work,
    rw_facade_checked_materialize_run proof root result work.

(** Two checked materialization runs on the same proof and root have equal results and work. *)
Definition rw_facade_checked_materialize_unique_statement : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root first fw second sw,
    rw_facade_checked_materialize_run proof root first fw ->
    rw_facade_checked_materialize_run proof root second sw ->
    first = second /\ fw = sw.
