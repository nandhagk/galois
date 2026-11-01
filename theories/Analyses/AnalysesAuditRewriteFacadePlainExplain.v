(** * AnalysesAuditRewriteFacadePlainExplain

    This file builds selected explanations and optimized outputs from plain legacy stages.
    For example, a checker result of false makes explanation reconstruction return None.
    Builds on: the fixed Rewrite plain builders and legacy facade source equations. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia Wellfounded.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadePlainHelpers
  AnalysesAuditRewriteFacadePlainMaterializer AnalysesAuditRewriteFacadePlainRun
  AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofTick RewriteAuditSharedPlain RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_facade_explain_core (Hmat : rw_facade_plain_materialize_well_founded_type) {K}
    (EK : encoding K) (rules : list (rewrite_rule K)) (seed : term K) (source : rw_term K unit nat)
    (legacy : rw_legacy_tracked_state K) (tree : rw_term K unit nat) : option (list (rewrite_step
    K)) :=
  match rw_selected_explanation EK unit_encoding nat_encoding
    (rw_tracked_final (rw_legacy_core K legacy)) (rw_legacy_root K legacy) source tree with
  | None => None
  | Some (proof, id) =>
    match rw_facade_checked_materialize_builder Hmat proof id with
    | None => None
    | Some steps =>
      let output := rw_plain_rw_facade_materialize_project_atomic tree in
      if check_explanation EK rules seed output steps then Some steps else None
    end
  end.

Definition rw_legacy_selected_explanation_builder (Hmat :
    rw_facade_plain_materialize_well_founded_type) (K : Type) (EK : encoding K) (rules : list
    (rewrite_rule K)) (seed : term K) (legacy : rw_legacy_tracked_state K) (output : term K) :
    option (list (rewrite_step K)) :=
  let source := legacy_embed seed in
  let tree := legacy_embed output in
  rw_plain_facade_explain_core Hmat EK rules seed source legacy tree.

Definition rw_plain_facade_extract (Hwf : rw_rd_plain_compare_well_founded_type) {K} (EK : encoding
    K) (cost : K -> nat) (legacy : rw_legacy_tracked_state K) : option (rw_shared_tree K unit nat *
    rw_term K unit nat) :=
  let graph := rw_index_graph (rw_tracked_machine (rw_tracked_final (rw_legacy_core K legacy))) in
  match rw_shared_extract_builder Hwf EK unit_encoding nat_encoding (fun _ => 0) cost graph
    (rw_legacy_root K legacy) with
  | None => None
  | Some dag =>
    match rw_shared_unfold dag with
    | None => None
    | Some tree => Some (dag, tree)
    end
  end.

Definition rw_tracked_optimise_builder (Hwf : rw_rd_plain_compare_well_founded_type) (Hmat :
    rw_facade_plain_materialize_well_founded_type) (K : Type) (EK : encoding K) (rules : list
    (rewrite_rule K)) (cost : K -> nat) (fuel : positive) (seed : term K) : option (rw_shared_tree K
    unit nat * list (rewrite_step K)) :=
  let legacy := rw_legacy_tracked_builder Hwf K EK rules fuel seed in
  match rw_plain_facade_extract Hwf EK cost legacy with
  | None => None
  | Some (dag, tree) =>
    let source := legacy_embed seed in
    option_map (fun steps => (dag, steps))
      (rw_plain_facade_explain_core Hmat EK rules seed source legacy tree)
  end.
