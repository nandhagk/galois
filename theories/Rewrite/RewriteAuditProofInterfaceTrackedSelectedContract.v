(** * RewriteAuditProofInterfaceTrackedSelectedContract

    This module states when a tracked run must provide a selected explanation.
    For example, extracting variable 0 requires an explanation ending at that variable when
    the rules are sound and well formed and the seed is typed.
    Builds on: RewriteAuditProofRun and
    RewriteAuditProofSemantic. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofRun RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},
    encoding K -> encoding Sort -> encoding V -> encoding H ->
    rw_signature K Sort V -> list (rw_rule K Sort V H) ->
    (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->
    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

Variable rw_selected_explanation : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> rw_tracked_state K Sort V H -> rw_id ->
  rw_term K Sort V -> rw_term K Sort V -> option (rw_provenance K Sort V H * positive).

(** For sound, well-formed rules and a typed seed, a successfully extracted tree has
    a valid selected explanation connecting the seed and tree. *)
Definition rw_tracked_selected_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    forall seed, rw_typed sig seed -> forall strategy fuel vc oc tree,
      let '(root, result) := rw_tracked_run EK ES EV EH sig rules strategy fuel seed in
      rw_extract_tree EK ES EV vc oc (rw_tracked_graph (rw_tracked_final result)) root =
        Some tree ->
      exists proof id node,
        rw_selected_explanation EK ES EV (rw_tracked_final result) root seed tree =
          Some (proof, id) /\
        rw_provenance_valid EH sig rules proof /\
        Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
        rw_evidence_left node = seed /\ rw_evidence_right node = tree.

End FuturePublicImplementations.
