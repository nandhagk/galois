(** * RewriteAuditProofInterfaceTrackedExtractableContract

    This module states a prospective extraction guarantee for tracked runs.
    For example, with sound, well-formed rules and a typed variable seed, it requires
    an extractable root even when fuel is zero.
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
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofSemantic.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->
  N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

(** For sound, well-formed rules and a typed seed, a tracked run admits extraction
    at the returned root. *)
Definition rw_tracked_extractable_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    forall seed, rw_typed sig seed -> forall strategy fuel vc oc,
      let '(root, result) := rw_tracked_run EK ES EV EH sig rules strategy fuel seed in
      exists tree, rw_extract_tree EK ES EV vc oc (rw_tracked_graph (rw_tracked_final result))
        root = Some tree.

End FuturePublicImplementations.
