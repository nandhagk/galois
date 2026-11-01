(** * RewriteAuditProofInterfaceTrackedTickCongruenceContract

    This module states the prospective evidence contract for congruence ticks.
    For example, with valid provenance and witnesses, a congruence at stamp (0, 1) must record
    the endpoints of any two witnesses that unfold successfully.
    Builds on: RewriteAuditProofCarrier and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofSemantic RewriteAuditProofTick
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

(** With valid provenance and witnesses, a congruence tick records stamped evidence
    between any successfully unfolded witnesses for the merged roots. *)
Definition rw_tracked_tick_congruence_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) rules stamp
    (state next : rw_tracked_state K Sort V H) n m a b root,
    rw_provenance_valid EH sig rules (rw_tracked_provenance state) ->
    rw_class_witnesses_valid (rw_tracked_graph state) (rw_tracked_witnesses state) ->
    rw_tracked_tick EK ES EV stamp state = Some (next, RWIndexCongruence (n, m) a b root) ->
    forall left_id right_id left right,
      let store := rw_tracked_witnesses state in
      Map.get positive_encoding a (rw_class_witness_roots store) = Some left_id ->
      Map.get positive_encoding b (rw_class_witness_roots store) = Some right_id ->
      rw_shared_unfold (RwSharedTree K Sort V left_id (rw_class_witness_nodes store)) = Some left ->
      rw_shared_unfold (RwSharedTree K Sort V right_id (rw_class_witness_nodes store)) =
        Some right ->
      exists id node,
        Map.get (pair_encoding nat_encoding nat_encoding) stamp (rw_tracked_event_nodes next) =
          Some id /\
        Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) =
          Some node /\
        rw_evidence_time node = stamp /\ rw_evidence_left node = left /\ rw_evidence_right node =
          right.

End FuturePublicImplementations.
