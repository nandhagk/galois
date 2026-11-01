(** * RewriteAuditSharedInterfaceSharedExtractUnfoldContract

    This module states the prospective agreement of shared extraction and tree extraction.
    For example, for root 1 of a well-formed graph with empty node and root lists and empty
    maps, the contract permits both extractions to return None.
    Builds on: RewriteAuditSharedReference and
    RewriteExtract. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_extract : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  (V -> nat) -> (K -> nat) -> rw_graph K Sort V -> rw_id -> option (rw_shared_tree K Sort V).

(** On a well-formed graph, shared and tree extraction fail together or produce a
    well-formed shared tree unfolding to the extracted tree. *)
Definition rw_shared_extract_unfold_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) vc oc (g : rw_graph K Sort V) c,
    rw_graph_wf sig g ->
    match rw_shared_extract EK ES EV vc oc g c,
          rw_extract_tree EK ES EV vc oc g c with
    | None, None => True
    | Some dag, Some tree => rw_shared_wf dag /\ rw_shared_unfold dag = Some tree
    | _, _ => False
    end.

End FuturePublicImplementations.
