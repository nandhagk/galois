(** * RewriteAuditSharedInterfaceSharedCompareAgreesContract

    This module states comparison agreement for well-formed, unfoldable shared trees.
    For example, if two well-formed singleton DAGs map root 1 to a variable of natural sort 0
    and value 0 and unfold to it, the proposed result compares its tree code with itself.
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

Variable rw_shared_compare : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option bool.

(** Comparing well-formed shared trees with successful unfoldings agrees with comparing
    their unfolded tree codes. *)
Definition rw_shared_compare_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (left right : rw_shared_tree K Sort V) t u,
    rw_shared_wf left -> rw_shared_wf right ->
    rw_shared_unfold left = Some t -> rw_shared_unfold right = Some u ->
    rw_shared_compare EK ES EV left right =
      Some (rw_codes_leb (rw_tree_code EK ES EV t) (rw_tree_code EK ES EV u)).

End FuturePublicImplementations.
