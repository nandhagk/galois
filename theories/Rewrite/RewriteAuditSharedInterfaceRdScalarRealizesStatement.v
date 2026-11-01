(** * RewriteAuditSharedInterfaceRdScalarRealizesStatement

    This module states prospective realization of unary and binary shared-tree observers.
    For example, on the singleton DAG whose root 1 maps to a variable of natural sort 0 and
    value 0, the contract equates binary size with the source result after erasing its work.
    Builds on: RewriteAuditSharedObservers and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedObservers RewriteAuditSharedPlain
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_cost : forall {K Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option nat.

Variable rw_shared_tree_cost_binary : forall {K Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option N.

Variable rw_shared_tree_size_binary : forall {K Sort V}, rw_shared_tree K Sort V -> option N.

(** Unary cost, binary cost, and binary size equal the result projections of their source
    observers after erasing their work counts. *)
Definition rw_rd_scalar_realizes_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K -> nat * nat) (dag : rw_shared_tree K Sort V),
    rw_shared_tree_cost (fun v => fst (vc v)) (fun k => fst (oc k)) dag =
      fst (rw_shared_tree_cost_atomic vc oc dag) /\
    rw_shared_tree_cost_binary (fun v => fst (vc v)) (fun k => fst (oc k)) dag =
      fst (rw_shared_tree_cost_binary_atomic vc oc dag) /\
    rw_shared_tree_size_binary dag = fst (rw_shared_tree_size_binary_atomic dag).

End FuturePublicImplementations.
