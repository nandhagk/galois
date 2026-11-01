(** * RewriteAuditIndexRuleTableContracts

    This module states a polynomial work bound for rule-table construction.
    For example, at start 0 with no rules, the stated bound is 65536.
    Builds on: RewriteAuditIndexRules and
    RewriteRules. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRules.
Import List.ListNotations.

(** Building a rule table costs at most the stated polynomial in its start and rule count. *)
Definition rw_rp_rule_table_bound_statement : Prop :=
  forall K Sort V H (rules : list (rw_rule K Sort V H)) start,
    (N.of_nat (snd (rw_rp_rule_table_atomic rules start)) <=
      65536 * N.pow (N.of_nat (S (start + length rules))) 16)%N.
