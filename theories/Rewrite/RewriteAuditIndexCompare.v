(** * RewriteAuditIndexCompare

    This module wraps positive equality decisions in index-audit events and states their bounds.
    For example, comparing 1 with 1 records a decision event whose answer is true.
    Builds on: RewriteAuditQueuePositive and
    PArith. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueuePositive.
Import List.ListNotations.

Inductive rw_ri_positive_call : Type :=
  | RIPositiveDecision : positive -> positive -> bool -> rw_ri_positive_call
  | RIPositiveFrame : rw_rq_decision_frame -> rw_ri_positive_call.

Definition rw_ri_positive_dec_atomic (a b : positive) : bool * audit_trace rw_ri_positive_call :=
  let '(answer, frames) := rw_rq_decision_atomic a b in
  (answer, AuditCall (RIPositiveDecision a b answer) ::
    map (fun frame => AuditCall (RIPositiveFrame frame)) frames).

Definition rw_ri_positive_dec_budget (a : positive) : nat :=
  8 * Pos.size_nat a.

(** Erasing the decision frames yields the standard equality decision on positive numbers. *)
Definition rw_ri_positive_dec_erases_contract : Prop :=
  forall a b, fst (rw_ri_positive_dec_atomic a b) = if Pos.eq_dec a b then true else false.

(** The decision trace length is bounded by a budget based on the first positive operand. *)
Definition rw_ri_positive_dec_bound_contract : Prop :=
  forall a b, audit_work (snd (rw_ri_positive_dec_atomic a b)) <= rw_ri_positive_dec_budget a.
