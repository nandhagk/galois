(** * RewriteAuditQueuePositive

    This module records the construction and application of a positive equality decision.
    For example, comparing 1 with 2 records a false return after building the decision for 1.
    Builds on: binary positive arithmetic in PArith. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Inductive rw_rq_decision_frame : Type :=
  | RQDecBuildCase : positive -> rw_rq_decision_frame
  | RQDecBuildRecursive : positive -> rw_rq_decision_frame
  | RQDecClosure : positive -> rw_rq_decision_frame
  | RQDecApply : positive -> positive -> rw_rq_decision_frame
  | RQDecInspect : positive -> rw_rq_decision_frame
  | RQDecReturn : bool -> rw_rq_decision_frame.

Fixpoint rw_rq_decision_build (first : positive) : (positive -> bool * list rw_rq_decision_frame) *
    list rw_rq_decision_frame :=
  match first with
  | xH =>
    ((fun second =>
      let answer :=
        match second with
        | xH => true
        | _ => false
        end in
      (answer, [RQDecInspect second; RQDecReturn answer])),
      [RQDecBuildCase first; RQDecClosure first])
  | xI rest =>
    let '(child, build_trace) := rw_rq_decision_build rest in
    ((fun second =>
      match second with
      | xI tail =>
        let '(answer, call_trace) := child tail in
        (answer, [RQDecInspect second; RQDecApply rest tail] ++ call_trace ++
          [RQDecReturn answer])
      | _ => (false, [RQDecInspect second; RQDecReturn false])
      end),
      [RQDecBuildCase first; RQDecBuildRecursive rest] ++ build_trace ++
        [RQDecClosure first])
  | xO rest =>
    let '(child, build_trace) := rw_rq_decision_build rest in
    ((fun second =>
      match second with
      | xO tail =>
        let '(answer, call_trace) := child tail in
        (answer, [RQDecInspect second; RQDecApply rest tail] ++ call_trace ++
          [RQDecReturn answer])
      | _ => (false, [RQDecInspect second; RQDecReturn false])
      end),
      [RQDecBuildCase first; RQDecBuildRecursive rest] ++ build_trace ++
        [RQDecClosure first])
  end.

Definition rw_rq_decision_atomic (first second : positive) : bool * list rw_rq_decision_frame :=
  let '(compare, build_trace) := rw_rq_decision_build first in
  let '(answer, call_trace) := compare second in
  (answer, build_trace ++ RQDecApply first second :: call_trace).

(** Erasing decision frames yields the standard positive equality decision. *)
Definition rw_rq_decision_source_erases_statement : Prop :=
  forall first second, fst (rw_rq_decision_atomic first second) = if Pos.eq_dec first second then
    true else false.

(** Building the positive decision emits three frames per first-operand bit minus one. *)
Definition rw_rq_decision_build_count_statement : Prop :=
  forall first, length (snd (rw_rq_decision_build first)) = 3 * Pos.size_nat first - 1.

(** The weighted positive-decision trace length is bounded by both operand bit lengths. *)
Definition rw_rq_decision_source_bound_statement : Prop :=
  forall first second, 64 * length (snd (rw_rq_decision_atomic first second)) <= 1024 + 512 *
    (Pos.size_nat first + Pos.size_nat second).
