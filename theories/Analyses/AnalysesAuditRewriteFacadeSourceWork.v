(** * AnalysesAuditRewriteFacadeSourceWork

    Computes source work for facade table, guard, equality, replay, and checker traces.
    For example, a table-set call includes natural encoding and trie update work.
    Builds on: AnalysesAuditRewriteFacadeReference and
    RewriteAuditQueueReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeReference.
From Galois.Rewrite Require Import RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_facade_table_source_work {A} (trace : audit_trace (rw_facade_table_call A)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeTableSet _ _ _ _ _ enc trie) =>
        64 + audit_nat_events_work enc + audit_trie_update_trace_source_work trie
      | AuditCall (RWFacadeTableGet _ _ _ _ enc trie) =>
        64 + audit_nat_events_work enc + audit_trie_get_trace_source_work trie
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_subst_source_work {K} (trace : audit_trace (rw_facade_subst_call K)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeNth _ _ _ child) => 64 + 64 * audit_work child
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_guard_source_work {K} (actions : list (rw_facade_guard_action K)) : nat :=
  fold_right (fun action total =>
    (
      match action with
      | RWGuardExternal body => body
      | RWGuardSubstitution _ _ trace => 64 + 64 * audit_work trace
      end) + total) 0 actions.

Definition rw_facade_gate_source_work {K} (trace : audit_trace (rw_facade_gate_call K)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeGuard _ _ _ actions) => 64 + rw_facade_guard_source_work actions
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_code_source_work {K} (trace : audit_trace (rw_facade_code_call K)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWCodeOp _ _ body) => 64 + rw_external_events_work body
      | AuditCall (RWCodeNat _ _ child) => 64 + audit_nat_events_work child
      | AuditCall (RWCodeAppend _ _ _ child) => 64 + 64 * audit_work child
      | AuditCall (RWCodeLength _ child) => 64 + 64 * audit_work child
      | AuditCall (RWCodeList _ _ child) =>
        64 + audit_list_events_work audit_basic_encoding_work child
      | AuditCall (RWCodeEmbed _ _ child) => 64 + 64 * audit_work child
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_eq_source_work {K} (trace : audit_trace (rw_facade_eq_call K)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeCode _ _ child) => 64 + rw_facade_code_source_work child
      | AuditCall (RWFacadeEqBits _ _ _ child) => 64 + 64 * audit_work child
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_step_source_work {K} (trace : audit_trace (rw_facade_step_call K)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeLookup _ _ child) => 64 + rw_facade_table_source_work child
      | AuditCall (RWFacadeGate _ _ _ child) => 64 + rw_facade_gate_source_work child
      | AuditCall (RWFacadeSubst _ _ child) => 64 + rw_facade_subst_source_work child
      | AuditCall (RWFacadePosition _ _ _ child) => 64 + 64 * audit_work child
      | AuditCall (RWFacadeEqual _ _ _ child) => 64 + rw_facade_eq_source_work child
      | AuditCall (RWFacadeReplace _ _ _ _ child) => 64 + 64 * audit_work child
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_replay_source_work {K} (trace : audit_trace (rw_facade_replay_call K)) : nat :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeReplayStep _ _ _ child) => 64 + rw_facade_step_source_work child
      | _ => 64
      end) + total) 0 trace.

Definition rw_facade_checker_source_work {K} (trace : audit_trace (rw_facade_checker_call K)) : nat
    :=
  fold_right (fun event total =>
    (
      match event with
      | AuditCall (RWFacadeCheckerTable _ child) => 64 + rw_facade_table_source_work child
      | AuditCall (RWFacadeCheckerReplay _ _ _ child) => 64 + rw_facade_replay_source_work child
      | AuditCall (RWFacadeCheckerEqual _ _ _ child) => 64 + rw_facade_eq_source_work child
      | _ => 64
      end) + total) 0 trace.
