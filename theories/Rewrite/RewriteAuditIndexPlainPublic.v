(** * RewriteAuditIndexPlainPublic

    This module exposes plain indexed rule-step, run, and apply operations.
    For example, a failed index rule step makes index application return None.
    Builds on: RewriteAuditPlainCore1 and
    RewriteAuditIndexTickReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexTickReference
  RewriteAuditPlainCore1 RewriteAuditPlainPrimitives.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_index_rule_step {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V) :=
  rw_plain_rw_ri_rule_step_atomic EK ES EV EH (rw_plain_callbacks_of sig) rules state attempt.

Definition rw_index_run {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) (fuel : N)
    (graph : rw_graph K Sort V) :
    rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H) :=
  rw_plain_rw_ri_run_atomic EK ES EV EH (rw_plain_callbacks_of sig) rules
    (fun state => strategy (rw_index_view EK ES EV state)) fuel graph.

Definition rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.
