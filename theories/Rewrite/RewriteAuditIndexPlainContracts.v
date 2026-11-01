(** * RewriteAuditIndexPlainContracts

    These types bind index-run contracts to fixed plain source bodies.
    For example, the zero-fuel contract requires the input graph and empty event lists.
    Builds on: RewriteAuditIndexPlainPublic and
    RewriteAuditIndexInterfaceIndexRunZeroContract. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexInterfaceIndexRuleStepSupportedContract
  RewriteAuditIndexInterfaceIndexRunCallbackBoundContract
  RewriteAuditIndexInterfaceIndexRunCleanTraceContract
  RewriteAuditIndexInterfaceIndexRunCorrectContract
  RewriteAuditIndexInterfaceIndexRunZeroContract
  RewriteAuditIndexInterfaceRiApplyRealizesStatement
  RewriteAuditIndexInterfaceRiRuleStepRealizesStatement
  RewriteAuditIndexInterfaceRiRunRealizesStatement RewriteAuditIndexPlainPublic.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** When encoder adapters and rule callbacks agree with their plain counterparts, erasing
    the rule-step observer yields the public index rule-step result. *)
Definition rw_ri_rule_step_realizes_fixed_type : Prop :=
  @rw_ri_rule_step_realizes_statement (@RewriteAuditIndexPlainPublic.rw_index_rule_step).

(** When encoder adapters and rule callbacks agree with their plain counterparts, erasing
    the apply observer yields the public index apply result and rebuild events. *)
Definition rw_ri_apply_realizes_fixed_type : Prop :=
  @rw_ri_apply_realizes_statement (@RewriteAuditIndexPlainPublic.rw_index_rule_step).

(** When encoders and callbacks agree and the strategy adapter agrees and has its
    execution witness, erasing the run observer yields the public index run and events. *)
Definition rw_ri_run_realizes_fixed_type : Prop :=
  @rw_ri_run_realizes_statement (@RewriteAuditIndexPlainPublic.rw_index_run).

(** For sound, well-formed rules and a well-formed, sound, productive input graph, positive
    fuel yields a clean trace from the initial rebuild; stopping leaves no next attempt. *)
Definition rw_index_run_clean_trace_fixed_type : Prop :=
  @rw_index_run_clean_trace_contract (@RewriteAuditIndexPlainPublic.rw_index_rule_step)
    (@RewriteAuditIndexPlainPublic.rw_index_run).

(** Zero fuel returns the input graph, fuel exhaustion, and no events. *)
Definition rw_index_run_zero_fixed_type : Prop :=
  @rw_index_run_zero_contract (@RewriteAuditIndexPlainPublic.rw_index_run).

(** Sound, well-formed rules on a well-formed, sound, productive input graph yield a
    well-formed, sound, productive extension, clean when fuel is nonzero. *)
Definition rw_index_run_correct_fixed_type : Prop :=
  @rw_index_run_correct_contract (@RewriteAuditIndexPlainPublic.rw_index_run).

(** The event count plus one for a stopped run is at most the supplied fuel. *)
Definition rw_index_run_callback_bound_fixed_type : Prop :=
  @rw_index_run_callback_bound_contract (@RewriteAuditIndexPlainPublic.rw_index_run).

(** A successful rule step preserves support and bucket-node support when its rules are
    well formed and the input state has both properties. *)
Definition rw_index_rule_step_supported_fixed_type : Prop :=
  @rw_index_rule_step_supported_contract (@RewriteAuditIndexPlainPublic.rw_index_rule_step).
