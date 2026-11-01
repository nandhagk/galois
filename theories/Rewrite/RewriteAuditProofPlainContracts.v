(** * RewriteAuditProofPlainContracts

    These types instantiate tracked-run, factful, and representation contracts with plain bodies.
    For example, the zero-fuel factful run contract retains the input fact store.
    Builds on: RewriteAuditIndexPlainPublic and
    RewriteAuditProofPlainPublic. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic
  RewriteAuditProofInterfaceFactfulRunCallbackBoundContract
  RewriteAuditProofInterfaceFactfulRunValidContract
  RewriteAuditProofInterfaceFactfulRunZeroContract
  RewriteAuditProofInterfaceReprFindSpecContract
  RewriteAuditProofInterfaceRpApplyRealizesStatement
  RewriteAuditProofInterfaceRpConnectRealizesStatement
  RewriteAuditProofInterfaceRpFactRunRealizesStatement
  RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement
  RewriteAuditProofInterfaceRpRebuildRealizesStatement
  RewriteAuditProofInterfaceRpReprRealizesStatement
  RewriteAuditProofInterfaceRpRuleStepRealizesStatement
  RewriteAuditProofInterfaceRpRunRealizesStatement
  RewriteAuditProofInterfaceRpSelectedRealizesStatement
  RewriteAuditProofInterfaceRpTickRealizesStatement
  RewriteAuditProofInterfaceTrackedApplyProjectsContract
  RewriteAuditProofInterfaceTrackedExtractableContract
  RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContract
  RewriteAuditProofInterfaceTrackedFactfulApplyRejectContract
  RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract
  RewriteAuditProofInterfaceTrackedRunInvariantsContract
  RewriteAuditProofInterfaceTrackedSelectedContract
  RewriteAuditProofInterfaceTrackedTickCongruenceContract
  RewriteAuditProofInterfaceTrackedTickProjectionContract RewriteAuditProofPlainPublic.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** When encoders and rule callbacks agree and the strategy adapter agrees and has its
    execution witness, the erased run observer equals the public tracked run. *)
Definition rw_rp_run_realizes_fixed_type : Prop :=
  @rw_rp_run_realizes_statement (@RewriteAuditProofPlainPublic.rw_tracked_run).

(** When operator, sort, and value adapters agree, the erased selected observer yields
    the public explanation for the same state, root, seed, and tree. *)
Definition rw_rp_selected_realizes_fixed_type : Prop :=
  @rw_rp_selected_realizes_statement (@RewriteAuditProofPlainPublic.rw_selected_explanation).

(** On a well-formed graph and agreeing view, this contract requires a valid returned witness
    or, on None, absence of representation in the requested class. *)
Definition rw_repr_find_spec_fixed_type : Prop :=
  @rw_repr_find_spec_contract (@RewriteAuditProofPlainPublic.rw_repr_find).

(** For sound, well-formed rules and a typed seed, a tracked run admits extraction
    at the returned root. *)
Definition rw_tracked_extractable_fixed_type : Prop :=
  @rw_tracked_extractable_contract (@RewriteAuditProofPlainPublic.rw_tracked_run).

(** For sound, well-formed rules and a typed seed, a successfully extracted tree has
    a valid selected explanation connecting the seed and tree. *)
Definition rw_tracked_selected_fixed_type : Prop :=
  @rw_tracked_selected_contract (@RewriteAuditProofPlainPublic.rw_tracked_run)
    (@RewriteAuditProofPlainPublic.rw_selected_explanation).

(** For sound, well-formed rules and a typed seed, the final graph is well formed, sound,
    productive, and represents the seed; final provenance, witnesses, connections, and event
    indices are valid, and nonzero fuel yields a clean graph. *)
Definition rw_tracked_run_invariants_fixed_type : Prop :=
  @rw_tracked_run_invariants_contract (@RewriteAuditProofPlainPublic.rw_tracked_run)
    (@RewriteAuditProofPlainPublic.rw_connect_class).

(** For a valid tracked phase and fresh stamp, a tracked tick projects to the index
    tick and preserves phase validity on success. *)
Definition rw_tracked_tick_projection_fixed_type : Prop :=
  @rw_tracked_tick_projection_contract (@RewriteAuditProofPlainPublic.rw_connect_class)
    (@RewriteAuditProofPlainPublic.rw_tracked_tick).

(** With valid provenance and witnesses, a congruence tick records stamped evidence
    between any successfully unfolded witnesses for the merged roots. *)
Definition rw_tracked_tick_congruence_fixed_type : Prop :=
  @rw_tracked_tick_congruence_contract (@RewriteAuditProofPlainPublic.rw_tracked_tick).

(** A valid tracked phase and fresh initial stamp yield a valid final phase, a tracked
    rebuild trace, and the same machine and events as index rebuild. *)
Definition rw_tracked_rebuild_trace_correct_fixed_type : Prop :=
  @rw_tracked_rebuild_trace_correct_contract (@RewriteAuditProofPlainPublic.rw_connect_class)
    (@RewriteAuditProofPlainPublic.rw_tracked_tick)
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild).

(** For well-formed rules, a valid tracked phase, and a fresh stamp, apply projects to
    index apply; success preserves phase validity and records the stamped rule evidence. *)
Definition rw_tracked_apply_projects_fixed_type : Prop :=
  @rw_tracked_apply_projects_contract (@RewriteAuditIndexPlainPublic.rw_index_rule_step)
    (@RewriteAuditProofPlainPublic.rw_connect_class)
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
    (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** Factful apply rejects exactly when the corresponding tracked apply rejects. *)
Definition rw_tracked_factful_apply_reject_fixed_type : Prop :=
  @rw_tracked_factful_apply_reject_contract (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
    (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** Given valid input facts, a successful factful apply matches tracked apply and
    invalidates the facts while preserving their validity for the new graph. *)
Definition rw_tracked_factful_apply_accept_fixed_type : Prop :=
  @rw_tracked_factful_apply_accept_contract (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
    (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** Zero fuel returns the tracked state and facts unchanged with no events. *)
Definition rw_factful_run_zero_fixed_type : Prop :=
  @rw_factful_run_zero_contract (@RewriteAuditProofPlainPublic.rw_factful_run).

(** A factful run preserves fact-store validity when the input store is valid. *)
Definition rw_factful_run_valid_fixed_type : Prop :=
  @rw_factful_run_valid_contract (@RewriteAuditProofPlainPublic.rw_factful_run).

(** The factful run event count plus one when stopped is bounded by its fuel. *)
Definition rw_factful_run_callback_bound_fixed_type : Prop :=
  @rw_factful_run_callback_bound_contract (@RewriteAuditProofPlainPublic.rw_factful_run).

(** When operator, sort, and value adapters agree, erasing representation-search work
    yields the representation search on the index snapshot. *)
Definition rw_rp_repr_realizes_fixed_type : Prop :=
  @rw_rp_repr_realizes_statement (@RewriteAuditProofPlainPublic.rw_repr_find).

(** When the operator, sort, and value adapters agree, erasing connection observation
    yields the public class-connection result for the supplied endpoints. *)
Definition rw_rp_connect_realizes_fixed_type : Prop :=
  @rw_rp_connect_realizes_statement (@RewriteAuditProofPlainPublic.rw_connect_class).

(** When operator, sort, and value adapters agree, the erased tick observer yields
    the public tracked tick result. *)
Definition rw_rp_tick_realizes_fixed_type : Prop :=
  @rw_rp_tick_realizes_statement (@RewriteAuditProofPlainPublic.rw_tracked_tick).

(** When operator, sort, and value adapters agree, the erased rebuild observer yields
    the public tracked rebuild state and events. *)
Definition rw_rp_rebuild_realizes_fixed_type : Prop :=
  @rw_rp_rebuild_realizes_statement (@RewriteAuditProofPlainPublic.rw_tracked_rebuild).

(** When encoders and rule callbacks agree, the erased rule-step observer equals the
    public tracked rule-step result. *)
Definition rw_rp_rule_step_realizes_fixed_type : Prop :=
  @rw_rp_rule_step_realizes_statement (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** When encoders and rule callbacks agree, the erased apply observer equals tracked apply. *)
Definition rw_rp_apply_realizes_fixed_type : Prop :=
  @rw_rp_apply_realizes_statement (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
    (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** When encoders and rule callbacks agree, the erased factful apply observer equals
    the public tracked factful apply result. *)
Definition rw_rp_factful_apply_realizes_fixed_type : Prop :=
  @rw_rp_factful_apply_realizes_statement (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
    (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** When encoders, rule callbacks, and fact strategies agree, the erased factful run
    observer yields the public factful run result. *)
Definition rw_rp_fact_run_realizes_fixed_type : Prop :=
  @rw_rp_fact_run_realizes_statement (@RewriteAuditProofPlainPublic.rw_factful_run).
