(** * RewriteAuditSharedFixedContracts

    These types bind the shared-operation contracts to fixed plain source builders.
    For example, given the well-foundedness witness, the rejection contract requires None
    when the left node map is empty.
    Builds on: RewriteAuditSharedPlain and
    RewriteAuditSharedInterfaceRdScalarRealizesStatement. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedInterfaceRdCompareRealizesStatement
  RewriteAuditSharedInterfaceRdExtractRealizesStatement
  RewriteAuditSharedInterfaceRdScalarRealizesStatement
  RewriteAuditSharedInterfaceSharedCompareAgreesContract
  RewriteAuditSharedInterfaceSharedCompareRejectContract
  RewriteAuditSharedInterfaceSharedExtractUnfoldContract
  RewriteAuditSharedInterfaceSharedObserversRejectContract
  RewriteAuditSharedInterfaceSharedTreeCostAgreesContract
  RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract
  RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract RewriteAuditSharedPlain.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** If the encoder adapters agree, comparison has a source run returning the public result
    with work bounded by the comparison budget. *)
Definition rw_rd_compare_realizes_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_compare_realizes_statement (@RewriteAuditSharedPlain.rw_shared_compare_builder Hwf).

(** If the encoder adapters agree, extraction has a source run returning the public result
    with work bounded by the extraction budget. *)
Definition rw_rd_extract_realizes_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_extract_realizes_statement (@RewriteAuditSharedPlain.rw_shared_extract_builder Hwf).

(** Unary cost, binary cost, and binary size equal the result projections of their source
    observers after erasing their work counts. *)
Definition rw_rd_scalar_realizes_fixed_type : Prop :=
  @rw_rd_scalar_realizes_statement (@RewriteAuditSharedPlain.rw_shared_tree_cost)
    (@RewriteAuditSharedPlain.rw_shared_tree_cost_binary)
    (@RewriteAuditSharedPlain.rw_shared_tree_size_binary).

(** Comparing well-formed shared trees with successful unfoldings agrees with comparing
    their unfolded tree codes. *)
Definition rw_shared_compare_agrees_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  @rw_shared_compare_agrees_contract (@RewriteAuditSharedPlain.rw_shared_compare_builder Hwf).

(** Comparison returns None if either shared tree is not well formed. *)
Definition rw_shared_compare_reject_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  @rw_shared_compare_reject_contract (@RewriteAuditSharedPlain.rw_shared_compare_builder Hwf).

(** On a well-formed graph, shared and tree extraction fail together or produce a
    well-formed shared tree unfolding to the extracted tree. *)
Definition rw_shared_extract_unfold_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  @rw_shared_extract_unfold_contract (@RewriteAuditSharedPlain.rw_shared_extract_builder Hwf).

(** A well-formed shared tree with a successful unfolding has the unfolded tree cost. *)
Definition rw_shared_tree_cost_agrees_fixed_type : Prop :=
  @rw_shared_tree_cost_agrees_contract (@RewriteAuditSharedPlain.rw_shared_tree_cost).

(** A well-formed shared tree with a successful unfolding has the unfolded cost in binary. *)
Definition rw_shared_tree_cost_binary_agrees_fixed_type : Prop :=
  @rw_shared_tree_cost_binary_agrees_contract (@RewriteAuditSharedPlain.rw_shared_tree_cost_binary).

(** A well-formed shared tree with a successful unfolding has the unfolded size in binary. *)
Definition rw_shared_tree_size_binary_agrees_fixed_type : Prop :=
  @rw_shared_tree_size_binary_agrees_contract (@RewriteAuditSharedPlain.rw_shared_tree_size_binary).

(** Unfolding, cost, binary cost, and binary size all reject a malformed shared tree. *)
Definition rw_shared_observers_reject_fixed_type : Prop :=
  @rw_shared_observers_reject_contract (@RewriteAuditSharedPlain.rw_shared_tree_cost)
    (@RewriteAuditSharedPlain.rw_shared_tree_cost_binary)
    (@RewriteAuditSharedPlain.rw_shared_tree_size_binary).
