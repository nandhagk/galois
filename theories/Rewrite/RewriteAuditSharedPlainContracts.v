(** * Fixed plain shared-operation contract bindings

    Binds shared comparison, extraction, and observer contracts to fixed plain builders.
    For example, with a well-foundedness witness, the rejection contract covers a left tree
    rooted at 1 with an empty node map.
    Builds on: the plain computational bodies and the unchanged public contract schemas. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedCompare
  RewriteAuditSharedExtract RewriteAuditSharedInterfaceRdCompareRealizesStatement
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
Definition rw_rd_plain_compare_realizes_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_compare_realizes_statement (@rw_shared_compare_builder Hwf).

(** If the encoder adapters agree, extraction has a source run returning the public result
    with work bounded by the extraction budget. *)
Definition rw_rd_plain_extract_realizes_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_extract_realizes_statement (@rw_shared_extract_builder Hwf).

(** Unary cost, binary cost, and binary size equal the result projections of their source
    observers after erasing their work counts. *)
Definition rw_rd_plain_scalar_realizes_type : Prop :=
  @rw_rd_scalar_realizes_statement (@rw_shared_tree_cost) (@rw_shared_tree_cost_binary)
    (@rw_shared_tree_size_binary).

(** Comparing well-formed shared trees with successful unfoldings agrees with comparing
    their unfolded tree codes. *)
Definition rw_rd_plain_compare_agrees_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_shared_compare_agrees_contract (@rw_shared_compare_builder Hwf).

(** Comparison returns None if either shared tree is not well formed. *)
Definition rw_rd_plain_compare_reject_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_shared_compare_reject_contract (@rw_shared_compare_builder Hwf).

(** On a well-formed graph, shared and tree extraction fail together or produce a
    well-formed shared tree unfolding to the extracted tree. *)
Definition rw_rd_plain_extract_unfold_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_shared_extract_unfold_contract (@rw_shared_extract_builder Hwf).

(** A well-formed shared tree with a successful unfolding has the unfolded tree cost. *)
Definition rw_rd_plain_tree_cost_agrees_type : Prop :=
  @rw_shared_tree_cost_agrees_contract (@rw_shared_tree_cost).

(** A well-formed shared tree with a successful unfolding has the unfolded cost in binary. *)
Definition rw_rd_plain_tree_cost_binary_agrees_type : Prop :=
  @rw_shared_tree_cost_binary_agrees_contract (@rw_shared_tree_cost_binary).

(** A well-formed shared tree with a successful unfolding has the unfolded size in binary. *)
Definition rw_rd_plain_tree_size_binary_agrees_type : Prop :=
  @rw_shared_tree_size_binary_agrees_contract (@rw_shared_tree_size_binary).

(** Unfolding, cost, binary cost, and binary size all reject a malformed shared tree. *)
Definition rw_rd_plain_observers_reject_type : Prop :=
  @rw_shared_observers_reject_contract (@rw_shared_tree_cost) (@rw_shared_tree_cost_binary)
    (@rw_shared_tree_size_binary).

(** When encoder adapters agree, a source comparison run returns the plain builder's result. *)
Definition rw_rd_plain_compare_source_erases_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V) op sort value left right
    answer work,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_shared_compare_run op sort value left right answer work ->
    rw_shared_compare_builder Hwf EK ES EV left right = answer.

(** When encoder adapters agree, a source extraction run returns the plain builder's result. *)
Definition rw_rd_plain_extract_source_erases_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    op sort value vc oc g root answer work,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_shared_extract_run op sort value vc oc g root answer work ->
    rw_shared_extract_builder Hwf EK ES EV (fun v => fst (vc v))
      (fun k => fst (oc k)) g root = answer.

(** Plain dynamic-programming production equals the result of the source observer. *)
Definition rw_rd_plain_production_source_erases_type : Prop :=
  forall K Sort V vc oc (g : RewriteEgraph.rw_graph K Sort V) old node store,
    rd_plain_production (fun v => fst (vc v)) (fun k => fst (oc k)) g old node store =
      fst (rw_rd_production vc oc g old node store).
