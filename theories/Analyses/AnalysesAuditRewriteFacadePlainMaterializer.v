(** * Fixed plain proof-DAG materialization

    After shape validation, root and positioned-child calls attempt ordered replay; a failed
    validation or subcall returns None.
    For example, successful symmetry reverses a two-step replay and flips both directions.
    Builds on: original provenance data, plain facade helpers and checked shape validation. *)

From Stdlib Require Import List Bool PArith NArith Wellfounded.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeCheckedMaterialize
  AnalysesAuditRewriteFacadeDimensions AnalysesAuditRewriteFacadeOptimizer
  AnalysesAuditRewriteFacadePlainHelpers AnalysesAuditRewriteFacadeWholeContracts.
From Galois.Rewrite Require Import RewriteAuditProofCarrier.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Inductive rw_facade_plain_materialize_call : Type :=
  | RWFacadePlainRoot (id : positive)
  | RWFacadePlainChildren (ids : list positive) (position : nat).

(** The dispatcher descends through stored symmetry, transitivity and congruence references,
    and from a child list to its head and tail. *)
Inductive rw_facade_plain_materialize_descend {K} (proof : rw_provenance K unit nat nat) :
    rw_facade_plain_materialize_call -> rw_facade_plain_materialize_call -> Prop :=
  | RWFacadeDescendSym : forall id node child,
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
      rw_evidence_reason_of node = RWEvidenceSym child ->
      rw_facade_plain_materialize_descend proof (RWFacadePlainRoot child) (RWFacadePlainRoot id)
  | RWFacadeDescendFirst : forall id node first second,
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
      rw_evidence_reason_of node = RWEvidenceTrans first second ->
      rw_facade_plain_materialize_descend proof (RWFacadePlainRoot first) (RWFacadePlainRoot id)
  | RWFacadeDescendSecond : forall id node first second,
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
      rw_evidence_reason_of node = RWEvidenceTrans first second ->
      rw_facade_plain_materialize_descend proof (RWFacadePlainRoot second) (RWFacadePlainRoot id)
  | RWFacadeDescendCongruence : forall id node children,
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
      rw_evidence_reason_of node = RWEvidenceCongruence children ->
      rw_facade_plain_materialize_descend proof (RWFacadePlainChildren children 0)
        (RWFacadePlainRoot id)
  | RWFacadeDescendChild : forall id rest position,
      rw_facade_plain_materialize_descend proof (RWFacadePlainRoot id)
        (RWFacadePlainChildren (id :: rest) position)
  | RWFacadeDescendTail : forall id rest position,
      rw_facade_plain_materialize_descend proof (RWFacadePlainChildren rest (S position))
        (RWFacadePlainChildren (id :: rest) position).

(** Complete stored-key/reference validation makes the literal dispatcher well founded. *)
Definition rw_facade_plain_materialize_well_founded_type : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root,
    rw_plain_rw_facade_materialize_shape_atomic proof root = true ->
    well_founded (rw_facade_plain_materialize_descend proof).

Definition rw_facade_plain_materialize_body {K} (proof : rw_provenance K unit nat nat)
    (call : rw_facade_plain_materialize_call)
    (recurse : forall child, rw_facade_plain_materialize_descend proof child call ->
      option (list (rewrite_step K))) : option (list (rewrite_step K)).
Proof.
  destruct call as [id | ids position].
  - destruct (Map.get positive_encoding id (rw_provenance_nodes proof)) as [node |] eqn:Hnode;
      [|exact None].
    destruct (rw_evidence_reason_of node) as [|rule bindings|child|first second|children]
      eqn:Hreason.
    + exact (Some []).
    + exact (Some [RewriteStep [] rule true (rw_plain_rw_facade_bindings_atomic bindings)]).
    + destruct (recurse (RWFacadePlainRoot child)
        (RWFacadeDescendSym proof id node child Hnode Hreason)) as [steps |]; [|exact None].
      exact (Some (rw_plain_rw_facade_invert_onto steps [])).
    + destruct (recurse (RWFacadePlainRoot first)
        (RWFacadeDescendFirst proof id node first second Hnode Hreason)) as [lhs |];
        [|exact None].
      destruct (recurse (RWFacadePlainRoot second)
        (RWFacadeDescendSecond proof id node first second Hnode Hreason)) as [rhs |];
        [|exact None].
      exact (Some (lhs ++ rhs)).
    + exact (recurse (RWFacadePlainChildren children 0)
        (RWFacadeDescendCongruence proof id node children Hnode Hreason)).
  - destruct ids as [|id rest]; [exact (Some []) |].
    destruct (recurse (RWFacadePlainRoot id)
      (RWFacadeDescendChild proof id rest position)) as [steps |]; [|exact None].
    pose (prefixed := rw_plain_rw_facade_prefix_atomic position steps).
    destruct (recurse (RWFacadePlainChildren rest (S position))
      (RWFacadeDescendTail proof id rest position)) as [tail |]; [|exact None].
    exact (Some (prefixed ++ tail)).
Defined.

(** The fixed kernel consumes only actual accessibility evidence for its literal calls. *)
Definition rw_facade_plain_materialize_execute {K} (proof : rw_provenance K unit nat nat) (call :
    rw_facade_plain_materialize_call) (accessible : Acc (rw_facade_plain_materialize_descend proof)
    call) : option (list (rewrite_step K)) :=
  @Fix_F rw_facade_plain_materialize_call (rw_facade_plain_materialize_descend proof)
    (fun _ => option (list (rewrite_step K))) (rw_facade_plain_materialize_body proof)
    call accessible.

(** Full shape validation guards the exact proof-DAG dispatcher without identifier fuel. *)
Definition rw_facade_checked_materialize_builder
    (Hmat : rw_facade_plain_materialize_well_founded_type)
    {K} (proof : rw_provenance K unit nat nat) (root : positive)
    : option (list (rewrite_step K)).
Proof.
  destruct (rw_plain_rw_facade_materialize_shape_atomic proof root) eqn:Hshape.
  - exact (rw_facade_plain_materialize_execute proof (RWFacadePlainRoot root)
      (Hmat K proof root Hshape (RWFacadePlainRoot root))).
  - exact None.
Defined.

(** A checked source run has exactly the fixed builder's actual replay result. *)
Definition rw_facade_plain_materialize_source_erases_type (Hmat :
    rw_facade_plain_materialize_well_founded_type) : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root result work,
    rw_facade_checked_materialize_run proof root result work ->
    rw_facade_checked_materialize_builder Hmat proof root = result.

(** The builder has a fixed source execution including its validation and expanded replay work. *)
Definition rw_facade_plain_materialize_realizes_type (Hmat :
    rw_facade_plain_materialize_well_founded_type) : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root, exists work,
    rw_facade_checked_materialize_run proof root
      (rw_facade_checked_materialize_builder Hmat proof root) work.

(** The plain full-store shape check agrees with its unchanged counted source mirror. *)
Definition rw_facade_plain_materialize_shape_erases_type : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root,
    rw_plain_rw_facade_materialize_shape_atomic proof root =
      fst (rw_facade_materialize_shape_atomic proof root).

(** The materialization builder has a source run whose work meets the proof-and-result ceiling. *)
Definition rw_facade_plain_materialize_source_bound_type (Hmat :
    rw_facade_plain_materialize_well_founded_type) : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root,
    let result := rw_facade_checked_materialize_builder Hmat proof root in
    exists work, rw_facade_checked_materialize_run proof root result work /\
    let dimension := S (rw_facade_proof_dimension proof + Pos.size_nat root +
      match result with
      | None => 1
      | Some steps => rw_facade_steps_dimension steps
      end) in
    (N.of_nat work <= rw_facade_whole_ceiling 0%N dimension 0 0 0)%N.
