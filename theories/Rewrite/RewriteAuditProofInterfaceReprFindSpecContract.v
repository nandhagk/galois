(** * RewriteAuditProofInterfaceReprFindSpecContract

    States the prospective representation-search witness and absence contract.
    For example, for a well-formed graph and agreeing view, a None result must rule out
    representation at the requested root.
    Builds on: RewriteAuditProofRepresentation and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRepresentation.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_repr_find : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_phase_view K Sort V -> rw_id -> rw_term K Sort V -> option (rw_repr_witness K Sort V).

(** On a well-formed graph and agreeing view, this contract requires a valid returned witness
    or, on None, absence of representation in the requested class. *)
Definition rw_repr_find_spec_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) view c t,
    rw_graph_wf sig g -> rw_view_agrees g view ->
    match rw_repr_find EK ES EV view c t with
    | Some w => rw_repr_witness_valid g c t w
    | None => ~ rw_represents g c t
    end.

End FuturePublicImplementations.
