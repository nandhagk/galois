(** * RewriteAuditProofInterfaceTrackedPhaseValid

    Defines the invariant joining index validity, provenance, class witnesses, and connections.
    For example, provenance identifiers [1; 1] violate the required no-duplicates invariant.
    Builds on: RewriteAuditProofSemantic and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).

(** A valid tracked phase combines index, provenance, class witness, and class
    connection invariants. *)
Definition rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\ rw_provenance_valid EH sig rules proof /\
  rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
  rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
    (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.

End FuturePublicImplementations.
