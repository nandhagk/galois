(** * RewriteAuditProofInterfaceTrackedRunInvariantsContract

    This module states invariant requirements for a tracked run interface.
    For example, its contract requires a clean final graph at fuel 1 when the rules
    are sound and well formed and the seed is typed.
    Builds on: RewriteAuditProofRun and
    RewriteAuditProofSemantic. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofRun
  RewriteAuditProofSemantic RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},
    encoding K -> encoding Sort -> encoding V -> encoding H ->
    rw_signature K Sort V -> list (rw_rule K Sort V H) ->
    (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->
    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

Variable rw_connect_class : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).

(** For sound, well-formed rules and a typed seed, the final graph is well formed, sound,
    productive, and represents the seed; final provenance, witnesses, connections, and event
    indices are valid, and nonzero fuel yields a clean graph. *)
Definition rw_tracked_run_invariants_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    forall seed, rw_typed sig seed -> forall strategy fuel,
      let '(root, result) := rw_tracked_run EK ES EV EH sig rules strategy fuel seed in
      let state := rw_tracked_final result in
      let g := rw_tracked_graph state in
      let proof := rw_tracked_provenance state in
      let witnesses := rw_tracked_witnesses state in
      rw_graph_wf sig g /\ rw_graph_sound sig admissible rules g /\ rw_productive g /\
      rw_represents g root seed /\ (fuel <> 0%N -> rw_clean g) /\
      rw_provenance_valid EH sig rules proof /\ rw_class_witnesses_valid g witnesses /\
      rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
        (rw_connect_class EK ES EV EH) g witnesses proof /\
      rw_tracked_event_index_valid state (rw_tracked_initial result) (rw_tracked_events result) /\
      rw_tracked_rule_nodes_covered state (rw_tracked_events result).

End FuturePublicImplementations.
