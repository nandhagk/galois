(** * RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract

    States a prospective trace, phase-validity, and projection contract for tracked rebuild.
    For example, with a valid phase and fresh stamp (0, 1), group 0 must yield an index-aligned
    rebuild trace.
    Builds on: RewriteAuditIndexTickReference and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexTickReference
  RewriteAuditProofCarrier RewriteAuditProofInterfaceTrackedPhaseValid
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).

Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

(** A valid tracked phase combines index, provenance, class witness, and class connection
    invariants. *)
Let rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\ rw_provenance_valid EH sig rules proof /\
  rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
  rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
    (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.

(** A valid tracked phase and fresh initial stamp yield a valid final phase, a tracked
    rebuild trace, and the same machine and events as index rebuild. *)
Definition rw_tracked_rebuild_trace_correct_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules group (state : rw_tracked_state K Sort V H),
    rw_tracked_phase_valid EK ES EV EH sig rules state -> rw_tracked_stamp_fresh (group, 1) state ->
    let '(final, events) := rw_tracked_rebuild EK ES EV group state in
    rw_tracked_rebuild_trace (rw_tracked_tick EK ES EV) group 0 state events final /\
    rw_tracked_phase_valid EK ES EV EH sig rules final /\
    rw_index_rebuild EK ES EV (rw_tracked_machine state) = (rw_tracked_machine final, events).

End FuturePublicImplementations.
