(** * RewriteAuditProofInterfaceTrackedTickProjectionContract

    States the prospective projection and phase-validity contract for tracked ticks.
    For example, given a valid phase and fresh stamp (0, 1), a None tracked tick requires a None
    index tick.
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

(** For a valid tracked phase and fresh stamp, a tracked tick projects to the index
    tick and preserves phase validity on success. *)
Definition rw_tracked_tick_projection_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules stamp (state : rw_tracked_state K Sort V H),
    rw_tracked_phase_valid EK ES EV EH sig rules state -> rw_tracked_stamp_fresh stamp state ->
    match rw_tracked_tick EK ES EV stamp state with
    | None => rw_index_tick EK ES EV (rw_tracked_machine state) = None
    | Some (next, event) =>
      rw_index_tick EK ES EV (rw_tracked_machine state) = Some (rw_tracked_machine next, event) /\
      rw_tracked_phase_valid EK ES EV EH sig rules next
    end.

End FuturePublicImplementations.
