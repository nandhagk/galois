(** * RewriteAuditProofInterfaceTrackedApplyProjectsContract

    This module states the prospective projection and evidence contract for tracked apply.
    For example, with well-formed rules, a valid phase, and fresh stamp (1, 0), success at
    position zero is required to record the applied rule at that stamp.
    Builds on: RewriteAuditIndexReference and
    RewriteAuditProofSemantic. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference
  RewriteAuditIndexTickReference RewriteAuditProofCarrier
  RewriteAuditProofInterfaceTrackedPhaseValid RewriteAuditProofPlainPublic
  RewriteAuditProofRepresentation RewriteAuditProofSemantic RewriteAuditProofTick
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).

Variable rw_connect_class : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.

(** A valid tracked phase combines index, provenance, class witness, and class connection
    invariants. *)
Let rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\
    rw_provenance_valid EH sig rules proof /\
    rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
    rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
      (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

(** For well-formed rules, a valid tracked phase, and a fresh stamp, apply projects to
    index apply; success preserves phase validity and records the stamped rule evidence. *)
Definition rw_tracked_apply_projects_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H)) position
    (state : rw_tracked_state K Sort V H) attempt,
    Forall (rw_rule_wf sig) rules ->
    rw_tracked_phase_valid EK ES EV EH sig rules state ->
    rw_tracked_stamp_fresh (S position, 0) state ->
    match rw_tracked_apply EK ES EV EH sig rules position state attempt with
    | None => rw_index_apply EK ES EV EH sig rules (rw_tracked_machine state) attempt = None
    | Some (next, events) =>
      rw_index_apply EK ES EV EH sig rules (rw_tracked_machine state) attempt =
        Some (rw_tracked_machine next, events) /\
      rw_tracked_phase_valid EK ES EV EH sig rules next /\
      exists id node,
        Map.get (pair_encoding nat_encoding nat_encoding) (S position, 0)
          (rw_tracked_event_nodes next) = Some id /\
        Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) =
          Some node /\
        rw_evidence_time node = (S position, 0) /\
        rw_evidence_reason_of node =
          RWEvidenceRule (rw_attempt_rule attempt) (rw_attempt_sub attempt)
    end.

End FuturePublicImplementations.
