(** * AnalysesAuditRewriteFacadeRun

    Relates facade apply, repeated runner steps, and captured legacy provenance to source work.
    For example, an already stopped runner stays stopped on the next iteration.
    Builds on: AnalysesAuditRewriteFacadePrepare and
    RewriteAuditProofRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeDimensions
  AnalysesAuditRewriteFacadeMaterialize AnalysesAuditRewriteFacadeOffers
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeReference.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofApply RewriteAuditProofCarrier
  RewriteAuditProofRebuild RewriteAuditProofRun RewriteAuditProofSeed RewriteAuditProofTick
  RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_facade_apply_atomic {K} (EK : encoding K) (op : rw_queue_encoder_adapter K) (guard :
    rw_facade_guard_adapter K) (prepared : rw_facade_prepared K) (position : nat) (state :
    rw_tracked_state K unit nat nat) (attempt : rw_attempt K unit nat nat) : option
    (rw_tracked_state K unit nat nat * list rw_index_event) * nat :=
  let '(found, lookup) := audit_map_get audit_nat_encode (rw_attempt_rule attempt)
    (rw_facade_rule_table prepared) in
  let prefix := 64 + audit_map_source_work audit_nat_events_work lookup in
  match found with
  | None => (None, prefix)
  | Some entry =>
    let '(gate, gate_work) := rw_rp_rule_body_gate_atomic rw_facade_unit_adapter
      rw_facade_nat_adapter
      (rw_facade_local_callbacks guard entry) (rw_facade_core_rule entry) attempt in
    match gate with
    | None => (None, prefix + gate_work)
    | Some (lhs, rhs) =>
      let '(represented, member_work) := rw_ri_member_atomic op rw_facade_unit_adapter
        rw_facade_nat_adapter (rw_tracked_machine state) lhs (rw_attempt_root attempt) in
      if represented then
        let '(accepted, acceptance_work) := rw_rp_accept_atomic EK unit_encoding nat_encoding
          op rw_facade_unit_adapter rw_facade_nat_adapter (S position, 0) state attempt lhs rhs in
        match accepted with
        | None => (None, prefix + gate_work + member_work + acceptance_work)
        | Some next =>
          let '(out, rebuild_work) := rw_rp_rebuild_atomic op rw_facade_unit_adapter
            rw_facade_nat_adapter (S position) next in
          (Some out, prefix + gate_work + member_work + acceptance_work + rebuild_work)
        end
      else (None, prefix + gate_work + member_work)
    end
  end.

(** One facade iteration relates its current and next runner states with source work
    and operand dimension. *)
Inductive rw_facade_once_run {K} (EK : encoding K) (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (prepared : rw_facade_prepared K) :
    rw_rp_run_state K unit nat nat -> rw_rp_run_state K unit nat nat -> nat -> nat -> Prop :=
  | RPFOnceAlreadyStopped : forall run,
      rw_rp_stopped run = true ->
      rw_facade_once_run EK op guard prepared run run 64 (rw_facade_runner_dimension run)
  | RPFOnceStop : forall run callback_work callback_dimension,
      rw_rp_stopped run = false ->
      rw_facade_strategy_run op guard prepared (rw_tracked_machine (rw_rp_current run)) None
        callback_work callback_dimension ->
      rw_facade_once_run EK op guard prepared run
        (RwRpRunState (rw_rp_current run) true (rw_rp_position run) (rw_rp_events run))
        (64 + callback_work)
        (rw_facade_once_dimension run
          (RwRpRunState (rw_rp_current run) true (rw_rp_position run) (rw_rp_events run))
          callback_dimension)
  | RPFOnceReject : forall run attempt callback_work callback_dimension application_work,
      rw_rp_stopped run = false ->
      rw_facade_strategy_run op guard prepared (rw_tracked_machine (rw_rp_current run))
        (Some attempt) callback_work callback_dimension ->
      rw_facade_apply_atomic EK op guard prepared (rw_rp_position run) (rw_rp_current run) attempt =
        (None, application_work) ->
      rw_facade_once_run EK op guard prepared run
        (RwRpRunState (rw_rp_current run) false (S (rw_rp_position run))
          (RWRunRejected attempt :: rw_rp_events run)) (64 + callback_work + application_work)
        (rw_facade_once_dimension run
          (RwRpRunState (rw_rp_current run) false (S (rw_rp_position run))
            (RWRunRejected attempt :: rw_rp_events run)) callback_dimension)
  | RPFOnceAccept : forall run attempt callback_work callback_dimension next events
      application_work,
      rw_rp_stopped run = false ->
      rw_facade_strategy_run op guard prepared (rw_tracked_machine (rw_rp_current run))
        (Some attempt) callback_work callback_dimension ->
      rw_facade_apply_atomic EK op guard prepared (rw_rp_position run) (rw_rp_current run) attempt =
        (Some (next, events), application_work) ->
      rw_facade_once_run EK op guard prepared run
        (RwRpRunState next false (S (rw_rp_position run))
          (RWRunAccepted attempt events :: rw_rp_events run))
        (64 + callback_work + application_work)
        (rw_facade_once_dimension run
          (RwRpRunState next false (S (rw_rp_position run))
            (RWRunAccepted attempt events :: rw_rp_events run)) callback_dimension).

(** Repeated facade iterations relate initial and final runner states under binary fuel,
    recording work and the maximum dimension. *)
Inductive rw_facade_repeat_run {K} (EK : encoding K) (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (prepared : rw_facade_prepared K) :
    positive -> rw_rp_run_state K unit nat nat -> rw_rp_run_state K unit nat nat -> nat -> nat ->
    Prop :=
  | RPFRepeatStopped : forall fuel run,
      rw_rp_stopped run = true ->
      rw_facade_repeat_run EK op guard prepared fuel run run 64 (rw_facade_runner_dimension run)
  | RPFRepeatOne : forall run out work dimension,
      rw_rp_stopped run = false ->
      rw_facade_once_run EK op guard prepared run out work dimension ->
      rw_facade_repeat_run EK op guard prepared xH run out (64 + work) dimension
  | RPFRepeatEven : forall fuel run middle out first second first_dimension second_dimension,
      rw_rp_stopped run = false ->
      rw_facade_repeat_run EK op guard prepared fuel run middle first first_dimension ->
      rw_facade_repeat_run EK op guard prepared fuel middle out second second_dimension ->
      rw_facade_repeat_run EK op guard prepared (xO fuel) run out (64 + first + second)
        (Nat.max first_dimension second_dimension)
  | RPFRepeatOdd : forall fuel run first middle out one left right one_dimension left_dimension
      right_dimension,
      rw_rp_stopped run = false ->
      rw_facade_once_run EK op guard prepared run first one one_dimension ->
      rw_facade_repeat_run EK op guard prepared fuel first middle left left_dimension ->
      rw_facade_repeat_run EK op guard prepared fuel middle out right right_dimension ->
      rw_facade_repeat_run EK op guard prepared (xI fuel) run out (64 + one + left + right)
        (Nat.max one_dimension (Nat.max left_dimension right_dimension)).

Fixpoint rw_facade_capture_entries {K} (entries : list (positive * rw_evidence_node K unit nat nat))
    (leaves : Map.t positive (rewrite_step K)) : Map.t positive (rewrite_step K) * nat :=
  match entries with
  | nil => (leaves, 64)
  | (id, node) :: rest =>
    let '(next, work) :=
      match rw_evidence_reason_of node with
      | RWEvidenceRule index bindings =>
        let '(sub, binding_work) := rw_facade_bindings_atomic bindings in
        let '(out, trace) := audit_map_set audit_positive_encode id
          (RewriteStep nil index true sub) leaves in
        (out, 64 + binding_work + audit_map_source_work audit_basic_encoding_work trace)
      | _ => (leaves, 64)
      end in
    let '(out, tail_work) := rw_facade_capture_entries rest next in
    (out, 64 + work + tail_work)
  end.

Definition rw_facade_capture_atomic {K} (output : rw_tracked_output K unit nat nat) : Map.t positive
    (rewrite_step K) * nat :=
  let '(entries, trace) := audit_map_elements
    (rw_provenance_nodes (rw_tracked_provenance (rw_tracked_final output))) in
  let '(leaves, work) := rw_facade_capture_entries entries Map.empty in
  (leaves, 64 + audit_elements_work trace + work).

Record rw_legacy_tracked_state (K : Type) := RWLegacyTrackedState {
  rw_legacy_root : rw_id;
  rw_legacy_core : rw_tracked_output K unit nat nat;
  rw_legacy_leaves : Map.t positive (rewrite_step K)
}.

(** A tracked facade run relates a seed and positive fuel to the legacy tracked result,
    work, and dimension. *)
Inductive rw_facade_tracked_run {K} (EK : encoding K) (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (rules : list (rewrite_rule K))
    (fuel : positive) (seed : term K) : rw_legacy_tracked_state K -> nat -> nat -> Prop :=
  | RPFTrackedRun : forall prepared preparation_work source embedding_trace root initial seed_work
      ready initial_events initial_work final run_work run_dimension output leaves capture_work,
      rw_facade_prepare_atomic rules 0 = (prepared, preparation_work) ->
      rw_facade_embed_atomic seed = (source, embedding_trace) ->
      rw_rp_seed_atomic EK unit_encoding nat_encoding op rw_facade_nat_adapter source =
        ((root, initial), seed_work) ->
      rw_rp_rebuild_atomic op rw_facade_unit_adapter rw_facade_nat_adapter 0 initial =
        ((ready, initial_events), initial_work) ->
      rw_facade_repeat_run EK op guard prepared fuel (RwRpRunState ready false 0 nil)
        final run_work run_dimension ->
      output = RwTrackedOutput (rw_rp_current final)
        (if rw_rp_stopped final then RWStopped else RWFuelExhausted)
        initial_events (rw_rp_events final) ->
      rw_facade_capture_atomic output = (leaves, capture_work) ->
      rw_facade_tracked_run EK op guard rules fuel seed (RWLegacyTrackedState K root output leaves)
        (64 + preparation_work + 64 * audit_work embedding_trace + seed_work + initial_work +
          run_work + capture_work)
        (S (rw_facade_prepared_dimension prepared + rw_facade_term_dimension seed +
          rw_facade_tracked_dimension initial + rw_facade_tracked_dimension ready +
          rw_facade_tracked_dimension (rw_rp_current final) + run_dimension +
          rw_facade_leaves_dimension leaves)).
