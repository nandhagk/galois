(** * RewriteAuditProofTick

    Models tracked witness lookup, provenance updates, and congruence ticks.
    For example, merging roots 1 and 2 removes both entries before recording the new root.
    Builds on: RewriteAuditProofClosure and
    RewriteAuditIndexRebuild. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRebuild RewriteAuditIndexReference
  RewriteAuditProofCarrier RewriteAuditProofClosure RewriteAuditQueueReference
  RewriteAuditSharedReference.
Import List.ListNotations.

Record rw_class_witness_store (K Sort V : Type) := RWClassWitnessStore {
  rw_class_witness_nodes : Map.t positive (rw_shared_node K Sort V);
  rw_class_witness_roots : Map.t rw_id positive
}.
Arguments RWClassWitnessStore {K Sort V}.
Arguments rw_class_witness_nodes {K Sort V}.
Arguments rw_class_witness_roots {K Sort V}.

Record rw_tracked_state (K Sort V H : Type) := RWTrackedState {
  rw_tracked_machine : rw_index_state K Sort V;
  rw_tracked_provenance : rw_provenance K Sort V H;
  rw_tracked_witnesses : rw_class_witness_store K Sort V;
  rw_tracked_event_nodes : Map.t (nat * nat) positive
}.
Arguments RWTrackedState {K Sort V H}.
Arguments rw_tracked_machine {K Sort V H}.
Arguments rw_tracked_provenance {K Sort V H}.
Arguments rw_tracked_witnesses {K Sort V H}.
Arguments rw_tracked_event_nodes {K Sort V H}.

Definition rw_rp_stamp_encode :=
  audit_pair_encode audit_nat_encode audit_nat_encode.

Definition rw_rp_stamp_work (trace : list (audit_pair_event nat nat audit_nat_encoding_event
    audit_nat_encoding_event)) : nat :=
  audit_pair_events_work audit_nat_events_work audit_nat_events_work trace.

Definition rw_rp_stamp_put (stamp : nat * nat) (id : positive)
    (table : Map.t (nat * nat) positive) : Map.t (nat * nat) positive * nat :=
  let '(out, trace) := audit_map_set rw_rp_stamp_encode stamp id table in
  (out, 64 + audit_map_source_work rw_rp_stamp_work trace).

Definition rw_rp_witness_merge {K Sort V} (a b root pointer : positive) (store :
    rw_class_witness_store K Sort V) : rw_class_witness_store K Sort V * nat :=
  let '(first, ft) := audit_map_remove audit_positive_encode a
    (rw_class_witness_roots store) in
  let '(second, st) := audit_map_remove audit_positive_encode b first in
  let '(roots, rt) := audit_map_set audit_positive_encode root pointer second in
  (RWClassWitnessStore (rw_class_witness_nodes store) roots,
    64 + audit_map_source_work audit_basic_encoding_work ft +
      audit_map_source_work audit_basic_encoding_work st +
      audit_map_source_work audit_basic_encoding_work rt).

Definition rw_rp_witness_read {K Sort V} (id : rw_id) (store : rw_class_witness_store K Sort V) :
    option (positive * rw_term K Sort V) * nat :=
  let '(pointer, trace) := audit_map_get audit_positive_encode id (rw_class_witness_roots store) in
  let read_work := audit_map_source_work audit_basic_encoding_work trace in
  match pointer with
  | None => (None, 64 + read_work)
  | Some p =>
    let '(tree, unfold_trace) := rw_shared_unfold_atomic
      (RwSharedTree K Sort V p (rw_class_witness_nodes store)) in
    (option_map (fun t => (p, t)) tree,
      64 + read_work + rw_shared_unfold_trace_cost unfold_trace)
  end.

Definition rw_rp_restate {K Sort V H} (old : rw_tracked_state K Sort V H) (machine : rw_index_state
    K Sort V) (proof : rw_provenance K Sort V H) (witnesses : rw_class_witness_store K Sort V)
    (events : Map.t (nat * nat) positive) : rw_tracked_state K Sort V H :=
  RWTrackedState machine proof witnesses events.

Definition rw_rp_connect_at_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (proof : rw_provenance K Sort V H) (lhs rhs : rw_term K Sort V) :
    option (rw_provenance K Sort V H * positive) * nat :=
  let '(entries, et) := audit_map_elements (rw_provenance_nodes proof) in
  let '((known, largest), kw) := rw_rp_evidence_terms entries 0 in
  let '(lefts, lw) := rw_rp_subterms lhs in
  let '(rights, rw) := rw_rp_subterms rhs in
  let '(both, bw) := rw_rp_append lefts rights in
  let '(terms, aw) := rw_rp_append both known in
  let '(index, iw) :=
    rw_rp_index_existing op sort value (rw_provenance_ids proof) proof Map.empty in
  let '(count, lt) := rw_fuel_length terms in
  let '(square, mt) := rw_fuel_mul count count in
  let '(fuel, ft) := rw_fuel_to_positive square in
  let '(final, work) :=
    rw_rp_close_rounds op sort value stamp terms fuel (RwRpConnectionState proof index) in
  let '(lk, lkw) := rw_rp_term_key op sort value lhs in
  let '(rk, rkw) := rw_rp_term_key op sort value rhs in
  let '(answer, qw) := rw_rp_proof_get lk rk (rw_rp_index final) in
  (option_map (fun id => (rw_rp_proof final, id)) answer,
    64 + audit_elements_work et + kw + lw + rw + bw + aw + iw +
      audit_work lt + audit_work mt + audit_work ft + work + lkw + rkw + qw).

Definition rw_rp_record_connection {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (lhs rhs : rw_term K Sort V) (proof : rw_provenance K Sort V H) :
    option (rw_provenance K Sort V H * positive) * nat :=
  let '(connection, connection_work) :=
    rw_rp_connect_at_atomic op sort value stamp proof lhs rhs in
  match connection with
  | None => (None, 64 + connection_work)
  | Some (extended, id) =>
    let '(index, iw) :=
      rw_rp_index_existing op sort value (rw_provenance_ids extended) extended Map.empty in
    let state := RwRpConnectionState extended index in
    let '((refl, with_refl), rw) :=
      rw_rp_add_evidence op sort value stamp rhs rhs RWEvidenceRefl state in
    let '((event_id, final), fw) :=
      rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceTrans id refl) with_refl in
    (Some (rw_rp_proof final, event_id), 64 + connection_work + iw + rw + fw)
  end.

Definition rw_rp_tick_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (state : rw_tracked_state K Sort V H) :
    option (rw_tracked_state K Sort V H * rw_index_event) * nat :=
  let '(stepped, trace) :=
    rw_ri_tick_atomic op sort value (rw_tracked_machine state) in
  let step_work := rw_ri_tick_trace_cost trace in
  match stepped with
  | None => (None, 64 + step_work)
  | Some (next, event) =>
    match event with
    | RWIndexCongruence pair_value a b root =>
      let store := rw_tracked_witnesses state in
      let '(lhs, lw) := rw_rp_witness_read a store in
      match lhs with
      | None => (None, 64 + step_work + lw)
      | Some (left_pointer, left_term) =>
        let '(rhs, rw) := rw_rp_witness_read b store in
        match rhs with
        | None => (None, 64 + step_work + lw + rw)
        | Some (_, right_term) =>
          let '(recorded, record_work) :=
            rw_rp_record_connection op sort value stamp left_term right_term
              (rw_tracked_provenance state) in
          match recorded with
          | None => (None, 64 + step_work + lw + rw + record_work)
          | Some (proof, id) =>
            let '(witnesses, witness_work) := rw_rp_witness_merge a b root left_pointer store in
            let '(events, event_work) := rw_rp_stamp_put stamp id (rw_tracked_event_nodes state) in
            (Some (RWTrackedState next proof witnesses events, event),
              64 + step_work + lw + rw + record_work + witness_work + event_work)
          end
        end
      end
    | _ =>
      (Some (RWTrackedState next (rw_tracked_provenance state)
               (rw_tracked_witnesses state) (rw_tracked_event_nodes state), event), 64 + step_work)
    end
  end.

(** A source tick returning congruence has readable pre-state witnesses and records
    their endpoints in the node indexed by the tick stamp. *)
Definition rw_rp_tick_captures_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) stamp (state next : rw_tracked_state K Sort V H)
    pair_value a b root work,
    rw_rp_tick_atomic op sort value stamp state =
      (Some (next, RWIndexCongruence pair_value a b root), work) ->
    exists left_pointer lhs right_pointer rhs id node,
      fst (rw_rp_witness_read a (rw_tracked_witnesses state)) = Some (left_pointer, lhs) /\
      fst (rw_rp_witness_read b (rw_tracked_witnesses state)) = Some (right_pointer, rhs) /\
      Map.get (pair_encoding nat_encoding nat_encoding) stamp (rw_tracked_event_nodes next) =
        Some id /\
      Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) = Some node /\
      rw_evidence_left node = lhs /\
      rw_evidence_right node = rhs /\
      rw_evidence_time node = stamp.
