(** * RewriteAuditProofApply

    Models tracked rule acceptance, application, and the work of rebuilding afterward.
    For example, a rejected prepared rule step makes prepared apply return None.
    Builds on: RewriteAuditIndexPair and
    RewriteAuditProofRebuild. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexFind RewriteAuditIndexMembership
  RewriteAuditIndexPair RewriteAuditIndexPrepare RewriteAuditIndexPrepareReference
  RewriteAuditIndexRebuild RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditProofCarrier RewriteAuditProofClosure RewriteAuditProofRebuild
  RewriteAuditProofSeed RewriteAuditProofTick RewriteAuditQueueReference
  RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rp_accept_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (stamp : nat * nat) (state : rw_tracked_state K Sort V H)
    (attempt : rw_attempt K Sort V H) (lhs rhs : rw_term K Sort V) :
    option (rw_tracked_state K Sort V H) * nat :=
  let '(graph, graph_work) := rw_ri_graph_atomic (rw_tracked_machine state) in
  let '(witness_entries, witness_enum) :=
    audit_map_elements (rw_class_witness_nodes (rw_tracked_witnesses state)) in
  let '(largest, max_trace) :=
    @rw_ri_max_entries_atomic (rw_shared_node K Sort V) K Sort V witness_entries
      (rw_index_fresh (rw_tracked_machine state)) in
  let '(fresh, fresh_trace) := rw_fuel_pos_succ largest in
  let fresh_work :=
    audit_elements_work witness_enum + rw_ri_fresh_trace_cost max_trace + audit_work fresh_trace in
  let acc :=
    RwRpSeedAcc graph (rw_tracked_witnesses state)
      (rw_index_fresh (rw_tracked_machine state)) fresh in
  let '(((rhs_root, _), grown), growth_work) := rw_rp_seed_term rhs acc in
  let '(prepared, prepare_trace) := rw_ri_prepare_once op value (rw_rp_seed_graph grown) in
  let prepare_work := rw_ri_prepare_once_work prepare_trace in
  let '(first, ft) := rw_ri_find_atomic prepared (rw_attempt_root attempt) in
  let prefix :=
    64 + graph_work + fresh_work + growth_work + prepare_work + rw_ri_find_trace_cost ft in
  match first with
  | None => (None, prefix)
  | Some a =>
    let '(second, st) := rw_ri_find_atomic prepared rhs_root in
    let prefix := prefix + rw_ri_find_trace_cost st in
    match second with
    | None => (None, prefix)
    | Some b =>
      let '(left_sort, lt) :=
        audit_map_get audit_positive_encode a (rw_sorts (rw_index_base prepared)) in
      let prefix := prefix + audit_map_source_work audit_basic_encoding_work lt in
      match left_sort with
      | None => (None, prefix)
      | Some sa =>
        let '(right_sort, rt) :=
          audit_map_get audit_positive_encode b (rw_sorts (rw_index_base prepared)) in
        let prefix := prefix + audit_map_source_work audit_basic_encoding_work rt in
        match right_sort with
        | None => (None, prefix)
        | Some sb =>
          let '(same_sort, sort_work) := rw_ri_encoded_equal sort sa sb in
          let prefix := prefix + sort_work in
          if same_sort then
            let old_witnesses := rw_rp_seed_witnesses grown in
            let '(pointer, pt) :=
              audit_map_get audit_positive_encode a (rw_class_witness_roots old_witnesses) in
            let prefix := prefix + audit_map_source_work audit_basic_encoding_work pt in
            match pointer with
            | None => (None, prefix)
            | Some p =>
              let '((machine, merge_event), merge_trace) :=
                rw_ri_pair_merge_atomic prepared prepared (a, b)
                  (rw_index_pending prepared) a b nil in
              let root :=
                match merge_event with
                | RWIndexCongruence _ _ _ r => r
                | _ => a
                end in
              let '(witnesses, witness_work) := rw_rp_witness_merge a b root p old_witnesses in
              let proof := rw_tracked_provenance state in
              let '(index, iw) :=
                rw_rp_index_existing op sort value (rw_provenance_ids proof) proof Map.empty in
              let '((id, extended), evidence_work) :=
                rw_rp_add_evidence op sort value stamp lhs rhs
                  (RWEvidenceRule (rw_attempt_rule attempt) (rw_attempt_sub attempt))
                  (RwRpConnectionState proof index) in
              let '(events, event_work) :=
                rw_rp_stamp_put stamp id (rw_tracked_event_nodes state) in
              (Some (RWTrackedState machine (rw_rp_proof extended) witnesses events),
                prefix + rw_ri_pair_trace_cost merge_trace + witness_work + iw +
                  evidence_work + event_work)
            end
          else (None, prefix)
        end
      end
    end
  end.

Definition rw_rp_rule_step_prepared_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) * nat :=
  let '(gate, gate_work) := rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  match gate with
  | None => (None, 64 + gate_work)
  | Some (lhs, rhs) =>
    let '(represented, member_work) :=
      rw_ri_member_atomic op sort value (rw_tracked_machine state) lhs (rw_attempt_root attempt) in
    if represented then
      let '(accepted, work) :=
        rw_rp_accept_atomic EK ES EV op sort value (S position, 0) state attempt lhs rhs in
      (accepted, 64 + gate_work + member_work + work)
    else (None, 64 + gate_work + member_work)
  end.

Definition rw_rp_rule_step_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) :=
    rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks table position
      state attempt in
  (out, 64 + preparation_work + work).

Definition rw_rp_apply_prepared_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H * list rw_index_event) * nat :=
  let '(stepped, step_work) :=
    rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks table position
      state attempt in
  match stepped with
  | None => (None, 64 + step_work)
  | Some next =>
    let '(out, work) := rw_rp_rebuild_atomic op sort value (S position) next in
    (Some out, 64 + step_work + work)
  end.

Definition rw_rp_apply_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H * list rw_index_event) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) :=
    rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table position
      state attempt in
  (out, 64 + preparation_work + work).
