(** * RewriteAuditPlainCore3

    This module implements plain witness updates, tracked seeding, rebuilding, and rule steps.
    For example, merging witnesses at roots 1 and 2 removes those old root bindings first.
    Builds on: RewriteAuditPlainCore1 and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditPlainCore1
  RewriteAuditPlainCore2 RewriteAuditPlainPrimitives RewriteAuditProofCarrier
  RewriteAuditProofClosure RewriteAuditProofRun RewriteAuditProofSeed RewriteAuditProofTick
  RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_rw_rp_witness_merge {K Sort V} (a b root pointer : positive)
    (store : rw_class_witness_store K Sort V) : rw_class_witness_store K Sort V :=
  let first :=
    rw_plain_audit_map_remove rw_plain_audit_positive_encode a (rw_class_witness_roots store) in
  let second := rw_plain_audit_map_remove rw_plain_audit_positive_encode b first in
  let roots := rw_plain_audit_map_set rw_plain_audit_positive_encode root pointer second in
  RWClassWitnessStore (rw_class_witness_nodes store) roots.

Definition rw_plain_rw_rp_witness_read {K Sort V} (id : rw_id)
    (store : rw_class_witness_store K Sort V) : option (positive * rw_term K Sort V) :=
  let pointer :=
    rw_plain_audit_map_get rw_plain_audit_positive_encode id (rw_class_witness_roots store) in
  match pointer with
  | None => None
  | Some p =>
    let tree :=
      rw_plain_rw_shared_unfold_atomic (RwSharedTree K Sort V p (rw_class_witness_nodes store)) in
    option_map (fun t => (p, t)) tree
  end.

Definition rw_plain_rw_rp_connect_at_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (proof : rw_provenance K Sort V H)
    (lhs rhs : rw_term K Sort V) : option (rw_provenance K Sort V H * positive) :=
  let entries := rw_plain_audit_map_elements (rw_provenance_nodes proof) in
  let '(known, largest) := rw_plain_rw_rp_evidence_terms entries 0 in
  let lefts := rw_plain_rw_rp_subterms lhs in
  let rights := rw_plain_rw_rp_subterms rhs in
  let both := rw_plain_rw_rp_append lefts rights in
  let terms := rw_plain_rw_rp_append both known in
  let index :=
    rw_plain_rw_rp_index_existing op sort value (rw_provenance_ids proof) proof Map.empty in
  let count := rw_plain_rw_fuel_length terms in
  let square := rw_plain_rw_fuel_mul count count in
  let fuel := rw_plain_rw_fuel_to_positive square in
  let final := rw_plain_rw_rp_close_rounds op sort value stamp terms fuel
    (RwRpConnectionState proof index) in
  let lk := rw_plain_rw_rp_term_key op sort value lhs in
  let rk := rw_plain_rw_rp_term_key op sort value rhs in
  let answer := rw_plain_rw_rp_proof_get lk rk (rw_rp_index final) in
  option_map (fun id => (rw_rp_proof final, id)) answer.

Definition rw_plain_rw_rp_record_connection {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (lhs rhs : rw_term K Sort V)
    (proof : rw_provenance K Sort V H) : option (rw_provenance K Sort V H * positive) :=
  let connection := rw_plain_rw_rp_connect_at_atomic op sort value stamp proof lhs rhs in
  match connection with
  | None => None
  | Some (extended, id) =>
    let index :=
      rw_plain_rw_rp_index_existing op sort value (rw_provenance_ids extended) extended Map.empty in
    let state := RwRpConnectionState extended index in
    let '(refl, with_refl) :=
      rw_plain_rw_rp_add_evidence op sort value stamp rhs rhs RWEvidenceRefl state in
    let '(event_id, final) :=
      rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceTrans id refl) with_refl in
    Some (rw_rp_proof final, event_id)
  end.

Definition rw_plain_rw_rp_tick_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (state : rw_tracked_state K Sort V H) :
    option (rw_tracked_state K Sort V H * rw_index_event) :=
  let stepped := rw_plain_rw_ri_tick_atomic op sort value (rw_tracked_machine state) in
  match stepped with
  | None => None
  | Some (next, event) =>
    match event with
    | RWIndexCongruence pair_value a b root =>
      let store := rw_tracked_witnesses state in
      let lhs := rw_plain_rw_rp_witness_read a store in
      match lhs with
      | None => None
      | Some (left_pointer, left_term) =>
        let rhs := rw_plain_rw_rp_witness_read b store in
        match rhs with
        | None => None
        | Some (_, right_term) =>
          let recorded :=
            rw_plain_rw_rp_record_connection op sort value stamp left_term right_term
              (rw_tracked_provenance state) in
          match recorded with
          | None => None
          | Some (proof, id) =>
            let witnesses := rw_plain_rw_rp_witness_merge a b root left_pointer store in
            let events := rw_plain_rw_rp_stamp_put stamp id (rw_tracked_event_nodes state) in
            Some (RWTrackedState next proof witnesses events, event)
          end
        end
      end
    | _ =>
      Some (RWTrackedState next (rw_tracked_provenance state) (rw_tracked_witnesses state)
        (rw_tracked_event_nodes state), event)
    end
  end.

Definition rw_plain_rw_rp_seed_node {K Sort V} (node : rw_node K Sort V)
    (shared : rw_shared_node K Sort V) (acc : rw_rp_seed_acc K Sort V) :
    ((rw_id * positive) * rw_rp_seed_acc K Sort V) :=
  let id := rw_rp_seed_next acc in
  let pointer := rw_rp_seed_witness_next acc in
  let graph := rw_rp_seed_graph acc in
  let store := rw_rp_seed_witnesses acc in
  let aliases :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id id (rw_class_roots graph) in
  let sorts :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id (rw_node_sort node) (rw_sorts graph) in
  let nodes :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id (id, node) (rw_nodes graph) in
  let shared_nodes :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode pointer shared
      (rw_class_witness_nodes store) in
  let witness_roots :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id pointer
      (rw_class_witness_roots store) in
  let fresh := rw_plain_rw_fuel_pos_succ id in
  let witness_fresh := rw_plain_rw_fuel_pos_succ pointer in
  ((id, pointer), RwRpSeedAcc
    (RwGraph (id :: rw_roots graph) (id :: rw_nodes_in graph) aliases sorts nodes)
    (RWClassWitnessStore shared_nodes witness_roots) fresh witness_fresh).

Fixpoint rw_plain_rw_rp_seed_term {K Sort V} (term : rw_term K Sort V)
    (acc : rw_rp_seed_acc K Sort V) : ((rw_id * positive) * rw_rp_seed_acc K Sort V) :=
  match term with
  | RWVar ty v =>
    let out := rw_plain_rw_rp_seed_node (RWNVar ty v) (RWSharedVar K Sort V ty v) acc in
    out
  | RWApp ty op children =>
    let fix visit (ts : list (rw_term K Sort V)) (state : rw_rp_seed_acc K Sort V) :
        (list rw_id * list positive * rw_rp_seed_acc K Sort V) :=
      match ts with
      | nil => (nil, nil, state)
      | t :: rest =>
        let '((head, pointer), next) := rw_plain_rw_rp_seed_term t state in
        let '(tail, pointers, final) := visit rest next in
        (head :: tail, pointer :: pointers, final)
      end in
    let '(ids, pointers, next) := visit children acc in
    let out :=
      rw_plain_rw_rp_seed_node (RWNApp ty op ids) (RWSharedApp K Sort V ty op pointers) next in
    out
  end.

Definition rw_plain_rw_rp_seed_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (value : encoding V) (term : rw_term K Sort V) :
    (rw_id * rw_tracked_state K Sort V H) :=
  let '((root, _), acc) := rw_plain_rw_rp_seed_term term rw_rp_seed_empty in
  let machine := rw_plain_rw_ri_prepare_once op value (rw_rp_seed_graph acc) in
  (root, RWTrackedState machine (RWProvenance nil Map.empty) (rw_rp_seed_witnesses acc) Map.empty).

Definition rw_plain_rw_rp_rebuild_done {K Sort V H}
    (state : rw_tracked_state K Sort V H * nat * list rw_index_event) : bool :=
  let '(tracked, _, _) := state in
  match rw_index_dirty_order (rw_tracked_machine tracked),
    rw_pending_sequence (rw_index_pending (rw_tracked_machine tracked)) with
  | nil, nil => true
  | _, _ => false
  end.

Definition rw_plain_rw_rp_rebuild_once {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (group : nat)
    (state : rw_tracked_state K Sort V H * nat * list rw_index_event) :
    (rw_tracked_state K Sort V H * nat * list rw_index_event) :=
  let '(tracked, position, events) := state in
  let next := rw_plain_rw_rp_tick_atomic op sort value (group, S position) tracked in
  match next with
  | None => state
  | Some (final, event) => (final, S position, event :: events)
  end.

Fixpoint rw_plain_rw_rp_rebuild_repeat {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (group : nat) (fuel : positive)
    (state : rw_tracked_state K Sort V H * nat * list rw_index_event) :
    (rw_tracked_state K Sort V H * nat * list rw_index_event) :=
  if rw_plain_rw_rp_rebuild_done state then state
  else
    match fuel with
    | xH =>
      let out := rw_plain_rw_rp_rebuild_once op sort value group state in
      out
    | xO rest =>
      let middle := rw_plain_rw_rp_rebuild_repeat op sort value group rest state in
      let out := rw_plain_rw_rp_rebuild_repeat op sort value group rest middle in
      out
    | xI rest =>
      let first := rw_plain_rw_rp_rebuild_once op sort value group state in
      let middle := rw_plain_rw_rp_rebuild_repeat op sort value group rest first in
      let out := rw_plain_rw_rp_rebuild_repeat op sort value group rest middle in
      out
    end.

Fixpoint rw_plain_rw_ri_reverse_onto {A} (xs acc : list A) : list A :=
  match xs with
  | nil => acc
  | x :: rest =>
    let out := rw_plain_rw_ri_reverse_onto rest (x :: acc) in
    out
  end.

Definition rw_plain_rw_rp_rebuild_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (group : nat) (state : rw_tracked_state K Sort V H) :
    (rw_tracked_state K Sort V H * list rw_index_event) :=
  let fuel := rw_plain_rw_ri_rebuild_fuel_atomic (rw_tracked_machine state) in
  let '(final, _, reversed) :=
    rw_plain_rw_rp_rebuild_repeat op sort value group fuel (state, 0, nil) in
  let events := rw_plain_rw_ri_reverse_onto reversed nil in
  (final, events).

Definition rw_plain_rw_rp_rule_gate_atomic {K Sort V H} (sort : encoding Sort) (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (attempt : rw_attempt K Sort V H) : option (rw_term K Sort V * rw_term K Sort V) :=
  let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
  let out := rw_plain_rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  out.

Definition rw_plain_rw_rp_accept_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (stamp : nat * nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H)
    (lhs rhs : rw_term K Sort V) : option (rw_tracked_state K Sort V H) :=
  let graph := rw_plain_rw_ri_graph_atomic (rw_tracked_machine state) in
  let witness_entries :=
    rw_plain_audit_map_elements (rw_class_witness_nodes (rw_tracked_witnesses state)) in
  let largest := @rw_plain_rw_ri_max_entries_atomic (rw_shared_node K Sort V) K Sort V
    witness_entries (rw_index_fresh (rw_tracked_machine state)) in
  let fresh := rw_plain_rw_fuel_pos_succ largest in
  let acc := RwRpSeedAcc graph (rw_tracked_witnesses state)
    (rw_index_fresh (rw_tracked_machine state)) fresh in
  let '((rhs_root, _), grown) := rw_plain_rw_rp_seed_term rhs acc in
  let prepared := rw_plain_rw_ri_prepare_once op value (rw_rp_seed_graph grown) in
  let first := rw_plain_rw_ri_find_atomic prepared (rw_attempt_root attempt) in
  match first with
  | None => None
  | Some a =>
    let second := rw_plain_rw_ri_find_atomic prepared rhs_root in
    match second with
    | None => None
    | Some b =>
      let left_sort :=
        rw_plain_audit_map_get rw_plain_audit_positive_encode a
          (rw_sorts (rw_index_base prepared)) in
      match left_sort with
      | None => None
      | Some sa =>
        let right_sort :=
          rw_plain_audit_map_get rw_plain_audit_positive_encode b
            (rw_sorts (rw_index_base prepared)) in
        match right_sort with
        | None => None
        | Some sb =>
          let same_sort := rw_plain_rw_ri_encoded_equal sort sa sb in
          if same_sort then
            let old_witnesses := rw_rp_seed_witnesses grown in
            let pointer :=
              rw_plain_audit_map_get rw_plain_audit_positive_encode a
                (rw_class_witness_roots old_witnesses) in
            match pointer with
            | None => None
            | Some p =>
              let '(machine, merge_event) :=
                rw_plain_rw_ri_pair_merge_atomic prepared prepared (a, b)
                  (rw_index_pending prepared) a b nil in
              let root :=
                match merge_event with
                | RWIndexCongruence _ _ _ r => r
                | _ => a
                end in
              let witnesses := rw_plain_rw_rp_witness_merge a b root p old_witnesses in
              let proof := rw_tracked_provenance state in
              let index :=
                rw_plain_rw_rp_index_existing op sort value (rw_provenance_ids proof)
                  proof Map.empty in
              let '(id, extended) :=
                rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs
                  (RWEvidenceRule (rw_attempt_rule attempt) (rw_attempt_sub attempt))
                  (RwRpConnectionState proof index) in
              let events := rw_plain_rw_rp_stamp_put stamp id (rw_tracked_event_nodes state) in
              Some (RWTrackedState machine (rw_rp_proof extended) witnesses events)
            end
          else None
        end
      end
    end
  end.

Definition rw_plain_rw_rp_rule_step_prepared_atomic {K Sort V H} (EK : encoding K)
    (ES : encoding Sort) (EV : encoding V) (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (position : nat) (state : rw_tracked_state K Sort V H)
    (attempt : rw_attempt K Sort V H) : option (rw_tracked_state K Sort V H) :=
  let gate := rw_plain_rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  match gate with
  | None => None
  | Some (lhs, rhs) =>
    let represented :=
      rw_plain_rw_ri_member_atomic op sort value (rw_tracked_machine state) lhs
        (rw_attempt_root attempt) in
    if represented then
      let accepted :=
        rw_plain_rw_rp_accept_atomic EK ES EV op sort value (S position, 0) state attempt lhs rhs in
      accepted
    else None
  end.

Definition rw_plain_rw_rp_rule_step_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) :=
  let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
  let out :=
    rw_plain_rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks table position
      state attempt in
  out.

Definition rw_plain_rw_rp_apply_prepared_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H * list rw_index_event) :=
  let stepped :=
    rw_plain_rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks table position
      state attempt in
  match stepped with
  | None => None
  | Some next =>
    let out := rw_plain_rw_rp_rebuild_atomic op sort value (S position) next in
    Some out
  end.

Definition rw_plain_rw_rp_apply_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H * list rw_index_event) :=
  let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
  let out :=
    rw_plain_rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table position
      state attempt in
  out.

Definition rw_plain_rw_rp_run_once {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (strategy : rw_plain_strategy K Sort V H) (state : rw_rp_run_state K Sort V H) :
    rw_rp_run_state K Sort V H :=
  if rw_rp_stopped state then state
  else
    let tracked := rw_rp_current state in
    let offer := rw_plain_rw_rp_strategy_run op value strategy (rw_tracked_machine tracked) in
    match offer with
    | None => RwRpRunState tracked true (rw_rp_position state) (rw_rp_events state)
    | Some attempt =>
      let applied :=
        rw_plain_rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table
          (rw_rp_position state) tracked attempt in
      match applied with
      | None =>
        RwRpRunState tracked false (S (rw_rp_position state))
          (RWRunRejected attempt :: rw_rp_events state)
      | Some (next, events) =>
        RwRpRunState next false (S (rw_rp_position state))
          (RWRunAccepted attempt events :: rw_rp_events state)
      end
    end.
