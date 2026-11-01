(** * AnalysesAuditRewriteFacadePlainRun

    This file builds legacy offers and runs a plain tracked optimization strategy.
    For example, an empty hole list produces an empty binding map.
    Builds on: the fixed Rewrite plain builders and legacy facade source equations. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia Wellfounded.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadePlainHelpers
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditIndexMatchReference RewriteAuditIndexReference
  RewriteAuditPlainCore1 RewriteAuditPlainCore3 RewriteAuditPlainPrimitives RewriteAuditProofRun
  RewriteAuditProofTick RewriteAuditSharedExtract RewriteAuditSharedPlain
  RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rw_plain_facade_make_bindings {K} (graph : rw_graph K unit nat) (table : rw_rd_table)
    (store : rw_rd_store K unit nat) (holes : list nat) (assignment : rw_assignment nat) : option
    (Map.t nat (rw_term K unit nat)) :=
  match holes with
  | nil => Some Map.empty
  | hole :: rest =>
    let tail := rw_plain_facade_make_bindings graph table store rest assignment in
    match tail with
    | None => None
    | Some bindings =>
      let found := Map.get nat_encoding hole assignment in
      let observed :=
        match found with
        | None => Some (RWVar tt hole)
        | Some root =>
          match rd_plain_candidate_get graph table root with
          | None => None
          | Some candidate =>
            rw_shared_unfold (RwSharedTree K unit nat (rw_rd_pointer candidate) (rw_rd_nodes store))
          end
        end in
      match observed with
      | None => None
      | Some term => Some (Map.set nat_encoding hole term bindings)
      end
    end
  end.

Definition rw_plain_facade_rule_offers {K} (EK : encoding K) (state : rw_index_state K unit nat)
    (graph : rw_graph K unit nat) (table : rw_rd_table) (store : rw_rd_store K unit nat) (entry :
    nat * rw_facade_prepared_rule K) : list (rw_attempt K unit nat nat) :=
  let '(index, prepared) := entry in
  let rule := rw_facade_core_rule prepared in
  flat_map (fun root =>
    let assignments := rw_view_match EK unit_encoding nat_encoding nat_encoding
      (rw_snapshot_base (rw_index_view EK unit_encoding nat_encoding state)) root (rw_lhs rule) in
    flat_map (fun assignment =>
      match rw_plain_facade_make_bindings graph table store (rw_holes rule) assignment with
      | None => nil
      | Some bindings => [RwAttempt index root bindings]
      end) assignments) (rw_roots graph).

Definition rw_plain_facade_offer_gate {K} (EK : encoding K) (prepared : rw_facade_prepared K)
    (attempt : rw_attempt K unit nat nat) : bool :=
  match Map.get nat_encoding (rw_attempt_rule attempt) (rw_facade_rule_table prepared) with
  | None => false
  | Some entry =>
    let gate := rw_plain_rw_rp_rule_body_gate_atomic unit_encoding nat_encoding
      (rw_plain_rw_facade_local_callbacks tt entry) (rw_facade_core_rule entry) attempt in
    match gate with
    | None => false
    | Some (lhs, rhs) =>
      let left_legacy := rw_plain_rw_facade_materialize_project_atomic lhs in
      let right_legacy := rw_plain_rw_facade_materialize_project_atomic rhs in
      let bindings := rw_plain_rw_facade_bindings_atomic (rw_attempt_sub attempt) in
      match legacy_replay_step EK
        (fun index => Map.get nat_encoding index (rw_facade_original_table prepared)) left_legacy
        (RewriteStep nil (rw_attempt_rule attempt) true bindings) with
      | None => false
      | Some actual => term_eqb EK actual right_legacy
      end
    end
  end.

Fixpoint rw_plain_facade_choose {K} (EK : encoding K) (prepared : rw_facade_prepared K) (offers :
    list (rw_attempt K unit nat nat)) : option (rw_attempt K unit nat nat) :=
  match offers with
  | nil => None
  | attempt :: rest =>
    if rw_plain_facade_offer_gate EK prepared attempt then Some attempt
    else rw_plain_facade_choose EK prepared rest
  end.

Definition rw_plain_facade_strategy (Hwf : rw_rd_plain_compare_well_founded_type) {K} (EK : encoding
    K) (prepared : rw_facade_prepared K) (state : rw_index_state K unit nat) : option (rw_attempt K
    unit nat nat) :=
  let graph := rw_index_graph state in
  let fresh := rw_plain_rw_ri_prepare_once EK nat_encoding graph in
  match length (rw_roots graph) with
  | 0 => None
  | S count =>
    let entries := Map.elements (rw_nodes graph) in
    let '(table, store) := rd_plain_rounds Hwf EK unit_encoding nat_encoding
      (fun _ => 0) (fun _ => 0) graph entries (rd_plain_nat_positive count) Map.empty
      (RwRdStore Map.empty 1%positive) in
    let offers := flat_map (rw_plain_facade_rule_offers EK fresh graph table store)
      (rw_facade_rule_entries prepared) in
    rw_plain_facade_choose EK prepared offers
  end.

Definition rw_plain_facade_once (Hwf : rw_rd_plain_compare_well_founded_type) {K} (EK : encoding K)
    (prepared : rw_facade_prepared K) (run : rw_rp_run_state K unit nat nat) : rw_rp_run_state K
    unit nat nat :=
  if rw_rp_stopped run then run
  else
    let tracked := rw_rp_current run in
    match rw_plain_facade_strategy Hwf EK prepared (rw_tracked_machine tracked) with
    | None => RwRpRunState tracked true (rw_rp_position run) (rw_rp_events run)
    | Some attempt =>
      match rw_plain_rw_facade_apply_atomic EK EK tt prepared (rw_rp_position run) tracked
        attempt with
      | None => RwRpRunState tracked false (S (rw_rp_position run))
        (RWRunRejected attempt :: rw_rp_events run)
      | Some (next, events) => RwRpRunState next false (S (rw_rp_position run))
        (RWRunAccepted attempt events :: rw_rp_events run)
      end
    end.

Fixpoint rw_plain_facade_repeat (Hwf : rw_rd_plain_compare_well_founded_type) {K} (EK : encoding K)
    (prepared : rw_facade_prepared K) (fuel : positive) (run : rw_rp_run_state K unit nat nat) :
    rw_rp_run_state K unit nat nat :=
  if rw_rp_stopped run then run
  else
    match fuel with
    | xH => rw_plain_facade_once Hwf EK prepared run
    | xO rest =>
      let middle := rw_plain_facade_repeat Hwf EK prepared rest run in
      rw_plain_facade_repeat Hwf EK prepared rest middle
    | xI rest =>
      let first := rw_plain_facade_once Hwf EK prepared run in
      let middle := rw_plain_facade_repeat Hwf EK prepared rest first in
      rw_plain_facade_repeat Hwf EK prepared rest middle
    end.

Definition rw_legacy_tracked_builder (Hwf : rw_rd_plain_compare_well_founded_type) (K : Type) (EK :
    encoding K) (rules : list (rewrite_rule K)) (fuel : positive) (seed : term K) :
    rw_legacy_tracked_state K :=
  let prepared := rw_plain_rw_facade_prepare_atomic rules 0 in
  let source := legacy_embed seed in
  let '(root, initial) := @rw_plain_rw_rp_seed_atomic K unit nat nat
    EK unit_encoding nat_encoding EK nat_encoding source in
  let '(ready, initial_events) := rw_plain_rw_rp_rebuild_atomic EK unit_encoding nat_encoding
    0 initial in
  let final := rw_plain_facade_repeat Hwf EK prepared fuel (RwRpRunState ready false 0 nil) in
  let output := RwTrackedOutput (rw_rp_current final)
    (if rw_rp_stopped final then RWStopped else RWFuelExhausted) initial_events
    (rw_rp_events final) in
  let leaves := rw_plain_rw_facade_capture_atomic output in
  RWLegacyTrackedState K root output leaves.
