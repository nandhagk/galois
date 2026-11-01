(** * AnalysesAuditRewriteFacadeDimensions

    Measures the size of legacy terms, rules, index states, evidence, and facade operands.
    For example, the legacy variable with index 2 has term dimension 3.
    Builds on: AnalysesEgraph and
    RewriteAuditIndexDimensions. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadePrepare.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexReference
  RewriteAuditProofCarrier RewriteAuditProofDimensions RewriteAuditProofRun
  RewriteAuditProofTick RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Fixpoint rw_facade_term_dimension {K} (value : term K) : nat :=
  match value with
  | TVar index => S index
  | TApp _ children =>
    S ((fix visit (terms : list (term K)) : nat :=
      match terms with
      | nil => 1
      | term :: rest => S (rw_facade_term_dimension term + visit rest)
      end) children)
  end.

Definition rw_facade_rule_dimension {K} (rule : rewrite_rule K) : nat :=
  S (rw_facade_term_dimension (rule_lhs rule) + rw_facade_term_dimension (rule_rhs rule)).

Fixpoint rw_facade_core_dimension {K} (value : rw_term K unit nat) : nat :=
  match value with
  | RWVar _ index => S index
  | RWApp _ _ children =>
    S ((fix visit (terms : list (rw_term K unit nat)) : nat :=
      match terms with
      | nil => 1
      | term :: rest => S (rw_facade_core_dimension term + visit rest)
      end) children)
  end.

Definition rw_facade_node_dimension {K} (node : rw_node K unit nat) : nat :=
  match node with
  | RWNVar _ index => S index
  | RWNApp _ _ children => S (rw_whole_ids_dimension children)
  end.

Definition rw_facade_graph_dimension {K} (graph : rw_graph K unit nat) : nat :=
  S (rw_whole_graph_dimension graph +
    rw_whole_map_dimension Pos.size_nat
      (fun entry => Pos.size_nat (fst entry) + rw_facade_node_dimension (snd entry))
      (rw_nodes graph)).

Definition rw_facade_index_dimension {K} (state : rw_index_state K unit nat) : nat :=
  S (rw_whole_index_dimension state + rw_facade_graph_dimension (rw_index_base state) +
    rw_whole_map_dimension (fun index => S index) rw_whole_set_dimension
      (rw_index_variables state) +
    rw_whole_map_dimension rw_facade_node_dimension rw_whole_set_dimension
      (rw_index_signatures state) +
    rw_whole_map_dimension Pos.size_nat rw_facade_node_dimension (rw_index_node_keys state)).

Definition rw_facade_reason_dimension {K} (reason : rw_evidence_reason K unit nat nat) : nat :=
  match reason with
  | RWEvidenceRule index bindings => S (index +
      rw_whole_map_dimension (fun hole => S hole) rw_facade_core_dimension bindings)
  | _ => rw_whole_reason_dimension reason
  end.

Definition rw_facade_proof_dimension {K} (proof : rw_provenance K unit nat nat) : nat :=
  S (rw_whole_ids_dimension (rw_provenance_ids proof) +
    rw_whole_map_dimension Pos.size_nat (fun node =>
      rw_facade_core_dimension (rw_evidence_left node) +
      rw_facade_core_dimension (rw_evidence_right node) +
      rw_facade_reason_dimension (rw_evidence_reason_of node) +
      fst (rw_evidence_time node) + snd (rw_evidence_time node)) (rw_provenance_nodes proof)).

Definition rw_facade_witness_dimension {K} (store : rw_class_witness_store K unit nat) : nat :=
  let nodes := rw_class_witness_nodes store in
  S (rw_whole_map_dimension Pos.size_nat (fun node =>
      match node with
      | RWSharedVar _ _ _ _ index => S index
      | RWSharedApp _ _ _ _ _ children => S (rw_whole_ids_dimension children)
      end) nodes +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (rw_class_witness_roots store) +
    fold_right (fun entry total =>
      match rw_shared_unfold (RwSharedTree K unit nat (fst entry) nodes) with
      | None => S total
      | Some term => S (rw_facade_core_dimension term + total)
      end) 1 (Map.elements nodes)).

Definition rw_facade_tracked_dimension {K} (state : rw_tracked_state K unit nat nat) : nat :=
  S (rw_facade_index_dimension (rw_tracked_machine state) +
    rw_facade_proof_dimension (rw_tracked_provenance state) +
    rw_facade_witness_dimension (rw_tracked_witnesses state) +
    rw_whole_map_dimension (fun stamp => S (fst stamp + snd stamp)) Pos.size_nat
      (rw_tracked_event_nodes state)).

Definition rw_facade_prepared_dimension {K} (prepared : rw_facade_prepared K) : nat :=
  S (rw_whole_rules_dimension (rw_facade_core_rules prepared) +
    rw_whole_map_dimension (fun index => S index) (fun entry =>
      rw_facade_rule_dimension (rw_facade_original_rule entry) +
      rw_whole_map_dimension (fun index => S index) (fun _ => 1) (rw_facade_hole_set entry))
      (rw_facade_rule_table prepared) +
    rw_whole_map_dimension (fun index => S index) rw_facade_rule_dimension
      (rw_facade_original_table prepared)).

Definition rw_facade_attempt_dimension {K} (attempt : rw_attempt K unit nat nat) : nat :=
  S (rw_attempt_rule attempt + Pos.size_nat (rw_attempt_root attempt) +
    rw_whole_map_dimension (fun index => S index) rw_facade_core_dimension
      (rw_attempt_sub attempt)).

Definition rw_facade_offers_dimension {K} (offers : list (rw_attempt K unit nat nat)) : nat :=
  fold_right (fun attempt total => S (rw_facade_attempt_dimension attempt + total)) 1 offers.

Definition rw_facade_N_dimension (number : N) : nat :=
  match number with
  | N0 => 1
  | Npos value => Pos.size_nat value
  end.

Definition rw_facade_dp_dimension {K} (table : rw_rd_table) (store : rw_rd_store K unit nat) : nat
    :=
  S (rw_whole_map_dimension Pos.size_nat (fun candidate =>
      Pos.size_nat (rw_rd_pointer candidate) + rw_facade_N_dimension (rw_rd_cost candidate) +
      rw_facade_N_dimension (rw_rd_size candidate)) table +
    rw_whole_map_dimension Pos.size_nat (fun node =>
      match node with
      | RWSharedVar _ _ _ _ index => S index
      | RWSharedApp _ _ _ _ _ children => S (rw_whole_ids_dimension children)
      end) (rw_rd_nodes store) + Pos.size_nat (rw_rd_next store)).

Definition rw_facade_strategy_dimension {K} (prepared : rw_facade_prepared K) (state :
    rw_index_state K unit nat) (graph : rw_graph K unit nat) (fresh : rw_index_state K unit nat)
    (table : rw_rd_table) (store : rw_rd_store K unit nat) (offers : list (rw_attempt K unit nat
    nat)) : nat :=
  S (rw_facade_prepared_dimension prepared + rw_facade_index_dimension state +
    rw_facade_graph_dimension graph + rw_facade_index_dimension fresh +
    rw_facade_dp_dimension table store + rw_facade_offers_dimension offers).

Definition rw_facade_runner_dimension {K} (run : rw_rp_run_state K unit nat nat) : nat :=
  S (rw_facade_tracked_dimension (rw_rp_current run) + rw_rp_position run +
    fold_right (fun event largest => Nat.max largest
      (
        match event with
        | RWRunRejected attempt => rw_facade_attempt_dimension attempt
        | RWRunAccepted attempt _ => rw_facade_attempt_dimension attempt
        end)) 1 (rw_rp_events run)).

Definition rw_facade_once_dimension {K} (before after : rw_rp_run_state K unit nat nat)
    (callback_dimension : nat) : nat :=
  S (rw_facade_runner_dimension before + rw_facade_runner_dimension after + callback_dimension).

Definition rw_facade_step_dimension {K} (step : rewrite_step K) : nat :=
  S (step_rule step + fold_right (fun index total => S (index + total)) 1 (step_pos step) +
    fold_right (fun term total => S (rw_facade_term_dimension term + total)) 1 (step_subst step)).

Definition rw_facade_leaves_dimension {K} (leaves : Map.t positive (rewrite_step K)) : nat :=
  rw_whole_map_dimension Pos.size_nat rw_facade_step_dimension leaves.
