(** * Finite observations and a PRE budget support diagnostic

    These examples observe finalization results and the points whose encodings it charges.
    For example, an initial version can name an expression-CFG entry absent from the SSA graph.
    Builds on: AnalysesAuditPrePlanAdequacy, AnalysesAuditSourceAdequacy and ViewsSsaPoints. *)

From Stdlib Require Import Arith Bool List PArith Lia.
From Galois.Analyses Require Import AnalysesAuditPrePlan AnalysesAuditPrePlanAdequacy
  AnalysesAuditSourceAdequacy AnalysesAvailable AnalysesSsaPre AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsFinSet CollectionsTrie.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominators.
From Galois.Views Require Import ViewsGraph ViewsSsa ViewsSsaPoints.
Import List.ListNotations.

(** * A finite graph with distinct expression and SSA entries *)

Definition plan_live_graph : Graph.t bool unit :=
  Graph.Make [false] [false] (fun _ => [tt]) (fun _ => false) (fun _ => false).

Definition plan_expression_graph : Graph.t bool unit :=
  Graph.Make [true] [true] (fun _ => []) (fun _ => true) (fun _ => true).

Definition plan_block_graph : Graph.t unit unit :=
  Graph.Make [] [] (fun _ => []) (fun _ => tt) (fun _ => tt).

Definition plan_points : ssa_points unit unit bool unit unit :=
  SsaPoints (PointUses plan_live_graph (fun _ => []) (fun _ => []) (fun _ => []))
    plan_block_graph (fun _ => [false]) (fun _ => [tt]) (fun _ => tt) (fun _ => tt)
    (fun _ => None) (fun _ => []) (fun _ => []) (fun _ => None).

Definition plan_expression_view : pre_expression_view unit unit bool unit unit unit :=
  PreExpressionView
    (GenKillView (GraphView plan_expression_graph (fun _ => true)
      (fun _ _ _ _ => False) (fun _ _ _ => False))
      (fun _ => []) (fun _ _ => false) (fun _ _ => Some tt))
    (fun _ => true) (fun _ => Some tt).

Definition plan_ssa_view : ssa_view unit unit unit unit unit unit unit :=
  SsaView (GraphView plan_block_graph (fun _ => tt)
    (fun _ _ _ _ => False) (fun _ _ _ => False))
    (fun _ => Arbitrary) (fun _ => tt) (fun _ => []) (fun _ => []) (fun _ => [])
    (fun _ _ => Some tt) (fun _ _ => Some tt) (fun _ => true).

Definition plan_fixture : pre_expr_ssa unit unit unit unit bool unit unit unit unit unit :=
  PreExprSsa plan_points plan_ssa_view plan_expression_view [tt] [tt] (fun _ => 1%positive)
    (fun _ => []) (fun _ _ => Some tt) (fun _ _ => Some tt) (fun _ => true) (fun _ => false).

Definition plan_client (pure killed initial : bool) (recomputed translated : option unit)
    : pre_expr_ssa unit unit unit unit bool unit unit unit unit unit :=
  PreExprSsa plan_points plan_ssa_view
    (PreExpressionView
      (GenKillView (GraphView plan_expression_graph (fun _ => true)
        (fun _ _ _ _ => False) (fun _ _ _ => False))
        (fun _ => []) (fun _ _ => killed) (fun _ _ => Some tt))
      (fun _ => pure) (fun _ => recomputed))
    [tt] [tt] (fun _ => 1%positive) (fun _ => []) (fun _ _ => Some tt)
    (fun _ _ => translated) (fun _ => initial) (fun _ => false).

Definition plan_frg : factored_redundancy_graph unit unit unit unit :=
  FactoredRedundancyGraph [FrInitial tt]
    (Map.set unit_encoding tt (FrInitial tt) Map.empty)
    FinSet.empty FinSet.empty Map.empty FinSet.empty.

Definition plan_facts : ssapre_facts unit unit :=
  SsaPreFacts Map.empty Map.empty Map.empty.

Definition plan_tree : dom_tree bool := DomTree Map.empty Map.empty Map.empty.

Definition plan_prepared : prepared bool_encoding plan_live_graph :=
  Prepared (Map.set bool_encoding false [tt] Map.empty) Map.empty 1%positive.

Definition plan_zero (_ : unit) : nat := 0.

Definition plan_bool_zero (_ : bool) : nat := 0.

Definition plan_point_body (coefficient : nat) (point : bool) : nat :=
  if point then coefficient else 0.

Definition plan_run coefficient :=
  pre_finalize_order_counted unit_encoding unit_encoding bool_encoding unit_encoding
    unit_encoding plan_fixture plan_zero plan_zero (plan_point_body coefficient)
    plan_zero plan_zero plan_frg plan_facts plan_tree plan_prepared [false].

(** * Flags, operand and dominance branches *)

Definition plan_can_facts : ssapre_facts unit unit :=
  SsaPreFacts Map.empty
    (Map.set (pair_encoding unit_encoding unit_encoding) (tt,tt) true Map.empty) Map.empty.

Definition plan_later_facts : ssapre_facts unit unit :=
  SsaPreFacts Map.empty (ssapre_can_available plan_can_facts)
    (Map.set (pair_encoding unit_encoding unit_encoding) (tt,tt) true Map.empty).

Definition plan_will facts :=
  pre_will_counted (BE:=unit) (N:=bool) (E:=unit)
    unit_encoding unit_encoding plan_zero plan_zero facts (tt,tt).

Definition plan_insert_operand facts (operand : frg_operand unit unit unit) :=
  pre_insert_operand_counted (BE:=unit) (N:=bool)
    unit_encoding unit_encoding plan_zero plan_zero facts operand.

Example plan_missing_flags_are_false : exact_value (plan_will plan_facts) = false.
Proof.
  reflexivity.
Qed.

Example plan_can_without_later_is_true : exact_value (plan_will plan_can_facts) = true.
Proof.
  reflexivity.
Qed.

Example plan_later_blocks_will : exact_value (plan_will plan_later_facts) = false.
Proof.
  reflexivity.
Qed.

Example plan_unavailable_inserts :
  exact_value (plan_insert_operand plan_facts (FrgOperand (FrUnavailable tt) false)) = true.
Proof.
  reflexivity.
Qed.

Example plan_initial_does_not_insert :
  exact_value (plan_insert_operand plan_facts (FrgOperand (FrInitial tt) false)) = false.
Proof.
  reflexivity.
Qed.

Example plan_fresh_does_not_insert :
  exact_value (plan_insert_operand plan_facts (FrgOperand (FrFresh tt tt) false)) = false.
Proof.
  reflexivity.
Qed.

Example plan_unselected_phi_inserts :
  exact_value (plan_insert_operand plan_facts (FrgOperand (FrPhi tt tt) false)) = true.
Proof.
  reflexivity.
Qed.

Example plan_selected_phi_does_not_insert :
  exact_value (plan_insert_operand plan_can_facts (FrgOperand (FrPhi tt tt) false)) = false.
Proof.
  reflexivity.
Qed.

Example plan_real_phi_use_does_not_insert :
  exact_value (plan_insert_operand plan_facts (FrgOperand (FrPhi tt tt) true)) = false.
Proof.
  reflexivity.
Qed.

Definition plan_dom tree :=
  pre_dominates_counted (B:=unit) (BE:=unit) (E:=unit) (U:=unit)
    bool_encoding plan_bool_zero tree false true.

(** A failed lookup charges the actual expression-only point supplied to dominance. *)
Example plan_dom_charges_expression_point coefficient :
  coefficient <= exact_units
    (pre_dominates_counted (B:=unit) (BE:=unit) (E:=unit) (U:=unit)
      bool_encoding (plan_point_body coefficient) plan_tree true false).
Proof.
  unfold pre_dominates_counted.
  rewrite plan_bind_units, plan_get_units, exact_get_erases.
  change (coefficient <= (194 + coefficient + 34 * 2) + 64 + 128).
  lia.
Qed.

Definition plan_single_time : Map.t bool positive :=
  Map.set bool_encoding false 1%positive Map.empty.

Definition plan_times : Map.t bool positive :=
  Map.set bool_encoding true 2%positive plan_single_time.

Definition plan_finish : Map.t bool positive :=
  Map.set bool_encoding false 3%positive
    (Map.set bool_encoding true 2%positive Map.empty).

Example plan_dom_first_missing : exact_value (plan_dom plan_tree) = false.
Proof.
  reflexivity.
Qed.

Example plan_dom_second_missing :
  exact_value (plan_dom (DomTree Map.empty plan_single_time Map.empty)) = false.
Proof.
  reflexivity.
Qed.

Example plan_dom_third_missing :
  exact_value (plan_dom (DomTree Map.empty plan_times Map.empty)) = false.
Proof.
  reflexivity.
Qed.

Example plan_dom_fourth_missing :
  exact_value (plan_dom (DomTree Map.empty plan_times plan_single_time)) = false.
Proof.
  reflexivity.
Qed.

Example plan_dom_interval_accepts :
  exact_value (plan_dom (DomTree Map.empty plan_times plan_finish)) = true.
Proof.
  reflexivity.
Qed.

Example plan_dom_interval_rejects :
  exact_value (plan_dom (DomTree Map.empty plan_times plan_times)) = false.
Proof.
  reflexivity.
Qed.

(** * Exact view payloads and materialization *)

Definition plan_empty : pre_plan unit unit :=
  PrePlan Map.empty Map.empty Map.empty Map.empty.

Example plan_order_single_node : exact_value (plan_run 0) = plan_empty.
Proof.
  reflexivity.
Qed.

Example plan_order_repeats_actual_occurrence :
  audit_case_count 760
    (exact_events (pre_finalize_order_counted unit_encoding unit_encoding bool_encoding
      unit_encoding unit_encoding plan_fixture plan_zero plan_zero plan_bool_zero
      plan_zero plan_zero plan_frg plan_facts plan_tree plan_prepared [false;false])) = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example plan_version_point_uses_expression_entry :
  exact_value (pre_version_point_counted plan_fixture (PreInitial tt)) = Some true.
Proof.
  reflexivity.
Qed.

Example plan_live_entry_is_different :
  Graph.entries (live_graph (point_model (pre_ssa_points plan_fixture))) = [false].
Proof.
  reflexivity.
Qed.

Definition plan_materialize (view : pre_expression_view unit unit bool unit unit unit) plan :=
  pre_materialize_counted unit_encoding unit_encoding view plan_zero plan_zero plan_zero plan.

Definition plan_phi_map version : Map.t ((unit * unit) * unit) (pre_version unit unit) :=
  Map.set (pair_encoding (pair_encoding unit_encoding unit_encoding) unit_encoding)
    ((tt,tt),tt) version Map.empty.

Definition plan_reload_map : Map.t unit (pre_version unit unit) :=
  Map.set unit_encoding tt (PreInitial tt) Map.empty.

Definition plan_version_maps : pre_plan unit unit :=
  PrePlan Map.empty Map.empty plan_reload_map (plan_phi_map (PreInserted tt tt)).

Definition plan_one_expression : Map.t unit (FinSet.t unit) :=
  Map.set unit_encoding tt (FinSet.add unit_encoding tt FinSet.empty) Map.empty.

Example plan_materialize_empty :
  exact_value (plan_materialize plan_expression_view plan_empty) = plan_empty.
Proof.
  reflexivity.
Qed.

Example plan_materialize_insert_and_reload :
  exact_value (plan_materialize plan_expression_view plan_version_maps) =
    PrePlan plan_one_expression plan_one_expression plan_reload_map
      (plan_phi_map (PreInserted tt tt)).
Proof.
  reflexivity.
Qed.

Example plan_materialize_initial_phi_skips_insertion :
  pre_insertions (exact_value (plan_materialize plan_expression_view
    (PrePlan Map.empty Map.empty Map.empty (plan_phi_map (PreInitial tt))))) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_materialize_computed_phi_skips_insertion :
  pre_insertions (exact_value (plan_materialize plan_expression_view
    (PrePlan Map.empty Map.empty Map.empty (plan_phi_map (PreComputed tt tt))))) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_materialize_merged_phi_skips_insertion :
  pre_insertions (exact_value (plan_materialize plan_expression_view
    (PrePlan Map.empty Map.empty Map.empty (plan_phi_map (PreMerged tt tt))))) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_materialize_absent_recomputation_skips_deletion :
  pre_deletions (exact_value (plan_materialize
    (pre_expression (plan_client true false true None (Some tt))) plan_version_maps)) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_expression_rows_repeat_idempotent :
  exact_value (pre_expression_rows_counted unit_encoding unit_encoding plan_zero plan_zero
    [(tt,tt);(tt,tt)]) = plan_one_expression.
Proof.
  reflexivity.
Qed.

Definition plan_malformed_phis : Map.t ((unit * unit) * unit) (pre_version unit unit) :=
  Trie.set 1%positive (((tt,tt),tt),PreInserted tt tt) Trie.Empty.

Example plan_materialize_enumerates_malformed_stored_key :
  pre_insertions (exact_value (plan_materialize plan_expression_view
    (PrePlan Map.empty Map.empty Map.empty plan_malformed_phis))) = plan_one_expression.
Proof.
  reflexivity.
Qed.

(** * Actual row setup, scope and argument branches *)

Definition plan_index_points : ssa_points unit unit bool unit unit :=
  SsaPoints (PointUses plan_live_graph (fun _ => []) (fun _ => []) (fun _ => []))
    plan_block_graph (fun _ => [false]) (fun _ => [tt]) (fun _ => tt) (fun _ => tt)
    (fun _ => Some tt) (fun _ => []) (fun _ => []) (fun _ => None).

Definition plan_index_client : pre_expr_ssa unit unit unit unit bool unit unit unit unit unit :=
  PreExprSsa plan_index_points plan_ssa_view plan_expression_view [tt] [tt]
    (fun _ => 1%positive) (fun _ => []) (fun _ _ => Some tt) (fun _ _ => Some tt)
    (fun _ => true) (fun _ => false).

Example plan_point_index_absent_projection :
  exact_value (pre_point_index_counted unit_encoding plan_fixture plan_zero) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_point_index_present_projection :
  exact_value (pre_point_index_counted unit_encoding plan_index_client plan_zero) =
    Map.set unit_encoding tt tt Map.empty.
Proof.
  reflexivity.
Qed.

Definition plan_phi_frg : factored_redundancy_graph unit unit unit unit :=
  FactoredRedundancyGraph [] Map.empty FinSet.empty
    (FinSet.add (pair_encoding unit_encoding unit_encoding) (tt,tt) FinSet.empty)
    Map.empty FinSet.empty.

Definition plan_phi_rows facts :=
  pre_phi_rows_counted unit_encoding bool_encoding unit_encoding plan_fixture
    plan_zero plan_bool_zero plan_zero plan_phi_frg facts.

Example plan_phi_rows_skips_false_will : exact_value (plan_phi_rows plan_facts) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_phi_rows_includes_selected_key :
  exact_value (plan_phi_rows plan_can_facts) =
    Map.set bool_encoding false [(tt,tt)] Map.empty.
Proof.
  reflexivity.
Qed.

Definition plan_argument : pre_finalize_argument unit unit unit unit :=
  PreFinalizeArgument tt tt tt tt (FrgOperand (FrUnavailable tt) false).

Definition plan_argument_frg : factored_redundancy_graph unit unit unit unit :=
  FactoredRedundancyGraph [] Map.empty FinSet.empty FinSet.empty
    (Map.set (pair_encoding (pair_encoding unit_encoding unit_encoding) unit_encoding)
      ((tt,tt),tt) (FrgOperand (FrUnavailable tt) false) Map.empty) FinSet.empty.

Example plan_argument_rows_missing_projection :
  exact_value (pre_argument_rows_counted unit_encoding bool_encoding plan_fixture
    plan_zero plan_bool_zero plan_argument_frg) = Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_argument_rows_present_projection :
  exact_value (pre_argument_rows_counted unit_encoding bool_encoding plan_index_client
    plan_zero plan_bool_zero plan_argument_frg) =
    Map.set bool_encoding false [plan_argument] Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_row_repetition_keeps_order :
  let first := exact_value (pre_add_phi_row_counted (BE:=unit) (E:=unit)
    bool_encoding plan_bool_zero Map.empty (false,(false,tt))) in
  exact_value (pre_add_phi_row_counted (BE:=unit) (E:=unit)
    bool_encoding plan_bool_zero first (false,(true,tt))) =
    Map.set bool_encoding false [(true,tt);(false,tt)] Map.empty.
Proof.
  reflexivity.
Qed.

Definition plan_argument_run
    (client : pre_expr_ssa unit unit unit unit bool unit unit unit unit unit) facts :=
  pre_argument_counted unit_encoding bool_encoding unit_encoding unit_encoding client
    plan_zero plan_bool_zero plan_zero plan_zero facts plan_tree Map.empty plan_empty plan_argument.

Example plan_argument_will_false_keeps_plan :
  exact_value (plan_argument_run plan_fixture plan_facts) = plan_empty.
Proof.
  reflexivity.
Qed.

Example plan_argument_translation_absent_keeps_plan :
  exact_value (plan_argument_run (plan_client true false true (Some tt) None)
    plan_can_facts) = plan_empty.
Proof.
  reflexivity.
Qed.

Example plan_argument_insert_selected :
  pre_phi_versions (exact_value (plan_argument_run plan_fixture plan_can_facts)) =
    plan_phi_map (PreInserted tt tt).
Proof.
  reflexivity.
Qed.

Example plan_argument_impure_keeps_plan :
  exact_value (plan_argument_run (plan_client false false true (Some tt) (Some tt))
    plan_can_facts) = plan_empty.
Proof.
  reflexivity.
Qed.

Example plan_argument_killed_keeps_plan :
  exact_value (plan_argument_run (plan_client true true true (Some tt) (Some tt))
    plan_can_facts) = plan_empty.
Proof.
  reflexivity.
Qed.

Example plan_initial_scope_selected :
  exact_value (pre_initial_scope_counted unit_encoding unit_encoding unit_encoding plan_fixture
    plan_zero plan_zero plan_zero [FrInitial tt; FrUnavailable tt; FrFresh tt tt; FrPhi tt tt]) =
    Map.set (frg_version_encoding unit_encoding unit_encoding unit_encoding)
      (FrInitial tt) (PreInitial tt) Map.empty.
Proof.
  reflexivity.
Qed.

Example plan_initial_scope_unavailable :
  exact_value (pre_initial_scope_counted unit_encoding unit_encoding unit_encoding
    (plan_client true false false (Some tt) (Some tt))
    plan_zero plan_zero plan_zero [FrInitial tt]) = Map.empty.
Proof.
  reflexivity.
Qed.

(** * Saved definitions and reload selections *)

Definition plan_all_times : Map.t bool positive :=
  Map.set bool_encoding true 1%positive plan_single_time.

Definition plan_accept_tree : dom_tree bool := DomTree Map.empty plan_all_times plan_all_times.

Definition plan_scope : Map.t (frg_version unit unit unit) (pre_version unit unit) :=
  Map.set (frg_version_encoding unit_encoding unit_encoding unit_encoding)
    (FrInitial tt) (PreInitial tt) Map.empty.

Example plan_available_saved_initial :
  exact_value (pre_available_counted unit_encoding bool_encoding unit_encoding unit_encoding
    plan_fixture plan_zero plan_bool_zero plan_zero plan_zero
    plan_accept_tree plan_scope (FrInitial tt) tt false) = Some (PreInitial tt).
Proof.
  reflexivity.
Qed.

Example plan_available_missing_scope :
  exact_value (pre_available_counted unit_encoding bool_encoding unit_encoding unit_encoding
    plan_fixture plan_zero plan_bool_zero plan_zero plan_zero
    plan_accept_tree Map.empty (FrInitial tt) tt false) = None.
Proof.
  reflexivity.
Qed.

Definition plan_occurrence
    (client : pre_expr_ssa unit unit unit unit bool unit unit unit unit unit) tree scope :=
  pre_occurrence_counted unit_encoding bool_encoding unit_encoding unit_encoding client
    plan_zero plan_bool_zero plan_zero plan_zero plan_frg tree (scope,plan_empty) tt.

Example plan_occurrence_selects_reload :
  exact_value (plan_occurrence plan_fixture plan_accept_tree plan_scope) =
    (plan_scope,PrePlan Map.empty Map.empty plan_reload_map Map.empty).
Proof.
  reflexivity.
Qed.

Example plan_occurrence_saves_unavailable_definition :
  exact_value (plan_occurrence plan_fixture plan_tree Map.empty) =
    (Map.set (frg_version_encoding unit_encoding unit_encoding unit_encoding)
      (FrInitial tt) (PreComputed tt tt) Map.empty,plan_empty).
Proof.
  reflexivity.
Qed.

Example plan_occurrence_skips_absent_recomputation :
  exact_value (plan_occurrence (plan_client true false true None (Some tt))
    plan_accept_tree plan_scope) = (plan_scope,plan_empty).
Proof.
  reflexivity.
Qed.

Example plan_occurrence_skips_impure_recomputation :
  exact_value (plan_occurrence (plan_client false false true (Some tt) (Some tt))
    plan_accept_tree plan_scope) = (plan_scope,plan_empty).
Proof.
  reflexivity.
Qed.

Definition plan_reuse_argument : pre_finalize_argument unit unit unit unit :=
  PreFinalizeArgument tt tt tt tt (FrgOperand (FrInitial tt) false).

Example plan_argument_reuses_saved_version :
  pre_phi_versions (exact_value
    (pre_argument_counted unit_encoding bool_encoding unit_encoding unit_encoding
      plan_fixture plan_zero plan_bool_zero plan_zero plan_zero plan_can_facts
      plan_accept_tree plan_scope plan_empty plan_reuse_argument)) =
    plan_phi_map (PreInitial tt).
Proof.
  reflexivity.
Qed.

Example plan_argument_unavailable_reuse_keeps_plan :
  exact_value (pre_argument_counted unit_encoding bool_encoding unit_encoding unit_encoding
    plan_fixture plan_zero plan_bool_zero plan_zero plan_zero plan_can_facts
    plan_accept_tree Map.empty plan_empty plan_reuse_argument) = plan_empty.
Proof.
  reflexivity.
Qed.
