(** * Computed PRE finalizer support observations

    These examples exercise different expression and live graphs, malformed raw maps,
    repeated visits and nonempty insertion and reload traces. For example, an expression
    target event carries true while a live target event carries false on the same edge.
    Builds on: AnalysesAuditPrePlanSupport and the public PRE input records. *)

From Stdlib Require Import Arith Bool Decimal List PArith.
From Galois.Analyses Require Import AnalysesAuditPrePlanSupport AnalysesAuditPrePlan
  AnalysesAuditSource AnalysesAvailable AnalysesSsaPre AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsFinSet
  CollectionsMap CollectionsTrie.
From Galois.Graph Require Import GraphCore GraphDominators GraphPrepare.
From Galois.Views Require Import ViewsGraph ViewsSsa ViewsSsaPoints.
Import List.ListNotations.

Definition support_graph (entry target : bool) : Graph.t bool bool :=
  Graph.Make [entry] [false] (fun n => if n then [] else [false]) (fun _ => false)
    (fun _ => target).

Definition support_block_graph : Graph.t bool bool :=
  Graph.Make [] [] (fun _ => []) (fun _ => false) (fun _ => false).

Definition support_graph_view (graph : Graph.t bool bool) : graph_view unit unit bool bool :=
  GraphView graph (fun _ => false) (fun _ _ _ _ => False) (fun _ _ _ => False).

Definition support_points : ssa_points bool bool bool bool unit :=
  SsaPoints (PointUses (support_graph false false) (fun _ => []) (fun _ => []) (fun _ => []))
    support_block_graph (fun _ => [false]) (fun _ => []) (fun b => b) (fun _ => false)
    (fun e => Some e) (fun _ => []) (fun _ => []) (fun _ => None).

Definition support_ssa_view : ssa_view unit unit bool bool unit unit unit :=
  SsaView (support_graph_view support_block_graph) (fun _ => Arbitrary) (fun _ => false)
    (fun _ => []) (fun _ => []) (fun _ => []) (fun _ _ => Some tt) (fun _ _ => Some tt)
    (fun _ => true).

Definition support_expression (entry target : bool) :
    pre_expr_ssa unit unit bool bool bool bool unit unit unit bool :=
  PreExprSsa support_points support_ssa_view
    (PreExpressionView (GenKillView (support_graph_view (support_graph entry target))
      (fun _ => [false]) (fun _ _ => false) (fun _ _ => Some tt)) (fun _ => true)
      (fun _ => Some false))
    [false] [tt] (fun u => encode bool_encoding u) (fun _ => []) (fun _ _ => Some tt)
    (fun _ u => Some u) (fun _ => true) (fun _ => false).

Definition support_facts : ssapre_facts bool bool :=
  SsaPreFacts Map.empty
    (Map.set (pair_encoding bool_encoding bool_encoding) (true,false) true Map.empty) Map.empty.

Definition support_empty_frg : factored_redundancy_graph bool bool bool bool :=
  FactoredRedundancyGraph [] Map.empty FinSet.empty FinSet.empty Map.empty FinSet.empty.

Definition support_frg : factored_redundancy_graph bool bool bool bool :=
  FactoredRedundancyGraph [FrInitial false]
    (Trie.set 1%positive (true,FrInitial false) Map.empty) FinSet.empty
    (FinSet.add (pair_encoding bool_encoding bool_encoding) (true,false) FinSet.empty)
    (Trie.set 1%positive (((true,false),false),FrgOperand (FrUnavailable false) false) Map.empty)
    FinSet.empty.

Definition support_link_frg : factored_redundancy_graph bool bool bool bool :=
  FactoredRedundancyGraph [] Map.empty FinSet.empty FinSet.empty
    (Trie.set 1%positive (((true,false),false),FrgOperand (FrUnavailable false) false) Map.empty)
    FinSet.empty.

Definition support_tree : dom_tree bool :=
  DomTree Map.empty (Map.set bool_encoding false 1%positive Map.empty)
    (Map.set bool_encoding false 1%positive Map.empty).

Definition support_empty_tree : dom_tree bool := DomTree Map.empty Map.empty Map.empty.

Definition support_prepared : prepared bool_encoding (support_graph false false) :=
  Prepared (Trie.set 1%positive (true,[false]) Map.empty) Map.empty 1%positive.

Definition support_zero (_ : bool) := 0.

Definition support_block_body (b : bool) := if b then 7 else 2.

Definition support_block_edge_body (be : bool) := if be then 11 else 3.

Definition support_point_body (n : bool) := if n then 9 else 1.

Definition support_edge_body (e : bool) := if e then 5 else 2.

Definition support_expr_body (u : bool) := if u then 13 else 4.

Definition support_run (entry target : bool) (order : list bool) :=
  pre_finalize_order_counted bool_encoding bool_encoding bool_encoding bool_encoding bool_encoding
    (support_expression entry target) support_block_body support_block_edge_body support_point_body
    support_edge_body support_expr_body support_frg support_facts support_tree support_prepared
    order.

(** The actual raw malformed-input run instantiates the theorem with all five body functions. *)
Example support_actual_bound :
  exact_units (support_run false false [false;false]) <=
  pre_finalize_order_input_budget bool_encoding bool_encoding bool_encoding bool_encoding
    bool_encoding (support_expression false false) support_block_body support_block_edge_body
    support_point_body support_edge_body support_expr_body support_frg support_facts support_tree
    support_prepared [false;false].
Proof.
  exact (pre_finalize_order_bound bool_encoding bool_encoding bool_encoding bool_encoding
    bool_encoding (support_expression false false) support_block_body support_block_edge_body
    support_point_body support_edge_body support_expr_body support_frg support_facts support_tree
    support_prepared [false;false]).
Qed.

Inductive support_observation : Type :=
  | SupportInitial (expr : bool) (result : bool)
  | SupportParameter (block edge : bool)
  | SupportTranslate (edge expr : bool) (result : option bool)
  | SupportLiveTarget (edge point : bool)
  | SupportExpressionTarget (edge point : bool)
  | SupportSource (edge point : bool)
  | SupportRecomputed (edge : bool) (result : option bool)
  | SupportPure (expr result : bool)
  | SupportKill (edge expr result : bool)
  | SupportPhi (key : (bool * bool) * bool) (version : pre_version bool bool)
  | SupportReload (edge : bool) (version : pre_version bool bool).

Definition support_observe_call (call : pre_finalize_call bool bool bool bool bool) :=
  match call with
  | PfInitial u result =>
    [SupportInitial u result]
  | PfParameter b e =>
    [SupportParameter b e]
  | PfTranslate be u result =>
    [SupportTranslate be u result]
  | PfTarget e n =>
    [SupportLiveTarget e n]
  | PfExpressionTarget e n =>
    [SupportExpressionTarget e n]
  | PfSource e n =>
    [SupportSource e n]
  | PfRecomputed e result =>
    [SupportRecomputed e result]
  | PfPure u result =>
    [SupportPure u result]
  | PfKill e u result =>
    [SupportKill e u result]
  | PfPhi (ExactSet key _ version _ _) =>
    [SupportPhi key version]
  | PfReload (ExactSet edge _ version _ _) =>
    [SupportReload edge version]
  | _ =>
    []
  end.

Definition support_observe (run : exact_counted (pre_rows_call bool bool bool bool bool)
    (pre_plan bool bool)) :=
  flat_map (fun call =>
    match call with
    | PrFinalize nested =>
      support_observe_call nested
    | _ =>
      []
    end) (audit_calls (exact_events run)).

Example support_expression_entry :
  exact_value (pre_version_point_counted (support_expression true false) (PreInitial false)) =
    Some true.
Proof.
  reflexivity.
Qed.

Example support_expression_target_trace :
  exact_events (pre_version_point_counted (support_expression false true)
    (PreComputed false false)) =
    [AuditCase 721 []; AuditCall (PfExpressionTarget false true); AuditCase 722 [];
     AuditConstruct 723 []].
Proof.
  reflexivity.
Qed.

Example support_malformed_occurrence_lookup :
  Map.get bool_encoding false (frg_occurrence_index support_frg) = Some (FrInitial false) /\
  Map.elements (frg_occurrence_index support_frg) = [(true,FrInitial false)].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example support_absent_occurrence_lookup :
  Map.get bool_encoding true (frg_occurrence_index support_frg) = None.
Proof.
  reflexivity.
Qed.

Example support_malformed_prepared_lookup :
  Map.get bool_encoding false (out_index support_prepared) = Some [false] /\
  Map.elements (out_index support_prepared) = [(true,[false])].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example support_nonempty_plan :
  Map.get bool_encoding false (pre_reload_versions (exact_value (support_run false false [false])))
    = Some (PreInitial false) /\
  Map.get (pair_encoding (pair_encoding bool_encoding bool_encoding) bool_encoding)
    ((true,false),false) (pre_phi_versions (exact_value (support_run false false [false]))) =
      Some (PreInserted false false).
Proof.
  vm_compute. split; reflexivity.
Qed.

Example support_empty_order_trace : support_observe (support_run false false []) =
  [SupportParameter true true; SupportLiveTarget true false; SupportSource false false;
   SupportInitial false true].
Proof.
  vm_compute. reflexivity.
Qed.

Example support_insertion_reload_trace : support_observe (support_run false false [false]) =
  [SupportParameter true true; SupportLiveTarget true false; SupportSource false false;
   SupportInitial false true; SupportParameter true true; SupportParameter true true;
   SupportTranslate false false (Some false); SupportPure false true; SupportKill false false false;
   SupportPhi ((true,false),false) (PreInserted false false); SupportRecomputed false (Some false);
   SupportPure false true; SupportSource false false; SupportReload false (PreInitial false)].
Proof.
  vm_compute. reflexivity.
Qed.

Example support_repeated_order_trace : support_observe (support_run false false [false;false]) =
  support_observe (support_run false false [false]) ++
  [SupportParameter true true; SupportParameter true true;
   SupportTranslate false false (Some false); SupportPure false true; SupportKill false false false;
   SupportPhi ((true,false),false) (PreInserted false false); SupportRecomputed false (Some false);
   SupportPure false true; SupportSource false false; SupportReload false (PreInitial false)].
Proof.
  vm_compute. reflexivity.
Qed.

Example support_repeated_order_cost :
  exact_units (support_run false false [false]) <
    exact_units (support_run false false [false;false]).
Proof.
  apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

Definition support_computed_frg : factored_redundancy_graph bool bool bool bool :=
  FactoredRedundancyGraph [] (Map.set bool_encoding false (FrFresh false false) Map.empty)
    FinSet.empty FinSet.empty Map.empty FinSet.empty.

Definition support_computed_prepared : prepared bool_encoding (support_graph false false) :=
  Prepared (Map.set bool_encoding false [false;false] Map.empty) Map.empty 1%positive.

Definition support_computed_tree : dom_tree bool :=
  DomTree Map.empty
    (Map.set bool_encoding true 1%positive (Map.set bool_encoding false 1%positive Map.empty))
    (Map.set bool_encoding true 1%positive (Map.set bool_encoding false 1%positive Map.empty)).

Definition support_computed_run :=
  pre_finalize_order_counted bool_encoding bool_encoding bool_encoding bool_encoding bool_encoding
    (support_expression false true) support_block_body support_block_edge_body support_point_body
    support_edge_body support_expr_body support_computed_frg support_facts support_computed_tree
    support_computed_prepared [false].

Example support_computed_reload_target_trace : support_observe support_computed_run =
  [SupportRecomputed false (Some false); SupportPure false true; SupportSource false false;
   SupportRecomputed false (Some false); SupportPure false true; SupportSource false false;
   SupportExpressionTarget false true; SupportReload false (PreComputed false false)].
Proof.
  vm_compute. reflexivity.
Qed.

Example support_computed_reload_version :
  Map.get bool_encoding false (pre_reload_versions (exact_value support_computed_run)) =
    Some (PreComputed false false).
Proof.
  vm_compute. reflexivity.
Qed.

Example support_absent_scope :
  exact_value (pre_available_counted bool_encoding bool_encoding bool_encoding bool_encoding
    (support_expression false true) support_block_body support_point_body support_edge_body
    support_expr_body support_tree Map.empty (FrInitial false) false false) = None.
Proof.
  reflexivity.
Qed.

Example support_link_only_block :
  Graph.nodes (block_graph (pre_ssa_points (support_expression false false))) = [] /\
  FinSet.elements (frg_phi_index support_link_frg) = [] /\
  Map.elements (frg_phi_operands support_link_frg) =
    [(((true,false),false),FrgOperand (FrUnavailable false) false)].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example support_empty_raw_plan :
  exact_value (pre_finalize_order_counted bool_encoding bool_encoding bool_encoding bool_encoding
    bool_encoding (support_expression false false) support_zero support_zero support_zero
    support_zero support_zero support_empty_frg support_facts support_empty_tree support_prepared
    [])
  = PrePlan Map.empty Map.empty Map.empty Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example support_absent_parent_fallback :
  exact_value (pre_finalize_order_counted bool_encoding bool_encoding bool_encoding bool_encoding
    bool_encoding (support_expression false false) support_block_body support_block_edge_body
    support_point_body support_edge_body support_expr_body support_frg support_facts
    (DomTree (Map.set bool_encoding false true Map.empty) (tin support_tree) (tout support_tree))
    support_prepared [false]) = exact_value (support_run false false [false]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Scalar powers remain symbolic while computation checks the actual support dimensions. *)
Section SymbolicBudgets.

Local Opaque Nat.pow Nat.mul Nat.of_num_uint.

Definition support_point_budget (entry target : bool) :=
  pre_finalize_order_input_budget bool_encoding bool_encoding bool_encoding bool_encoding
    bool_encoding (support_expression entry target) support_zero support_zero
    (fun n => if n then 9 else 0) support_zero support_zero support_empty_frg support_facts
    support_empty_tree support_prepared [false].

Definition support_link_budget (block_cost : nat) :=
  pre_finalize_order_input_budget bool_encoding bool_encoding bool_encoding bool_encoding
    bool_encoding (support_expression false false) (fun b => if b then block_cost else 0)
    support_zero support_zero support_zero support_zero support_link_frg support_facts
    support_empty_tree support_prepared [false].

Example support_budget_base : support_point_budget false false =
  Nat.of_num_uint 16777216%uint * 26 ^ 32 * 5 ^ 16.
Proof.
  cbv. reflexivity.
Qed.

Example support_budget_entry_difference : support_point_budget true false =
  Nat.of_num_uint 16777216%uint * 26 ^ 32 * 15 ^ 16.
Proof.
  cbv. reflexivity.
Qed.

Example support_budget_target_difference : support_point_budget false true =
  Nat.of_num_uint 16777216%uint * 26 ^ 32 * 15 ^ 16.
Proof.
  cbv. reflexivity.
Qed.

Example support_budget_link_base : support_link_budget 0 =
  Nat.of_num_uint 16777216%uint * 40 ^ 32 * 9 ^ 16.
Proof.
  cbv. reflexivity.
Qed.

Example support_budget_link_block_difference : support_link_budget 9 =
  Nat.of_num_uint 16777216%uint * 40 ^ 32 * 18 ^ 16.
Proof.
  cbv. reflexivity.
Qed.

End SymbolicBudgets.
