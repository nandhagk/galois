(** * Whole PRE original callback source closure

    Receipts connect counted PRE phases to original graph, encoding and expression callbacks.
    For example, a translation receipt retains its incoming edge and expression.
    Builds on: PRE phase models and external source adapters. *)

From Stdlib Require Import Arith Bool List PArith.
From Galois.Analyses Require Export AnalysesAuditPre AnalysesAuditPreFamily AnalysesAuditPreFinite
  AnalysesAuditPreFrg AnalysesAuditPrePlan AnalysesAuditPreSolve AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSsaPre AnalysesSsaPreGraph
  AnalysesSsaPreSemantics.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditMap CollectionsAuditPrimitive
  CollectionsAuditTrie CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditDominators
  GraphAuditFrontier GraphAuditLengauerTarjan GraphAuditSemiDominators GraphAuditVirtual GraphCore
  GraphDfs GraphDominance GraphDominators GraphFrontier GraphLengauerTarjan GraphPrepare
  GraphSemiDominators.
From Galois.Views Require Import ViewsGraph ViewsSemantics ViewsSsa ViewsSsaPoints.
Import List.ListNotations.

Scheme All for ex.

Scheme All for and.

Scheme All for Forall2.

(** * Genuine original PRE view callback sources

    Only functions supplied by the original public encodings and expression/graph view
    receive external adapters. Internal phi graphs, reset closures and derived encoders use
    fixed library source instances and the actual callback payloads already retained.
    For example, a translation receipt names its original incoming edge and expression.
    Builds on: exact source combinators and the canonical PRE phase models. *)
Section PreCallbackTypes.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U).

(** The original block and live point graphs supply the graph adapters below. *)
Let bg := block_graph (pre_ssa_points a).

Let pg := live_graph (point_model (pre_ssa_points a)).

(** Each field instruments one original PRE view operation or encoding. *)
Record audit_pre_view_adapters : Type := PreViewAdapters {
  (** Encode an original block. *)
  pre_block_encoder : audit_external_adapter B positive (encode EB);
  (** Encode an original block edge. *)
  pre_block_edge_encoder : audit_external_adapter BE positive (encode EBE);
  (** Encode an original program point. *)
  pre_point_encoder : audit_external_adapter N positive (encode EN);
  (** Encode an original point edge. *)
  pre_edge_encoder : audit_external_adapter E positive (encode EE);
  (** Encode an original SSA value. *)
  pre_value_encoder : audit_external_adapter V positive (encode EV);
  (** Encode an original expression. *)
  pre_expr_encoder : audit_external_adapter U positive (encode EU);
  (** Enumerate outgoing block edges. *)
  pre_block_out_source : audit_external_adapter B (list BE) (Graph.out bg);
  (** Observe a block edge source. *)
  pre_block_source_source : audit_external_adapter BE B (Graph.source bg);
  (** Observe a block edge target. *)
  pre_block_target_source : audit_external_adapter BE B (Graph.target bg);
  (** Enumerate outgoing point edges. *)
  pre_point_out_source : audit_external_adapter N (list E) (Graph.out pg);
  (** Observe a point edge source. *)
  pre_point_source_source : audit_external_adapter E N (Graph.source pg);
  (** Observe a point edge target. *)
  pre_point_target_source : audit_external_adapter E N (Graph.target pg);
  (** Observe the expression graph target used by version availability. *)
  pre_expression_target_source : audit_external_adapter E N
    (Graph.target (cfg (gkview (pre_genkill (pre_expression a)))));
  (** Observe an expression operand list. *)
  pre_operands_source : audit_external_adapter U (list V) (pre_operands a);
  (** Translate an expression on its block edge. *)
  pre_translate_source : audit_external_adapter (BE * U) (option U)
    (fun input => pre_phi_translate a (fst input) (snd input));
  (** Observe initial expression availability. *)
  pre_initial_source : audit_external_adapter U bool (pre_initial_available a);
  (** Observe whether an expression is total and pure. *)
  pre_pure_source : audit_external_adapter U bool (pre_total_pure (pre_expression a));
  (** Observe the expression recomputed on an edge. *)
  pre_recomputed_source : audit_external_adapter E (option U) (pre_recomputed (pre_expression a));
  (** Observe whether an edge kills an expression. *)
  pre_kill_source : audit_external_adapter (E * U) bool
    (fun input => kill (pre_genkill (pre_expression a)) (fst input) (snd input));
  (** Observe a block parameter edge. *)
  pre_parameter_source : audit_external_adapter B E (parameter_edge (pre_ssa_points a));
  (** Enumerate the points in a block. *)
  pre_points_source : audit_external_adapter B (list N) (points_in_block (pre_ssa_points a));
  (** Enumerate a block's instruction edges. *)
  pre_instructions_source : audit_external_adapter B (list E)
    (instruction_edges (pre_ssa_points a));
  (** Observe the values defined on a point edge. *)
  pre_definitions_source : audit_external_adapter E (list V)
    (edge_def (point_model (pre_ssa_points a)));
  (** Observe whether a point is an exit. *)
  pre_exit_source : audit_external_adapter N bool (pre_exit_point a);
  (** Observe the home block of an SSA value. *)
  pre_home_source : audit_external_adapter V B (home (pre_ssa_view a));
  (** Observe the block containing a point. *)
  pre_block_of_source : audit_external_adapter N B (block_of_point (pre_ssa_points a));
  (** Observe a block's parameters. *)
  pre_block_params_source : audit_external_adapter B (list V) (block_params (pre_ssa_points a));
  (** Observe the block edge associated with a point edge. *)
  pre_block_edge_of_source : audit_external_adapter E (option BE)
    (block_edge_of (pre_ssa_points a))
}.

(** Every original PRE callback adapter must erase and meet its own per-call source budget. *)
Definition audit_pre_view_adapter_laws (adapters : audit_pre_view_adapters) : Prop :=
  audit_external_adapter_laws (pre_block_encoder adapters) /\
  audit_external_adapter_laws (pre_block_edge_encoder adapters) /\
  audit_external_adapter_laws (pre_point_encoder adapters) /\
  audit_external_adapter_laws (pre_edge_encoder adapters) /\
  audit_external_adapter_laws (pre_value_encoder adapters) /\
  audit_external_adapter_laws (pre_expr_encoder adapters) /\
  audit_external_adapter_laws (pre_block_out_source adapters) /\
  audit_external_adapter_laws (pre_block_source_source adapters) /\
  audit_external_adapter_laws (pre_block_target_source adapters) /\
  audit_external_adapter_laws (pre_point_out_source adapters) /\
  audit_external_adapter_laws (pre_point_source_source adapters) /\
  audit_external_adapter_laws (pre_point_target_source adapters) /\
  audit_external_adapter_laws (pre_expression_target_source adapters) /\
  audit_external_adapter_laws (pre_operands_source adapters) /\
  audit_external_adapter_laws (pre_translate_source adapters) /\
  audit_external_adapter_laws (pre_initial_source adapters) /\
  audit_external_adapter_laws (pre_pure_source adapters) /\
  audit_external_adapter_laws (pre_recomputed_source adapters) /\
  audit_external_adapter_laws (pre_kill_source adapters) /\
  audit_external_adapter_laws (pre_parameter_source adapters) /\
  audit_external_adapter_laws (pre_points_source adapters) /\
  audit_external_adapter_laws (pre_instructions_source adapters) /\
  audit_external_adapter_laws (pre_definitions_source adapters) /\
  audit_external_adapter_laws (pre_exit_source adapters) /\
  audit_external_adapter_laws (pre_home_source adapters) /\
  audit_external_adapter_laws (pre_block_of_source adapters) /\
  audit_external_adapter_laws (pre_block_params_source adapters) /\
  audit_external_adapter_laws (pre_block_edge_of_source adapters).

End PreCallbackTypes.

Definition pre_receipt_work (receipts : list (list audit_external_frame * nat)) : nat :=
  fold_right (fun receipt rest => audit_external_trace_work (fst receipt) + rest) 0 receipts.

Definition pre_receipt_allowance (receipts : list (list audit_external_frame * nat)) : nat :=
  fold_right (fun receipt rest => snd receipt + rest) 0 receipts.

Definition pre_receipt_trace (receipts : list (list audit_external_frame * nat)) :=
  concat (map fst receipts).

(** Each actual call has a matching receipt whose traces and allowances concatenate in order. *)
Definition pre_fixed_calls_receipt {Call}
    (source : Call -> list audit_external_frame -> nat -> Prop)
    (calls : list Call) trace allowance : Prop :=
  exists receipts,
    Forall2 (fun call receipt => source call (fst receipt) (snd receipt)) calls receipts /\
    trace = pre_receipt_trace receipts /\ allowance = pre_receipt_allowance receipts.

(** An external receipt retains the actual call result and its input-specific allowance. *)
Definition pre_actual_external_receipt {I O plain}
    (adapter : audit_external_adapter I O plain) input output trace allowance : Prop :=
  audit_external_same_call adapter input output trace /\
  allowance = external_input_budget adapter input.

(** An internal operation adds neither an external trace nor an external allowance. *)
Definition pre_internal_receipt (trace : list audit_external_frame) (allowance : nat) : Prop :=
  trace = [] /\ allowance = 0.

(** A pair encoding receipt combines the actual component codes, traces and allowances in order. *)
Definition pre_pair_source_receipt {A B} (EA : encoding A) (EB : encoding B)
    (left : A -> positive -> list audit_external_frame -> nat -> Prop)
    (right : B -> positive -> list audit_external_frame -> nat -> Prop)
    (input : A * B) output trace allowance : Prop :=
  exists first second first_trace second_trace first_allowance second_allowance,
    left (fst input) first first_trace first_allowance /\
    right (snd input) second second_trace second_allowance /\
    first = encode EA (fst input) /\ second = encode EB (snd input) /\
    output = fst (audit_pair_encode (fun _ : A => (first,([] : list unit)))
      (fun _ : B => (second,([] : list unit))) input) /\
    trace = first_trace ++ second_trace /\ allowance = first_allowance + second_allowance.

(** Only an actual map encoder call contributes an external receipt. *)
Definition pre_actual_map_receipt {K V}
    (source : K -> positive -> list audit_external_frame -> nat -> Prop)
    (call : exact_map_call K V) trace allowance : Prop :=
  match call with
  | ExactEncode key code => source key code trace allowance
  | _ => pre_internal_receipt trace allowance
  end.

(** Only an actual audited call contributes its associated external receipt. *)
Definition pre_audit_event_receipt {Call}
    (source : Call -> list audit_external_frame -> nat -> Prop)
    (event : audit_event Call) trace allowance : Prop :=
  match event with
  | AuditCall call => source call trace allowance
  | _ => pre_internal_receipt trace allowance
  end.

Definition pre_map_callback_calls {K V Call} (event : audit_map_event K V Call) : list Call :=
  match event with
  | AuditMapGet _ _ _ _ body _ | AuditMapSet _ _ _ _ _ body _ |
      AuditMapRemove _ _ _ _ body _ => body
  end.

Definition pre_set_callback_calls {K Call} (event : audit_set_event K Call) : list Call :=
  match event with
  | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
      AuditSetRemove _ _ _ _ body _ => body
  | AuditSetFold _ _ => []
  end.

Definition pre_prepare_callback_calls {V E Call}
    (event : audit_prepare_source_event V E Call) : list Call :=
  match event with
  | PrepareSourceOut _ _ body | PrepareSourceTarget _ _ body => body
  | PrepareSourceMap call => pre_map_callback_calls call
  | _ => []
  end.

Definition pre_dfs_callback_calls {V E Call}
    (event : audit_dfs_nested_event V E (audit_graph_callback_capture V E Call)) : list Call :=
  flat_map (fun captured =>
    match captured with
    | AuditGraphTargetCapture _ _ _ _ _ body | AuditGraphEncodeCapture _ _ _ _ _ body => body
    end) (snd event).

Section PrePhaseBodyReceipts.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (adapters : audit_pre_view_adapters EB EBE EN EE EV EU a).

(** The six receipts retain actual block, block-edge, point, edge, value and expression codes. *)
Let bs := pre_actual_external_receipt (pre_block_encoder EB EBE EN EE EV EU a adapters).

Let bes := pre_actual_external_receipt (pre_block_edge_encoder EB EBE EN EE EV EU a adapters).

Let ns := pre_actual_external_receipt (pre_point_encoder EB EBE EN EE EV EU a adapters).

Let es := pre_actual_external_receipt (pre_edge_encoder EB EBE EN EE EV EU a adapters).

Let vs := pre_actual_external_receipt (pre_value_encoder EB EBE EN EE EV EU a adapters).

Let us := pre_actual_external_receipt (pre_expr_encoder EB EBE EN EE EV EU a adapters).

(** Pair receipts compose those encoders in key order: BU, UB, BEU, EE, EEU and BU-BE. *)
Let bu := pre_pair_source_receipt EB EU bs us.

Let ubu := pre_pair_source_receipt EU EB us bs.

Let beu := pre_pair_source_receipt EBE EU bes us.

Let eep := pre_pair_source_receipt EE EE es es.

Let eeu := pre_pair_source_receipt (pair_encoding EE EE) EU eep us.

Let bube := pre_pair_source_receipt (pair_encoding EB EU) EBE bu bes.

(** A version encoding receipt follows the actual version constructor and component encoders. *)
Definition pre_frg_version_receipt (input : frg_version B E U) output trace allowance : Prop :=
  output = fst (pre_frg_source_encoding EB EE EU input) /\
  match input with
  | FrUnavailable u | FrInitial u => us u (encode EU u) trace allowance
  | FrFresh e u =>
    pre_pair_source_receipt EE EU es us (e,u)
      (encode (pair_encoding EE EU) (e,u)) trace allowance
  | FrPhi b u => bu (b,u) (encode (pair_encoding EB EU) (b,u)) trace allowance
  end.

(** Family receipts charge original graph, expression and encoder callbacks on their
    actual operands. *)
Definition pre_family_call_receipt (call : pre_family_call B BE V U) trace allowance : Prop :=
  match call with
  | PreFamilyExpr nested => pre_actual_map_receipt us nested trace allowance
  | PreFamilyEdges nested => pre_actual_map_receipt bes nested trace allowance
  | PreFamilyOut block result =>
    pre_actual_external_receipt
      (pre_block_out_source EB EBE EN EE EV EU a adapters) block result trace allowance
  | PreFamilyOperands u result =>
    pre_actual_external_receipt
      (pre_operands_source EB EBE EN EE EV EU a adapters) u result trace allowance
  | PreFamilyTranslate edge u result =>
    pre_actual_external_receipt
      (pre_translate_source EB EBE EN EE EV EU a adapters) (edge,u) result trace allowance
  | _ => pre_internal_receipt trace allowance
  end.

(** Rename receipts attach original view and encoding callbacks to their recorded operands. *)
Definition pre_rename_call_receipt (call : pre_rename_call B BE N E V U) trace allowance : Prop :=
  match call with
  | PrnScope nested => pre_actual_map_receipt us nested trace allowance
  | PrnOccurrence nested => pre_actual_map_receipt es nested trace allowance
  | PrnFresh nested => pre_actual_map_receipt es nested trace allowance
  | PrnLink nested => pre_actual_map_receipt bube nested trace allowance
  | PrnUnsafe nested => pre_actual_map_receipt bu nested trace allowance
  | PrnSeen nested => pre_actual_map_receipt bs nested trace allowance
  | PrnGroupBU nested => pre_actual_map_receipt bs nested trace allowance
  | PrnGroupEU nested => pre_actual_map_receipt es nested trace allowance
  | PrnGroupVU nested => pre_actual_map_receipt vs nested trace allowance
  | PrnSites nested => pre_actual_map_receipt us nested trace allowance
  | PrnPred nested => pre_actual_map_receipt bs nested trace allowance
  | PrnSetU nested => pre_actual_map_receipt us nested trace allowance
  | PrnExit nested => pre_actual_map_receipt ns nested trace allowance
  | PrnArguments nested => pre_actual_map_receipt bs nested trace allowance
  | PrnSetArgument nested => pre_actual_map_receipt beu nested trace allowance
  | PrnChildren nested => pre_actual_map_receipt bs nested trace allowance
  | PrnPhis nested => pre_actual_map_receipt bu nested trace allowance
  | PrnVersions nested => pre_actual_map_receipt pre_frg_version_receipt nested trace allowance
  | PrnInitial u result =>
    pre_actual_external_receipt
      (pre_initial_source EB EBE EN EE EV EU a adapters) u result trace allowance
  | PrnPure u result =>
    pre_actual_external_receipt
      (pre_pure_source EB EBE EN EE EV EU a adapters) u result trace allowance
  | PrnRecomputed edge result =>
    pre_actual_external_receipt
      (pre_recomputed_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PrnTranslate edge u result =>
    pre_actual_external_receipt
      (pre_translate_source EB EBE EN EE EV EU a adapters) (edge,u) result trace allowance
  | PrnKilled edge u result =>
    pre_actual_external_receipt
      (pre_kill_source EB EBE EN EE EV EU a adapters) (edge,u) result trace allowance
  | PrnTarget edge result =>
    pre_actual_external_receipt
      (pre_point_target_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PrnBlockTarget edge result =>
    pre_actual_external_receipt
      (pre_block_target_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PrnBlockSource edge result =>
    pre_actual_external_receipt
      (pre_block_source_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PrnParameter block result =>
    pre_actual_external_receipt
      (pre_parameter_source EB EBE EN EE EV EU a adapters) block result trace allowance
  | PrnPoints block result =>
    pre_actual_external_receipt
      (pre_points_source EB EBE EN EE EV EU a adapters) block result trace allowance
  | PrnInstructions block result =>
    pre_actual_external_receipt
      (pre_instructions_source EB EBE EN EE EV EU a adapters) block result trace allowance
  | PrnOperands u result =>
    pre_actual_external_receipt
      (pre_operands_source EB EBE EN EE EV EU a adapters) u result trace allowance
  | PrnDefinitions edge result =>
    pre_actual_external_receipt
      (pre_definitions_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PrnOut point result =>
    pre_actual_external_receipt
      (pre_point_out_source EB EBE EN EE EV EU a adapters) point result trace allowance
  | PrnExitPoint point result =>
    pre_actual_external_receipt
      (pre_exit_source EB EBE EN EE EV EU a adapters) point result trace allowance
  | PrnEncodeU input output => us input output trace allowance
  | PrnEncodeE input output => es input output trace allowance
  | _ => pre_internal_receipt trace allowance
  end.

(** Phi receipts attach the original callbacks and nested rename calls to the recorded work. *)
Definition pre_phi_call_receipt (call : pre_phi_call B BE N E V U) trace allowance : Prop :=
  match call with
  | PhiOccurrences nested => pre_actual_map_receipt us nested trace allowance
  | PhiParameters nested => pre_actual_map_receipt vs nested trace allowance
  | PhiBlocks nested => pre_actual_map_receipt bs nested trace allowance
  | PhiPairs nested => pre_actual_map_receipt ubu nested trace allowance
  | PhiFrontier nested => pre_actual_map_receipt bs nested trace allowance
  | PhiPred nested => pre_actual_map_receipt bs nested trace allowance
  | PhiHome value result =>
    pre_actual_external_receipt
      (pre_home_source EB EBE EN EE EV EU a adapters) value result trace allowance
  | PhiBlockOf point result =>
    pre_actual_external_receipt
      (pre_block_of_source EB EBE EN EE EV EU a adapters) point result trace allowance
  | PhiSource edge result =>
    pre_actual_external_receipt
      (pre_point_source_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PhiBlockParams block result =>
    pre_actual_external_receipt
      (pre_block_params_source EB EBE EN EE EV EU a adapters) block result trace allowance
  | PhiRename nested => pre_rename_call_receipt nested trace allowance
  | _ => pre_internal_receipt trace allowance
  end.

(** Finalizer receipts attach original callbacks and map encoders to their actual calls. *)
Definition pre_finalize_call_receipt (call : pre_finalize_call B BE N E U) trace allowance : Prop :=
  match call with
  | PfFlags nested => pre_actual_map_receipt bu nested trace allowance
  | PfScope nested => pre_actual_map_receipt pre_frg_version_receipt nested trace allowance
  | PfReload nested => pre_actual_map_receipt es nested trace allowance
  | PfPhi nested => pre_actual_map_receipt eeu nested trace allowance
  | PfOccurrence nested => pre_actual_map_receipt es nested trace allowance
  | PfDom nested => pre_actual_map_receipt ns nested trace allowance
  | PfExpr nested => pre_actual_map_receipt us nested trace allowance
  | PfNodeRows nested => pre_actual_map_receipt ns nested trace allowance
  | PfArguments nested => pre_actual_map_receipt ns nested trace allowance
  | PfEdges nested => pre_actual_map_receipt ns nested trace allowance
  | PfIdom nested => pre_actual_map_receipt ns nested trace allowance
  | PfOutputs nested => pre_actual_map_receipt ns nested trace allowance
  | PfInitial u result =>
    pre_actual_external_receipt
      (pre_initial_source EB EBE EN EE EV EU a adapters) u result trace allowance
  | PfRecomputed edge result =>
    pre_actual_external_receipt
      (pre_recomputed_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PfPure u result =>
    pre_actual_external_receipt
      (pre_pure_source EB EBE EN EE EV EU a adapters) u result trace allowance
  | PfTranslate edge u result =>
    pre_actual_external_receipt
      (pre_translate_source EB EBE EN EE EV EU a adapters) (edge,u) result trace allowance
  | PfKill edge u result =>
    pre_actual_external_receipt
      (pre_kill_source EB EBE EN EE EV EU a adapters) (edge,u) result trace allowance
  | PfParameter block result =>
    pre_actual_external_receipt
      (pre_parameter_source EB EBE EN EE EV EU a adapters) block result trace allowance
  | PfSource edge result =>
    pre_actual_external_receipt
      (pre_point_source_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PfTarget edge result =>
    pre_actual_external_receipt
      (pre_point_target_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PfExpressionTarget edge result =>
    pre_actual_external_receipt
      (pre_expression_target_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | _ => pre_internal_receipt trace allowance
  end.

(** Row preparation receipts retain point-edge lookups and nested finalizer callbacks. *)
Definition pre_rows_call_receipt (call : pre_rows_call B BE N E U) trace allowance : Prop :=
  match call with
  | PrPointIndex nested => pre_actual_map_receipt bes nested trace allowance
  | PrLinks nested => pre_actual_map_receipt bube nested trace allowance
  | PrPhis nested => pre_actual_map_receipt bu nested trace allowance
  | PrOut point result =>
    pre_actual_external_receipt
      (pre_point_out_source EB EBE EN EE EV EU a adapters) point result trace allowance
  | PrBlockEdge edge result =>
    pre_actual_external_receipt
      (pre_block_edge_of_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  | PrFinalize nested => pre_finalize_call_receipt nested trace allowance
  end.

(** Materialization receipts retain actual encoder and recomputation calls. *)
Definition pre_materialize_call_receipt (call : pre_materialize_call E U) trace allowance : Prop :=
  match call with
  | PreMaterializePhi nested => pre_actual_map_receipt eeu nested trace allowance
  | PreMaterializeReload nested => pre_actual_map_receipt es nested trace allowance
  | PreMaterializeRows nested => pre_actual_map_receipt es nested trace allowance
  | PreMaterializeSet nested => pre_actual_map_receipt us nested trace allowance
  | PreMaterializeRecomputed edge result =>
    pre_actual_external_receipt
      (pre_recomputed_source EB EBE EN EE EV EU a adapters) edge result trace allowance
  end.

(** The internal phi graph expands all nested source callbacks from this same construction. *)
Inductive pre_phi_graph_call_receipt : pre_phi_graph_call B BE N E V U ->
    list audit_external_frame -> nat -> Prop :=
  | PrePhiGraphBody call trace allowance :
    pre_phi_call_receipt call trace allowance ->
    pre_phi_graph_call_receipt (PhiGraphBody call) trace allowance
  | PrePhiGraphOut key result units events trace allowance :
    pre_fixed_calls_receipt (pre_audit_event_receipt pre_phi_call_receipt)
      events trace allowance ->
    pre_phi_graph_call_receipt (PhiGraphOut key result units events) trace allowance
  | PrePhiGraphEncode key code trace allowance :
    ubu key code trace allowance ->
    pre_phi_graph_call_receipt (PhiGraphEncode key code) trace allowance
  | PrePhiGraphTarget edge target :
    pre_phi_graph_call_receipt (PhiGraphTarget edge target) [] 0
  | PrePhiGraphPrepare graph events trace allowance :
    pre_fixed_calls_receipt (fun event => pre_fixed_calls_receipt pre_phi_graph_call_receipt
      (pre_prepare_callback_calls event)) events trace allowance ->
    pre_phi_graph_call_receipt (PhiGraphPrepare graph events) trace allowance
  | PrePhiGraphDfs graph events trace allowance :
    pre_fixed_calls_receipt (fun event => pre_fixed_calls_receipt pre_phi_graph_call_receipt
      (pre_dfs_callback_calls event)) events trace allowance ->
    pre_phi_graph_call_receipt (PhiGraphDfs graph events) trace allowance.

(** FRG receipts follow the actual family, phi, rename and parent-map child calls. *)
Definition pre_frg_call_receipt (call : pre_frg_call B BE N E V U) trace allowance : Prop :=
  match call with
  | FrgFamily nested => pre_family_call_receipt nested trace allowance
  | FrgPhi nested => pre_phi_graph_call_receipt nested trace allowance
  | FrgRename nested => pre_rename_call_receipt nested trace allowance
  | FrgParents nested => pre_actual_map_receipt bs nested trace allowance
  | FrgFuel _ _ _ => pre_internal_receipt trace allowance
  end.

(** Reset closure callbacks are concrete map/encode/projection bodies from the actual graph. *)
Inductive pre_closure_call_receipt : pre_closure_call (B * U) ->
    list audit_external_frame -> nat -> Prop :=
  | PreClosureRowsReceipt call trace allowance :
    pre_actual_map_receipt bu call trace allowance ->
    pre_closure_call_receipt (PreClosureRows call) trace allowance
  | PreClosureSetReceipt call trace allowance :
    pre_actual_map_receipt bu call trace allowance ->
    pre_closure_call_receipt (PreClosureSet call) trace allowance
  | PreClosureOutReceipt key result units events receipts :
    Forall2 (fun event receipt =>
      pre_closure_event_receipt event (fst receipt) (snd receipt)) events receipts ->
    pre_closure_call_receipt (PreClosureOut key result units events)
      (pre_receipt_trace receipts) (pre_receipt_allowance receipts)
  | PreClosureEncodeReceipt key code trace allowance :
    bu key code trace allowance ->
    pre_closure_call_receipt (PreClosureEncode key code) trace allowance
  | PreClosureTargetReceipt edge target :
    pre_closure_call_receipt (PreClosureTarget edge target) [] 0
  | PreClosurePrepareReceipt graph events trace allowance :
    pre_fixed_calls_receipt (fun event => pre_fixed_calls_receipt pre_closure_call_receipt
      (pre_prepare_callback_calls event)) events trace allowance ->
    pre_closure_call_receipt (PreClosurePrepare graph events) trace allowance
  | PreClosureDfsReceipt graph events trace allowance :
    pre_fixed_calls_receipt (fun event => pre_fixed_calls_receipt pre_closure_call_receipt
      (pre_dfs_callback_calls event)) events trace allowance ->
    pre_closure_call_receipt (PreClosureDfs graph events) trace allowance
with pre_closure_event_receipt : audit_event (pre_closure_call (B * U)) ->
    list audit_external_frame -> nat -> Prop :=
  | PreClosureEventCall call trace allowance :
    pre_closure_call_receipt call trace allowance ->
    pre_closure_event_receipt (AuditCall call) trace allowance
  | PreClosureEventCase site operands :
    pre_closure_event_receipt (AuditCase site operands) [] 0
  | PreClosureEventConstruct site operands :
    pre_closure_event_receipt (AuditConstruct site operands) [] 0
  | PreClosureEventKeyBit bit : pre_closure_event_receipt (AuditKeyBit bit) [] 0
  | PreClosureEventArithmetic site operands :
    pre_closure_event_receipt (AuditArithmetic site operands) [] 0.

(** Solver receipts follow the actual closure and flag-map child calls. *)
Definition pre_solver_call_receipt (call : pre_solver_call B BE E U) trace allowance : Prop :=
  match call with
  | PreSolverClosure nested => pre_closure_call_receipt nested trace allowance
  | PreSolverFlags nested => pre_actual_map_receipt bu nested trace allowance
  | PreSolverKeys nested => pre_actual_map_receipt bu nested trace allowance
  | PreSolverLinks nested => pre_actual_map_receipt bube nested trace allowance
  end.

(** A body receipt delegates to the actual PRE phase represented by the call. *)
Definition pre_body_call_receipt (call : pre_place_body_call B BE N E V U) trace allowance
    : Prop :=
  match call with
  | PreBodyFrg nested => pre_frg_call_receipt nested trace allowance
  | PreBodySolve nested => pre_solver_call_receipt nested trace allowance
  | PreBodyFinalize nested => pre_rows_call_receipt nested trace allowance
  | PreBodyMaterialize nested => pre_materialize_call_receipt nested trace allowance
  end.

(** Finite-check receipts retain the actual checker, recomputation and encoder calls. *)
Definition pre_finite_call_receipt (accept : pre_plan E U -> bool)
    (accept_source : audit_external_adapter (pre_plan E U) bool accept)
    (call : pre_finite_call E U) trace allowance : Prop :=
  match call with
  | PfcRows nested => pre_actual_map_receipt es nested trace allowance
  | PfcExprs nested => pre_actual_map_receipt us nested trace allowance
  | PfcReload nested => pre_actual_map_receipt es nested trace allowance
  | PfcPhi nested => pre_actual_map_receipt eeu nested trace allowance
  | PfcRecomputed edge output =>
    pre_actual_external_receipt
      (pre_recomputed_source EB EBE EN EE EV EU a adapters) edge output trace allowance
  | PfcAccept plan output =>
    pre_actual_external_receipt accept_source plan output trace allowance
  | PfcNatAdd _ _ _ | PfcNatLe _ _ _ => pre_internal_receipt trace allowance
  end.

(** Under the view and acceptance adapter laws, enumeration, minimum checking and correction
    have actual callback receipts and their respective input-budget-plus-allowance bounds. *)
Definition audit_pre_certificate_body_source_statement : Prop :=
  audit_pre_view_adapter_laws EB EBE EN EE EV EU a adapters ->
  forall edges exprs chosen candidates accept
    (accept_source : audit_external_adapter (pre_plan E U) bool accept),
  audit_external_adapter_laws accept_source ->
  let eb := external_input_budget (pre_edge_encoder EB EBE EN EE EV EU a adapters) in
  let ub := external_input_budget (pre_expr_encoder EB EBE EN EE EV EU a adapters) in
  let enumeration := pre_enumerate_counted EE EU eb ub edges exprs in
  let minimum := pre_minimum_check_counted EE EU eb ub edges exprs
    (pre_expression a) chosen candidates accept in
  let corrected := pre_choose_best_counted EE EU eb ub edges exprs
    (pre_expression a) accept candidates in
  exists enumeration_receipts minimum_receipts correction_receipts,
    Forall2 (fun event receipt => pre_audit_event_receipt
      (pre_finite_call_receipt accept accept_source) event (fst receipt) (snd receipt))
      (exact_events enumeration) enumeration_receipts /\
    Forall2 (fun event receipt => pre_audit_event_receipt
      (pre_finite_call_receipt accept accept_source) event (fst receipt) (snd receipt))
      (exact_events minimum) minimum_receipts /\
    Forall2 (fun event receipt => pre_audit_event_receipt
      (pre_finite_call_receipt accept accept_source) event (fst receipt) (snd receipt))
      (exact_events corrected) correction_receipts /\
    exact_units enumeration + pre_receipt_work enumeration_receipts <=
      64 * pre_enumerate_input_budget EE EU eb ub edges exprs +
      pre_receipt_allowance enumeration_receipts /\
    exact_units minimum + pre_receipt_work minimum_receipts <=
      64 * pre_minimum_input_budget EE EU eb ub edges exprs (length candidates) +
      pre_receipt_allowance minimum_receipts /\
    exact_units corrected + pre_receipt_work correction_receipts <=
      64 * pre_minimum_input_budget EE EU eb ub edges exprs (length candidates) +
      pre_receipt_allowance correction_receipts.

End PrePhaseBodyReceipts.

(** * Original callback leaves of the fixed graph source models *)
Definition pre_virtual_callback_calls {V E Call}
    (event : audit_virtual_full_call V E Call) : list Call :=
  match event with
  | VirtualFullOut _ _ body | VirtualFullTarget _ _ body |
      VirtualFullSource _ _ body | VirtualFullEncode _ _ body => body
  | VirtualFullEntry (VirtualEntriesSet call) => pre_set_callback_calls call
  | _ => []
  end.

Definition pre_semi_callback_calls {V Call} (event : audit_semi_nested_event V Call)
    : list Call :=
  match event with
  | SemiNestedVertexMap call => pre_map_callback_calls call
  | SemiNestedRankMap call => pre_map_callback_calls call
  | _ => []
  end.

Definition pre_semi_producer_callback_calls {V E Call}
    (event : audit_semi_producer_nested_event V E Call) : list Call :=
  match event with
  | SemiProducerSource _ _ body => body
  | SemiProducerInner nested => pre_semi_callback_calls nested
  | SemiProducerTreeMap call => pre_map_callback_calls call
  | SemiProducerPredMap call => pre_map_callback_calls call
  | _ => []
  end.

Definition pre_lt_callback_calls {V E Call} (event : audit_lt_nested_event V E Call)
    : list Call :=
  match event with
  | LtNestedSemi call => pre_semi_callback_calls call
  | LtNestedProducer call => pre_semi_producer_callback_calls call
  | LtNestedBucket call => pre_map_callback_calls call
  | LtNestedTree call => pre_map_callback_calls call
  | LtNestedSource _ _ body | LtNestedEncode _ _ body => body
  | _ => []
  end.

Definition pre_erase_callback_calls {V Call} (event : audit_erase_nested_event V Call)
    : list Call :=
  match event with
  | EraseNestedSet call => pre_map_callback_calls call
  | _ => []
  end.

Definition pre_dom_body_callback_calls {V Call} (event : audit_dom_source_body V Call)
    : list Call :=
  match event with
  | DomSourceBodyMap call => pre_map_callback_calls call
  | DomSourceBodyEncode _ _ body => body
  | _ => []
  end.

Definition pre_dom_callback_calls {V E Call} (event : audit_dom_source_event V E Call)
    : list Call :=
  match event with
  | DomSourceInitialDfs call => pre_dfs_callback_calls call
  | DomSourceChild call => pre_map_callback_calls call
  | DomSourceParent call => pre_map_callback_calls call
  | DomSourcePrepare call =>
    flat_map pre_dom_body_callback_calls (pre_prepare_callback_calls call)
  | DomSourceDfs call => flat_map pre_dom_body_callback_calls (pre_dfs_callback_calls call)
  | _ => []
  end.

Definition pre_frontier_callback_calls {V E Call} (event : audit_frontier_source_event V E Call)
    : list Call :=
  match event with
  | FrontierSourceDfs call => pre_dfs_callback_calls call
  | FrontierSourceSource _ _ body | FrontierSourceTarget _ _ body => body
  | FrontierSourceParent call => pre_map_callback_calls call
  | FrontierSourceRank call => pre_map_callback_calls call
  | FrontierSourcePred call => pre_map_callback_calls call
  | FrontierSourceRows call => pre_map_callback_calls call
  | FrontierSourceSet call => pre_set_callback_calls call
  | _ => []
  end.

Definition pre_dom_actual_callback_calls {V E Call EV}
    (data : pre_dom_source_data V E Call EV) : list Call :=
  flat_map pre_virtual_callback_calls
    (flat_map pre_prepare_callback_calls (pre_dom_prepare_events data)) ++
  flat_map pre_virtual_callback_calls
    (flat_map pre_dfs_callback_calls (pre_dom_dfs_events data)) ++
  flat_map pre_virtual_callback_calls
    (flat_map pre_semi_producer_callback_calls (pre_dom_semi data)) ++
  flat_map pre_virtual_callback_calls
    (flat_map pre_lt_callback_calls (pre_dom_lt data)) ++
  flat_map pre_erase_callback_calls (pre_dom_erase data) ++
  flat_map pre_dom_callback_calls (audit_dom_source_events (pre_dom_search data)).

Section PreWholeBodySource.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (adapters : audit_pre_view_adapters EB EBE EN EE EV EU a).

(** The two original graphs, six encoder budgets and their corresponding dominance witnesses. *)
Let bg := block_graph (pre_ssa_points a).

Let pg := live_graph (point_model (pre_ssa_points a)).

Let bb := external_input_budget (pre_block_encoder EB EBE EN EE EV EU a adapters).

Let beb := external_input_budget (pre_block_edge_encoder EB EBE EN EE EV EU a adapters).

Let nb := external_input_budget (pre_point_encoder EB EBE EN EE EV EU a adapters).

Let eb := external_input_budget (pre_edge_encoder EB EBE EN EE EV EU a adapters).

Let vb := external_input_budget (pre_value_encoder EB EBE EN EE EV EU a adapters).

Let ub := external_input_budget (pre_expr_encoder EB EBE EN EE EV EU a adapters).

Let BD := pre_dom_source_data B BE (pre_graph_view_call B BE) EB.

Let ND := pre_dom_source_data N E (pre_graph_view_call N E) EN.

(** A block graph receipt binds each recorded graph operation to its original adapter. *)
Definition pre_block_view_receipt (call : pre_graph_view_call B BE) trace allowance : Prop :=
  match call with
  | PreViewOut input output =>
    pre_actual_external_receipt
      (pre_block_out_source EB EBE EN EE EV EU a adapters) input output trace allowance
  | PreViewSource input output =>
    pre_actual_external_receipt
      (pre_block_source_source EB EBE EN EE EV EU a adapters) input output trace allowance
  | PreViewTarget input output =>
    pre_actual_external_receipt
      (pre_block_target_source EB EBE EN EE EV EU a adapters) input output trace allowance
  | PreViewEncode input output =>
    pre_actual_external_receipt
      (pre_block_encoder EB EBE EN EE EV EU a adapters) input output trace allowance
  end.

(** A point graph receipt binds each recorded graph operation to its original adapter. *)
Definition pre_point_view_receipt (call : pre_graph_view_call N E) trace allowance : Prop :=
  match call with
  | PreViewOut input output =>
    pre_actual_external_receipt
      (pre_point_out_source EB EBE EN EE EV EU a adapters) input output trace allowance
  | PreViewSource input output =>
    pre_actual_external_receipt
      (pre_point_source_source EB EBE EN EE EV EU a adapters) input output trace allowance
  | PreViewTarget input output =>
    pre_actual_external_receipt
      (pre_point_target_source EB EBE EN EE EV EU a adapters) input output trace allowance
  | PreViewEncode input output =>
    pre_actual_external_receipt
      (pre_point_encoder EB EBE EN EE EV EU a adapters) input output trace allowance
  end.

(** One placement run shares each graph witness and each literal counted phase exactly once. *)
Definition pre_place_graph_body_run (bd : BD) (nd : ND) (result : pre_plan E U)
    (work allowance : nat) : Prop :=
  let '(p,prepare_b) := audit_prepare_source_counted EB bg (pre_view_prepare EB bg) in
  let '(df,frontier_events) := audit_frontier_source_counted (pre_view_frontier EB bg)
    p (pre_dom_result bd) in
  let '(points,prepare_n) := audit_prepare_source_counted EN pg (pre_view_prepare EN pg) in
  let body := pre_place_from_backends_counted EB EBE EN EE EV EU a bb beb nb eb vb ub
    p (pre_dom_result bd) df points (pre_dom_result nd)
    (preorder (audit_dom_source_result (pre_dom_search nd))) in
  pre_dom_fixed_run p (pre_view_virtual EB bg) (pre_view_source bg) bd /\
  pre_dom_fixed_run points (pre_view_virtual EN pg) (pre_view_source pg) nd /\
  exists block_receipts point_receipts body_receipts,
    Forall2 (fun call receipt => pre_block_view_receipt call (fst receipt) (snd receipt))
      (flat_map pre_prepare_callback_calls prepare_b ++ pre_dom_actual_callback_calls bd ++
        flat_map pre_frontier_callback_calls frontier_events) block_receipts /\
    Forall2 (fun call receipt => pre_point_view_receipt call (fst receipt) (snd receipt))
      (flat_map pre_prepare_callback_calls prepare_n ++ pre_dom_actual_callback_calls nd)
      point_receipts /\
    Forall2 (fun call receipt => pre_audit_event_receipt
      (pre_body_call_receipt EB EBE EN EE EV EU a adapters) call (fst receipt) (snd receipt))
      (exact_events body) body_receipts /\
    result = exact_value body /\
    work = 2048 + audit_prepare_source_work (pre_view_weight bb) prepare_b +
      pre_dom_whole_work (pre_view_weight bb) bd +
      audit_frontier_source_work (pre_view_weight bb) frontier_events +
      audit_prepare_source_work (pre_view_weight nb) prepare_n +
      pre_dom_whole_work (pre_view_weight nb) nd + exact_units body +
      pre_receipt_work block_receipts + pre_receipt_work point_receipts +
      pre_receipt_work body_receipts /\
    allowance = pre_receipt_allowance block_receipts +
      pre_receipt_allowance point_receipts + pre_receipt_allowance body_receipts.

(** Whole source work includes original callbacks under per-function source laws. *)
Definition audit_pre_place_body_source_statement : Prop :=
  audit_pre_view_adapter_laws EB EBE EN EE EV EU a adapters ->
  pre_expr_ssa_laws EV a -> exists bd nd result work allowance,
    pre_place_graph_body_run bd nd result work allowance /\
    result = ssa_pre_place EB EBE EN EE EV EU a /\
    work <= 64 * pre_place_graph_budget EB EBE EN EE EV EU a bb beb nb eb vb ub bd nd + allowance.

End PreWholeBodySource.

(** Every actual PRE callback body is charged under local original-view source laws. *)
Definition audit_pre_body_source_family_statement : Prop :=
  forall S O B BE N E V K C U (EB : encoding B) (EBE : encoding BE) (EN : encoding N)
    (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (adapters : audit_pre_view_adapters EB EBE EN EE EV EU a),
    audit_pre_place_body_source_statement EB EBE EN EE EV EU a adapters /\
    audit_pre_certificate_body_source_statement EB EBE EN EE EV EU a adapters.

(** The final source obligation combines exact caller models with genuine callback bodies. *)
Definition audit_pre_full_source_statement : Prop :=
  audit_pre_caller_source_statement /\ audit_pre_body_source_family_statement.
