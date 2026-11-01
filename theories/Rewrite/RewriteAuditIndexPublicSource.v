(** * Fixed public Rewrite source family

    This module states a source-work bound for the fixed public indexed runner.
    For example, at fuel 0 the iteration premise is vacuous, but the other assumptions
    still require a matching source result with bounded work.
    Builds on: RewriteAuditIndexPlainPublic and RewriteAuditIndexExternal. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions4 RewriteAuditIndexExternal
  RewriteAuditIndexPlainPublic RewriteAuditIndexPrepareReference RewriteAuditIndexProgramLaws
  RewriteAuditIndexPrograms RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditIndexRun RewriteAuditIndexTickReference RewriteAuditIndexWholeContracts
  RewriteAuditPlainCore1 RewriteAuditPlainPrimitives RewriteAuditQueueReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** With agreeing encoders and callbacks, a strategy adapter agreement and execution witness,
    well-formed rules, input atom bounds, and bounded strategy control, queries, and offers,
    the index result has a matching source run with bounded work. *)
Definition rw_ri_public_source_cost_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter strategy execution fuel graph width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
    rw_rp_strategy_adapter_laws EK ES EV adapter strategy (execution strategy) ->
    let actual :=
      RewriteAuditIndexPlainPublic.rw_index_run EK ES EV EH sig rules strategy fuel graph in
    let '(result, initial_events, events) := actual in
    rw_whole_graph_atoms op sort value width body graph ->
    rw_whole_rules_external op sort value hole callbacks width body rules ->
    (let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
      let ready := fst (rw_index_rebuild EK ES EV (rw_index_build EK ES EV graph)) in
      forall n, (N.of_nat n < fuel)%N ->
        let run := Nat.iter n
          (rw_plain_rw_ri_run_once EK ES EV EH (rw_plain_callbacks_of sig) table
            (fun state => strategy (rw_index_view EK ES EV state))) (RwRiRunner ready false nil) in
        rw_ri_runner_stopped run = false ->
        let view := rw_index_view EK ES EV (rw_ri_runner_state run) in
        rw_whole_view_control view (rw_rp_strategy_program adapter) <= body /\
        rw_whole_view_queries op value width body view (rw_rp_strategy_program adapter) /\
        match rw_rp_view_plain view (rw_rp_strategy_program adapter) with
        | None => True
        | Some attempt =>
          rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
        end) ->
    exists work,
      rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph = (actual, work) /\
      (N.of_nat work <= rw_whole_source_ceiling fuel
        (rw_ri_whole_operand_dimension rules graph result events) width body)%N.
