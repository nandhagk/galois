(** * Fixed public Rewrite source family

    This module states source-cost correspondence for tracked, selected, and factful runs.
    For example, at zero fuel the tracked-run statement still requires a source-work witness
    under its encoder, callback, strategy, typing, and atom-bound premises.
    Builds on: fixed plain builders, exact public contracts and full source cost models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions4
  RewriteAuditIndexExternal RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditPlainCore1
  RewriteAuditPlainCore3 RewriteAuditPlainCore4 RewriteAuditPlainPrimitives
  RewriteAuditProofDimensions2 RewriteAuditProofDimensions3 RewriteAuditProofFactPublic
  RewriteAuditProofFactWholeContracts RewriteAuditProofFacts RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofSelected RewriteAuditProofSemantic RewriteAuditProofTick
  RewriteAuditProofWholeContracts RewriteAuditQueueReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** With agreeing encoders and callbacks, a strategy adapter agreement and execution witness,
    well-formed rules, a typed bounded seed, and bounded strategy control, queries, and offers,
    the tracked result has a matching source run with bounded work. *)
Definition rw_rp_public_source_cost_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter strategy execution fuel seed width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
    rw_typed sig seed ->
    rw_rp_strategy_adapter_laws EK ES EV adapter strategy (execution strategy) ->
    let actual := RewriteAuditProofPlainPublic.rw_tracked_run EK ES EV EH sig rules strategy fuel
      seed in
    rw_whole_term_atoms op sort value width body seed ->
    rw_whole_rules_external op sort value hole callbacks width body rules ->
    (let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
      let initial := snd (@rw_plain_rw_rp_seed_atomic K Sort V H EK ES EV EK EV seed) in
      let ready := fst (RewriteAuditProofPlainPublic.rw_tracked_rebuild EK ES EV 0 initial) in
      forall n, (N.of_nat n < fuel)%N ->
        let run := Nat.iter n
          (rw_plain_rw_rp_run_once EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) table
            (fun state => strategy (rw_index_view EK ES EV state)))
          (RwRpRunState ready false 0 nil) in
        rw_rp_stopped run = false ->
        let view := rw_index_view EK ES EV (rw_tracked_machine (rw_rp_current run)) in
        rw_whole_view_control view (rw_rp_strategy_program adapter) <= body /\
        rw_whole_view_queries op value width body view (rw_rp_strategy_program adapter) /\
        match rw_rp_view_plain view (rw_rp_strategy_program adapter) with
        | None => True
        | Some attempt =>
          rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
        end) ->
    exists work,
      rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed =
        (actual, work) /\
      (N.of_nat work <= rw_whole_source_ceiling fuel
        (rw_rp_whole_operand_dimension rules seed (snd actual)) width body)%N.

(** With agreeing encoders and bounded index, provenance, and endpoint atoms, the plain selected
    result has a source work witness within its dimension-dependent ceiling. *)
Definition rw_rp_public_selected_source_cost_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H)
    root seed tree width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_whole_index_atoms op sort value width body (rw_tracked_machine state) ->
    rw_whole_provenance_atoms op sort value width body (rw_tracked_provenance state) ->
    rw_whole_term_atoms op sort value width body seed ->
    rw_whole_term_atoms op sort value width body tree ->
    let actual := RewriteAuditProofPlainPublic.rw_selected_explanation EK ES EV state root seed
      tree in
    let dimension := S (rw_whole_tracked_dimension state + Pos.size_nat root +
      rw_whole_term_dimension seed + rw_whole_term_dimension tree + width) in
    exists work,
      rw_rp_selected_atomic op sort value state root seed tree = (actual, work) /\
      (N.of_nat work <= 4294967296 * (1 + N.of_nat body) * N.pow (N.of_nat dimension)
        (128 + 16 * N.of_nat (rw_whole_term_dimension seed + rw_whole_term_dimension tree)))%N.

(** With agreeing adapters and fact strategy execution, well-formed bounded rules, bounded initial
    atoms, and bounded strategy control, queries, and offers, the factful result has a matching
    source run with bounded work. *)
Definition rw_rp_public_fact_source_cost_statement : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules (an : rw_analysis K Sort V C F) adapter strategy execution fuel initial facts width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
    rw_rp_fact_strategy_agrees EK ES EV an adapter strategy ->
    (forall (state : rw_tracked_state K Sort V H) facts,
      execution strategy (rw_fact_observe EK ES EV an state facts)
        (rw_rp_fact_strategy_program adapter)) ->
    let actual := RewriteAuditProofPlainPublic.rw_factful_run EK ES EV EH sig rules an strategy fuel
      (initial, facts) in
    rw_whole_tracked_atoms op sort value width body initial ->
    rw_whole_rules_external op sort value hole callbacks width body rules ->
    (let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
      let ready := fst (RewriteAuditProofPlainPublic.rw_tracked_rebuild EK ES EV 0 initial) in
      let callback := fun state unknown retained => strategy
        (RWFactView (rw_index_view EK ES EV state)
          (fun id =>
            match Map.get positive_encoding id retained with
            | Some fact => fact
            | None => unknown
            end)) in
      forall n, (N.of_nat n < fuel)%N ->
        let '(run, retained) := Nat.iter n
          (rw_plain_rw_rp_fact_run_once EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) table
            (rw_fact_unknown an) callback) (RwRpRunState ready false 0 nil, Map.empty) in
        rw_rp_stopped run = false ->
        let view := rw_index_view EK ES EV (rw_tracked_machine (rw_rp_current run)) in
        rw_whole_fact_control view (rw_fact_unknown an) (rw_rp_fact_strategy_program adapter) <=
          body /\
        rw_whole_fact_queries op value width body view (rw_fact_unknown an)
          (rw_rp_fact_strategy_program adapter) /\
        match rw_rp_fact_plain view
          (fun id =>
            match Map.get positive_encoding id retained with
            | Some fact => fact
            | None => rw_fact_unknown an
            end) (rw_rp_fact_strategy_program adapter) with
        | None => True
        | Some attempt =>
          rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
        end) ->
    exists work,
      rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules (rw_fact_unknown an)
        adapter fuel (initial, facts) = (actual, work) /\
      (N.of_nat work <= rw_whole_source_ceiling fuel
        (rw_fact_whole_operand_dimension rules initial facts (fst actual) (snd actual))
        width body)%N.
