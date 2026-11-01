(** * RewriteAuditProofFactPublic

    This module interprets fact strategy programs and states factful source-run properties.
    For example, a return program containing None interprets to None.
    Builds on: RewriteAuditProofFacts and
    RewriteAuditIndexPrograms. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofFacts RewriteAuditProofRun RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_rp_fact_plain {K Sort V H F} (view : rw_snapshot_view K Sort V) (lookup : rw_id -> F)
    (program : rw_rp_fact_program K Sort V H F) : option (rw_attempt K Sort V H) :=
  match program with
  | RPFactReturn offer _ => offer
  | RPFactView _ request next =>
    rw_rp_fact_plain view lookup (next (rw_rp_view_plain_request view request))
  | RPFactLookup _ id next => rw_rp_fact_plain view lookup (next (lookup id))
  end.

(** The fact strategy program agrees with the supplied strategy on every observed
    tracked state and fact store. *)
Definition rw_rp_fact_strategy_agrees {K Sort V H C F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (an : rw_analysis K Sort V C F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F)
    (strategy : rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) : Prop :=
  forall (state : rw_tracked_state K Sort V H) facts,
    let view := rw_fact_observe EK ES EV an state facts in
    rw_rp_fact_plain (rw_fact_snapshot view) (rw_fact_lookup view)
      (rw_rp_fact_strategy_program adapter) = strategy view.

(** A fact-source run starting with valid facts retains facts valid for its final graph. *)
Definition rw_rp_fact_run_valid_statement : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules (an : rw_analysis K Sort V C F)
    (admissible : rw_semantics K Sort V C -> Prop) adapter fuel state facts,
    rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
    let '((output, retained), _) := rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks
      rules (rw_fact_unknown an) adapter fuel (state, facts) in
    rw_fact_store_valid admissible an (rw_tracked_graph (rw_tracked_final output)) retained.

(** The fact-source run event count plus one when stopped is bounded by its fuel. *)
Definition rw_rp_fact_callback_bound_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules (unknown : F) adapter fuel input,
    let '((output, _), _) := rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks
      rules unknown adapter fuel input in
    (N.of_nat (length (rw_tracked_events output)) +
      match rw_tracked_stop output with
      | RWStopped => 1%N
      | RWFuelExhausted => 0%N
      end <= fuel)%N.
