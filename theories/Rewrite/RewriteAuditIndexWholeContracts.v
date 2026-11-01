(** * RewriteAuditIndexWholeContracts

    Defines whole-invocation bounds and prospective work ceilings for index runs and matching.
    For example, an empty event list makes the invocation's event-wise bound vacuous.
    Builds on: RewriteAuditIndexExternal and
    RewriteAuditIndexEventEnvelope. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions3
  RewriteAuditIndexDimensions4 RewriteAuditIndexEventEnvelope RewriteAuditIndexExternal
  RewriteAuditIndexMatch RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditIndexRun RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_whole_operand_dimension {K Sort V H} (rules : list (rw_rule K Sort V H))
    (input : rw_graph K Sort V) (result : rw_run_result K Sort V)
    (events : list (rw_run_event K Sort V H)) : nat :=
  S (rw_whole_graph_dimension input + rw_whole_graph_dimension (rw_run_graph result) +
    rw_whole_rules_dimension rules + rw_whole_event_attempt_dimension events).

(** The graph-only invocation bounds input and output atoms, rule and event operations,
    and strategy operations for the observed operand dimension. *)
Record rw_ri_whole_invocation {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (adapter : rw_rp_strategy_adapter K Sort V H)
    (input : rw_graph K Sort V) (result : rw_run_result K Sort V)
    (events : list (rw_run_event K Sort V H)) (width body : nat) : Prop := RwRiWholeInvocation {
  (** Input-graph atoms satisfy the encoder width and work bounds. *)
  rw_ri_whole_input_atoms : rw_whole_graph_atoms op sort value width body input;
  (** Output-graph atoms satisfy the encoder width and work bounds. *)
  rw_ri_whole_output_atoms : rw_whole_graph_atoms op sort value width body (rw_run_graph result);
  (** Listed rule patterns and holes meet encoder bounds, and listed holes meet callback bounds. *)
  rw_ri_whole_rules_external : rw_whole_rules_external op sort value hole callbacks
    width body rules;
  (** Each attempt bounds binding encoders and term callbacks; a listed rule also bounds
      guard control and queries. *)
  rw_ri_whole_event_external : Forall
    (rw_whole_event_external EH op sort value hole callbacks width body rules) events;
  (** Strategy control and visited view queries meet the operand and body bounds. *)
  rw_ri_whole_strategy_external : rw_whole_strategy_external EK ES EV op sort value
    (rw_ri_whole_operand_dimension rules input result events) width body adapter
}.

(** With agreeing encoders, global variable/operator callbacks and listed-rule hole/guard
    callbacks, well-formed rules and graph, and the whole invocation premise, source work is
    bounded by the whole-source ceiling. *)
Definition rw_ri_whole_bound_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter fuel graph width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
    rw_graph_wf sig graph ->
    let '((result, _, events), work) :=
      rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph in
    rw_ri_whole_invocation EK ES EV EH op sort value hole callbacks rules adapter graph result
      events width body ->
    (N.of_nat work <= rw_whole_source_ceiling fuel
      (rw_ri_whole_operand_dimension rules graph result events) width body)%N.

(** Given index and pattern atom bounds, matcher work is bounded by the stated
    dimension-dependent expression. *)
Definition rw_ri_match_bound_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    state root (pattern : rw_pattern K Sort V H) width body,
    rw_whole_index_atoms op sort value width body state ->
    rw_whole_pattern_atoms op sort value hole width body pattern ->
    let dimension := S (rw_whole_index_dimension state + Pos.size_nat root +
      rw_whole_pattern_dimension pattern + width) in
    (N.of_nat (snd (rw_ri_match_atomic op sort value hole state root pattern)) <=
      4294967296 * (1 + N.of_nat body) *
        N.pow (N.of_nat dimension) (32 + 16 * N.of_nat (rw_whole_pattern_dimension pattern)))%N.
