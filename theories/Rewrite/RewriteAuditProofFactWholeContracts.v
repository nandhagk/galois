(** * RewriteAuditProofFactWholeContracts

    Defines external-operation premises and prospective whole-source bounds for factful runs.
    For example, a fact lookup continues with the supplied unknown fact while a view query uses its
    actual response.
    Builds on: RewriteAuditIndexExternal and
    RewriteAuditProofFacts. *)

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
  RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofDimensions2 RewriteAuditProofFacts
  RewriteAuditProofRun RewriteAuditProofTick RewriteAuditProofWholeContracts
  RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_whole_fact_control {K Sort V H F} (view : rw_snapshot_view K Sort V) (unknown : F)
    (program : rw_rp_fact_program K Sort V H F) : nat :=
  match program with
  | RPFactReturn _ body => 64 + body
  | RPFactView body request next =>
    64 + body + rw_whole_fact_control view unknown
      (next (rw_rp_view_plain_request view request))
  | RPFactLookup body _ next => 64 + body + rw_whole_fact_control view unknown (next unknown)
  end.

(** View queries follow the actual view response; fact lookups follow the unknown value,
    and each visited request satisfies its operand bounds. *)
Fixpoint rw_whole_fact_queries {K Sort V H F} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (width body : nat) (view : rw_snapshot_view K Sort V)
    (unknown : F)
    (program : rw_rp_fact_program K Sort V H F) : Prop :=
  match program with
  | RPFactReturn _ _ => True
  | RPFactView _ request next => rw_whole_request_external op value width body request /\
      rw_whole_fact_queries op value width body view unknown
        (next (rw_rp_view_plain_request view request))
  | RPFactLookup _ id next => Pos.size_nat id <= width /\
      rw_whole_fact_queries op value width body view unknown (next unknown)
  end.

Definition rw_fact_whole_operand_dimension {K Sort V H F} (rules : list (rw_rule K Sort V H))
    (initial : rw_tracked_state K Sort V H) (input_facts : Map.t rw_id F)
    (output : rw_tracked_output K Sort V H) (retained : Map.t rw_id F) : nat :=
  S (rw_whole_tracked_dimension initial + rw_whole_tracked_dimension (rw_tracked_final output) +
    rw_whole_rules_dimension rules + rw_whole_event_attempt_dimension (rw_tracked_events output) +
    audit_trie_nodes input_facts + audit_trie_nodes retained).

(** For every index within the dimension bound and satisfying atom bounds, fact strategy
    control and queries satisfy body and operand bounds along actual view responses and
    unknown facts. *)
Definition rw_whole_fact_strategy_external {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (dimension width body : nat) (unknown : F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F) : Prop :=
  forall state,
    rw_whole_index_dimension state <= Nat.pow (S (dimension + width)) 8 ->
    rw_whole_index_atoms op sort value width body state ->
    let view := rw_index_view EK ES EV state in
    rw_whole_fact_control view unknown (rw_rp_fact_strategy_program adapter) <= body /\
    rw_whole_fact_queries op value width body view unknown (rw_rp_fact_strategy_program adapter).

(** The tracked machine, provenance, and witnesses all satisfy their atom bounds. *)
Definition rw_whole_tracked_atoms {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat)
    (state : rw_tracked_state K Sort V H) : Prop :=
  rw_whole_index_atoms op sort value width body (rw_tracked_machine state) /\
  rw_whole_provenance_atoms op sort value width body (rw_tracked_provenance state) /\
  rw_whole_witness_atoms op sort value width body (rw_tracked_witnesses state).

(** The factful invocation bounds initial and final tracked atoms, rule and event
    operations, and fact-strategy operations for the observed dimension. *)
Record rw_fact_whole_invocation {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (unknown : F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F) (initial : rw_tracked_state K Sort V H)
    (input_facts : Map.t rw_id F) (output : rw_tracked_output K Sort V H)
    (retained : Map.t rw_id F) (width body : nat) : Prop := RwFactWholeInvocation {
  (** The initial tracked machine, provenance, and witnesses satisfy the atom bounds. *)
  rw_fact_whole_initial_atoms : rw_whole_tracked_atoms op sort value width body initial;
  (** The final tracked machine, provenance, and witnesses satisfy the atom bounds. *)
  rw_fact_whole_final_atoms : rw_whole_tracked_atoms op sort value width body
    (rw_tracked_final output);
  (** Listed rule patterns and holes meet encoder bounds, and listed holes meet callback bounds. *)
  rw_fact_whole_rules_external : rw_whole_rules_external op sort value hole callbacks
    width body rules;
  (** Each attempt bounds binding encoders and term callbacks; a listed rule also bounds
      guard control and queries. *)
  rw_fact_whole_events_external : Forall
    (rw_whole_event_external EH op sort value hole callbacks width body rules)
    (rw_tracked_events output);
  (** Fact-strategy control and visited queries satisfy their dimension and body bounds. *)
  rw_fact_whole_strategy_external : rw_whole_fact_strategy_external EK ES EV op sort value
    (rw_fact_whole_operand_dimension rules initial input_facts output retained) width body
    unknown adapter
}.

(** With agreeing encoders, global variable/operator callbacks and listed-rule hole/guard
    callbacks, well-formed rules, and the whole fact invocation premise, fact-source work is
    bounded by the whole-source ceiling. *)
Definition rw_rp_fact_whole_bound_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules (unknown : F) adapter fuel initial facts width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
    let '((output, retained), work) :=
      rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules unknown adapter fuel
        (initial, facts) in
    rw_fact_whole_invocation EK ES EV EH op sort value hole callbacks rules unknown adapter
      initial facts output retained width body ->
    (N.of_nat work <= rw_whole_source_ceiling fuel
      (rw_fact_whole_operand_dimension rules initial facts output retained) width body)%N.
