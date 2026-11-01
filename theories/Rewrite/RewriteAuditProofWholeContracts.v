(** * RewriteAuditProofWholeContracts

    This module states whole-operation bounds for tracked runs and their stored evidence.
    For example, an empty provenance-node map satisfies the endpoint-atoms predicate.
    Builds on: RewriteAuditProofRun and
    RewriteAuditIndexExternal. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions4 RewriteAuditIndexEventEnvelope
  RewriteAuditIndexExternal RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexRules RewriteAuditProofCarrier RewriteAuditProofDimensions3
  RewriteAuditProofRun RewriteAuditProofTick RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

(** Both endpoints of every stored provenance node satisfy the term atom bounds. *)
Definition rw_whole_provenance_atoms {K Sort V H} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat) (proof :
    rw_provenance K Sort V H) : Prop :=
  Forall (fun entry => rw_whole_term_atoms op sort value width body
      (rw_evidence_left (snd entry)) /\
    rw_whole_term_atoms op sort value width body (rw_evidence_right (snd entry)))
    (Map.elements (rw_provenance_nodes proof)).

(** Every stored shared witness node has sort, operator, or value atoms within bounds. *)
Definition rw_whole_witness_atoms {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat) (store :
    rw_class_witness_store K Sort V) : Prop :=
  Forall (fun entry =>
    match snd entry with
    | RWSharedVar _ _ _ ty v => rw_whole_encoder_fits sort width body ty /\
        rw_whole_encoder_fits value width body v
    | RWSharedApp _ _ _ ty k _ => rw_whole_encoder_fits sort width body ty /\
        rw_whole_encoder_fits op width body k
    end) (Map.elements (rw_class_witness_nodes store)).

(** The tracked invocation bounds seed, rules, events, final index, proof and witness
    atoms, and strategy operations for the observed operand dimension. *)
Record rw_rp_whole_invocation {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (adapter : rw_rp_strategy_adapter K Sort V H)
    (seed : rw_term K Sort V) (output : rw_tracked_output K Sort V H)
    (width body : nat) : Prop := RwRpWholeInvocation {
  (** The input seed's atoms fit the encoder bounds. *)
  rw_rp_whole_seed_atoms : rw_whole_term_atoms op sort value width body seed;
  (** The rule inputs and callbacks meet their external bounds. *)
  rw_rp_whole_rules_external : rw_whole_rules_external op sort value hole callbacks
    width body rules;
  (** Every recorded event's attempt meets the external bounds. *)
  rw_rp_whole_event_external : Forall
    (rw_whole_event_external EH op sort value hole callbacks width body rules)
    (rw_tracked_events output);
  (** The final tracked index's atoms fit the bounds. *)
  rw_rp_whole_index_atoms : rw_whole_index_atoms op sort value width body
    (rw_tracked_machine (rw_tracked_final output));
  (** Both endpoints of each final provenance node fit the bounds. *)
  rw_rp_whole_proof_atoms : rw_whole_provenance_atoms op sort value width body
    (rw_tracked_provenance (rw_tracked_final output));
  (** Atoms in the final witness store fit the bounds. *)
  rw_rp_whole_witness_atoms : rw_whole_witness_atoms op sort value width body
    (rw_tracked_witnesses (rw_tracked_final output));
  (** Strategy operations fit the bounds at the observed operand dimension. *)
  rw_rp_whole_strategy_external : rw_whole_strategy_external EK ES EV op sort value
    (rw_rp_whole_operand_dimension rules seed output) width body adapter
}.

(** With agreeing encoders and callbacks, well-formed rules, a typed seed, and the whole
    tracked invocation premise, source work is bounded by the whole-source ceiling. *)
Definition rw_rp_whole_bound_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter fuel seed width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
    rw_typed sig seed ->
    let '((_, output), work) :=
      rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed in
    rw_rp_whole_invocation EK ES EV EH op sort value hole callbacks rules adapter seed output
      width body ->
    (N.of_nat work <= rw_whole_source_ceiling fuel
      (rw_rp_whole_operand_dimension rules seed output) width body)%N.
