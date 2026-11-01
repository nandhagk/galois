(** * RewriteAuditProofSelected

    Models selected explanations and states prospective tracked-run semantic guarantees.
    For example, for a seed variable of natural sort 0 and value 0 at root 1, a false
    seed-membership result makes the selected observer return None.
    Builds on: RewriteAuditIndexMembership and
    RewriteAuditProofClosure. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditIndexProgramLaws
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditProofCarrier
  RewriteAuditProofClosure RewriteAuditProofRebuild RewriteAuditProofRun RewriteAuditProofTick
  RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rp_selected_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_tracked_state K Sort V H) (root : rw_id) (seed tree : rw_term K Sort V) :
    option (rw_provenance K Sort V H * positive) * nat :=
  let machine := rw_tracked_machine state in
  let '(source_member, source_work) := rw_ri_member_atomic op sort value machine seed root in
  let '(tree_member, tree_work) := rw_ri_member_atomic op sort value machine tree root in
  if source_member && tree_member then
    let '(out, connection_work) :=
      rw_rp_connect_atomic op sort value (rw_tracked_provenance state) seed tree in
    (out, 64 + source_work + tree_work + connection_work)
  else (None, 64 + source_work + tree_work).

(** With agreeing encoders and callbacks, sound well-formed rules, and a typed seed,
    the tracked source run has a well-formed, sound, productive final graph representing the
    seed, with valid provenance and connections; nonzero fuel yields a clean graph. *)
Definition rw_rp_run_semantic_statement : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) rules adapter fuel seed,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    rw_typed sig seed ->
    let '((root, output), _) :=
      rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed in
    let state := rw_tracked_final output in
    let graph := rw_index_graph (rw_tracked_machine state) in
    rw_graph_wf sig graph /\ rw_graph_sound sig admissible rules graph /\
    rw_productive graph /\ rw_represents graph root seed /\
    (fuel <> 0%N -> rw_clean graph) /\
    rw_rp_phase_connected EK ES EV state /\
    rw_provenance_valid EH sig rules (rw_tracked_provenance state).

(** With agreeing encoders, a well-formed connected phase, valid provenance, and both endpoints
    represented at the root, selected explanation succeeds with valid endpoint evidence. *)
Definition rw_rp_selected_complete_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H)
    (sig : rw_signature K Sort V) rules root seed tree,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_graph_wf sig (rw_index_graph (rw_tracked_machine state)) ->
    rw_rp_phase_connected EK ES EV state ->
    rw_provenance_valid EH sig rules (rw_tracked_provenance state) ->
    rw_represents (rw_index_graph (rw_tracked_machine state)) root seed ->
    rw_represents (rw_index_graph (rw_tracked_machine state)) root tree ->
    exists proof id node,
      fst (rw_rp_selected_atomic op sort value state root seed tree) = Some (proof, id) /\
      rw_provenance_valid EH sig rules proof /\
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
      rw_evidence_left node = seed /\
      rw_evidence_right node = tree.
