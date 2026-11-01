(** * RewriteAuditProofSemantic

    Defines tracked provenance, class witnesses, event-index invariants, and fact validity.
    For example, stamp (0, 0) is fresh when both the event index and provenance map are empty.
    Builds on: RewriteAuditProofRepresentation and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofRepresentation RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_tracked_graph {K Sort V H} (state : rw_tracked_state K Sort V H) :=
  rw_index_graph (rw_tracked_machine state).

(** Witness maps are well formed, stored roots are graph roots, and every found class
    has a well-formed shared witness unfolding to a represented term. *)
Definition rw_class_witnesses_valid {K Sort V} (g : rw_graph K Sort V) (store :
    rw_class_witness_store K Sort V) : Prop :=
  Map.wf positive_encoding (rw_class_witness_nodes store) /\
  Map.wf positive_encoding (rw_class_witness_roots store) /\
  (forall root pointer,
    Map.get positive_encoding root (rw_class_witness_roots store) = Some pointer ->
    rw_find g root = Some root) /\
  forall c root, rw_find g c = Some root ->
    exists pointer term,
      Map.get positive_encoding root (rw_class_witness_roots store) = Some pointer /\
      let dag := RwSharedTree K Sort V pointer (rw_class_witness_nodes store) in
      rw_shared_wf dag /\ rw_shared_unfold dag = Some term /\ rw_represents g root term.

(** Every node in the old provenance remains at the same identifier in the new provenance. *)
Definition rw_provenance_extends {K Sort V H} (old new : rw_provenance K Sort V H) : Prop :=
  forall id node, Map.get positive_encoding id (rw_provenance_nodes old) = Some node ->
    Map.get positive_encoding id (rw_provenance_nodes new) = Some node.

(** Every rule node in the new provenance already occurred unchanged in the old provenance. *)
Definition rw_provenance_rule_stable {K Sort V H} (old new : rw_provenance K Sort V H) : Prop :=
  forall id node index bindings,
    Map.get positive_encoding id (rw_provenance_nodes new) = Some node ->
    rw_evidence_reason_of node = RWEvidenceRule index bindings ->
    Map.get positive_encoding id (rw_provenance_nodes old) = Some node.

(** For valid extending provenance, a found root with an unfolding class witness, and a valid
    representation witness, connection preserves validity, adds no rule nodes, and records both
    endpoints. *)
Definition rw_class_connected {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H))
    (unfold_tree : rw_shared_tree K Sort V -> option (rw_term K Sort V))
    (connect : rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V ->
      rw_term K Sort V -> rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive))
    (graph : rw_graph K Sort V) (store : rw_class_witness_store K Sort V)
    (proof : rw_provenance K Sort V H) : Prop :=
  forall current, rw_provenance_valid EH sig rules current ->
    rw_provenance_extends proof current ->
    forall c root pointer base term witness, rw_find graph c = Some root ->
      Map.get positive_encoding root (rw_class_witness_roots store) = Some pointer ->
      unfold_tree (RwSharedTree K Sort V pointer (rw_class_witness_nodes store)) = Some base ->
      rw_repr_witness_valid graph c term witness ->
      exists extended id node, connect graph current c base term witness = Some (extended, id) /\
        rw_provenance_extends current extended /\
        rw_provenance_rule_stable current extended /\
        rw_provenance_valid EH sig rules extended /\
        Map.get positive_encoding id (rw_provenance_nodes extended) = Some node /\
        rw_evidence_left node = base /\
        rw_evidence_right node = term.

(** The well-formed event index maps initial congruences, accepted rule events, and
    rebuild congruences to evidence nodes with their corresponding timestamps. *)
Definition rw_tracked_event_index_valid {K Sort V H} (state : rw_tracked_state K Sort V H)
    (initial : list rw_index_event) (events : list (rw_run_event K Sort V H)) : Prop :=
  let index := rw_tracked_event_nodes state in
  let proof := rw_tracked_provenance state in
  let E := pair_encoding nat_encoding nat_encoding in
  Map.wf E index /\
  (forall position item a b root,
    nth_error initial position = Some (RWIndexCongruence item a b root) ->
    exists id node, Map.get E (0, S position) index = Some id /\
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
      rw_evidence_time node = (0, S position)) /\
  (forall position attempt rebuild_events,
    nth_error (rev events) position = Some (RWRunAccepted attempt rebuild_events) ->
    exists id node, Map.get E (S position, 0) index = Some id /\
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
      rw_evidence_time node = (S position, 0) /\
      rw_evidence_reason_of node = RWEvidenceRule (rw_attempt_rule attempt)
        (rw_attempt_sub attempt)) /\
  forall position attempt rebuild_events subposition item a b root,
    nth_error (rev events) position = Some (RWRunAccepted attempt rebuild_events) ->
    nth_error rebuild_events subposition = Some (RWIndexCongruence item a b root) ->
    exists id node, Map.get E (S position, S subposition) index = Some id /\
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
      rw_evidence_time node = (S position, S subposition).

(** Every stored rule evidence node is indexed by a matching accepted run event. *)
Definition rw_tracked_rule_nodes_covered {K Sort V H} (state : rw_tracked_state K Sort V H)
    (events : list (rw_run_event K Sort V H)) : Prop :=
  let index := rw_tracked_event_nodes state in
  let proof := rw_tracked_provenance state in
  forall id node rule_index bindings,
    Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
    rw_evidence_reason_of node = RWEvidenceRule rule_index bindings ->
    exists position attempt rebuild_events,
      nth_error (rev events) position = Some (RWRunAccepted attempt rebuild_events) /\
      Map.get (pair_encoding nat_encoding nat_encoding) (S position, 0) index = Some id /\
      rw_attempt_rule attempt = rule_index /\ rw_attempt_sub attempt = bindings.

(** A fresh timestamp is absent from the event index and strictly later than every
    stored evidence timestamp. *)
Definition rw_tracked_stamp_fresh {K Sort V H} (stamp : nat * nat) (state : rw_tracked_state K Sort
    V H) : Prop :=
  Map.get (pair_encoding nat_encoding nat_encoding) stamp (rw_tracked_event_nodes state) = None /\
  forall id node,
    Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance state)) = Some node ->
    rw_evidence_time_lt (rw_evidence_time node) stamp.

(** A tracked rebuild trace records successive stamped ticks through the final failed tick. *)
Inductive rw_tracked_rebuild_trace {T} (tick : (nat * nat) -> T -> option (T * rw_index_event))
    (group : nat) : nat -> T -> list rw_index_event -> T -> Prop :=
  | RWTrackedRebuildDone : forall position state,
      tick (group, S position) state = None ->
      rw_tracked_rebuild_trace tick group position state nil state
  | RWTrackedRebuildStep : forall position state next final event events,
      tick (group, S position) state = Some (next, event) ->
      rw_tracked_rebuild_trace tick group (S position) next events final ->
      rw_tracked_rebuild_trace tick group position state (event :: events) final.

Definition rw_facts_invalidate {F} (_ : Map.t rw_id F) : Map.t rw_id F :=
  Map.empty.

(** The fact map is well formed and each stored fact is valid for its graph and analysis. *)
Definition rw_fact_store_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop) (an :
    rw_analysis K Sort V C F) (g : rw_graph K Sort V) (facts : Map.t rw_id F) : Prop :=
  Map.wf positive_encoding facts /\
  forall id f, Map.get positive_encoding id facts = Some f ->
    rw_fact_valid admissible an g id f.

(** Invalidating a valid fact store yields a valid store for any new graph and no
    retained lookup entries. *)
Definition rw_facts_invalidate_sound_contract : Prop :=
  forall K Sort V C F (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (old new : rw_graph K Sort V) facts, rw_fact_store_valid admissible an old facts ->
    rw_fact_store_valid admissible an new (rw_facts_invalidate facts) /\
    forall id, Map.get positive_encoding id (rw_facts_invalidate facts) = None.

Definition rw_fact_store_total {K Sort V C F} (an : rw_analysis K Sort V C F) (facts : Map.t rw_id
    F) (id : rw_id) : F :=
  match Map.get positive_encoding id facts with
  | Some fact => fact
  | None => rw_fact_unknown an
  end.

(** Under analysis laws, a valid fact store yields a valid total fact function. *)
Definition rw_fact_store_total_valid_contract : Prop :=
  forall K Sort V C F (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) facts,
    rw_analysis_laws sig admissible an ->
    rw_fact_store_valid admissible an g facts ->
    rw_facts_valid admissible an g (rw_fact_store_total an facts).

(** A total lookup after invalidation returns the analysis unknown fact. *)
Definition rw_fact_store_total_after_invalidate_contract : Prop :=
  forall K Sort V C F (an : rw_analysis K Sort V C F) facts id, rw_fact_store_total an
    (rw_facts_invalidate facts) id = rw_fact_unknown an.

Record rw_fact_view (K Sort V F : Type) := RWFactView {
  rw_fact_snapshot : rw_snapshot_view K Sort V;
  rw_fact_lookup : rw_id -> F
}.
Arguments RWFactView {K Sort V F}.
Arguments rw_fact_snapshot {K Sort V F}.
Arguments rw_fact_lookup {K Sort V F}.

Definition rw_fact_observe {K Sort V H C F} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (an : rw_analysis K Sort V C F) (state : rw_tracked_state K Sort V H) (facts : Map.t rw_id F) :
    rw_fact_view K Sort V F :=
  RWFactView (rw_index_view EK ES EV (rw_tracked_machine state)) (rw_fact_store_total an facts).

(** Under analysis laws, snapshot agreement, and valid stored facts, fact observation
    returns an agreeing snapshot and a valid total fact function. *)
Definition rw_fact_observe_valid_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (state : rw_tracked_state K Sort V H) facts,
    rw_analysis_laws sig admissible an ->
    rw_snapshot_agrees (rw_tracked_graph state)
      (rw_index_view EK ES EV (rw_tracked_machine state)) ->
    rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
    let observed := rw_fact_observe EK ES EV an state facts in
    rw_snapshot_agrees (rw_tracked_graph state) (rw_fact_snapshot observed) /\
    rw_facts_valid admissible an (rw_tracked_graph state) (rw_fact_lookup observed).
