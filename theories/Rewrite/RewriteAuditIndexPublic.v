(** * RewriteAuditIndexPublic

    This module states index rebuild contracts and support invariants for indexed buckets.
    For example, bucket-node support for an empty node list allows no stored bucket member.
    Builds on: RewriteAuditIndexPrepareReference and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrepareReference RewriteAuditIndexReference
  RewriteAuditIndexTickReference.
Import List.ListNotations.

(** A clean trace records strategy attempts and their rejection or application between
    clean states with agreeing snapshots. *)
Inductive rw_index_clean_trace {K Sort V H T}
    (graph : T -> rw_graph K Sort V) (view : T -> rw_snapshot_view K Sort V)
    (apply : T -> rw_attempt K Sort V H -> option (T * list rw_index_event))
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) :
    T -> list (rw_run_event K Sort V H) -> T -> Prop :=
  | RWIndexCleanTraceNil : forall state,
      rw_snapshot_agrees (graph state) (view state) -> rw_clean (graph state) ->
      rw_index_clean_trace graph view apply strategy state nil state
  | RWIndexCleanTraceReject : forall state final attempt events,
      rw_snapshot_agrees (graph state) (view state) -> rw_clean (graph state) ->
      strategy (view state) = Some attempt -> apply state attempt = None ->
      rw_index_clean_trace graph view apply strategy state events final ->
      rw_index_clean_trace graph view apply strategy state (RWRunRejected attempt :: events) final
  | RWIndexCleanTraceAccept : forall state next final attempt merges events,
      rw_snapshot_agrees (graph state) (view state) -> rw_clean (graph state) ->
      strategy (view state) = Some attempt -> apply state attempt = Some (next, merges) ->
      rw_index_clean_trace graph view apply strategy next events final ->
      rw_index_clean_trace graph view apply strategy state (RWRunAccepted attempt merges :: events)
        final.

Definition rw_index_result {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_graph K Sort V :=
  rw_index_graph (fst (rw_index_rebuild EK ES EV (rw_index_build EK ES EV g))).

(** A well-formed, sound, productive graph rebuilds to a clean phase and a well-formed,
    clean, productive result graph. *)
Definition rw_index_clean_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V),
    rw_graph_wf sig g ->
    rw_graph_sound sig admissible rules g ->
    rw_productive g ->
    rw_index_phase_clean EK ES EV (fst (rw_index_rebuild EK ES EV (rw_index_build EK ES EV g))) /\
    rw_graph_wf sig (rw_index_result EK ES EV g) /\
    rw_clean (rw_index_result EK ES EV g) /\
    rw_productive (rw_index_result EK ES EV g).

(** A well-formed, sound, productive graph rebuilds to a sound result graph. *)
Definition rw_index_sound_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V),
    rw_graph_wf sig g ->
    rw_graph_sound sig admissible rules g ->
    rw_productive g ->
    rw_graph_sound sig admissible rules (rw_index_result EK ES EV g).

(** A well-formed, sound, productive graph retains its represented terms after rebuild. *)
Definition rw_index_witness_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V),
    rw_graph_wf sig g ->
    rw_graph_sound sig admissible rules g ->
    rw_productive g ->
    forall c t, rw_represents g c t ->
      rw_represents (rw_index_result EK ES EV g) c t.

(** Each stored operator, variable, and signature bucket contains a node identifier. *)
Definition index_nonempty_buckets {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_index_state K Sort V) : Prop :=
  (forall key bucket, Map.get EK key (rw_index_operators state) = Some bucket -> exists node,
    FinSet.mem positive_encoding node bucket = true) /\
  (forall key bucket, Map.get EV key (rw_index_variables state) = Some bucket -> exists node,
    FinSet.mem positive_encoding node bucket = true) /\
  (forall key bucket, Map.get (rw_node_encoding EK ES EV) key (rw_index_signatures state) =
    Some bucket -> exists node, FinSet.mem positive_encoding node bucket = true).

(** Every stored parent bucket is keyed by a root of the base graph. *)
Definition index_parent_support {K Sort V} (state : rw_index_state K Sort V) : Prop :=
  forall root bucket,
    Map.get positive_encoding root (rw_index_parent_buckets state) = Some bucket ->
    In root (rw_roots (rw_index_base state)).

(** A supported valid index is valid, has nonempty indexed buckets, and has root-keyed parents. *)
Definition index_supported_valid {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state : rw_index_state K Sort V) : Prop :=
  rw_index_valid EK ES EV sig state /\ index_nonempty_buckets EK ES EV state /\
  index_parent_support state.

(** A supported valid index has operator, variable, and signature map sizes bounded
    by node count and parent-bucket map size bounded by root count. *)
Definition index_support_cardinality_type : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state : rw_index_state K Sort V),
    index_supported_valid EK ES EV sig state ->
    Map.size (rw_index_operators state) <= length (rw_nodes_in (rw_index_base state)) /\
    Map.size (rw_index_variables state) <= length (rw_nodes_in (rw_index_base state)) /\
    Map.size (rw_index_signatures state) <= length (rw_nodes_in (rw_index_base state)) /\
    Map.size (rw_index_parent_buckets state) <= length (rw_roots (rw_index_base state)).

(** A supported valid index has operator, variable, and signature map sizes bounded
    by node count and parent-bucket map size bounded by root count. *)
Definition index_supported_cardinality_contract : Prop :=
  index_support_cardinality_type.

Definition bucket_member_count {K} (table : Map.t K (FinSet.t positive)) : nat :=
  fold_right (fun entry total => FinSet.size (snd entry) + total) 0 (Map.elements table).

(** Each stored bucket is well formed and contains only identifiers from the supplied node list. *)
Definition bucket_node_support {K} (E : encoding K) (nodes : list positive)
    (table : Map.t K (FinSet.t positive)) : Prop :=
  forall key bucket, Map.get E key table = Some bucket ->
    FinSet.wf positive_encoding bucket /\
    forall node, FinSet.mem positive_encoding node bucket = true ->
      In node nodes.

(** Every stored index bucket is well formed and contains only base-graph node identifiers. *)
Definition index_bucket_node_support {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_index_state K Sort V) : Prop :=
  let nodes := rw_nodes_in (rw_index_base state) in
  bucket_node_support EK nodes (rw_index_operators state) /\
  bucket_node_support EV nodes (rw_index_variables state) /\
  bucket_node_support (rw_node_encoding EK ES EV) nodes (rw_index_signatures state) /\
  bucket_node_support positive_encoding nodes (rw_index_parent_buckets state).

(** For a supported valid index with bucket-node support, operator, variable, and signature
    memberships are bounded by nodes squared and parent memberships by roots times nodes. *)
Definition index_member_node_bound_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state : rw_index_state K Sort V),
    index_supported_valid EK ES EV sig state -> index_bucket_node_support EK ES EV state ->
    let nodes := length (rw_nodes_in (rw_index_base state)) in
    let roots := length (rw_roots (rw_index_base state)) in
    bucket_member_count (rw_index_operators state) <= nodes * nodes /\
    bucket_member_count (rw_index_variables state) <= nodes * nodes /\
    bucket_member_count (rw_index_signatures state) <= nodes * nodes /\
    bucket_member_count (rw_index_parent_buckets state) <= roots * nodes.

(** Building an index from a well-formed graph preserves the graph and establishes
    supported validity and bucket-node support. *)
Definition rw_index_build_supported_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V),
    rw_graph_wf sig g ->
    let state := rw_index_build EK ES EV g in
    rw_index_graph state = g /\ index_supported_valid EK ES EV sig state /\
    index_bucket_node_support EK ES EV state.

(** From a supported valid state with bucket-node support, a successful tick preserves both. *)
Definition rw_index_tick_supported_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state next : rw_index_state K Sort V) event,
    index_supported_valid EK ES EV sig state ->
    index_bucket_node_support EK ES EV state ->
    rw_index_tick EK ES EV state = Some (next, event) ->
    index_supported_valid EK ES EV sig next /\
    index_bucket_node_support EK ES EV next.
