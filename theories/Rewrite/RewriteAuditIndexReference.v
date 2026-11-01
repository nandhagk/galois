(** * RewriteAuditIndexReference

    Defines phase and snapshot views, indexed states, and their consistency predicates.
    For example, an agreeing view exposes exactly the root list of its graph.
    Builds on: RewriteAuditQueueReference and
    RewriteEgraph. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference.
Import List.ListNotations.

Record rw_phase_view (K Sort V : Type) := RwPhaseView {
  rw_view_find : rw_id -> option rw_id;
  rw_view_sort : rw_id -> option Sort;
  rw_view_node : rw_id -> option (rw_id * rw_node K Sort V);
  rw_view_operator_nodes : K -> list rw_id;
  rw_view_variable_nodes : V -> list rw_id;
  rw_view_parent_nodes : rw_id -> list rw_id;
  rw_view_roots : unit -> list rw_id;
  rw_view_nodes : unit -> list rw_id
}.
Arguments RwPhaseView {K Sort V}.
Arguments rw_view_find {K Sort V}.
Arguments rw_view_sort {K Sort V}.
Arguments rw_view_node {K Sort V}.
Arguments rw_view_operator_nodes {K Sort V}.
Arguments rw_view_variable_nodes {K Sort V}.
Arguments rw_view_parent_nodes {K Sort V}.
Arguments rw_view_roots {K Sort V}.
Arguments rw_view_nodes {K Sort V}.

Record rw_snapshot_view (K Sort V : Type) := RwSnapshotView {
  rw_snapshot_base : rw_phase_view K Sort V;
  rw_snapshot_graph : unit -> rw_graph K Sort V
}.
Arguments RwSnapshotView {K Sort V}.
Arguments rw_snapshot_base {K Sort V}.
Arguments rw_snapshot_graph {K Sort V}.

(** The view agrees with graph lookup, roots, nodes, and duplicate-free indexed
    operator, variable, and parent memberships. *)
Definition rw_view_agrees {K Sort V} (g : rw_graph K Sort V) (v : rw_phase_view K Sort V) : Prop :=
  (forall c, rw_view_find v c = rw_find g c) /\
  (forall c, rw_view_sort v c = rw_class_sort g c) /\
  (forall n, rw_view_node v n = rw_node_at g n) /\
  (forall op, NoDup (rw_view_operator_nodes v op)) /\
  (forall value, NoDup (rw_view_variable_nodes v value)) /\
  (forall c, NoDup (rw_view_parent_nodes v c)) /\
  (forall op n, In n (rw_view_operator_nodes v op) <->
    exists owner sort children, rw_node_at g n = Some (owner, RWNApp sort op children)) /\
  (forall value n, In n (rw_view_variable_nodes v value) <->
    exists owner sort, rw_node_at g n = Some (owner, RWNVar sort value)) /\
  (forall c n, In n (rw_view_parent_nodes v c) <->
    exists root owner sort op children child,
      rw_find g c = Some root /\ rw_find g child = Some root /\
      rw_node_at g n = Some (owner, RWNApp sort op children) /\ In child children) /\
  rw_view_roots v tt = rw_roots g /\
  rw_view_nodes v tt = rw_nodes_in g.

(** Operator, variable, and parent lists use the canonical finite-set enumeration order. *)
Definition rw_phase_ordered {K Sort V} (v : rw_phase_view K Sort V) : Prop :=
  (forall op, rw_view_operator_nodes v op = FinSet.elements (FinSet.of_list positive_encoding
    (rw_view_operator_nodes v op))) /\
  (forall value, rw_view_variable_nodes v value = FinSet.elements (FinSet.of_list positive_encoding
    (rw_view_variable_nodes v value))) /\
  forall id, rw_view_parent_nodes v id = FinSet.elements (FinSet.of_list positive_encoding
    (rw_view_parent_nodes v id)).

(** A snapshot has an agreeing ordered phase view and returns the original graph. *)
Definition rw_snapshot_agrees {K Sort V} (g : rw_graph K Sort V) (v : rw_snapshot_view K Sort V) :
    Prop :=
  rw_view_agrees g (rw_snapshot_base v) /\ rw_phase_ordered (rw_snapshot_base v) /\
    rw_snapshot_graph v tt = g.

Definition rw_snapshot_extract {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (vc : V -> nat) (oc : K -> nat) (view : rw_snapshot_view K Sort V) (root : rw_id) :
    option (rw_term K Sort V) :=
  rw_extract_tree EK ES EV vc oc (rw_snapshot_graph view tt) root.

(** Extraction from an agreeing snapshot equals extraction from the original graph. *)
Definition rw_snapshot_extract_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V) vc oc
    (g : rw_graph K Sort V) view root, rw_snapshot_agrees g view ->
    rw_snapshot_extract EK ES EV vc oc view root = rw_extract_tree EK ES EV vc oc g root.

Inductive rw_index_event : Type :=
  | RWIndexDirty : rw_id -> rw_index_event
  | RWIndexSkipped : rw_pair -> rw_index_event
  | RWIndexCongruence : rw_pair -> rw_id -> rw_id -> rw_id -> rw_index_event.

Inductive rw_run_event (K Sort V H : Type) : Type :=
  | RWRunRejected : rw_attempt K Sort V H -> rw_run_event K Sort V H
  | RWRunAccepted : rw_attempt K Sort V H -> list rw_index_event -> rw_run_event K Sort V H.
Arguments RWRunRejected {K Sort V H}.
Arguments RWRunAccepted {K Sort V H}.

Record rw_index_state (K Sort V : Type) := RWIndexState {
  rw_index_base : rw_graph K Sort V;
  rw_index_forest : UnionFind.t rw_id;
  rw_index_parent_buckets : Map.t rw_id (FinSet.t rw_id);
  rw_index_signatures : Map.t (rw_node K Sort V) (FinSet.t rw_id);
  rw_index_node_keys : Map.t rw_id (rw_node K Sort V);
  rw_index_dirty_order : list rw_id;
  rw_index_dirty_set : FinSet.t rw_id;
  rw_index_pending : rw_pending_queue;
  rw_index_operators : Map.t K (FinSet.t rw_id);
  rw_index_variables : Map.t V (FinSet.t rw_id);
  rw_index_fresh : positive
}.
Arguments RWIndexState {K Sort V}.
Arguments rw_index_base {K Sort V}.
Arguments rw_index_forest {K Sort V}.
Arguments rw_index_parent_buckets {K Sort V}.
Arguments rw_index_signatures {K Sort V}.
Arguments rw_index_node_keys {K Sort V}.
Arguments rw_index_dirty_order {K Sort V}.
Arguments rw_index_dirty_set {K Sort V}.
Arguments rw_index_pending {K Sort V}.
Arguments rw_index_operators {K Sort V}.
Arguments rw_index_variables {K Sort V}.
Arguments rw_index_fresh {K Sort V}.

Definition rw_index_find {K Sort V} (state : rw_index_state K Sort V) (id : rw_id) : option rw_id :=
  match rw_find (rw_index_base state) id with
  | None => None
  | Some root => Some (fst (UnionFind.find positive_encoding root (rw_index_forest state)))
  end.

Definition rw_index_graph {K Sort V} (state : rw_index_state K Sort V) : rw_graph K Sort V :=
  let base := rw_index_base state in
  let root r := fst (UnionFind.find positive_encoding r (rw_index_forest state)) in
  RwGraph (filter (fun r => Pos.eqb (root r) r) (rw_roots base)) (rw_nodes_in base)
    (Map.map root (rw_class_roots base)) (rw_sorts base) (rw_nodes base).

Definition rw_index_bucket {A} (E : encoding A) (key : A) (table : Map.t A (FinSet.t rw_id)) :
    FinSet.t rw_id :=
  match Map.get E key table with
  | Some bucket => bucket
  | None => FinSet.empty
  end.

Definition rw_index_view {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (state : rw_index_state K Sort V) : rw_snapshot_view K Sort V :=
  RwSnapshotView (RwPhaseView (rw_index_find state) (rw_class_sort (rw_index_base state))
    (rw_node_at (rw_index_base state))
    (fun op => FinSet.elements (rw_index_bucket EK op (rw_index_operators state)))
    (fun value => FinSet.elements (rw_index_bucket EV value (rw_index_variables state)))
    (fun id =>
      match rw_index_find state id with
      | None => nil
      | Some root =>
        FinSet.elements (rw_index_bucket positive_encoding root (rw_index_parent_buckets state))
      end)
    (fun _ => rw_roots (rw_index_graph state)) (fun _ => rw_nodes_in (rw_index_base state)))
    (fun _ => rw_index_graph state).

Definition rw_index_canonical_node {K Sort V} (state : rw_index_state K Sort V)
    (node : rw_node K Sort V) : rw_node K Sort V :=
  let canon id :=
    match rw_index_find state id with
    | Some root => root
    | None => id
    end in
  match node with
  | RWNVar sort v => RWNVar sort v
  | RWNApp sort op ids => RWNApp sort op (map canon ids)
  end.

(** An index phase is clean when its dirty order and pending queue are empty. *)
Definition rw_index_phase_clean {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (state : rw_index_state K Sort V) : Prop :=
  rw_index_dirty_order state = nil /\ rw_pending_sequence (rw_index_pending state) = nil.

(** The index graph, snapshot, forest, maps, buckets, dirty queue, and pending state
    satisfy their well-formedness and consistency invariants. *)
Definition rw_index_valid {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state : rw_index_state K Sort V) : Prop :=
  let graph := rw_index_graph state in
  let base := rw_index_base state in
  let EN := rw_node_encoding EK ES EV in
  rw_graph_wf sig graph /\ rw_snapshot_agrees graph (rw_index_view EK ES EV state) /\
  UnionFind.wf positive_encoding (rw_index_forest state) /\
  (forall c, In c (UnionFind.keys positive_encoding (rw_index_forest state)) -> rw_find base c =
    Some c) /\
  Map.wf EK (rw_index_operators state) /\ Map.wf EV (rw_index_variables state) /\
  Map.wf positive_encoding (rw_index_parent_buckets state) /\
  Map.wf EN (rw_index_signatures state) /\
  Map.wf positive_encoding (rw_index_node_keys state) /\
  (forall op, FinSet.wf positive_encoding (rw_index_bucket EK op (rw_index_operators state))) /\
  (forall value,
    FinSet.wf positive_encoding (rw_index_bucket EV value (rw_index_variables state))) /\
  (forall root, FinSet.wf positive_encoding (rw_index_bucket positive_encoding root
    (rw_index_parent_buckets state))) /\
  (forall key, FinSet.wf positive_encoding (rw_index_bucket EN key (rw_index_signatures state))) /\
  NoDup (rw_index_dirty_order state) /\ FinSet.wf positive_encoding (rw_index_dirty_set state) /\
  (forall n, FinSet.mem positive_encoding n (rw_index_dirty_set state) = true <-> In n
    (rw_index_dirty_order state)) /\
  (forall n, In n (rw_index_dirty_order state) -> exists owner node, rw_node_at base n = Some
    (owner,node)) /\
  (forall n owner node, rw_node_at base n = Some (owner,node) ->
    ~ In n (rw_index_dirty_order state) ->
    Map.get positive_encoding n (rw_index_node_keys state) =
      Some (rw_index_canonical_node state node)) /\
  (forall n key, Map.get positive_encoding n (rw_index_node_keys state) = Some key <->
    FinSet.mem positive_encoding n (rw_index_bucket EN key (rw_index_signatures state)) = true) /\
  (forall n key, Map.get positive_encoding n (rw_index_node_keys state) = Some key ->
    exists owner node, rw_node_at base n = Some (owner,node)) /\
  (forall n m owner other_owner node other root other_root,
    rw_node_at base n = Some (owner,node) -> rw_node_at base m = Some (other_owner,other) ->
    ~ In n (rw_index_dirty_order state) -> ~ In m (rw_index_dirty_order state) ->
    rw_index_canonical_node state node = rw_index_canonical_node state other ->
    rw_index_find state owner = Some root -> rw_index_find state other_owner = Some other_root ->
    root <> other_root -> In (n,m) (rw_pending_sequence (rw_index_pending state)) \/
      In (m,n) (rw_pending_sequence (rw_index_pending state))) /\
  rw_pending_valid (rw_index_pending state) /\
  (forall p, In p (rw_pending_sequence (rw_index_pending state)) ->
    (exists owner node, rw_node_at base (fst p) = Some (owner,node)) /\
    (exists owner node, rw_node_at base (snd p) = Some (owner,node))) /\
  (forall c root, rw_find graph c = Some root -> (c < rw_index_fresh state)%positive) /\
  (forall n owner node, rw_node_at graph n = Some (owner,node) ->
    (n < rw_index_fresh state)%positive) /\
  (rw_index_phase_clean EK ES EV state -> rw_clean graph).
