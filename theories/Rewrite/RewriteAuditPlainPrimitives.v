(** * RewriteAuditPlainPrimitives

    This module supplies plain collection, encoding, and callback primitives for source phases.
    For example, the plain positive equality operation returns true for 1 and 1.
    Builds on: RewriteAuditIndexReference and
    RewriteAuditIndexTickReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexPrepareReference
  RewriteAuditIndexReference RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_audit_positive_encode :=
  positive_encoding.

Definition rw_plain_audit_nat_encode :=
  nat_encoding.

Definition rw_plain_audit_pair_encode :=
  @pair_encoding.

Definition rw_plain_rw_rd_pair_encode :=
  pair_encoding positive_encoding positive_encoding.

Definition rw_plain_rw_rp_stamp_encode :=
  pair_encoding nat_encoding nat_encoding.

Definition rw_plain_rw_queue_encoder_run {A} (E : encoding A) :=
  encode E.

Definition rw_plain_rw_external_encoding_events {A} (E : encoding A) :=
  E.

Definition rw_plain_rw_external_events_work :=
  tt.

Definition rw_plain_audit_map_get :=
  @Map.get.

Definition rw_plain_audit_map_set :=
  @Map.set.

Definition rw_plain_audit_map_remove :=
  @Map.remove.

Definition rw_plain_audit_map_elements :=
  @Map.elements.

Definition rw_plain_audit_list_encode {A} (E : encoding A) :=
  encode (list_encoding E).

Definition rw_plain_audit_positive_eqb :=
  Pos.eqb.

Definition rw_plain_rw_fuel_pos_succ :=
  Pos.succ.

Definition rw_plain_rw_fuel_length :=
  @length.

Definition rw_plain_rw_fuel_add :=
  Nat.add.

Definition rw_plain_rw_fuel_mul :=
  Nat.mul.

Definition rw_plain_rw_fuel_to_positive :=
  Pos.of_succ_nat.

Definition rw_plain_rw_rd_positive_compare_cont :=
  Pos.compare_cont.

Definition rw_plain_rw_ri_positive_dec_atomic (a b : positive) : bool :=
  if Pos.eq_dec a b then true else false.

Definition rw_plain_rw_ri_find_atomic :=
  @rw_index_find.

Definition rw_plain_rw_ri_canon_atomic :=
  @rw_index_canonical_node.

Definition rw_plain_rw_ri_graph_atomic :=
  @rw_index_graph.

Definition rw_plain_rw_ri_tick_atomic :=
  @rw_index_tick.

Definition rw_plain_rw_ri_rebuild_atomic :=
  @rw_index_rebuild.

Definition rw_plain_rw_ri_rebuild_fuel_atomic :=
  @rw_ri_rebuild_fuel.

Definition rw_plain_rw_ri_bucket_ids {A} (E : encoding A) (_ : unit) (key : A)
    (table : Map.t A (FinSet.t rw_id)) : list rw_id :=
  let bucket :=
    match Map.get E key table with
    | Some b => b
    | None => FinSet.empty
    end in
  FinSet.elements bucket.

Definition rw_plain_rw_ri_prepare_once {K Sort V} (op : encoding K) (value : encoding V)
    (g : rw_graph K Sort V) : rw_index_state K Sort V :=
  let empty := RwRiBuildAcc Map.empty Map.empty Map.empty in
  let buckets := rw_ri_build_nodes_value op value g (rw_nodes_in g) empty in
  let dirty := FinSet.of_list positive_encoding (rw_nodes_in g) in
  let fresh := rw_ri_fresh_value g in
  RWIndexState g UnionFind.make (rw_ri_build_parents buckets) Map.empty Map.empty
    (rw_nodes_in g) dirty rw_pending_empty (rw_ri_build_ops buckets) (rw_ri_build_vars buckets)
    fresh.

Fixpoint rw_plain_rw_ri_max_entries_atomic {A K Sort V : Type} (entries : list (positive * A))
    (current : positive) : positive :=
  match entries with
  | nil => current
  | (id, _) :: rest =>
    rw_plain_rw_ri_max_entries_atomic (K:=K) (Sort:=Sort) (V:=V) rest
      (Pos.max id current)
  end.

Definition rw_plain_rw_ri_pair_merge_atomic {K Sort V} (s dropped : rw_index_state K Sort V)
    (p : rw_pair) (remaining : rw_pending_queue) (ra rb : rw_id) (_ : list unit) :
    rw_index_state K Sort V * rw_index_event :=
  let forest := UnionFind.union positive_encoding ra rb (rw_index_forest s) in
  let root := fst (UnionFind.find positive_encoding ra forest) in
  let table := rw_index_parent_buckets s in
  let left_bucket := rw_index_bucket positive_encoding ra table in
  let right_bucket := rw_index_bucket positive_encoding rb table in
  let merged := FinSet.union positive_encoding left_bucket right_bucket in
  let without := Map.remove positive_encoding rb (Map.remove positive_encoding ra table) in
  let parents := if FinSet.is_empty merged then without
    else Map.set positive_encoding root merged without in
  let '(order, dirty) := rw_ri_mark_dirty (FinSet.elements merged)
    (rw_index_dirty_order s) (rw_index_dirty_set s) in
  let next := rw_ri_state_update s forest parents (rw_index_signatures s) (rw_index_node_keys s)
    order dirty remaining in
  (next, RWIndexCongruence p ra rb root).

Record rw_plain_callbacks (K Sort V H : Type) := RwPlainCallbacks {
  rw_plain_rw_rp_var_sort : V -> option Sort;
  rw_plain_rw_rp_operator_shape : K -> list Sort -> Sort -> bool;
  rw_plain_rw_rp_hole_sort : rw_rule K Sort V H -> H -> option Sort;
  rw_plain_guard : rw_rule K Sort V H -> rw_substitution K Sort V H -> bool
}.
Arguments RwPlainCallbacks {K Sort V H}.
Arguments rw_plain_rw_rp_var_sort {K Sort V H}.
Arguments rw_plain_rw_rp_operator_shape {K Sort V H}.
Arguments rw_plain_rw_rp_hole_sort {K Sort V H}.
Arguments rw_plain_guard {K Sort V H}.

Definition rw_plain_callbacks_of {K Sort V H} (sig : rw_signature K Sort V) :
    rw_plain_callbacks K Sort V H :=
  RwPlainCallbacks (rw_var_sort sig) (rw_operator_shape sig)
    rw_hole_sort (fun rule => rw_condition rule).

Definition rw_plain_rw_rp_guard_atomic {K Sort V H} (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (rule : rw_rule K Sort V H)
    (bindings : Map.t H (rw_term K Sort V)) : bool :=
  rw_plain_guard callbacks rule (fun h => Map.get hole h bindings).

Definition rw_plain_strategy (K Sort V H : Type) :=
  rw_index_state K Sort V -> option (rw_attempt K Sort V H).

Definition rw_plain_rw_rp_strategy_run {K Sort V H} (op : encoding K) (value : encoding V)
    (strategy : rw_plain_strategy K Sort V H) (state : rw_index_state K Sort V) :=
  strategy state.

Definition rw_plain_fact_strategy (K Sort V H F : Type) :=
  rw_index_state K Sort V -> F -> Map.t rw_id F -> option (rw_attempt K Sort V H).

Definition rw_plain_rw_rp_fact_strategy_run {K Sort V H F} (op : encoding K) (value : encoding V)
    (strategy : rw_plain_fact_strategy K Sort V H F) (state : rw_index_state K Sort V) (unknown : F)
    (facts : Map.t rw_id F) :=
  strategy state unknown facts.

Arguments rw_plain_audit_pair_encode {A B} _ _.
Arguments rw_plain_audit_map_get {K V} _ _ _.
Arguments rw_plain_audit_map_set {K V} _ _ _ _.
Arguments rw_plain_audit_map_remove {K V} _ _ _.
Arguments rw_plain_audit_map_elements {K V} _.
Arguments rw_plain_rw_fuel_length {A} _.
Arguments rw_plain_rw_ri_find_atomic {K Sort V} _ _.
Arguments rw_plain_rw_ri_canon_atomic {K Sort V} _ _.
Arguments rw_plain_rw_ri_graph_atomic {K Sort V} _.
Arguments rw_plain_rw_ri_tick_atomic {K Sort V} _ _ _ _.
Arguments rw_plain_rw_ri_rebuild_atomic {K Sort V} _ _ _ _.
Arguments rw_plain_rw_ri_rebuild_fuel_atomic {K Sort V} _.
