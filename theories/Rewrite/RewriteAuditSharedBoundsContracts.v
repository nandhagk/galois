(** * RewriteAuditSharedBoundsContracts

    This module defines shared-extraction and scalar-observer budgets and their prospective bounds.
    For example, converting a variable graph node with natural sort 0 and value 0 keeps both.
    Builds on: RewriteAuditSharedExtract and
    RewriteAuditSharedObservers. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedExtract
  RewriteAuditSharedObservers RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rd_source_node {K Sort V} (node : rw_node K Sort V) : rw_shared_node K Sort V :=
  match node with
  | RWNVar s v => RWSharedVar K Sort V s v
  | RWNApp s k ids => RWSharedApp K Sort V s k ids
  end.

Definition rw_rd_callback_weight {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (node : rw_node K Sort V) : nat :=
  match node with
  | RWNVar _ v =>
    let '(cost, work) := vc v in
    S (cost + work)
  | RWNApp _ k _ =>
    let '(cost, work) := oc k in
    S (cost + work)
  end.

Definition rw_rd_extract_input_weight {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K Sort V) (root : rw_id) : nat :=
  S (Pos.size_nat root + length (rw_roots g) +
    audit_trie_nodes (rw_nodes g) + audit_trie_nodes (rw_class_roots g) +
    fold_right (fun entry n =>
      Pos.size_nat (fst entry) + Pos.size_nat (fst (snd entry)) +
        rw_rd_node_input_weight op sort value (rw_rd_source_node (snd (snd entry))) +
        rw_rd_callback_weight vc oc (snd (snd entry)) + n)
      0 (Map.elements (rw_nodes g)) +
    fold_right (fun entry n => Pos.size_nat (fst entry) + Pos.size_nat (snd entry) + n)
      0 (Map.elements (rw_class_roots g))).

Definition rw_rd_extract_budget {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K Sort V) (root : rw_id) : nat :=
  Nat.pow (1024 * rw_rd_extract_input_weight op sort value vc oc g root) 20.

(** The work of a shared extraction run is bounded by its extraction budget. *)
Definition rw_rd_extract_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat * nat) (oc : K -> nat * nat)
    g root answer work,
    rw_shared_extract_run op sort value vc oc g root answer work ->
    work <= rw_rd_extract_budget op sort value vc oc g root.

(** A successful shared extraction run stores at most roots times graph nodes. *)
Definition rw_rd_extract_storage_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat * nat) (oc : K -> nat * nat)
    g root dag work,
    rw_shared_extract_run op sort value vc oc g root (Some dag) work ->
    Map.size (rw_shared_nodes K Sort V dag) <= length (rw_roots g) * Map.size (rw_nodes g).

Definition rw_rd_scalar_input_weight {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) : nat :=
  S (audit_trie_nodes (rw_shared_nodes K Sort V dag) + Pos.size_nat (rw_shared_root K Sort V dag) +
    fold_right (fun entry n => Pos.size_nat (fst entry) +
      match snd entry with
      | RWSharedVar _ _ _ _ v =>
        let '(cost, work) := vc v in
        S (cost + work + n)
      | RWSharedApp _ _ _ _ k ids =>
        let '(cost, work) := oc k in
        S (cost + work + rw_shared_children_bits ids + n)
      end) 0 (Map.elements (rw_shared_nodes K Sort V dag))).

Definition rw_rd_scalar_budget {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) : nat :=
  Nat.pow (1024 * rw_rd_scalar_input_weight vc oc dag) 8.

(** The scalar observer work is bounded by its stored-input budget. *)
Definition rw_rd_scalar_bound_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K -> nat * nat) (dag : rw_shared_tree K Sort V),
    snd (rw_rd_scalar_observe vc oc dag) <= rw_rd_scalar_budget vc oc dag.

(** Unary cost observer work is bounded by 128 plus the scalar budget and, when binary
    cost exists, the actual binary-to-unary conversion work. *)
Definition rw_rd_unary_cost_bound_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K -> nat * nat) (dag : rw_shared_tree K Sort V),
    snd (rw_shared_tree_cost_atomic vc oc dag) <=
      128 + rw_rd_scalar_budget vc oc dag +
      match fst (rw_shared_tree_cost_binary_atomic vc oc dag) with
      | None => 0
      | Some cost => snd (rw_rd_N_to_nat cost)
      end.
