(** * RewriteAuditIndexDimensions

    Defines structural dimensions for Rewrite terms, patterns, graphs, indexes, and rules.
    For example, every Rewrite variable term has dimension 1.
    Builds on: RewriteAuditIndexReference and
    RewriteSyntax. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_whole_term_dimension {K Sort V} (term : rw_term K Sort V) : nat :=
  match term with
  | RWVar _ _ => 1
  | RWApp _ _ children =>
    S ((fix visit (terms : list (rw_term K Sort V)) : nat :=
      match terms with
      | nil => 1
      | t :: rest => S (rw_whole_term_dimension t + visit rest)
      end) children)
  end.

Fixpoint rw_whole_pattern_dimension {K Sort V H} (pattern : rw_pattern K Sort V H) : nat :=
  match pattern with
  | RWHole _ _ => 1
  | RWPVar _ _ => 1
  | RWPApp _ _ children =>
    S ((fix visit (patterns : list (rw_pattern K Sort V H)) : nat :=
      match patterns with
      | nil => 1
      | p :: rest => S (rw_whole_pattern_dimension p + visit rest)
      end) children)
  end.

Definition rw_whole_ids_dimension (ids : list positive) : nat :=
  fold_right (fun id total => S (Pos.size_nat id + total)) 1 ids.

Definition rw_whole_map_dimension {K V} (key_dimension : K -> nat) (value_dimension : V -> nat)
    (table : Map.t K V) : nat :=
  S (audit_trie_nodes table + fold_right (fun entry total =>
    S (key_dimension (fst entry) + value_dimension (snd entry) + total)) 1 (Map.elements table)).

Definition rw_whole_set_dimension (set : FinSet.t rw_id) : nat :=
  rw_whole_map_dimension Pos.size_nat (fun _ => 1) set.

Definition rw_whole_node_dimension {K Sort V} (node : rw_node K Sort V) : nat :=
  match node with
  | RWNVar _ _ => 1
  | RWNApp _ _ children => S (rw_whole_ids_dimension children)
  end.

Definition rw_whole_graph_dimension {K Sort V} (graph : rw_graph K Sort V) : nat :=
  S (rw_whole_ids_dimension (rw_roots graph) + rw_whole_ids_dimension (rw_nodes_in graph) +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (rw_class_roots graph) +
    rw_whole_map_dimension Pos.size_nat (fun _ => 1) (rw_sorts graph) +
    rw_whole_map_dimension Pos.size_nat
      (fun entry => Pos.size_nat (fst entry) + rw_whole_node_dimension (snd entry))
      (rw_nodes graph)).

Definition rw_whole_forest_dimension (forest : UnionFind.t rw_id) : nat :=
  S (UnionFind.max_rank forest +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (UnionFind.parents forest) +
    rw_whole_map_dimension Pos.size_nat (fun rank => S rank) (UnionFind.ranks forest)).

Definition rw_whole_index_dimension {K Sort V} (state : rw_index_state K Sort V) : nat :=
  S (rw_whole_graph_dimension (rw_index_base state) +
    rw_whole_forest_dimension (rw_index_forest state) +
    rw_whole_map_dimension Pos.size_nat rw_whole_set_dimension (rw_index_parent_buckets state) +
    rw_whole_map_dimension rw_whole_node_dimension rw_whole_set_dimension
      (rw_index_signatures state) +
    rw_whole_map_dimension Pos.size_nat rw_whole_node_dimension (rw_index_node_keys state) +
    rw_whole_ids_dimension (rw_index_dirty_order state) +
    rw_whole_set_dimension (rw_index_dirty_set state) +
    fold_right (fun pair total => S (Pos.size_nat (fst pair) + Pos.size_nat (snd pair) + total))
      1 (rw_pending_sequence (rw_index_pending state)) +
    rw_whole_map_dimension
      (fun pair => Pos.size_nat (fst pair) + Pos.size_nat (snd pair)) (fun _ => 1)
      (rw_pending_members (rw_index_pending state)) +
    rw_whole_map_dimension (fun _ => 1) rw_whole_set_dimension (rw_index_operators state) +
    rw_whole_map_dimension (fun _ => 1) rw_whole_set_dimension (rw_index_variables state) +
    Pos.size_nat (rw_index_fresh state)).

Definition rw_whole_bindings_dimension {K Sort V H} (bindings : Map.t H (rw_term K Sort V)) : nat :=
  rw_whole_map_dimension (fun _ => 1) rw_whole_term_dimension bindings.

Definition rw_whole_attempt_dimension {K Sort V H} (attempt : rw_attempt K Sort V H) : nat :=
  S (rw_attempt_rule attempt + Pos.size_nat (rw_attempt_root attempt) + rw_whole_bindings_dimension
    (rw_attempt_sub attempt)).

Definition rw_whole_rules_dimension {K Sort V H} (rules : list (rw_rule K Sort V H)) : nat :=
  fold_right (fun rule total => S (length (rw_holes rule) +
    rw_whole_pattern_dimension (rw_lhs rule) + rw_whole_pattern_dimension (rw_rhs rule) + total))
    1 rules.
