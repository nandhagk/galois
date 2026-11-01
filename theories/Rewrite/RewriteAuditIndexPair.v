(** * RewriteAuditIndexPair

    This module audits processing of a pending pair, including skips and congruence merges.
    For example, a missing first node causes the pair to be skipped.
    Builds on: RewriteAuditIndexDirty and
    RewriteAuditIndexFind. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexCompare RewriteAuditIndexDirty
  RewriteAuditIndexFind RewriteAuditIndexMark RewriteAuditIndexReference
  RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_pair_call (K Sort V : Type) : Type :=
  | RIPairNode : list (audit_map_event rw_id (rw_id * rw_node K Sort V) (audit_basic_encoding_event
      positive)) -> rw_ri_pair_call K Sort V
  | RIPairFind : rw_id -> option rw_id -> audit_trace rw_ri_find_call -> rw_ri_pair_call K Sort V
  | RIPairCanon : rw_node K Sort V -> rw_node K Sort V -> audit_trace rw_ri_canon_call ->
      rw_ri_pair_call K Sort V
  | RIPairNodeCode : rw_node K Sort V -> positive -> list (rw_ri_node_event K Sort V) ->
      rw_ri_pair_call K Sort V
  | RIPairDecision : positive -> positive -> bool -> audit_trace rw_ri_positive_call ->
      rw_ri_pair_call K Sort V
  | RIPairSort : list (audit_map_event rw_id Sort (audit_basic_encoding_event positive)) ->
      rw_ri_pair_call K Sort V
  | RIPairSortCode : Sort -> positive -> list nat -> rw_ri_pair_call K Sort V
  | RIPairUnion : list (audit_uf_event rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_pair_call K Sort V
  | RIPairForestFind : list (audit_uf_event rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_pair_call K Sort V
  | RIPairParentMap : list (audit_map_event rw_id (FinSet.t rw_id) (audit_basic_encoding_event
      positive)) -> rw_ri_pair_call K Sort V
  | RIPairSetUnion : list (audit_union_event rw_id) -> rw_ri_pair_call K Sort V
  | RIPairParentElements : list (audit_set_elements_event rw_id) -> rw_ri_pair_call K Sort V
  | RIPairMark : audit_trace rw_ri_mark_call -> rw_ri_pair_call K Sort V.
Arguments RIPairNode {K Sort V}.
Arguments RIPairFind {K Sort V}.
Arguments RIPairCanon {K Sort V}.
Arguments RIPairNodeCode {K Sort V}.
Arguments RIPairDecision {K Sort V}.
Arguments RIPairSort {K Sort V}.
Arguments RIPairSortCode {K Sort V}.
Arguments RIPairUnion {K Sort V}.
Arguments RIPairForestFind {K Sort V}.
Arguments RIPairParentMap {K Sort V}.
Arguments RIPairSetUnion {K Sort V}.
Arguments RIPairParentElements {K Sort V}.
Arguments RIPairMark {K Sort V}.

Definition rw_ri_pair_event_cost {K Sort V} (event : audit_event (rw_ri_pair_call K Sort V)) : nat
    :=
  match event with
  | AuditCall (RIPairNode trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairFind _ _ trace) => 1 + rw_ri_find_trace_cost trace
  | AuditCall (RIPairCanon _ _ trace) => 1 + rw_ri_canon_trace_cost trace
  | AuditCall (RIPairNodeCode _ _ trace) => 1 + rw_ri_node_encoding_work trace
  | AuditCall (RIPairDecision _ _ _ trace) => 64 + 64 * audit_work trace
  | AuditCall (RIPairSort trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairSortCode _ _ trace) => 1 + rw_external_events_work trace
  | AuditCall (RIPairUnion trace) => 1 + audit_uf_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairForestFind trace) => 1 + audit_uf_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairParentMap trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairSetUnion trace) => 1 + audit_finset_union_source_work trace
  | AuditCall (RIPairParentElements trace) => 1 + audit_set_elements_work trace
  | AuditCall (RIPairMark trace) => 1 + rw_ri_mark_trace_cost trace
  | _ => 1
  end.

Definition rw_ri_pair_trace_cost {K Sort V} (trace : audit_trace (rw_ri_pair_call K Sort V)) : nat
    :=
  fold_right (fun event total => rw_ri_pair_event_cost event + total) 0 trace.

Definition rw_ri_pair_skip {K Sort V} (dropped : rw_index_state K Sort V) (p : rw_pair)
    (prefix : audit_trace (rw_ri_pair_call K Sort V)) :
    (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_pair_call K Sort V) :=
  ((dropped, RWIndexSkipped p), prefix ++ [AuditCase 890 []; AuditConstruct 891 []; AuditConstruct
    892 []]).

Definition rw_ri_pair_merge_atomic {K Sort V} (s dropped : rw_index_state K Sort V) (p : rw_pair)
    (remaining : rw_pending_queue) (ra rb : rw_id)
    (prefix : audit_trace (rw_ri_pair_call K Sort V)) :
    (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_pair_call K Sort V) :=
  let '(forest, union_trace) := audit_uf_union audit_positive_encode ra rb (rw_index_forest s) in
  let '(found_root, root_trace) := audit_uf_find audit_positive_encode ra forest in
  let root := fst found_root in
  let parent_table := rw_index_parent_buckets s in
  let '(left_found, left_trace) := audit_map_get audit_positive_encode ra parent_table in
  let '(right_found, right_trace) := audit_map_get audit_positive_encode rb parent_table in
  let left_bucket :=
    match left_found with
    | Some b => b
    | None => FinSet.empty
    end in
  let right_bucket :=
    match right_found with
    | Some b => b
    | None => FinSet.empty
    end in
  let '(merged, union_set_trace) := audit_finset_union left_bucket right_bucket in
  let '(removed_a, remove_a_trace) := audit_map_remove audit_positive_encode ra parent_table in
  let '(without, remove_b_trace) := audit_map_remove audit_positive_encode rb removed_a in
  let '(parents, write_events) :=
    if FinSet.is_empty merged then (without, [AuditCase 893 []])
    else
      let '(updated, write_trace) := audit_map_set audit_positive_encode root merged without in
      (updated, [AuditCase 894 []; AuditCall (RIPairParentMap write_trace)]) in
  let '(ids, elements_trace) := audit_finset_elements merged in
  let '((order, dirty), mark_trace) := rw_ri_mark_dirty_atomic ids (rw_index_dirty_order s)
    (rw_index_dirty_set s) in
  let next := rw_ri_state_update s forest parents (rw_index_signatures s) (rw_index_node_keys s)
    order dirty remaining in
  ((next, RWIndexCongruence p ra rb root), prefix ++
    [AuditCall (RIPairUnion union_trace); AuditCall (RIPairForestFind root_trace);
      AuditCall (RIPairParentMap left_trace); AuditCall (RIPairParentMap right_trace);
      AuditCall (RIPairSetUnion union_set_trace); AuditCall (RIPairParentMap remove_a_trace);
      AuditCall (RIPairParentMap remove_b_trace)] ++ write_events ++
      [AuditCall (RIPairParentElements elements_trace); AuditCall (RIPairMark mark_trace);
      AuditConstruct 895 []; AuditConstruct 896 []; AuditConstruct 897 []]).

Definition rw_ri_pair_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) (p : rw_pair) (remaining : rw_pending_queue) :
    (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_pair_call K Sort V) :=
  let '(n, m) := p in
  let dropped := rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
    (rw_index_signatures s) (rw_index_node_keys s) (rw_index_dirty_order s) (rw_index_dirty_set s)
    remaining in
  let base := rw_index_base s in
  let node_enc := rw_ri_node_encoder op sort value in
  let '(first, first_trace) := audit_map_get audit_positive_encode n (rw_nodes base) in
  let prefix := [AuditConstruct 898 []; AuditCall (RIPairNode first_trace)] in
  match first with
  | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 899 []])
  | Some (a, node) =>
    let '(second, second_trace) := audit_map_get audit_positive_encode m (rw_nodes base) in
    let prefix := prefix ++ [AuditCase 900 []; AuditCall (RIPairNode second_trace)] in
    match second with
    | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 901 []])
    | Some (b, other) =>
      let '(first_root, first_root_trace) := rw_ri_find_atomic s a in
      let prefix := prefix ++ [AuditCase 902 []; AuditCall (RIPairFind a first_root
        first_root_trace)] in
      match first_root with
      | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 903 []])
      | Some ra =>
        let '(second_root, second_root_trace) := rw_ri_find_atomic s b in
        let prefix := prefix ++ [AuditCase 904 []; AuditCall (RIPairFind b second_root
          second_root_trace)] in
        match second_root with
        | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 905 []])
        | Some rb =>
          let '(ca, ca_trace) := rw_ri_canon_atomic s node in
          let '(code_a, code_a_trace) := node_enc ca in
          let '(cb, cb_trace) := rw_ri_canon_atomic s other in
          let '(code_b, code_b_trace) := node_enc cb in
          let '(same_code, code_compare_trace) := rw_ri_positive_dec_atomic code_a code_b in
          let prefix := prefix ++ [AuditCase 906 []; AuditCall (RIPairCanon node ca ca_trace);
            AuditCall (RIPairNodeCode ca code_a code_a_trace);
            AuditCall (RIPairCanon other cb cb_trace);
            AuditCall (RIPairNodeCode cb code_b code_b_trace);
            AuditCall (RIPairDecision code_a code_b same_code code_compare_trace)] in
          if same_code then
            let '(same_root, root_compare_trace) := rw_ri_positive_dec_atomic ra rb in
            let prefix := prefix ++ [AuditCase 907 []; AuditCall (RIPairDecision ra rb same_root
              root_compare_trace)] in
            if same_root then rw_ri_pair_skip dropped p (prefix ++ [AuditCase 908 []])
            else
              let '(first_sort, first_sort_trace) := audit_map_get audit_positive_encode a
                (rw_sorts base) in
              let prefix := prefix ++ [AuditCase 909 []; AuditCall (RIPairSort first_sort_trace)] in
              match first_sort with
              | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 910 []])
              | Some sa =>
                let '(second_sort, second_sort_trace) := audit_map_get audit_positive_encode b
                  (rw_sorts base) in
                let prefix := prefix ++ [AuditCase 911 []; AuditCall (RIPairSort
                  second_sort_trace)] in
                match second_sort with
                | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 912 []])
                | Some sb =>
                  let '(code_sa, sa_trace) := rw_external_encoding_events sort sa in
                  let '(code_sb, sb_trace) := rw_external_encoding_events sort sb in
                  let '(same_sort, sort_compare_trace) := rw_ri_positive_dec_atomic code_sa
                    code_sb in
                  let prefix := prefix ++ [AuditCase 913 []; AuditCall (RIPairSortCode sa code_sa
                    sa_trace);
                    AuditCall (RIPairSortCode sb code_sb sb_trace);
                    AuditCall (RIPairDecision code_sa code_sb same_sort sort_compare_trace)] in
                  if same_sort then
                    rw_ri_pair_merge_atomic s dropped p remaining ra rb
                      (prefix ++ [AuditCase 914 []])
                  else rw_ri_pair_skip dropped p (prefix ++ [AuditCase 915 []])
                end
              end
          else rw_ri_pair_skip dropped p (prefix ++ [AuditCase 916 []])
        end
      end
    end
  end.
