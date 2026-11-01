(** * RewriteAuditProofRepresentation

    This module defines representation witnesses and their search in an indexed graph.
    For example, a valid node matching variable 0 has an empty child-reference list.
    Builds on: RewriteAuditIndexMembership and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Record rw_repr_node (K Sort V : Type) := RWReprNode {
  rw_repr_class : rw_id;
  rw_repr_graph_node : rw_id;
  rw_repr_term : rw_term K Sort V;
  rw_repr_children : list positive
}.
Arguments RWReprNode {K Sort V}.
Arguments rw_repr_class {K Sort V}.
Arguments rw_repr_graph_node {K Sort V}.
Arguments rw_repr_term {K Sort V}.
Arguments rw_repr_children {K Sort V}.

Record rw_repr_witness (K Sort V : Type) := RWReprWitness {
  rw_repr_root : positive;
  rw_repr_ids : list positive;
  rw_repr_nodes : Map.t positive (rw_repr_node K Sort V)
}.
Arguments RWReprWitness {K Sort V}.
Arguments rw_repr_root {K Sort V}.
Arguments rw_repr_ids {K Sort V}.
Arguments rw_repr_nodes {K Sort V}.

(** A representation node matches a graph node in the same class; its application child
    references are smaller, exist, and contain the corresponding class and term. *)
Definition rw_repr_node_valid {K Sort V} (g : rw_graph K Sort V) (w : rw_repr_witness K Sort V)
    (id : positive) (n : rw_repr_node K Sort V) : Prop :=
  exists owner root graph_node,
    rw_node_at g (rw_repr_graph_node n) = Some (owner, graph_node) /\
    rw_find g owner = Some root /\ rw_find g (rw_repr_class n) = Some root /\
    match graph_node, rw_repr_term n with
    | RWNVar s v, RWVar s' v' => s = s' /\ v = v' /\ rw_repr_children n = nil
    | RWNApp s op ids, RWApp s' op' terms =>
      s = s' /\ op = op' /\ length ids = length terms /\
      Forall2 (fun child pair => (child < id)%positive /\
        exists m, Map.get positive_encoding child (rw_repr_nodes w) = Some m /\
          rw_repr_class m = fst pair /\ rw_repr_term m = snd pair)
        (rw_repr_children n) (combine ids terms)
    | _, _ => False
    end.

(** A representation witness has a well-formed enumerated node map, a root for the
    requested class and term, and valid representation nodes. *)
Definition rw_repr_witness_valid {K Sort V} (g : rw_graph K Sort V) (c : rw_id)
    (t : rw_term K Sort V) (w : rw_repr_witness K Sort V) : Prop :=
  NoDup (rw_repr_ids w) /\
  Map.wf positive_encoding (rw_repr_nodes w) /\
  (forall id, In id (rw_repr_ids w) <-> exists n, Map.get positive_encoding id (rw_repr_nodes w) =
    Some n) /\
  (exists n, Map.get positive_encoding (rw_repr_root w) (rw_repr_nodes w) = Some n /\
    rw_repr_class n = c /\ rw_repr_term n = t) /\
  forall id n, Map.get positive_encoding id (rw_repr_nodes w) = Some n ->
    rw_repr_node_valid g w id n.

Record rw_rp_repr_acc (K Sort V : Type) := RwRpReprAcc {
  rw_rp_repr_ids : list positive;
  rw_rp_repr_nodes : Map.t positive (rw_repr_node K Sort V);
  rw_rp_repr_next : positive
}.
Arguments RwRpReprAcc {K Sort V}.
Arguments rw_rp_repr_ids {K Sort V}.
Arguments rw_rp_repr_nodes {K Sort V}.
Arguments rw_rp_repr_next {K Sort V}.

Definition rw_rp_repr_emit {K Sort V} (node : rw_repr_node K Sort V)
    (acc : rw_rp_repr_acc K Sort V) : (positive * rw_rp_repr_acc K Sort V) * nat :=
  let id := rw_rp_repr_next acc in
  let '(nodes, trace) := audit_map_set audit_positive_encode id node (rw_rp_repr_nodes acc) in
  let '(fresh, successor_trace) := rw_fuel_pos_succ id in
  ((id, RwRpReprAcc (id :: rw_rp_repr_ids acc) nodes fresh),
    64 + audit_map_source_work audit_basic_encoding_work trace + audit_work successor_trace).

Fixpoint rw_rp_repr_term_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (term : rw_term K Sort V) (root : rw_id)
    (acc : rw_rp_repr_acc K Sort V) {struct term} :
    option (positive * rw_rp_repr_acc K Sort V) * nat :=
  let key_match := fun owner ty other_ty =>
    let '(same_sort, sw) := rw_ri_encoded_equal sort ty other_ty in
    if same_sort then
      let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
      (same_class, 64 + sw + cw)
    else (false, 64 + sw) in
  match term with
  | RWVar ty v =>
    let '(candidates, bw) := rw_ri_bucket_ids (rw_external_encoding_events value)
      rw_external_events_work v (rw_index_variables state) in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) * nat :=
      match ids with
      | nil => (None, 64)
      | id :: rest =>
        let '(found, trace) := audit_map_get audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
        let '(candidate, candidate_work) :=
          match found with
          | Some (owner, RWNVar declared other) =>
            let '(same, kw) := key_match owner ty declared in
            if same then
              let '(same_value, vw) := rw_ri_encoded_equal value v other in
              if same_value then
                let '(out, ew) := rw_rp_repr_emit (RWReprNode root id term nil) acc in
                (Some out, kw + vw + ew)
              else (None, kw + vw)
            else (None, kw)
          | _ => (None, 64)
          end in
        match candidate with
        | Some out => (Some out, prefix + candidate_work)
        | None =>
          let '(out, later_work) := visit rest in
          (out, prefix + candidate_work + later_work)
        end
      end in
    let '(out, work) := visit candidates in (out, 64 + bw + work)
  | RWApp ty key terms =>
    let '(candidates, bw) := rw_ri_bucket_ids (rw_external_encoding_events op)
      rw_external_events_work key (rw_index_operators state) in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) * nat :=
      match ids with
      | nil => (None, 64)
      | id :: rest =>
        let '(found, trace) := audit_map_get audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
        let '(candidate, candidate_work) :=
          match found with
          | Some (owner, RWNApp declared other children) =>
            let '(same, kw) := key_match owner ty declared in
            if same then
              let '(same_op, ow) := rw_ri_encoded_equal op key other in
              if same_op then
                let fix descend (ts : list (rw_term K Sort V)) (cs : list rw_id)
                    (acc : rw_rp_repr_acc K Sort V) :
                    option (list positive * rw_rp_repr_acc K Sort V) * nat :=
                  match ts, cs with
                  | nil, nil => (Some (nil, acc), 64)
                  | t :: ts, c :: cs =>
                    let '(head, hw) := rw_rp_repr_term_atomic op sort value state t c acc in
                    match head with
                    | None => (None, 64 + hw)
                    | Some (pointer, next) =>
                      let '(tail, tw) := descend ts cs next in
                      (option_map (fun pair => (pointer :: fst pair, snd pair)) tail,
                        64 + hw + tw)
                    end
                  | _, _ => (None, 64)
                  end in
                let '(children, cw) := descend terms children acc in
                match children with
                | None => (None, kw + ow + cw)
                | Some (pointers, next) =>
                  let '(out, ew) := rw_rp_repr_emit (RWReprNode root id term pointers) next in
                  (Some out, kw + ow + cw + ew)
                end
              else (None, kw + ow)
            else (None, kw)
          | _ => (None, 64)
          end in
        match candidate with
        | Some out => (Some out, prefix + candidate_work)
        | None =>
          let '(out, later_work) := visit rest in
          (out, prefix + candidate_work + later_work)
        end
      end in
    let '(out, work) := visit candidates in (out, 64 + bw + work)
  end.

Definition rw_rp_repr_find_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (root : rw_id) (term : rw_term K Sort V) :
    option (rw_repr_witness K Sort V) * nat :=
  let '(found, work) := rw_rp_repr_term_atomic op sort value state term root
    (RwRpReprAcc nil Map.empty 1%positive) in
  (option_map (fun pair =>
    RWReprWitness (fst pair) (rw_rp_repr_ids (snd pair)) (rw_rp_repr_nodes (snd pair))) found,
    64 + work).

(** With agreeing encoders, a well-formed graph, and an agreeing snapshot, the search
    specification requires a valid returned witness or, on None, absence of representation. *)
Definition rw_rp_repr_find_spec_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (sig : rw_signature K Sort V) state root term,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_graph_wf sig (rw_index_graph state) ->
    rw_snapshot_agrees (rw_index_graph state) (rw_index_view EK ES EV state) ->
    match fst (rw_rp_repr_find_atomic op sort value state root term) with
    | Some witness => rw_repr_witness_valid (rw_index_graph state) root term witness
    | None => ~ rw_represents (rw_index_graph state) root term
    end.
