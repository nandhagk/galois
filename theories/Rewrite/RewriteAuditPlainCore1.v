(** * RewriteAuditPlainCore1

    This module implements plain indexed membership, rule application, and run phases.
    For example, if root lookup for identifier 1 fails, the same-class check returns false.
    Builds on: RewriteAuditIndexReference and
    RewriteAuditIndexRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexRun
  RewriteAuditPlainPrimitives.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_rw_ri_encoded_equal {A} (adapter : encoding A) (a b : A) : bool :=
  let p := rw_plain_rw_queue_encoder_run adapter a in
  let q := rw_plain_rw_queue_encoder_run adapter b in
  let answer := rw_plain_rw_ri_positive_dec_atomic p q in answer.

Definition rw_plain_rw_ri_same_class_atomic {K Sort V} (state : rw_index_state K Sort V)
    (a b : rw_id) : bool :=
  let first := rw_plain_rw_ri_find_atomic state a in
  match first with
  | None => false
  | Some x =>
    let second := rw_plain_rw_ri_find_atomic state b in
    match second with
    | None => false
    | Some y =>
      let answer := rw_plain_audit_positive_eqb x y in answer
    end
  end.

Fixpoint rw_plain_rw_ri_member_atomic {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_index_state K Sort V) (term : rw_term K Sort V)
    (root : rw_id) : bool :=
  match term with
  | RWVar ty v =>
    let candidates := rw_plain_rw_ri_bucket_ids (rw_plain_rw_external_encoding_events value)
      rw_plain_rw_external_events_work v (rw_index_variables state) in
    let fix visit (ids : list rw_id) : bool :=
      match ids with
      | nil => false
      | id :: rest =>
        let found := rw_plain_audit_map_get rw_plain_audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let head :=
          match found with
          | Some (owner, RWNVar ty' v') =>
            let same_sort := rw_plain_rw_ri_encoded_equal sort ty ty' in
            if same_sort then
              let same_value := rw_plain_rw_ri_encoded_equal value v v' in
              if same_value then
                let same_class := rw_plain_rw_ri_same_class_atomic state root owner in
                same_class
              else false
            else false
          | _ => false
          end in
        let tail := visit rest in head || tail
      end in
    let answer := visit candidates in answer
  | RWApp ty k children =>
    let candidates := rw_plain_rw_ri_bucket_ids (rw_plain_rw_external_encoding_events op)
      rw_plain_rw_external_events_work k (rw_index_operators state) in
    let fix visit (ids : list rw_id) : bool :=
      match ids with
      | nil => false
      | id :: rest =>
        let found := rw_plain_audit_map_get rw_plain_audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let head :=
          match found with
          | Some (owner, RWNApp ty' k' child_ids) =>
            let same_sort := rw_plain_rw_ri_encoded_equal sort ty ty' in
            if same_sort then
              let same_op := rw_plain_rw_ri_encoded_equal op k k' in
              if same_op then
                let same_class := rw_plain_rw_ri_same_class_atomic state root owner in
                let fix pairs (terms : list (rw_term K Sort V)) (classes : list rw_id) : bool :=
                  match terms, classes with
                  | nil, nil => true
                  | t :: ts, c :: cs =>
                    let head := rw_plain_rw_ri_member_atomic op sort value state t c in
                    let tail := pairs ts cs in head && tail
                  | _, _ => false
                  end in
                let same_children := pairs children child_ids in same_class && same_children
              else false
            else false
          | _ => false
          end in
        let tail := visit rest in head || tail
      end in
    let answer := visit candidates in answer
  end.

Definition rw_plain_rw_ri_grow_node {K Sort V} (node : rw_node K Sort V)
    (state : rw_graph K Sort V * positive) : (rw_id * (rw_graph K Sort V * positive)) :=
  let '(graph, id) := state in
  let aliases :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id id (rw_class_roots graph) in
  let sorts :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id (rw_node_sort node) (rw_sorts graph) in
  let nodes :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id (id, node) (rw_nodes graph) in
  let fresh := rw_plain_rw_fuel_pos_succ id in
  (id, (RwGraph (id :: rw_roots graph) (id :: rw_nodes_in graph) aliases sorts nodes, fresh)).

Fixpoint rw_plain_rw_ri_grow_term {K Sort V} (term : rw_term K Sort V)
    (state : rw_graph K Sort V * positive) : (rw_id * (rw_graph K Sort V * positive)) :=
  match term with
  | RWVar ty v =>
    let out := rw_plain_rw_ri_grow_node (RWNVar ty v) state in
    out
  | RWApp ty op terms =>
    let fix visit (terms : list (rw_term K Sort V)) (state : rw_graph K Sort V * positive) :
        (list rw_id * (rw_graph K Sort V * positive)) :=
      match terms with
      | nil => (nil, state)
      | term :: rest =>
        let '(id, next) := rw_plain_rw_ri_grow_term term state in
        let '(ids, final) := visit rest next in
        (id :: ids, final)
      end in
    let '(ids, next) := visit terms state in
    let out := rw_plain_rw_ri_grow_node (RWNApp ty op ids) next in
    out
  end.

Definition rw_plain_rw_ri_accept_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H)
    (rhs : rw_term K Sort V) : option (rw_index_state K Sort V) :=
  let graph := rw_plain_rw_ri_graph_atomic state in
  let '(rhs_root, (grown, _)) := rw_plain_rw_ri_grow_term rhs (graph, rw_index_fresh state) in
  let prepared := rw_plain_rw_ri_prepare_once op value grown in
  let first := rw_plain_rw_ri_find_atomic prepared (rw_attempt_root attempt) in
  match first with
  | None => None
  | Some a =>
    let second := rw_plain_rw_ri_find_atomic prepared rhs_root in
    match second with
    | None => None
    | Some b =>
      let left_sort := rw_plain_audit_map_get rw_plain_audit_positive_encode a (rw_sorts grown) in
      match left_sort with
      | None => None
      | Some sa =>
        let right_sort :=
          rw_plain_audit_map_get rw_plain_audit_positive_encode b (rw_sorts grown) in
        match right_sort with
        | None => None
        | Some sb =>
          let same_sort := rw_plain_rw_ri_encoded_equal sort sa sb in
          if same_sort then
            let '(machine, _) := rw_plain_rw_ri_pair_merge_atomic prepared prepared
              (rw_attempt_root attempt, rhs_root) (rw_index_pending prepared) a b nil in
            Some machine
          else None
        end
      end
    end
  end.

Fixpoint rw_plain_rw_rp_term_sorts {K Sort V} (terms : list (rw_term K Sort V)) : list Sort :=
  match terms with
  | nil => nil
  | t :: rest =>
    let tail := rw_plain_rw_rp_term_sorts rest in
    rw_sort t :: tail
  end.

Fixpoint rw_plain_rw_rp_type_atomic {K Sort V H} (sort : encoding Sort)
    (callbacks : rw_plain_callbacks K Sort V H) (term : rw_term K Sort V) : bool :=
  match term with
  | RWVar ty v =>
    let declared := rw_plain_rw_rp_var_sort callbacks v in
    match declared with
    | None => false
    | Some s =>
      let answer := rw_plain_rw_ri_encoded_equal sort ty s in
      answer
    end
  | RWApp ty op children =>
    let fix visit (terms : list (rw_term K Sort V)) : bool :=
      match terms with
      | nil => true
      | t :: rest =>
        let head := rw_plain_rw_rp_type_atomic sort callbacks t in
        let tail := visit rest in
        head && tail
      end in
    let typed := visit children in
    let sorts := rw_plain_rw_rp_term_sorts children in
    let shape := rw_plain_rw_rp_operator_shape callbacks op sorts ty in
    typed && shape
  end.

Fixpoint rw_plain_rw_rp_sub_check_atomic {K Sort V H} (sort : encoding Sort) (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (rule : rw_rule K Sort V H) (holes : list H)
    (bindings : Map.t H (rw_term K Sort V)) : bool :=
  match holes with
  | nil => true
  | h :: rest =>
    let declared := rw_plain_rw_rp_hole_sort callbacks rule h in
    let head :=
      match declared with
      | None => false
      | Some ty =>
        let binding :=
          rw_plain_audit_map_get (rw_plain_rw_external_encoding_events hole) h bindings in
        match binding with
        | None => false
        | Some term =>
          let same_sort := rw_plain_rw_ri_encoded_equal sort (rw_sort term) ty in
          if same_sort then
            let typed := rw_plain_rw_rp_type_atomic sort callbacks term in
            typed
          else false
        end
      end in
    let tail := rw_plain_rw_rp_sub_check_atomic sort hole callbacks rule rest bindings in
    head && tail
  end.

Fixpoint rw_plain_rw_rp_instantiate_atomic {K Sort V H} (hole : encoding H)
    (bindings : Map.t H (rw_term K Sort V)) (pattern : rw_pattern K Sort V H) :
    option (rw_term K Sort V) :=
  match pattern with
  | RWHole _ h =>
    let out := rw_plain_audit_map_get (rw_plain_rw_external_encoding_events hole) h bindings in
    out
  | RWPVar ty v => Some (RWVar ty v)
  | RWPApp ty op children =>
    let fix visit (ps : list (rw_pattern K Sort V H)) : option (list (rw_term K Sort V)) :=
      match ps with
      | nil => Some nil
      | p :: rest =>
        let head := rw_plain_rw_rp_instantiate_atomic hole bindings p in
        match head with
        | None => None
        | Some term =>
          let tail := visit rest in
          option_map (fun ts => term :: ts) tail
        end
      end in
    let args := visit children in
    option_map (RWApp ty op) args
  end.

Definition rw_plain_rw_rp_rule_body_gate_atomic {K Sort V H} (sort : encoding Sort)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H) (rule : rw_rule K Sort V H)
    (attempt : rw_attempt K Sort V H) : option (rw_term K Sort V * rw_term K Sort V) :=
  let bindings := rw_attempt_sub attempt in
  let typed := rw_plain_rw_rp_sub_check_atomic sort hole callbacks rule (rw_holes rule) bindings in
  let guard := rw_plain_rw_rp_guard_atomic hole callbacks rule bindings in
  if typed && guard then
    let lhs := rw_plain_rw_rp_instantiate_atomic hole bindings (rw_lhs rule) in
    match lhs with
    | None => None
    | Some left_term =>
      let rhs := rw_plain_rw_rp_instantiate_atomic hole bindings (rw_rhs rule) in
      option_map (fun right_term => (left_term, right_term)) rhs
    end
  else None.

Definition rw_plain_rw_rp_rule_gate_prepared_atomic {K Sort V H} (sort : encoding Sort)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) :=
  let found := rw_plain_audit_map_get rw_plain_audit_nat_encode (rw_attempt_rule attempt) table in
  match found with
  | None => None
  | Some rule =>
    let out := rw_plain_rw_rp_rule_body_gate_atomic sort hole callbacks rule attempt in
    out
  end.

Definition rw_plain_rw_ri_rule_step_prepared_atomic {K Sort V H} (op : encoding K)
    (sort : encoding Sort) (value : encoding V) (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V) :=
  let gate := rw_plain_rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  match gate with
  | None => None
  | Some (lhs, rhs) =>
    let represented :=
      rw_plain_rw_ri_member_atomic op sort value state lhs (rw_attempt_root attempt) in
    if represented then
      let out := rw_plain_rw_ri_accept_atomic op sort value state attempt rhs in
      out
    else None
  end.

Fixpoint rw_plain_rw_rp_rule_table_atomic {K Sort V H} (rules : list (rw_rule K Sort V H))
    (index : nat) : Map.t nat (rw_rule K Sort V H) :=
  match rules with
  | nil => Map.empty
  | rule :: rest =>
    let table := rw_plain_rw_rp_rule_table_atomic rest (S index) in
    let out := rw_plain_audit_map_set rw_plain_audit_nat_encode index rule table in
    out
  end.

Definition rw_plain_rw_ri_rule_step_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) : option (rw_index_state K Sort V) :=
  let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
  let out :=
    rw_plain_rw_ri_rule_step_prepared_atomic op sort value hole callbacks table state attempt in
  out.

Definition rw_plain_rw_ri_apply_prepared_atomic {K Sort V H} (op : encoding K)
    (sort : encoding Sort) (value : encoding V) (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) : option (rw_index_state K Sort V * list rw_index_event) :=
  let applied :=
    rw_plain_rw_ri_rule_step_prepared_atomic op sort value hole callbacks table state attempt in
  match applied with
  | None => None
  | Some next =>
    let out := rw_plain_rw_ri_rebuild_atomic op sort value next in
    Some out
  end.

Definition rw_plain_rw_ri_run_once {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_plain_strategy K Sort V H)
    (run : rw_ri_runner K Sort V H) : rw_ri_runner K Sort V H :=
  if rw_ri_runner_stopped run then run
  else
    let state := rw_ri_runner_state run in
    let offer := rw_plain_rw_rp_strategy_run op value strategy state in
    match offer with
    | None => RwRiRunner state true (rw_ri_runner_events run)
    | Some attempt =>
      let applied :=
        rw_plain_rw_ri_apply_prepared_atomic op sort value hole callbacks table state attempt in
      match applied with
      | None => RwRiRunner state false (RWRunRejected attempt :: rw_ri_runner_events run)
      | Some (next, events) =>
        RwRiRunner next false (RWRunAccepted attempt events :: rw_ri_runner_events run)
      end
    end.

Fixpoint rw_plain_rw_ri_run_repeat {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_plain_strategy K Sort V H)
    (fuel : positive) (run : rw_ri_runner K Sort V H) : rw_ri_runner K Sort V H :=
  if rw_ri_runner_stopped run then run
  else
    match fuel with
    | xH =>
      let out := rw_plain_rw_ri_run_once op sort value hole callbacks table strategy run in
      out
    | xO rest =>
      let middle :=
        rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy rest run in
      let out :=
        rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy rest middle in
      out
    | xI rest =>
      let first := rw_plain_rw_ri_run_once op sort value hole callbacks table strategy run in
      let middle :=
        rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy rest first in
      let out :=
        rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy rest middle in
      out
    end.

Definition rw_plain_rw_ri_run_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (strategy : rw_plain_strategy K Sort V H) (fuel : N)
    (graph : rw_graph K Sort V) :
    (rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H)) :=
  match fuel with
  | N0 => (RwRunResult graph RWFuelExhausted, nil, nil)
  | Npos fuel =>
    let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
    let prepared := rw_plain_rw_ri_prepare_once op value graph in
    let '(ready, initial_events) := rw_plain_rw_ri_rebuild_atomic op sort value prepared in
    let final :=
      rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy fuel
        (RwRiRunner ready false nil) in
    let result_graph := rw_plain_rw_ri_graph_atomic (rw_ri_runner_state final) in
    (RwRunResult result_graph (if rw_ri_runner_stopped final then RWStopped else RWFuelExhausted),
      initial_events, rw_ri_runner_events final)
  end.

Fixpoint rw_plain_rw_rp_append {A} (xs ys : list A) : list A :=
  match xs with
  | nil => ys
  | x :: rest =>
    let tail := rw_plain_rw_rp_append rest ys in
    x :: tail
  end.
