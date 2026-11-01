(** * RewriteAuditIndexExternal

    Defines external encoding, callback, guard, and strategy bounds for index runs.
    For example, a guard return has no hole queries to bound.
    Builds on: RewriteAuditIndexPrograms and
    RewriteAuditIndexRules. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

(** An adapter input fits when its encoded positive width and observed work meet the bounds. *)
Definition rw_whole_encoder_fits {A} (adapter : rw_queue_encoder_adapter A) (width body : nat)
    (input : A) : Prop :=
  let '(code, work) := rw_queue_encoder_run adapter input in
  Pos.size_nat code <= width /\ work <= body.

(** The sort, operator, and value atoms throughout a term fit their encoder bounds. *)
Fixpoint rw_whole_term_atoms {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat) (term :
    rw_term K Sort V) : Prop :=
  match term with
  | RWVar ty v => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits value width body v
  | RWApp ty k children =>
    rw_whole_encoder_fits sort width body ty /\ rw_whole_encoder_fits op width body k /\
    (fix visit (terms : list (rw_term K Sort V)) : Prop :=
      match terms with
      | nil => True
      | t :: rest => rw_whole_term_atoms op sort value width body t /\ visit rest
      end) children
  end.

(** The sort, operator, value, and hole atoms throughout a pattern fit their encoder bounds. *)
Fixpoint rw_whole_pattern_atoms {K Sort V H} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H) (width body : nat) (pattern : rw_pattern K Sort V H) : Prop :=
  match pattern with
  | RWHole ty h => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits hole width body h
  | RWPVar ty v => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits value width body v
  | RWPApp ty k children =>
    rw_whole_encoder_fits sort width body ty /\ rw_whole_encoder_fits op width body k /\
    (fix visit (patterns : list (rw_pattern K Sort V H)) : Prop :=
      match patterns with
      | nil => True
      | p :: rest => rw_whole_pattern_atoms op sort value hole width body p /\ visit rest
      end) children
  end.

(** A node's sort and its operator or value fit the corresponding encoder bounds. *)
Definition rw_whole_node_atoms {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat) (node :
    rw_node K Sort V) : Prop :=
  match node with
  | RWNVar ty v => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits value width body v
  | RWNApp ty k _ => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits op width body k
  end.

(** Every stored sort and node atom in the graph fits its encoder bounds. *)
Definition rw_whole_graph_atoms {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat) (graph :
    rw_graph K Sort V) : Prop :=
  Forall (fun entry => rw_whole_encoder_fits sort width body (snd entry))
    (Map.elements (rw_sorts graph)) /\
  Forall (fun entry => rw_whole_node_atoms op sort value width body (snd (snd entry)))
    (Map.elements (rw_nodes graph)).

(** The base graph and the stored operator, variable, signature, and node-key atoms
    in an index fit their encoder bounds. *)
Definition rw_whole_index_atoms {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (width body : nat) (state :
    rw_index_state K Sort V) : Prop :=
  rw_whole_graph_atoms op sort value width body (rw_index_base state) /\
  Forall (fun entry => rw_whole_encoder_fits op width body (fst entry))
    (Map.elements (rw_index_operators state)) /\
  Forall (fun entry => rw_whole_encoder_fits value width body (fst entry))
    (Map.elements (rw_index_variables state)) /\
  Forall (fun entry => rw_whole_node_atoms op sort value width body (fst entry))
    (Map.elements (rw_index_signatures state)) /\
  Forall (fun entry => rw_whole_node_atoms op sort value width body (snd entry))
    (Map.elements (rw_index_node_keys state)).

(** Variable-sort and operator-shape callback work for a term is bounded, and returned
    variable sorts fit the sort encoder bounds. *)
Fixpoint rw_whole_term_callbacks {K Sort V H} (sort : rw_queue_encoder_adapter Sort) (callbacks :
    rw_rp_rule_callbacks K Sort V H) (width body : nat) (term : rw_term K Sort V) : Prop :=
  match term with
  | RWVar _ v =>
    let '(declared, work) := rw_rp_var_sort callbacks v in
    work <= body /\
    match declared with
    | None => True
    | Some ty => rw_whole_encoder_fits sort width body ty
    end
  | RWApp ty k children =>
    snd (rw_rp_operator_shape callbacks k (map rw_sort children) ty) <= body /\
    (fix visit (terms : list (rw_term K Sort V)) : Prop :=
      match terms with
      | nil => True
      | t :: rest => rw_whole_term_callbacks sort callbacks width body t /\ visit rest
      end) children
  end.

Fixpoint rw_whole_guard_control {K Sort V H} (sub : rw_substitution K Sort V H) (program :
    rw_rp_guard_program K Sort V H) : nat :=
  match program with
  | RPGuardReturn _ body => 64 + body
  | RPGuardLookup body h next => 64 + body + rw_whole_guard_control sub (next (sub h))
  end.

(** Every hole queried along the guard program fits the hole encoder bounds. *)
Fixpoint rw_whole_guard_queries {K Sort V H} (hole : rw_queue_encoder_adapter H) (width body : nat)
    (sub : rw_substitution K Sort V H) (program : rw_rp_guard_program K Sort V H) : Prop :=
  match program with
  | RPGuardReturn _ _ => True
  | RPGuardLookup _ h next => rw_whole_encoder_fits hole width body h /\
      rw_whole_guard_queries hole width body sub (next (sub h))
  end.

(** Rule patterns and hole-sort callbacks satisfy the atom and callback bounds for
    each rule and its listed holes. *)
Definition rw_whole_rules_external {K Sort V H} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H) (width body : nat)
    (rules : list (rw_rule K Sort V H)) : Prop :=
  Forall (fun rule =>
    rw_whole_pattern_atoms op sort value hole width body (rw_lhs rule) /\
    rw_whole_pattern_atoms op sort value hole width body (rw_rhs rule) /\
    Forall (fun h => rw_whole_encoder_fits hole width body h /\
      let '(declared, work) := rw_rp_hole_sort callbacks rule h in
      work <= body /\
      match declared with
      | None => True
      | Some ty => rw_whole_encoder_fits sort width body ty
      end)
      (rw_holes rule)) rules.

(** Attempt bindings satisfy encoder and callback bounds; an existing rule also has
    bounded guard control and queries for that substitution. *)
Definition rw_whole_attempt_external {K Sort V H} (EH : encoding H) (op : rw_queue_encoder_adapter
    K) (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H) (width body : nat)
    (rules : list (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) : Prop :=
  Forall (fun entry => rw_whole_encoder_fits hole width body (fst entry) /\
    rw_whole_term_atoms op sort value width body (snd entry) /\
    rw_whole_term_callbacks sort callbacks width body (snd entry))
    (Map.elements (rw_attempt_sub attempt)) /\
  match nth_error rules (rw_attempt_rule attempt) with
  | None => True
  | Some rule =>
    let sub := fun h => Map.get EH h (rw_attempt_sub attempt) in
    rw_whole_guard_control sub (rw_rp_guard callbacks rule) <= body /\
    rw_whole_guard_queries hole width body sub (rw_rp_guard callbacks rule)
  end.

(** A view request satisfies the identifier-width or encoder bounds for its operand. *)
Definition rw_whole_request_external {K Sort V R} (op : rw_queue_encoder_adapter K) (value :
    rw_queue_encoder_adapter V) (width body : nat) (request : rw_rp_view_request K Sort V R) : Prop
    :=
  match request with
  | RPRequestFind id => Pos.size_nat id <= width
  | RPRequestSort id => Pos.size_nat id <= width
  | RPRequestNode id => Pos.size_nat id <= width
  | RPRequestOperator key => rw_whole_encoder_fits op width body key
  | RPRequestVariable key => rw_whole_encoder_fits value width body key
  | RPRequestParents id => Pos.size_nat id <= width
  | RPRequestRoots => True
  | RPRequestNodes => True
  | RPRequestGraph => True
  end.

Fixpoint rw_whole_view_control {K Sort V A} (view : rw_snapshot_view K Sort V) (program :
    rw_rp_view_program K Sort V A) : nat :=
  match program with
  | RPViewReturn _ body => 64 + body
  | RPViewAsk body request next =>
    64 + body + rw_whole_view_control view (next (rw_rp_view_plain_request view request))
  end.

(** Every request visited by a view program satisfies the external operand bounds. *)
Fixpoint rw_whole_view_queries {K Sort V A} (op : rw_queue_encoder_adapter K) (value :
    rw_queue_encoder_adapter V) (width body : nat) (view : rw_snapshot_view K Sort V) (program :
    rw_rp_view_program K Sort V A) : Prop :=
  match program with
  | RPViewReturn _ _ => True
  | RPViewAsk _ request next => rw_whole_request_external op value width body request /\
      rw_whole_view_queries op value width body view
        (next (rw_rp_view_plain_request view request))
  end.

(** For every bounded index with fitting atoms, strategy control and view queries
    meet their body and operand bounds. *)
Definition rw_whole_strategy_external {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV :
    encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V) (dimension width body : nat) (adapter : rw_rp_strategy_adapter K
    Sort V H) : Prop :=
  forall state,
    rw_whole_index_dimension state <= Nat.pow (S (dimension + width)) 8 ->
    rw_whole_index_atoms op sort value width body state ->
    let view := rw_index_view EK ES EV state in
    rw_whole_view_control view (rw_rp_strategy_program adapter) <= body /\
    rw_whole_view_queries op value width body view (rw_rp_strategy_program adapter).
