(** * RewriteAuditSharedExtract

    This module relates shared extraction rounds and candidate selection to their source work.
    For example, the empty-roots case relates a graph with empty lists and maps at root 1
    to None.
    Builds on: RewriteAuditSharedCompare and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedCompare
  RewriteAuditSharedReference.
Import List.ListNotations.

Fixpoint rw_rd_positive_add (a b : positive) : positive * nat :=
  match a, b with
  | xH, xH => (xO xH, 64)
  | xH, xO y => (xI y, 64)
  | xH, xI y =>
    let '(s, w) := rw_fuel_pos_succ y in
    (xO s, 64 + audit_work w)
  | xO x, xH => (xI x, 64)
  | xI x, xH =>
    let '(s, w) := rw_fuel_pos_succ x in
    (xO s, 64 + audit_work w)
  | xO x, xO y =>
    let '(s, w) := rw_rd_positive_add x y in
    (xO s, 64 + w)
  | xO x, xI y =>
    let '(s, w) := rw_rd_positive_add x y in
    (xI s, 64 + w)
  | xI x, xO y =>
    let '(s, w) := rw_rd_positive_add x y in
    (xI s, 64 + w)
  | xI x, xI y =>
    let '(s, w) := rw_rd_positive_add x y in
    let '(t, tw) := rw_fuel_pos_succ s in
    (xO t, 64 + w + audit_work tw)
  end.

Definition rw_rd_N_add (a b : N) : N * nat :=
  match a, b with
  | N0, _ => (b, 64)
  | _, N0 => (a, 64)
  | Npos x, Npos y =>
    let '(s, w) := rw_rd_positive_add x y in
    (Npos s, 64 + w)
  end.

Definition rw_rd_N_compare (a b : N) : comparison * nat :=
  match a, b with
  | N0, N0 => (Eq, 64)
  | N0, _ => (Lt, 64)
  | _, N0 => (Gt, 64)
  | Npos x, Npos y => rw_rd_positive_compare_cont Eq x y
  end.

Fixpoint rw_rd_nat_to_N (n : nat) : N * nat :=
  match n with
  | 0 => (0%N, 64)
  | S rest =>
    let '(x, w) := rw_rd_nat_to_N rest in
    let '(out, aw) := rw_rd_N_add 1%N x in
    (out, 64 + w + aw)
  end.

Record rw_rd_candidate := RwRdCandidate {
  rw_rd_pointer : positive;
  rw_rd_cost : N;
  rw_rd_size : N
}.

Record rw_rd_store (K Sort V : Type) := RwRdStore {
  rw_rd_nodes : Map.t positive (rw_shared_node K Sort V);
  rw_rd_next : positive
}.
Arguments RwRdStore {K Sort V}.
Arguments rw_rd_nodes {K Sort V}.
Arguments rw_rd_next {K Sort V}.

Definition rw_rd_table :=
  Map.t rw_id rw_rd_candidate.

Definition rw_rd_candidate_get {K Sort V} (g : rw_graph K Sort V)
    (table : rw_rd_table) (id : rw_id) :
    option rw_rd_candidate * nat :=
  let '(root, rt) := audit_map_get audit_positive_encode id (rw_class_roots g) in
  match root with
  | None => (None, 64 + audit_map_source_work audit_basic_encoding_work rt)
  | Some r =>
    let '(answer, add_trace) := audit_map_get audit_positive_encode r table in
    (answer, 64 + audit_map_source_work audit_basic_encoding_work rt +
      audit_map_source_work audit_basic_encoding_work add_trace)
  end.

Fixpoint rw_rd_gather {K Sort V} (g : rw_graph K Sort V) (table : rw_rd_table) (ids : list rw_id) :
    option (list positive * N * N) * nat :=
  match ids with
  | nil => (Some (nil, 0%N, 0%N), 64)
  | id :: rest =>
    let '(head, hw) := rw_rd_candidate_get g table id in
    let '(tail, tw) := rw_rd_gather g table rest in
    match head, tail with
    | Some c, Some (pointers, cost, size) =>
      let '(cost', cw) := rw_rd_N_add (rw_rd_cost c) cost in
      let '(size', sw) := rw_rd_N_add (rw_rd_size c) size in
      (Some (rw_rd_pointer c :: pointers, cost', size'), 64 + hw + tw + cw + sw)
    | _, _ => (None, 64 + hw + tw)
    end
  end.

Definition rw_rd_allocate {K Sort V} (node : rw_shared_node K Sort V) (cost size : N)
    (store : rw_rd_store K Sort V) : (rw_rd_candidate * rw_rd_store K Sort V) * nat :=
  let id := rw_rd_next store in
  let '(nodes, nt) := audit_map_set audit_positive_encode id node (rw_rd_nodes store) in
  let '(fresh, ft) := rw_fuel_pos_succ id in
  ((RwRdCandidate id cost size, RwRdStore nodes fresh),
    64 + audit_map_source_work audit_basic_encoding_work nt + audit_work ft).

Definition rw_rd_production {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (g : rw_graph K Sort V) (old : rw_rd_table) (node : rw_node K Sort V)
    (store : rw_rd_store K Sort V) : (option rw_rd_candidate * rw_rd_store K Sort V) * nat :=
  match node with
  | RWNVar ty v =>
    let '(cost, callback_work) := vc v in
    let '(binary, conversion_work) := rw_rd_nat_to_N cost in
    let '((candidate, next), allocation_work) :=
      rw_rd_allocate (RWSharedVar K Sort V ty v) binary 1%N store in
    ((Some candidate, next), 64 + callback_work + conversion_work + allocation_work)
  | RWNApp ty op children =>
    let '(args, gather_work) := rw_rd_gather g old children in
    match args with
    | None => ((None, store), 64 + gather_work)
    | Some (pointers, child_cost, child_size) =>
      let '(cost, callback_work) := oc op in
      let '(binary, conversion_work) := rw_rd_nat_to_N cost in
      let '(total, addition_work) := rw_rd_N_add binary child_cost in
      let '(size, size_work) := rw_rd_N_add 1%N child_size in
      let '((candidate, next), allocation_work) :=
        rw_rd_allocate (RWSharedApp K Sort V ty op pointers) total size store in
      ((Some candidate, next), 64 + gather_work + callback_work + conversion_work +
        addition_work + size_work + allocation_work)
    end
  end.

(** Candidate selection relates two candidates to the chosen candidate and work after
    comparing cost, size, and, when needed, shared codes. *)
Inductive rw_rd_choose_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (store : rw_rd_store K Sort V) (old fresh : rw_rd_candidate) :
    rw_rd_candidate -> nat -> Prop :=
  | RDChooseCost : forall answer work,
      rw_rd_N_compare (rw_rd_cost old) (rw_rd_cost fresh) = (answer, work) ->
      answer <> Eq ->
      rw_rd_choose_run op sort value store old fresh
        (match answer with
        | Lt => old
        | _ => fresh
        end) (64 + work)
  | RDChooseSize : forall cost_work answer work,
      rw_rd_N_compare (rw_rd_cost old) (rw_rd_cost fresh) = (Eq, cost_work) ->
      rw_rd_N_compare (rw_rd_size old) (rw_rd_size fresh) = (answer, work) ->
      answer <> Eq ->
      rw_rd_choose_run op sort value store old fresh
        (match answer with
        | Lt => old
        | _ => fresh
        end) (64 + cost_work + work)
  | RDChooseCode : forall cost_work size_work answer work,
      rw_rd_N_compare (rw_rd_cost old) (rw_rd_cost fresh) = (Eq, cost_work) ->
      rw_rd_N_compare (rw_rd_size old) (rw_rd_size fresh) = (Eq, size_work) ->
      rw_shared_compare_run op sort value
        (RwSharedTree K Sort V (rw_rd_pointer old) (rw_rd_nodes store))
        (RwSharedTree K Sort V (rw_rd_pointer fresh) (rw_rd_nodes store))
        (Some answer) work ->
      rw_rd_choose_run op sort value store old fresh (if answer then old else fresh)
        (64 + cost_work + size_work + work).

(** Candidate insertion uses the supplied store for comparison and relates an input
    table to an output table and work. *)
Inductive rw_rd_insert_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (store : rw_rd_store K Sort V) (root : rw_id) (fresh : rw_rd_candidate)
    (table : rw_rd_table) : rw_rd_table -> nat -> Prop :=
  | RDInsertAbsent : forall rt out wt,
      audit_map_get audit_positive_encode root table = (None, rt) ->
      audit_map_set audit_positive_encode root fresh table = (out, wt) ->
      rw_rd_insert_run op sort value store root fresh table out
        (64 + audit_map_source_work audit_basic_encoding_work rt +
          audit_map_source_work audit_basic_encoding_work wt)
  | RDInsertPresent : forall rt old chosen choose_work out wt,
      audit_map_get audit_positive_encode root table = (Some old, rt) ->
      rw_rd_choose_run op sort value store old fresh chosen choose_work ->
      audit_map_set audit_positive_encode root chosen table = (out, wt) ->
      rw_rd_insert_run op sort value store root fresh table out
        (64 + audit_map_source_work audit_basic_encoding_work rt + choose_work +
          audit_map_source_work audit_basic_encoding_work wt).

(** One extraction round relates a node list, table, and store to the updated table,
    store, and work. *)
Inductive rw_rd_round_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K Sort V)
    (old : rw_rd_table) : list (rw_id * (rw_id * rw_node K Sort V)) ->
    rw_rd_table -> rw_rd_store K Sort V -> rw_rd_table -> rw_rd_store K Sort V -> nat -> Prop :=
  | RDRoundNil : forall table store,
      rw_rd_round_run op sort value vc oc g old nil table store table store 64
  | RDRoundSkip : forall id owner node rest table store root rt produced next pw out final tw,
      audit_map_get audit_positive_encode owner (rw_class_roots g) = (root, rt) ->
      rw_rd_production vc oc g old node store = ((produced, next), pw) ->
      (root = None \/ produced = None) ->
      rw_rd_round_run op sort value vc oc g old rest table next out final tw ->
      rw_rd_round_run op sort value vc oc g old ((id, (owner, node)) :: rest) table store out final
        (64 + audit_map_source_work audit_basic_encoding_work rt + pw + tw)
  | RDRoundInsert : forall id owner node rest table store root rt fresh next pw inserted iw out
      final tw,
      audit_map_get audit_positive_encode owner (rw_class_roots g) = (Some root, rt) ->
      rw_rd_production vc oc g old node store = ((Some fresh, next), pw) ->
      rw_rd_insert_run op sort value next root fresh table inserted iw ->
      rw_rd_round_run op sort value vc oc g old rest inserted next out final tw ->
      rw_rd_round_run op sort value vc oc g old ((id, (owner, node)) :: rest) table store out final
        (64 + audit_map_source_work audit_basic_encoding_work rt + pw + iw + tw).

(** Fuel-bounded extraction rounds relate an input table and store to their outputs
    and accumulated work. *)
Inductive rw_rd_rounds_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K Sort V)
    (entries : list (rw_id * (rw_id * rw_node K Sort V))) :
    positive -> rw_rd_table -> rw_rd_store K Sort V -> rw_rd_table -> rw_rd_store K Sort V ->
    nat -> Prop :=
  | RDRoundsOne : forall table store out final work,
      rw_rd_round_run op sort value vc oc g table entries table store out final work ->
      rw_rd_rounds_run op sort value vc oc g entries xH table store out final (64 + work)
  | RDRoundsEven : forall p table store middle ms out final first second,
      rw_rd_rounds_run op sort value vc oc g entries p table store middle ms first ->
      rw_rd_rounds_run op sort value vc oc g entries p middle ms out final second ->
      rw_rd_rounds_run op sort value vc oc g entries (xO p) table store out final
        (64 + first + second)
  | RDRoundsOdd : forall p table store next ns middle ms out final one first second,
      rw_rd_round_run op sort value vc oc g table entries table store next ns one ->
      rw_rd_rounds_run op sort value vc oc g entries p next ns middle ms first ->
      rw_rd_rounds_run op sort value vc oc g entries p middle ms out final second ->
      rw_rd_rounds_run op sort value vc oc g entries (xI p) table store out final
        (64 + one + first + second).

(** Shared extraction relates a graph and root to an optional shared tree and source work. *)
Inductive rw_shared_extract_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K Sort V) (root : rw_id) :
    option (rw_shared_tree K Sort V) -> nat -> Prop :=
  | RDExtractEmpty : forall lt,
      rw_fuel_length (rw_roots g) = (0, lt) ->
      rw_shared_extract_run op sort value vc oc g root None (64 + audit_work lt)
  | RDExtractMissing : forall n lt fuel ft entries et table store rounds_work lookup_work,
      rw_fuel_length (rw_roots g) = (S n, lt) ->
      rw_fuel_to_positive n = (fuel, ft) ->
      audit_map_elements (rw_nodes g) = (entries, et) ->
      rw_rd_rounds_run op sort value vc oc g entries fuel Map.empty
        (RwRdStore Map.empty 1%positive) table store rounds_work ->
      rw_rd_candidate_get g table root = (None, lookup_work) ->
      rw_shared_extract_run op sort value vc oc g root None
        (64 + audit_work lt + audit_work ft + audit_elements_work et + rounds_work + lookup_work)
  | RDExtractFound : forall n lt fuel ft entries et table store rounds_work candidate lookup_work,
      rw_fuel_length (rw_roots g) = (S n, lt) ->
      rw_fuel_to_positive n = (fuel, ft) ->
      audit_map_elements (rw_nodes g) = (entries, et) ->
      rw_rd_rounds_run op sort value vc oc g entries fuel Map.empty
        (RwRdStore Map.empty 1%positive) table store rounds_work ->
      rw_rd_candidate_get g table root = (Some candidate, lookup_work) ->
      rw_shared_extract_run op sort value vc oc g root
        (Some (RwSharedTree K Sort V (rw_rd_pointer candidate) (rw_rd_nodes store)))
        (64 + audit_work lt + audit_work ft + audit_elements_work et + rounds_work + lookup_work).

Definition rw_rd_node_input_weight {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (node : rw_shared_node K
    Sort V) : nat :=
  let '(header, work) := rw_rd_header op sort value node in
  S (work + fold_right (fun p n => Pos.size_nat p + n) 0 header +
    rw_shared_children_bits (rw_rd_children node)).

Definition rw_rd_graph_input_weight {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (dag : rw_shared_tree K Sort V) : nat :=
  let entries := Map.elements (rw_shared_nodes K Sort V dag) in
  S (Pos.size_nat (rw_shared_root K Sort V dag) +
    fold_right (fun entry n =>
      Pos.size_nat (fst entry) + rw_rd_node_input_weight op sort value (snd entry) + n) 0 entries +
    audit_trie_nodes (rw_shared_nodes K Sort V dag)).

Definition rw_rd_compare_budget {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (left right : rw_shared_tree K Sort V) : nat :=
  Nat.pow (1024 * S (rw_rd_graph_input_weight op sort value left +
    rw_rd_graph_input_weight op sort value right)) 8.

(** The work of a shared comparison run is bounded by its comparison budget. *)
Definition rw_rd_compare_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) left right answer work,
    rw_shared_compare_run op sort value left right answer work ->
    work <= rw_rd_compare_budget op sort value left right.

(** If encoder adapters agree and the graph is well formed, a shared extraction run
    fails with tree extraction or returns a well-formed DAG unfolding to its tree. *)
Definition rw_rd_extract_agrees_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat * nat) (oc : K -> nat * nat)
    (sig : rw_signature K Sort V) g root answer work,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_graph_wf sig g ->
    rw_shared_extract_run op sort value vc oc g root answer work ->
    match answer, rw_extract_tree EK ES EV (fun v => fst (vc v))
        (fun k => fst (oc k)) g root with
    | None, None => True
    | Some dag, Some tree =>
      rw_shared_wf dag /\ rw_shared_unfold dag = Some tree
    | _, _ => False
    end.

(** Shared extraction has a result and work observation for every graph and root. *)
Definition rw_rd_extract_total_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat * nat) (oc : K -> nat * nat) g root,
    exists answer work, rw_shared_extract_run op sort value vc oc g root answer work.

(** Two shared extraction runs on the same inputs have equal results and work. *)
Definition rw_rd_extract_unique_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat * nat) (oc : K -> nat * nat)
    g root first second fw sw,
    rw_shared_extract_run op sort value vc oc g root first fw ->
    rw_shared_extract_run op sort value vc oc g root second sw ->
    first = second /\ fw = sw.
