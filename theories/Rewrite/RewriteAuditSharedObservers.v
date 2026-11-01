(** * RewriteAuditSharedObservers

    Models scalar cost and size observation over shared trees with source work.
    For example, a DAG with root 1 and an empty node map fails validation and returns None.
    Builds on: RewriteAuditSharedExtract and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedExtract
  RewriteAuditSharedReference.
Import List.ListNotations.

Fixpoint rw_rd_shared_gather (table : rw_rd_table) (ids : list positive) : option (N * N) * nat :=
  match ids with
  | nil => (Some (0%N, 0%N), 64)
  | id :: rest =>
    let '(head, ht) := audit_map_get audit_positive_encode id table in
    let '(tail, tw) := rw_rd_shared_gather table rest in
    let hw := audit_map_source_work audit_basic_encoding_work ht in
    match head, tail with
    | Some c, Some (cost, size) =>
      let '(cost', cw) := rw_rd_N_add (rw_rd_cost c) cost in
      let '(size', sw) := rw_rd_N_add (rw_rd_size c) size in
      (Some (cost', size'), 64 + hw + tw + cw + sw)
    | _, _ => (None, 64 + hw + tw)
    end
  end.

Definition rw_rd_scalar_node {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (table : rw_rd_table) (id : positive) (node : rw_shared_node K Sort V) :
    option rw_rd_candidate * nat :=
  match node with
  | RWSharedVar _ _ _ _ v =>
    let '(cost, callback_work) := vc v in
    let '(binary, conversion_work) := rw_rd_nat_to_N cost in
    (Some (RwRdCandidate id binary 1%N), 64 + callback_work + conversion_work)
  | RWSharedApp _ _ _ _ op children =>
    let '(args, gather_work) := rw_rd_shared_gather table children in
    match args with
    | None => (None, 64 + gather_work)
    | Some (child_cost, child_size) =>
      let '(cost, callback_work) := oc op in
      let '(binary, conversion_work) := rw_rd_nat_to_N cost in
      let '(total, addition_work) := rw_rd_N_add binary child_cost in
      let '(size, size_work) := rw_rd_N_add 1%N child_size in
      (Some (RwRdCandidate id total size),
        64 + gather_work + callback_work + conversion_work + addition_work + size_work)
    end
  end.

Fixpoint rw_rd_scalar_pass {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (old : rw_rd_table) (entries : list (positive * rw_shared_node K Sort V)) (acc : rw_rd_table) :
    rw_rd_table * nat :=
  match entries with
  | nil => (acc, 64)
  | (id, node) :: rest =>
    let '(candidate, nw) := rw_rd_scalar_node vc oc old id node in
    match candidate with
    | None =>
      let '(out, tw) := rw_rd_scalar_pass vc oc old rest acc in
      (out, 64 + nw + tw)
    | Some c =>
      let '(next, wt) := audit_map_set audit_positive_encode id c acc in
      let '(out, tw) := rw_rd_scalar_pass vc oc old rest next in
      (out, 64 + nw + audit_map_source_work audit_basic_encoding_work wt + tw)
    end
  end.

Fixpoint rw_rd_scalar_rounds {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (entries : list (positive * rw_shared_node K Sort V)) (rounds : positive)
    (table : rw_rd_table) : rw_rd_table * nat :=
  match rounds with
  | xH =>
    let '(out, work) := rw_rd_scalar_pass vc oc table entries table in
    (out, 64 + work)
  | xO p =>
    let '(middle, mw) := rw_rd_scalar_rounds vc oc entries p table in
    let '(out, tw) := rw_rd_scalar_rounds vc oc entries p middle in
    (out, 64 + mw + tw)
  | xI p =>
    let '(first, fw) := rw_rd_scalar_pass vc oc table entries table in
    let '(middle, mw) := rw_rd_scalar_rounds vc oc entries p first in
    let '(out, tw) := rw_rd_scalar_rounds vc oc entries p middle in
    (out, 64 + fw + mw + tw)
  end.

Definition rw_rd_scalar_observe {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) : option (N * N) * nat :=
  let '(valid, vt) := rw_shared_validate_atomic dag in
  let vw := rw_shared_validation_trace_cost vt in
  if valid then
    let '(entries, et) := audit_map_elements (rw_shared_nodes K Sort V dag) in
    let '(count, lt) := rw_fuel_length entries in
    let setup := 64 + vw + audit_elements_work et + audit_work lt in
    match count with
    | 0 => (None, setup)
    | S rest =>
      let '(fuel, ft) := rw_fuel_to_positive rest in
      let '(table, tw) := rw_rd_scalar_rounds vc oc entries fuel Map.empty in
      let '(found, rt) := audit_map_get audit_positive_encode (rw_shared_root K Sort V dag) table in
      (option_map (fun c => (rw_rd_cost c, rw_rd_size c)) found,
        setup + audit_work ft + tw + audit_map_source_work audit_basic_encoding_work rt)
    end
  else (None, 64 + vw).

Fixpoint rw_rd_positive_to_nat (p : positive) : nat * nat :=
  match p with
  | xH => (1, 64)
  | xO rest =>
    let '(n, nw) := rw_rd_positive_to_nat rest in
    let '(out, add_trace) := rw_fuel_add n n in
    (out, 64 + nw + audit_work add_trace)
  | xI rest =>
    let '(n, nw) := rw_rd_positive_to_nat rest in
    let '(out, add_trace) := rw_fuel_add n n in
    (S out, 64 + nw + audit_work add_trace)
  end.

Definition rw_rd_N_to_nat (n : N) : nat * nat :=
  match n with
  | N0 => (0, 64)
  | Npos p => rw_rd_positive_to_nat p
  end.

Definition rw_shared_tree_cost_binary_atomic {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) : option N * nat :=
  let '(out, work) := rw_rd_scalar_observe vc oc dag in
  (option_map fst out, 64 + work).

Definition rw_shared_tree_size_binary_atomic {K Sort V} (dag : rw_shared_tree K Sort V) :
    option N * nat :=
  let '(out, work) := rw_rd_scalar_observe (fun _ => (0, 64)) (fun _ => (0, 64)) dag in
  (option_map snd out, 64 + work).

Definition rw_shared_tree_cost_atomic {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) : option nat * nat :=
  let '(out, work) := rw_shared_tree_cost_binary_atomic vc oc dag in
  match out with
  | None => (None, 64 + work)
  | Some n =>
    let '(result, conversion_work) := rw_rd_N_to_nat n in
    (Some result, 64 + work + conversion_work)
  end.

(** If a shared tree unfolds, scalar observation returns its unfolded cost and size
    in binary using the supplied cost values. *)
Definition rw_rd_scalar_agrees_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K -> nat * nat) (dag : rw_shared_tree K Sort V) tree,
    rw_shared_unfold dag = Some tree ->
    fst (rw_rd_scalar_observe vc oc dag) =
      Some (N.of_nat (rw_tree_cost (fun v => fst (vc v)) (fun k => fst (oc k)) tree),
        N.of_nat (rw_tree_size tree)).

(** If shared validation fails, scalar observation returns None. *)
Definition rw_rd_scalar_reject_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K -> nat * nat) (dag : rw_shared_tree K Sort V),
    rw_shared_validate dag = false ->
    fst (rw_rd_scalar_observe vc oc dag) = None.
