(** * RewriteAuditSharedReference

    Defines shared trees, their well-formedness, validation, and unfolding observers.
    For example, a shared tree with an empty node map cannot have the required stored root.
    Builds on: RewriteSyntax and
    CollectionsMap. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Inductive rw_shared_node (K Sort V : Type) : Type :=
  | RWSharedVar : Sort -> V -> rw_shared_node K Sort V
  | RWSharedApp : Sort -> K -> list positive -> rw_shared_node K Sort V.

Record rw_shared_tree (K Sort V : Type) := RwSharedTree {
  rw_shared_root : positive;
  rw_shared_nodes : Map.t positive (rw_shared_node K Sort V)
}.

(** A shared tree has a well-formed map, an existing root, and existing children with
    strictly decreasing ranks at each application node. *)
Definition rw_shared_wf {K Sort V} (dag : rw_shared_tree K Sort V) : Prop :=
  Map.wf positive_encoding (rw_shared_nodes K Sort V dag) /\
  (exists node,
    Map.get positive_encoding (rw_shared_root K Sort V dag) (rw_shared_nodes K Sort V dag) =
      Some node) /\
  exists rank : positive -> nat,
    forall id s op children,
      Map.get positive_encoding id (rw_shared_nodes K Sort V dag) =
        Some (RWSharedApp K Sort V s op children) ->
      forall child, In child children ->
        (exists node, Map.get positive_encoding child (rw_shared_nodes K Sort V dag) = Some node) /\
        rank child < rank id.

Inductive rw_shared_validation_call (K Sort V : Type) : Type :=
  | RWSharedEnumerate : Trie.t (positive * rw_shared_node K Sort V) ->
      list (positive * (positive * rw_shared_node K Sort V)) ->
      list (audit_elements_event (positive * rw_shared_node K Sort V)) ->
      rw_shared_validation_call K Sort V
  | RWSharedKeyCheck : positive -> positive -> bool -> rw_shared_validation_call K Sort V
  | RWSharedRootRead : positive -> Trie.t (positive * rw_shared_node K Sort V) -> option
      (rw_shared_node K Sort V) -> rw_shared_validation_call K Sort V
  | RWSharedLength : nat -> audit_trace unit -> rw_shared_validation_call K Sort V
  | RWSharedReadyRead : positive -> FinSet.t positive -> option unit -> rw_shared_validation_call K
      Sort V
  | RWSharedReadyAdd : positive -> FinSet.t positive -> FinSet.t positive ->
      rw_shared_validation_call K Sort V.
Arguments RWSharedEnumerate {K Sort V}.
Arguments RWSharedKeyCheck {K Sort V}.
Arguments RWSharedRootRead {K Sort V}.
Arguments RWSharedLength {K Sort V}.
Arguments RWSharedReadyRead {K Sort V}.
Arguments RWSharedReadyAdd {K Sort V}.

Definition rw_shared_validation_event_cost {K Sort V}
    (event : audit_event (rw_shared_validation_call K Sort V)) : nat :=
  match event with
  | AuditCall (RWSharedEnumerate _ _ events) => 1 + audit_elements_work events
  | AuditCall (RWSharedKeyCheck p q _) =>
    1 + audit_positive_eqb_source_work (snd (audit_positive_eqb p q))
  | AuditCall (RWSharedRootRead id input _) => 2 + audit_trie_get_source_work id input
  | AuditCall (RWSharedLength _ trace) => 1 + audit_work trace
  | AuditCall (RWSharedReadyRead id input _) => 2 + audit_trie_get_source_work id input
  | AuditCall (RWSharedReadyAdd id input _) =>
    2 + audit_trie_update_source_work id (Some (id, tt)) input
  | _ => 1
  end.

Definition rw_shared_validation_trace_cost {K Sort V}
    (trace : audit_trace (rw_shared_validation_call K Sort V)) : nat :=
  fold_right (fun event total => rw_shared_validation_event_cost event + total) 0 trace.

Fixpoint rw_shared_length_atomic {A} (xs : list A) : nat * audit_trace unit :=
  match xs with
  | nil => (0, [AuditCase 751 []; AuditConstruct 752 []])
  | _ :: rest =>
    let '(n, trace) := rw_shared_length_atomic rest in
    (S n, [AuditCase 753 []; AuditArithmetic 754 []] ++ trace ++ [AuditConstruct 755 []])
  end.

Fixpoint rw_shared_children_ready {K Sort V} (children : list positive)
    (ready : FinSet.t positive) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  match children with
  | nil => (true, [AuditCase 720 []; AuditConstruct 721 []])
  | child :: rest =>
    let found := Map.code_get child ready in
    let present :=
      match found with
      | Some _ => true
      | None => false
      end in
    let '(tail, trace) := rw_shared_children_ready rest ready in
    let '(answer, bool_trace) := if present then (tail, [AuditCase 724 []])
      else (false, [AuditCase 724 []; AuditConstruct 745 []]) in
    (answer, [AuditCase 722 []; AuditCall (RWSharedReadyRead child ready found);
      AuditCase 723 []] ++
      trace ++ bool_trace)
  end.

Fixpoint rw_shared_validation_pass {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive * audit_trace (rw_shared_validation_call K Sort V) :=
  match entries with
  | nil => (ready, [AuditCase 725 []])
  | (_, (id, node)) :: rest =>
    let '(is_ready, child_trace) :=
      match node with
      | RWSharedVar _ _ _ _ _ => (true, [AuditCase 726 []; AuditConstruct 727 []])
      | RWSharedApp _ _ _ _ _ children =>
        let '(out, trace) := rw_shared_children_ready children ready in
        (out, AuditCase 746 [] :: trace)
      end in
    if is_ready then
      let updated := Trie.set id (id, tt) ready in
      let '(out, tail_trace) := rw_shared_validation_pass rest updated in
      (out, [AuditCase 728 []] ++ child_trace ++ [AuditCase 729 [];
        AuditCall (RWSharedReadyAdd id ready updated)] ++ tail_trace)
    else
      let '(out, tail_trace) := rw_shared_validation_pass rest ready in
      (out, [AuditCase 728 []] ++ child_trace ++ [AuditCase 730 []] ++ tail_trace)
  end.

Fixpoint rw_shared_validation_rounds {K Sort V} (fuel : nat)
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive * audit_trace (rw_shared_validation_call K Sort V) :=
  match fuel with
  | 0 => (ready, [AuditCase 731 []])
  | S rest =>
    let '(next, pass_trace) := rw_shared_validation_pass entries ready in
    let '(out, tail_trace) := rw_shared_validation_rounds rest entries next in
    (out, [AuditCase 732 []] ++ pass_trace ++ tail_trace)
  end.

Fixpoint rw_shared_validation_keys {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  match entries with
  | nil => (true, [AuditCase 733 []; AuditConstruct 734 []])
  | (position, (id, _)) :: rest =>
    let same := Pos.eqb position id in
    let '(tail, trace) := rw_shared_validation_keys rest in
    let '(answer, bool_trace) := if same then (tail, [AuditCase 736 []])
      else (false, [AuditCase 736 []; AuditConstruct 747 []]) in
    (answer, [AuditCase 735 []; AuditCall (RWSharedKeyCheck position id same)] ++ trace ++
      bool_trace)
  end.

Fixpoint rw_shared_validation_all_ready {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  match entries with
  | nil => (true, [AuditCase 737 []; AuditConstruct 738 []])
  | (_, (id, _)) :: rest =>
    let found := Map.code_get id ready in
    let present :=
      match found with
      | Some _ => true
      | None => false
      end in
    let '(tail, trace) := rw_shared_validation_all_ready rest ready in
    let '(answer, bool_trace) := if present then (tail, [AuditCase 741 []])
      else (false, [AuditCase 741 []; AuditConstruct 748 []]) in
    (answer, [AuditCase 739 []; AuditCall (RWSharedReadyRead id ready found); AuditCase 740 []] ++
      trace ++ bool_trace)
  end.

Definition rw_shared_validate_atomic {K Sort V} (dag : rw_shared_tree K Sort V) : bool * audit_trace
    (rw_shared_validation_call K Sort V) :=
  let nodes := rw_shared_nodes K Sort V dag in
  let '(entries, enum_trace) := audit_trie_elements nodes in
  let root := rw_shared_root K Sort V dag in
  let root_found := Map.code_get root nodes in
  let root_ok :=
    match root_found with
    | Some _ => true
    | None => false
    end in
  let '(keys_ok, key_trace) := rw_shared_validation_keys entries in
  let '(count, length_trace) := rw_shared_length_atomic entries in
  let '(ready, round_trace) := rw_shared_validation_rounds count entries FinSet.empty in
  let '(all_ok, all_trace) := rw_shared_validation_all_ready entries ready in
  let '(both, first_bool_trace) := if root_ok then (keys_ok, [AuditCase 743 []])
    else (false, [AuditCase 743 []; AuditConstruct 749 []]) in
  let '(answer, second_bool_trace) := if both then (all_ok, [AuditCase 744 []])
    else (false, [AuditCase 744 []; AuditConstruct 750 []]) in
  (answer,
    [AuditCall (RWSharedEnumerate nodes entries enum_trace);
      AuditCall (RWSharedRootRead root nodes root_found);
      AuditCase 742 []] ++ key_trace ++ [AuditCall (RWSharedLength count length_trace)] ++
      round_trace ++ all_trace ++ first_bool_trace ++ second_bool_trace).

Fixpoint rw_shared_children_ready_value (children : list positive) (ready : FinSet.t positive) :
    bool :=
  match children with
  | nil => true
  | child :: rest =>
    let present :=
      match Map.code_get child ready with
      | Some _ => true
      | None => false
      end in
    present && rw_shared_children_ready_value rest ready
  end.

Fixpoint rw_shared_validation_pass_value {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive :=
  match entries with
  | nil => ready
  | (_, (id, node)) :: rest =>
    let is_ready :=
      match node with
      | RWSharedVar _ _ _ _ _ => true
      | RWSharedApp _ _ _ _ _ children => rw_shared_children_ready_value children ready
      end in
    rw_shared_validation_pass_value rest (if is_ready then Trie.set id (id, tt) ready else ready)
  end.

Fixpoint rw_shared_validation_rounds_value {K Sort V} (fuel : nat)
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive :=
  match fuel with
  | 0 => ready
  | S rest =>
    rw_shared_validation_rounds_value rest entries (rw_shared_validation_pass_value entries ready)
  end.

Fixpoint rw_shared_validation_keys_value {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) : bool :=
  match entries with
  | nil => true
  | (position, (id, _)) :: rest =>
    Pos.eqb position id && rw_shared_validation_keys_value rest
  end.

Fixpoint rw_shared_validation_all_ready_value {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    bool :=
  match entries with
  | nil => true
  | (_, (id, _)) :: rest =>
    let present :=
      match Map.code_get id ready with
      | Some _ => true
      | None => false
      end in
    present && rw_shared_validation_all_ready_value rest ready
  end.

Definition rw_shared_validate {K Sort V} (dag : rw_shared_tree K Sort V) : bool :=
  let nodes := rw_shared_nodes K Sort V dag in
  let entries := Trie.elements nodes in
  let root_ok :=
    match Map.code_get (rw_shared_root K Sort V dag) nodes with
    | Some _ => true
    | None => false
    end in
  let keys_ok := rw_shared_validation_keys_value entries in
  let ready := rw_shared_validation_rounds_value (length entries) entries FinSet.empty in
  let all_ok := rw_shared_validation_all_ready_value entries ready in
  root_ok && keys_ok && all_ok.

Fixpoint rw_shared_children_bits (children : list positive) : nat :=
  match children with
  | nil => 0
  | id :: rest => S (Pos.size_nat id) + rw_shared_children_bits rest
  end.

(** Shared validation succeeds exactly for well-formed shared trees. *)
Definition rw_shared_validate_spec_contract : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V),
    rw_shared_validate dag = true <-> rw_shared_wf dag.

(** Erasing validation receipts yields the plain shared validator result. *)
Definition rw_shared_validate_atomic_erases_contract : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V), fst (rw_shared_validate_atomic dag) =
    rw_shared_validate dag.

Inductive rw_shared_unfold_call (K Sort V : Type) : Type :=
  | RWUnfoldValidate : bool -> audit_trace (rw_shared_validation_call K Sort V) ->
      rw_shared_unfold_call K Sort V
  | RWUnfoldEnumerate : Trie.t (positive * rw_shared_node K Sort V) ->
      list (positive * (positive * rw_shared_node K Sort V)) ->
      list (audit_elements_event (positive * rw_shared_node K Sort V)) ->
      rw_shared_unfold_call K Sort V
  | RWUnfoldLength : nat -> audit_trace unit -> rw_shared_unfold_call K Sort V
  | RWUnfoldRead : positive -> Trie.t (positive * rw_shared_node K Sort V) -> option (rw_shared_node
      K Sort V) -> rw_shared_unfold_call K Sort V.
Arguments RWUnfoldValidate {K Sort V}.
Arguments RWUnfoldEnumerate {K Sort V}.
Arguments RWUnfoldLength {K Sort V}.
Arguments RWUnfoldRead {K Sort V}.

Definition rw_shared_unfold_event_cost {K Sort V}
    (event : audit_event (rw_shared_unfold_call K Sort V)) : nat :=
  match event with
  | AuditCall (RWUnfoldValidate _ trace) => 1 + rw_shared_validation_trace_cost trace
  | AuditCall (RWUnfoldEnumerate _ _ trace) => 1 + audit_elements_work trace
  | AuditCall (RWUnfoldLength _ trace) => 1 + audit_work trace
  | AuditCall (RWUnfoldRead id nodes _) => 2 + audit_trie_get_source_work id nodes
  | _ => 1
  end.

Definition rw_shared_unfold_trace_cost {K Sort V}
    (trace : audit_trace (rw_shared_unfold_call K Sort V)) : nat :=
  fold_right (fun event total => rw_shared_unfold_event_cost event + total) 0 trace.

Fixpoint rw_shared_unfold_fuel_atomic {K Sort V} (fuel : nat) (dag : rw_shared_tree K Sort V)
    (id : positive) : option (rw_term K Sort V) * audit_trace (rw_shared_unfold_call K Sort V) :=
  match fuel with
  | 0 => (None, [AuditCase 760 []; AuditConstruct 761 []])
  | S rest =>
    let nodes := rw_shared_nodes K Sort V dag in
    let found := Map.code_get id nodes in
    match found with
    | None => (None, [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes None);
        AuditCase 763 []; AuditConstruct 764 []])
    | Some (RWSharedVar _ _ _ sort value) =>
      (Some (RWVar sort value), [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes found);
        AuditCase 765 []; AuditConstruct 766 []; AuditConstruct 767 []])
    | Some (RWSharedApp _ _ _ sort op children) =>
      let fix visit (ids : list positive) :
          option (list (rw_term K Sort V)) * audit_trace (rw_shared_unfold_call K Sort V) :=
        match ids with
        | nil => (Some nil, [AuditCase 768 []; AuditConstruct 769 []; AuditConstruct 770 []])
        | child :: tail =>
          let '(head, ht) := rw_shared_unfold_fuel_atomic rest dag child in
          match head with
          | None => (None, [AuditCase 771 []] ++ ht ++ [AuditCase 772 []; AuditConstruct 773 []])
          | Some head_tree =>
            let '(others, ot) := visit tail in
            match others with
            | None => (None, [AuditCase 771 []] ++ ht ++ [AuditCase 774 []] ++ ot ++
                [AuditCase 775 []; AuditConstruct 776 []])
            | Some tail_trees =>
              (Some (head_tree :: tail_trees),
                [AuditCase 771 []] ++ ht ++ [AuditCase 774 []] ++ ot ++
                  [AuditCase 777 []; AuditConstruct 778 []; AuditConstruct 779 []])
            end
          end
        end in
      let '(out, trace) := visit children in
      match out with
      | None =>
        (None, [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes found); AuditCase 780 []] ++
          trace ++ [AuditCase 781 []; AuditConstruct 782 []])
      | Some trees => (Some (RWApp sort op trees),
          [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes found); AuditCase 780 []] ++ trace ++
          [AuditCase 783 []; AuditConstruct 784 []; AuditConstruct 785 []])
      end
    end
  end.

Definition rw_shared_unfold_atomic {K Sort V} (dag : rw_shared_tree K Sort V) :
    option (rw_term K Sort V) * audit_trace (rw_shared_unfold_call K Sort V) :=
  let '(valid, valid_trace) := rw_shared_validate_atomic dag in
  if valid then
    let nodes := rw_shared_nodes K Sort V dag in
    let '(entries, enum_trace) := audit_trie_elements nodes in
    let '(count, length_trace) := rw_shared_length_atomic entries in
    let '(out, trace) := rw_shared_unfold_fuel_atomic (S count) dag (rw_shared_root K Sort V dag) in
    (out, [AuditCall (RWUnfoldValidate valid valid_trace); AuditCase 786 [];
      AuditCall (RWUnfoldEnumerate nodes entries enum_trace); AuditCall (RWUnfoldLength count
        length_trace);
      AuditConstruct 787 []] ++ trace)
  else
    (None, [AuditCall (RWUnfoldValidate valid valid_trace); AuditCase 788 [];
      AuditConstruct 789 []]).

Fixpoint rw_shared_unfold_fuel_value {K Sort V} (fuel : nat) (dag : rw_shared_tree K Sort V)
    (id : positive) : option (rw_term K Sort V) :=
  match fuel with
  | 0 => None
  | S rest =>
    match Map.code_get id (rw_shared_nodes K Sort V dag) with
    | None => None
    | Some (RWSharedVar _ _ _ sort value) => Some (RWVar sort value)
    | Some (RWSharedApp _ _ _ sort op children) =>
      let fix visit (ids : list positive) : option (list (rw_term K Sort V)) :=
        match ids with
        | nil => Some nil
        | child :: tail =>
          match rw_shared_unfold_fuel_value rest dag child with
          | None => None
          | Some head =>
            match visit tail with
            | None => None
            | Some tails => Some (head :: tails)
            end
          end
        end in
      match visit children with
      | None => None
      | Some trees => Some (RWApp sort op trees)
      end
    end
  end.

Definition rw_shared_unfold {K Sort V} (dag : rw_shared_tree K Sort V) :
    option (rw_term K Sort V) :=
  if rw_shared_validate dag then
    let nodes := rw_shared_nodes K Sort V dag in
    let count := length (Trie.elements nodes) in
    rw_shared_unfold_fuel_value (S count) dag (rw_shared_root K Sort V dag)
  else None.

(** Every well-formed shared tree has a successful unfolding. *)
Definition rw_shared_unfold_total_statement : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V),
    rw_shared_wf dag ->
    exists tree, rw_shared_unfold dag = Some tree.

(** A successful shared unfolding implies that the shared tree is well formed. *)
Definition rw_shared_unfold_valid_statement : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V) tree,
    rw_shared_unfold dag = Some tree ->
    rw_shared_wf dag.

(** Erasing unfolding receipts yields the plain shared unfolding result. *)
Definition rw_shared_unfold_erases_statement : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V), fst (rw_shared_unfold_atomic dag) =
    rw_shared_unfold dag.

(** Every well-formed shared tree has a successful unfolding. *)
Definition rw_shared_unfold_total_contract : Prop :=
  rw_shared_unfold_total_statement.

(** A successful shared unfolding implies that the shared tree is well formed. *)
Definition rw_shared_unfold_valid_contract : Prop :=
  rw_shared_unfold_valid_statement.

(** Erasing unfolding receipts yields the plain shared unfolding result. *)
Definition rw_shared_unfold_atomic_erases_contract : Prop :=
  rw_shared_unfold_erases_statement.
