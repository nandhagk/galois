(** * Counted primitive trie frames

    These candidate clauses expose the source's accessor, node and map projection cases.
    For example, an empty root and a present leaf take distinct accessor branches.
    Builds on: CollectionsTrie, CollectionsMap and the audit trie model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap
  CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

(** * Accessor cases *)

Definition audit_trie_left_source {A} (input : Trie.t A) : Trie.t A * nat :=
  let result := match input with
    | Trie.Nodes (Trie.N100 l) | Trie.Nodes (Trie.N101 l _) |
      Trie.Nodes (Trie.N110 l _) | Trie.Nodes (Trie.N111 l _ _) => Trie.Nodes l
    | _ => Trie.Empty
    end in
  (result, audit_trie_accessor_work input).

Definition audit_trie_right_source {A} (input : Trie.t A) : Trie.t A * nat :=
  let result := match input with
    | Trie.Nodes (Trie.N001 r) | Trie.Nodes (Trie.N011 _ r) |
      Trie.Nodes (Trie.N101 _ r) | Trie.Nodes (Trie.N111 _ _ r) => Trie.Nodes r
    | _ => Trie.Empty
    end in
  (result, audit_trie_accessor_work input).

Definition audit_trie_value_source {A} (input : Trie.t A) : option A * nat :=
  let result := match input with
    | Trie.Nodes (Trie.N010 v) | Trie.Nodes (Trie.N011 v _) |
      Trie.Nodes (Trie.N110 _ v) | Trie.Nodes (Trie.N111 _ v _) => Some v
    | _ => None
    end in
  (result, audit_trie_accessor_work input).

(** Each named claim equates both the original output and the fixed actual branch charge. *)
Definition audit_trie_left_source_adequate_statement : Prop :=
  forall A (input : Trie.t A), audit_trie_left_source input =
    (Trie.left input, audit_trie_accessor_work input).

(** The trie right source relation agrees with the corresponding trie accessor. *)
Definition audit_trie_right_source_adequate_statement : Prop :=
  forall A (input : Trie.t A), audit_trie_right_source input =
    (Trie.right input, audit_trie_accessor_work input).

(** The trie value source relation agrees with the corresponding trie accessor. *)
Definition audit_trie_value_source_adequate_statement : Prop :=
  forall A (input : Trie.t A), audit_trie_value_source input =
    (Trie.value input, audit_trie_accessor_work input).

(** * Smart-constructor cases *)

(** Every combination of absent and present inputs selects its original exact constructor. *)
Definition audit_trie_node_source {A} (left : Trie.t A) (value : option A) (right : Trie.t A)
    : Trie.t A * nat :=
  let result := match left, value, right with
    | Trie.Empty, None, Trie.Empty => Trie.Empty
    | Trie.Empty, None, Trie.Nodes r => Trie.Nodes (Trie.N001 r)
    | Trie.Empty, Some v, Trie.Empty => Trie.Nodes (Trie.N010 v)
    | Trie.Empty, Some v, Trie.Nodes r => Trie.Nodes (Trie.N011 v r)
    | Trie.Nodes l, None, Trie.Empty => Trie.Nodes (Trie.N100 l)
    | Trie.Nodes l, None, Trie.Nodes r => Trie.Nodes (Trie.N101 l r)
    | Trie.Nodes l, Some v, Trie.Empty => Trie.Nodes (Trie.N110 l v)
    | Trie.Nodes l, Some v, Trie.Nodes r => Trie.Nodes (Trie.N111 l v r)
    end in
  (result, audit_trie_node_work left value right).

(** The trie node source agrees with node construction and its recorded work. *)
Definition audit_trie_node_source_adequate_statement : Prop :=
  forall A (left : Trie.t A) value right,
    audit_trie_node_source left value right =
      (Trie.node left value right, audit_trie_node_work left value right).

(** * Position-map projection *)

Inductive audit_map_code_get_run {K V} : positive -> Map.t K V -> option V ->
    audit_trace (audit_trie_call (K * V)) -> nat -> Prop :=
  | AuditMapCodeGet : forall key input found events work,
      audit_trie_get_run key input found events work ->
      audit_map_code_get_run key input (option_map snd found) events
        (work + match found with
        | None => 2
        | Some _ => 4
        end).

(** Every map code get input has a corresponding source run. *)
Definition audit_map_code_get_run_total_statement : Prop :=
  forall K V key (input : Map.t K V),
    exists output events work, audit_map_code_get_run key input output events work.

(** A map code get source run agrees with the counted result and its work bounds. *)
Definition audit_map_code_get_run_correct_statement : Prop :=
  forall K V key (input : Map.t K V) output events work,
    audit_map_code_get_run key input output events work ->
    output = Map.code_get key input /\ (output, events) = audit_map_code_get key input /\
    work <= 5 * Pos.size_nat key + 4.

(** The branch-level accounting must be independently related to the literal source evaluation. *)
Definition audit_trie_access_source_clauses_statement : Prop :=
  audit_trie_left_source_adequate_statement /\ audit_trie_right_source_adequate_statement /\
  audit_trie_value_source_adequate_statement /\ audit_trie_node_source_adequate_statement.

(** * Positive equality source cases *)

Inductive audit_positive_eqb_event : Type :=
  | AuditPositiveEqb (left right : positive) (result : bool).

(** The actual [Pos.eqb] descends only while both current constructors match. *)
Fixpoint audit_positive_eqb (left right : positive) {struct right}
    : bool * list audit_positive_eqb_event :=
  match left, right with
  | xI l, xI r =>
      let '(result, events) := audit_positive_eqb l r in
      (result, AuditPositiveEqb left right result :: events)
  | xO l, xO r =>
      let '(result, events) := audit_positive_eqb l r in
      (result, AuditPositiveEqb left right result :: events)
  | xH, xH => (true, [AuditPositiveEqb left right true])
  | _, _ => (false, [AuditPositiveEqb left right false])
  end.

Definition audit_positive_eqb_source_work (events : list audit_positive_eqb_event) : nat :=
  2 * length events.

(** Discarding equality-test events recovers [Pos.eqb]. *)
Definition audit_positive_eqb_erases_statement : Prop :=
  forall left right, fst (audit_positive_eqb left right) = Pos.eqb left right.

(** Positive equality work is bounded by twice the smaller operand width. *)
Definition audit_positive_eqb_source_bound_statement : Prop :=
  forall left right,
    audit_positive_eqb_source_work (snd (audit_positive_eqb left right)) <=
      2 * Nat.min (Pos.size_nat left) (Pos.size_nat right).
