(** * Strict partial-checker source model

    This proposal retains the actual explored-set and indexed contributor traversals.
    For example, a failed early constraint does not skip later strict boolean arguments.
    Builds on: FixpointPartial and the counted index, set, trie and query models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointPartial.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet
  CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

(** Typed observations retain the actual callbacks and each concrete library subrun. *)

Inductive fx_partial_event (X C A : Type) : Type :=
  | FxPartialQuery (events : audit_trace (fx_declared_call X C A))
  | FxPartialRhs (constraint : C) (result : Query.t X A)
  | FxPartialTarget (constraint : C) (result : X)
  | FxPartialLeb (left right : A) (result : bool)
  | FxPartialMem (key : X) (set : FinSet.t X) (result : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxPartialIndexGet (key : X) (code : positive) (before : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxPartialElements (set : FinSet.t X) (values : list X)
      (body : list (audit_set_elements_event X))
  | FxPartialNot (input result : bool)
  | FxPartialAnd (left right result : bool)
  | FxPartialOr (left right result : bool)
  | FxPartialCase (site : nat).

Arguments FxPartialQuery {X C A} _.

Arguments FxPartialRhs {X C A} _ _.

Arguments FxPartialTarget {X C A} _ _.

Arguments FxPartialLeb {X C A} _ _ _.

Arguments FxPartialMem {X C A} _ _ _ _.

Arguments FxPartialIndexGet {X C A} _ _ _ _ _.

Arguments FxPartialElements {X C A} _ _ _.

Arguments FxPartialNot {X C A} _ _.

Arguments FxPartialAnd {X C A} _ _ _.

Arguments FxPartialOr {X C A} _ _ _.

Arguments FxPartialCase {X C A} _.

Section PartialModel.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (S : System.t X C A) (SS : System.static S) (ix : sys_index X C).
Context (explored : FinSet.t X) (m : assignment X A).

(** Every recorded read is checked even if an earlier read failed. *)

Fixpoint fx_partial_reads (reads : list X) : bool * list (fx_partial_event X C A) :=
  match reads with
  | [] => (true, [FxPartialCase 0])
  | x :: rest =>
      let '(head, body) := audit_finset_mem (fx_index_encoder EX) x explored in
      let '(tail, events) := fx_partial_reads rest in
      (andb head tail, FxPartialCase 0 :: FxPartialMem x explored head body :: events ++
        [FxPartialAnd head tail (andb head tail)])
  end.

(** Strict orb checks the actual membership and lattice comparison for every side. *)

Fixpoint fx_partial_sides (sides : list (X * A)) : bool * list (fx_partial_event X C A) :=
  match sides with
  | [] => (true, [FxPartialCase 1])
  | (x, value) :: rest =>
      let '(member, body) := audit_finset_mem (fx_index_encoder EX) x explored in
      let negated := negb member in
      let '(old, read_events) := @fx_model_lookup X C A EX L m x in
      let within := leb L value old in
      let guard := orb negated within in
      let '(tail, events) := fx_partial_sides rest in
      (andb guard tail,
       FxPartialCase 1 :: FxPartialMem x explored member body :: FxPartialNot member negated ::
       FxPartialQuery read_events :: FxPartialLeb value old within ::
       FxPartialOr negated within guard :: events ++ [FxPartialAnd guard tail (andb guard tail)])
  end.

(** One contributor executes its RHS once, target callback twice, and both strict sides. *)

Definition fx_partial_constraint (c : C) : bool * list (fx_partial_event X C A) :=
  let rhs := System.rhs S c in
  let '(result, query_events) := @fx_model_query X C A EX L rhs m in
  let '(value, reads, sides) := result in
  let '(reads_ok, reads_events) := fx_partial_reads reads in
  let target1 := System.target S c in
  let '(member, member_events) := audit_finset_mem (fx_index_encoder EX) target1 explored in
  let negated := negb member in
  let target2 := System.target S c in
  let '(old, lookup_events) := @fx_model_lookup X C A EX L m target2 in
  let within := leb L value old in
  let guard := orb negated within in
  let first := andb reads_ok guard in
  let '(sides_ok, sides_events) := fx_partial_sides sides in
  (andb first sides_ok,
   [FxPartialRhs c rhs; FxPartialQuery query_events] ++ reads_events ++
   [FxPartialTarget c target1; FxPartialMem target1 explored member member_events;
    FxPartialNot member negated; FxPartialTarget c target2; FxPartialQuery lookup_events;
    FxPartialLeb value old within; FxPartialOr negated within guard;
    FxPartialAnd reads_ok guard first] ++ sides_events ++
   [FxPartialAnd first sides_ok (andb first sides_ok); FxPartialCase 2]).

(** The inner forallb visits every contributor occurrence, including duplicates. *)

Fixpoint fx_partial_contributors (cs : list C) : bool * list (fx_partial_event X C A) :=
  match cs with
  | [] => (true, [FxPartialCase 3])
  | c :: rest =>
      let '(head, first) := fx_partial_constraint c in
      let '(tail, later) := fx_partial_contributors rest in
      (andb head tail, FxPartialCase 3 :: first ++ later ++
        [FxPartialAnd head tail (andb head tail)])
  end.

(** An indexed lookup retains its actual encoding, trie input and result. *)

Fixpoint fx_partial_unknowns (xs : list X) : bool * list (fx_partial_event X C A) :=
  match xs with
  | [] => (true, [FxPartialCase 4])
  | x :: rest =>
      let code := encode EX x in
      let '(raw, get_events) := audit_map_code_get code (contributors ix) in
      let cs :=
        match raw with
        | Some values => values
        | None => []
        end in
      let '(head, first) := fx_partial_contributors cs in
      let '(tail, later) := fx_partial_unknowns rest in
      (andb head tail, FxPartialCase 4 ::
       FxPartialIndexGet x code (contributors ix) raw get_events :: first ++ later ++
       [FxPartialAnd head tail (andb head tail)])
  end.

(** The whole partial checker enumerates exactly the current explored set. *)

Definition check_partial_counted : bool * list (fx_partial_event X C A) :=
  let '(xs, elements_events) := audit_finset_elements explored in
  let '(result, events) := fx_partial_unknowns xs in
  (result, FxPartialElements explored xs elements_events :: events).

(** Every helper and the whole check erase to their original strict computations. *)

(** Erasing the counted read, side, constraint and partial-check traces recovers their original
    checks. *)
Definition fx_partial_model_erasure_statement : Prop :=
  (forall reads, fst (fx_partial_reads reads) = forallb (fun x => FinSet.mem EX x explored) reads)
    /\
  (forall sides, fst (fx_partial_sides sides) =
    forallb (fun ya => negb (FinSet.mem EX (fst ya) explored) ||
      leb L (snd ya) (lookup EX L m (fst ya))) sides) /\
  (forall c, fst (fx_partial_constraint c) = partial_constraint_check EX L S explored (lookup EX L
    m) c) /\
  fst check_partial_counted = check_partial EX L S SS ix explored m.

(** Each typed event has a fixed selected source-frame charge. *)

Definition fx_partial_event_work (event : fx_partial_event X C A) : nat :=
  match event with
  | FxPartialQuery events => fx_declared_model_work EC events
  | FxPartialMem _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxPartialIndexGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FxPartialElements _ _ body => 1 + audit_set_elements_work body
  | _ => 1
  end.

(** The bound uses actual keys, trie states and query events, not a supplied work price. *)

Definition fx_partial_event_budget (event : fx_partial_event X C A) : nat :=
  match event with
  | FxPartialQuery events => audit_work events + fx_declared_primitive_budget EC events
  | FxPartialMem x _ _ _ => 12 + 5 * Pos.size_nat (encode EX x)
  | FxPartialIndexGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FxPartialElements set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | _ => 1
  end.

Definition fx_partial_work (events : list (fx_partial_event X C A)) : nat :=
  fold_right (fun event n => fx_partial_event_work event + n) 0 events.

Definition fx_partial_budget (events : list (fx_partial_event X C A)) : nat :=
  fold_right (fun event n => fx_partial_event_budget event + n) 0 events.

(** The original result and the operand-derived bound refer to the same counted execution. *)

(** Counted partial checking returns the original result and its work fits the trace-derived
    budget. *)
Definition fx_partial_model_cost_statement : Prop :=
  let '(result, events) := check_partial_counted in
  result = check_partial EX L S SS ix explored m /\ fx_partial_work events <= fx_partial_budget
    events.

End PartialModel.

(** The following bounds use only source inputs and the original intermediate query results.
    They are mathematical observations, not executions included in the source-work claim. *)

Fixpoint fx_partial_reads_input_budget {X} (EX : encoding X) (reads : list X) : nat :=
  match reads with
  | [] => 1
  | x :: rest => 2 + (12 + 5 * Pos.size_nat (encode EX x)) + fx_partial_reads_input_budget EX rest
  end.

Fixpoint fx_partial_sides_input_budget {X A} (EX : encoding X) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 1
  | (x, _) :: rest => 5 + (12 + 5 * Pos.size_nat (encode EX x)) +
      fx_fullcheck_lookup_input_budget EX x + fx_partial_sides_input_budget EX rest
  end.

Definition fx_partial_constraint_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (c : C) : nat :=
  let rhs := System.rhs S c in
  let '(_, reads, sides) := Query.run rhs (lookup EX L m) in
  let target := System.target S c in
  9 + fx_fullcheck_query_input_budget EX L m rhs + fx_partial_reads_input_budget EX reads +
    (12 + 5 * Pos.size_nat (encode EX target)) + fx_fullcheck_lookup_input_budget EX target +
    fx_partial_sides_input_budget EX sides.

Fixpoint fx_partial_contributors_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 2 + fx_partial_constraint_input_budget EX L S m c +
      fx_partial_contributors_input_budget EX L S m rest
  end.

Fixpoint fx_partial_unknowns_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (m : assignment X A) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 2 + (2 + 6 * Pos.size_nat (encode EX x)) +
      fx_partial_contributors_input_budget EX L S m (contributors_of EX ix x) +
      fx_partial_unknowns_input_budget EX L S ix m rest
  end.

Definition fx_partial_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (explored : FinSet.t X) (m : assignment X A) : nat :=
  7 + 19 * audit_trie_nodes explored + audit_trie_output_bits explored +
    fx_partial_unknowns_input_budget EX L S ix m (FinSet.elements explored).

(** Counted partial checking returns the original result and its work fits the input-derived
    budget. *)
Definition fx_partial_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix explored m,
    let '(result, events) := check_partial_counted EX L S ix explored m in
    result = check_partial EX L S SS ix explored m /\
    fx_partial_work EC events <= fx_partial_input_budget EX L S ix explored m.
