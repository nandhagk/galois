(** * Partial checker with explicit callback-body subruns

    Every explored-set visit, contributor, query and strict boolean side is retained.
    Higher-order query continuations use the fixed relation from the full checker.
    For example, an explored-set visit records its nested membership check.
    Builds on: FixpointPartial and shared collection/full-check models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointPartial.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditFullCheck.
Import List.ListNotations.

Inductive fx_partial_nested_event (X C A B : Type) : Type :=
  | FpnCheck (body : list (fx_check_nested_event X C A B))
  | FpnMem (x : X) (set : FinSet.t X) (answer : bool) (body : list (audit_set_event X B))
  | FpnIndex (x : X) (input : Map.t X (list C)) (raw : option (list C))
      (body : list (audit_map_event X (list C) B))
  | FpnElements (set : FinSet.t X) (items : list X) (body : list (audit_set_elements_event X))
  | FpnCase (site : nat).

Arguments FpnCheck {X C A B} _.

Arguments FpnMem {X C A B} _ _ _ _.

Arguments FpnIndex {X C A B} _ _ _ _.

Arguments FpnElements {X C A B} _ _ _.

Arguments FpnCase {X C A B} _.

Section PartialAdapter.
Context {X C A B : Type} (L : lattice A) (S : System.t X C A)
  (ix : sys_index X C) (explored : FinSet.t X) (m : assignment X A)
  (cb : fx_check_external_model X C A B).

Fixpoint fpn_reads (xs : list X) : bool * list (fx_partial_nested_event X C A B) :=
  match xs with
  | [] => (true, [FpnCase 0])
  | x :: rest =>
      let '(head, body) := audit_finset_mem (fx_check_encode_model cb) x explored in
      let '(tail, events) := fpn_reads rest in
      (andb head tail, FpnCase 0 :: FpnMem x explored head body :: events ++ [FpnCase 1])
  end.

Fixpoint fpn_sides (xs : list (X * A)) : bool * list (fx_partial_nested_event X C A B) :=
  match xs with
  | [] => (true, [FpnCase 2])
  | (x, value) :: rest =>
      let '(member, mem_body) := audit_finset_mem (fx_check_encode_model cb) x explored in
      let '(old, lookup_events) := fcn_lookup L m cb x in
      let '(le, leb_body) := fx_check_leb_model cb value old in
      let guard := orb (negb member) le in
      let '(tail, events) := fpn_sides rest in
      (andb guard tail, FpnCase 2 :: FpnMem x explored member mem_body :: FpnCase 3 ::
        FpnCheck lookup_events :: FpnCheck [FcnLeb value old le leb_body] :: FpnCase 4 ::
        events ++ [FpnCase 5])
  end.

(** A constraint derivation records its query, explored-set checks and comparisons in order. *)
Inductive fpn_constraint_run : C -> bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnConstraint : forall c rhs rhs_body value reads sides query_events reads_ok reads_events
      target1 target_body1 member mem_body target2 target_body2 old lookup_events le leb_body
      side_ok side_events,
      fx_check_rhs_model cb c = (rhs, rhs_body) ->
      fcn_query_run L m cb rhs (value, reads, sides) query_events ->
      fpn_reads reads = (reads_ok, reads_events) ->
      fx_check_target_model cb c = (target1, target_body1) ->
      audit_finset_mem (fx_check_encode_model cb) target1 explored = (member, mem_body) ->
      fx_check_target_model cb c = (target2, target_body2) ->
      fcn_lookup L m cb target2 = (old, lookup_events) ->
      fx_check_leb_model cb value old = (le, leb_body) ->
      fpn_sides sides = (side_ok, side_events) ->
      fpn_constraint_run c (andb (andb reads_ok (orb (negb member) le)) side_ok)
        ([FpnCheck [FcnRhs c rhs rhs_body]; FpnCheck query_events] ++ reads_events ++
         [FpnCheck [FcnTarget c target1 target_body1]; FpnMem target1 explored member mem_body;
          FpnCase 6; FpnCheck [FcnTarget c target2 target_body2]; FpnCheck lookup_events;
          FpnCheck [FcnLeb value old le leb_body]; FpnCase 7; FpnCase 8] ++ side_events ++
  [FpnCase 9]).

(** A constraint-list derivation combines each result strictly and concatenates its event trace. *)
Inductive fpn_constraints_run : list C -> bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnConstraintsNil : fpn_constraints_run [] true [FpnCase 10]
  | FpnConstraintsCons : forall c rest head first tail later,
      fpn_constraint_run c head first -> fpn_constraints_run rest tail later ->
      fpn_constraints_run (c :: rest) (andb head tail)
        (FpnCase 10 :: first ++ later ++ [FpnCase 11]).

(** An unknown-list derivation checks each unknown's indexed contributors and retains the events. *)
Inductive fpn_unknowns_run : list X -> bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnUnknownsNil : fpn_unknowns_run [] true [FpnCase 12]
  | FpnUnknownsCons : forall x rest raw map_body cs head first tail later,
      audit_map_get (fx_check_encode_model cb) x (contributors ix) = (raw, map_body) ->
      cs = (
        match raw with
        | Some found => found
        | None => []
        end) ->
      fpn_constraints_run cs head first -> fpn_unknowns_run rest tail later ->
      fpn_unknowns_run (x :: rest) (andb head tail)
        (FpnCase 12 :: FpnIndex x (contributors ix) raw map_body :: first ++ later ++ [FpnCase 13]).

(** A partial-check derivation enumerates the explored set and checks its indexed contributors. *)
Inductive fx_partial_nested_run : bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnRun : forall xs elements_body out events,
      audit_finset_elements explored = (xs, elements_body) ->
      fpn_unknowns_run xs out events ->
      fx_partial_nested_run out (FpnElements explored xs elements_body :: events).

End PartialAdapter.

(** When callbacks erase correctly, every nested partial-check run returns the original result. *)
Definition fx_partial_nested_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> forall out events,
    fx_partial_nested_run L ix explored m cb out events ->
    out = check_partial EX L S SS ix explored m.

(** When callbacks erase correctly, the nested partial-check relation has a run for each input. *)
Definition fx_partial_nested_total_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> exists out events, fx_partial_nested_run L ix explored
  m cb out events.

Definition fpn_event_work {X C A B} (budget : fx_check_external_budget X C A B)
    (event : fx_partial_nested_event X C A B) : nat :=
  match event with
  | FpnCheck body => fx_check_nested_work budget body
  | FpnMem _ _ _ body => 3 + audit_finset_source_work (fx_check_body_work budget) body
  | FpnIndex _ _ _ body => 3 + audit_map_source_work (fx_check_body_work budget) body
  | FpnElements _ _ body => 3 + audit_set_elements_work body
  | FpnCase _ => 3
  end.

Definition fx_partial_nested_work {X C A B} (budget : fx_check_external_budget X C A B)
    (events : list (fx_partial_nested_event X C A B)) : nat :=
  fold_right (fun e n => fpn_event_work budget e + n) 0 events.

Definition fpn_mem_budget {X C A B} (EX : encoding X) (budget : fx_check_external_budget X C A B)
    (x : X) : nat := 9 + fx_check_encode_bound budget x + 5 * Pos.size_nat (encode EX x).

Fixpoint fpn_reads_budget {X C A B} (EX : encoding X) (budget : fx_check_external_budget X C A B)
    (reads : list X) : nat :=
  match reads with
  | [] => 3
  | x :: rest => 6 + fpn_mem_budget EX budget x + fpn_reads_budget EX
      budget rest
  end.

Fixpoint fpn_sides_budget {X C A B} (EX : encoding X) (L : lattice A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 3
  | (x, value) :: rest => 15 + fpn_mem_budget EX budget x + fx_check_nested_lookup_budget EX
    budget x +
      fx_check_leb_bound budget value (lookup EX L m x) + fpn_sides_budget EX L budget m rest
  end.

Definition fpn_constraint_budget {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (c : C) : nat :=
  let rhs := System.rhs S c in let '(value, reads, sides) := Query.run rhs (lookup EX L m) in
  let target := System.target S c in
  24 + fx_check_rhs_bound budget c + 2 * fx_check_target_bound budget c +
    fx_check_nested_query_budget EX L budget m rhs + fpn_reads_budget EX budget reads +
    fpn_mem_budget EX budget target + fx_check_nested_lookup_budget EX budget target +
    fx_check_leb_bound budget value (lookup EX L m target) + fpn_sides_budget EX L budget m sides.

Fixpoint fpn_constraints_budget {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 3
  | c :: rest => 6 + fpn_constraint_budget EX L S budget m c + fpn_constraints_budget EX L S
    budget m rest
  end.

Fixpoint fpn_unknowns_budget {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (budget : fx_check_external_budget X C A B) (ix : sys_index X C) (m : assignment X A)
    (xs : list X) : nat :=
  match xs with
  | [] => 3
  | x :: rest => 14 + fx_check_encode_bound budget x + 5 * Pos.size_nat (encode EX x) +
      fpn_constraints_budget EX L S budget m (contributors_of EX ix x) +
      fpn_unknowns_budget EX L S budget ix m rest
  end.

Definition fx_partial_nested_input_budget {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (budget : fx_check_external_budget X C A B) (ix : sys_index X C)
    (explored : FinSet.t X) (m : assignment X A) : nat :=
  9 + 19 * audit_trie_nodes explored + audit_trie_output_bits explored +
    fpn_unknowns_budget EX L S budget ix m (FinSet.elements explored).

(** With checker callback erasure and bounds, every nested partial-check run returns the original
    result within its input budget. *)
Definition fx_partial_nested_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B)
    (budget : fx_check_external_budget X C A B),
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_partial_nested_run L ix explored m cb out events ->
    out = check_partial EX L S SS ix explored m /\
    fx_partial_nested_work budget events <= fx_partial_nested_input_budget EX L S budget ix
  explored m.

(** Set addition, membership and removal bodies satisfy the checker encoder source relation; fold
    events impose no condition. *)
Definition fpn_set_source_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (body : list (audit_set_event X B)) : Prop :=
  Forall (fun e =>
    match e with
    | AuditSetAdd x code _ _ trace _
    | AuditSetMem x code _ _ trace _
    | AuditSetRemove x code _ _ trace _ => fx_check_encode_source source x code trace
    | AuditSetFold _ _ => True
    end) body.

(** Every encoded map key in the body is justified by the checker encoder source relation. *)
Definition fpn_map_source_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (body : list (audit_map_event X (list C) B)) : Prop :=
  Forall (fun e =>
    match e with
    | AuditMapGet x code _ _ trace _
    | AuditMapSet x _ code _ _ trace _
    | AuditMapRemove x code _ _ trace _ => fx_check_encode_source source x code trace
    end) body.

(** Checker, set-membership and index events require their respective nested source relations;
    other partial-check events impose no condition. *)
Definition fx_partial_external_trace_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (events : list (fx_partial_nested_event X C A B)) : Prop :=
  Forall (fun e =>
    match e with
    | FpnCheck body => fx_check_external_trace_adequacy source body
    | FpnMem _ _ _ body => fpn_set_source_adequacy source body
    | FpnIndex _ _ _ body => fpn_map_source_adequacy source body
    | _ => True
    end) events.

(** With index laws, checker callback erasure and bounds, and adequate trace receipts, a
    partial-check run has its original result within its input bound. *)
Definition fx_partial_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B)
    (budget : fx_check_external_budget X C A B) (source : fx_check_external_source X C A B),
    sys_index_laws EX S SS ix ->
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_partial_nested_run L ix explored m cb out events -> fx_partial_external_trace_adequacy
  source events ->
    out = check_partial EX L S SS ix explored m /\
    fx_partial_nested_work budget events <= fx_partial_nested_input_budget EX L S budget ix
  explored m.
