(** * Strict full checker with concrete assignment lookup

    Every query read and side comparison retains the actual map-lookup subrun.
    Both arguments of boolean conjunction are evaluated even after a false comparison.
    For example, a failed comparison does not skip the later strict boolean argument.
    Builds on: FixpointCheck and the counted worklist query model. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

Inductive fx_fullcheck_event (X C A : Type) : Type :=
  | FfcQuery (body : audit_trace (fx_declared_call X C A))
  | FfcRhs (c : C) (result : Query.t X A)
  | FfcTarget (c : C) (result : X)
  | FfcLeb (lhs rhs : A) (result : bool)
  | FfcAnd (lhs rhs result : bool)
  | FfcCase (site : nat).

Arguments FfcQuery {X C A} _.

Arguments FfcRhs {X C A} _ _.

Arguments FfcTarget {X C A} _ _.

Arguments FfcLeb {X C A} _ _ _.

Arguments FfcAnd {X C A} _ _ _.

Arguments FfcCase {X C A} _.

Section Check.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (m : assignment X A).

Fixpoint fx_fullcheck_sides (sides : list (X * A)) : bool * list (fx_fullcheck_event X C A) :=
  match sides with
  | [] => (true, [FfcCase 0])
  | (x, value) :: rest =>
      let '(old, lookup_events) := @fx_model_lookup X C A EX L m x in
      let head := leb L value old in
      let '(tail, tail_events) := fx_fullcheck_sides rest in
      (andb head tail, FfcCase 0 :: FfcQuery lookup_events :: FfcLeb value old head ::
        tail_events ++ [FfcAnd head tail (andb head tail)])
  end.

Fixpoint fx_fullcheck_constraints (cs : list C) : bool * list (fx_fullcheck_event X C A) :=
  match cs with
  | [] => (true, [FfcCase 1])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs m in
      let '(value, _, sides) := answer in
      let target := System.target S c in
      let '(old, lookup_events) := @fx_model_lookup X C A EX L m target in
      let direct := leb L value old in
      let '(side_ok, side_events) := fx_fullcheck_sides sides in
      let current := andb direct side_ok in
      let '(tail, tail_events) := fx_fullcheck_constraints rest in
      (andb current tail, FfcCase 1 :: FfcRhs c rhs :: FfcQuery query_events ::
        FfcTarget c target :: FfcQuery lookup_events :: FfcLeb value old direct :: side_events ++
        FfcAnd direct side_ok current :: tail_events ++ [FfcAnd current tail (andb current tail)])
  end.

Definition fx_fullcheck_counted : bool * list (fx_fullcheck_event X C A) :=
  fx_fullcheck_constraints (System.constraints S).

(** Discarding the counted checker's events recovers the original full-check result. *)
Definition fx_fullcheck_erasure_statement : Prop :=
  fst fx_fullcheck_counted = check_post L S (lookup EX L m).

End Check.

Definition fx_fullcheck_event_work {X C A} (EC : encoding C) (event : fx_fullcheck_event X C A)
  : nat :=
  match event with
  | FfcQuery body => fx_declared_model_work EC body
  | _ => 1
  end.

Definition fx_fullcheck_event_budget {X C A} (EC : encoding C) (event : fx_fullcheck_event X C
  A) : nat :=
  match event with
  | FfcQuery body => audit_work body + fx_declared_primitive_budget EC body
  | _ => 1
  end.

Definition fx_fullcheck_work {X C A} (EC : encoding C) (events : list (fx_fullcheck_event X C
  A)) : nat :=
  fold_right (fun event n => fx_fullcheck_event_work EC event + n) 0 events.

Definition fx_fullcheck_budget {X C A} (EC : encoding C) (events : list (fx_fullcheck_event X C
  A)) : nat :=
  fold_right (fun event n => fx_fullcheck_event_budget EC event + n) 0 events.

(** The counted checker returns the original result and its selected work fits the trace-derived
    budget. *)
Definition fx_fullcheck_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A) m,
    let '(out, events) := fx_fullcheck_counted EX L S m in
    out = check_post L S (lookup EX L m) /\ fx_fullcheck_work EC events <= fx_fullcheck_budget
  EC events.

(** These recurrences are functions of source inputs, not the returned event list. The
    budget is a mathematical specification; evaluating it is not part of the claimed run. *)

Fixpoint fx_fullcheck_sides_input_budget {X A} (EX : encoding X) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 1
  | (x, _) :: rest => 3 + fx_fullcheck_lookup_input_budget EX x +
      fx_fullcheck_sides_input_budget EX rest
  end.

Fixpoint fx_fullcheck_constraints_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(_, _, sides) := Query.run rhs (lookup EX L m) in
      6 + fx_fullcheck_query_input_budget EX L m rhs +
        fx_fullcheck_lookup_input_budget EX (System.target S c) +
        fx_fullcheck_sides_input_budget EX sides +
        fx_fullcheck_constraints_input_budget EX L S m rest
  end.

Definition fx_fullcheck_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) : nat :=
  fx_fullcheck_constraints_input_budget EX L S m (System.constraints S).

(** The counted checker returns the original result and its work fits the input-derived budget. *)
Definition fx_fullcheck_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A) m,
    let '(result, events) := fx_fullcheck_counted EX L S m in
    result = check_post L S (lookup EX L m) /\
    fx_fullcheck_work EC events <= fx_fullcheck_input_budget EX L S m.
