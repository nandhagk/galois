(** * Observation-plan key comparisons

    Both boolean operands and all list tails are evaluated by the source functions.
    For example, a matching early element does not erase later equality calls.
    Builds on: FixpointObserve and FixpointAuditWorklistCallbacks. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditWorklist
  FixpointAuditWorklistCallbacks.
Import List.ListNotations.

Inductive fx_observe_compare_event (X : Type) : Type :=
  | FxObserveCompare (x y : X) (left right : positive) (result : bool)
  | FxObserveCompareCase.

Arguments FxObserveCompare {X} _ _ _ _ _.

Arguments FxObserveCompareCase {X}.

(** A comparison captures both actual encoder inputs, outputs and the equality result. *)

Definition fx_observe_key_compare {X} (EX : encoding X) (x y : X) :
    bool * list (fx_observe_compare_event X) :=
  let left := encode EX x in
  let right := encode EX y in
  let result := Pos.eqb left right in
  (result, [FxObserveCompare x y left right result]).

(** Both the head predicate and the recursive tail contribute, even after a match. *)

Fixpoint fx_observe_exists_key {X} (EX : encoding X) (x : X) (ys : list X) :
    bool * list (fx_observe_compare_event X) :=
  match ys with
  | [] => (false, [FxObserveCompareCase])
  | y :: rest =>
      let '(same, first) := fx_observe_key_compare EX x y in
      let '(later, tail) := fx_observe_exists_key EX x rest in
      (same || later, FxObserveCompareCase :: first ++ tail)
  end.

(** Every outer element invokes the complete inner scan. *)

Fixpoint fx_observe_all_keys {X} (EX : encoding X) (xs ys : list X) :
    bool * list (fx_observe_compare_event X) :=
  match xs with
  | [] => (true, [FxObserveCompareCase])
  | x :: rest =>
      let '(found, first) := fx_observe_exists_key EX x ys in
      let '(later, tail) := fx_observe_all_keys EX rest ys in
      (found && later, FxObserveCompareCase :: first ++ tail)
  end.

(** Set equality evaluates both directed scans. *)

Definition fx_observe_seteq {X} (EX : encoding X) (xs ys : list X) :
    bool * list (fx_observe_compare_event X) :=
  let '(forward, first) := fx_observe_all_keys EX xs ys in
  let '(backward, later) := fx_observe_all_keys EX ys xs in
  (forward && backward, FxObserveCompareCase :: first ++ later).

(** A duplicate check evaluates all later duplicate checks. *)

Fixpoint fx_observe_nodup {X} (EX : encoding X) (xs : list X) :
    bool * list (fx_observe_compare_event X) :=
  match xs with
  | [] => (true, [FxObserveCompareCase])
  | x :: rest =>
      let '(found, first) := fx_observe_exists_key EX x rest in
      let '(later, tail) := fx_observe_nodup EX rest in
      (negb found && later, FxObserveCompareCase :: first ++ tail)
  end.

(** Source frames charge comparison operand widths and the list constructors. *)

Definition fx_observe_compare_event_work {X} (event : fx_observe_compare_event X) : nat :=
  match event with
  | FxObserveCompare _ _ code1 code2 _ => 4 + Pos.size_nat code1 + Pos.size_nat code2
  | FxObserveCompareCase => 1
  end.

(** The frame work folds over the events captured by the same execution. *)

Definition fx_observe_compare_work {X} (events : list (fx_observe_compare_event X)) : nat :=
  fold_right (fun e n => fx_observe_compare_event_work e + n) 0 events.

(** The inner source bound uses all actual input elements and encoded-key lengths. *)

Fixpoint fx_observe_exists_key_budget {X} (EX : encoding X) (x : X) (ys : list X) : nat :=
  match ys with
  | [] => 1
  | y :: rest => 5 + Pos.size_nat (encode EX x) + Pos.size_nat (encode EX y) +
      fx_observe_exists_key_budget EX x rest
  end.

(** The outer source bound charges each complete inner scan. *)

Fixpoint fx_observe_all_keys_budget {X} (EX : encoding X) (xs ys : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 1 + fx_observe_exists_key_budget EX x ys +
      fx_observe_all_keys_budget EX rest ys
  end.

(** The duplicate-check bound charges the suffix scan for every element. *)

Fixpoint fx_observe_nodup_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 1 + fx_observe_exists_key_budget EX x rest + fx_observe_nodup_budget EX rest
  end.

(** The two-sided source bound is independent of the captured events. *)

Definition fx_observe_seteq_budget {X} (EX : encoding X) (xs ys : list X) : nat :=
  1 + fx_observe_all_keys_budget EX xs ys + fx_observe_all_keys_budget EX ys xs.

(** Set equality retains the actual result and an input-derived source-frame bound. *)

(** Counted set comparison returns the original equality test within the budget for both input
    lists. *)
Definition fx_observe_seteq_statement : Prop :=
  forall (X : Type) (EX : encoding X) (xs ys : list X),
    let '(out, events) := fx_observe_seteq EX xs ys in
    out = observation_seteq EX xs ys /\
    fx_observe_compare_work events <= fx_observe_seteq_budget EX xs ys.

(** Duplicate checking retains the actual result and an input-derived source-frame bound. *)

(** Counted duplicate checking returns the original result within the budget for its input list. *)
Definition fx_observe_nodup_statement : Prop :=
  forall (X : Type) (EX : encoding X) (xs : list X),
    let '(out, events) := fx_observe_nodup EX xs in
    out = observation_nodup_check EX xs /\
    fx_observe_compare_work events <= fx_observe_nodup_budget EX xs.

(** A comparison event relates its two encoder bodies to its operands and codes; a case event
    requires no bodies. *)

Definition fx_observe_compare_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_observe_compare_event X) (bodies : list (list B)) : Prop :=
  match event with
  | FxObserveCompare x y code1 code2 _ => exists body1 body2,
      bodies = [body1; body2] /\ fx_source_encode_x source x code1 body1 /\
        fx_source_encode_x source y code2 body2
  | FxObserveCompareCase => bodies = []
  end.

(** Every unknown-key encoding has a source witness, and every accepted encoder body fits its key
    budget. *)

Definition fx_observe_compare_source_laws {X C A B} (EX : encoding X)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall x code body, fx_source_encode_x source x code body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x).

(** The callback budget sums the two encoder calls of each captured comparison. *)

Definition fx_observe_compare_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_observe_compare_event X) : nat :=
  match event with
  | FxObserveCompare x y _ _ _ => fx_budget_encode_x budget x + fx_budget_encode_x budget y
  | FxObserveCompareCase => 0
  end.

(** One captured set-equality scan carries all source bodies and both cost components. *)

(** Under encoder source laws, set comparison returns the original result with source receipts
    and a work bound. *)
Definition fx_observe_seteq_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (xs ys : list X),
    fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_seteq EX xs ys in
    exists bodies, Forall2 (fx_observe_compare_source source) events bodies /\
      out = observation_seteq EX xs ys /\
      fx_observe_compare_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_seteq_budget EX xs ys +
        fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events.

(** One captured duplicate scan carries its own encoder bodies and frame bound. *)

(** Under encoder source laws, duplicate checking returns the original result with source
    receipts and a work bound. *)
Definition fx_observe_nodup_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (xs : list X),
    fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_nodup EX xs in
    exists bodies, Forall2 (fx_observe_compare_source source) events bodies /\
      out = observation_nodup_check EX xs /\
      fx_observe_compare_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_nodup_budget EX xs +
        fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events.
