(** * Observation lifetime searches

    The last-reader search considers later components before an earlier component.
    For example, a found later use avoids constructing the earlier component's set.
    Builds on: FixpointObserve and the counted collection operations. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditMap.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointObserve
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks
  FixpointAuditObserveExecute.
Import List.ListNotations.

Inductive fx_observe_expiry_event (X C : Type) : Type :=
  | FxExpirySet (events : list (audit_set_event X (fx_encoder_entry X)))
  | FxExpiryReaders (events : list (audit_map_event X (list C) (fx_encoder_entry X)))
  | FxExpiryMap (events : list (audit_map_event X (list X) (fx_encoder_entry X)))
  | FxExpiryTarget (constraint : C) (target : X)
  | FxExpiryCase.

Arguments FxExpirySet {X C} _.

Arguments FxExpiryReaders {X C} _.

Arguments FxExpiryMap {X C} _.

Arguments FxExpiryTarget {X C} _ _.

Arguments FxExpiryCase {X C}.

(** Every reader's actual target is checked, even if an earlier target matched. *)

Fixpoint fx_observe_reader_uses {X C A} (EX : encoding X) (S : System.t X C A)
    (members : FinSet.t X) (cs : list C) : bool * list (fx_observe_expiry_event X C) :=
  match cs with
  | [] => (false, [FxExpiryCase])
  | c :: rest =>
      let target := System.target S c in
      let '(present, mem) := audit_finset_mem (fx_index_encoder EX) target members in
      let '(later, tail) := fx_observe_reader_uses EX S members rest in
      (present || later, FxExpiryCase :: FxExpiryTarget c target :: FxExpirySet mem :: tail)
  end.

(** Membership and reader lookup are both evaluated for the current component. *)

Definition fx_observe_component_uses {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (members : FinSet.t X) (x : X) :
    bool * list (fx_observe_expiry_event X C) :=
  let '(self, mem) := audit_finset_mem (fx_index_encoder EX) x members in
  let '(found, read) := audit_map_get (fx_index_encoder EX) x (readers ix) in
  let cs :=
    match found with
    | Some items => items
    | None => []
    end in
  let '(used, calls) := fx_observe_reader_uses EX S members cs in
  (self || used, FxExpiryCase :: FxExpirySet mem :: FxExpiryReaders read :: calls).

(** The tail is searched first, and only a missing result inspects this component. *)

Fixpoint fx_observe_last_reader {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x : X) :
    option X * list (fx_observe_expiry_event X C) :=
  match order with
  | [] => (None, [FxExpiryCase])
  | [] :: rest =>
      let '(out, events) := fx_observe_last_reader EX S ix rest x in
      (out, FxExpiryCase :: events)
  | (h :: body) :: rest =>
      let '(last, later) := fx_observe_last_reader EX S ix rest x in
      match last with
      | Some found => (Some found, FxExpiryCase :: later)
      | None =>
          let '(members, set) := audit_finset_of_list (fx_index_encoder EX) (h :: body) in
          let '(used, calls) := fx_observe_component_uses EX S ix members x in
          (if used then Some h else None, FxExpiryCase :: later ++ FxExpirySet set :: calls)
      end
  end.

(** Expiration writes capture both index lookup and persistent update for each selected key. *)

Fixpoint fx_observe_expiry_fold {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (xs : list X) :
    Map.t X (list X) * list (fx_observe_expiry_event X C) :=
  match xs with
  | [] => (Map.empty, [FxExpiryCase])
  | x :: rest =>
      let '(before, tail) := fx_observe_expiry_fold EX S ix order rest in
      let '(last, calls) := fx_observe_last_reader EX S ix order x in
      match last with
      | None => (before, FxExpiryCase :: tail ++ calls)
      | Some h =>
          let '(old, read) := audit_map_get (fx_index_encoder EX) h before in
          let previous :=
            match old with
            | Some ys => ys
            | None => []
            end in
          let '(after, write) := audit_map_set (fx_index_encoder EX) h (x :: previous) before in
          (after, FxExpiryCase :: tail ++ calls ++ [FxExpiryMap read; FxExpiryMap write])
      end
  end.

(** The fold returns the same map as the source expiration traversal. *)

(** Discarding events yields the fold that indexes each present last reader and skips missing
    readers. *)
Definition fx_observe_expiry_fold_statement : Prop :=
  forall (X C A : Type) (EX : encoding X) (S : System.t X C A) (ix : sys_index X C)
    (order : list (list X)) (xs : list X),
    fst (fx_observe_expiry_fold EX S ix order xs) =
      fold_right (fun x expiration =>
        match observation_last_reader EX S ix order x with
        | Some h => index_push EX x h expiration
        | None => expiration
        end) Map.empty xs.

(** The frame fold charges concrete set and map child traces and selected target calls. *)

Definition fx_observe_expiry_event_work {X C} (event : fx_observe_expiry_event X C) : nat :=
  match event with
  | FxExpirySet events => audit_finset_source_work (@length (fx_encoder_entry X)) events
  | FxExpiryReaders events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxExpiryMap events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxExpiryTarget _ _
  | FxExpiryCase => 1
  end.

(** The work is computed from the same captured lifetime-search events. *)

Definition fx_observe_expiry_work {X C} (events : list (fx_observe_expiry_event X C)) : nat :=
  fold_right (fun event total => fx_observe_expiry_event_work event + total) 0 events.

(** The set construction bound charges every source list occurrence. *)

Fixpoint fx_observe_expiry_set_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 4 + 16 * Pos.size_nat (encode EX x) + fx_observe_expiry_set_budget EX rest
  end.

(** Reader checking charges each actual target and finite-set membership. *)

Fixpoint fx_observe_reader_uses_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 9 + 5 * Pos.size_nat (encode EX (System.target S c)) +
      fx_observe_reader_uses_budget EX S rest
  end.

(** The use bound includes the reader-index lookup and all its actual readers. *)

Definition fx_observe_component_uses_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (x : X) : nat :=
  16 + 10 * Pos.size_nat (encode EX x) + fx_observe_reader_uses_budget EX S (readers_of EX ix x).

(** The last-reader bound follows the real selective branch after the recursive tail. *)

Fixpoint fx_observe_last_reader_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x : X) : nat :=
  match order with
  | [] => 1
  | [] :: rest => 1 + fx_observe_last_reader_budget EX S ix rest x
  | (h :: body) :: rest =>
      1 + fx_observe_last_reader_budget EX S ix rest x +
      match observation_last_reader EX S ix rest x with
      | Some _ => 0
      | None => fx_observe_expiry_set_budget EX (h :: body) +
          fx_observe_component_uses_budget EX S ix x
      end
  end.

(** The fold bound charges the selected last-reader search and optional map operations. *)

Fixpoint fx_observe_expiry_fold_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest =>
      1 + fx_observe_expiry_fold_budget EX S ix order rest +
      fx_observe_last_reader_budget EX S ix order x +
      match observation_last_reader EX S ix order x with
      | None => 0
      | Some h => 10 + 21 * Pos.size_nat (encode EX h)
      end
  end.

(** The captured expiration fold has an input-derived source-frame bound. *)

(** The expiry fold's recorded work fits a budget derived from the system, order and input
    values. *)
Definition fx_observe_expiry_fold_bound_statement : Prop :=
  forall (X C A : Type) (EX : encoding X) (S : System.t X C A) (ix : sys_index X C)
    (order : list (list X)) (xs : list X),
    let '(_, events) := fx_observe_expiry_fold EX S ix order xs in
    fx_observe_expiry_work events <= fx_observe_expiry_fold_budget EX S ix order xs.

(** Set, reader, map and target events relate their bodies to encoder or target sources; expiry
    case events require no bodies. *)

Definition fx_observe_expiry_event_source {X C A B}
    (source : fx_declared_callback_source X C A B) (event : fx_observe_expiry_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxExpirySet events => Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies
  | FxExpiryReaders events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxExpiryMap events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxExpiryTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxExpiryCase => bodies = []
  end.

(** Every encoder and target callback has a source witness, and every accepted body fits its
    input bound. *)

Definition fx_observe_expiry_source_laws {X C A B} (EX : encoding X) (S : System.t X C A)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c).

(** The callback budget charges every encoder entry and selected original target call. *)

Definition fx_observe_expiry_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_observe_expiry_event X C) : nat :=
  match event with
  | FxExpirySet events => fx_nested_entries_budget budget (fx_nested_entries events)
  | FxExpiryReaders events =>
      fx_nested_entries_budget budget (flat_map fx_observe_map_entries events)
  | FxExpiryMap events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries events)
  | FxExpiryTarget c _ => fx_budget_target budget c
  | FxExpiryCase => 0
  end.

(** A single expiration-fold witness supplies its erasure, frame bound and callback bodies. *)

(** With expiry callback source laws and bounds, the expiry fold preserves its original result
    with source receipts and a work bound. *)
Definition fx_observe_expiry_fold_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (ix : sys_index X C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (order : list (list X)) (xs : list X),
    fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_expiry_fold EX S ix order xs in
    exists bodies, Forall2 (fx_observe_expiry_event_source source) events bodies /\
      out = fold_right (fun x expiration =>
        match observation_last_reader EX S ix order x with
        | Some h => index_push EX x h expiration
        | None => expiration
        end) Map.empty xs /\
      fx_observe_expiry_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_expiry_fold_budget EX S ix order xs +
        fold_right (fun e n => fx_observe_expiry_external_budget budget e + n) 0 events.
