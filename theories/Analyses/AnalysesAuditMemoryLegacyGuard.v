(** * Strict legacy producer guard

    This mirror executes every operand of the existing three-way guard.
    For example, a failing node comparison still probes both membership sets.
    Builds on: shared encoding, positive equality and finite-set observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore.
From Galois.Collections Require Import CollectionsAuditPrimitive CollectionsAuditFinSet.
Import List.ListNotations.

Inductive audit_legacy_guard_event (N E CN CE SE : Type) : Type :=
  | AuditGuardSource (edge : E) (node : N) (events : list SE)
  | AuditGuardNodeEncode (node : N) (code : positive) (events : list CN)
  | AuditGuardEqual (left right : positive) (result : bool) (events : list audit_positive_eqb_event)
  | AuditGuardReached (node : N) (result : bool) (events : list (audit_set_event N CN))
  | AuditGuardListed (edge : E) (result : bool) (events : list (audit_set_event E CE)).

Arguments AuditGuardSource {N E CN CE SE} _ _ _.
Arguments AuditGuardNodeEncode {N E CN CE SE} _ _ _.
Arguments AuditGuardEqual {N E CN CE SE} _ _ _ _.
Arguments AuditGuardReached {N E CN CE SE} _ _ _.
Arguments AuditGuardListed {N E CN CE SE} _ _ _.

(** The two source calls and both membership probes are always evaluated. *)
Definition audit_legacy_guard {N E CN CE SE} (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (source : E -> N * list SE)
    (reached : FinSet.t N) (listed : FinSet.t E) (edge : E) (node : N)
    : bool * list (audit_legacy_guard_event N E CN CE SE) :=
  let '(first_source, fs) := source edge in
  let '(first_code, fc) := node_enc first_source in
  let '(node_code, nc) := node_enc node in
  let '(equal, eq) := audit_positive_eqb first_code node_code in
  let '(second_source, ss) := source edge in
  let '(reachable, re) := audit_finset_mem node_enc second_source reached in
  let '(is_listed, li) := audit_finset_mem edge_enc edge listed in
  (andb (andb equal reachable) is_listed,
    [AuditGuardSource edge first_source fs; AuditGuardNodeEncode first_source first_code fc;
     AuditGuardNodeEncode node node_code nc; AuditGuardEqual first_code node_code equal eq;
     AuditGuardSource edge second_source ss; AuditGuardReached second_source reachable re;
     AuditGuardListed edge is_listed li]).

(** Matching node and edge codes and graph sources recover the source-equality, reached and
    listed guard boolean. *)
Definition audit_legacy_guard_erases_statement : Prop :=
  forall N E CN CE SE (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (source : E -> N * list SE) reached listed edge node,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall e, fst (source e) = Graph.source g e) ->
    fst (audit_legacy_guard node_enc edge_enc source reached listed edge node) =
      andb (andb (Pos.eqb (encode EN (Graph.source g edge)) (encode EN node))
        (FinSet.mem EN (Graph.source g edge) reached)) (FinSet.mem EE edge listed).

(** The legacy guard records exactly seven outer events. *)
Definition audit_legacy_guard_count_statement : Prop :=
  forall N E CN CE SE (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (source : E -> N * list SE) reached listed edge node,
    length (snd (audit_legacy_guard node_enc edge_enc source reached listed edge node)) = 7.

(** Each fixed operation charges its captured internal source work and true external child trace. *)
Fixpoint audit_legacy_guard_primitive_work {N E CN CE SE}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (source_work : list SE -> nat)
    (events : list (audit_legacy_guard_event N E CN CE SE)) : nat :=
  match events with
  | [] => 0
  | AuditGuardSource _ _ calls :: rest => source_work calls +
      audit_legacy_guard_primitive_work node_work edge_work source_work rest
  | AuditGuardNodeEncode _ _ calls :: rest => node_work calls +
      audit_legacy_guard_primitive_work node_work edge_work source_work rest
  | AuditGuardEqual _ _ _ calls :: rest => audit_positive_eqb_source_work calls +
      audit_legacy_guard_primitive_work node_work edge_work source_work rest
  | AuditGuardReached _ _ calls :: rest => audit_finset_source_work node_work calls +
      audit_legacy_guard_primitive_work node_work edge_work source_work rest
  | AuditGuardListed _ _ calls :: rest => audit_finset_source_work edge_work calls +
      audit_legacy_guard_primitive_work node_work edge_work source_work rest
  end.

Definition audit_legacy_guard_source_work {N E CN CE SE}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (source_work : list SE -> nat)
    (events : list (audit_legacy_guard_event N E CN CE SE)) : nat :=
  2 * length events + audit_legacy_guard_primitive_work node_work edge_work source_work events.

(** Guard work is bounded by fourteen outer units plus its captured primitive calls. *)
Definition audit_legacy_guard_source_bound_statement : Prop :=
  forall N E CN CE SE (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (source : E -> N * list SE) reached listed edge node node_work edge_work source_work,
    let events := snd (audit_legacy_guard node_enc edge_enc source reached listed edge node) in
    audit_legacy_guard_source_work node_work edge_work source_work events <=
      14 + audit_legacy_guard_primitive_work node_work edge_work source_work events.
