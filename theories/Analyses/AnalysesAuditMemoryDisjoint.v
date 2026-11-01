(** * Counted footprint disjointness

    This mirror retains every footprint pair and both strict boolean operands.
    For example, a false first pair does not skip later [forallb] operands.
    Builds on: AnalysesMemoryWalk and the footprint API. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditPrimitive.
Import List.ListNotations.

Inductive audit_disjoint_event (T CE : Type) : Type :=
  | AuditDisjointOuter (remaining : list (footprint T))
  | AuditDisjointInner (item : footprint T) (remaining : list (footprint T))
  | AuditDisjointPair (left right : footprint T) (left_code right_code : positive)
      (left_events right_events : list CE) (eq_events : list audit_positive_eqb_event)
      (same left_before right_before result : bool).

Arguments AuditDisjointOuter {T CE} _.
Arguments AuditDisjointInner {T CE} _ _.
Arguments AuditDisjointPair {T CE} _ _ _ _ _ _ _ _ _ _ _.

(** Both comparisons and both component encoder executions are retained for each pair. *)
Definition audit_disjoint_pair {T CE} (enc : T -> positive * list CE)
    (left right : footprint T) : bool * list (audit_disjoint_event T CE) :=
  let '(lc, le) := enc (fp_site left) in
  let '(rc, re) := enc (fp_site right) in
  let '(same, eq_events) := audit_positive_eqb lc rc in
  let first := Z.leb (fp_hi left) (fp_lo right) in
  let second := Z.leb (fp_hi right) (fp_lo left) in
  let result := orb (orb (negb same) first) second in
  (result, [AuditDisjointPair left right lc rc le re eq_events same first second result]).

(** Every right operand of [andb] is evaluated, even after a false earlier result. *)
Fixpoint audit_disjoint_inner {T CE} (enc : T -> positive * list CE)
    (item : footprint T) (input : list (footprint T))
    : bool * list (audit_disjoint_event T CE) :=
  match input with
  | [] => (true, [AuditDisjointInner item input])
  | x :: rest =>
      let '(head, he) := audit_disjoint_pair enc item x in
      let '(tail, te) := audit_disjoint_inner enc item rest in
      (andb head tail, AuditDisjointInner item input :: he ++ te)
  end.

Fixpoint audit_footprints_disjoint {T CE} (enc : T -> positive * list CE)
    (left right : list (footprint T)) : bool * list (audit_disjoint_event T CE) :=
  match left with
  | [] => (true, [AuditDisjointOuter left])
  | item :: rest =>
      let '(head, he) := audit_disjoint_inner enc item right in
      let '(tail, te) := audit_footprints_disjoint enc rest right in
      (andb head tail, AuditDisjointOuter left :: he ++ te)
  end.

Definition audit_memory_scopes_disjoint {T CE} (enc : T -> positive * list CE)
    (left right : memory_scope T) : bool * list (audit_disjoint_event T CE) :=
  match left, right with
  | MemoryRegions fs, MemoryRegions gs => audit_footprints_disjoint enc fs gs
  | _, _ => (false, [])
  end.

(** * Future erasure and pair-count obligations *)

(** Matching site codes recover the plain pairwise footprint disjointness boolean. *)
Definition audit_footprints_disjoint_erases_statement : Prop :=
  forall T CE (enc : T -> positive * list CE) (ET : encoding T) left right,
    (forall site, fst (enc site) = encode ET site) ->
    fst (audit_footprints_disjoint enc left right) = footprints_disjoint ET left right.

(** Matching site codes recover disjointness for region scopes and the all-memory fallback. *)
Definition audit_memory_scopes_disjoint_erases_statement : Prop :=
  forall T CE (enc : T -> positive * list CE) (ET : encoding T) left right,
    (forall site, fst (enc site) = encode ET site) ->
    fst (audit_memory_scopes_disjoint enc left right) = memory_scopes_disjoint ET left right.

Fixpoint audit_disjoint_pairs {T CE} (events : list (audit_disjoint_event T CE)) : nat :=
  match events with
  | [] => 0
  | AuditDisjointPair _ _ _ _ _ _ _ _ _ _ _ :: rest => S (audit_disjoint_pairs rest)
  | _ :: rest => audit_disjoint_pairs rest
  end.

(** The footprint traversal records one pair event for each pair of inputs. *)
Definition audit_disjoint_pairs_count_statement : Prop :=
  forall T CE (enc : T -> positive * list CE) left right,
    audit_disjoint_pairs (snd (audit_footprints_disjoint enc left right)) =
      length left * length right.

(** * Fixed primitive charges and input-derived pair budget *)

(** Comparison charges use the actual positive and signed operands. *)
Definition audit_disjoint_pair_work {T CE} (encoder_work : list CE -> nat)
    (left right : footprint T) (le re : list CE) (eq_events : list audit_positive_eqb_event)
    : nat :=
  4 + encoder_work le + encoder_work re + audit_positive_eqb_source_work eq_events +
    audit_binary_weight (fp_hi left) (fp_lo right) +
    audit_binary_weight (fp_hi right) (fp_lo left).

Fixpoint audit_disjoint_source_work {T CE} (encoder_work : list CE -> nat)
    (events : list (audit_disjoint_event T CE)) : nat :=
  match events with
  | [] => 0
  | AuditDisjointOuter _ :: rest => 1 + audit_disjoint_source_work encoder_work rest
  | AuditDisjointInner _ _ :: rest => 1 + audit_disjoint_source_work encoder_work rest
  | AuditDisjointPair lf rf _ _ le re eq_events _ _ _ _ :: rest =>
      audit_disjoint_pair_work encoder_work lf rf le re eq_events +
        audit_disjoint_source_work encoder_work rest
  end.

Fixpoint audit_disjoint_inner_budget {T CE} (enc : T -> positive * list CE)
    (encoder_work : list CE -> nat) (item : footprint T) (input : list (footprint T)) : nat :=
  match input with
  | [] => 1
  | x :: rest =>
      1 + audit_disjoint_pair_work encoder_work item x (snd (enc (fp_site item)))
        (snd (enc (fp_site x)))
        (snd (audit_positive_eqb (fst (enc (fp_site item))) (fst (enc (fp_site x))))) +
        audit_disjoint_inner_budget enc encoder_work item rest
  end.

Fixpoint audit_disjoint_budget {T CE} (enc : T -> positive * list CE)
    (encoder_work : list CE -> nat) (left right : list (footprint T)) : nat :=
  match left with
  | [] => 1
  | x :: rest => 1 + audit_disjoint_inner_budget enc encoder_work x right +
      audit_disjoint_budget enc encoder_work rest right
  end.

(** The paired trace's source work equals the budget derived from both input lists. *)
Definition audit_disjoint_source_work_statement : Prop :=
  forall T CE (enc : T -> positive * list CE) encoder_work left right,
    audit_disjoint_source_work encoder_work (snd (audit_footprints_disjoint enc left right)) =
      audit_disjoint_budget enc encoder_work left right.
