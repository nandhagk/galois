(** * Legacy half-open footprint overlap

    The legacy checker uses four strict signed comparisons for every pair.
    This observer keeps those operands and the actual site equality execution.
    For example, adjacent half-open ranges do not overlap.
    Builds on: legacy memory certificates and collection primitive observations. *)
From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditPrimitive.
Import List.ListNotations.

Inductive audit_legacy_overlap_event (T C : Type) : Type :=
  | AuditLegacyOverlapOuter (remaining : list (footprint T))
  | AuditLegacyOverlapInner (left : footprint T) (remaining : list (footprint T))
  | AuditLegacyOverlapPair (left right : footprint T) (lc rc : positive)
      (le re : list C) (eq : list audit_positive_eqb_event)
      (same nonempty_left nonempty_right left_cross right_cross result : bool).
Arguments AuditLegacyOverlapOuter {T C} _.
Arguments AuditLegacyOverlapInner {T C} _ _.
Arguments AuditLegacyOverlapPair {T C} _ _ _ _ _ _ _ _ _ _ _ _ _.

Definition audit_legacy_overlap_pair {T C} (enc : T -> positive * list C)
    (left right : footprint T) : bool * list (audit_legacy_overlap_event T C) :=
  let '(lc, le) := enc (fp_site left) in
  let '(rc, re) := enc (fp_site right) in
  let '(same, eq) := audit_positive_eqb lc rc in
  let nl := Z.ltb (fp_lo left) (fp_hi left) in
  let nr := Z.ltb (fp_lo right) (fp_hi right) in
  let lr := Z.ltb (fp_lo left) (fp_hi right) in
  let rl := Z.ltb (fp_lo right) (fp_hi left) in
  let result := andb (andb (andb (andb same nl) nr) lr) rl in
  (result, [AuditLegacyOverlapPair left right lc rc le re eq same nl nr lr rl result]).

Fixpoint audit_legacy_overlap_inner {T C} (enc : T -> positive * list C)
    (left : footprint T) (right : list (footprint T))
    : bool * list (audit_legacy_overlap_event T C) :=
  match right with
  | [] => (false, [AuditLegacyOverlapInner left right])
  | x :: xs =>
      let '(head, he) := audit_legacy_overlap_pair enc left x in
      let '(tail, te) := audit_legacy_overlap_inner enc left xs in
      (orb head tail, AuditLegacyOverlapInner left right :: he ++ te)
  end.

Fixpoint audit_legacy_overlap_exists {T C} (enc : T -> positive * list C)
    (left right : list (footprint T)) : bool * list (audit_legacy_overlap_event T C) :=
  match left with
  | [] => (false, [AuditLegacyOverlapOuter left])
  | x :: xs =>
      let '(head, he) := audit_legacy_overlap_inner enc x right in
      let '(tail, te) := audit_legacy_overlap_exists enc xs right in
      (orb head tail, AuditLegacyOverlapOuter left :: he ++ te)
  end.
Definition audit_legacy_disjoint {T C} (enc : T -> positive * list C)
    (left right : list (footprint T)) : bool * list (audit_legacy_overlap_event T C) :=
  let '(overlap, events) := audit_legacy_overlap_exists enc left right in (negb overlap, events).

Fixpoint audit_legacy_overlap_pairs {T C} (events : list (audit_legacy_overlap_event T C)) : nat :=
  match events with
  | [] => 0
  | AuditLegacyOverlapPair _ _ _ _ _ _ _ _ _ _ _ _ _ :: rest =>
      S (audit_legacy_overlap_pairs rest)
  | _ :: rest => audit_legacy_overlap_pairs rest
  end.

(** Matching site codes recover the legacy half-open footprint disjointness result. *)
Definition audit_legacy_disjoint_erases_statement : Prop :=
  forall T C (enc : T -> positive * list C) (ET : encoding T) left right,
    (forall site, fst (enc site) = encode ET site) ->
    fst (audit_legacy_disjoint enc left right) = legacy_disjoint_b ET left right.

(** Each legacy footprint pair records its comparison event. *)
Definition audit_legacy_overlap_pair_count_statement : Prop :=
  forall T C (enc : T -> positive * list C) left right,
    audit_legacy_overlap_pairs (snd (audit_legacy_disjoint enc left right)) =
      length left * length right.

Fixpoint audit_legacy_overlap_source_work {T C} (encoder_work : list C -> nat)
    (events : list (audit_legacy_overlap_event T C)) : nat :=
  match events with
  | [] => 0
  | AuditLegacyOverlapOuter _ :: rest | AuditLegacyOverlapInner _ _ :: rest =>
      1 + audit_legacy_overlap_source_work encoder_work rest
  | AuditLegacyOverlapPair l r _ _ le re eq _ _ _ _ _ _ :: rest =>
      7 + encoder_work le + encoder_work re + audit_positive_eqb_source_work eq +
      audit_binary_weight (fp_lo l) (fp_hi l) + audit_binary_weight (fp_lo r) (fp_hi r) +
      audit_binary_weight (fp_lo l) (fp_hi r) + audit_binary_weight (fp_lo r) (fp_hi l) +
      audit_legacy_overlap_source_work encoder_work rest
  end.

Fixpoint audit_legacy_overlap_inner_budget {T C} (enc : T -> positive * list C)
    (encoder_work : list C -> nat) (l : footprint T) (rs : list (footprint T)) : nat :=
  match rs with
  | [] => 1
  | r :: rest =>
      8 + encoder_work (snd (enc (fp_site l))) + encoder_work (snd (enc (fp_site r))) +
      2 * Nat.min (Pos.size_nat (fst (enc (fp_site l)))) (Pos.size_nat (fst (enc (fp_site r)))) +
      audit_binary_weight (fp_lo l) (fp_hi l) + audit_binary_weight (fp_lo r) (fp_hi r) +
      audit_binary_weight (fp_lo l) (fp_hi r) + audit_binary_weight (fp_lo r) (fp_hi l) +
      audit_legacy_overlap_inner_budget enc encoder_work l rest
  end.
Fixpoint audit_legacy_overlap_budget {T C} (enc : T -> positive * list C)
    (encoder_work : list C -> nat) (left right : list (footprint T)) : nat :=
  match left with
  | [] => 1
  | l :: rest => 1 + audit_legacy_overlap_inner_budget enc encoder_work l right +
      audit_legacy_overlap_budget enc encoder_work rest right
  end.

(** Legacy overlap work is bounded by the budget for each footprint pair and its captured
    encoder work. *)
Definition audit_legacy_overlap_source_bound_statement : Prop :=
  forall T C (enc : T -> positive * list C) encoder_work left right,
    audit_legacy_overlap_source_work encoder_work (snd (audit_legacy_disjoint enc left right)) <=
      audit_legacy_overlap_budget enc encoder_work left right.
