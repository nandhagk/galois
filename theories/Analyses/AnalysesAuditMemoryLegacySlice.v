(** * Legacy slice node traversal

    Both membership lookups occur at every listed node, including a false first lookup.
    Footprint testing occurs exactly when both memberships hold, and forallb visits the tail.
    For example, a missing forward membership still incurs the backward lookup.
    Builds on: the actual legacy overlap and finite-set source observers. *)
From Stdlib Require Import List PArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacyOverlap.
Import List.ListNotations.
Open Scope bool_scope.

Inductive audit_legacy_slice_event (N T CN CT W : Type) : Type :=
  | AuditLegacySliceNode (node : N) (forward backward : bool)
      (first second : list (audit_set_event N CN))
  | AuditLegacySliceWrite (node : N) (writes : list (footprint T)) (calls : list W)
      (disjoint : bool) (checks : list (audit_legacy_overlap_event T CT)).
Arguments AuditLegacySliceNode {N T CN CT W} _ _ _ _ _.
Arguments AuditLegacySliceWrite {N T CN CT W} _ _ _ _ _.

Fixpoint audit_legacy_slice_nodes {N T CN CT W} (node_enc : N -> positive * list CN)
    (site_enc : T -> positive * list CT) (writes : N -> list (footprint T) * list W)
    (read : list (footprint T)) (forward backward : FinSet.t N) (nodes : list N)
    : bool * list (audit_legacy_slice_event N T CN CT W) :=
  match nodes with
  | [] => (true, [])
  | n :: rest =>
      let '(f, fe) := audit_finset_mem node_enc n forward in
      let '(b, be) := audit_finset_mem node_enc n backward in
      let '(head, extra) := if andb f b then
          let '(footprints, we) := writes n in
          let '(answer, de) := audit_legacy_disjoint site_enc footprints read in
          (answer, [AuditLegacySliceWrite n footprints we answer de])
        else (true, []) in
      let '(tail, te) := audit_legacy_slice_nodes node_enc site_enc writes read
        forward backward rest in
      (andb head tail, AuditLegacySliceNode n f b fe be :: extra ++ te)
  end.

(** With matching node and site codes, the slice scan checks disjointness exactly at nodes in
    both reached sets. *)
Definition audit_legacy_slice_nodes_erases_statement : Prop :=
  forall N T CN CT W (EN : encoding N) (ET : encoding T)
      (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
      (writes : N -> list (footprint T) * list W) read forward backward nodes,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    fst (audit_legacy_slice_nodes node_enc site_enc writes read forward backward nodes) =
      forallb (fun n => if FinSet.mem EN n forward && FinSet.mem EN n backward
        then legacy_disjoint_b ET (fst (writes n)) read else true) nodes.

Fixpoint audit_legacy_slice_source_work {N T CN CT W} (node_work : list CN -> nat)
    (site_work : list CT -> nat) (writes_work : list W -> nat)
    (events : list (audit_legacy_slice_event N T CN CT W)) : nat :=
  match events with
  | [] => 0
  | AuditLegacySliceNode _ _ _ fe be :: rest =>
      4 + audit_finset_source_work node_work fe + audit_finset_source_work node_work be +
      audit_legacy_slice_source_work node_work site_work writes_work rest
  | AuditLegacySliceWrite _ _ we _ de :: rest =>
      2 + writes_work we + audit_legacy_overlap_source_work site_work de +
      audit_legacy_slice_source_work node_work site_work writes_work rest
  end.

(** The budget uses each actual input node and the original membership decision. *)
Fixpoint audit_legacy_slice_budget {N T CN CT W} (node_enc : N -> positive * list CN)
    (site_enc : T -> positive * list CT) (writes : N -> list (footprint T) * list W)
    (node_work : list CN -> nat) (site_work : list CT -> nat) (writes_work : list W -> nat)
    (read : list (footprint T)) (forward backward : FinSet.t N) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | n :: rest =>
      let '(f, fe) := audit_finset_mem node_enc n forward in
      let '(b, be) := audit_finset_mem node_enc n backward in
      4 + audit_finset_source_work node_work fe + audit_finset_source_work node_work be +
      (if andb f b then
        2 + writes_work (snd (writes n)) +
          audit_legacy_overlap_budget site_enc site_work (fst (writes n)) read
       else 0) +
      audit_legacy_slice_budget node_enc site_enc writes node_work site_work writes_work
        read forward backward rest
  end.

(** Slice node-scan work is bounded by membership probes and selected write and overlap budgets. *)
Definition audit_legacy_slice_nodes_source_bound_statement : Prop :=
  forall N T CN CT W (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
      (writes : N -> list (footprint T) * list W) node_work site_work writes_work
      read forward backward nodes,
    audit_legacy_slice_source_work node_work site_work writes_work
      (snd (audit_legacy_slice_nodes node_enc site_enc writes read forward backward nodes)) <=
      audit_legacy_slice_budget node_enc site_enc writes node_work site_work writes_work
        read forward backward nodes.
