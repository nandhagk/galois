(** * AnalysesAuditRewriteFacadeMaterialize

    This module relates provenance evidence to legacy replay steps and records their work.
    For example, a stored reflexive evidence node materializes to an empty replay list.
    Builds on: AnalysesEgraph and
    RewriteAuditProofCarrier. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditProofClosure.
Import List.ListNotations.

Fixpoint rw_facade_materialize_project_atomic {K} (source : rw_term K unit nat) : term K * nat :=
  match source with
  | RWVar _ v => (TVar v, 64)
  | RWApp _ op children =>
    let fix visit (ts : list (rw_term K unit nat)) : list (term K) * nat :=
      match ts with
      | nil => (nil, 64)
      | t :: rest =>
        let '(head, hw) := rw_facade_materialize_project_atomic t in
        let '(tail, tw) := visit rest in
        (head :: tail, 64 + hw + tw)
      end in
    let '(args, work) := visit children in
    (TApp op args, 64 + work)
  end.

Fixpoint rw_facade_binding_max {K} (entries : list (nat * rw_term K unit nat)) : option nat * nat :=
  match entries with
  | nil => (None, 64)
  | (index, _) :: rest =>
    let '(tail, work) := rw_facade_binding_max rest in
    match tail with
    | None => (Some index, 64 + work)
    | Some largest =>
      let '(order, cw) := rw_rp_nat_compare index largest in
      (Some (
        match order with
        | Gt => index
        | _ => largest
        end), 64 + work + cw)
    end
  end.

Fixpoint rw_facade_binding_range {K} (bindings : Map.t nat (rw_term K unit nat))
    (remaining index : nat) : list (term K) * nat :=
  match remaining with
  | 0 => (nil, 64)
  | S rest =>
    let '(found, trace) := audit_map_get audit_nat_encode index bindings in
    let '(head, hw) :=
      match found with
      | None => (TVar index, 64)
      | Some term => rw_facade_materialize_project_atomic term
      end in
    let '(tail, tw) := rw_facade_binding_range bindings rest (S index) in
    (head :: tail, 64 + audit_map_source_work audit_nat_events_work trace + hw + tw)
  end.

Definition rw_facade_bindings_atomic {K} (bindings : Map.t nat (rw_term K unit nat)) :
    list (term K) * nat :=
  let '(entries, trace) := audit_map_elements bindings in
  let '(largest, mw) := rw_facade_binding_max entries in
  match largest with
  | None => (nil, 64 + audit_elements_work trace + mw)
  | Some n =>
    let '(out, work) := rw_facade_binding_range bindings (S n) 0 in
    (out, 64 + audit_elements_work trace + mw + work)
  end.

Fixpoint rw_facade_invert_onto {K} (steps acc : list (rewrite_step K)) :
    list (rewrite_step K) * nat :=
  match steps with
  | nil => (acc, 64)
  | step :: rest =>
    let flipped :=
      RewriteStep (step_pos step) (step_rule step) (negb (step_forward step)) (step_subst step) in
    let '(out, work) := rw_facade_invert_onto rest (flipped :: acc) in
    (out, 128 + work)
  end.

Fixpoint rw_facade_prefix_atomic {K} (position : nat) (steps : list (rewrite_step K)) :
    list (rewrite_step K) * nat :=
  match steps with
  | nil => (nil, 64)
  | step :: rest =>
    let head :=
      RewriteStep (position :: step_pos step) (step_rule step) (step_forward step)
        (step_subst step) in
    let '(tail, work) := rw_facade_prefix_atomic position rest in
    (head :: tail, 128 + work)
  end.

(** Materializing a provenance node produces replay steps and their accumulated work. *)
Inductive rw_facade_materialize_run {K} (proof : rw_provenance K unit nat nat) :
    positive -> list (rewrite_step K) -> nat -> Prop :=
  | RPFMaterializeRefl : forall id node trace,
      audit_map_get audit_positive_encode id (rw_provenance_nodes proof) = (Some node, trace) ->
      rw_evidence_reason_of node = RWEvidenceRefl ->
      rw_facade_materialize_run proof id nil
        (64 + audit_map_source_work audit_basic_encoding_work trace)
  | RPFMaterializeRule : forall id node trace rule bindings steps work,
      audit_map_get audit_positive_encode id (rw_provenance_nodes proof) = (Some node, trace) ->
      rw_evidence_reason_of node = RWEvidenceRule rule bindings ->
      rw_facade_bindings_atomic bindings = (steps, work) ->
      rw_facade_materialize_run proof id [RewriteStep nil rule true steps]
        (64 + audit_map_source_work audit_basic_encoding_work trace + work)
  | RPFMaterializeSym : forall id node trace child steps child_work out inversion_work,
      audit_map_get audit_positive_encode id (rw_provenance_nodes proof) = (Some node, trace) ->
      rw_evidence_reason_of node = RWEvidenceSym child ->
      rw_facade_materialize_run proof child steps child_work ->
      rw_facade_invert_onto steps nil = (out, inversion_work) ->
      rw_facade_materialize_run proof id out
        (64 + audit_map_source_work audit_basic_encoding_work trace + child_work + inversion_work)
  | RPFMaterializeTrans : forall id node trace first second lhs rhs lw rw out append_work,
      audit_map_get audit_positive_encode id (rw_provenance_nodes proof) = (Some node, trace) ->
      rw_evidence_reason_of node = RWEvidenceTrans first second ->
      rw_facade_materialize_run proof first lhs lw ->
      rw_facade_materialize_run proof second rhs rw ->
      rw_rp_append lhs rhs = (out, append_work) ->
      rw_facade_materialize_run proof id out
        (64 + audit_map_source_work audit_basic_encoding_work trace + lw + rw + append_work)
  | RPFMaterializeCongruence : forall id node trace children steps work,
      audit_map_get audit_positive_encode id (rw_provenance_nodes proof) = (Some node, trace) ->
      rw_evidence_reason_of node = RWEvidenceCongruence children ->
      rw_facade_materialize_children_run proof children 0 steps work ->
      rw_facade_materialize_run proof id steps
        (64 + audit_map_source_work audit_basic_encoding_work trace + work)
(** Child materialization combines the replay steps and work of a list of references
    at successive child positions. *)
with rw_facade_materialize_children_run {K} (proof : rw_provenance K unit nat nat) :
    list positive -> nat -> list (rewrite_step K) -> nat -> Prop :=
  | RPFMaterializeChildrenNil : forall position,
      rw_facade_materialize_children_run proof nil position nil 64
  | RPFMaterializeChildrenCons : forall id rest position steps sw prefixed pw tail tw out aw,
      rw_facade_materialize_run proof id steps sw ->
      rw_facade_prefix_atomic position steps = (prefixed, pw) ->
      rw_facade_materialize_children_run proof rest (S position) tail tw ->
      rw_rp_append prefixed tail = (out, aw) ->
      rw_facade_materialize_children_run proof (id :: rest) position out (64 + sw + pw + tw + aw).

(** If the requested node exists and every reference points to a smaller existing node,
    materialization has a replay list and work observation. *)
Definition rw_facade_materialize_total_statement : Prop :=
  forall K (proof : rw_provenance K unit nat nat) id node,
    Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
    (forall key current,
      Map.get positive_encoding key (rw_provenance_nodes proof) = Some current ->
      Forall (fun child => (child < key)%positive /\
        exists previous,
          Map.get positive_encoding child (rw_provenance_nodes proof) = Some previous)
        (rw_reason_references (rw_evidence_reason_of current))) ->
    exists steps work, rw_facade_materialize_run proof id steps work.

(** Erasing binding-conversion work yields indices through the maximum binding,
    projecting present terms and using variables for gaps. *)
Definition rw_facade_bindings_erases_statement : Prop :=
  forall K (attempt : rw_attempt K unit nat nat),
    fst (rw_facade_bindings_atomic (rw_attempt_sub attempt)) =
      match fst (rw_facade_binding_max (Map.elements (rw_attempt_sub attempt))) with
      | None => nil
      | Some n => map (fun index =>
        match Map.get nat_encoding index (rw_attempt_sub attempt) with
        | None => TVar index
        | Some term => legacy_project term
        end) (seq 0 (S n))
      end.
