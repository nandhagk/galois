(** * RewriteAuditIndexBucket

    This module records indexed bucket additions and removals and states their work bounds.
    For example, removing an identifier from a missing bucket returns the original table.
    Builds on: RewriteAuditIndexBuild and
    RewriteAuditIndexTickReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexTickReference.
Import List.ListNotations.

Inductive rw_ri_bucket_call (A CE : Type) : Type :=
  | RIBucketRead : list (audit_map_event A (FinSet.t rw_id) CE) -> rw_ri_bucket_call A CE
  | RIBucketMember : list (audit_set_event rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_bucket_call A CE
  | RIBucketWrite : list (audit_map_event A (FinSet.t rw_id) CE) -> rw_ri_bucket_call A CE.
Arguments RIBucketRead {A CE}.
Arguments RIBucketMember {A CE}.
Arguments RIBucketWrite {A CE}.

Definition rw_ri_bucket_event_cost {A CE} (enc_work : list CE -> nat) (event : audit_event
    (rw_ri_bucket_call A CE)) : nat :=
  match event with
  | AuditCall (RIBucketRead trace) => 1 + audit_map_source_work enc_work trace
  | AuditCall (RIBucketMember trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | AuditCall (RIBucketWrite trace) => 1 + audit_map_source_work enc_work trace
  | _ => 1
  end.

Definition rw_ri_bucket_trace_cost {A CE} (enc_work : list CE -> nat) (trace : audit_trace
    (rw_ri_bucket_call A CE)) : nat :=
  fold_right (fun event total => rw_ri_bucket_event_cost enc_work event + total) 0 trace.

Definition rw_ri_bucket_add_atomic {A CE} (enc : A -> positive * list CE) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) * audit_trace (rw_ri_bucket_call A
    CE) :=
  let '(found, read_trace) := audit_map_get enc key table in
  let bucket :=
    match found with
    | Some stored => stored
    | None => FinSet.empty
    end in
  let '(updated, member_trace) := audit_finset_add audit_positive_encode id bucket in
  let '(out, write_trace) := audit_map_set enc key updated table in
  (out, [AuditCall (RIBucketRead read_trace); AuditCase 834 [];
    AuditCall (RIBucketMember member_trace); AuditCall (RIBucketWrite write_trace)]).

Definition rw_ri_bucket_remove_atomic {A CE} (enc : A -> positive * list CE) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) * audit_trace (rw_ri_bucket_call A
    CE) :=
  let '(found, read_trace) := audit_map_get enc key table in
  match found with
  | None => (table, [AuditCall (RIBucketRead read_trace); AuditCase 835 []])
  | Some bucket =>
    let '(updated, member_trace) := audit_finset_remove audit_positive_encode id bucket in
    if FinSet.is_empty updated then
      let '(out, write_trace) := audit_map_remove enc key table in
      (out, [AuditCall (RIBucketRead read_trace); AuditCase 836 [];
        AuditCall (RIBucketMember member_trace); AuditCase 837 [];
        AuditCall (RIBucketWrite write_trace)])
    else
      let '(out, write_trace) := audit_map_set enc key updated table in
      (out, [AuditCall (RIBucketRead read_trace); AuditCase 836 [];
        AuditCall (RIBucketMember member_trace); AuditCase 838 [];
        AuditCall (RIBucketWrite write_trace)])
  end.

Definition rw_ri_bucket_atomic_budget {A CE} (enc : A -> positive * list CE) (enc_work : list CE ->
    nat) (key : A) (id : rw_id) : nat :=
  let '(code, trace) := enc key in
  50 + 2 * enc_work trace + 32 * Pos.size_nat code + 16 * Pos.size_nat id.

(** When the key encoder returns its specified code, erasing bucket-add receipts
    yields the plain bucket addition. *)
Definition rw_ri_bucket_add_erases_contract : Prop :=
  forall A CE (E : encoding A) (enc : A -> positive * list CE) key id table, fst (enc key) = encode
    E key ->
    fst (rw_ri_bucket_add_atomic enc key id table) = rw_ri_bucket_add E key id table.

(** When the key encoder returns its specified code, erasing bucket-remove receipts
    yields the plain bucket removal. *)
Definition rw_ri_bucket_remove_erases_contract : Prop :=
  forall A CE (E : encoding A) (enc : A -> positive * list CE) key id table, fst (enc key) = encode
    E key ->
    fst (rw_ri_bucket_remove_atomic enc key id table) = rw_ri_bucket_remove E key id table.

(** The expanded bucket-add trace cost is bounded by the atomic budget for its inputs. *)
Definition rw_ri_bucket_add_bound_contract : Prop :=
  forall A CE (enc : A -> positive * list CE) enc_work key id table, rw_ri_bucket_trace_cost
    enc_work (snd (rw_ri_bucket_add_atomic enc key id table)) <= rw_ri_bucket_atomic_budget enc
    enc_work key id.

(** The expanded bucket-remove trace cost is bounded by the atomic budget for its inputs. *)
Definition rw_ri_bucket_remove_bound_contract : Prop :=
  forall A CE (enc : A -> positive * list CE) enc_work key id table, rw_ri_bucket_trace_cost
    enc_work (snd (rw_ri_bucket_remove_atomic enc key id table)) <= rw_ri_bucket_atomic_budget enc
    enc_work key id.
