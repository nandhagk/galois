(** * Graph audit model computations

    Exercise finite source-model observations used by graph analyses.
    For example, addition records the zero-input branch and reverse counts its steps.
    Builds on: the graph audit base and IDF arithmetic models. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditNAdd
  CollectionsAuditPositiveSub.
From Galois.Graph Require Import GraphPrepare GraphAuditBase.
From Galois.Tests.Graph Require Import GraphGRA1a.
Import List.ListNotations.

Example graph_audit_prepare_nonempty :
  fst (audit_graph_prepare_counted nat_encoding example_graph) =
    prepare nat_encoding example_graph /\
  length (snd (audit_graph_prepare_counted nat_encoding example_graph)) = 24.
Proof.
  split; reflexivity.
Qed.

Example graph_audit_prepare_trace_order :
  firstn 2 (snd (audit_graph_prepare_counted nat_encoding example_graph)) =
    [AuditPrepareOutCall 2 []; AuditPrepareEncodeCall AuditGraphOutSet 2 3%positive].
Proof.
  reflexivity.
Qed.

Example graph_audit_reverse_nonempty :
  audit_graph_reverse_fast_counted [1; 2; 3] [] = ([3; 2; 1], 7).
Proof.
  reflexivity.
Qed.

Example graph_audit_nadd_zero :
  audit_idf_nadd_counted 0%N 3%N = (3%N, [IdfNaddZero 0%N 3%N]).
Proof.
  reflexivity.
Qed.

Example graph_audit_sub_borrow :
  fst (audit_idf_sub_counted 8 3) = 5%positive.
Proof.
  reflexivity.
Qed.

Example graph_audit_nadd_carry :
  fst (audit_idf_nadd_counted 7%N 1%N) = 8%N.
Proof.
  reflexivity.
Qed.

Example graph_audit_sub_underflow :
  fst (audit_idf_sub_counted 2 5) = 1%positive.
Proof.
  reflexivity.
Qed.
