(** * Computed PRE source observations

    These examples exercise arithmetic, finite candidates, reset indexes and graph callbacks.
    For example, enumeration of two elements retains both singleton choices and their order.
    Builds on: AnalysesAuditPre and its family, finite and solver components. *)

From Stdlib Require Import List NArith PArith.
From Galois.Analyses Require Import AnalysesAuditPre AnalysesAuditPreFamily AnalysesAuditPreFinite
  AnalysesAuditPreSolve AnalysesAuditSource.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore.
Import List.ListNotations.

Example pre_code_successor_carries : pre_positive_succ_body 3%positive = (4%positive, 4).
Proof.
  reflexivity.
Qed.

Example pre_code_zero_addition : pre_nadd_body 0%N 5%N = (5%N, 1).
Proof.
  reflexivity.
Qed.

Example pre_code_sublists_order :
    audit_pre_sublists [1; 2] = [[]; [2]; [1]; [1; 2]].
Proof.
  reflexivity.
Qed.

Example pre_code_counted_sublists :
    exact_value (@pre_sublists_counted unit nat [1; 2]) = [[]; [2]; [1]; [1; 2]].
Proof.
  reflexivity.
Qed.

Example pre_code_select_even_minimum :
    audit_pre_choose_best Nat.even (fun n => n) [3; 4; 2] = Some 2.
Proof.
  reflexivity.
Qed.

Example pre_code_select_rejects_all :
    audit_pre_choose_best Nat.even (fun n => n) [1; 3] = None.
Proof.
  reflexivity.
Qed.

Example pre_code_select_empty :
    audit_pre_choose_best Nat.even (fun n => n) [] = None.
Proof.
  reflexivity.
Qed.

Definition pre_code_reset_index :=
  exact_value (pre_reset_index_source nat_encoding (fun _ => 0) [(1, 2)]).

Example pre_code_reset_index_finds_edge :
    exact_value (pre_reset_out_source nat_encoding (fun _ => 0) pre_code_reset_index 1) = [(1, 2)].
Proof.
  reflexivity.
Qed.

Example pre_code_reset_index_missing_key :
    exact_value (pre_reset_out_source nat_encoding (fun _ => 0) pre_code_reset_index 2) = [].
Proof.
  reflexivity.
Qed.

Definition pre_code_graph : Graph.t nat nat :=
  Graph.Make [0] [0] (fun _ => [1]) (fun _ => 0) (fun _ => 0).

Example pre_code_graph_out_receipt :
    pre_view_out pre_code_graph 0 = ([1], [PreViewOut 0 [1]]).
Proof.
  reflexivity.
Qed.
