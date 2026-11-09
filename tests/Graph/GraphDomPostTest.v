(** * Reverse-parent backend fixtures

    Both finishers run through the actual charged prepared reversal.
    For example, separate exits remove the former diamond join's strict post-dominator.
    Builds on: GraphDomPost and GraphFixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphCheckDom GraphDomSpec
  GraphDomBackend GraphDomPost.
Import List.ListNotations.
Open Scope positive_scope.

Definition diamond_expected := Fixtures.parents [(1, 4); (2, 4); (3, 4)].

Example diamond_post_backends :
  (DomPost.parents DomBackend.lt Fixtures.Diamond.prepared [4],
   DomPost.parents DomBackend.semi_nca Fixtures.Diamond.prepared [4]) =
    (diamond_expected, diamond_expected).
Proof.
  vm_compute. reflexivity.
Qed.

Definition two_exits := Fixtures.prepare [1]%nat [1; 2; 3; 4]%nat
  [(1, 2); (1, 3); (2, 4)]%nat.
Definition two_exits_expected := Fixtures.parents [(2, 4)].

Example two_exit_post_backends :
  (DomPost.parents DomBackend.lt two_exits [3; 4],
   DomPost.parents DomBackend.semi_nca two_exits [3; 4]) =
    (two_exits_expected, two_exits_expected).
Proof.
  vm_compute. reflexivity.
Qed.

Example two_exit_checked_candidates :
  (DomCheck.check (Prepared.reverse two_exits [3; 4])
     (DomPost.parents DomBackend.lt two_exits [3; 4]),
   DomCheck.check (Prepared.reverse two_exits [3; 4])
     (DomPost.parents DomBackend.semi_nca two_exits [3; 4])) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_and_unknown_exits :
  DomPost.parents DomBackend.lt Fixtures.Diamond.prepared [4; 9; 4] = diamond_expected.
Proof.
  vm_compute. reflexivity.
Qed.

Example reversal_exit_work_is_retained :
  Cost.ticks (Prepared.reverse_c Fixtures.Diamond.prepared [4; 9; 4]) = 22%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example full_two_exit_post_tree :
  let t := DomPost.post DomBackend.lt two_exits [3; 4] in
  (Dom.idom t,
   DomCheck.dominates_b t 4 2,
   DomCheck.dominates_b t 4 1,
   DomCheck.dominates_b t 3 1) = (two_exits_expected, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.
