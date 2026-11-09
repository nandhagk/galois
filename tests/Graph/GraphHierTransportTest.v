(** * Arbitrary-scope child transport clients

    Runtime body restriction and specified header deletion agree on raw blocked tables.
    For example, storing a key under a colliding encoding does not require a scope invariant.
    Builds on: GraphHierTransport. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphVisitor GraphHierSpec GraphHier GraphHierTransport.
Import List.ListNotations.
Open Scope positive_scope.

Definition collision_encoding : encoding positive := of_pure (fun _ => 1).
Definition raw_scope :=
  Scope.Make (FinSet.add collision_encoding 2 FinSet.empty)
    (Some (FinSet.of_list positive_encoding [1; 2; 3])).

Example raw_child_transport_client v :
  Scope.admits (HierRun.child_scope raw_scope 1 [2; 3]) v =
    Scope.admits (Hier.remove_header raw_scope 1 [1; 3; 2]) v.
Proof.
  apply (HierTransport.child_admits raw_scope 1 [2; 3] [3; 2] v).
  intro x. cbn [In]. intuition congruence.
Qed.

Example raw_child_header_rejected :
  Scope.admits (HierRun.child_scope raw_scope 1 [2; 3]) 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.
