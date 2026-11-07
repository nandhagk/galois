(** * Bounded walk fixtures

    These examples distinguish a stop, a terminal parent and fuel exhaustion.
    For example, a cyclic callback returns a bounded repeated-node prefix.
    Builds on: GraphWalk and GraphFixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphWalk GraphFixtures GraphCheckDom.
Import List.ListNotations.

Definition parent_c v :=
  Cost.ret (if Pos.eqb v 1 then None else Some (Pos.pred v)).

Example stopped_prefix :
  Walk.until parent_c (fun v => Cost.ret (Pos.eqb v 2)) 5 4 = [4; 3]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example terminal_prefix :
  Walk.until parent_c (fun _ => Cost.ret false) 5 4 = [4; 3; 2; 1]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example exhausted_cycle :
  Walk.until (fun v => Cost.ret (Some v)) (fun _ => Cost.ret false) 3 1 =
    [1; 1; 1]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example stop_before_visit :
  Walk.until parent_c (fun _ => Cost.ret true) 1 1 = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example retained_callback_cost :
  Cost.ticks (Walk.until_c
    (fun _ => Cost.lift (fun _ => 7%N) (fun _ => None) tt)
    (fun _ => Cost.lift (fun _ => 5%N) (fun _ => false) tt) 1 1) = 17%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_tree_checked :
  DomCheck.check Fixtures.Line.prepared Fixtures.Line.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_parent_walk :
  Walk.until (Walk.up_c Fixtures.Line.tree) (fun _ => Cost.ret false) 5 4 =
    [4; 3; 2; 1]%positive.
Proof.
  vm_compute. reflexivity.
Qed.
