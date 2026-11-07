(** * Generic term fixtures

    Terms support nested operand lists and pointwise assumptions.
    For example, assuming a leaf false meets its current reachable fact with false.
    Builds on: DomainsTerm and DomainsValueTest. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Domains Require Import DomainsValue DomainsTerm.
From Galois.Tests.Domains Require Import DomainsValueTest.
Import List.ListNotations.

Example nested_term_evaluation :
  abs_eval reach_values (fun _ : nat => true)
    (Node tt [Leaf 0; Node tt [Leaf 1]]) = true.
Proof. vm_compute. reflexivity. Qed.

Example leaf_assumption_rejects :
  abs_assume (fun x y => Cost.ret (Nat.eqb x y)) (fun a b => Cost.ret (a && b))
    reach_values (fun _ : nat => Cost.ret true) (Leaf 0) false 0 = false.
Proof. vm_compute. reflexivity. Qed.

Example leaf_assumption_keeps_other :
  abs_assume (fun x y => Cost.ret (Nat.eqb x y)) (fun a b => Cost.ret (a && b))
    reach_values (fun _ : nat => Cost.ret true) (Leaf 0) false 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example empty_node_evaluation :
  eval_term (fun (_ : unit) (_ : list unit) => None) (fun _ : nat => tt) (Leaf 0) = Some tt.
Proof. vm_compute. reflexivity. Qed.

Example leaf_visit_cost :
  Cost.ticks (abs_eval_c reach_values (fun _ : nat => Cost.ret true) (Leaf 0)) = 2%N.
Proof. vm_compute. reflexivity. Qed.
