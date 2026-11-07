(** * Generic term fixtures

    Terms support nested operand lists and pointwise assumptions.
    For example, assuming a leaf false meets its current reachable fact with false.
    Builds on: DomainsTerm and DomainsValueTest. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Domains Require Import DomainsValue DomainsTerm.
From Galois.Tests.Domains Require Import DomainsValueTest.
Import List.ListNotations.

Local Open Scope nat_scope.

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
  eval_term (fun (_ : unit) (_ : list unit) => None)
    (fun _ : nat => tt) (Node tt []) = None.
Proof. vm_compute. reflexivity. Qed.

Example leaf_visit_cost :
  Cost.ticks (abs_eval_c reach_values (fun _ : nat => Cost.ret true) (Leaf 0)) = 2%N.
Proof. vm_compute. reflexivity. Qed.

(** This computational fixture records update order and makes no value-law claim. *)
Definition trace_values (targets : list (list nat)) : ValueAbs.t (list nat) unit unit :=
  {| ValueAbs.lat := simple (fun _ _ => true) [] (fun xs _ => xs);
     ValueAbs.top := [];
     ValueAbs.op_c := fun _ _ => Cost.ret [];
     ValueAbs.back_c := fun _ _ _ => Cost.ret targets;
     ValueAbs.guard_c := fun _ xs => Cost.ret xs |}.

Definition trace_assume targets seed :=
  abs_assume (fun x y => Cost.ret (Nat.eqb x y)) (@CostList.app_c nat)
    (trace_values targets) (fun _ : nat => Cost.ret seed)
    (Node tt [Leaf 0; Leaf 0]) [] 0.

Example node_assumptions_thread_left_to_right :
  trace_assume [[1]; [2]] [] = [1; 2].
Proof. vm_compute. reflexivity. Qed.

Example node_assumptions_retain_earlier_environment :
  trace_assume [[1]; [2]] [9] = [9; 1; 2].
Proof. vm_compute. reflexivity. Qed.

Example reversed_node_targets_are_observable :
  trace_assume [[2]; [1]] [] = [2; 1].
Proof. vm_compute. reflexivity. Qed.

Definition charged_leaf :=
  abs_assume_c
    (fun x y => Cost.bind (Cost.tick 3%N) (fun _ => Cost.ret (Nat.eqb x y)))
    (fun a b => Cost.bind (Cost.tick 7%N) (fun _ => Cost.ret (a && b)))
    reach_values (fun _ : nat => Cost.bind (Cost.tick 5%N) (fun _ => Cost.ret true))
    (Leaf 0) true.

Example matching_leaf_charges_each_callback :
  Cost.ticks (Cost.bind charged_leaf (fun env => env 0)) = 19%N.
Proof. vm_compute. reflexivity. Qed.

Example other_leaf_still_charges_environment_callback :
  Cost.ticks (Cost.bind charged_leaf (fun env => env 1)) = 11%N.
Proof. vm_compute. reflexivity. Qed.
