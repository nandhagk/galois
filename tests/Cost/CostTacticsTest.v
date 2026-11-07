(** * Cost tactic clients

    Client proofs exercise normalization, bound search and loop obligations.
    For example, normalization leaves a symbolic inequality for [lia].
    Builds on: CostTactics. *)

From Stdlib Require Import NArith Lia List.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound CostTactics.
Import Cost.Notations List.ListNotations.
Open Scope N_scope.

Example simplify_ret : Cost.ticks (Cost.ret true) = 0.
Proof.
  cost_simpl. reflexivity.
Qed.

Example simplify_bind :
  Cost.ticks (Cost.tick 2 ;; Cost.tick 3 ;; Cost.ret true) = 5.
Proof.
  cost_simpl. reflexivity.
Qed.

Example simplify_list : Cost.value (map_c (fun n : nat => Cost.ret (S n)) [0%nat]) = [1%nat].
Proof.
  cost_simpl. reflexivity.
Qed.

Example simplify_leaves_arithmetic (n : N) :
  Cost.ticks (Cost.tick n ;; Cost.tick 1) <= n + 3.
Proof.
  cost_simpl.
  Fail solve [reflexivity].
  lia.
Qed.

Example solve_reflexive : bigO (fun n : N => n) (fun n => n).
Proof.
  bigO_solver.
Qed.

Example solve_sum : bigO (fun n : N => n + n) (fun n => n + n).
Proof.
  bigO_solver.
Qed.

Example solve_product :
  bigO (fun n : N => n + n + n * n) (fun n => n * n).
Proof.
  bigO_solver.
Qed.

Example solve_composed :
  bigO (fun n : N => (n + 1) + (n + 1) + (n + 1) * (n + 1))
    (fun n => (n + 1) * (n + 1)).
Proof.
  bigO_solver.
Qed.

Example solve_assumed_sum {X} (f g h k : X -> N) :
  bigO f g -> bigO h k ->
  bigO (fun x => f x + h x) (fun x => g x + k x).
Proof.
  intros Hfirst Hsecond. bigO_solver.
Qed.

Example solve_assumed_comp {X Y} (f g : Y -> N) (h : X -> Y) :
  bigO f g -> bigO (fun x => f (h x)) (fun x => g (h x)).
Proof.
  intro Hbound. bigO_solver.
Qed.

Definition stop_c (n : nat) : Cost.t (nat + nat) := Cost.ret (inr n).

Example loop_one :
  Cost.ticks (iterate stop_c 1 0%nat) <= 2 * (0 + 1) + 2 * N.pos (Pos.size 1).
Proof.
  iterate_invariant (fun _ : nat => True) (fun _ : nat => 0) 0.
  - intros s _. split; [reflexivity | constructor].
  - constructor.
Qed.

Example loop_even :
  Cost.ticks (iterate stop_c 8 4%nat) <= 2 * (0 + 1) + 2 * N.pos (Pos.size 8).
Proof.
  iterate_invariant (fun _ : nat => True) (fun _ : nat => 0) 0.
  - intros s _. split; [reflexivity | constructor].
  - constructor.
Qed.

Example loop_odd p n :
  Cost.ticks (iterate stop_c p n) <= 2 * (0 + 1) + 2 * N.pos (Pos.size p).
Proof.
  iterate_invariant (fun _ : nat => True) (fun _ : nat => 0) 0.
  - intros s _. split; [reflexivity | constructor].
  - constructor.
Qed.
