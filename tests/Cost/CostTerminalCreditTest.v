(** * Terminal-potential loop clients

    These clients retain a nonzero stopping-result potential through the public loop contract.
    For example, a three-tick callback returning potential seventeen fits terminal budget twenty.
    Builds on: CostLoop and CostMonad. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
Import Cost.Notations.

Definition terminal_step (_ : unit) : Cost.t (unit + N) :=
  Cost.tick 3 ;; Cost.ret (inr 17%N).

(** A symbolic client applies the public theorem without inspecting the binary driver. *)
Theorem terminal_credit_client fuel :
  (Cost.ticks (iterate terminal_step fuel tt) +
    match Cost.value (iterate terminal_step fuel tt) with
    | inl _ => 0
    | inr result => result
    end <= 20 + N.pos (Pos.size fuel))%N.
Proof.
  pose proof (iterate_terminal_credit terminal_step (fun _ => True) (fun _ => 0%N)
    (fun result => result) 20%N
    ltac:(intros state Hstate; change (3 + 17 <= 20 + 0)%N; lia) fuel tt I) as Hcredit.
  exact Hcredit.
Qed.

Example terminal_credit_nonzero_result :
  (Cost.ticks (iterate terminal_step 8%positive tt),
    Cost.value (iterate terminal_step 8%positive tt)) = (7%N, inr 17%N).
Proof.
  vm_compute. reflexivity.
Qed.
