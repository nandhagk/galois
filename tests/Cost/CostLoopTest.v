(** * Loop observations

    These examples distinguish callback charges, descent charges and stopping.
    For example, an exhausted one-step run returns its continuation state.
    Builds on: CostLoop. *)

From Stdlib Require Import NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
Import Cost.Notations.
Open Scope N_scope.

Definition countdown_c (n : nat) : Cost.t (nat + nat) :=
  Cost.tick 3 ;;
  match n with
  | O => Cost.ret (inr 42%nat)
  | S n' => Cost.ret (inl n')
  end.

Example one_exhausted :
  (Cost.value (iterate countdown_c 1 2%nat), Cost.ticks (iterate countdown_c 1 2%nat)) =
    (inl 1%nat, 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example one_stopped :
  (Cost.value (iterate countdown_c 1 0%nat), Cost.ticks (iterate countdown_c 1 0%nat)) =
    (inr 42%nat, 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example even_exhausted :
  (Cost.value (iterate countdown_c 4 9%nat), Cost.ticks (iterate countdown_c 4 9%nat)) =
    (inl 5%nat, 19).
Proof.
  vm_compute. reflexivity.
Qed.

Example odd_exhausted :
  (Cost.value (iterate countdown_c 3 9%nat), Cost.ticks (iterate countdown_c 3 9%nat)) =
    (inl 6%nat, 13).
Proof.
  vm_compute. reflexivity.
Qed.

Example even_stopped :
  (Cost.value (iterate countdown_c 8 0%nat), Cost.ticks (iterate countdown_c 8 0%nat)) =
    (inr 42%nat, 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example odd_stopped :
  (Cost.value (iterate countdown_c 9 0%nat), Cost.ticks (iterate countdown_c 9 0%nat)) =
    (inr 42%nat, 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example countdown_bound p n :
  Cost.ticks (iterate countdown_c p n) <=
    5 * (N.of_nat n + 1) + 2 * N.pos (Pos.size p).
Proof.
  apply (iterate_cost countdown_c (fun _ => True) N.of_nat 3).
  - intros s _. destruct s as [|s']; cbn [countdown_c]; autorewrite with galois_cost.
    + split; [reflexivity | constructor].
    + split; [reflexivity |]. split; [constructor | rewrite Nat2N.inj_succ; lia].
  - constructor.
Qed.

Definition stationary_c (n : nat) : Cost.t (nat + unit) := Cost.step ;; Cost.ret (inl n).

Example amortised_without_decrease :
  Cost.ticks (iterate stationary_c 4 0%nat) = 11.
Proof.
  vm_compute. reflexivity.
Qed.

Example stationary_amortised p n :
  Cost.ticks (iterate stationary_c p n) + 1 <= 3 * N.pos p.
Proof.
  pose proof (iterate_cost_amortised stationary_c (fun _ => True) (fun _ => 0) 1)
    as Hcredit.
  assert (Hstep : forall n, True ->
    (match Cost.value (stationary_c n) with inl _ => True | inr _ => True end) /\
    Cost.ticks (stationary_c n) +
      result_potential (fun _ => 0) (Cost.value (stationary_c n)) <= 1 + 0).
  { intros s _. split; [constructor | change (1 <= 1); lia]. }
  destruct (Hcredit Hstep p n I) as [_ Hcost].
  destruct (Cost.value (iterate stationary_c p n)); cbn [result_potential] in Hcost; lia.
Qed.

Definition wf_counter_F (n : nat)
    (rec : forall y, (y < n)%nat -> Cost.t N) : Cost.t N :=
  Cost.step ;;
  (match n as m return (forall y, (y < m)%nat -> Cost.t N) -> Cost.t N with
   | O => fun _ => Cost.ret 0
   | S n' => fun call => Cost.map N.succ (call n' (Nat.lt_succ_diag_r n'))
   end) rec.

Lemma wf_counter_ext n f g :
  (forall y H, f y H = g y H) -> wf_counter_F n f = wf_counter_F n g.
Proof.
  intro Hequal. unfold wf_counter_F. destruct n as [|n]; cbn beta iota zeta.
  - reflexivity.
  - rewrite (Hequal n (Nat.lt_succ_diag_r n)). reflexivity.
Qed.

Example wf_counter_cost n :
  Cost.ticks (fix_wf (fun n => n) wf_counter_F n) <= N.of_nat (S n).
Proof.
  apply (fix_wf_cost (fun n => n) wf_counter_F (fun x => N.of_nat (S x)));
    [exact wf_counter_ext |].
  intros x rec Hrec. unfold wf_counter_F. destruct x as [|x]; cbn beta iota zeta;
    autorewrite with galois_cost.
  - cbn. lia.
  - specialize (Hrec x (Nat.lt_succ_diag_r x)).
    rewrite Nat2N.inj_succ. nia.
Qed.

Example wf_counter_value n :
  Cost.value (fix_wf (fun n => n) wf_counter_F n) = N.of_nat n.
Proof.
  induction n as [|n IH]; rewrite (fix_wf_unfold _ _ wf_counter_ext);
    unfold wf_counter_F at 1; cbn beta iota zeta; autorewrite with galois_cost.
  - reflexivity.
  - rewrite IH, Nat2N.inj_succ. reflexivity.
Qed.

Definition residual_step_c (n : nat) : Cost.t (nat + nat) :=
  match n with
  | O => Cost.step ;; Cost.ret (inr 0%nat)
  | S next => Cost.tick 3 ;; Cost.ret (inl next)
  end.

Definition residual_credit n := 6 * N.of_nat n + 11.

(** The symbolic client retains nonzero terminal credit and the stronger exhausted refund. *)
Example residual_credit_client fuel n :
  match Cost.value (iterate residual_step_c fuel n) with
  | inl final =>
    (final <= n)%nat /\
    Cost.ticks (iterate residual_step_c fuel n) + residual_credit final + 1 <= residual_credit n
  | inr final =>
    (final <= n)%nat /\
    Cost.ticks (iterate residual_step_c fuel n) + residual_credit final <=
      residual_credit n + (1 + N.pos (Pos.size fuel))
  end.
Proof.
  apply (iterate_residual_credit residual_step_c (fun state => (state <= n)%nat)
    residual_credit fuel n).
  - intros [|state] Hbound; cbn [residual_step_c]; autorewrite with galois_cost.
    + split; [exact Hbound|unfold residual_credit; lia].
    + split; [lia|unfold residual_credit; rewrite Nat2N.inj_succ; nia].
  - apply Nat.le_refl.
Qed.

Example residual_credit_stopped :
  (match Cost.value (iterate residual_step_c 8 0%nat) with
  | inl final => (false, residual_credit final)
  | inr final => (true, residual_credit final)
  end) = (true, 11).
Proof.
  vm_compute. reflexivity.
Qed.

Example residual_credit_exhausted :
  (match Cost.value (iterate residual_step_c 1 2%nat) with
  | inl final => (false, residual_credit final)
  | inr final => (true, residual_credit final)
  end) = (false, 17).
Proof.
  vm_compute. reflexivity.
Qed.
