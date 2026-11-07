(** * Costs of known-bit recursive algorithms

    Multiplication is linear in the numeric width and expansion visits each mask digit once.
    For example, intersecting two multipliers retains the complete cost of each driver.
    Builds on: DomainsTnumMul, DomainsTnumExpand, DomainsTnumBack and CostLoop. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostLoop CostBound.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsTnum DomainsTnumMul DomainsTnumExpand DomainsTnumBack.
Import Cost.Notations.

Local Open Scope N_scope.

Definition tnum_mul_tick_k : N := 3.

Lemma tnum_unit_driver_cost : forall S R (step : S -> Cost.t (S + R)),
  (forall s, Cost.ticks (step s) = 1) ->
  forall fuel s, Cost.ticks (iterate step fuel s) <= tnum_mul_tick_k * N.pos fuel.
Proof.
  intros S R step Hstep fuel s.
  pose proof (iterate_cost_amortised step (fun _ => True) (fun _ => 0) 1) as Hbound.
  assert (Hcallback : forall s, True ->
    (match Cost.value (step s) with inl _ => True | inr _ => True end) /\
    Cost.ticks (step s) + result_potential (fun _ => 0) (Cost.value (step s)) <= 1 + 0).
  { intros x _. destruct (Cost.value (step x)); cbn [result_potential]; rewrite Hstep.
    all: split; [exact I|lia]. }
  specialize (Hbound Hcallback fuel s I).
  destruct Hbound as [_ Hbound]. destruct (Cost.value (iterate step fuel s));
    cbn [result_potential] in Hbound; unfold tnum_mul_tick_k; lia.
Qed.

(** Every staged multiplication pays at most three ticks per width bit, including driver work. *)
Theorem tnum_mul_stages_cost : forall w a b,
  Cost.ticks (tnum_mul_stages_c w a b) <= tnum_mul_tick_k * N.pos w.
Proof.
  intros w a b. unfold tnum_mul_stages_c.
  destruct (tnum_empty w a || tnum_empty w b); [cbn; lia|].
  autorewrite with galois_cost. rewrite N.add_0_r.
  apply tnum_unit_driver_cost. intros [i r]. reflexivity.
Qed.

(** Early stopping never increases the accumulator driver's fuel-linear cost bound. *)
Theorem tnum_mul_acc_cost : forall w a b,
  Cost.ticks (tnum_mul_acc_c w a b) <= tnum_mul_tick_k * N.pos w.
Proof.
  intros w a b. unfold tnum_mul_acc_c.
  destruct (tnum_empty w a || tnum_empty w b); [cbn; lia|].
  autorewrite with galois_cost. rewrite N.add_0_r.
  apply tnum_unit_driver_cost. intros [i r].
  unfold tnum_mul_acc_step_c. autorewrite with galois_cost.
  destruct (tnum_mul_acc_done w b i); reflexivity.
Qed.

(** Every selected multiplier is bounded uniformly, including both complete intersected drivers. *)
Theorem tnum_mul_with_cost : forall choice w a b,
  Cost.ticks (tnum_mul_with_c choice w a b) <= 2 * tnum_mul_tick_k * N.pos w.
Proof.
  intros choice w a b.
  assert (Hwidth : 0 < N.pos w) by reflexivity.
  destruct choice.
  - cbn [tnum_mul_with_c]. autorewrite with galois_cost. unfold tnum_mul_tick_k. lia.
  - eapply N.le_trans; [apply tnum_mul_stages_cost|]. nia.
  - eapply N.le_trans; [apply tnum_mul_acc_cost|]. nia.
  - cbn [tnum_mul_with_c]. autorewrite with galois_cost.
    pose proof (tnum_mul_stages_cost w a b). pose proof (tnum_mul_acc_cost w a b). nia.
Qed.

(** The selected multiplication cost is big-O of the numeric word width. *)
Theorem tnum_mul_with_bigO : forall choice a b,
  bigO (fun w => N.pos w) (fun w => Cost.ticks (tnum_mul_with_c choice w a b)).
Proof.
  intros choice a b. exists (2 * tnum_mul_tick_k). intro w.
  pose proof (tnum_mul_with_cost choice w a b). nia.
Qed.

(** Factored expansion visits precisely the binary mask's digits. *)
Theorem tnum_expand_cost : forall o w p d r,
  Cost.ticks (tnum_expand_c o w p d r) = N.pos (Pos.size p).
Proof.
  intros o w p. induction p as [p IH|p IH|]; intros d r;
    cbn [tnum_expand_c Pos.size]; autorewrite with galois_cost;
    rewrite ?IH; try lia.
  all: change (N.pos (Pos.succ (Pos.size p))) with (1 + N.pos (Pos.size p)); lia.
Qed.

Definition tnum_mask_digits (u : Z) : N :=
  match u with Zpos p => N.pos (Pos.size p) | _ => 0 end.

(** Empty or negative raw expansion masks take no recursive steps. *)
Theorem tnum_expand_mask_cost : forall o w u r,
  Cost.ticks (tnum_expand_mask_c o w u r) = tnum_mask_digits u.
Proof.
  intros o w [|p|p] r; [reflexivity|apply tnum_expand_cost|reflexivity].
Qed.

Definition tnum_variable_digits (o : op) (w : width) (b : tnum) : N :=
  let u := tnum_mask w b in
  tnum_mask_digits (if tnum_rotation o then u else u mod 2 ^ tnum_shift_cutoff w)%Z.

(** A variable transfer charges every digit of the actual selected amount-mask expansion. *)
Theorem tnum_variable_raw_cost : forall o w a b,
  Cost.ticks (tnum_variable_raw_c o w a b) = tnum_variable_digits o w b.
Proof.
  intros o w a b. unfold tnum_variable_raw_c, tnum_variable_digits.
  destruct (tnum_rotation o); autorewrite with galois_cost;
    rewrite ?N.add_0_r; apply tnum_expand_mask_cost.
Qed.

(** The emptiness fast path can only decrease a variable transfer's recursive cost. *)
Theorem tnum_variable_cost : forall o w a b,
  Cost.ticks (tnum_variable_c o w a b) <= tnum_variable_digits o w b.
Proof.
  intros o w a b. unfold tnum_variable_c.
  destruct (tnum_empty w a || tnum_empty w b); [cbn; lia|].
  rewrite tnum_variable_raw_cost. lia.
Qed.

(** Backward variable transfer retains both inverse expansions, one for each result mask. *)
Theorem tnum_back_variable_shift_cost : forall o w b q,
  Cost.ticks (tnum_back_variable_shift_c o w b q) =
    2 * tnum_variable_digits (tnum_inverse_shift o) w b.
Proof.
  intros o w b q. unfold tnum_back_variable_shift_c, tnum_project_variable_c.
  autorewrite with galois_cost. rewrite !tnum_variable_raw_cost. lia.
Qed.
