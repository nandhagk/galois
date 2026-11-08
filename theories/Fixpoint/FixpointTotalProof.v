(** * Total engine numeric bounds

    Preparation and loop costs are derived from primitive duties on finite declared domains.
    For example, the fuel conversion retains its charged unary traversal even for empty systems.
    Builds on: FixpointTotalCost, FixpointTotalPotential and CostBound. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseMap.
From Galois.Lattice Require Import LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointIndexCost FixpointAnalysis
  FixpointTotalQueue FixpointTotalKernel FixpointTotalInvariant FixpointTotalPotential
  FixpointTotal FixpointTotalCost.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module TotalProof.

(** Setup retains index preparation, queue insertion, metadata traversal and fuel conversion. *)
Definition setup (b : TotalCost.Budget.t) (C D H : nat) : N :=
  SystemIndexCost.Budget.preparation (TotalCost.Budget.metadata b) C +
  N.of_nat C * TotalCost.Budget.enqueue b +
  N.of_nat C * (3 + SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b) +
    N.of_nat (SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b))) +
  N.of_nat D + N.of_nat (C + H * D).

(** The named total prefactor absorbs setup without discarding its primitive charges. *)
Definition total_k b C D H := setup b C D H + TotalCost.Budget.step b C.

(** Positive-fuel conversion pays one tick for each consumed unary successor. *)
Theorem positive_cost n :
  Cost.ticks (TotalKernel.positive_c n) = N.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [TotalKernel.positive_c]; autorewrite with galois_cost.
  rewrite IH, Nat2N.inj_succ; lia.
Qed.

Section Bounds.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a) (b : TotalCost.Budget.t) (HB : TotalCost.model a b).

Let EX := Analysis.key_enc a.
Let S := Analysis.system a.
Let SS := Analysis.static a.
Let cs := System.constraints S.
Let rows := length cs.
Let D := length (TotalKernel.read_keys a).
Let H := bound (Terminates.hgt HT).
Let ix := index_system EX S SS.
Let HI := index_system_laws EX (Analysis.key_laws HL) S SS.

(** Read construction pays each original metadata invocation and every copied read occurrence. *)
Theorem read_keys_cost :
  Cost.ticks (TotalKernel.read_keys_c a) <= N.of_nat rows *
    (2 + SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b) +
      N.of_nat (SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b))).
Proof.
  unfold TotalKernel.read_keys_c.
  pose proof (ticks_fold_right_c_potential
    (fun c xs => Cost.step ;; let* reads := System.deps_c SS c in app_c reads xs)
    (fun _ => True) (fun _ => 0)
    (1 + SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b) +
      N.of_nat (SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b)))
    cs []) as Hfold.
  assert (Hcallback : forall c xs, In c cs -> True ->
    True /\
    Cost.ticks (Cost.step ;; let* reads := System.deps_c SS c in app_c reads xs) + 0 <=
      (1 + SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b) +
        N.of_nat (SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b))) + 0).
  { intros c xs Hc _; split; [exact I|].
    destruct (SystemIndexCost.callback_budget (TotalCost.metadata_model HB) c Hc)
      as [_ [Hdeps _]].
    destruct (SystemIndexCost.count_budget (TotalCost.metadata_model HB) c Hc) as [Hcount _].
    rewrite !Cost.ticks_bind, Cost.ticks_step, ticks_app_c.
    change (Cost.ticks (System.deps_c SS c) <=
      SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b)) in Hdeps.
    change (length (deps SS c) <=
      SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b))%nat in Hcount.
    fold (deps SS c); nia. }
  destruct (Hfold Hcallback I) as [_ Hcost].
  change (Cost.ticks
    (fold_right_c
      (fun (c : C) xs => Cost.step ;; let* reads := System.deps_c SS c in app_c reads xs)
      [] cs) <=
    N.of_nat rows *
      (2 + SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b) +
        N.of_nat (SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b)))).
  unfold rows; nia.
Qed.

(** Fuel setup retains row and incidence counting and the numeric conversion cost. *)
Theorem fuel_cost :
  Cost.ticks (TotalKernel.fuel_c a HT) <=
    N.of_nat rows *
      (3 + SystemIndexCost.Budget.deps_ticks (TotalCost.Budget.metadata b) +
        N.of_nat (SystemIndexCost.Budget.read_count (TotalCost.Budget.metadata b))) +
      N.of_nat D + N.of_nat (rows + H * D).
Proof.
  unfold TotalKernel.fuel_c.
  rewrite !Cost.ticks_bind, !ticks_length_c, !value_length_c, positive_cost.
  fold cs rows (TotalKernel.read_keys a) D H.
  pose proof read_keys_cost; unfold rows, cs, S in *; nia.
Qed.

(** Numeric initial queue insertion charges every original row occurrence. *)
Theorem initial_cost :
  Cost.ticks (TotalKernel.initial_c a) <= N.of_nat rows * TotalCost.Budget.enqueue b.
Proof.
  unfold TotalKernel.initial_c; rewrite Cost.ticks_bind, Cost.ticks_ret.
  pose proof (TotalCost.enqueue_cost a b HB cs TotalQueue.empty (fun _ Hc => Hc)).
  unfold rows, cs, S in *; lia.
Qed.

(** The decreasing incidence potential bounds the prepared loop independently of excess fuel. *)
Theorem loop_cost fuel :
  Cost.ticks (TotalKernel.loop_c a ix fuel) <=
    N.of_nat rows * TotalCost.Budget.enqueue b +
    (TotalCost.Budget.step b rows + 2) * (N.of_nat (rows + H * D) + 1) +
    2 * N.pos (Pos.size fuel).
Proof.
  assert (Hstep : forall s, TotalInvariant.invariant a HT s ->
    Cost.ticks (TotalKernel.step_c a ix s) <= TotalCost.Budget.step b rows /\
    match Cost.value (TotalKernel.step_c a ix s) with
    | inl t => TotalInvariant.invariant a HT t /\
      N.of_nat (TotalPotential.potential a HT t) < N.of_nat (TotalPotential.potential a HT s)
    | inr _ => True
    end).
  { intros s Hs; split.
    - exact (TotalCost.step_cost a HL b HB HT s Hs).
    - destruct (Cost.value (TotalKernel.step_c a ix s)) as [t|m] eqn:Hnext; [|exact I].
      split.
      + exact (TotalInvariant.step_preserved a HL HT ix HI s t Hs Hnext).
      + pose proof (TotalPotential.step_decreases a HL HT s t Hs Hnext); lia. }
  pose proof (iterate_cost (TotalKernel.step_c a ix) (TotalInvariant.invariant a HT)
    (fun s => N.of_nat (TotalPotential.potential a HT s)) (TotalCost.Budget.step b rows)
    fuel (TotalKernel.initial a) Hstep (TotalInvariant.initial_invariant a HL HT)) as Hloop.
  pose proof (TotalPotential.initial_bound a HT) as Hbound.
  pose proof initial_cost as Hinitial.
  unfold TotalKernel.loop_c; rewrite Cost.ticks_bind.
  fold (TotalKernel.initial a).
  assert (HboundN : N.of_nat (TotalPotential.potential a HT (TotalKernel.initial a)) <=
    N.of_nat (rows + H * D)).
  { change (TotalPotential.potential a HT (TotalKernel.initial a) <= rows + H * D)%nat
      in Hbound.
    lia. }
  cbn beta in Hloop.
  nia.
Qed.

(** Primitive budgets imply a closed numeric total-run bound including preparation. *)
Theorem total_cost_separate :
  Cost.ticks (Total.run_c a HT) <= setup b rows D H +
    (TotalCost.Budget.step b rows + 2) * (N.of_nat (rows + H * D) + 1) +
    2 * N.pos (Pos.size (TotalKernel.fuel a HT)).
Proof.
  pose proof (SystemIndexCost.index_system_cost EX (Analysis.key_laws HL) S SS
    (TotalCost.Budget.metadata b) (TotalCost.metadata_model HB)) as Hindex.
  pose proof fuel_cost as Hfuel.
  pose proof (loop_cost (TotalKernel.fuel a HT)) as Hloop.
  unfold Total.run_c, TotalKernel.run_c; rewrite !Cost.ticks_bind, Cost.ticks_ret.
  fold (TotalKernel.fuel a HT).
  change (Cost.ticks (index_system_c EX S SS) +
    (Cost.ticks (TotalKernel.fuel_c a HT) +
      (Cost.ticks (TotalKernel.loop_c a ix (TotalKernel.fuel a HT)) + 0)) <=
    setup b rows D H +
    (TotalCost.Budget.step b rows + 2) * (N.of_nat (rows + H * D) + 1) +
    2 * N.pos (Pos.size (TotalKernel.fuel a HT))).
  unfold setup, rows, cs in *; nia.
Qed.

(** Absorbing setup gives the card's named-prefactor form without dropping its charges. *)
Theorem total_cost :
  Cost.ticks (Total.run_c a HT) <=
    (total_k b rows D H + 2) * (N.of_nat (rows + H * D) + 1) +
    2 * N.pos (Pos.size (TotalKernel.fuel a HT)).
Proof.
  pose proof total_cost_separate; unfold total_k; nia.
Qed.

End Bounds.

(** Families with primitive budgets inherit a big-O bound in numeric setup and incidence work. *)
Theorem total_bigO {T X C A} (a : T -> Analysis.t X C A)
    (HL : forall t, Analysis.laws (a t)) (HT : forall t, Terminates.t (a t))
    (b : T -> TotalCost.Budget.t) (HB : forall t, TotalCost.model (a t) (b t)) :
  bigO (fun t =>
    let rows := length (System.constraints (Analysis.system (a t))) in
    let D := length (TotalKernel.read_keys (a t)) in
    let H := bound (Terminates.hgt (HT t)) in
    setup (b t) rows D H +
    (TotalCost.Budget.step (b t) rows + 2) * (N.of_nat (rows + H * D) + 1) +
    2 * N.pos (Pos.size (TotalKernel.fuel (a t) (HT t))))
    (fun t => Cost.ticks (Total.run_c (a t) (HT t))).
Proof.
  exists 1; intro t; pose proof (total_cost_separate (a t) (HL t) (HT t) (b t) (HB t)).
  cbn zeta; nia.
Qed.

End TotalProof.
Import TotalProof.
