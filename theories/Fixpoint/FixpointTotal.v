(** * Numerically fuelled total joining

    The total engine computes its fuel from finite read incidence and invariant-relative height.
    For example, cyclic finite-height joining runs directly under vm_compute.
    Builds on: FixpointTotalKernel, FixpointTotalInvariant and FixpointTotalPotential. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointLeast FixpointIndex
  FixpointAnalysis FixpointTotalQueue FixpointTotalKernel FixpointTotalInvariant
  FixpointTotalPotential.
Import Cost.Notations.

Module Total.

(** The fuel-free public computation prepares one index and uses the numeric height bound. *)
Definition run_c {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) :=
  TotalKernel.run_c a HT.

Definition run {X C A} (a : Analysis.t X C A) HT := Cost.value (run_c a HT).

(** Positive conversion returns its input successor. *)
Theorem positive_value n : Pos.to_nat (Cost.value (TotalKernel.positive_c n)) = S n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [TotalKernel.positive_c]; autorewrite with galois_cost.
  rewrite Pos2Nat.inj_succ; lia.
Qed.

(** Total fuel is one probe beyond rows plus height times duplicate-preserving read incidence. *)
Theorem fuel_value {X C A} (a : Analysis.t X C A) HT :
  Pos.to_nat (TotalKernel.fuel a HT) =
    S (length (System.constraints (Analysis.system a)) +
      bound (Terminates.hgt HT) * length (TotalKernel.read_keys a)).
Proof.
  unfold TotalKernel.fuel, TotalKernel.fuel_c; autorewrite with galois_cost.
  apply positive_value.
Qed.

Section Laws.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a).
Let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a).
Let HI := index_system_laws (Analysis.key_enc a) (Analysis.key_laws HL)
  (Analysis.system a) (Analysis.static a).
Let I := TotalInvariant.invariant a HT.
Let Phi := TotalPotential.potential a HT.

Local Lemma runs_continue n s last :
  runs (TotalKernel.step_c a ix) n s (inl last) -> I s ->
  I last /\ (Phi last + n <= Phi s)%nat.
Proof.
  intro Hrun; remember (inl last) as result eqn:Hresult.
  induction Hrun as [s|n s m Hstop|n s t result Hnext Hrun IH]; intro Hs.
  - injection Hresult as <-; split; [exact Hs|lia].
  - discriminate.
  - pose proof (TotalInvariant.step_preserved a HL HT ix HI s t Hs Hnext) as Ht.
    destruct (IH Hresult Ht) as [Hlast Hbound]; split; [exact Hlast|].
    pose proof (TotalPotential.step_decreases a HL HT s t Hs Hnext) as Hdecrease.
    change (Phi t < Phi s)%nat in Hdecrease; lia.
Qed.

(** The internally computed numeric fuel always reaches an actual stopping result under laws. *)
Theorem total_solved :
  exists m, Cost.value (TotalKernel.loop_c a ix (TotalKernel.fuel a HT)) = inr m.
Proof.
  unfold TotalKernel.loop_c; rewrite Cost.value_bind.
  fold (TotalKernel.initial a).
  pose proof (iterate_value (TotalKernel.step_c a ix) (TotalKernel.fuel a HT)
    (TotalKernel.initial a)) as Hrun.
  destruct (Cost.value (iterate (TotalKernel.step_c a ix) (TotalKernel.fuel a HT)
    (TotalKernel.initial a))) as [last|m] eqn:Hloop.
  - destruct (runs_continue _ _ last Hrun
      (TotalInvariant.initial_invariant a HL HT)) as [Hlast Hbound].
    pose proof (TotalPotential.initial_bound a HT) as Hinitial.
    pose proof (fuel_value a HT) as Hfuel; unfold Phi in Hbound; lia.
  - now exists m.
Qed.

Local Lemma runs_post n s m :
  runs (TotalKernel.step_c a ix) n s (inr m) -> I s ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intro Hrun; remember (inr m) as result eqn:Hresult.
  induction Hrun as [s|n s m' Hstop|n s t result Hnext Hrun IH]; intro Hs.
  - discriminate.
  - injection Hresult as <-; eapply TotalInvariant.step_post; eassumption.
  - apply IH; [exact Hresult|].
    eapply TotalInvariant.step_preserved; eassumption.
Qed.

(** The computed total assignment satisfies every original constraint and side contribution. *)
Theorem total_post :
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (run a HT)).
Proof.
  destruct total_solved as [m Hloop].
  unfold run, run_c; fold (TotalKernel.run a HT).
  rewrite TotalKernel.run_equation; fold ix; rewrite Hloop.
  apply (runs_post (Pos.to_nat (TotalKernel.fuel a HT)) (TotalKernel.initial a) m).
  - unfold TotalKernel.loop_c in Hloop; rewrite Cost.value_bind in Hloop.
    fold (TotalKernel.initial a) in Hloop; rewrite <- Hloop; apply iterate_value.
  - apply TotalInvariant.initial_invariant, HL.
Qed.

Local Lemma step_raise s t :
  I s -> TotalKernel.step a ix s = inl t ->
  raise (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (TotalKernel.current s) (TotalKernel.current t).
Proof.
  intros [Hg [Hq [Hlisted Hvalid]]] Hstep.
  rewrite TotalKernel.step_equation in Hstep.
  destruct (TotalQueue.pop (Analysis.row_enc a) (TotalKernel.queue s))
    as [[c rest]|] eqn:Hpop; [|discriminate].
  injection Hstep as <-; split; [exact (proj1 Hg)|]; exists c; split.
  - destruct (TotalQueue.pop_spec (Analysis.row_enc a) (Analysis.row_laws HL)
      _ _ c Hq Hpop) as [_ Hqueue].
    apply Hlisted; rewrite Hqueue; now left.
  - rewrite TotalInvariant.updates_current, raise_equation; reflexivity.
Qed.

Local Lemma runs_reached n s result :
  runs (TotalKernel.step_c a ix) n s result -> I s ->
  clos_refl_trans (assignment X A)
    (raise (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a))
    Map.empty (TotalKernel.current s) ->
  match result with
  | inl t => True
  | inr m => reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m)
  end.
Proof.
  intro Hrun; induction Hrun as [s|n s m Hstop|n s t result Hnext Hrun IH];
    intros Hs Hpath.
  - exact Logic.I.
  - fold (TotalKernel.step a ix s) in Hstop.
    rewrite TotalKernel.step_equation in Hstop.
    destruct (TotalQueue.pop (Analysis.row_enc a) (TotalKernel.queue s))
      as [[c rest]|]; [discriminate|].
    injection Hstop as <-; exists (TotalKernel.current s); split; [exact Hpath|reflexivity].
  - apply IH.
    + eapply TotalInvariant.step_preserved; eassumption.
    + eapply rt_trans; [exact Hpath|apply rt_step; apply step_raise; assumption].
Qed.

(** Total joining reaches its assignment from bottom through shared constraint raises. *)
Theorem total_reached :
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (run a HT)).
Proof.
  destruct total_solved as [m Hloop].
  assert (Hrun : runs (TotalKernel.step_c a ix) (Pos.to_nat (TotalKernel.fuel a HT))
    (TotalKernel.initial a) (inr m)).
  { unfold TotalKernel.loop_c in Hloop; rewrite Cost.value_bind in Hloop.
    rewrite <- Hloop; apply iterate_value. }
  pose proof (runs_reached _ _ _ Hrun (TotalInvariant.initial_invariant a HL HT)) as Hreached.
  assert (Hstart : clos_refl_trans (assignment X A)
    (raise (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a))
    Map.empty (TotalKernel.current (TotalKernel.initial a))).
  { rewrite TotalKernel.initial_equation; apply rt_refl. }
  specialize (Hreached Hstart).
  unfold run, run_c; fold (TotalKernel.run a HT).
  rewrite TotalKernel.run_equation; fold ix; rewrite Hloop; exact Hreached.
Qed.

(** The total assignment is least under the separate least-upper-bound and monotonicity laws. *)
Theorem total_least :
  lub_laws (Analysis.lat a) -> monotone_system (Analysis.lat a) (Analysis.system a) ->
  least_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (run a HT)).
Proof.
  intros Hlub Hmonotone; apply (reached_least _ (Analysis.key_laws HL)).
  - apply Analysis.lattice_law, HL.
  - exact Hlub.
  - exact Hmonotone.
  - exact total_reached.
  - exact total_post.
Qed.

End Laws.

(** The certified map computation adds no proof-driven recursion. *)
Definition solve_c {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (HT : Terminates.t a) :
    Cost.t {s : X -> A | post_solution (Analysis.lat a) (Analysis.system a) s} :=
  let result := run_c a HT in
  Cost.map (fun _ => exist _
    (lookup (Analysis.key_enc a) (Analysis.lat a) (Cost.value result))
    (total_post a HL HT)) result.

Definition solve {X C A} (a : Analysis.t X C A) HL HT := Cost.value (solve_c a HL HT).

End Total.
Import Total.
