(** * Depth-first discovery credits

    Finite adjacency credits pay for expansion and pending probes separately.
    For example, a repeated incidence pays for another probe without expanding its vertex again.
    Builds on: FixpointLocalDiscover, CostLoop and public finite-set equations. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Fixpoint Require Import FixpointLocalDiscover.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module LocalCredit.

Local Lemma fuel_nat_N p : N.of_nat (Pos.to_nat p) = N.pos p.
Proof.
  induction p as [p IH|p IH|].
  - rewrite Pos2Nat.inj_xI, Nat2N.inj_succ, Nat2N.inj_mul, IH; reflexivity.
  - rewrite Pos2Nat.inj_xO, Nat2N.inj_mul, IH; reflexivity.
  - reflexivity.
Qed.

Fixpoint sum {V} (f : V -> N) (xs : list V) : N :=
  match xs with
  | [] => 0
  | v :: rest => f v + sum f rest
  end.

Local Lemma sum_le {V} f g (xs : list V) :
  (forall v, In v xs -> f v <= g v) -> sum f xs <= sum g xs.
Proof.
  intro Hle; induction xs as [|v xs IH]; cbn [sum]; [lia|].
  specialize (IH (fun x Hx => Hle x (or_intror Hx))).
  specialize (Hle v (or_introl eq_refl)); lia.
Qed.

Local Lemma sum_credit {V} f g (xs : list V) d :
  (forall v, In v xs -> f v <= g v) ->
  (exists v, In v xs /\ f v + d <= g v) -> sum f xs + d <= sum g xs.
Proof.
  intros Hle [v [Hv Hcredit]]; induction xs as [|x xs IH]; [contradiction|].
  cbn [sum]; destruct Hv as [<-|Hv].
  - pose proof (sum_le f g xs (fun y Hy => Hle y (or_intror Hy))); lia.
  - specialize (IH (fun y Hy => Hle y (or_intror Hy)) Hv).
    specialize (Hle x (or_introl eq_refl)); lia.
Qed.

Local Lemma sum_ext {V} f g (xs : list V) :
  (forall v, f v = g v) -> sum f xs = sum g xs.
Proof.
  intro Heq; induction xs as [|v xs IH]; cbn [sum]; [reflexivity|].
  rewrite Heq, IH; reflexivity.
Qed.

Local Lemma sum_partition {V} (p : V -> bool) f xs :
  sum (fun v => if p v then f v else 0) xs +
    sum (fun v => if p v then 0 else f v) xs = sum f xs.
Proof.
  induction xs as [|v xs IH]; cbn [sum]; [reflexivity|].
  destruct (p v); lia.
Qed.

Section Credit.
Context {V : Type} (EV : encoding V) (HE : encoding_laws EV)
  (next : V -> Cost.t (list V)) (U roots : list V).
Hypothesis Hroots : incl roots U.
Hypothesis Hclosed : forall v, In v U -> incl (Cost.value (next v)) U.

Definition weight v := 1 + N.of_nat (length (Cost.value (next v))).
Definition unused marked := sum (fun v => if FinSet.mem EV v marked then 0 else weight v) U.
Definition visited_work marked := sum (fun v => if FinSet.mem EV v marked then weight v else 0) U.

(** Visited and unused adjacency credits partition the finite domain's original credit. *)
Theorem partition marked : visited_work marked + unused marked = sum weight U.
Proof.
  unfold visited_work, unused; apply sum_partition.
Qed.

Local Lemma mark_credit marked v :
  FinSet.wf EV marked -> In v U -> FinSet.mem EV v marked = false ->
  unused (FinSet.add EV v marked) + weight v <= unused marked.
Proof.
  intros Hwf Hv Hfresh; unfold unused.
  apply sum_credit.
  - intros x Hx; rewrite FinSet.mem_add by exact Hwf.
    destruct (eqb EV x v), (FinSet.mem EV x marked); cbn [orb]; lia.
  - exists v; split; [exact Hv|].
    rewrite FinSet.mem_add by exact Hwf; rewrite eqb_refl, Hfresh; cbn [orb]; lia.
Qed.

Definition invariant (s : LocalDiscover.state V) :=
  FinSet.wf EV (LocalDiscover.visited s) /\ incl (LocalDiscover.pending s) U.

Local Lemma preserved s t :
  invariant s -> LocalDiscover.step EV next s = inl t -> invariant t.
Proof.
  intros [Hwf Htodo] Hstep; rewrite LocalDiscover.step_equation in Hstep.
  destruct (LocalDiscover.pending s) as [|v rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem EV v (LocalDiscover.visited s)) eqn:Hseen;
    apply (f_equal (fun o => match o with inl t => t | inr _ => s end)) in Hstep;
    cbn beta iota in Hstep; subst t; cbn [LocalDiscover.visited LocalDiscover.pending].
  - split; [exact Hwf|]; intros x Hx; apply Htodo; now right.
  - split; [apply FinSet.wf_add, Hwf|].
    intros x Hx; apply in_app_or in Hx as [Hx|Hx].
    + apply (Hclosed v (Htodo v (or_introl eq_refl)) x Hx).
    + apply Htodo; now right.
Qed.

(** Counting pending probes and unused incidence strictly bounds discovery continuations. *)
Definition count_potential (s : LocalDiscover.state V) :=
  N.of_nat (length (LocalDiscover.pending s)) + unused (LocalDiscover.visited s).

Local Lemma decreases s t :
  invariant s -> LocalDiscover.step EV next s = inl t ->
  count_potential t < count_potential s.
Proof.
  intros [Hwf Htodo] Hstep; rewrite LocalDiscover.step_equation in Hstep.
  destruct (LocalDiscover.pending s) as [|v rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem EV v (LocalDiscover.visited s)) eqn:Hseen;
    apply (f_equal (fun o => match o with inl t => t | inr _ => s end)) in Hstep;
    cbn beta iota in Hstep; subst t; unfold count_potential;
    cbn [LocalDiscover.visited LocalDiscover.pending]; rewrite Hpending;
    cbn [length]; rewrite ?length_app, Nat2N.inj_succ.
  - lia.
  - pose proof (mark_credit _ v Hwf (Htodo v (or_introl eq_refl)) Hseen).
    unfold weight in *; rewrite Nat2N.inj_add; lia.
Qed.

(** Fuel above roots plus finite adjacency incidence forces an actual completed discovery. *)
Theorem adequate fuel :
  N.of_nat (length roots) + sum weight U < N.pos fuel ->
  exists region, Cost.value (iterate (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots)) = inr region.
Proof.
  intro Hfuel; pose proof (iterate_value (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots)) as Hrun.
  assert (HI : invariant (LocalDiscover.State FinSet.empty roots)).
  { split; [apply FinSet.wf_empty|exact Hroots]. }
  assert (Hexhaust : forall n s last,
    runs (LocalDiscover.step_c EV next) n s (inl last) -> invariant s ->
    count_potential last + N.of_nat n <= count_potential s).
  { intros n s last Hr; remember (inl last) as result eqn:Hresult.
    induction Hr as [s|n s r Hstop|n s t result Hnext Hr IH]; intro Hs.
    - injection Hresult as <-; cbn; lia.
    - discriminate.
    - specialize (IH Hresult (preserved s t Hs Hnext)).
      pose proof (decreases s t Hs Hnext); rewrite Nat2N.inj_succ; lia. }
  destruct (Cost.value (iterate (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots))) as [last|region] eqn:Hloop.
  - pose proof (Hexhaust _ _ _ Hrun HI) as Hbound.
    unfold count_potential in Hbound; cbn [LocalDiscover.pending LocalDiscover.visited] in Hbound.
    assert (Hunused : unused (@FinSet.empty V) = sum weight U).
    { unfold unused; apply sum_ext; intro v; rewrite FinSet.mem_empty; reflexivity. }
    rewrite Hunused, fuel_nat_N in Hbound; lia.
  - now exists region.
Qed.

Variable w : N.
Hypothesis Hkey : forall v, In v U ->
  forall marked, Cost.ticks (FinSet.mem_c EV v marked) <= w /\
    Cost.ticks (FinSet.add_c EV v marked) <= w.
Hypothesis Hnext : forall v, In v U -> Cost.ticks (next v) <= w * weight v.

(** Pending probes and unseen expansion budgets remain separate in the cost potential. *)
Definition potential s :=
  (w + 3) * N.of_nat (length (LocalDiscover.pending s)) +
  (4 * w + 10) * unused (LocalDiscover.visited s).

Local Lemma step_credit s :
  invariant s ->
  match Cost.value (LocalDiscover.step_c EV next s) with
  | inl t => invariant t /\
    Cost.ticks (LocalDiscover.step_c EV next s) + potential t + 2 <= potential s
  | inr region => Cost.ticks (LocalDiscover.step_c EV next s) +
    (4 * w + 10) * unused region <= potential s
  end.
Proof.
  intros [Hwf Htodo].
  unfold LocalDiscover.step_c.
  destruct (LocalDiscover.pending s) as [|v rest] eqn:Hpending.
  - rewrite Cost.value_ret, Cost.ticks_ret; unfold potential; rewrite Hpending.
    cbn [length]; lia.
  - destruct (Hkey v (Htodo v (or_introl eq_refl)) (LocalDiscover.visited s))
      as [Hmem Hadd].
    pose proof (Hnext v (Htodo v (or_introl eq_refl))) as Hadj.
    rewrite Cost.value_bind, Cost.ticks_bind; fold (FinSet.mem EV v (LocalDiscover.visited s)).
    destruct (FinSet.mem EV v (LocalDiscover.visited s)) eqn:Hseen.
    + rewrite Cost.value_ret, Cost.ticks_ret; split.
      * split; [exact Hwf|]; intros x Hx; apply Htodo; now right.
      * unfold potential; cbn [LocalDiscover.visited LocalDiscover.pending].
        rewrite Hpending; cbn [length]; rewrite Nat2N.inj_succ; nia.
    + rewrite !Cost.value_bind, !Cost.ticks_bind, ?Cost.ticks_step, ?Cost.value_step,
        ?Cost.value_ret, ?Cost.ticks_ret, ?value_app_c, ?ticks_app_c.
      split.
      * split; [apply FinSet.wf_add, Hwf|].
        cbn [LocalDiscover.pending]; intros x Hx; apply in_app_or in Hx as [Hx|Hx].
        -- apply (Hclosed v (Htodo v (or_introl eq_refl)) x Hx).
        -- apply Htodo; now right.
      * pose proof (mark_credit _ v Hwf (Htodo v (or_introl eq_refl)) Hseen) as Hmark.
        unfold potential; cbn [LocalDiscover.visited LocalDiscover.pending].
        rewrite Hpending, length_app; cbn [length]; rewrite Nat2N.inj_succ, Nat2N.inj_add.
        fold (FinSet.add EV v (LocalDiscover.visited s)).
        unfold weight in Hadj, Hmark; nia.
Qed.

(** Every fuelled discovery is bounded by the finite support's complete incidence budget. *)
Theorem discover_full_cost fuel :
  Cost.ticks (iterate (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots)) <=
    (w + 3) * N.of_nat (length roots) +
    (4 * w + 10) * sum weight U + N.pos (Pos.size fuel).
Proof.
  pose proof (iterate_terminal_credit (LocalDiscover.step_c EV next) invariant potential
    (fun region => (4 * w + 10) * unused region) 0
    (fun s Hs => step_credit s Hs) fuel (LocalDiscover.State FinSet.empty roots)
    (conj (FinSet.wf_empty EV) Hroots)) as Hcost.
  unfold potential in Hcost; cbn beta in Hcost.
  cbn [LocalDiscover.visited LocalDiscover.pending] in Hcost.
  assert (Hempty : unused (@FinSet.empty V) = sum weight U).
  { unfold unused; apply sum_ext; intro v; rewrite FinSet.mem_empty; reflexivity. }
  rewrite Hempty in Hcost.
  destruct (Cost.value (iterate (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots))); nia.
Qed.

(** A successful discovery pays for its visited incidence and refunds all unvisited credits. *)
Theorem local_discover_cost fuel region :
  Cost.value (iterate (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots)) = inr region ->
  Cost.ticks (iterate (LocalDiscover.step_c EV next) fuel
    (LocalDiscover.State FinSet.empty roots)) <=
    (w + 3) * N.of_nat (length roots) +
    (4 * w + 10) * visited_work region + N.pos (Pos.size fuel).
Proof.
  intro Hloop.
  pose proof (iterate_terminal_credit (LocalDiscover.step_c EV next) invariant potential
    (fun region => (4 * w + 10) * unused region) 0
    (fun s Hs => step_credit s Hs) fuel (LocalDiscover.State FinSet.empty roots)
    (conj (FinSet.wf_empty EV) Hroots)) as Hcost.
  rewrite Hloop in Hcost; cbn beta in Hcost.
  unfold potential in Hcost; cbn [LocalDiscover.visited LocalDiscover.pending] in Hcost.
  assert (Hempty : unused (@FinSet.empty V) = sum weight U).
  { unfold unused; apply sum_ext; intro v; rewrite FinSet.mem_empty; reflexivity. }
  rewrite Hempty in Hcost.
  pose proof (partition region); nia.
Qed.

End Credit.

End LocalCredit.
Import LocalCredit.
