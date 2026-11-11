(** * Structural progress of the actual value worklist

    Queue coherence and finite prepared key support are maintained by every raw value step.
    For example, a newly joined destination is an actual prepared transition endpoint.
    Builds on: FrameworkTabValues and FrameworkTabQueue. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Framework Require Import FrameworkIfds FrameworkIde FrameworkTabValues FrameworkTabQueue
  FrameworkTabCost.
Import List.ListNotations Cost.Notations.

Module TabValueProgress.

(** Structural validity ties the real pending set to its real duplicate-free queue. *)
Definition shape {N E P D A F} (I : Ide.t N E P D A F)
    (s : TabValues.state N D A) :=
  Map.wf (IdeValue.key_enc I) (TabValues.values s) /\
  TabQueue.coherent (IdeValue.key_enc I) (TabValues.work s) (TabValues.pending s).

(** Both stored and scheduled value keys stay in the actual prepared inventory. *)
Definition supported {N E P D A F} (I : Ide.t N E P D A F) (p : TabValues.prepared N D F)
    (s : TabValues.state N D A) :=
  (forall v, In v (TabValues.work s) -> In v (TabValues.inventory p)) /\
  (forall v a, Map.get (IdeValue.key_enc I) v (TabValues.values s) = Some a ->
    In v (TabValues.inventory p)).

Definition invariant {N E P D A F} (I : Ide.t N E P D A F) p s :=
  shape I s /\ supported I p s.

(** Rank credits are a semantic measure over the full prepared inventory. *)
Definition remaining {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Ide.values I)) (p : TabValues.prepared N D F) m :=
  fold_right (fun v total =>
    (bound H - rank H (TabValues.lookup I m v) + total)%nat) O (TabValues.inventory p).

(** Popping work spends one credit while a strict join can refund at most one scheduled item. *)
Definition potential {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Ide.values I)) p s :=
  (remaining I H p (TabValues.values s) + length (TabValues.work s))%nat.

Local Lemma sum_monotone {X} (old new : X -> nat) xs :
  (forall x, In x xs -> new x <= old x)%nat ->
  (fold_right (fun x n => new x + n) O xs <=
    fold_right (fun x n => old x + n) O xs)%nat.
Proof.
  induction xs as [|x xs IH]; intro Hbound; cbn [fold_right]; [lia|].
  assert (Htail : forall y, In y xs -> (new y <= old y)%nat).
  { intros y Hy; apply Hbound; right; exact Hy. }
  specialize (IH Htail); specialize (Hbound x (or_introl eq_refl)); lia.
Qed.

Local Lemma sum_decreases {X} (old new : X -> nat) xs changed :
  In changed xs -> (forall x, In x xs -> new x <= old x)%nat ->
  (new changed < old changed)%nat ->
  (fold_right (fun x n => new x + n) O xs <
    fold_right (fun x n => old x + n) O xs)%nat.
Proof.
  induction xs as [|x xs IH]; intros Hin Hbound Hchanged; [inversion Hin|].
  cbn [fold_right]; assert (Htail : forall y, In y xs -> (new y <= old y)%nat).
  { intros y Hy; apply Hbound; right; exact Hy. }
  destruct Hin as [Heq|Hin].
  - subst x; pose proof (sum_monotone old new xs Htail); lia.
  - specialize (IH Hin Htail Hchanged); specialize (Hbound x (or_introl eq_refl)); lia.
Qed.

Local Lemma lookup_set {N E P D A F} (I : Ide.t N E P D A F) m key value query :
  Map.wf (IdeValue.key_enc I) m ->
  TabValues.lookup I (Map.set (IdeValue.key_enc I) key value m) query =
    if eqb (IdeValue.key_enc I) query key then value else TabValues.lookup I m query.
Proof.
  intro Hwf; rewrite !TabValues.lookup_equation, !Map.find_or_equation.
  rewrite Map.get_set by exact Hwf.
  destruct (eqb (IdeValue.key_enc I) query key); reflexivity.
Qed.

Local Lemma remaining_bound {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Ide.values I)) p m :
  (remaining I H p m <= bound H * length (TabValues.inventory p))%nat.
Proof.
  unfold remaining; induction (TabValues.inventory p) as [|v vs IH]; cbn [fold_right length];
    nia.
Qed.

Local Lemma schedule_potential {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Ide.values I)) p key s :
  (potential I H p (Cost.value (TabValues.schedule_c I key s)) <=
    S (potential I H p s))%nat.
Proof.
  rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) key (TabValues.pending s));
    unfold potential; cbn [TabValues.values TabValues.work length]; lia.
Qed.

(** Actual value updates cannot increase rank-plus-queue potential on prepared keys. *)
Theorem update_potential {N E P D A F} (I : Ide.t N E P D A F)
    (H : height (Ide.values I)) p key a s :
  encoding_laws (IdeValue.key_enc I) -> lattice_laws (Ide.values I) ->
  Map.wf (IdeValue.key_enc I) (TabValues.values s) -> In key (TabValues.inventory p) ->
  (potential I H p (Cost.value (TabValues.update_c I key a s)) <= potential I H p s)%nat.
Proof.
  intros HE HL Hwf Hkey; rewrite TabValues.update_equation.
  destruct (leb (Ide.values I) a (TabValues.lookup I (TabValues.values s) key)) eqn:Hcovered;
    [lia|].
  set (joined := join (Ide.values I) (TabValues.lookup I (TabValues.values s) key) a).
  set (updated := Map.set (IdeValue.key_enc I) key joined (TabValues.values s)).
  assert (Hrank :
    (rank H (TabValues.lookup I (TabValues.values s) key) < rank H joined)%nat).
  { apply TabCost.update_rank_progress; try exact HL; try exact Logic.I; exact Hcovered. }
  pose proof (rank_bounded H joined Logic.I) as Hrank_bound.
  assert (Hcredit :
    (bound H - rank H joined <
      bound H - rank H (TabValues.lookup I (TabValues.values s) key))%nat) by lia.
  assert (Hchanged : (remaining I H p updated < remaining I H p (TabValues.values s))%nat).
  { unfold remaining; apply sum_decreases with (changed := key); [exact Hkey| |].
    - intros query Hquery; unfold updated; rewrite lookup_set by exact Hwf.
      destruct (eqb (IdeValue.key_enc I) query key) eqn:Heq; [|lia].
      apply (eqb_true_iff (IdeValue.key_enc I) HE) in Heq; subst query; lia.
    - unfold updated; rewrite lookup_set by exact Hwf.
      rewrite eqb_refl; exact Hcredit. }
  pose proof (schedule_potential I H p key
    (TabValues.State updated (TabValues.work s) (TabValues.pending s))) as Hschedule.
  unfold potential in *; cbn [TabValues.values TabValues.work] in *; lia.
Qed.

Local Lemma fold_valid {X S} (P : S -> Prop) (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x)) -> P s -> P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - exact Hs.
  - apply IH.
    + intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy].
    + apply Hstep; [exact Hs|left; reflexivity].
Qed.

Local Lemma fold_nonincreasing {X S} (P : S -> Prop) (phi : S -> nat)
    (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x) /\ phi (f s x) <= phi s)%nat ->
  P s -> P (fold_left f xs s) /\ (phi (fold_left f xs s) <= phi s)%nat.
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - split; [exact Hs|lia].
  - destruct (Hstep s x Hs (or_introl eq_refl)) as [Hnext Hdecrease].
    assert (Htail : forall t y, P t -> In y xs ->
      P (f t y) /\ (phi (f t y) <= phi t)%nat).
    { intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy]. }
    destruct (IH (f s x) Htail Hnext) as [Hfinal Hbound]; split; [exact Hfinal|lia].
Qed.

Local Lemma schedule_shape {N E P D A F} (I : Ide.t N E P D A F) v s :
  encoding_laws (IdeValue.key_enc I) -> shape I s ->
  shape I (Cost.value (TabValues.schedule_c I v s)).
Proof.
  intros HE [Hwf Hqueue]; rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) v (TabValues.pending s)) eqn:Hpending.
  - split; assumption.
  - split; [exact Hwf|].
    apply TabQueue.insert_coherent; assumption.
Qed.

Local Lemma schedule_supported {N E P D A F} (I : Ide.t N E P D A F) p v s :
  supported I p s -> In v (TabValues.inventory p) ->
  supported I p (Cost.value (TabValues.schedule_c I v s)).
Proof.
  intros [Hwork Hstored] Hv; rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) v (TabValues.pending s)).
  - split; assumption.
  - split; [|exact Hstored].
    intros q [Heq|Hq]; [subst q; exact Hv|apply Hwork; exact Hq].
Qed.

Local Lemma update_shape {N E P D A F} (I : Ide.t N E P D A F) v a s :
  encoding_laws (IdeValue.key_enc I) -> shape I s ->
  shape I (Cost.value (TabValues.update_c I v a s)).
Proof.
  intros HE [Hwf Hqueue]; rewrite TabValues.update_equation.
  destruct (leb (Ide.values I) a (TabValues.lookup I (TabValues.values s) v)).
  - split; assumption.
  - apply schedule_shape; [exact HE|].
    split; [apply Map.wf_set; exact Hwf|exact Hqueue].
Qed.

Local Lemma update_supported {N E P D A F} (I : Ide.t N E P D A F) p v a s :
  encoding_laws (IdeValue.key_enc I) -> shape I s -> supported I p s ->
  In v (TabValues.inventory p) ->
  supported I p (Cost.value (TabValues.update_c I v a s)).
Proof.
  intros HE [Hwf Hqueue] [Hwork Hstored] Hv; rewrite TabValues.update_equation.
  destruct (leb (Ide.values I) a (TabValues.lookup I (TabValues.values s) v)).
  - split; assumption.
  - apply schedule_supported; [|exact Hv]; split; [exact Hwork|].
    intros q b Hget; cbn [TabValues.values] in Hget.
    rewrite Map.get_set in Hget by exact Hwf.
    destruct (eqb (IdeValue.key_enc I) q v) eqn:Hkey.
    + apply (eqb_true_iff (IdeValue.key_enc I) HE) in Hkey; subst q; exact Hv.
    + apply Hstored with (a := b); exact Hget.
Qed.

Local Lemma prepared_source_supported {N E P D A F} (I : Ide.t N E P D A F) J start v :
  In v (TabValues.sources (TabValues.prepare I J start)) ->
  In v (TabValues.inventory (TabValues.prepare I J start)).
Proof.
  rewrite TabValues.prepare_equation; cbn [TabValues.sources TabValues.inventory].
  intros [Heq|Hin]; [left; exact Heq|right; apply in_app_iff; left; exact Hin].
Qed.

Local Lemma prepared_target_supported {N E P D A F} (I : Ide.t N E P D A F)
    J start source a :
  In a (Index.find (IdeValue.key_enc I) source
    (TabValues.outgoing (TabValues.prepare I J start))) ->
  In (snd (fst a)) (TabValues.inventory (TabValues.prepare I J start)).
Proof.
  rewrite TabValues.prepare_equation; cbn [TabValues.outgoing TabValues.inventory].
  rewrite Index.find_group_by; intro Hin; apply filter_In in Hin.
  right; apply in_app_iff; right; apply in_map_iff.
  exists a; split; [reflexivity|exact (proj1 Hin)].
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F)
  (start : N * option D) (a0 : A).
Context (HE : encoding_laws (IdeValue.key_enc I)).

(** Initialization establishes the actual queue coherence and finite endpoint support internally. *)
Theorem initial_invariant :
  invariant I (TabValues.prepare I J start)
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0)).
Proof.
  rewrite TabValues.initial_equation.
  assert (Hscheduled : invariant I (TabValues.prepare I J start)
    (fold_left (fun s v => Cost.value (TabValues.schedule_c I v s))
      (TabValues.sources (TabValues.prepare I J start))
      (TabValues.State Map.empty [] FinSet.empty))).
  { apply fold_valid.
    - intros s v [Hshape Hsupport] Hv; split.
      + apply schedule_shape; assumption.
      + apply schedule_supported; [exact Hsupport|].
        apply prepared_source_supported; exact Hv.
    - split; [split; [apply Map.wf_empty|apply TabQueue.empty_coherent]|].
      split.
      + intros v Hin; inversion Hin.
      + intros v a Hget; cbn [TabValues.values] in Hget.
        rewrite Map.get_empty in Hget; discriminate. }
  split.
  - apply update_shape; [exact HE|exact (proj1 Hscheduled)].
  - apply update_supported; try exact HE; [exact (proj1 Hscheduled)|exact (proj2 Hscheduled)|].
    rewrite TabValues.prepare_equation; left; reflexivity.
Qed.

Local Lemma step_invariant s :
  invariant I (TabValues.prepare I J start) s ->
  match Cost.value (TabValues.step_c I (TabValues.prepare I J start) s) with
  | inl next | inr next => invariant I (TabValues.prepare I J start) next
  end.
Proof.
  intros [[Hwf Hqueue] [Hwork Hstored]]; rewrite TabValues.step_equation.
  destruct (TabValues.work s) as [|v rest] eqn:Hlist.
  - split.
    + split; [exact Hwf|rewrite Hlist; exact Hqueue].
    + split; [|exact Hstored].
      intros q Hq; rewrite Hlist in Hq; exact (Hwork q Hq).
  - apply fold_valid.
    + intros t a [Hshape Hsupport] Ha; rewrite TabValues.arc_equation; split.
      * apply update_shape; assumption.
      * apply update_supported; try assumption.
        apply prepared_target_supported with (source := v); exact Ha.
    + split.
      * split; [exact Hwf|].
        apply TabQueue.pop_coherent; [exact HE|exact Hqueue].
      * split; [|exact Hstored].
        intros q Hq; apply Hwork; right; exact Hq.
Qed.

(** Every actual raw state retains queue coherence and finite prepared key support. *)
Theorem raw_invariant fuel :
  match TabValues.raw I J start a0 fuel with
  | inl s | inr s => invariant I (TabValues.prepare I J start) s
  end.
Proof.
  rewrite TabValues.raw_equation.
  pose proof (iterate_value (TabValues.step_c I (TabValues.prepare I J start)) fuel
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (TabValues.step_c I (TabValues.prepare I J start)) n s result ->
    invariant I (TabValues.prepare I J start) s ->
    match result with
    | inl next | inr next => invariant I (TabValues.prepare I J start) next
    end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intro Hinv.
    - exact Hinv.
    - pose proof (step_invariant s Hinv) as Hstep; rewrite Hstop in Hstep; exact Hstep.
    - apply IH; pose proof (step_invariant s Hinv) as Hstep.
      rewrite Hnext in Hstep; exact Hstep. }
  exact (Hpreserved _ _ _ Hrun initial_invariant).
Qed.

Section Height.
Context (H : height (Ide.values I)) (HL : lattice_laws (Ide.values I)).

Local Lemma outgoing_progress source s :
  invariant I (TabValues.prepare I J start) s ->
  let final := fold_left (fun s a => Cost.value (TabValues.arc_c I a s))
    (Index.find (IdeValue.key_enc I) source
      (TabValues.outgoing (TabValues.prepare I J start))) s in
  invariant I (TabValues.prepare I J start) final /\
    (potential I H (TabValues.prepare I J start) final <=
      potential I H (TabValues.prepare I J start) s)%nat.
Proof.
  intro Hinv; apply fold_nonincreasing; [|exact Hinv].
  intros t a [Hshape Hsupport] Ha; rewrite TabValues.arc_equation.
  assert (Htarget : In (snd (fst a)) (TabValues.inventory (TabValues.prepare I J start))).
  { apply prepared_target_supported with (source := source); exact Ha. }
  split.
  - split.
    + apply update_shape; assumption.
    + apply update_supported; assumption.
  - apply update_potential; [exact HE|exact HL|exact (proj1 Hshape)|exact Htarget].
Qed.

Local Lemma step_potential s :
  invariant I (TabValues.prepare I J start) s ->
  match Cost.value (TabValues.step_c I (TabValues.prepare I J start) s) with
  | inl next =>
    (potential I H (TabValues.prepare I J start) next <
      potential I H (TabValues.prepare I J start) s)%nat
  | inr _ => True
  end.
Proof.
  intros [[Hwf Hqueue] [Hwork Hstored]]; rewrite TabValues.step_equation.
  destruct (TabValues.work s) as [|v rest] eqn:Hlist; [exact Logic.I|].
  set (popped := TabValues.State (TabValues.values s) rest
    (FinSet.remove (IdeValue.key_enc I) v (TabValues.pending s))).
  assert (Hpopped : invariant I (TabValues.prepare I J start) popped).
  { split.
    - split; [exact Hwf|apply TabQueue.pop_coherent; assumption].
    - split; [|exact Hstored]; intros q Hq; apply Hwork; right; exact Hq. }
  pose proof (proj2 (outgoing_progress v popped Hpopped)) as Hprogress.
  unfold popped in *; unfold potential in *.
  cbn [TabValues.values TabValues.work] in Hprogress.
  rewrite Hlist; cbn [length]; lia.
Qed.

Local Lemma initial_potential :
  (potential I H (TabValues.prepare I J start)
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0)) <=
    (1 + bound H) * length (TabValues.inventory (TabValues.prepare I J start)))%nat.
Proof.
  set (initial := Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0)).
  pose proof initial_invariant as Hinv; fold initial in Hinv.
  destruct Hinv as [[Hwf [Hset [Hnodup Hpending]]] [Hwork Hstored]].
  pose proof (remaining_bound I H (TabValues.prepare I J start) (TabValues.values initial))
    as Hremaining.
  assert (Hlength :
    (length (TabValues.work initial) <=
      length (TabValues.inventory (TabValues.prepare I J start)))%nat).
  { apply NoDup_incl_length; [exact Hnodup|exact Hwork]. }
  unfold potential; fold initial; nia.
Qed.

Local Lemma runs_bound n s result :
  runs (TabValues.step_c I (TabValues.prepare I J start)) n s result ->
  invariant I (TabValues.prepare I J start) s ->
  match result with
  | inl _ => (n <= potential I H (TabValues.prepare I J start) s)%nat
  | inr _ => True
  end.
Proof.
  intro Hrun; induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH]; intro Hinv.
  - lia.
  - exact Logic.I.
  - pose proof (step_invariant s Hinv) as Hvalid.
    pose proof (step_potential s Hinv) as Hdecrease.
    rewrite Hnext in Hvalid, Hdecrease.
    specialize (IH Hvalid); destruct result; [lia|exact Logic.I].
Qed.

(** A separately supplied finite height constructively bounds the actual number of value steps. *)
Theorem raw_stops fuel :
  ((1 + bound H) * length (TabValues.inventory (TabValues.prepare I J start)) <
    Pos.to_nat fuel)%nat ->
  exists stopped, TabValues.raw I J start a0 fuel = inr stopped /\ TabValues.work stopped = [].
Proof.
  intro Hfuel; rewrite TabValues.raw_equation.
  remember (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))
    as initial eqn:Hinitial.
  destruct (Cost.value (iterate (TabValues.step_c I (TabValues.prepare I J start)) fuel initial))
    as [exhausted|stopped] eqn:Hresult.
  - pose proof (iterate_value (TabValues.step_c I (TabValues.prepare I J start)) fuel initial)
      as Hrun; rewrite Hresult in Hrun.
    pose proof (runs_bound _ _ _ Hrun) as Hbound.
    rewrite Hinitial in Hbound; specialize (Hbound initial_invariant).
    pose proof initial_potential; lia.
  - exists stopped; split; [reflexivity|].
    destruct (iterate_inr_stops (TabValues.step_c I (TabValues.prepare I J start))
      fuel initial stopped Hresult) as [used [last [Hused [Hprefix Hstop]]]].
    rewrite TabValues.step_equation in Hstop.
    destruct (TabValues.work last) as [|v rest] eqn:Hwork; [|discriminate].
    injection Hstop as Hsame; subst stopped; exact Hwork.
Qed.

End Height.

End Run.

(** Finite-height execution constructs its own numeric fuel and prepares transitions once. *)
Definition complete_raw_c {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :=
  let* p := TabValues.prepare_c I J start in
  let* fuel := TabCost.inventory_fuel_c (TabValues.inventory p) (bound H) in
  let* s := TabValues.initial_c I p start a0 in
  iterate (TabValues.step_c I p) fuel s.

Definition complete_raw {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :=
  Cost.value (complete_raw_c I J start a0 H).

(** The finite-height runner agrees with the raw engine at its constructed inventory budget. *)
Theorem complete_raw_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  complete_raw I J start a0 H =
    TabValues.raw I J start a0
      (TabCost.inventory_fuel (TabValues.inventory (TabValues.prepare I J start)) (bound H)).
Proof.
  rewrite TabValues.raw_equation; unfold complete_raw, complete_raw_c.
  autorewrite with galois_cost; reflexivity.
Qed.

(** Raw completion retains preparation, numeric construction, initialization and actual loop ticks. *)
Theorem complete_raw_cost_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  Cost.ticks (complete_raw_c I J start a0 H) =
    let p := TabValues.prepare I J start in
    let fuel := TabCost.inventory_fuel (TabValues.inventory p) (bound H) in
    (Cost.ticks (TabValues.prepare_c I J start) +
      Cost.ticks (TabCost.inventory_fuel_c (TabValues.inventory p) (bound H)) +
      Cost.ticks (TabValues.initial_c I p start a0) +
      Cost.ticks (iterate (TabValues.step_c I p) fuel
        (Cost.value (TabValues.initial_c I p start a0))))%N.
Proof.
  unfold complete_raw_c; autorewrite with galois_cost; cbn zeta.
  fold (TabValues.prepare I J start).
  fold (TabCost.inventory_fuel
    (TabValues.inventory (TabValues.prepare I J start)) (bound H)).
  lia.
Qed.

(** Actual finite-height value execution reaches a stopped state without caller-supplied fuel. *)
Theorem complete_raw_stops {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  encoding_laws (IdeValue.key_enc I) -> lattice_laws (Ide.values I) ->
  exists stopped, complete_raw I J start a0 H = inr stopped /\ TabValues.work stopped = [].
Proof.
  intros HE HL; rewrite complete_raw_equation.
  apply (raw_stops I J start a0 HE H HL).
  rewrite TabCost.inventory_fuel_numeric; lia.
Qed.

(** The finite-height wrapper certifies the actual reached candidate and retains rejection explicitly. *)
Definition complete_c {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :=
  let* result := complete_raw_c I J start a0 H in
  match result with
  | inl s => Cost.ret (TabValues.Exhausted s)
  | inr s => TabValues.certify_c I J start a0 s
  end.

Definition complete {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :=
  Cost.value (complete_c I J start a0 H).

(** The wrapper's outcome is determined by its actual constructed-budget raw run. *)
Theorem complete_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  complete I J start a0 H =
    match complete_raw I J start a0 H with
    | inl s => TabValues.Exhausted s
    | inr s => Cost.value (TabValues.certify_c I J start a0 s)
    end.
Proof.
  unfold complete, complete_c; autorewrite with galois_cost.
  fold (complete_raw I J start a0 H); destruct (complete_raw I J start a0 H); reflexivity.
Qed.

(** The finite-height wrapper returns exactly the raw wrapper's constructed-budget outcome. *)
Theorem complete_agrees {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  complete I J start a0 H =
    TabValues.tabulate_values I J start a0
      (TabCost.inventory_fuel (TabValues.inventory (TabValues.prepare I J start)) (bound H)).
Proof.
  rewrite complete_equation, complete_raw_equation, TabValues.outcome_equation; reflexivity.
Qed.

(** The total wrapper retains the entire reached candidate checker charge. *)
Theorem complete_cost_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  Cost.ticks (complete_c I J start a0 H) =
    (Cost.ticks (complete_raw_c I J start a0 H) +
      match complete_raw I J start a0 H with
      | inl _ => 0
      | inr s => Cost.ticks (TabValues.certify_c I J start a0 s)
      end)%N.
Proof.
  unfold complete_c; rewrite Cost.ticks_bind; fold (complete_raw I J start a0 H).
  destruct (complete_raw I J start a0 H); rewrite ?Cost.ticks_ret; reflexivity.
Qed.

(** Numeric exhaustion is impossible for the actual finite-height wrapper on lawful keys and joins. *)
Theorem complete_not_exhausted {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  encoding_laws (IdeValue.key_enc I) -> lattice_laws (Ide.values I) ->
  forall s, complete I J start a0 H <> TabValues.Exhausted s.
Proof.
  intros HE HL s.
  destruct (complete_raw_stops I J start a0 H HE HL) as [stopped [Hrun Hempty]].
  rewrite complete_equation, Hrun; apply TabValues.certify_not_exhausted.
Qed.

End TabValueProgress.
