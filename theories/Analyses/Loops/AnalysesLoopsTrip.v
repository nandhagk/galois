(** * Closed-form wrapped first failure

    A Euclidean prefix count guides a binary search for the first failed comparison.
    For example, a periodic sequence with no failures returns None after one prefix count.
    Builds on: AnalysesLoopsFloor, AnalysesLoopsFailure and CostLoop. *)

From Stdlib Require Import NArith ZArith List Lia.
From Galois.Cost Require Import CostMonad CostLoop CostBound.
From Galois.Bits Require Import BitsWord.
From Galois.Analyses.Loops Require Import
  AnalysesLoopsChrec AnalysesLoopsFailure AnalysesLoopsFloor.
Import Cost.Notations Failure Floor.
Local Open Scope N_scope.

Module Trip.

(** The exact executable search remains the first-failure specification. *)
Definition first_failure := Failure.first_failure.

(** The modular failure counter is the floor file's single implementation. *)
Definition mod_count := Floor.mod_count.

(** The public charged counter retains the floor owner's complete instrumentation. *)
Definition mod_count_c := Floor.mod_count_c.

(** Projecting the charged alias gives the same modular counter. *)
Theorem mod_count_value w sg cmp a step bound n :
  Cost.value (mod_count_c w sg cmp a step bound n) =
    mod_count w sg cmp a step bound n.
Proof.
  reflexivity.
Qed.

Lemma total_zero_iff (test : N -> bool) n :
  floor_total (fun i => if test i then 0 else 1) n = 0 <->
    forall k, k < n -> test k = true.
Proof.
  induction n using N.peano_ind.
  - split; [intros _ k Hk; lia|intro Hall; reflexivity].
  - rewrite floor_total_succ; destruct (test n) eqn:Hlast.
    + rewrite N.add_0_r, IHn; split.
      * intros Hall k Hk.
        destruct (N.eq_dec k n) as [Heq|Hne]; [subst; exact Hlast|apply Hall; lia].
      * intros Hall k Hk; apply Hall; lia.
    + split; [lia|].
      intro Hall; specialize (Hall n ltac:(lia)); congruence.
Qed.

(** A zero prefix count certifies continuation at every index in that prefix. *)
Theorem mod_count_zero_iff w sg cmp a step bound n :
  mod_count w sg cmp a step bound n = 0 <->
    forall k, k < n -> affine_test w sg cmp a step bound k = true.
Proof.
  unfold mod_count; rewrite mod_count_total; apply total_zero_iff.
Qed.

(** Extending a prefix adds the indicator of its new final comparison. *)
Theorem mod_count_succ w sg cmp a step bound n :
  mod_count w sg cmp a step bound (N.succ n) =
    mod_count w sg cmp a step bound n +
      if affine_test w sg cmp a step bound n then 0 else 1.
Proof.
  unfold mod_count; rewrite !mod_count_total, floor_total_succ; reflexivity.
Qed.

(** Failure counts are monotone in the prefix length. *)
Theorem mod_count_monotone w sg cmp a step bound n m : n <= m ->
  mod_count w sg cmp a step bound n <= mod_count w sg cmp a step bound m.
Proof.
  intro Hle; induction m using N.peano_ind.
  - assert (n = 0) by lia; subst n; reflexivity.
  - destruct (N.eq_dec n (N.succ m)) as [Heq|Hne]; [subst; reflexivity|].
    rewrite mod_count_succ; specialize (IHm ltac:(lia)).
    destruct (affine_test w sg cmp a step bound m); lia.
Qed.

(** A prefix contains at most one failure for each of its indices. *)
Theorem mod_count_bound w sg cmp a step bound n :
  mod_count w sg cmp a step bound n <= n.
Proof.
  induction n using N.peano_ind.
  - unfold mod_count; rewrite mod_count_total, floor_total_zero; reflexivity.
  - rewrite mod_count_succ.
    destruct (affine_test w sg cmp a step bound n); lia.
Qed.

(** Binary-search endpoints delimit a zero-count prefix and a prefix with a failure. *)
Record interval : Type := Interval {
  lower : N;
  upper : N
}.

(** Search validity attaches both count facts to the current endpoints. *)
Definition valid w sg cmp a step bound (s : interval) : Prop :=
  lower s < upper s /\
    mod_count w sg cmp a step bound (lower s) = 0 /\
    0 < mod_count w sg cmp a step bound (upper s).

(** The binary-search rank is the bit size of the number of undecided indices. *)
Definition rank (s : interval) := N.size (N.pred (upper s - lower s)).

(** A search step charges its endpoint arithmetic and the actual modular-count call. *)
Definition search_step_c w sg cmp a step bound (s : interval) : Cost.t (interval + N) :=
  let* gap := primitive_c (fun _ => upper s - lower s) in
  let* finished := primitive_c (fun _ => gap <=? 1) in
  if finished then Cost.ret (inr (lower s)) else
  let* sum := primitive_c (fun _ => lower s + upper s) in
  let* mid := primitive_c (fun _ => sum / 2) in
  let* count := Floor.mod_count_c w sg cmp a step bound mid in
  let* zero := primitive_c (fun _ => count =? 0) in
  Cost.ret (inl (if zero then Interval mid (upper s) else Interval (lower s) mid)).

Lemma search_step_value w sg cmp a step bound s :
  Cost.value (search_step_c w sg cmp a step bound s) =
    if upper s - lower s <=? 1 then inr (lower s) else
    let mid := (lower s + upper s) / 2 in
    inl (if mod_count w sg cmp a step bound mid =? 0
      then Interval mid (upper s) else Interval (lower s) mid).
Proof.
  unfold search_step_c, primitive_c; autorewrite with galois_cost.
  destruct (_ <=? _); autorewrite with galois_cost; reflexivity.
Qed.

Lemma midpoint_bounds lo hi : lo + 1 < hi ->
  lo < (lo + hi) / 2 < hi /\
  2 * N.pred ((lo + hi) / 2 - lo) <= N.pred (hi - lo) /\
  2 * N.pred (hi - (lo + hi) / 2) <= N.pred (hi - lo).
Proof.
  intro Hgap.
  pose proof (N.div_mod (lo + hi) 2 ltac:(lia)) as Hdivision.
  pose proof (N.mod_lt (lo + hi) 2 ltac:(lia)) as Hremainder.
  remember ((lo + hi) / 2) as mid in *.
  remember ((lo + hi) mod 2) as remainder in *.
  assert (Hmid : lo < mid < hi) by lia.
  repeat split; try lia.
Qed.

Lemma size_half_le x y : 0 < y -> 2 * x <= y -> N.size x < N.size y.
Proof.
  intros Hpositive Hhalf.
  destruct (N.eq_dec x 0) as [Hzero|Hnonzero].
  - subst x; cbn [N.size]; rewrite N.size_log2 by lia; lia.
  - pose proof (floor_size_mono (2 * x) y Hhalf) as Hsize.
    rewrite !N.size_log2 in * by nia.
    rewrite N.log2_double in Hsize by lia; lia.
Qed.

Lemma search_step_preserved w sg cmp a step bound s :
  valid w sg cmp a step bound s ->
  match Cost.value (search_step_c w sg cmp a step bound s) with
  | inl next => valid w sg cmp a step bound next /\ rank next < rank s
  | inr t =>
    (forall k, k < t -> affine_test w sg cmp a step bound k = true) /\
      affine_test w sg cmp a step bound t = false
  end.
Proof.
  destruct s as [lo hi]; intros [Hlt [Hzero Hpositive]].
  rewrite search_step_value; cbn [lower upper] in *.
  destruct (hi - lo <=? 1) eqn:Hfinished.
  - apply N.leb_le in Hfinished; assert (Hhi : hi = N.succ lo) by lia.
    split; [apply mod_count_zero_iff; exact Hzero|].
    rewrite Hhi, mod_count_succ, Hzero in Hpositive.
    destruct (affine_test w sg cmp a step bound lo); [lia|reflexivity].
  - apply N.leb_gt in Hfinished.
    destruct (midpoint_bounds lo hi ltac:(lia)) as [Hmid [Hleft Hright]].
    destruct (mod_count w sg cmp a step bound ((lo + hi) / 2) =? 0) eqn:Hcount.
    + apply N.eqb_eq in Hcount; split.
      * unfold valid; cbn [lower upper]; repeat split; try lia.
      * unfold rank; cbn [lower upper].
        apply size_half_le; lia.
    + apply N.eqb_neq in Hcount; split.
      * unfold valid; cbn [lower upper]; repeat split; try lia.
      * unfold rank; cbn [lower upper].
        apply size_half_le; lia.
Qed.

Lemma search_runs_sound w sg cmp a step bound n s result :
  runs (search_step_c w sg cmp a step bound) n s result ->
  valid w sg cmp a step bound s ->
  match result with
  | inl next => valid w sg cmp a step bound next /\ rank next + N.of_nat n <= rank s
  | inr t =>
    (forall k, k < t -> affine_test w sg cmp a step bound k = true) /\
      affine_test w sg cmp a step bound t = false
  end.
Proof.
  intro Hrun; induction Hrun as [s|n s t Hstop|n s next result Hnext Hrun IH];
    intro Hvalid.
  - split; [exact Hvalid|cbn; lia].
  - pose proof (search_step_preserved w sg cmp a step bound s Hvalid) as Hstep.
    rewrite Hstop in Hstep; exact Hstep.
  - pose proof (search_step_preserved w sg cmp a step bound s Hvalid) as Hstep.
    rewrite Hnext in Hstep; destruct Hstep as [Hvalid' Hrank].
    specialize (IH Hvalid'); destruct result as [last|t]; [|exact IH].
    destruct IH as [Hlast Hbound]; split; [exact Hlast|].
    rewrite Nat2N.inj_succ; lia.
Qed.

(** A search budget larger than its rank cannot exhaust and returns the first failed test. *)
Theorem search_terminates w sg cmp a step bound fuel s :
  valid w sg cmp a step bound s -> rank s < N.pos fuel ->
  exists t, Cost.value (iterate (search_step_c w sg cmp a step bound) fuel s) = inr t /\
    (forall k, k < t -> affine_test w sg cmp a step bound k = true) /\
      affine_test w sg cmp a step bound t = false.
Proof.
  intros Hvalid Hrank.
  pose proof (search_runs_sound w sg cmp a step bound _ _ _
    (iterate_value (search_step_c w sg cmp a step bound) fuel s) Hvalid) as Hrun.
  rewrite positive_nat_N in Hrun.
  destruct (Cost.value (iterate (search_step_c w sg cmp a step bound) fuel s))
    as [next|t] eqn:Hresult.
  - destruct Hrun as [_ Hbound]; lia.
  - exists t; split; [reflexivity|exact Hrun].
Qed.

(** Fast first failure tests one period and searches its failing prefix with the shared driver. *)
Definition first_failure_fast w sg cmp a step bound : Cost.t (option N) :=
  let* period := period_c w in
  let* count := Floor.mod_count_c w sg cmp a step bound period in
  let* zero := primitive_c (fun _ => count =? 0) in
  if zero then Cost.ret None else
  let* twice := primitive_c (fun _ => N.pos w + 1) in
  let* fuel := primitive_c (fun _ => N.succ_pos twice) in
  let* result := iterate (search_step_c w sg cmp a step bound) fuel (Interval 0 period) in
  Cost.ret (match result with inl _ => None | inr t => Some t end).

(** The fast function agrees with exact search for every width, integer input and outcome. *)
Theorem first_failure_fast_agrees w sg cmp a step bound :
  Cost.value (first_failure_fast w sg cmp a step bound) =
    first_failure w sg cmp a step bound.
Proof.
  unfold first_failure_fast, primitive_c; autorewrite with galois_cost.
  rewrite period_value; autorewrite with galois_cost.
  remember (Cost.value (Floor.mod_count_c w sg cmp a step bound
    (N.pos (word_period w)))) as count eqn:Hvalue.
  change (count = mod_count w sg cmp a step bound (N.pos (word_period w))) in Hvalue.
  destruct (count =? 0) eqn:Hcount.
  - apply N.eqb_eq in Hcount; subst count.
    pose proof (proj1 (mod_count_zero_iff w sg cmp a step bound
      (N.pos (word_period w))) Hcount) as Hall.
    rewrite Cost.value_ret; symmetry.
    apply (proj2 (affine_first_failure_none w sg cmp a step bound)); intro k.
    rewrite affine_test_period; apply Hall.
    apply N.mod_lt; discriminate.
  - apply N.eqb_neq in Hcount; autorewrite with galois_cost.
    assert (Hvalid : valid w sg cmp a step bound (Interval 0 (N.pos (word_period w)))).
    { unfold valid; cbn [lower upper]; split; [lia|]; split; [|lia].
      apply mod_count_zero_iff; intros k Hk; lia. }
    assert (Hrank : rank (Interval 0 (N.pos (word_period w))) <
      N.pos (N.succ_pos (N.pos w + 1))).
    { unfold rank; cbn [lower upper]; rewrite N.sub_0_r, N.succ_pos_spec.
      pose proof (floor_size_mono (N.pred (N.pos (word_period w)))
        (N.pos (word_period w)) (N.le_pred_l _)) as Hsize.
      rewrite period_size in Hsize; lia. }
    destruct (search_terminates w sg cmp a step bound _ _ Hvalid Hrank)
      as [t [Hrun [Hbefore Hfailed]]].
    rewrite Hrun; cbn; symmetry; apply affine_first_failure_complete; assumption.
Qed.

(** A search callback includes all midpoint arithmetic and the actual Euclidean counter. *)
Theorem search_step_cost w sg cmp a step bound s :
  Cost.ticks (search_step_c w sg cmp a step bound s) <= 1000 * (N.pos w + 1) + 5.
Proof.
  unfold search_step_c, primitive_c; autorewrite with galois_cost.
  destruct (upper s - lower s <=? 1); autorewrite with galois_cost; [lia|].
  pose proof (Floor.mod_count_cost w sg cmp a step bound ((lower s + upper s) / 2)).
  lia.
Qed.

(** The search driver charges its callbacks and binary descent using its proved interval rank. *)
Theorem search_cost w sg cmp a step bound fuel s :
  valid w sg cmp a step bound s ->
  Cost.ticks (iterate (search_step_c w sg cmp a step bound) fuel s) <=
    (1000 * (N.pos w + 1) + 7) * (rank s + 1) + 2 * N.pos (Pos.size fuel).
Proof.
  intro Hvalid.
  apply (iterate_cost (search_step_c w sg cmp a step bound)
    (valid w sg cmp a step bound) rank (1000 * (N.pos w + 1) + 5)).
  - intros current Hcurrent; split; [apply search_step_cost|].
    pose proof (search_step_preserved w sg cmp a step bound current Hcurrent) as Hstep.
    destruct (Cost.value (search_step_c w sg cmp a step bound current)); [exact Hstep|].
    exact I.
  - exact Hvalid.
Qed.

Lemma initial_valid w sg cmp a step bound :
  mod_count w sg cmp a step bound (N.pos (word_period w)) <> 0 ->
  valid w sg cmp a step bound (Interval 0 (N.pos (word_period w))).
Proof.
  intro Hpositive; unfold valid; cbn [lower upper].
  split; [lia|]; split; [|lia].
  apply mod_count_zero_iff; intros k Hk; lia.
Qed.

Lemma initial_rank w :
  rank (Interval 0 (N.pos (word_period w))) <= N.pos w + 1.
Proof.
  unfold rank; cbn [lower upper]; rewrite N.sub_0_r.
  pose proof (floor_size_mono (N.pred (N.pos (word_period w)))
    (N.pos (word_period w)) (N.le_pred_l _)) as Hsize.
  rewrite period_size in Hsize; exact Hsize.
Qed.

(** The numeric fast-search bound uses a fixed constant for all widths and all integer inputs. *)
Definition first_failure_fast_k : N := 4000.

(** Each fast branch pays modulus construction, normalization, counts and driver overhead. *)
Theorem first_failure_fast_cost w sg cmp a step bound :
  Cost.ticks (first_failure_fast w sg cmp a step bound) <=
    first_failure_fast_k * (N.pos w + 1) * (N.pos w + 1).
Proof.
  unfold first_failure_fast, primitive_c; autorewrite with galois_cost.
  rewrite period_value.
  pose proof (period_cost w) as Hperiod.
  pose proof (positive_size_le w) as Hwidth.
  pose proof (Floor.mod_count_cost w sg cmp a step bound
    (N.pos (word_period w))) as Hcount.
  destruct (Cost.value (Floor.mod_count_c w sg cmp a step bound
    (N.pos (word_period w))) =? 0) eqn:Hzero; autorewrite with galois_cost.
  - unfold first_failure_fast_k; nia.
  - apply N.eqb_neq in Hzero.
    change (mod_count w sg cmp a step bound (N.pos (word_period w)) <> 0) in Hzero.
    pose proof (search_cost w sg cmp a step bound (N.succ_pos (N.pos w + 1))
      (Interval 0 (N.pos (word_period w)))
      (initial_valid w sg cmp a step bound Hzero)) as Hsearch.
    pose proof (initial_rank w) as Hrank.
    pose proof (positive_size_le (N.succ_pos (N.pos w + 1))) as Hfuel.
    rewrite N.succ_pos_spec in Hfuel.
    destruct (Cost.value (iterate (search_step_c w sg cmp a step bound)
      (N.succ_pos (N.pos w + 1)) (Interval 0 (N.pos (word_period w)))));
      autorewrite with galois_cost; unfold first_failure_fast_k; nia.
Qed.

(** Uniformly in start, step and bound, fast search uses quadratically many primitive operations. *)
Theorem first_failure_fast_bigO sg cmp a step bound :
  bigO (fun w => N.pos w * N.pos w)
    (fun w => Cost.ticks (first_failure_fast w sg cmp a step bound)).
Proof.
  exists (4 * first_failure_fast_k); intro w.
  pose proof (first_failure_fast_cost w sg cmp a step bound).
  nia.
Qed.

(** Fast trip counting changes only the affine first-failure engine. *)
Definition trip_count_fast {V} (inv : V -> Z) (w : width) (sg : signedness) (cmp : cmp_kind)
    (ch : Chrec.t V) (bound : iexpr V) : option N :=
  match ch with
  | Chrec.CRec base (Chrec.CInv step) =>
    Cost.value (first_failure_fast w sg cmp (Chrec.eval inv base O) (eval_iexpr inv step)
      (eval_iexpr inv bound))
  | _ => None
  end.

(** Fast and exact trip counts have the same result on every supported and rejected recurrence. *)
Theorem trip_count_fast_agrees {V} (inv : V -> Z) w sg cmp ch bound :
  trip_count_fast inv w sg cmp ch bound = Failure.trip_count inv w sg cmp ch bound.
Proof.
  destruct ch as [e|base step|base ratio|a b|a b]; try reflexivity.
  destruct step; try reflexivity.
  apply first_failure_fast_agrees.
Qed.

End Trip.
