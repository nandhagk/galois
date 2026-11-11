(** * Euclidean floor sums

    The floor machine transposes a normalized affine staircase at each Euclidean step.
    For example, summing the floors of [0/3; 2/3; 4/3; 6/3] gives three.
    Builds on: CostMonad, CostLoop, BitsWord and AnalysesLoopsFailure. *)

From Stdlib Require Import NArith ZArith List Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Bits Require Import BitsWord.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsFailure.
Import List.ListNotations Cost.Notations Failure.
Local Open Scope N_scope.

Module Floor.

(** The independent reference sum visits each index in its finite prefix. *)
Definition floor_sum_reference (n modulus multiplier offset : N) : N :=
  snd (N.iter n (fun state =>
    let '(index, total) := state in
    (N.succ index, total + (multiplier * index + offset) / modulus)) (0, 0)).

(** The Euclidean state retains its actual update count as a termination witness. *)
Record state : Type := State {
  floor_n : N;
  floor_m : N;
  floor_a : N;
  floor_b : N;
  floor_acc : N;
  floor_done : bool;
  floor_updates : N
}.

(** A primitive arithmetic operation costs one source-level word-RAM tick. *)
Definition primitive_c {A} (f : unit -> A) : Cost.t A :=
  Cost.lift (fun _ => 1) f tt.

(** Each active floor step charges all arithmetic operations, including the update counter. *)
Definition floor_step_c (st : state) : Cost.t state :=
  if floor_done st then Cost.ret st else
  let n := floor_n st in
  let m := floor_m st in
  let a := floor_a st in
  let b := floor_b st in
  let* ar := primitive_c (fun _ => a mod m) in
  let* br := primitive_c (fun _ => b mod m) in
  let* pred := primitive_c (fun _ => N.pred n) in
  let* prod := primitive_c (fun _ => n * pred) in
  let* triangle := primitive_c (fun _ => prod / 2) in
  let* aq := primitive_c (fun _ => a / m) in
  let* first := primitive_c (fun _ => triangle * aq) in
  let* acc1 := primitive_c (fun _ => floor_acc st + first) in
  let* bq := primitive_c (fun _ => b / m) in
  let* second := primitive_c (fun _ => n * bq) in
  let* acc := primitive_c (fun _ => acc1 + second) in
  let* scaled := primitive_c (fun _ => ar * n) in
  let* y := primitive_c (fun _ => scaled + br) in
  let* finished := primitive_c (fun _ => y <? m) in
  let* updates := primitive_c (fun _ => N.succ (floor_updates st)) in
  if finished then Cost.ret (State n m ar br acc true updates) else
  let* q := primitive_c (fun _ => y / m) in
  let* r := primitive_c (fun _ => y mod m) in
  Cost.ret (State q ar m r acc false updates).

(** The plain transition is the value of the charged transition. *)
Definition floor_step (st : state) : state := Cost.value (floor_step_c st).

(** A transition removes quotient contributions and swaps the normalized staircase. *)
Theorem floor_step_equation st :
  floor_step st =
  if floor_done st then st else
  let n := floor_n st in
  let m := floor_m st in
  let a := floor_a st in
  let b := floor_b st in
  let ar := a mod m in
  let br := b mod m in
  let acc := floor_acc st + (n * N.pred n / 2) * (a / m) + n * (b / m) in
  let y := ar * n + br in
  if y <? m then State n m ar br acc true (N.succ (floor_updates st))
  else State (y / m) ar m (y mod m) acc false (N.succ (floor_updates st)).
Proof.
  unfold floor_step, floor_step_c, primitive_c.
  destruct (floor_done st); [reflexivity|].
  autorewrite with galois_cost. destruct (_ <? _); reflexivity.
Qed.

(** One transition charges at most seventeen primitive arithmetic operations. *)
Theorem floor_step_cost st : Cost.ticks (floor_step_c st) <= 17.
Proof.
  unfold floor_step_c, primitive_c.
  destruct (floor_done st); autorewrite with galois_cost; [lia|].
  destruct (_ <? _); autorewrite with galois_cost; lia.
Qed.

(** The shared driver stops on the same transition that sets the completion flag. *)
Definition floor_next_c (st : state) : Cost.t (state + state) :=
  let* next := floor_step_c st in
  Cost.ret (if floor_done next then inr next else inl next).

Lemma floor_next_value st :
  Cost.value (floor_next_c st) =
    if floor_done (floor_step st) then inr (floor_step st) else inl (floor_step st).
Proof.
  reflexivity.
Qed.

(** The executable machine uses the shared binary-fuel driver without a private runner. *)
Definition floor_execute_c fuel st : Cost.t state :=
  let* result := iterate floor_next_c fuel st in
  Cost.ret (match result with inl next => next | inr next => next end).

Lemma floor_size_mono x y : x <= y -> N.size x <= N.size y.
Proof.
  intro Hle.
  destruct (N.eq_dec x 0) as [Hzero | Hpositive].
  - subst; cbn; lia.
  - rewrite !N.size_log2 by lia.
    pose proof (N.log2_le_mono x y Hle); lia.
Qed.

Lemma floor_size_half x y : 2 * x < y -> N.size x < N.size y.
Proof.
  intro Hhalf.
  destruct (N.eq_dec x 0) as [Hzero | Hpositive].
  - subst; cbn [N.size]; rewrite N.size_log2 by lia; lia.
  - pose proof (floor_size_mono (2 * x) y ltac:(lia)) as Hsize.
    rewrite !N.size_log2 in * by nia.
    rewrite N.log2_double in Hsize by lia; lia.
Qed.

Lemma floor_remainder_half m a : 0 < a < m -> 2 * (m mod a) < m.
Proof.
  intros [Hpositive Hless].
  pose proof (N.mod_lt m a ltac:(lia)) as Hremainder.
  pose proof (N.div_mod m a ltac:(lia)) as Hdivision.
  pose proof (N.div_str_pos m a ltac:(lia)) as Hquotient.
  nia.
Qed.

(** The two remainder sizes form the strict Euclidean descent rank. *)
Definition floor_rank (st : state) : N :=
  N.size (floor_m st) + N.size (floor_a st mod floor_m st).

Lemma floor_step_descent st :
  0 < floor_m st -> floor_done st = false ->
  floor_done (floor_step st) = false ->
  0 < floor_m (floor_step st) /\ floor_rank (floor_step st) < floor_rank st.
Proof.
  destruct st as [n m a b acc done updates]; cbn.
  intros Hmod Hdone; subst done.
  rewrite floor_step_equation; cbn.
  destruct (a mod m * n + b mod m <? m) eqn:Htest; cbn; [discriminate|].
  intros _.
  assert (Hremainder : 0 < a mod m < m).
  { pose proof (N.mod_lt a m ltac:(lia)).
    pose proof (N.mod_lt b m ltac:(lia)).
    apply N.ltb_ge in Htest; nia. }
  split; [lia|].
  unfold floor_rank; cbn.
  pose proof (floor_remainder_half m (a mod m) Hremainder) as Hhalf.
  pose proof (floor_size_half (m mod (a mod m)) m Hhalf); lia.
Qed.

Lemma floor_done_step st : floor_done st = true -> floor_step st = st.
Proof.
  intro Hdone; rewrite floor_step_equation, Hdone; reflexivity.
Qed.

Lemma floor_done_iter fuel st : floor_done st = true -> N.iter fuel floor_step st = st.
Proof.
  intro Hdone; induction fuel using N.peano_ind.
  - reflexivity.
  - rewrite N.iter_succ, IHfuel; apply floor_done_step; exact Hdone.
Qed.

Lemma floor_rank_finishes fuel : forall st,
  0 < floor_m st -> floor_rank st < fuel ->
  floor_done (N.iter fuel floor_step st) = true.
Proof.
  induction fuel using N.peano_ind; intros st Hmod Hrank; [lia|].
  destruct (floor_done st) eqn:Hdone.
  - rewrite floor_done_iter by exact Hdone; exact Hdone.
  - rewrite N.iter_succ_r.
    destruct (floor_done (floor_step st)) eqn:Hnext.
    + rewrite floor_done_iter by exact Hnext; exact Hnext.
    + destruct (floor_step_descent st Hmod Hdone Hnext) as [Hmodnext Hdecrease].
      apply IHfuel; lia.
Qed.

Lemma floor_runs_agrees n st result :
  runs floor_next_c n st result ->
  (match result with inl next => next | inr next => next end) =
    N.iter (N.of_nat n) floor_step st.
Proof.
  intro Hrun; induction Hrun as [st|n st r Hstop|n st next result Hnext Hrun IH].
  - reflexivity.
  - rewrite floor_next_value in Hstop.
    destruct (floor_done (floor_step st)) eqn:Hdone; [|discriminate].
    injection Hstop as Heq; subst r.
    rewrite Nat2N.inj_succ, N.iter_succ_r, floor_done_iter by exact Hdone.
    reflexivity.
  - rewrite floor_next_value in Hnext.
    destruct (floor_done (floor_step st)); [discriminate|].
    injection Hnext as Heq; subst next.
    rewrite Nat2N.inj_succ, N.iter_succ_r; exact IH.
Qed.

(** Early stopping and padded mathematical iteration reach the same final state. *)
Theorem floor_execute_value fuel st :
  Cost.value (floor_execute_c fuel st) = N.iter (N.pos fuel) floor_step st.
Proof.
  unfold floor_execute_c; autorewrite with galois_cost.
  pose proof (floor_runs_agrees _ _ _ (iterate_value floor_next_c fuel st)) as Hrun.
  rewrite positive_nat_N in Hrun; exact Hrun.
Qed.

(** Binary size preparation charges each visited digit. *)
Fixpoint positive_size_c (p : positive) : Cost.t N :=
  Cost.step ;;
  match p with
  | xH => Cost.ret 1
  | xO q | xI q =>
    let* bits := positive_size_c q in
    primitive_c (fun _ => N.succ bits)
  end.

Lemma positive_size_value p : Cost.value (positive_size_c p) = N.pos (Pos.size p).
Proof.
  induction p as [p IH|p IH|]; cbn [positive_size_c];
    unfold primitive_c; autorewrite with galois_cost; try rewrite IH; reflexivity.
Qed.

(** Counted floor summation prepares its fuel and runs the actual Euclidean machine. *)
Definition floor_sum_counted_c (n m a b : N) : Cost.t (N * N * bool) :=
  let* zero := primitive_c (fun _ => m =? 0) in
  if zero then Cost.ret (0, 0, false) else
  let* bits := match m with
    | N0 => Cost.ret 0
    | Npos p => positive_size_c p
    end in
  let* twice := primitive_c (fun _ => 2 * bits) in
  let* budget := primitive_c (fun _ => N.succ_pos twice) in
  let* final := floor_execute_c budget (State n m a b 0 false 0) in
  Cost.ret (floor_acc final, floor_updates final, floor_done final).

(** The counted value records the sum, actual active updates and completion flag. *)
Definition floor_sum_counted n m a b := Cost.value (floor_sum_counted_c n m a b).

(** The charged machine exposes its mathematical iteration equation for proofs. *)
Theorem floor_sum_counted_equation n m a b :
  floor_sum_counted n m a b =
  if m =? 0 then (0, 0, false) else
  let final := N.iter (2 * N.size m + 1) floor_step (State n m a b 0 false 0) in
  (floor_acc final, floor_updates final, floor_done final).
Proof.
  unfold floor_sum_counted, floor_sum_counted_c, primitive_c.
  autorewrite with galois_cost.
  destruct m as [|p]; [reflexivity|].
  cbn [N.eqb]. rewrite Cost.value_bind, positive_size_value.
  autorewrite with galois_cost.
  rewrite floor_execute_value, N.succ_pos_spec, N.add_1_r; reflexivity.
Qed.

(** Floor summation returns the accumulator of the actual charged machine. *)
Definition floor_sum_fast_c n m a b : Cost.t N :=
  let* result := floor_sum_counted_c n m a b in
  let '(sum, _, _) := result in Cost.ret sum.

(** The plain fast sum is the value projection of its costed implementation. *)
Definition floor_sum_fast n m a b := Cost.value (floor_sum_fast_c n m a b).

Lemma floor_sum_fast_equation n m a b :
  floor_sum_fast n m a b = let '(sum, _, _) := floor_sum_counted n m a b in sum.
Proof.
  unfold floor_sum_fast, floor_sum_fast_c.
  rewrite Cost.value_bind; fold (floor_sum_counted n m a b).
  destruct (floor_sum_counted n m a b) as [[sum updates] done]; reflexivity.
Qed.

Lemma floor_updates_step st : floor_updates (floor_step st) <= N.succ (floor_updates st).
Proof.
  destruct st as [n m a b acc done updates].
  rewrite floor_step_equation; cbn.
  destruct done; cbn; [lia|].
  destruct (a mod m * n + b mod m <? m); cbn; lia.
Qed.

Lemma floor_updates_iter fuel st :
  floor_updates (N.iter fuel floor_step st) <= floor_updates st + fuel.
Proof.
  induction fuel using N.peano_ind.
  - cbn; lia.
  - rewrite N.iter_succ.
    pose proof (floor_updates_step (N.iter fuel floor_step st)); lia.
Qed.

(** Positive-modulus execution finishes within twice the modulus size plus one active steps. *)
Theorem floor_sum_terminates n m a b :
  0 < m ->
  let '(_, steps, done) := floor_sum_counted n m a b in
  done = true /\ steps <= 2 * N.size m + 1.
Proof.
  intro Hmod; rewrite floor_sum_counted_equation.
  destruct (m =? 0) eqn:Hzero; [apply N.eqb_eq in Hzero; lia|].
  split.
  - apply floor_rank_finishes; cbn; [exact Hmod|].
    unfold floor_rank; cbn.
    change (N.size m + N.size (a mod m) < 2 * N.size m + 1).
    pose proof (N.mod_lt a m ltac:(lia)).
    pose proof (floor_size_mono (a mod m) m ltac:(lia)); lia.
  - pose proof (floor_updates_iter (2 * N.size m + 1)
      (State n m a b 0 false 0)) as Hupdates; exact Hupdates.
Qed.

(** A zero modulus follows the explicit zero-result branch. *)
Theorem floor_sum_zero n a b : floor_sum_fast n 0 a b = 0.
Proof.
  reflexivity.
Qed.

(** The accumulator and remaining affine rectangle bound all live arithmetic values. *)
Definition floor_potential (st : state) : N :=
  floor_acc st + floor_n st * floor_n st * floor_a st + floor_n st * floor_b st.

Lemma floor_triangle_bound n : n * N.pred n / 2 <= n * n.
Proof.
  apply N.Div0.div_le_upper_bound.
  pose proof (N.le_pred_l n); nia.
Qed.

Lemma floor_rectangle_bound n m a b y q r :
  y = a * n + b -> y = m * q + r -> q <= n ->
  q * q * m + q * r <= n * n * a + n * b.
Proof.
  intros Hy Hdivision Hq.
  replace (q * q * m + q * r) with (q * (m * q + r)) by ring.
  rewrite <- Hdivision, Hy.
  replace (n * n * a + n * b) with (n * (a * n + b)) by ring.
  apply N.mul_le_mono_r; exact Hq.
Qed.

Lemma floor_step_potential st : 0 < floor_m st ->
  floor_potential (floor_step st) <= floor_potential st.
Proof.
  destruct st as [n m a b acc done updates]; cbn; intro Hmod.
  rewrite floor_step_equation; cbn; destruct done; [reflexivity|].
  pose proof (N.div_mod a m ltac:(lia)) as Ha.
  pose proof (N.div_mod b m ltac:(lia)) as Hb.
  pose proof (N.mod_lt a m ltac:(lia)) as Har.
  pose proof (N.mod_lt b m ltac:(lia)) as Hbr.
  pose proof (floor_triangle_bound n) as Htriangle.
  assert (Hfirst : n * N.pred n / 2 * (a / m) <= n * n * (a / m)).
  { apply N.mul_le_mono_r; exact Htriangle. }
  assert (Hmul_a : a / m <= m * (a / m)).
  { replace (a / m) with (1 * (a / m)) at 1 by lia.
    apply N.mul_le_mono_r; lia. }
  assert (Hsplit_a : a / m + a mod m <= a) by lia.
  assert (Hmul_b : b / m <= m * (b / m)).
  { replace (b / m) with (1 * (b / m)) at 1 by lia.
    apply N.mul_le_mono_r; lia. }
  assert (Hsplit_b : b / m + b mod m <= b) by lia.
  assert (Hcharge : n * N.pred n / 2 * (a / m) + n * (b / m) +
      n * n * (a mod m) + n * (b mod m) <= n * n * a + n * b) by nia.
  destruct (a mod m * n + b mod m <? m) eqn:Htest.
  - unfold floor_potential; cbn; nia.
  - assert (Hnext : (a mod m * n + b mod m) / m <= n).
    { apply N.lt_succ_r, N.Div0.div_lt_upper_bound; nia. }
    pose proof (N.div_mod (a mod m * n + b mod m) m ltac:(lia)) as Hy.
    pose proof (floor_rectangle_bound n m (a mod m) (b mod m)
      (a mod m * n + b mod m) ((a mod m * n + b mod m) / m)
      ((a mod m * n + b mod m) mod m) eq_refl Hy Hnext) as Hrectangle.
    unfold floor_potential; cbn; nia.
Qed.

(** The live-state invariant bounds fields independently of the number of padded steps. *)
Definition floor_live_bound n m a b (st : state) : Prop :=
  0 < floor_m st /\ floor_n st <= n /\ floor_m st <= m /\
  floor_a st <= a + m /\ floor_b st <= b + m /\
  floor_potential st <= n * n * a + n * b.

Lemma floor_live_step n m a b st :
  floor_live_bound n m a b st -> floor_live_bound n m a b (floor_step st).
Proof.
  intros [Hmod [Hn [Hm [Ha [Hb Hpotential]]]]].
  pose proof (floor_step_potential st Hmod) as Hdecrease.
  pose proof (N.le_trans _ _ _ Hdecrease Hpotential) as Hnextpotential.
  destruct st as [sn sm sa sb acc done updates]; cbn in *.
  rewrite floor_step_equation in Hnextpotential |- *; cbn in Hnextpotential |- *.
  destruct done.
  - unfold floor_live_bound; cbn; repeat split; assumption.
  - pose proof (N.mod_lt sa sm ltac:(lia)) as Har.
    pose proof (N.mod_lt sb sm ltac:(lia)) as Hbr.
    destruct (sa mod sm * sn + sb mod sm <? sm) eqn:Htest.
    + unfold floor_live_bound; cbn; repeat split; try lia.
    + apply N.ltb_ge in Htest.
      pose proof (N.div_mod (sa mod sm * sn + sb mod sm) sm ltac:(lia)) as Hy.
      assert (Hq : (sa mod sm * sn + sb mod sm) / sm <= sn).
      { apply N.lt_succ_r, N.Div0.div_lt_upper_bound; nia. }
      pose proof (N.mod_lt (sa mod sm * sn + sb mod sm) sm ltac:(lia)) as Hr.
      unfold floor_live_bound; cbn; repeat split; try nia.
Qed.

Lemma floor_live_iter n m a b k : 0 < m ->
  floor_live_bound n m a b (N.iter k floor_step (State n m a b 0 false 0)).
Proof.
  intro Hmod; apply N.iter_invariant.
  - apply floor_live_step.
  - unfold floor_live_bound, floor_potential; cbn; repeat split; lia.
Qed.

Lemma floor_size_bound x bits : x < 2 ^ bits -> N.size x <= bits.
Proof.
  intro Hbound.
  destruct (N.eq_dec x 0) as [Hzero | Hnonzero].
  - subst; cbn; lia.
  - rewrite N.size_log2 by exact Hnonzero.
    apply N.log2_lt_pow2 in Hbound; lia.
Qed.

Lemma floor_size_mul x y : N.size (x * y) <= N.size x + N.size y.
Proof.
  apply floor_size_bound; rewrite N.pow_add_r.
  pose proof (N.size_gt x); pose proof (N.size_gt y); nia.
Qed.

Lemma floor_size_add x y : N.size (x + y) <= N.size x + N.size y + 1.
Proof.
  apply floor_size_bound; rewrite !N.pow_add_r; cbn [N.pow].
  pose proof (N.size_gt x); pose proof (N.size_gt y); nia.
Qed.

(** Live-bit size includes every arithmetic field used by the staircase invariant. *)
Definition floor_state_bits (st : state) : N :=
  N.size (floor_n st) + N.size (floor_m st) + N.size (floor_a st) +
    N.size (floor_b st) + N.size (floor_acc st).

(** Every initialized execution has bounded live bits even when padded after completion. *)
Theorem floor_sum_live_bits n m a b k : 0 < m ->
  floor_state_bits (N.iter k floor_step (State n m a b 0 false 0)) <=
    10 * (N.size n + N.size m + N.size a + N.size b + 1).
Proof.
  intro Hmod; pose proof (floor_live_iter n m a b k Hmod) as Hlive.
  destruct (N.iter k floor_step (State n m a b 0 false 0))
    as [sn sm sa sb acc done updates].
  destruct Hlive as [Hpositive [Hn [Hm [Ha [Hb Hacc]]]]].
  unfold floor_potential in Hacc; cbn in *.
  pose proof (floor_size_mono sn n Hn).
  pose proof (floor_size_mono sm m Hm).
  pose proof (floor_size_mono sa (a + m) Ha).
  pose proof (floor_size_mono sb (b + m) Hb).
  pose proof (floor_size_mono acc (n * n * a + n * b) ltac:(nia)).
  pose proof (floor_size_add a m); pose proof (floor_size_add b m).
  pose proof (floor_size_add (n * n * a) (n * b)).
  pose proof (floor_size_mul (n * n) a); pose proof (floor_size_mul n n).
  pose proof (floor_size_mul n b).
  unfold floor_state_bits; cbn.
  change (N.size sn + N.size sm + N.size sa + N.size sb + N.size acc <=
    10 * (N.size n + N.size m + N.size a + N.size b + 1)).
  lia.
Qed.

(** The proof model sums arbitrary terms without changing the executable floor producer. *)
Definition floor_total (f : N -> N) (n : N) : N :=
  snd (N.iter n (fun state : N * N =>
    (N.succ (fst state), snd state + f (fst state))) (0, 0)).

Lemma floor_total_index f n :
  fst (N.iter n (fun state : N * N =>
    (N.succ (fst state), snd state + f (fst state))) (0, 0)) = n.
Proof.
  induction n using N.peano_ind; [reflexivity|].
  rewrite N.iter_succ; cbn; rewrite IHn; reflexivity.
Qed.

Lemma floor_total_zero f : floor_total f 0 = 0.
Proof.
  reflexivity.
Qed.

Lemma floor_total_succ f n : floor_total f (N.succ n) = floor_total f n + f n.
Proof.
  unfold floor_total at 1; rewrite N.iter_succ; cbn.
  rewrite floor_total_index; reflexivity.
Qed.

Lemma floor_total_ext f g n :
  (forall i, i < n -> f i = g i) -> floor_total f n = floor_total g n.
Proof.
  induction n using N.peano_ind; intro Hequal; [reflexivity|].
  rewrite !floor_total_succ, IHn; [rewrite Hequal by lia; reflexivity|].
  intros i Hi; apply Hequal; lia.
Qed.

Lemma floor_total_add f g n :
  floor_total (fun i => f i + g i) n = floor_total f n + floor_total g n.
Proof.
  induction n using N.peano_ind; [reflexivity|].
  rewrite !floor_total_succ, IHn; lia.
Qed.

Lemma floor_total_scale f n c :
  floor_total (fun i => c * f i) n = c * floor_total f n.
Proof.
  induction n using N.peano_ind; [rewrite !floor_total_zero; lia|].
  rewrite !floor_total_succ, IHn; ring.
Qed.

Lemma floor_total_constant n c : floor_total (fun _ => c) n = n * c.
Proof.
  induction n using N.peano_ind; [reflexivity|].
  rewrite floor_total_succ, IHn; nia.
Qed.

Lemma floor_total_shift f n :
  floor_total f (N.succ n) = f 0 + floor_total (fun i => f (N.succ i)) n.
Proof.
  induction n using N.peano_ind.
  - rewrite floor_total_succ, !floor_total_zero; lia.
  - rewrite floor_total_succ, IHn, floor_total_succ; lia.
Qed.

Lemma floor_triangle_succ n :
  N.succ n * N.pred (N.succ n) / 2 = n * N.pred n / 2 + n.
Proof.
  destruct (N.eq_dec n 0) as [Hzero | Hnonzero]; [subst; reflexivity|].
  replace (N.succ n * N.pred (N.succ n)) with (n * N.pred n + n * 2)
    by (pose proof (N.succ_pred n Hnonzero); rewrite N.pred_succ; nia).
  apply N.div_add; discriminate.
Qed.

Lemma floor_total_indices n : floor_total (fun i => i) n = n * N.pred n / 2.
Proof.
  induction n using N.peano_ind; [reflexivity|].
  rewrite floor_total_succ, IHn, floor_triangle_succ; reflexivity.
Qed.

Lemma floor_reference_total n m a b :
  floor_sum_reference n m a b = floor_total (fun i => (a * i + b) / m) n.
Proof.
  unfold floor_sum_reference, floor_total; f_equal.
  induction n using N.peano_ind; [reflexivity|].
  rewrite !N.iter_succ, IHn.
  destruct (N.iter n
    (fun state : N * N => (N.succ (fst state), snd state + (a * fst state + b) / m))
    (0, 0)); reflexivity.
Qed.

Lemma floor_reference_succ n m a b :
  floor_sum_reference (N.succ n) m a b = floor_sum_reference n m a b + (a * n + b) / m.
Proof.
  rewrite !floor_reference_total; exact (floor_total_succ (fun i => (a * i + b) / m) n).
Qed.

Lemma floor_reference_offset n m a b : 0 < m ->
  floor_sum_reference n m a (b + m) = floor_sum_reference n m a b + n.
Proof.
  intro Hmod; rewrite !floor_reference_total.
  transitivity (floor_total (fun i => (a * i + b) / m + 1) n).
  - apply floor_total_ext; intros i Hi.
    replace (a * i + (b + m)) with ((a * i + b) + 1 * m) by ring.
    apply N.div_add; lia.
  - rewrite floor_total_add, floor_total_constant; lia.
Qed.

Lemma floor_reference_head n m a b :
  floor_sum_reference (N.succ n) m a b = b / m + floor_sum_reference n m a (a + b).
Proof.
  rewrite !floor_reference_total, floor_total_shift; cbn [N.mul N.add].
  replace (a * 0 + b) with b by ring.
  f_equal; apply floor_total_ext; intros i Hi; f_equal; nia.
Qed.

Lemma floor_reference_normalize n m a b : 0 < m ->
  floor_sum_reference n m a b =
    (n * N.pred n / 2) * (a / m) + n * (b / m) +
    floor_sum_reference n m (a mod m) (b mod m).
Proof.
  intro Hmod; rewrite !floor_reference_total.
  assert (Hterm : forall i,
    (a * i + b) / m =
      (a / m) * i + b / m + ((a mod m) * i + b mod m) / m).
  { intro i.
    pose proof (N.div_mod a m ltac:(lia)) as Ha.
    pose proof (N.div_mod b m ltac:(lia)) as Hb.
    replace (a * i + b) with
      ((a mod m * i + b mod m) + (a / m * i + b / m) * m) by nia.
    rewrite N.div_add by lia; lia. }
  transitivity (floor_total
    (fun i => (a / m) * i + b / m + ((a mod m) * i + b mod m) / m) n).
  - apply floor_total_ext; intros; apply Hterm.
  - rewrite !floor_total_add, floor_total_constant.
    rewrite floor_total_scale, floor_total_indices; ring.
Qed.

Lemma floor_divmod y m q r : r < m -> y = m * q + r ->
  y / m = q /\ y mod m = r.
Proof.
  intros Hremainder Hdivision; split; symmetry.
  - apply (N.div_unique y m q r); assumption.
  - apply (N.mod_unique y m q r); assumption.
Qed.

Lemma floor_reference_reciprocal n m a b : 0 < a < m -> b < m ->
  floor_sum_reference n m a b =
    floor_sum_reference ((a * n + b) / m) a m ((a * n + b) mod m).
Proof.
  intros [Ha Hmod] Hb; induction n using N.peano_ind.
  - change (0 = floor_sum_reference ((a * 0 + b) / m) a m ((a * 0 + b) mod m)).
    replace (a * 0 + b) with b by ring.
    rewrite N.div_small by exact Hb; reflexivity.
  - rewrite floor_reference_succ, IHn.
    set (q := (a * n + b) / m); set (r := (a * n + b) mod m).
    pose proof (N.div_mod (a * n + b) m ltac:(lia)) as Hy.
    pose proof (N.mod_lt (a * n + b) m ltac:(lia)) as Hr.
    change (a * n + b = m * q + r) in Hy; change (r < m) in Hr.
    destruct (N.lt_ge_cases (r + a) m) as [Hsmall | Hcarry].
    + destruct (floor_divmod (a * N.succ n + b) m q (r + a) Hsmall ltac:(nia))
        as [Hquotient Hremainder].
      rewrite Hquotient, Hremainder.
      rewrite floor_reference_offset by exact Ha; reflexivity.
    + assert (Hresidue : r + a - m < a) by lia.
      destruct (floor_divmod (a * N.succ n + b) m (N.succ q) (r + a - m)
        ltac:(lia) ltac:(nia)) as [Hquotient Hremainder].
      rewrite Hquotient, Hremainder, floor_reference_head.
      rewrite N.div_small by exact Hresidue.
      replace (m + (r + a - m)) with (r + a) by lia.
      rewrite floor_reference_offset by exact Ha; lia.
Qed.

Lemma floor_reference_small n m a b : a * n + b < m ->
  floor_sum_reference n m a b = 0.
Proof.
  intro Hsmall; rewrite floor_reference_total.
  transitivity (floor_total (fun _ => 0) n).
  - apply floor_total_ext; intros i Hi; apply N.div_small; nia.
  - rewrite floor_total_constant; lia.
Qed.

(** The accumulator plus the remaining staircase is the semantic value of a floor state. *)
Definition floor_value (st : state) : N :=
  floor_acc st + floor_sum_reference (floor_n st) (floor_m st) (floor_a st) (floor_b st).

Lemma floor_value_step st : 0 < floor_m st -> floor_value (floor_step st) = floor_value st.
Proof.
  destruct st as [n m a b acc done updates]; cbn; intro Hmod.
  rewrite floor_step_equation; cbn; destruct done; [reflexivity|].
  pose proof (floor_reference_normalize n m a b Hmod) as Hnormalize.
  destruct (a mod m * n + b mod m <? m) eqn:Htest.
  - unfold floor_value; cbn; lia.
  - apply N.ltb_ge in Htest.
    pose proof (N.mod_lt a m ltac:(lia)) as Har.
    pose proof (N.mod_lt b m ltac:(lia)) as Hbr.
    assert (Hpositive : 0 < a mod m) by nia.
    pose proof (floor_reference_reciprocal n m (a mod m) (b mod m)
      ltac:(lia) Hbr) as Hswap.
    unfold floor_value; cbn; lia.
Qed.

Lemma floor_done_remainder_step st : 0 < floor_m st ->
  (floor_done st = true ->
    floor_sum_reference (floor_n st) (floor_m st) (floor_a st) (floor_b st) = 0) ->
  floor_done (floor_step st) = true ->
  floor_sum_reference (floor_n (floor_step st)) (floor_m (floor_step st))
    (floor_a (floor_step st)) (floor_b (floor_step st)) = 0.
Proof.
  destruct st as [n m a b acc done updates]; cbn; intros Hmod Hdone.
  rewrite !floor_step_equation; cbn; destruct done.
  - intros _; apply Hdone; reflexivity.
  - destruct (a mod m * n + b mod m <? m) eqn:Htest; cbn; [intros _|discriminate].
    apply floor_reference_small, N.ltb_lt; exact Htest.
Qed.

(** The invariant couples the accumulator and completion flag to the same reference sum. *)
Definition floor_semantic_bound n m a b (st : state) : Prop :=
  floor_live_bound n m a b st /\
  floor_value st = floor_sum_reference n m a b /\
  (floor_done st = true ->
    floor_sum_reference (floor_n st) (floor_m st) (floor_a st) (floor_b st) = 0).

Lemma floor_semantic_step n m a b st :
  floor_semantic_bound n m a b st -> floor_semantic_bound n m a b (floor_step st).
Proof.
  intros [Hlive [Hvalue Hdone]].
  assert (Hmod : 0 < floor_m st) by (destruct Hlive; assumption).
  split; [apply floor_live_step; exact Hlive|]; split.
  - rewrite floor_value_step by exact Hmod; exact Hvalue.
  - apply floor_done_remainder_step; assumption.
Qed.

Lemma floor_semantic_iter n m a b k : 0 < m ->
  floor_semantic_bound n m a b (N.iter k floor_step (State n m a b 0 false 0)).
Proof.
  intro Hmod; apply N.iter_invariant.
  - apply floor_semantic_step.
  - split; [apply (floor_live_iter n m a b 0 Hmod)|].
    split; [reflexivity|discriminate].
Qed.

(** The actual Euclidean machine equals the independent term-by-term sum for positive moduli. *)
Theorem floor_sum_fast_correct n m a b : 0 < m ->
  floor_sum_fast n m a b = floor_sum_reference n m a b.
Proof.
  intro Hmod.
  pose proof (floor_sum_terminates n m a b Hmod) as Htermination.
  pose proof (floor_semantic_iter n m a b (2 * N.size m + 1) Hmod) as Hsemantic.
  rewrite floor_sum_fast_equation, floor_sum_counted_equation.
  rewrite floor_sum_counted_equation in Htermination.
  destruct (m =? 0) eqn:Hzero; [apply N.eqb_eq in Hzero; lia|].
  destruct (N.iter (2 * N.size m + 1) floor_step (State n m a b 0 false 0))
    as [sn sm sa sb acc done updates].
  destruct Htermination as [Hdone Hupdates].
  destruct Hsemantic as [Hlive [Hvalue Hremainder]].
  unfold floor_value in Hvalue; cbn in *.
  rewrite Hremainder in Hvalue by exact Hdone; lia.
Qed.

(** The binary digit count is bounded by the positive numeral's numeric value. *)
Lemma positive_size_le p : N.pos (Pos.size p) <= N.pos p.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size].
  - change (N.succ (N.pos (Pos.size p)) <= N.pos (xI p)).
    rewrite binary_length_odd; lia.
  - change (N.succ (N.pos (Pos.size p)) <= N.pos (xO p)).
    rewrite binary_length_even; lia.
  - reflexivity.
Qed.

Lemma positive_size_cost p :
  Cost.ticks (positive_size_c p) <= 2 * N.pos (Pos.size p).
Proof.
  induction p as [p IH|p IH|]; cbn [positive_size_c];
    unfold primitive_c; autorewrite with galois_cost.
  - change (1 + (Cost.ticks (positive_size_c p) + 1) <=
      2 * N.succ (N.pos (Pos.size p))); lia.
  - change (1 + (Cost.ticks (positive_size_c p) + 1) <=
      2 * N.succ (N.pos (Pos.size p))); lia.
  - cbn; lia.
Qed.

Lemma floor_next_cost st : Cost.ticks (floor_next_c st) <= 17.
Proof.
  unfold floor_next_c; autorewrite with galois_cost.
  pose proof (floor_step_cost st); lia.
Qed.

Lemma floor_next_descent st : 0 < floor_m st ->
  match Cost.value (floor_next_c st) with
  | inl next => 0 < floor_m next /\ floor_rank next < floor_rank st
  | inr _ => True
  end.
Proof.
  intro Hmod; rewrite floor_next_value.
  destruct (floor_done (floor_step st)) eqn:Hnext; [exact I|].
  assert (Hdone : floor_done st = false).
  { destruct (floor_done st) eqn:Hdone; [|reflexivity].
    rewrite floor_done_step in Hnext by exact Hdone; congruence. }
  exact (floor_step_descent st Hmod Hdone Hnext).
Qed.

(** The actual floor runner pays its primitive work and the shared driver's binary overhead. *)
Theorem floor_execute_cost fuel st : 0 < floor_m st ->
  Cost.ticks (floor_execute_c fuel st) <=
    19 * (floor_rank st + 1) + 2 * N.pos (Pos.size fuel).
Proof.
  intro Hmod; unfold floor_execute_c; autorewrite with galois_cost.
  pose proof (iterate_cost floor_next_c (fun s => 0 < floor_m s) floor_rank 17 fuel st)
    as Hcost.
  assert (Hstep : forall s, 0 < floor_m s ->
    Cost.ticks (floor_next_c s) <= 17 /\
    match Cost.value (floor_next_c s) with
    | inl next => 0 < floor_m next /\ floor_rank next < floor_rank s
    | inr _ => True
    end).
  { intros s Hs; split; [apply floor_next_cost|apply floor_next_descent; exact Hs]. }
  specialize (Hcost Hstep Hmod); lia.
Qed.

(** All floor work, including fuel preparation, has a linear source-arithmetic bound. *)
Theorem floor_sum_fast_cost n m a b :
  Cost.ticks (floor_sum_fast_c n m a b) <= 100 * (N.size m + 1).
Proof.
  unfold floor_sum_fast_c; rewrite Cost.ticks_bind.
  destruct (Cost.value (floor_sum_counted_c n m a b)) as [[sum updates] done].
  rewrite Cost.ticks_ret, N.add_0_r.
  unfold floor_sum_counted_c, primitive_c; autorewrite with galois_cost.
  destruct m as [|p]; [cbn; lia|].
  cbn [N.eqb]; autorewrite with galois_cost.
  rewrite positive_size_value.
  pose proof (positive_size_cost p) as Hsize.
  pose proof (floor_execute_cost (N.succ_pos (2 * N.pos (Pos.size p)))
    (State n (N.pos p) a b 0 false 0) ltac:(cbn; lia)) as Hrun.
  pose proof (positive_size_le (N.succ_pos (2 * N.pos (Pos.size p)))) as Hfuel.
  rewrite N.succ_pos_spec in Hfuel.
  assert (Hrank : floor_rank (State n (N.pos p) a b 0 false 0) <=
    2 * N.pos (Pos.size p)).
  { unfold floor_rank; cbn [floor_m floor_a].
    pose proof (N.mod_lt a (N.pos p) ltac:(lia)) as Hmod.
    pose proof (floor_size_mono (a mod N.pos p) (N.pos p) ltac:(lia)) as Hbound.
    change (N.pos (Pos.size p) + N.size (a mod N.pos p) <=
      2 * N.pos (Pos.size p)); change (N.size (a mod N.pos p) <=
      N.pos (Pos.size p)) in Hbound; lia. }
  change (1 + (Cost.ticks (positive_size_c p) + (1 + (1 +
    (Cost.ticks (floor_execute_c (N.succ_pos (2 * N.pos (Pos.size p)))
      (State n (N.pos p) a b 0 false 0)) + 0)))) <=
    100 * (N.pos (Pos.size p) + 1)).
  lia.
Qed.

(** Threshold counting subtracts two actual floor sums and charges its affine offset. *)
Definition count_ge_c (n m a b threshold : N) : Cost.t N :=
  let* plus := primitive_c (fun _ => b + m) in
  let* offset := primitive_c (fun _ => plus - threshold) in
  let* upper := floor_sum_fast_c n m a offset in
  let* lower := floor_sum_fast_c n m a b in
  primitive_c (fun _ => upper - lower).

(** Threshold counting is the value of the charged floor-sum difference. *)
Definition count_ge n m a b threshold := Cost.value (count_ge_c n m a b threshold).

Lemma count_ge_equation n m a b threshold :
  count_ge n m a b threshold =
    floor_sum_fast n m a (b + m - threshold) - floor_sum_fast n m a b.
Proof.
  unfold count_ge, count_ge_c, primitive_c; autorewrite with galois_cost; reflexivity.
Qed.

Lemma floor_threshold_term m a b threshold i : 0 < m -> threshold <= m ->
  (a * i + (b + m - threshold)) / m =
    (a * i + b) / m + (if threshold <=? (a * i + b) mod m then 1 else 0).
Proof.
  intros Hmod Hthreshold.
  set (q := (a * i + b) / m); set (r := (a * i + b) mod m).
  pose proof (N.div_mod (a * i + b) m ltac:(lia)) as Hdivision.
  pose proof (N.mod_lt (a * i + b) m ltac:(lia)) as Hremainder.
  change (a * i + b = m * q + r) in Hdivision; change (r < m) in Hremainder.
  destruct (threshold <=? r) eqn:Htest.
  - apply N.leb_le in Htest.
    destruct (floor_divmod (a * i + (b + m - threshold)) m (q + 1) (r - threshold)
      ltac:(lia) ltac:(nia)) as [Hquotient _]; exact Hquotient.
  - apply N.leb_gt in Htest.
    destruct (floor_divmod (a * i + (b + m - threshold)) m q (r + m - threshold)
      ltac:(lia) ltac:(nia)) as [Hquotient _].
    rewrite Hquotient; lia.
Qed.

Lemma floor_ge_total n m a b threshold : 0 < m -> threshold <= m ->
  count_ge n m a b threshold =
    floor_total (fun i => if threshold <=? (a * i + b) mod m then 1 else 0) n.
Proof.
  intros Hmod Hthreshold; rewrite count_ge_equation.
  rewrite !floor_sum_fast_correct by exact Hmod; rewrite !floor_reference_total.
  assert (Hsum : floor_total (fun i => (a * i + (b + m - threshold)) / m) n =
    floor_total (fun i => (a * i + b) / m +
      (if threshold <=? (a * i + b) mod m then 1 else 0)) n).
  { apply floor_total_ext; intros; apply floor_threshold_term; assumption. }
  rewrite Hsum, floor_total_add; lia.
Qed.

Lemma floor_indicator_difference r t :
  (if t <=? r then 1 else 0) =
    (if N.succ t <=? r then 1 else 0) + (if r =? t then 1 else 0).
Proof.
  destruct (N.leb_spec0 t r); destruct (N.leb_spec0 (N.succ t) r);
    destruct (N.eqb_spec r t); lia.
Qed.

Lemma floor_ge_difference n m a b t : 0 < m -> N.succ t <= m ->
  count_ge n m a b t - count_ge n m a b (N.succ t) =
    floor_total (fun i => if (a * i + b) mod m =? t then 1 else 0) n.
Proof.
  intros Hmod Hthreshold; rewrite !floor_ge_total by lia.
  assert (Hsum :
    floor_total (fun i => if t <=? (a * i + b) mod m then 1 else 0) n =
    floor_total (fun i =>
      (if N.succ t <=? (a * i + b) mod m then 1 else 0) +
      (if (a * i + b) mod m =? t then 1 else 0)) n).
  { apply floor_total_ext; intros; apply floor_indicator_difference. }
  rewrite Hsum, floor_total_add; lia.
Qed.

(** Power-of-two preparation uses repeated squaring with charged primitive multiplications. *)
Fixpoint period_c (w : width) : Cost.t N :=
  Cost.step ;;
  match w with
  | xH => Cost.ret 2
  | xO p =>
    let* half := period_c p in primitive_c (fun _ => half * half)
  | xI p =>
    let* half := period_c p in
    let* square := primitive_c (fun _ => half * half) in
    primitive_c (fun _ => 2 * square)
  end.

(** Prepared powers of two equal the exact search's word period. *)
Theorem period_value w : Cost.value (period_c w) = N.pos (word_period w).
Proof.
  assert (Hpow : forall p, Z.of_N (Cost.value (period_c p)) = (2 ^ Z.pos p)%Z).
  { intro p; induction p as [p IH|p IH|]; cbn [period_c];
      unfold primitive_c; autorewrite with galois_cost.
    - rewrite !N2Z.inj_mul, IH.
      replace (Z.pos (xI p)) with (1 + (Z.pos p + Z.pos p))%Z by lia.
      rewrite !Z.pow_add_r by lia; reflexivity.
    - rewrite N2Z.inj_mul, IH.
      replace (Z.pos (xO p)) with (Z.pos p + Z.pos p)%Z by lia.
      rewrite Z.pow_add_r by lia; reflexivity.
    - reflexivity. }
  apply N2Z.inj; rewrite Hpow, word_period_modulus, modulus_value; reflexivity.
Qed.

(** The signed bias orders wrapped words by their signed representatives. *)
Definition sign_bias (w : width) (sg : signedness) : Z :=
  match sg with
  | Unsigned => 0%Z
  | Signed => (modulus w / 2)%Z
  end.

(** Modular counting prepares the modulus once and charges every normalization primitive. *)
Definition mod_count_c (w : width) (sg : signedness) (cmp : cmp_kind)
    (a step bound : Z) (n : N) : Cost.t N :=
  let* period := period_c w in
  let* m := primitive_c (fun _ => Z.of_N period) in
  let* shift := match sg with
    | Unsigned => Cost.ret 0%Z
    | Signed => primitive_c (fun _ => (m / 2)%Z)
    end in
  let* shifted_a := primitive_c (fun _ => (a + shift)%Z) in
  let* wrapped_a := primitive_c (fun _ => (shifted_a mod m)%Z) in
  let* start := primitive_c (fun _ => Z.to_N wrapped_a) in
  let* shifted_b := primitive_c (fun _ => (bound + shift)%Z) in
  let* wrapped_b := primitive_c (fun _ => (shifted_b mod m)%Z) in
  let* target := primitive_c (fun _ => Z.to_N wrapped_b) in
  let* wrapped_step := primitive_c (fun _ => (step mod m)%Z) in
  let* delta := primitive_c (fun _ => Z.to_N wrapped_step) in
  match cmp with
  | CmpLt => count_ge_c n period delta start target
  | CmpLe =>
    let* threshold := primitive_c (fun _ => N.succ target) in
    count_ge_c n period delta start threshold
  | CmpNe =>
    let* threshold := primitive_c (fun _ => N.succ target) in
    let* ge := count_ge_c n period delta start target in
    let* gt := count_ge_c n period delta start threshold in
    primitive_c (fun _ => ge - gt)
  end.

(** Modular count is the value of the costed Euclidean failure counter. *)
Definition mod_count w sg cmp a step bound n :=
  Cost.value (mod_count_c w sg cmp a step bound n).

(** The modular counter uses a signed bias and two floor sums per threshold. *)
Theorem mod_count_equation w sg cmp a step bound n :
  mod_count w sg cmp a step bound n =
  let period := N.pos (word_period w) in
  let start := Z.to_N (wrap w (a + sign_bias w sg)) in
  let target := Z.to_N (wrap w (bound + sign_bias w sg)) in
  let delta := Z.to_N (wrap w step) in
  match cmp with
  | CmpLt => count_ge n period delta start target
  | CmpLe => count_ge n period delta start (N.succ target)
  | CmpNe => count_ge n period delta start target -
      count_ge n period delta start (N.succ target)
  end.
Proof.
  unfold mod_count, mod_count_c, primitive_c; autorewrite with galois_cost.
  rewrite period_value, word_period_modulus.
  destruct sg; cbn [sign_bias]; autorewrite with galois_cost;
    rewrite <- !wrap_mod; destruct cmp; autorewrite with galois_cost; reflexivity.
Qed.

Lemma floor_bias_view w sg z :
  wrap w (z + sign_bias w sg) = (view_z w sg z + sign_bias w sg)%Z.
Proof.
  destruct sg.
  - unfold sign_bias, view_z; rewrite !Z.add_0_r; reflexivity.
  - unfold sign_bias, view_z.
    assert (Hhalf : (modulus w / 2)%Z = half w).
    { rewrite modulus_half; replace (2 * half w)%Z with (half w * 2)%Z by ring.
      rewrite Z.div_mul by lia; reflexivity. }
    rewrite Hhalf.
    pose proof (wrap_is_word w z) as Hword.
    pose proof (half_pos w) as Hpositive; pose proof (modulus_half w) as Hmodulus.
    unfold is_word in Hword; rewrite wrap_add.
    rewrite (wrap_id w (half w)) by (unfold is_word; lia).
    destruct (wrap w z <? half w)%Z eqn:Hsign.
    + apply Z.ltb_lt in Hsign; apply wrap_id; unfold is_word; lia.
    + apply Z.ltb_ge in Hsign.
      replace (wrap w z + half w)%Z with
        ((wrap w z - modulus w + half w) + 1 * modulus w)%Z by ring.
      rewrite wrap_add_modulus; apply wrap_id; unfold is_word; lia.
Qed.

Lemma floor_wrapped_affine w a step shift i :
  Z.of_N ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + shift))) mod
    N.pos (word_period w)) = wrap w (a + step * Z.of_N i + shift).
Proof.
  rewrite N2Z.inj_mod, N2Z.inj_add, N2Z.inj_mul, word_period_modulus.
  rewrite !Z2N.id by (pose proof (wrap_is_word w step);
    pose proof (wrap_is_word w (a + shift)); unfold is_word in *; lia).
  rewrite <- !wrap_mod.
  replace (a + step * Z.of_N i + shift)%Z with
    (step * Z.of_N i + (a + shift))%Z by ring.
  rewrite (wrap_add w (step * Z.of_N i) (a + shift)).
  rewrite (wrap_add w (wrap w step * Z.of_N i) (wrap w (a + shift))).
  rewrite (wrap_mul w (wrap w step) (Z.of_N i)),
    (wrap_mul w step (Z.of_N i)), !wrap_wrap; reflexivity.
Qed.

Lemma floor_residue_view w sg a step i :
  Z.of_N ((Z.to_N (wrap w step) * i +
    Z.to_N (wrap w (a + sign_bias w sg))) mod N.pos (word_period w)) =
  (view_z w sg (a + step * Z.of_N i) + sign_bias w sg)%Z.
Proof.
  rewrite floor_wrapped_affine; apply floor_bias_view.
Qed.

Lemma floor_target_view w sg bound :
  Z.of_N (Z.to_N (wrap w (bound + sign_bias w sg))) =
    (view_z w sg bound + sign_bias w sg)%Z.
Proof.
  rewrite Z2N.id by (pose proof (wrap_is_word w (bound + sign_bias w sg));
    unfold is_word in *; lia).
  apply floor_bias_view.
Qed.

Lemma floor_target_bound w sg bound :
  N.succ (Z.to_N (wrap w (bound + sign_bias w sg))) <= N.pos (word_period w).
Proof.
  pose proof (wrap_is_word w (bound + sign_bias w sg)) as Hword.
  unfold is_word in Hword; apply N2Z.inj_le.
  rewrite N2Z.inj_succ, Z2N.id by lia; rewrite word_period_modulus; lia.
Qed.

Lemma floor_failure_indicator w sg cmp a step bound i :
  (if affine_test w sg cmp a step bound i then 0 else 1) =
  let residue := (Z.to_N (wrap w step) * i +
    Z.to_N (wrap w (a + sign_bias w sg))) mod N.pos (word_period w) in
  let target := Z.to_N (wrap w (bound + sign_bias w sg)) in
  match cmp with
  | CmpLt => if target <=? residue then 1 else 0
  | CmpLe => if N.succ target <=? residue then 1 else 0
  | CmpNe => if residue =? target then 1 else 0
  end.
Proof.
  pose proof (floor_residue_view w sg a step i) as Hresidue.
  pose proof (floor_target_view w sg bound) as Htarget.
  unfold affine_test, test_check; destruct cmp.
  - destruct (Z.ltb_spec (view_z w sg (a + step * Z.of_N i)) (view_z w sg bound))
      as [Hword | Hword];
      destruct (N.leb_spec0 (Z.to_N (wrap w (bound + sign_bias w sg)))
        ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + sign_bias w sg))) mod
          N.pos (word_period w))) as [Hnumeric | Hnumeric]; try reflexivity; lia.
  - destruct (Z.leb_spec (view_z w sg (a + step * Z.of_N i)) (view_z w sg bound))
      as [Hword | Hword];
      destruct (N.leb_spec0 (N.succ (Z.to_N (wrap w (bound + sign_bias w sg))))
        ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + sign_bias w sg))) mod
          N.pos (word_period w))) as [Hnumeric | Hnumeric]; try reflexivity; lia.
  - destruct (Z.eqb_spec (view_z w sg (a + step * Z.of_N i)) (view_z w sg bound))
      as [Hword | Hword];
      destruct (N.eqb_spec
        ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + sign_bias w sg))) mod
          N.pos (word_period w)) (Z.to_N (wrap w (bound + sign_bias w sg))))
      as [Hnumeric | Hnumeric]; cbn; try reflexivity.
    + exfalso; apply Hnumeric, N2Z.inj; lia.
    + apply (f_equal Z.of_N) in Hnumeric; lia.
Qed.

(** The actual modular counter equals the sum of failure indicators over its prefix. *)
Theorem mod_count_total w sg cmp a step bound limit :
  mod_count w sg cmp a step bound limit =
    floor_total (fun i => if affine_test w sg cmp a step bound i then 0 else 1) limit.
Proof.
  pose proof (floor_target_bound w sg bound) as Htarget.
  rewrite mod_count_equation; destruct cmp.
  - rewrite floor_ge_total by lia.
    apply floor_total_ext; intros i Hi.
    symmetry; apply (floor_failure_indicator w sg CmpLt a step bound i).
  - rewrite floor_ge_total by lia.
    apply floor_total_ext; intros i Hi.
    symmetry; apply (floor_failure_indicator w sg CmpLe a step bound i).
  - rewrite floor_ge_difference by lia.
    apply floor_total_ext; intros i Hi.
    symmetry; apply (floor_failure_indicator w sg CmpNe a step bound i).
Qed.

Lemma floor_failed_indices_exist (test : N -> bool) limit :
  exists indices : list N,
    NoDup indices /\
    (forall k, In k indices <-> k < limit /\ test k = false) /\
    floor_total (fun i => if test i then 0 else 1) limit = N.of_nat (length indices).
Proof.
  induction limit using N.peano_ind.
  - exists nil; split; [constructor|].
    split; [intros k; cbn; lia|reflexivity].
  - destruct IHlimit as [indices [Hnodup [Hindices Hcount]]].
    destruct (test limit) eqn:Hlast.
    + exists indices; split; [exact Hnodup|]; split.
      * intros k; rewrite Hindices.
        split; intros [Hbound Hfailed]; split; try lia; try exact Hfailed.
        assert (Hdifferent : k <> limit) by (intro Hequal; subst; congruence); lia.
      * rewrite floor_total_succ, Hlast, Hcount; lia.
    + exists (limit :: indices)%list; split.
      * constructor; [rewrite Hindices; lia|exact Hnodup].
      * split.
        -- intros k; cbn; rewrite Hindices; split.
           ++ intros [Hequal | [Hbound Hfailed]]; subst; split; try lia; assumption.
           ++ intros [Hbound Hfailed].
              destruct (N.eq_dec limit k) as [Hequal | Hdifferent]; [left; exact Hequal|].
              right; split; [lia|exact Hfailed].
        -- rewrite floor_total_succ, Hlast, Hcount; cbn [length].
           rewrite Nat2N.inj_succ; lia.
Qed.

(** Failed-index witnesses contain every failed prefix index once and contain no other index. *)
Definition failed_indices w sg cmp a step bound limit (indices : list N) : Prop :=
  NoDup indices /\
    forall k, In k indices <-> k < limit /\ affine_test w sg cmp a step bound k = false.

(** Every modular count equals the number of distinct failed indices in its entire prefix. *)
Theorem mod_count_exact w sg cmp a step bound limit :
  exists indices, failed_indices w sg cmp a step bound limit indices /\
    mod_count w sg cmp a step bound limit = N.of_nat (length indices).
Proof.
  destruct (floor_failed_indices_exist (affine_test w sg cmp a step bound) limit)
    as [indices [Hnodup [Hindices Hcount]]].
  exists indices; split.
  - split; assumption.
  - rewrite mod_count_total; exact Hcount.
Qed.

(** The exact word period is a power of two over binary natural exponents. *)
Theorem period_power w : N.pos (word_period w) = 2 ^ N.pos w.
Proof.
  apply N2Z.inj; rewrite N2Z.inj_pow, word_period_modulus, modulus_value; reflexivity.
Qed.

(** The prepared modulus has one more bit than the word width. *)
Theorem period_size w : N.size (N.pos (word_period w)) = N.pos w + 1.
Proof.
  rewrite N.size_log2 by discriminate.
  rewrite period_power, N.log2_pow2 by lia; lia.
Qed.

(** Repeated-squaring preparation charges at most three ticks per width digit. *)
Theorem period_cost w : Cost.ticks (period_c w) <= 3 * N.pos (Pos.size w).
Proof.
  induction w as [w IH|w IH|]; cbn [period_c]; unfold primitive_c;
    autorewrite with galois_cost.
  - change (1 + (Cost.ticks (period_c w) + (1 + 1)) <=
      3 * N.succ (N.pos (Pos.size w))); lia.
  - change (1 + (Cost.ticks (period_c w) + 1) <=
      3 * N.succ (N.pos (Pos.size w))); lia.
  - cbn; lia.
Qed.

(** Both floor sums and threshold-offset arithmetic are included in a threshold count's price. *)
Theorem count_ge_cost n m a b threshold :
  Cost.ticks (count_ge_c n m a b threshold) <= 203 * (N.size m + 1).
Proof.
  unfold count_ge_c, primitive_c; autorewrite with galois_cost.
  pose proof (floor_sum_fast_cost n m a (b + m - threshold)).
  pose proof (floor_sum_fast_cost n m a b); lia.
Qed.

(** Modular counting includes normalization, modulus preparation and every called floor sum. *)
Theorem mod_count_cost w sg cmp a step bound n :
  Cost.ticks (mod_count_c w sg cmp a step bound n) <= 1000 * (N.pos w + 1).
Proof.
  unfold mod_count_c, primitive_c; autorewrite with galois_cost.
  rewrite period_value.
  pose proof (period_cost w) as Hperiod.
  pose proof (positive_size_le w) as Hwidth.
  destruct sg, cmp; autorewrite with galois_cost.
  all: repeat match goal with
  | |- context [Cost.ticks (count_ge_c ?n ?m ?a ?b ?t)] =>
    let Hprice := fresh "Hprice" in
    let ticks := fresh "ticks" in
    pose proof (count_ge_cost n m a b t) as Hprice;
    rewrite period_size in Hprice;
    remember (Cost.ticks (count_ge_c n m a b t)) as ticks in *
  end.
  all: lia.
Qed.

Lemma floor_size_div x y : N.size (x / y) <= N.size x.
Proof.
  apply floor_size_mono; destruct y as [|p].
  - rewrite N.div_0_r; lia.
  - apply N.Div0.div_le_upper_bound; nia.
Qed.

Lemma floor_size_mod x y : N.size (x mod y) <= N.size x.
Proof.
  apply floor_size_mono, N.Div0.mod_le.
Qed.

(** This list contains every numeric field and intermediate used by an active arithmetic step. *)
Definition floor_intermediates (st : state) : list N :=
  let n := floor_n st in
  let m := floor_m st in
  let a := floor_a st in
  let b := floor_b st in
  let acc := floor_acc st in
  let updates := floor_updates st in
  let ar := a mod m in
  let br := b mod m in
  let pred := N.pred n in
  let prod := n * pred in
  let triangle := prod / 2 in
  let aq := a / m in
  let first := triangle * aq in
  let acc1 := acc + first in
  let bq := b / m in
  let second := n * bq in
  let acc' := acc1 + second in
  let scaled := ar * n in
  let y := scaled + br in
  [n; m; a; b; acc; updates; ar; br; pred; prod; triangle; aq; first; acc1;
   bq; second; acc'; scaled; y; N.succ updates; y / m; y mod m].

(** Primitive operand size includes temporary products and the actual update counter. *)
Definition floor_primitive_bits (st : state) : N :=
  fold_right (fun x bound => N.max (N.size x) bound) 0 (floor_intermediates st).

(** Each actual arithmetic temporary uses a constant multiple of the live state's total bits. *)
Theorem floor_step_primitive_bits st :
  floor_primitive_bits st <=
    8 * (floor_state_bits st + N.size (floor_updates st) + 1).
Proof.
  destruct st as [n m a b acc done updates].
  pose proof (floor_size_mod a m).
  pose proof (floor_size_mod b m).
  pose proof (floor_size_mono (N.pred n) n (N.le_pred_l n)).
  pose proof (floor_size_mul n (N.pred n)).
  pose proof (floor_size_div (n * N.pred n) 2).
  pose proof (floor_size_div a m).
  pose proof (floor_size_div b m).
  pose proof (floor_size_mul (n * N.pred n / 2) (a / m)).
  pose proof (floor_size_add acc (n * N.pred n / 2 * (a / m))).
  pose proof (floor_size_mul n (b / m)).
  pose proof (floor_size_add (acc + n * N.pred n / 2 * (a / m)) (n * (b / m))).
  pose proof (floor_size_mul (a mod m) n).
  pose proof (floor_size_add (a mod m * n) (b mod m)).
  pose proof (floor_size_add updates 1) as Hsuccessor.
  change (N.size (updates + 1) <= N.size updates + 1 + 1) in Hsuccessor.
  pose proof (floor_size_div (a mod m * n + b mod m) m).
  pose proof (floor_size_mod (a mod m * n + b mod m) m).
  replace (updates + 1) with (N.succ updates) in Hsuccessor by lia.
  unfold floor_primitive_bits, floor_intermediates, floor_state_bits.
  cbn [floor_n floor_m floor_a floor_b floor_acc floor_updates fold_right].
  repeat apply N.max_lub; lia.
Qed.

(** Initialized floor executions bound temporary operand bits as well as retained state bits. *)
Theorem floor_execute_primitive_bits n m a b k : 0 < m ->
  floor_primitive_bits (N.iter k floor_step (State n m a b 0 false 0)) <=
    80 * (N.size n + N.size m + N.size a + N.size b + 1) + 8 * N.size k + 8.
Proof.
  intro Hmod.
  pose proof (floor_step_primitive_bits (N.iter k floor_step
    (State n m a b 0 false 0))) as Hstep.
  pose proof (floor_sum_live_bits n m a b k Hmod) as Hlive.
  pose proof (floor_updates_iter k (State n m a b 0 false 0)) as Hupdates.
  change (floor_updates (N.iter k floor_step (State n m a b 0 false 0)) <= k) in Hupdates.
  pose proof (floor_size_mono _ _ Hupdates); lia.
Qed.

Lemma floor_size_le n : N.size n <= n.
Proof.
  destruct n as [|p]; [reflexivity|apply positive_size_le].
Qed.

(** Every staircase operand in a word-sized threshold count has linearly many width bits. *)
Theorem word_floor_primitive_bits w n a b k :
  n <= N.pos (word_period w) ->
  a <= N.pos (word_period w) ->
  b <= 2 * N.pos (word_period w) ->
  k <= 2 * N.size (N.pos (word_period w)) + 1 ->
  floor_primitive_bits (N.iter k floor_step
    (State n (N.pos (word_period w)) a b 0 false 0)) <= 500 * (N.pos w + 1).
Proof.
  intros Hn Ha Hb Hk.
  pose proof (floor_execute_primitive_bits n (N.pos (word_period w)) a b k
    ltac:(lia)) as Hbits.
  pose proof (floor_size_mono _ _ Hn) as Hnsize.
  pose proof (floor_size_mono _ _ Ha) as Hasize.
  pose proof (floor_size_mono _ _ Hb) as Hbsize.
  pose proof (floor_size_mul 2 (N.pos (word_period w))) as Hdouble.
  change (N.size (2 * N.pos (word_period w)) <= 2 + N.size (N.pos (word_period w)))
    in Hdouble.
  pose proof (floor_size_le k) as Hksize.
  rewrite period_size in *; lia.
Qed.

(** Both actual floor calls made by a normalized threshold count use word-sized operands. *)
Theorem count_ge_primitive_bits w n a b threshold k :
  n <= N.pos (word_period w) ->
  a <= N.pos (word_period w) ->
  b <= N.pos (word_period w) ->
  threshold <= N.pos (word_period w) ->
  k <= 2 * N.size (N.pos (word_period w)) + 1 ->
  floor_primitive_bits (N.iter k floor_step
    (State n (N.pos (word_period w)) a (b + N.pos (word_period w) - threshold)
      0 false 0)) <= 500 * (N.pos w + 1) /\
  floor_primitive_bits (N.iter k floor_step
    (State n (N.pos (word_period w)) a b 0 false 0)) <= 500 * (N.pos w + 1).
Proof.
  intros Hn Ha Hb Hthreshold Hk; split; apply word_floor_primitive_bits; lia.
Qed.

Lemma wrapped_count_bound w z :
  Z.to_N (wrap w z) < N.pos (word_period w).
Proof.
  pose proof (wrap_is_word w z) as Hword; unfold is_word in Hword.
  apply N2Z.inj_lt; rewrite Z2N.id by lia.
  rewrite word_period_modulus; lia.
Qed.

(** Modular normalization discharges both floor calls' primitive-size obligations. *)
Theorem mod_count_primitive_bits w sg a step bound n k threshold :
  n <= N.pos (word_period w) ->
  k <= 2 * N.size (N.pos (word_period w)) + 1 ->
  (threshold = Z.to_N (wrap w (bound + sign_bias w sg)) \/
    threshold = N.succ (Z.to_N (wrap w (bound + sign_bias w sg)))) ->
  let delta := Z.to_N (wrap w step) in
  let start := Z.to_N (wrap w (a + sign_bias w sg)) in
  floor_primitive_bits (N.iter k floor_step
    (State n (N.pos (word_period w)) delta
      (start + N.pos (word_period w) - threshold) 0 false 0)) <=
      500 * (N.pos w + 1) /\
  floor_primitive_bits (N.iter k floor_step
    (State n (N.pos (word_period w)) delta start 0 false 0)) <=
      500 * (N.pos w + 1).
Proof.
  intros Hn Hk Hthreshold.
  apply count_ge_primitive_bits; try assumption.
  - pose proof (wrapped_count_bound w step); lia.
  - pose proof (wrapped_count_bound w (a + sign_bias w sg)); lia.
  - pose proof (floor_target_bound w sg bound).
    destruct Hthreshold; subst threshold; lia.
Qed.

End Floor.
