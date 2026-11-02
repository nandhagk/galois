(** * Arithmetic of the fixed modular prefix counter

    The Euclidean floor-sum machine and modular counter satisfy their exact arithmetic contracts.
    For example, a zero modulus returns zero without running a floor step.
    Builds on: AnalysesAuditScevModCountPlain, AnalysesScev, BitsWord and binary arithmetic. *)

From Stdlib Require Import NArith ZArith List Lia.
From Galois.Bits Require Import BitsWord.
From Galois.Analyses Require Import AnalysesScev AnalysesAuditScevModCountPlain.

Local Open Scope N_scope.

(** * Binary size and Euclidean descent *)

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

(** The two remainder sizes decrease at every unfinished Euclidean transition. *)
Definition floor_rank (st : audit_floor_state) : N :=
  N.size (audit_floor_m st) + N.size (audit_floor_a st mod audit_floor_m st).

Lemma floor_step_descent st :
  0 < audit_floor_m st -> audit_floor_done st = false ->
  audit_floor_done (audit_floor_step st) = false ->
  0 < audit_floor_m (audit_floor_step st) /\
  floor_rank (audit_floor_step st) < floor_rank st.
Proof.
  destruct st as [n m a b acc done updates]; cbn.
  intros Hmod Hdone; subst done.
  unfold audit_floor_step; cbn.
  destruct (a mod m * n + b mod m <? m) eqn:Htest; cbn; [discriminate |].
  intros _.
  assert (Hremainder : 0 < a mod m < m).
  { pose proof (N.mod_lt a m ltac:(lia)).
    pose proof (N.mod_lt b m ltac:(lia)).
    apply N.ltb_ge in Htest.
    nia. }
  split; [lia |].
  unfold floor_rank; cbn.
  pose proof (floor_remainder_half m (a mod m) Hremainder) as Hhalf.
  pose proof (floor_size_half (m mod (a mod m)) m Hhalf); lia.
Qed.

Lemma floor_done_step st : audit_floor_done st = true -> audit_floor_step st = st.
Proof.
  intro Hdone; unfold audit_floor_step; rewrite Hdone; reflexivity.
Qed.

Lemma floor_done_iter fuel st :
  audit_floor_done st = true -> N.iter fuel audit_floor_step st = st.
Proof.
  intro Hdone; induction fuel using N.peano_ind.
  - reflexivity.
  - rewrite N.iter_succ, IHfuel; apply floor_done_step; exact Hdone.
Qed.

Lemma floor_rank_finishes fuel : forall st,
  0 < audit_floor_m st -> floor_rank st < fuel ->
  audit_floor_done (N.iter fuel audit_floor_step st) = true.
Proof.
  induction fuel using N.peano_ind; intros st Hmod Hrank; [lia |].
  destruct (audit_floor_done st) eqn:Hdone.
  - rewrite floor_done_iter by exact Hdone; exact Hdone.
  - rewrite N.iter_succ_r.
    destruct (audit_floor_done (audit_floor_step st)) eqn:Hnext.
    + rewrite floor_done_iter by exact Hnext; exact Hnext.
    + destruct (floor_step_descent st Hmod Hdone Hnext) as [Hmodnext Hdecrease].
      apply IHfuel; lia.
Qed.

Lemma floor_updates_step st :
  audit_floor_updates (audit_floor_step st) <= N.succ (audit_floor_updates st).
Proof.
  destruct st as [n m a b acc done updates].
  unfold audit_floor_step; cbn.
  destruct done; cbn; [lia |].
  destruct (a mod m * n + b mod m <? m); cbn; lia.
Qed.

Lemma floor_updates_iter fuel st :
  audit_floor_updates (N.iter fuel audit_floor_step st) <= audit_floor_updates st + fuel.
Proof.
  induction fuel using N.peano_ind.
  - cbn; lia.
  - rewrite N.iter_succ.
    pose proof (floor_updates_step (N.iter fuel audit_floor_step st)); lia.
Qed.

(** * Public termination and rejected-modulus contracts *)

(** The fixed positive-modulus execution finishes within its actual update budget. *)
Theorem audit_floor_sum_terminates : forall n m a b : N,
  0 < m ->
  let '(_, steps, done) := audit_floor_sum_counted n m a b in
  done = true /\ steps <= 2 * N.size m + 1.
Proof.
  intros n m a b Hmod.
  unfold audit_floor_sum_counted.
  destruct (m =? 0) eqn:Hzero; [apply N.eqb_eq in Hzero; lia |].
  split.
  - apply floor_rank_finishes; cbn; [exact Hmod |].
    unfold floor_rank; cbn.
    change (N.size m + N.size (a mod m) < 2 * N.size m + 1).
    pose proof (N.mod_lt a m ltac:(lia)).
    pose proof (floor_size_mono (a mod m) m ltac:(lia)); lia.
  - pose proof (floor_updates_iter (2 * N.size m + 1)
      (AuditFloorState n m a b 0 false 0)) as Hupdates.
    cbn in Hupdates; exact Hupdates.
Qed.

(** A zero modulus follows the specified zero-result branch. *)
Theorem audit_floor_sum_zero : forall n a b : N,
  audit_floor_sum_fast n 0 a b = 0.
Proof.
  reflexivity.
Qed.

(** * Numeric bounds on the actual live state *)

(** This potential pays for accumulated quotients and the remaining affine rectangle. *)
Definition floor_potential (st : audit_floor_state) : N :=
  audit_floor_acc st + audit_floor_n st * audit_floor_n st * audit_floor_a st +
    audit_floor_n st * audit_floor_b st.

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

Lemma floor_step_potential st : 0 < audit_floor_m st ->
  floor_potential (audit_floor_step st) <= floor_potential st.
Proof.
  destruct st as [n m a b acc done updates]; cbn.
  intro Hmod.
  unfold audit_floor_step; cbn.
  destruct done; [reflexivity |].
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

(** The invariant bounds fields numerically, independently of the iteration count. *)
Definition floor_live_bound n m a b (st : audit_floor_state) : Prop :=
  0 < audit_floor_m st /\ audit_floor_n st <= n /\ audit_floor_m st <= m /\
  audit_floor_a st <= a + m /\ audit_floor_b st <= b + m /\
  floor_potential st <= n * n * a + n * b.

Lemma floor_live_step n m a b st :
  floor_live_bound n m a b st -> floor_live_bound n m a b (audit_floor_step st).
Proof.
  intros Hlive.
  destruct Hlive as [Hmod [Hn [Hm [Ha [Hb Hpotential]]]]].
  pose proof (floor_step_potential st Hmod) as Hdecrease.
  pose proof (N.le_trans _ _ _ Hdecrease Hpotential) as Hnextpotential.
  destruct st as [sn sm sa sb acc done updates]; cbn in *.
  unfold audit_floor_step in Hnextpotential |- *; cbn in Hnextpotential |- *.
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
  floor_live_bound n m a b
    (N.iter k audit_floor_step (AuditFloorState n m a b 0 false 0)).
Proof.
  intro Hmod.
  apply N.iter_invariant.
  - apply floor_live_step.
  - unfold floor_live_bound, floor_potential; cbn; repeat split; lia.
Qed.

(** * Binary size bounds *)

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
  apply floor_size_bound.
  rewrite N.pow_add_r.
  pose proof (N.size_gt x); pose proof (N.size_gt y); nia.
Qed.

Lemma floor_size_add x y : N.size (x + y) <= N.size x + N.size y + 1.
Proof.
  apply floor_size_bound.
  rewrite !N.pow_add_r; cbn [N.pow].
  pose proof (N.size_gt x); pose proof (N.size_gt y); nia.
Qed.

(** Every initialized execution, including ticks after completion, has bounded live bits. *)
Theorem audit_floor_live_bits : forall n m a b k : N,
  0 < m ->
  audit_floor_state_bits
    (N.iter k audit_floor_step (AuditFloorState n m a b 0 false 0)) <=
    10 * (N.size n + N.size m + N.size a + N.size b + 1).
Proof.
  intros n m a b k Hmod.
  pose proof (floor_live_iter n m a b k Hmod) as Hlive.
  destruct (N.iter k audit_floor_step (AuditFloorState n m a b 0 false 0))
    as [sn sm sa sb acc done updates].
  destruct Hlive as [Hpositive [Hn [Hm [Ha [Hb Hacc]]]]].
  unfold floor_potential in Hacc; cbn in *.
  pose proof (floor_size_mono sn n Hn).
  pose proof (floor_size_mono sm m Hm).
  pose proof (floor_size_mono sa (a + m) Ha).
  pose proof (floor_size_mono sb (b + m) Hb).
  pose proof (floor_size_mono acc (n * n * a + n * b) ltac:(nia)).
  pose proof (floor_size_add a m).
  pose proof (floor_size_add b m).
  pose proof (floor_size_add (n * n * a) (n * b)).
  pose proof (floor_size_mul (n * n) a).
  pose proof (floor_size_mul n n).
  pose proof (floor_size_mul n b).
  unfold audit_floor_state_bits; cbn.
  change (N.size sn + N.size sm + N.size sa + N.size sb + N.size acc <=
    10 * (N.size n + N.size m + N.size a + N.size b + 1)).
  lia.
Qed.

(** * Finite binary sums *)

(** The proof model sums an arbitrary sequence without changing the fixed floor producer. *)
Definition floor_total (f : N -> N) (n : N) : N :=
  snd (N.iter n (fun state : N * N =>
    (N.succ (fst state), snd state + f (fst state))) (0, 0)).

Lemma floor_total_index f n :
  fst (N.iter n (fun state : N * N =>
    (N.succ (fst state), snd state + f (fst state))) (0, 0)) = n.
Proof.
  induction n using N.peano_ind; [reflexivity |].
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
  induction n using N.peano_ind; intro Hequal; [reflexivity |].
  rewrite !floor_total_succ, IHn; [rewrite Hequal by lia; reflexivity |].
  intros i Hi; apply Hequal; lia.
Qed.

Lemma floor_total_add f g n :
  floor_total (fun i => f i + g i) n = floor_total f n + floor_total g n.
Proof.
  induction n using N.peano_ind; [reflexivity |].
  rewrite !floor_total_succ, IHn; lia.
Qed.

Lemma floor_total_scale f n c :
  floor_total (fun i => c * f i) n = c * floor_total f n.
Proof.
  induction n using N.peano_ind; [rewrite !floor_total_zero; lia |].
  rewrite !floor_total_succ, IHn; ring.
Qed.

Lemma floor_total_constant n c : floor_total (fun _ => c) n = n * c.
Proof.
  induction n using N.peano_ind; [reflexivity |].
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
  destruct (N.eq_dec n 0) as [Hzero | Hnonzero]; [subst; reflexivity |].
  replace (N.succ n * N.pred (N.succ n)) with (n * N.pred n + n * 2)
    by (pose proof (N.succ_pred n Hnonzero); rewrite N.pred_succ; nia).
  apply N.div_add; discriminate.
Qed.

Lemma floor_total_indices n : floor_total (fun i => i) n = n * N.pred n / 2.
Proof.
  induction n using N.peano_ind; [reflexivity |].
  rewrite floor_total_succ, IHn, floor_triangle_succ; reflexivity.
Qed.

Lemma floor_reference_total n m a b :
  audit_floor_sum_reference n m a b = floor_total (fun i => (a * i + b) / m) n.
Proof.
  unfold audit_floor_sum_reference, floor_total.
  f_equal.
  induction n using N.peano_ind; [reflexivity |].
  rewrite !N.iter_succ, IHn.
  destruct (N.iter n
    (fun state : N * N => (N.succ (fst state), snd state + (a * fst state + b) / m))
    (0, 0)); reflexivity.
Qed.

Lemma floor_reference_succ n m a b :
  audit_floor_sum_reference (N.succ n) m a b =
    audit_floor_sum_reference n m a b + (a * n + b) / m.
Proof.
  rewrite !floor_reference_total; exact (floor_total_succ (fun i => (a * i + b) / m) n).
Qed.

Lemma floor_reference_offset n m a b : 0 < m ->
  audit_floor_sum_reference n m a (b + m) = audit_floor_sum_reference n m a b + n.
Proof.
  intro Hmod; rewrite !floor_reference_total.
  transitivity (floor_total (fun i => (a * i + b) / m + 1) n).
  - apply floor_total_ext; intros i Hi.
    replace (a * i + (b + m)) with ((a * i + b) + 1 * m) by ring.
    apply N.div_add; lia.
  - rewrite floor_total_add, floor_total_constant; lia.
Qed.

Lemma floor_reference_head n m a b :
  audit_floor_sum_reference (N.succ n) m a b =
    b / m + audit_floor_sum_reference n m a (a + b).
Proof.
  rewrite !floor_reference_total, floor_total_shift; cbn [N.mul N.add].
  replace (a * 0 + b) with b by ring.
  f_equal; apply floor_total_ext; intros i Hi.
  f_equal; nia.
Qed.

Lemma floor_reference_normalize n m a b : 0 < m ->
  audit_floor_sum_reference n m a b =
    (n * N.pred n / 2) * (a / m) + n * (b / m) +
    audit_floor_sum_reference n m (a mod m) (b mod m).
Proof.
  intro Hmod; rewrite !floor_reference_total.
  transitivity (floor_total
    (fun i => i * (a / m) + b / m + ((a mod m) * i + b mod m) / m) n).
  - apply floor_total_ext; intros i Hi.
    pose proof (N.div_mod a m ltac:(lia)) as Ha.
    pose proof (N.div_mod b m ltac:(lia)) as Hb.
    replace (a * i + b) with
      (((a mod m) * i + b mod m) + (i * (a / m) + b / m) * m) by nia.
    rewrite N.div_add by lia; lia.
  - rewrite !floor_total_add, floor_total_constant.
    replace (floor_total (fun i => i * (a / m)) n) with
      ((a / m) * floor_total (fun i => i) n).
    + rewrite floor_total_indices; ring.
    + rewrite <- floor_total_scale; apply floor_total_ext; intros; ring.
Qed.

(** * Floor reciprocity *)

Lemma floor_divmod y m q r : r < m -> y = m * q + r ->
  y / m = q /\ y mod m = r.
Proof.
  intros Hremainder Hdivision; split; symmetry.
  - apply (N.div_unique y m q r); assumption.
  - apply (N.mod_unique y m q r); assumption.
Qed.

(** Transposing the normalized affine staircase gives the actual swapped recursive operands. *)
Lemma floor_reference_reciprocal n m a b : 0 < a < m -> b < m ->
  audit_floor_sum_reference n m a b =
    audit_floor_sum_reference ((a * n + b) / m) a m ((a * n + b) mod m).
Proof.
  intros [Ha Hmod] Hb.
  induction n using N.peano_ind.
  - change (0 = audit_floor_sum_reference ((a * 0 + b) / m) a m
      ((a * 0 + b) mod m)).
    replace (a * 0 + b) with b by ring.
    rewrite N.div_small by exact Hb; reflexivity.
  - rewrite floor_reference_succ, IHn.
    set (q := (a * n + b) / m).
    set (r := (a * n + b) mod m).
    pose proof (N.div_mod (a * n + b) m ltac:(lia)) as Hy.
    pose proof (N.mod_lt (a * n + b) m ltac:(lia)) as Hr.
    change (a * n + b = m * q + r) in Hy.
    change (r < m) in Hr.
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
  audit_floor_sum_reference n m a b = 0.
Proof.
  intro Hsmall; rewrite floor_reference_total.
  transitivity (floor_total (fun _ => 0) n).
  - apply floor_total_ext; intros i Hi; apply N.div_small; nia.
  - rewrite floor_total_constant; lia.
Qed.

(** The accumulator plus remaining staircase is preserved by each actual machine step. *)
Definition floor_value (st : audit_floor_state) : N :=
  audit_floor_acc st + audit_floor_sum_reference (audit_floor_n st) (audit_floor_m st)
    (audit_floor_a st) (audit_floor_b st).

Lemma floor_value_step st : 0 < audit_floor_m st ->
  floor_value (audit_floor_step st) = floor_value st.
Proof.
  destruct st as [n m a b acc done updates]; cbn; intro Hmod.
  unfold audit_floor_step; cbn; destruct done; [reflexivity |].
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

Lemma floor_done_remainder_step st : 0 < audit_floor_m st ->
  (audit_floor_done st = true ->
    audit_floor_sum_reference (audit_floor_n st) (audit_floor_m st)
      (audit_floor_a st) (audit_floor_b st) = 0) ->
  audit_floor_done (audit_floor_step st) = true ->
  audit_floor_sum_reference (audit_floor_n (audit_floor_step st))
    (audit_floor_m (audit_floor_step st)) (audit_floor_a (audit_floor_step st))
    (audit_floor_b (audit_floor_step st)) = 0.
Proof.
  destruct st as [n m a b acc done updates]; cbn; intros Hmod Hdone.
  unfold audit_floor_step; cbn; destruct done.
  - intros _; apply Hdone; reflexivity.
  - destruct (a mod m * n + b mod m <? m) eqn:Htest; cbn; [intros _ | discriminate].
    apply floor_reference_small, N.ltb_lt; exact Htest.
Qed.

(** The semantic invariant couples the accumulator and completion flag to the same state. *)
Definition floor_semantic_bound n m a b (st : audit_floor_state) : Prop :=
  floor_live_bound n m a b st /\
  floor_value st = audit_floor_sum_reference n m a b /\
  (audit_floor_done st = true ->
    audit_floor_sum_reference (audit_floor_n st) (audit_floor_m st)
      (audit_floor_a st) (audit_floor_b st) = 0).

Lemma floor_semantic_step n m a b st :
  floor_semantic_bound n m a b st -> floor_semantic_bound n m a b (audit_floor_step st).
Proof.
  intros [Hlive [Hvalue Hdone]].
  assert (Hmod : 0 < audit_floor_m st) by (destruct Hlive; assumption).
  split; [apply floor_live_step; exact Hlive |].
  split.
  - rewrite floor_value_step by exact Hmod; exact Hvalue.
  - apply floor_done_remainder_step; assumption.
Qed.

Lemma floor_semantic_iter n m a b k : 0 < m ->
  floor_semantic_bound n m a b
    (N.iter k audit_floor_step (AuditFloorState n m a b 0 false 0)).
Proof.
  intro Hmod; apply N.iter_invariant.
  - apply floor_semantic_step.
  - split; [apply (floor_live_iter n m a b 0 Hmod) |].
    split; [reflexivity | discriminate].
Qed.

(** The fixed binary-budget producer equals the independent term-by-term reference sum. *)
Theorem audit_floor_sum_fast_correct : forall n m a b : N,
  0 < m -> audit_floor_sum_fast n m a b = audit_floor_sum_reference n m a b.
Proof.
  intros n m a b Hmod.
  pose proof (audit_floor_sum_terminates n m a b Hmod) as Htermination.
  pose proof (floor_semantic_iter n m a b (2 * N.size m + 1) Hmod) as Hsemantic.
  unfold audit_floor_sum_fast, audit_floor_sum_counted in *.
  destruct (m =? 0) eqn:Hzero; [apply N.eqb_eq in Hzero; lia |].
  destruct (N.iter (2 * N.size m + 1) audit_floor_step
    (AuditFloorState n m a b 0 false 0)) as [sn sm sa sb acc done updates].
  destruct Htermination as [Hdone Hupdates].
  destruct Hsemantic as [Hlive [Hvalue Hremainder]].
  unfold floor_value in Hvalue; cbn in *.
  rewrite Hremainder in Hvalue by exact Hdone; lia.
Qed.

(** * Threshold indicators *)

Lemma floor_threshold_term m a b threshold i : 0 < m -> threshold <= m ->
  (a * i + (b + m - threshold)) / m =
    (a * i + b) / m + (if threshold <=? (a * i + b) mod m then 1 else 0).
Proof.
  intros Hmod Hthreshold.
  set (q := (a * i + b) / m).
  set (r := (a * i + b) mod m).
  pose proof (N.div_mod (a * i + b) m ltac:(lia)) as Hdivision.
  pose proof (N.mod_lt (a * i + b) m ltac:(lia)) as Hremainder.
  change (a * i + b = m * q + r) in Hdivision.
  change (r < m) in Hremainder.
  destruct (threshold <=? r) eqn:Htest.
  - apply N.leb_le in Htest.
    destruct (floor_divmod (a * i + (b + m - threshold)) m (q + 1) (r - threshold)
      ltac:(lia) ltac:(nia)) as [Hquotient _].
    exact Hquotient.
  - apply N.leb_gt in Htest.
    destruct (floor_divmod (a * i + (b + m - threshold)) m q (r + m - threshold)
      ltac:(lia) ltac:(nia)) as [Hquotient _].
    rewrite Hquotient; lia.
Qed.

Lemma floor_ge_total n m a b threshold : 0 < m -> threshold <= m ->
  audit_count_ge audit_floor_sum_fast n m a b threshold =
    floor_total (fun i => if threshold <=? (a * i + b) mod m then 1 else 0) n.
Proof.
  intros Hmod Hthreshold; unfold audit_count_ge.
  rewrite !audit_floor_sum_fast_correct by exact Hmod.
  rewrite !floor_reference_total.
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
  destruct (N.leb_spec0 t r);
    destruct (N.leb_spec0 (N.succ t) r);
    destruct (N.eqb_spec r t); lia.
Qed.

Lemma floor_ge_difference n m a b t : 0 < m -> N.succ t <= m ->
  audit_count_ge audit_floor_sum_fast n m a b t -
    audit_count_ge audit_floor_sum_fast n m a b (N.succ t) =
  floor_total (fun i => if (a * i + b) mod m =? t then 1 else 0) n.
Proof.
  intros Hmod Hthreshold.
  rewrite !floor_ge_total by lia.
  assert (Hsum :
    floor_total (fun i => if t <=? (a * i + b) mod m then 1 else 0) n =
    floor_total (fun i =>
      (if N.succ t <=? (a * i + b) mod m then 1 else 0) +
      (if (a * i + b) mod m =? t then 1 else 0)) n).
  { apply floor_total_ext; intros; apply floor_indicator_difference. }
  rewrite Hsum, floor_total_add; lia.
Qed.

(** * Word normalization and comparison *)

(** The signed bias orders wrapped words by their signed representatives. *)
Definition floor_sign_bias (w : width) (sg : signedness) : Z :=
  match sg with
  | Unsigned => 0%Z
  | Signed => (modulus w / 2)%Z
  end.

Lemma floor_bias_view w sg z :
  wrap w (z + floor_sign_bias w sg) = (view_z w sg z + floor_sign_bias w sg)%Z.
Proof.
  destruct sg.
  - unfold floor_sign_bias, view_z; rewrite !Z.add_0_r; reflexivity.
  - unfold floor_sign_bias, view_z.
    assert (Hhalf : (modulus w / 2)%Z = half w).
    { rewrite modulus_half.
      replace (2 * half w)%Z with (half w * 2)%Z by ring.
      rewrite Z.div_mul by lia; reflexivity. }
    rewrite Hhalf.
    pose proof (wrap_is_word w z) as Hword.
    pose proof (half_pos w) as Hpositive.
    pose proof (modulus_half w) as Hmodulus.
    unfold is_word in Hword.
    rewrite wrap_add.
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
  change (wrap w (wrap w step * Z.of_N i + wrap w (a + shift)) =
    wrap w (a + step * Z.of_N i + shift)).
  replace (a + step * Z.of_N i + shift)%Z with
    (step * Z.of_N i + (a + shift))%Z by ring.
  rewrite (wrap_add w (step * Z.of_N i) (a + shift)).
  rewrite (wrap_add w (wrap w step * Z.of_N i) (wrap w (a + shift))).
  rewrite (wrap_mul w (wrap w step) (Z.of_N i)),
    (wrap_mul w step (Z.of_N i)), !wrap_wrap; reflexivity.
Qed.

Lemma floor_residue_view w sg a step i :
  Z.of_N ((Z.to_N (wrap w step) * i +
    Z.to_N (wrap w (a + floor_sign_bias w sg))) mod N.pos (word_period w)) =
  (view_z w sg (a + step * Z.of_N i) + floor_sign_bias w sg)%Z.
Proof.
  rewrite floor_wrapped_affine; apply floor_bias_view.
Qed.

Lemma floor_target_view w sg bound :
  Z.of_N (Z.to_N (wrap w (bound + floor_sign_bias w sg))) =
    (view_z w sg bound + floor_sign_bias w sg)%Z.
Proof.
  rewrite Z2N.id by (pose proof (wrap_is_word w (bound + floor_sign_bias w sg));
    unfold is_word in *; lia).
  apply floor_bias_view.
Qed.

Lemma floor_target_bound w sg bound :
  N.succ (Z.to_N (wrap w (bound + floor_sign_bias w sg))) <= N.pos (word_period w).
Proof.
  pose proof (wrap_is_word w (bound + floor_sign_bias w sg)) as Hword.
  unfold is_word in Hword.
  apply N2Z.inj_le.
  rewrite N2Z.inj_succ, Z2N.id by lia.
  rewrite word_period_modulus; lia.
Qed.

Lemma floor_failure_indicator w sg cmp a step bound i :
  (if affine_test w sg cmp a step bound i then 0 else 1) =
  let residue := (Z.to_N (wrap w step) * i +
    Z.to_N (wrap w (a + floor_sign_bias w sg))) mod N.pos (word_period w) in
  let target := Z.to_N (wrap w (bound + floor_sign_bias w sg)) in
  match cmp with
  | CmpLt => if target <=? residue then 1 else 0
  | CmpLe => if N.succ target <=? residue then 1 else 0
  | CmpNe => if residue =? target then 1 else 0
  end.
Proof.
  pose proof (floor_residue_view w sg a step i) as Hresidue.
  pose proof (floor_target_view w sg bound) as Htarget.
  unfold affine_test, test_check.
  destruct cmp.
  - destruct (Z.ltb_spec (view_z w sg (a + step * Z.of_N i)) (view_z w sg bound))
      as [Hword | Hword];
      destruct (N.leb_spec0 (Z.to_N (wrap w (bound + floor_sign_bias w sg)))
        ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + floor_sign_bias w sg))) mod
          N.pos (word_period w))) as [Hnumeric | Hnumeric]; try reflexivity;
      lia.
  - destruct (Z.leb_spec (view_z w sg (a + step * Z.of_N i)) (view_z w sg bound))
      as [Hword | Hword];
      destruct (N.leb_spec0 (N.succ (Z.to_N (wrap w (bound + floor_sign_bias w sg))))
        ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + floor_sign_bias w sg))) mod
          N.pos (word_period w))) as [Hnumeric | Hnumeric]; try reflexivity;

      lia.
  - destruct (Z.eqb_spec (view_z w sg (a + step * Z.of_N i)) (view_z w sg bound))
      as [Hword | Hword];
      destruct (N.eqb_spec
        ((Z.to_N (wrap w step) * i + Z.to_N (wrap w (a + floor_sign_bias w sg))) mod
          N.pos (word_period w)) (Z.to_N (wrap w (bound + floor_sign_bias w sg))))
      as [Hnumeric | Hnumeric]; cbn; try reflexivity.
    + exfalso; apply Hnumeric, N2Z.inj; lia.
    + apply (f_equal Z.of_N) in Hnumeric; lia.
Qed.

(** The fixed count sums exactly one indicator for each failed wrapped comparison. *)
Lemma floor_mod_count_total w sg cmp a step bound limit :
  scev_mod_count w sg cmp a step bound limit =
    floor_total (fun i => if affine_test w sg cmp a step bound i then 0 else 1) limit.
Proof.
  pose proof (floor_target_bound w sg bound) as Htarget.
  unfold scev_mod_count; fold (floor_sign_bias w sg).
  destruct cmp.
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

(** The finite witness contains exactly the failed indices, with no duplicates. *)
Lemma floor_failed_indices_exist (test : N -> bool) limit :
  exists indices : list N,
    NoDup indices /\
    (forall k, In k indices <-> k < limit /\ test k = false) /\
    floor_total (fun i => if test i then 0 else 1) limit = N.of_nat (length indices).
Proof.
  induction limit using N.peano_ind.
  - exists nil; split; [constructor |].
    split; [intros k; cbn; lia | reflexivity].
  - destruct IHlimit as [indices [Hnodup [Hindices Hcount]]].
    destruct (test limit) eqn:Hlast.
    + exists indices; split; [exact Hnodup |].
      split.
      * intros k; rewrite Hindices.
        split; intros [Hbound Hfailed]; split; try lia; try exact Hfailed.
        assert (Hdifferent : k <> limit) by (intro Hequal; subst; congruence).
        lia.
      * rewrite floor_total_succ, Hlast, Hcount; lia.
    + exists (limit :: indices)%list; split.
      * constructor; [rewrite Hindices; lia | exact Hnodup].
      * split.
        -- intros k; cbn; rewrite Hindices.
           split.
           ++ intros [Hequal | [Hbound Hfailed]]; subst; split; try lia; assumption.
           ++ intros [Hbound Hfailed].
              destruct (N.eq_dec limit k) as [Hequal | Hdifferent]; [left; exact Hequal |].
              right; split; [lia | exact Hfailed].
        -- rewrite floor_total_succ, Hlast, Hcount; cbn [length].
           rewrite Nat2N.inj_succ; lia.
Qed.

(** Every public modular count equals the number of distinct failed indices in its prefix. *)
Theorem scev_mod_count_exact : forall (w : width) (sg : signedness) (cmp : cmp_kind)
    (a step bound : Z) (limit : N),
  exists indices : list N,
    audit_failed_indices w sg cmp a step bound limit indices /\
    scev_mod_count w sg cmp a step bound limit = N.of_nat (length indices).
Proof.
  intros w sg cmp a step bound limit.
  destruct (floor_failed_indices_exist (affine_test w sg cmp a step bound) limit)
    as [indices [Hnodup [Hindices Hcount]]].
  exists indices; split.
  - split; assumption.
  - rewrite floor_mod_count_total; exact Hcount.
Qed.
