(** * Reduced value products

    Reduced products apply a fixed number of reduction rounds after transfers.
    For example, backward transfer reduces each paired result.
    Builds on: ProductSig and value products. *)

From Stdlib Require Import List Arith NArith Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig Product.

Module Datatypes.
  TimeFun Corelib.Init.Datatypes.nat_rect.
End Datatypes.

Module Nat.
  TimeFun Nat.iter.
End Nat.

Module ReducedCode (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L)
    (R : REDUCER_OPS A B) (K : ROUNDS) <: REDUCED_OPS L A B R K.
  Definition t := (A.t * B.t)%type.
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot := product_is_bot A.is_bot B.is_bot.
  Definition leb := product_leb A.is_bot B.is_bot A.leb B.leb.
  Definition join := product_pair A.join B.join.
  Definition normalize := product_normalize A.is_bot B.is_bot A.bot B.bot.
  Definition top : t := (A.top, B.top).
  Definition meet (x y : t) : t := normalize (product_pair A.meet B.meet x y).
  Definition wparam := (A.wparam * B.wparam)%type.
  Definition widen := product_widen A.is_bot B.is_bot A.widen B.widen.
  Definition narrow := product_narrow A.is_bot B.is_bot A.narrow B.narrow.
  Definition red (x : t) : t := normalize (Nat.iter K.rounds R.reduce x).
  Definition forward (o : L.op) (xs : list t) : t :=
    red (product_forward A.is_bot B.is_bot A.bot B.bot A.forward B.forward o xs).
  Definition backward (o : L.op) (r : t) (xs : list t) : list t :=
    map red (product_backward A.is_bot B.is_bot A.bot B.bot A.backward B.backward o r xs).
  Definition guard (g : L.guard) (xs : list t) : list t :=
    map red (product_guard A.is_bot B.is_bot A.bot B.bot A.guard B.guard g xs).
End ReducedCode.

Module Reduced (L : LANG) (A B : VALUE_DOMAIN L) (R : VALUE_REDUCER L A B)
    (K : ROUNDS) <: REDUCED L A B R K.
  Include ReducedCode L A B R K.
  Module P := Product L A B.
  Definition wrank (p : wparam) (a : t) : nat :=
    A.wrank (fst p) (fst a) + B.wrank (snd p) (snd a).
  Definition gamma (a : t) (c : L.val) : Prop := A.gamma (fst a) c /\ B.gamma (snd a) c.
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    exact P.leb_refl.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    exact P.leb_trans.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    exact P.bot_least.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    exact P.is_bot_bot.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    exact P.is_bot_least.
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    exact P.join_ub_l.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    exact P.join_ub_r.
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    exact P.top_greatest.
  Qed.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    exact P.meet_lb_l.
  Qed.
  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    exact P.widen_ub_l.
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    exact P.widen_ub_r.
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    exact P.widen_stable.
  Qed.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    exact P.wrank_widen.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    exact P.wrank_widen_le.
  Qed.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    exact P.narrow_between.
  Qed.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    exact P.gamma_mono.
  Qed.
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c [Ha Hb]. exact (A.gamma_bot c Ha).
  Qed.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intro c. change (A.gamma A.top c /\ B.gamma B.top c).
    split; [apply A.gamma_top|apply B.gamma_top].
  Qed.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    exact P.gamma_meet.
  Qed.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    exact P.is_bot_sound.
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    exact P.is_bot_below.
  Qed.

  (** One reduction round preserves every value shared by the two components. *)
  Lemma step_sound : forall x c, gamma x c -> gamma (R.reduce x) c.
  Proof.
    intros [a b] c [Ha Hb]. exact (R.reduce_sound a b c Ha Hb).
  Qed.

  (** Every finite sequence of reduction rounds preserves shared concrete values. *)
  Lemma iter_sound : forall n x c, gamma x c -> gamma (Nat.iter n R.reduce x) c.
  Proof.
    intros n x c Hgamma. induction n as [|n IH].
    - exact Hgamma.
    - apply step_sound. exact IH.
  Qed.

  (** Repeated reduction descends in each original coordinate. *)
  Lemma iter_lower : forall n x,
    A.leb (fst (Nat.iter n R.reduce x)) (fst x) = true /\
    B.leb (snd (Nat.iter n R.reduce x)) (snd x) = true.
  Proof.
    intro n. induction n as [|n IH]; intros [a b].
    - split; [apply A.leb_refl|apply B.leb_refl].
    - change (A.leb (fst (R.reduce (Nat.iter n R.reduce (a, b)))) a = true /\
        B.leb (snd (R.reduce (Nat.iter n R.reduce (a, b)))) b = true).
      destruct (IH (a, b)) as [Ha Hb].
      destruct (Nat.iter n R.reduce (a, b)) as [u v] eqn:Hiter.
      destruct (R.reduce_lower u v) as [Hu Hv]. cbn [fst snd] in Ha, Hb.
      split; [eapply A.leb_trans|eapply B.leb_trans]; eassumption.
  Qed.

  (** Bottom normalization preserves the meaning of the completed reduction. *)
  Lemma red_sound : forall x c, gamma x c -> gamma (red x) c.
  Proof.
    intros x c Hgamma. unfold red. apply P.normalize_sound.
    now apply iter_sound.
  Qed.

  (** Completed reduction descends in both original coordinates. *)
  Lemma red_components_lower : forall x,
    A.leb (fst (red x)) (fst x) = true /\ B.leb (snd (red x)) (snd x) = true.
  Proof.
    intro x. unfold red.
    destruct (P.normalize_components_lower (Nat.iter K.rounds R.reduce x)) as [Hna Hnb].
    destruct (iter_lower K.rounds x) as [Ha Hb].
    split; [eapply A.leb_trans|eapply B.leb_trans]; eassumption.
  Qed.

  (** Completed reduction refines the original product. *)
  Lemma red_lower : forall x, leb (red x) x = true.
  Proof.
    intro x. destruct (red_components_lower x) as [Ha Hb].
    now apply P.components_below.
  Qed.

  (** Mapping reduction preserves the concrete value at every list position. *)
  Lemma map_red_sound : forall xs cs,
    Forall2 gamma xs cs -> Forall2 gamma (map red xs) cs.
  Proof.
    intros xs cs Hfacts. induction Hfacts as [|x c xs cs Hhead Htail IH]; cbn [map].
    - constructor.
    - constructor; [now apply red_sound|exact IH].
  Qed.

  (** Mapping reduction after a positional refinement keeps every result below its input. *)
  Lemma map_red_refines : forall ys xs,
    Forall2 (fun y x => leb y x = true) ys xs ->
    Forall2 (fun y x => leb y x = true) (map red ys) xs.
  Proof.
    intros ys xs Hbelow. induction Hbelow as [|y x ys xs Hhead Htail IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH]. eapply leb_trans; [apply red_lower|exact Hhead].
  Qed.

  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hfacts Heval. apply red_sound.
    exact (P.forward_sound o xs cs c Hfacts Heval).
  Qed.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hfacts Heval Hr. apply map_red_sound.
    exact (P.backward_sound o r xs cs c Hfacts Heval Hr).
  Qed.
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. apply map_red_refines. apply P.backward_refines.
  Qed.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hfacts Hholds. apply map_red_sound.
    exact (P.guard_sound g xs cs Hfacts Hholds).
  Qed.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. apply map_red_refines. apply P.guard_refines.
  Qed.
End Reduced.

Module ReducedT (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) <: REDUCED_ALL L A B R K.
  Include Reduced L A B R K.
  Module PT := ProductT L A B.

  TimeFun bot.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun normalize.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun red.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat := A.size (fst a) + B.size (snd a).
  Definition work (o : L.op) (xs : list t) : nat :=
    A.work o (map fst xs) + B.work o (map snd xs) + length xs.
  Definition gwork (g : L.guard) (xs : list t) : nat :=
    A.gwork g (map fst xs) + B.gwork g (map snd xs) + length xs.
  Definition wsize (p : wparam) : nat := A.wsize (fst p) + B.wsize (snd p).
  Definition wunits (_ : t) : nat := 0.
  Definition k_growth : N := (R.c_reduce + 1)%N.
  Definition k_iter : N := (k_growth ^ N.of_nat K.rounds)%N.
  Definition k_rounds : N := N.of_nat (K.rounds + 1).
  Definition c_red : N := (16 * (PT.k_core + R.c_reduce + 1) * k_iter)%N.
  Definition k_red_budget : N := (c_red * k_rounds)%N.
  Definition c_val : N := (k_red_budget * (PT.c_val + 1) + PT.c_val + 16)%N.
  Definition c_lat : N := c_val.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, c_val. lia.
  Qed.

  Local Lemma product_constant_le : (PT.c_val <= c_val)%N.
  Proof.
    unfold c_val. lia.
  Qed.

  Local Lemma nat_bound : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
  Proof.
    intros n m Hle. lia.
  Qed.

  (** One reduction has the advertised affine size growth. *)
  Lemma reduce_size_bound : forall x,
    (N.of_nat (size (R.reduce x) + 1) <= k_growth * N.of_nat (size x + 1))%N.
  Proof.
    intros [a b]. pose proof (R.reduce_size_le a b) as Hsize.
    change (N.of_nat (size (R.reduce (a, b))) <=
      R.c_reduce * N.of_nat (size (a, b) + 1))%N in Hsize.
    set (budget := N.of_nat (size (a, b) + 1)) in *.
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    rewrite Nat2N.inj_add. unfold k_growth. rewrite N.mul_add_distr_r. lia.
  Qed.

  (** Iterating reduction multiplies the affine size bound at each round. *)
  Lemma iter_size_bound : forall n x,
    (N.of_nat (size (Nat.iter n R.reduce x) + 1) <=
      k_growth ^ N.of_nat n * N.of_nat (size x + 1))%N.
  Proof.
    intro n. induction n as [|n IH]; intro x.
    - change (N.of_nat (size x + 1) <= 1 * N.of_nat (size x + 1))%N. lia.
    - change (N.of_nat (size (R.reduce (Nat.iter n R.reduce x)) + 1) <=
        k_growth ^ N.of_nat (S n) * N.of_nat (size x + 1))%N.
      eapply N.le_trans; [apply reduce_size_bound|].
      rewrite Nat2N.inj_succ, N.pow_succ_r by lia.
      replace (k_growth * k_growth ^ N.of_nat n * N.of_nat (size x + 1))%N with
        (k_growth * (k_growth ^ N.of_nat n * N.of_nat (size x + 1)))%N by ring.
      now apply N.mul_le_mono_l.
  Qed.

  Local Lemma growth_power_pos : forall n, (1 <= k_growth ^ N.of_nat n)%N.
  Proof.
    intro n. replace 1%N with (k_growth ^ 0)%N by apply N.pow_0_r.
    apply N.pow_le_mono_r; unfold k_growth; lia.
  Qed.

  Local Lemma iter_size_prefix : forall fuel n x, (n <= fuel)%nat ->
    (N.of_nat (size (Nat.iter n R.reduce x) + 1) <=
      k_growth ^ N.of_nat fuel * N.of_nat (size x + 1))%N.
  Proof.
    intros fuel n x Hn. eapply N.le_trans; [apply iter_size_bound|].
    apply N.mul_le_mono_r. apply N.pow_le_mono_r; unfold k_growth; lia.
  Qed.

  Local Lemma iter_budget_pos : forall fuel x,
    (1 <= k_growth ^ N.of_nat fuel * N.of_nat (size x + 1))%N.
  Proof.
    intros fuel x. replace 1%N with (1 * 1)%N by reflexivity. apply N.mul_le_mono.
    - apply growth_power_pos.
    - rewrite Nat2N.inj_add. lia.
  Qed.

  (** The derived unary iterator pays two ticks per reduction step. *)
  Lemma iter_clock_zero : forall x,
    Nat.T_iter 0 R.reduce (fun x => R.T_reduce x) x = 2%N.
  Proof.
    intro x. time_unfold @Nat.T_iter. time_unfold @Datatypes.T_nat_rect.
    time_cbn. reflexivity.
  Qed.

  Lemma iter_clock_succ : forall n x,
    Nat.T_iter (S n) R.reduce (fun x => R.T_reduce x) x =
      (Nat.T_iter n R.reduce (fun x => R.T_reduce x) x +
        R.T_reduce (Nat.iter n R.reduce x) + 2)%N.
  Proof.
    intros n x.
    set (rec_clock := Datatypes.T_nat_rect (fun _ : nat => (A.t * B.t)%type)
      x (fun _ : nat => R.reduce) (fun _ a => (1 + R.T_reduce a)%N) n).
    change (1 + (1 + (rec_clock + (1 + R.T_reduce (Nat.iter n R.reduce x)))) =
      (1 + rec_clock) + R.T_reduce (Nat.iter n R.reduce x) + 2)%N.
    ring.
  Qed.

  Local Lemma reduce_time_bound : forall x,
    (R.T_reduce x <= R.c_reduce * N.of_nat (size x + 1))%N.
  Proof.
    intros [a b]. exact (R.T_reduce_le a b).
  Qed.

  (** Every prefix charges a size budget for the full configured fuel. *)
  Lemma iter_clock_prefix : forall fuel n x, (n <= fuel)%nat ->
    (Nat.T_iter n R.reduce (fun x => R.T_reduce x) x <=
      (R.c_reduce + 2) * (N.of_nat n + 1) * k_growth ^ N.of_nat fuel *
        N.of_nat (size x + 1))%N.
  Proof.
    intros fuel n x Hn. set (budget := (k_growth ^ N.of_nat fuel * N.of_nat (size x + 1))%N).
    assert (Hbudget : (1 <= budget)%N) by apply iter_budget_pos.
    assert (Hprefix : forall m, (m <= fuel)%nat ->
      (Nat.T_iter m R.reduce (fun x => R.T_reduce x) x <=
        (R.c_reduce + 2) * (N.of_nat m + 1) * budget)%N).
    { intro m. induction m as [|m IH]; intro Hm.
      - rewrite iter_clock_zero.
        assert (Hfactor : (2 * budget <= (R.c_reduce + 2) * budget)%N).
        { apply N.mul_le_mono_r. lia. }
        change (2 <= (R.c_reduce + 2) * 1 * budget)%N. rewrite N.mul_1_r. lia.
      - assert (Hprev : (m <= fuel)%nat) by lia. specialize (IH Hprev).
        assert (Hcall : (R.T_reduce (Nat.iter m R.reduce x) <= R.c_reduce * budget)%N).
        { eapply N.le_trans; [apply reduce_time_bound|]. apply N.mul_le_mono_l.
          now apply iter_size_prefix. }
        assert (Hstep : (R.T_reduce (Nat.iter m R.reduce x) + 2 <=
          (R.c_reduce + 2) * budget)%N).
        { rewrite N.mul_add_distr_r. lia. }
        rewrite iter_clock_succ, time_of_nat_succ.
        replace ((R.c_reduce + 2) * (N.of_nat m + 1 + 1) * budget)%N with
          ((R.c_reduce + 2) * (N.of_nat m + 1) * budget +
            (R.c_reduce + 2) * budget)%N by ring. lia. }
    replace ((R.c_reduce + 2) * (N.of_nat n + 1) * k_growth ^ N.of_nat fuel *
      N.of_nat (size x + 1))%N with
      ((R.c_reduce + 2) * (N.of_nat n + 1) * budget)%N by (unfold budget; ring).
    now apply Hprefix.
  Qed.

  Local Lemma rounds_positive : (1 <= k_rounds)%N.
  Proof.
    unfold k_rounds. rewrite Nat2N.inj_add. lia.
  Qed.

  Local Lemma red_budget : forall budget,
    ((R.c_reduce + 2) * budget + 4 * (PT.k_core * budget) + budget <=
      16 * (PT.k_core + R.c_reduce + 1) * budget)%N.
  Proof.
    intro budget. replace
      ((R.c_reduce + 2) * budget + 4 * (PT.k_core * budget) + budget)%N with
      ((R.c_reduce + 2 + 4 * PT.k_core + 1) * budget)%N by ring.
    apply N.mul_le_mono_r. lia.
  Qed.

  (** Reduction time includes both iteration growth and final bottom normalization. *)
  Lemma red_time_bound : forall x,
    (T_red x <= k_red_budget * N.of_nat (size x + 1))%N.
  Proof.
    intro x. set (budget := (k_rounds * k_iter * N.of_nat (size x + 1))%N).
    assert (Hinput : (k_iter * N.of_nat (size x + 1) <= budget)%N).
    { unfold budget. replace (k_iter * N.of_nat (size x + 1))%N with
        (1 * (k_iter * N.of_nat (size x + 1)))%N at 1 by ring.
      replace (k_rounds * k_iter * N.of_nat (size x + 1))%N with
        (k_rounds * (k_iter * N.of_nat (size x + 1)))%N by ring.
      apply N.mul_le_mono_r. exact rounds_positive. }
    assert (Hbudget : (1 <= budget)%N).
    { eapply N.le_trans; [apply (iter_budget_pos K.rounds x)|exact Hinput]. }
    assert (Hiter : (Nat.T_iter K.rounds R.reduce (fun x => R.T_reduce x) x <=
      (R.c_reduce + 2) * budget)%N).
    { replace ((R.c_reduce + 2) * budget)%N with
        ((R.c_reduce + 2) * (N.of_nat K.rounds + 1) *
          k_growth ^ N.of_nat K.rounds * N.of_nat (size x + 1))%N
        by (unfold budget, k_rounds, k_iter; rewrite !Nat2N.inj_add;
          change (N.of_nat 1) with 1%N; ring).
      apply iter_clock_prefix. lia. }
    assert (Hnormal : (T_normalize (Nat.iter K.rounds R.reduce x) <=
      4 * (PT.k_core * budget))%N).
    { eapply N.le_trans; [apply PT.normalize_time_bound|].
      replace (4 * (PT.k_core * budget))%N with (4 * PT.k_core * budget)%N by ring.
      apply N.mul_le_mono_l.
      eapply N.le_trans; [apply iter_size_bound|exact Hinput]. }
    pose proof (red_budget budget) as Htotal.
    replace (k_red_budget * N.of_nat (size x + 1))%N with
      (16 * (PT.k_core + R.c_reduce + 1) * budget)%N
      by (unfold k_red_budget, c_red, budget; ring).
    time_unfold T_red. lia.
  Qed.

  Local Lemma sum_N_app : forall xs ys,
    fold_right N.add 0%N (xs ++ ys) =
      (fold_right N.add 0%N xs + fold_right N.add 0%N ys)%N.
  Proof.
    intro xs. induction xs as [|x xs IH]; intro ys; cbn [app fold_right].
    - lia.
    - rewrite IH. lia.
  Qed.

  (** The iterator clock sums every intermediate reducer call and its control cost. *)
  Lemma iter_clock_steps : forall n x,
    Nat.T_iter n R.reduce (fun x => R.T_reduce x) x =
      (N.of_nat n + 2 + fold_right N.add 0%N
        (map (fun i => R.T_reduce (Nat.iter i R.reduce x) + 1)%N (seq 0 n)))%N.
  Proof.
    intro n. induction n as [|n IH]; intro x.
    - rewrite iter_clock_zero. reflexivity.
    - rewrite iter_clock_succ, IH, seq_S, map_app, sum_N_app, time_of_nat_succ.
      cbn [Nat.add map fold_right]. lia.
  Qed.

  Local Lemma sum_clock_length {X : Type} (clock : X -> N) xs :
    (N.of_nat (length xs) <= fold_right N.add 0%N (map (fun x => clock x + 1)%N xs))%N.
  Proof.
    induction xs as [|x xs IH]; cbn [length map fold_right].
    - lia.
    - rewrite time_of_nat_succ. lia.
  Qed.

  (** The reduction wrapper charges only the configured calls and final bottom tests. *)
  Lemma red_time_steps : forall x,
    (T_red x <= 16 *
      (fold_right N.add 0
        (map (fun n => R.T_reduce (Nat.iter n R.reduce x) + 1)
          (seq 0 K.rounds)) +
       A.T_is_bot (fst (Nat.iter K.rounds R.reduce x)) +
       B.T_is_bot (snd (Nat.iter K.rounds R.reduce x)) + 1))%N.
  Proof.
    intro x. pose proof (iter_clock_steps K.rounds x) as Hiter.
    pose proof (sum_clock_length (fun n => R.T_reduce (Nat.iter n R.reduce x))
      (seq 0 K.rounds)) as Hlength. rewrite length_seq in Hlength.
    assert (Hnormal : (T_normalize (Nat.iter K.rounds R.reduce x) <=
      A.T_is_bot (fst (Nat.iter K.rounds R.reduce x)) +
      B.T_is_bot (snd (Nat.iter K.rounds R.reduce x)) + 8)%N).
    { time_unfold T_normalize. time_unfold @T_product_normalize.
      time_unfold @T_product_is_bot. time_cbn. time_pose.
      destruct (product_is_bot A.is_bot B.is_bot (Nat.iter K.rounds R.reduce x)); lia. }
    time_unfold T_red. lia.
  Qed.

  (** Final normalization adds only the closed pair of bottom sizes. *)
  Lemma red_size_bound : forall x,
    (N.of_nat (size (red x)) <= k_red_budget * N.of_nat (size x + 1))%N.
  Proof.
    intro x. set (budget := (k_rounds * k_iter * N.of_nat (size x + 1))%N).
    assert (Hinput : (k_iter * N.of_nat (size x + 1) <= budget)%N).
    { unfold budget. replace (k_iter * N.of_nat (size x + 1))%N with
        (1 * (k_iter * N.of_nat (size x + 1)))%N at 1 by ring.
      replace (k_rounds * k_iter * N.of_nat (size x + 1))%N with
        (k_rounds * (k_iter * N.of_nat (size x + 1)))%N by ring.
      apply N.mul_le_mono_r. exact rounds_positive. }
    assert (Hbudget : (1 <= budget)%N).
    { eapply N.le_trans; [apply (iter_budget_pos K.rounds x)|exact Hinput]. }
    pose proof (iter_size_bound K.rounds x) as Hiter.
    fold k_iter in Hiter. rewrite Nat2N.inj_add in Hiter.
    pose proof (nat_bound _ _ (PT.normalize_size_bound (Nat.iter K.rounds R.reduce x)))
      as Hsize.
    change (N.of_nat (size (red x)) <= N.of_nat
      (size (Nat.iter K.rounds R.reduce x) + A.size A.bot + B.size B.bot))%N in Hsize.
    rewrite !Nat2N.inj_add in Hsize.
    assert (Hbottom : (N.of_nat (A.size A.bot) + N.of_nat (B.size B.bot) <=
      PT.k_core * budget)%N).
    { eapply N.le_trans with (m := PT.k_core).
      - unfold PT.k_core. rewrite Nat2N.inj_add. lia.
      - replace PT.k_core with (PT.k_core * 1)%N at 1 by ring.
        now apply N.mul_le_mono_l. }
    pose proof (red_budget budget) as Htotal.
    replace (k_red_budget * N.of_nat (size x + 1))%N with
      (16 * (PT.k_core + R.c_reduce + 1) * budget)%N
      by (unfold k_red_budget, c_red, budget; ring).
    lia.
  Qed.

  (** Summing the affine reduction budget charges input sizes and list length. *)
  Lemma reduction_budget_sum : forall xs,
    fold_right N.add 0%N (map (fun x => k_red_budget * N.of_nat (size x + 1))%N xs) =
      (k_red_budget * (N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
        N.of_nat (length xs)))%N.
  Proof.
    intro xs. induction xs as [|x xs IH]; cbn [map fold_right length].
    - change (0 = k_red_budget * (0 + 0))%N. ring.
    - rewrite IH, !Nat2N.inj_add. change (N.of_nat 1) with 1%N.
      rewrite time_of_nat_succ. ring.
  Qed.

  (** Reducing a result list preserves the same total affine size budget. *)
  Lemma reduction_sizes_sum : forall xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (map red xs))) <=
      k_red_budget * (N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
        N.of_nat (length xs)))%N.
  Proof.
    intro xs. induction xs as [|x xs IH]; cbn [map fold_right length].
    - lia.
    - rewrite !Nat2N.inj_add, time_of_nat_succ.
      pose proof (red_size_bound x) as Hhead. rewrite Nat2N.inj_add in Hhead.
      replace (k_red_budget *
        (N.of_nat (size x) + N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
          (N.of_nat (length xs) + 1)))%N with
        (k_red_budget * (N.of_nat (size x) + 1) +
          k_red_budget * (N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
            N.of_nat (length xs)))%N by ring. lia.
  Qed.

  (** Mapping reduction adds one list tick per result. *)
  Lemma reduction_map_time : forall xs,
    (ListDef.T_map red (fun x => T_red x) xs <=
      k_red_budget * (N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
        N.of_nat (length xs)) + N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs. pose proof (PT.map_time_sum red (fun x => T_red x)
      (fun x => k_red_budget * N.of_nat (size x + 1))%N xs red_time_bound) as Htime.
    rewrite reduction_budget_sum in Htime. exact Htime.
  Qed.

  Local Lemma composed_budget : forall budget,
    (k_red_budget * (PT.c_val + 1) * budget + PT.c_val * budget + 16 * budget <=
      c_val * budget)%N.
  Proof.
    intro budget. unfold c_val. replace
      (k_red_budget * (PT.c_val + 1) * budget + PT.c_val * budget + 16 * budget)%N with
      ((k_red_budget * (PT.c_val + 1) + PT.c_val + 16) * budget)%N by ring.
    reflexivity.
  Qed.

  (** Forward transfer pays for the plain product and its final reduction. *)
  Lemma forward_time_parts : forall o xs,
    (T_forward o xs <= PT.T_forward o xs + T_red (PT.forward o xs) + 1)%N.
  Proof.
    intros o xs. time_unfold T_forward. time_unfold PT.T_forward.
    unfold PT.forward. lia.
  Qed.

  (** Backward transfer pays for the plain product and a reduction of each result. *)
  Lemma backward_time_parts : forall o r xs,
    (T_backward o r xs <= PT.T_backward o r xs +
      ListDef.T_map red (fun x => T_red x) (PT.backward o r xs) + 1)%N.
  Proof.
    intros o r xs. time_unfold T_backward. time_unfold PT.T_backward.
    unfold PT.backward. lia.
  Qed.

  (** Guard transfer pays for the plain product and a reduction of each result. *)
  Lemma guard_time_parts : forall g xs,
    (T_guard g xs <= PT.T_guard g xs +
      ListDef.T_map red (fun x => T_red x) (PT.guard g xs) + 1)%N.
  Proof.
    intros g xs. time_unfold T_guard. time_unfold PT.T_guard.
    unfold PT.guard. lia.
  Qed.
  Local Lemma scalar_reduction_budget : forall x budget,
    (1 <= budget)%N -> (N.of_nat (size x) <= PT.c_val * budget)%N ->
    (T_red x <= k_red_budget * (PT.c_val + 1) * budget)%N /\
    (N.of_nat (size (red x)) <= k_red_budget * (PT.c_val + 1) * budget)%N.
  Proof.
    intros x budget Hbudget Hsize.
    assert (Hplus : (N.of_nat (size x + 1) <= (PT.c_val + 1) * budget)%N).
    { rewrite Nat2N.inj_add, N.mul_add_distr_r. lia. }
    assert (Hscaled : (k_red_budget * N.of_nat (size x + 1) <=
      k_red_budget * (PT.c_val + 1) * budget)%N).
    { replace (k_red_budget * (PT.c_val + 1) * budget)%N with
        (k_red_budget * ((PT.c_val + 1) * budget))%N by ring.
      now apply N.mul_le_mono_l. }
    split; eapply N.le_trans;
      [apply red_time_bound|exact Hscaled|apply red_size_bound|exact Hscaled].
  Qed.

  Local Lemma list_reduction_budget : forall xs budget,
    (N.of_nat (fold_right Nat.add 0%nat (map size xs)) <= PT.c_val * budget)%N ->
    (N.of_nat (length xs) <= budget)%N ->
    (ListDef.T_map red (fun x => T_red x) xs <=
      k_red_budget * (PT.c_val + 1) * budget + budget + 1)%N /\
    (N.of_nat (fold_right Nat.add 0%nat (map size (map red xs))) <=
      k_red_budget * (PT.c_val + 1) * budget)%N.
  Proof.
    intros xs budget Hsize Hlength.
    assert (Hscaled : (k_red_budget *
      (N.of_nat (fold_right Nat.add 0%nat (map size xs)) + N.of_nat (length xs)) <=
      k_red_budget * (PT.c_val + 1) * budget)%N).
    { replace (k_red_budget * (PT.c_val + 1) * budget)%N with
        (k_red_budget * ((PT.c_val + 1) * budget))%N by ring.
      apply N.mul_le_mono_l. rewrite N.mul_add_distr_r. lia. }
    split.
    - pose proof (reduction_map_time xs). lia.
    - eapply N.le_trans; [apply reduction_sizes_sum|exact Hscaled].
  Qed.

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_leb_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_join_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_meet_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intro a. eapply N.le_trans; [apply PT.T_is_bot_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. eapply N.le_trans; [apply PT.T_widen_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_narrow_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. set (budget := N.of_nat (work o xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    pose proof (PT.T_forward_le o xs) as Hproduct.
    change (PT.T_forward o xs <= PT.c_val * budget)%N in Hproduct.
    assert (Hsize : (N.of_nat (size (PT.forward o xs)) <= PT.c_val * budget)%N).
    { exact (PT.forward_size o xs). }
    destruct (scalar_reduction_budget _ budget Hbudget Hsize) as [Hred Hredsize].
    pose proof (forward_time_parts o xs) as Hparts.
    pose proof (composed_budget budget) as Htotal. lia.
  Qed.
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. set (budget := N.of_nat (work o xs + size r + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    pose proof (PT.T_backward_le o r xs) as Hproduct.
    change (PT.T_backward o r xs <= PT.c_val * budget)%N in Hproduct.
    assert (Hsize : (N.of_nat (fold_right Nat.add 0%nat
      (map size (PT.backward o r xs))) <= PT.c_val * budget)%N).
    { exact (PT.backward_size o r xs). }
    assert (Hlength : (N.of_nat (length (PT.backward o r xs)) <= budget)%N).
    { pose proof (Forall2_length (PT.backward_refines o r xs)) as Heq.
      rewrite Heq. unfold budget, work, t. rewrite !Nat2N.inj_add. lia. }
    destruct (list_reduction_budget _ budget Hsize Hlength) as [Hred Hredsize].
    pose proof (backward_time_parts o r xs) as Hparts.
    pose proof (composed_budget budget) as Htotal. lia.
  Qed.
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. set (budget := N.of_nat (gwork g xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    pose proof (PT.T_guard_le g xs) as Hproduct.
    change (PT.T_guard g xs <= PT.c_val * budget)%N in Hproduct.
    assert (Hsize : (N.of_nat (fold_right Nat.add 0%nat
      (map size (PT.guard g xs))) <= PT.c_val * budget)%N).
    { exact (PT.guard_size g xs). }
    assert (Hlength : (N.of_nat (length (PT.guard g xs)) <= budget)%N).
    { pose proof (Forall2_length (PT.guard_refines g xs)) as Heq.
      rewrite Heq. unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    destruct (list_reduction_budget _ budget Hsize Hlength) as [Hred Hredsize].
    pose proof (guard_time_parts g xs) as Hparts.
    pose proof (composed_budget budget) as Htotal. lia.
  Qed.
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. set (budget := N.of_nat (work o xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hsize : (N.of_nat (size (PT.forward o xs)) <= PT.c_val * budget)%N).
    { exact (PT.forward_size o xs). }
    destruct (scalar_reduction_budget _ budget Hbudget Hsize) as [Hred Hredsize].
    pose proof (composed_budget budget) as Htotal.
    change (N.of_nat (size (red (PT.forward o xs))) <= c_val * budget)%N. lia.
  Qed.
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.meet_size|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.join_size|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <=
      c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. eapply N.le_trans; [apply PT.widen_size|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. set (budget := N.of_nat (work o xs + size r + 1)).
    assert (Hsize : (N.of_nat (fold_right Nat.add 0%nat
      (map size (PT.backward o r xs))) <= PT.c_val * budget)%N).
    { exact (PT.backward_size o r xs). }
    assert (Hlength : (N.of_nat (length (PT.backward o r xs)) <= budget)%N).
    { pose proof (Forall2_length (PT.backward_refines o r xs)) as Heq.
      rewrite Heq. unfold budget, work, t. rewrite !Nat2N.inj_add. lia. }
    destruct (list_reduction_budget _ budget Hsize Hlength) as [Hred Hredsize].
    pose proof (composed_budget budget) as Htotal.
    change (N.of_nat (fold_right Nat.add 0%nat (map size (map red (PT.backward o r xs)))) <=
      c_val * budget)%N. lia.
  Qed.
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. set (budget := N.of_nat (gwork g xs + 1)).
    assert (Hsize : (N.of_nat (fold_right Nat.add 0%nat
      (map size (PT.guard g xs))) <= PT.c_val * budget)%N).
    { exact (PT.guard_size g xs). }
    assert (Hlength : (N.of_nat (length (PT.guard g xs)) <= budget)%N).
    { pose proof (Forall2_length (PT.guard_refines g xs)) as Heq.
      rewrite Heq. unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    destruct (list_reduction_budget _ budget Hsize Hlength) as [Hred Hredsize].
    pose proof (composed_budget budget) as Htotal.
    change (N.of_nat (fold_right Nat.add 0%nat (map size (map red (PT.guard g xs)))) <=
      c_val * budget)%N. lia.
  Qed.
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof.
    exact PT.work_sizes.
  Qed.
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    exact PT.gwork_sizes.
  Qed.
  Lemma T_red_le : forall a b,
    (T_red (a, b) <= c_red * N.of_nat (K.rounds + 1) *
      N.of_nat ((A.size a + B.size b + 1)%nat))%N.
  Proof.
    intros a b. exact (red_time_bound (a, b)).
  Qed.
  Lemma forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat (work (fst ox) (snd ox)))
    (fun ox => T_forward (fst ox) (snd ox)))%N.
  Proof.
    exists c_val. intros [o xs] _. cbn [fst snd].
    pose proof (T_forward_le o xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.
  Lemma backward_bigO : (bigO (fun _ => True)
    (fun x => N.of_nat ((work (fst x) (snd (snd x)) + size (fst (snd x)))%nat))
    (fun x => T_backward (fst x) (fst (snd x)) (snd (snd x))))%N.
  Proof. Admitted. (* STUB *)
  Lemma guard_bigO : (bigO (fun _ => True)
    (fun gx => N.of_nat ((gwork (fst gx) (snd gx))%nat))
    (fun gx => T_guard (fst gx) (snd gx)))%N.
  Proof. Admitted. (* STUB *)

  Definition k_red : N := 16%N.
  Lemma F1_red_eq : forall x,
    red x = let result := Nat.iter K.rounds R.reduce x in
      if orb (A.is_bot (fst result)) (B.is_bot (snd result))
      then (A.bot, B.bot) else result.
  Proof.
    reflexivity.
  Qed.
  Lemma F_is_bot : forall a b,
    is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  Proof.
    reflexivity.
  Qed.
  Lemma F_leb : forall a b,
    leb a b = orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  Proof.
    reflexivity.
  Qed.
  Lemma F_wunits : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  Proof.
    reflexivity.
  Qed.
  Lemma F2_gamma : forall a b c,
    gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  Proof.
    reflexivity.
  Qed.
  Lemma F3_red_sound : forall x c, gamma x c -> gamma (red x) c.
  Proof.
    exact red_sound.
  Qed.
  Lemma F4_red_lower : forall a b,
    A.leb (fst (red (a, b))) a = true /\ B.leb (snd (red (a, b))) b = true.
  Proof.
    intros a b. exact (red_components_lower (a, b)).
  Qed.
  Lemma F5_widen : forall p a b,
    widen p a b = if is_bot b then a
      else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  Proof.
    reflexivity.
  Qed.
  Lemma T1_red_steps : forall x,
    (T_red x <= k_red *
      (fold_right N.add 0
        (map (fun n => R.T_reduce (Nat.iter n R.reduce x) + 1)
          (seq 0 K.rounds)) +
       A.T_is_bot (fst (Nat.iter K.rounds R.reduce x)) +
       B.T_is_bot (snd (Nat.iter K.rounds R.reduce x)) + 1))%N.
  Proof.
    exact red_time_steps.
  Qed.
End ReducedT.
