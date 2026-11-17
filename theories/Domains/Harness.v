(** * Transfer harness

    The harness combines concrete singleton evaluation with abstract transfer tables.
    For example, an unmodeled forward operation returns top.

    Main results
    - [is_bot_sound] Recognized bottoms represent no value.
    - [point_sound] A recognized singleton identifies every represented value.
    - [abst_sound] Abstraction retains its concrete argument.
    - [fwd_sound] A modeled forward entry retains concrete results.
    - [bwd_sound] A modeled backward entry retains consistent operands.
    - [grd_sound] A modeled guard entry retains satisfying operands.
    - [forward_complexity] Forward transfer has the published operator-work class, O(work o xs).
    - [backward_complexity] Backward transfer has the published work-plus-request class,
      O(work o xs + size r).
    - [guard_complexity] Guard transfer has the published guard-work class, O(gwork g xs).

    Builds on: HarnessSig. *)

From Stdlib Require Import List Arith NArith Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Domains Require Import LangSig HarnessSig.
Import ComplexityNotations.

Module HarnessCode (L : LANG_OPS) (B : HARNESS_BASE_OPS L) (T : TABLE_OPS L B)
    <: HARNESS_OPS L B T.
  Definition t := B.t.
  Definition leb := B.leb.
  Definition bot := B.bot.
  Definition is_bot := B.is_bot.
  Definition join := B.join.
  Definition top := B.top.
  Definition meet := B.meet.
  Definition wparam := B.wparam.
  Definition widen := B.widen.
  Definition narrow := B.narrow.

  Fixpoint points (xs : list B.t) : option (list L.val) :=
    match xs with
    | nil => Some nil
    | x :: rest =>
      match B.point x, points rest with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end
    end.

  Definition forward (o : L.op) (xs : list B.t) : B.t :=
    if existsb B.is_bot xs then B.bot else
    match points xs with
    | Some cs => match L.eval o cs with Some c => B.abst c | None => B.bot end
    | None => match T.fwd o xs with Some r => r | None => B.top end
    end.

  Fixpoint meet_all (xs ys : list B.t) : list B.t :=
    match xs, ys with
    | x :: rest, y :: tail => B.meet x y :: meet_all rest tail
    | _, _ => xs
    end.

  Definition backward (o : L.op) (r : B.t) (xs : list B.t) : list B.t :=
    match T.bwd o r xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs
    end.

  Definition guard (g : L.guard) (xs : list B.t) : list B.t :=
    match T.grd g xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs
    end.
End HarnessCode.

Module Harness (L : LANG) (B : HARNESS_BASE L) (T : TABLE L B) <: HARNESS L B T.
  Include HarnessCode L B T.
  Definition leb_refl := B.leb_refl.
  Definition leb_trans := B.leb_trans.
  Definition bot_least := B.bot_least.
  Definition is_bot_bot := B.is_bot_bot.
  Definition is_bot_least := B.is_bot_least.
  Definition join_ub_l := B.join_ub_l.
  Definition join_ub_r := B.join_ub_r.
  Definition top_greatest := B.top_greatest.
  Definition meet_lb_l := B.meet_lb_l.
  Definition wrank := B.wrank.
  Definition widen_ub_l := B.widen_ub_l.
  Definition widen_ub_r := B.widen_ub_r.
  Definition widen_stable := B.widen_stable.
  Definition wrank_widen := B.wrank_widen.
  Definition wrank_widen_le := B.wrank_widen_le.
  Definition narrow_between := B.narrow_between.
  Definition gamma := B.gamma.
  Definition gamma_mono := B.gamma_mono.
  Definition gamma_bot := B.gamma_bot.
  Definition gamma_top := B.gamma_top.
  Definition gamma_meet := B.gamma_meet.
  Definition is_bot_sound := B.is_bot_sound.
  Definition is_bot_below := B.is_bot_below.

  (** Collected singletons agree with every represented operand. *)
  Lemma points_sound_aux : forall xs cs vs,
    Forall2 gamma xs cs -> points xs = Some vs -> vs = cs.
  Proof.
    intros xs cs vs Hxs. revert vs.
    induction Hxs as [|x c xs cs Hx Hxs IH]; intros vs Hp.
    - inversion Hp. reflexivity.
    - cbn [points] in Hp.
      destruct (B.point x) as [v|] eqn:Hv; [|discriminate].
      destruct (points xs) as [tail|] eqn:Htail; [|discriminate].
      inversion Hp; subst vs. f_equal.
      + symmetry. exact (B.point_sound x v c Hv Hx).
      + apply IH. reflexivity.
  Qed.

  (** Successful collection records a singleton equation for each operand. *)
  Lemma points_complete : forall xs cs, points xs = Some cs ->
    Forall2 (fun x c => B.point x = Some c) xs cs.
  Proof.
    induction xs as [|x xs IH]; intros cs Hp.
    - inversion Hp. constructor.
    - cbn [points] in Hp.
      destruct (B.point x) as [c|] eqn:Hpoint; [|discriminate].
      destruct (points xs) as [tail|] eqn:Htail; [|discriminate].
      inversion Hp; subst cs. constructor.
      + exact Hpoint.
      + apply IH. reflexivity.
  Qed.

  (** A represented operand list contains no recognized bottom. *)
  Lemma no_bot : forall xs cs,
    Forall2 gamma xs cs -> existsb B.is_bot xs = false.
  Proof.
    intros xs cs Hxs.
    induction Hxs as [|x c xs cs Hx Hxs IH]; cbn [existsb].
    - reflexivity.
    - destruct (B.is_bot x) eqn:Hbot; [|exact IH].
      exfalso. exact (B.is_bot_sound x c Hbot Hx).
  Qed.

  (** Leaving the operands unchanged is a positional refinement. *)
  Lemma self_refines : forall xs,
    Forall2 (fun y x => B.leb y x = true) xs xs.
  Proof.
    induction xs as [|x xs IH]; constructor.
    - apply B.leb_refl.
    - exact IH.
  Qed.

  (** Positional meets retain values represented by both input lists. *)
  Lemma meet_all_sound_aux : forall xs ys cs, length ys = length xs ->
    Forall2 gamma xs cs -> Forall2 gamma ys cs ->
    Forall2 gamma (meet_all xs ys) cs.
  Proof.
    intros xs ys cs Hlength Hxs. revert ys Hlength.
    induction Hxs as [|x c xs cs Hx Hxs IH]; intros ys Hlength Hys.
    - destruct ys; [constructor|discriminate].
    - inversion Hys as [|y d tail ds Hy Htail]; subst.
      cbn [meet_all]. constructor.
      + apply B.gamma_meet; assumption.
      + apply IH; [cbn in Hlength; lia|exact Htail].
  Qed.

  (** Positional meets descend even when the candidate list has another length. *)
  Lemma meet_all_refines_aux : forall xs ys,
    Forall2 (fun y x => B.leb y x = true) (meet_all xs ys) xs.
  Proof.
    induction xs as [|x xs IH]; intros ys; destruct ys as [|y ys];
      cbn [meet_all]; try apply self_refines.
    constructor.
    - apply B.meet_lb_l.
    - apply IH.
  Qed.

  (** Positional meet always retains the original list length. *)
  Lemma meet_all_length : forall xs ys, length (meet_all xs ys) = length xs.
  Proof.
    induction xs as [|x xs IH]; intros ys; destruct ys as [|y ys];
      cbn [meet_all length]; try reflexivity.
    now rewrite IH.
  Qed.

  (** Forward dispatch retains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hxs Heval. unfold forward.
    rewrite (no_bot xs cs Hxs).
    destruct (points xs) as [vs|] eqn:Hpoints.
    - pose proof (points_sound_aux xs cs vs Hxs Hpoints) as ->.
      rewrite Heval. apply B.abst_sound.
    - destruct (T.fwd o xs) as [r|] eqn:Hfwd.
      + eapply T.fwd_sound; eauto.
      + apply B.gamma_top.
  Qed.

  (** Backward dispatch retains every consistent concrete operand. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hxs Heval Hr. unfold backward.
    destruct (T.bwd o r xs) as [ys|] eqn:Hbwd; [|exact Hxs].
    destruct (Nat.eqb (length ys) (length xs)) eqn:Hlength; [|exact Hxs].
    apply Nat.eqb_eq in Hlength.
    eapply meet_all_sound_aux; [exact Hlength|exact Hxs|].
    eapply T.bwd_sound; eauto.
  Qed.

  (** Backward dispatch refines every operand in place. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. unfold backward, leb.
    destruct (T.bwd o r xs) as [ys|]; [|apply self_refines].
    destruct (Nat.eqb (length ys) (length xs));
      [apply meet_all_refines_aux|apply self_refines].
  Qed.

  (** Guard dispatch retains every operand satisfying the guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hxs Hholds. unfold guard.
    destruct (T.grd g xs) as [ys|] eqn:Hgrd; [|exact Hxs].
    destruct (Nat.eqb (length ys) (length xs)) eqn:Hlength; [|exact Hxs].
    apply Nat.eqb_eq in Hlength.
    eapply meet_all_sound_aux; [exact Hlength|exact Hxs|].
    eapply T.grd_sound; eauto.
  Qed.

  (** Guard dispatch refines every operand in place. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. unfold guard, leb.
    destruct (T.grd g xs) as [ys|]; [|apply self_refines].
    destruct (Nat.eqb (length ys) (length xs));
      [apply meet_all_refines_aux|apply self_refines].
  Qed.
End Harness.

Module HarnessT (L : LANG_T) (B : HARNESS_BASE_T L) (T : TABLE_T L B)
    <: HARNESS_ALL L B T.
  Include Harness L B T.
  TimeFun leb.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun points.
  TimeFun forward.
  TimeFun meet_all.
  TimeFun backward.
  TimeFun guard.

  Definition opt_vals (xs : list B.t) : list L.val :=
    match points xs with Some cs => cs | None => nil end.
  Definition size (a : t) : nat := B.bsize a.
  Definition work (o : L.op) (xs : list t) : nat :=
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
      L.work o (opt_vals xs) + T.twork o xs.
  Definition gwork (g : L.guard) (xs : list t) : nat :=
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs + T.tgwork g xs.
  Definition wsize (p : wparam) : nat := B.wsize p.
  Definition wunits (_ : t) : nat := 0.
  (** A singleton scan charges the sum of the sizes of its operands. *)
  Local Lemma points_time_bound : forall xs,
    (T_points xs <= (B.c_base + 1) *
      N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1))%N.
  Proof.
    induction xs as [|x xs IH].
    - time_step.
    - time_unfold T_points. time_cbn.
      pose proof (B.T_point_le x) as Hpoint.
      destruct (B.point x);
        rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Bottom recognition charges every tested operand at its own size. *)
  Local Lemma bot_scan_time_bound : forall xs,
    (List.T_existsb B.is_bot B.T_is_bot xs <= (B.c_base + 2) *
      N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1))%N.
  Proof.
    induction xs as [|x xs IH].
    - time_step.
    - time_unfold List.T_existsb. time_simpl. time_cbn.
      pose proof (B.T_is_bot_le x) as Hbot.
      rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Positional meets charge only paired elements and the final branch. *)
  Local Lemma meet_all_time_bound : forall xs ys,
    (T_meet_all xs ys <= (B.c_base + 1) *
      N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs) +
        fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intros [|y ys].
    - time_step.
    - time_step.
    - time_step.
    - time_unfold T_meet_all. time_cbn.
      pose proof (B.T_meet_le x y) as Hmeet.
      pose proof (IH ys) as Htail.
      rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** The resulting operands fit within the sizes and lengths of both lists. *)
  Local Lemma meet_all_size_bound : forall xs ys,
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize (meet_all xs ys))) <=
      (B.c_base + 1) *
      N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs) +
        fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intros [|y ys].
    - time_cbn. nia.
    - time_cbn. nia.
    - time_cbn. rewrite !Nat2N.inj_add. time_cbn. nia.
    - time_cbn.
      pose proof (B.meet_size_le x y) as Hmeet.
      pose proof (IH ys) as Htail.
      rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  Definition c_val : N :=
    (64 * (B.c_base + 1) * (T.c_tab + 1) + L.c_lang +
      N.of_nat (B.bsize B.bot + B.bsize B.top) + 8)%N.

  (** The common constant covers a base call and its harness wrapper. *)
  Local Lemma c_val_base : (B.c_base + 1 <= c_val)%N.
  Proof.
    unfold c_val. nia.
  Qed.

  Definition k_table_base : N := ((B.c_base + 1) * (T.c_tab + 1))%N.

  Local Lemma table_base_bounds :
    (1 <= k_table_base /\ T.c_tab <= k_table_base /\ 16 * k_table_base <= c_val)%N.
  Proof.
    unfold k_table_base, c_val. nia.
  Qed.

  Local Lemma table_base_budget : forall budget,
    (budget <= k_table_base * budget /\
      T.c_tab * budget <= k_table_base * budget /\
      16 * (k_table_base * budget) <= c_val * budget)%N.
  Proof.
    intro budget. destruct table_base_bounds as [Hone [Htable Hconstant]].
    split.
    - replace budget with (1 * budget)%N at 1 by ring. now apply N.mul_le_mono_r.
    - split.
      + now apply N.mul_le_mono_r.
      + replace (16 * (k_table_base * budget))%N with
          ((16 * k_table_base) * budget)%N by ring. now apply N.mul_le_mono_r.
  Qed.

  (** A table result and the original operands share one product cost coefficient. *)
  Local Lemma meet_table_budget : forall xs ys budget,
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1) <= budget)%N ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <= T.c_tab * budget)%N ->
    (T_meet_all xs ys <= k_table_base * budget)%N /\
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize (meet_all xs ys))) <=
      k_table_base * budget)%N.
  Proof.
    intros xs ys budget Hinput Houtput.
    assert (Hcombined : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize xs) +
       fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1) <=
      (T.c_tab + 1) * budget)%N).
    { rewrite !Nat2N.inj_add in *. rewrite N.mul_add_distr_r. lia. }
    assert (Hscaled : ((B.c_base + 1) * N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize xs) +
       fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1) <=
      k_table_base * budget)%N).
    { unfold k_table_base. replace ((B.c_base + 1) * (T.c_tab + 1) * budget)%N with
        ((B.c_base + 1) * ((T.c_tab + 1) * budget))%N by ring.
      now apply N.mul_le_mono_l. }
    split.
    - eapply N.le_trans; [apply meet_all_time_bound|exact Hscaled].
    - eapply N.le_trans; [apply meet_all_size_bound|exact Hscaled].
  Qed.

  (** Abstraction result size composes the base and table work bounds. *)
  Local Lemma abst_table_budget : forall v budget,
    (1 <= budget)%N -> (N.of_nat (B.abst_work v) <= T.c_tab * budget)%N ->
    (N.of_nat (B.bsize (B.abst v)) <= k_table_base * budget)%N.
  Proof.
    intros v budget Hbudget Hwork.
    assert (Hplus : (N.of_nat (B.abst_work v + 1) <= (T.c_tab + 1) * budget)%N).
    { rewrite Nat2N.inj_add, N.mul_add_distr_r. lia. }
    eapply N.le_trans; [apply B.abst_size_le|]. unfold k_table_base.
    replace ((B.c_base + 1) * (T.c_tab + 1) * budget)%N with
      ((B.c_base + 1) * ((T.c_tab + 1) * budget))%N by ring.
    apply N.mul_le_mono; [lia|exact Hplus].
  Qed.

  Local Lemma closed_sizes_budget : forall budget, (1 <= budget)%N ->
    (N.of_nat (B.bsize B.bot) <= c_val * budget)%N /\
    (N.of_nat (B.bsize B.top) <= c_val * budget)%N.
  Proof.
    intros budget Hbudget.
    assert (Hclosed : (N.of_nat (B.bsize B.bot) + N.of_nat (B.bsize B.top) <= c_val)%N).
    { unfold c_val. rewrite Nat2N.inj_add. lia. }
    assert (Hscaled : (c_val <= c_val * budget)%N).
    { replace c_val with (c_val * 1)%N at 1 by ring. now apply N.mul_le_mono_l. }
    split; lia.
  Qed.

  Definition c_lat : N := c_val.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. pose proof c_val_base. lia.
  Qed.
  Lemma T_leb_le : forall a b, (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. unfold size.
    pose proof (B.T_leb_le a b) as Hbase.
    pose proof c_val_base as Hconstant.
    time_unfold T_leb. nia.
  Qed.
  Lemma T_join_le : forall a b, (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. unfold size.
    pose proof (B.T_join_le a b) as Hbase.
    pose proof c_val_base as Hconstant.
    time_unfold T_join. nia.
  Qed.
  Lemma T_meet_le : forall a b, (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. unfold size.
    pose proof (B.T_meet_le a b) as Hbase.
    pose proof c_val_base as Hconstant.
    time_unfold T_meet. nia.
  Qed.
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intros a. unfold size.
    pose proof (B.T_is_bot_le a) as Hbase.
    pose proof c_val_base as Hconstant.
    time_unfold T_is_bot. nia.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. unfold size, wsize.
    pose proof (B.T_widen_le p a b) as Hbase.
    pose proof c_val_base as Hconstant.
    time_unfold T_widen. nia.
  Qed.
  Lemma T_narrow_le : forall a b, (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. unfold size.
    pose proof (B.T_narrow_le a b) as Hbase.
    pose proof c_val_base as Hconstant.
    time_unfold T_narrow. nia.
  Qed.
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. unfold work, opt_vals, t. time_unfold T_forward.
    pose proof (bot_scan_time_bound xs) as Hscan.
    pose proof (points_time_bound xs) as Hpoints.
    change (fun x : B.t => B.T_is_bot x) with B.T_is_bot.
    destruct (existsb B.is_bot xs) eqn:Hbot.
    - unfold c_val. rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
    - destruct (points xs) as [cs|] eqn:Hcs.
      + pose proof (L.T_eval_le o cs) as Heval.
        destruct (L.eval o cs) as [v|] eqn:Hv.
        * pose proof (B.T_abst_le v) as Habst.
          pose proof (T.T_abst_le v xs o cs Hv (points_complete xs cs Hcs)) as Hwork.
          unfold c_val. rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
        * unfold c_val. rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
      + pose proof (T.T_fwd_le o xs) as Htable.
        unfold c_val. rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. set (budget := N.of_nat (work o xs + size r + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hinput : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1) <= budget)%N).
    { unfold budget, work, size, t. rewrite !Nat2N.inj_add. lia. }
    assert (Hwork : (N.of_nat (T.twork o xs + B.bsize r + 1) <= budget)%N).
    { unfold budget, work, size, t. rewrite !Nat2N.inj_add. lia. }
    assert (Htable : (T.T_bwd o r xs <= T.c_tab * budget)%N).
    { eapply N.le_trans; [apply T.T_bwd_le|]. now apply N.mul_le_mono_l. }
    destruct (table_base_budget budget) as [Hdom [Htabdom Htotal]].
    time_unfold T_backward. destruct (T.bwd o r xs) as [ys|] eqn:Hys.
    - assert (Houtput : (N.of_nat
        (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <= T.c_tab * budget)%N).
      { eapply N.le_trans; [exact (T.bwd_size_le o r xs ys Hys)|].
        now apply N.mul_le_mono_l. }
      destruct (meet_table_budget xs ys budget Hinput Houtput) as [Hmeet Hsize].
      assert (Hlenxs : (N.of_nat (length xs) <= budget)%N).
      { rewrite !Nat2N.inj_add in Hinput. lia. }
      assert (Hlenys : (N.of_nat (length ys) <= T.c_tab * budget)%N).
      { rewrite Nat2N.inj_add in Houtput. lia. }
      pose proof (Datatypes.T_length_le xs) as Hxsclock.
      pose proof (Datatypes.T_length_le ys) as Hysclock.
      pose proof (Nat.T_eqb_le (length ys) (length xs)) as Heqclock.
      unfold t in *. destruct (Nat.eqb (length ys) (length xs)); lia.
    - lia.
  Qed.
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. set (budget := N.of_nat (gwork g xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hinput : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1) <= budget)%N).
    { unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    assert (Hwork : (N.of_nat (T.tgwork g xs + 1) <= budget)%N).
    { unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    assert (Htable : (T.T_grd g xs <= T.c_tab * budget)%N).
    { eapply N.le_trans; [apply T.T_grd_le|]. now apply N.mul_le_mono_l. }
    destruct (table_base_budget budget) as [Hdom [Htabdom Htotal]].
    time_unfold T_guard. destruct (T.grd g xs) as [ys|] eqn:Hys.
    - assert (Houtput : (N.of_nat
        (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <= T.c_tab * budget)%N).
      { eapply N.le_trans; [exact (T.grd_size_le g xs ys Hys)|].
        now apply N.mul_le_mono_l. }
      destruct (meet_table_budget xs ys budget Hinput Houtput) as [Hmeet Hsize].
      assert (Hlenxs : (N.of_nat (length xs) <= budget)%N).
      { rewrite !Nat2N.inj_add in Hinput. lia. }
      assert (Hlenys : (N.of_nat (length ys) <= T.c_tab * budget)%N).
      { rewrite Nat2N.inj_add in Houtput. lia. }
      pose proof (Datatypes.T_length_le xs) as Hxsclock.
      pose proof (Datatypes.T_length_le ys) as Hysclock.
      pose proof (Nat.T_eqb_le (length ys) (length xs)) as Heqclock.
      unfold t in *. destruct (Nat.eqb (length ys) (length xs)); lia.
    - lia.
  Qed.
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. set (budget := N.of_nat (work o xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hwork : (N.of_nat (T.twork o xs + 1) <= budget)%N).
    { unfold budget, work, t. rewrite !Nat2N.inj_add. lia. }
    destruct (closed_sizes_budget budget Hbudget) as [Hbot Htop].
    destruct (table_base_budget budget) as [Hdom [Htabdom Htotal]].
    change (N.of_nat (B.bsize (forward o xs)) <= c_val * budget)%N.
    unfold forward. destruct (@existsb B.t B.is_bot xs); [exact Hbot|].
    destruct (points xs) as [cs|] eqn:Hcs.
    - destruct (L.eval o cs) as [v|] eqn:Heval; [|exact Hbot].
      pose proof (T.T_abst_le v xs o cs Heval (points_complete xs cs Hcs)) as Hvalue.
      assert (Hvaluework : (N.of_nat (B.abst_work v) <= T.c_tab * budget)%N).
      { eapply N.le_trans; [exact Hvalue|]. now apply N.mul_le_mono_l. }
      pose proof (abst_table_budget v budget Hbudget Hvaluework) as Hsize. lia.
    - destruct (T.fwd o xs) as [r|] eqn:Htable; [|exact Htop].
      assert (Hsize : (N.of_nat (B.bsize r) <= T.c_tab * budget)%N).
      { eapply N.le_trans; [exact (T.fwd_size_le o xs r Htable)|].
        now apply N.mul_le_mono_l. }
      lia.
  Qed.
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. unfold size, meet.
    pose proof (B.meet_size_le a b) as Hbase.
    pose proof c_val_base as Hconstant. nia.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. unfold size, join.
    pose proof (B.join_size_le a b) as Hbase.
    pose proof c_val_base as Hconstant. nia.
  Qed.
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <= c_val *
      N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. unfold size, wsize, widen.
    pose proof (B.widen_size_le p a b) as Hbase.
    pose proof c_val_base as Hconstant. nia.
  Qed.
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. set (budget := N.of_nat (work o xs + size r + 1)).
    assert (Hinput : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1) <= budget)%N).
    { unfold budget, work, size, t. rewrite !Nat2N.inj_add. lia. }
    assert (Hwork : (N.of_nat (T.twork o xs + B.bsize r + 1) <= budget)%N).
    { unfold budget, work, size, t. rewrite !Nat2N.inj_add. lia. }
    assert (Hinputsize : (N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs)) <= budget)%N).
    { rewrite !Nat2N.inj_add in Hinput. lia. }
    destruct (table_base_budget budget) as [Hdom [Htabdom Htotal]].
    change (N.of_nat (fold_right Nat.add 0%nat (map B.bsize (backward o r xs))) <=
      c_val * budget)%N.
    unfold backward. destruct (T.bwd o r xs) as [ys|] eqn:Hys; [|lia].
    assert (Houtput : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <= T.c_tab * budget)%N).
    { eapply N.le_trans; [exact (T.bwd_size_le o r xs ys Hys)|].
      now apply N.mul_le_mono_l. }
    destruct (meet_table_budget xs ys budget Hinput Houtput) as [Hmeet Hsize].
    unfold t in *. destruct (Nat.eqb (length ys) (length xs)); lia.
  Qed.
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. set (budget := N.of_nat (gwork g xs + 1)).
    assert (Hinput : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1) <= budget)%N).
    { unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    assert (Hwork : (N.of_nat (T.tgwork g xs + 1) <= budget)%N).
    { unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    assert (Hinputsize : (N.of_nat (fold_right Nat.add 0%nat (map B.bsize xs)) <= budget)%N).
    { rewrite !Nat2N.inj_add in Hinput. lia. }
    destruct (table_base_budget budget) as [Hdom [Htabdom Htotal]].
    change (N.of_nat (fold_right Nat.add 0%nat (map B.bsize (guard g xs))) <=
      c_val * budget)%N.
    unfold guard. destruct (T.grd g xs) as [ys|] eqn:Hys; [|lia].
    assert (Houtput : (N.of_nat
      (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <= T.c_tab * budget)%N).
    { eapply N.le_trans; [exact (T.grd_size_le g xs ys Hys)|].
      now apply N.mul_le_mono_l. }
    destruct (meet_table_budget xs ys budget Hinput Houtput) as [Hmeet Hsize].
    unfold t in *. destruct (Nat.eqb (length ys) (length xs)); lia.
  Qed.
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof.
    intros o xs.
    change (fold_right Nat.add 0 (map B.bsize xs) <= work o xs).
    unfold work. lia.
  Qed.
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    intros g xs.
    change (fold_right Nat.add 0 (map B.bsize xs) <= gwork g xs).
    unfold gwork. lia.
  Qed.

  Definition c_harness : N := (B.c_base + 1)%N.
  Lemma T_points_le : forall xs,
    (T_points xs <= c_harness *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1)%nat))%N.
  Proof.
    exact points_time_bound.
  Qed.
  Lemma T_meet_all_le : forall xs ys,
    (T_meet_all xs ys <= c_harness *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) +
        fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1)%nat))%N.
  Proof.
    exact meet_all_time_bound.
  Qed.
  (** Forward transfer has the published operator-work class. *)
  Lemma forward_complexity :
    T_forward o xs ∈ 𝑂(N.of_nat ((work o xs)%nat)) for (o, xs).
  Proof.
    exists c_val. intros [o xs] _. cbn [fst snd].
    pose proof (T_forward_le o xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.

  (** Backward transfer also charges the size of its requested result. *)
  Lemma backward_complexity :
    T_backward o r xs ∈ 𝑂(N.of_nat ((work o xs + size r)%nat)) for (o, (r, xs)).
  Proof.
    exists c_val. intros [o [r xs]] _. cbn [fst snd].
    pose proof (T_backward_le o r xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.

  (** Guard transfer has the published guard-work class. *)
  Lemma guard_complexity :
    T_guard g xs ∈ 𝑂(N.of_nat ((gwork g xs)%nat)) for (g, xs).
  Proof.
    exists c_val. intros [g xs] _. cbn [fst snd].
    pose proof (T_guard_le g xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.

  Definition k_points : N := 1%N.
  Definition k_meet : N := c_harness.
  Definition k_forward : N := c_val.
  Definition k_backward : N := 4%N.
  Definition k_guard : N := 4%N.
  Lemma gamma_def : forall a c, gamma a c <-> B.gamma a c.
  Proof.
    reflexivity.
  Qed.
  Lemma leb_def : forall a b, leb a b = B.leb a b.
  Proof.
    reflexivity.
  Qed.
  Lemma join_def : forall a b, join a b = B.join a b.
  Proof.
    reflexivity.
  Qed.
  Lemma meet_def : forall a b, meet a b = B.meet a b.
  Proof.
    reflexivity.
  Qed.
  Lemma size_def : forall a, size a = B.bsize a.
  Proof.
    reflexivity.
  Qed.
  Lemma work_def : forall o xs, work o xs =
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
    L.work o (opt_vals xs) + T.twork o xs.
  Proof.
    reflexivity.
  Qed.
  Lemma gwork_def : forall g xs, gwork g xs =
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs + T.tgwork g xs.
  Proof.
    reflexivity.
  Qed.
  Lemma points_sound : forall xs cs vs,
    Forall2 B.gamma xs cs -> points xs = Some vs -> vs = cs.
  Proof.
    exact points_sound_aux.
  Qed.
  Lemma gamma_no_bot : forall xs cs,
    Forall2 B.gamma xs cs -> existsb B.is_bot xs = false.
  Proof.
    exact no_bot.
  Qed.
  Lemma meet_all_sound : forall xs ys cs, length ys = length xs ->
    Forall2 B.gamma xs cs -> Forall2 B.gamma ys cs ->
    Forall2 B.gamma (meet_all xs ys) cs.
  Proof.
    exact meet_all_sound_aux.
  Qed.
  Lemma meet_all_refines : forall xs ys,
    Forall2 (fun y x => B.leb y x = true) (meet_all xs ys) xs.
  Proof.
    exact meet_all_refines_aux.
  Qed.
  Lemma T_points_split : forall xs, (T_points xs <=
    k_points * (fold_right N.add 0 (map (fun x => B.T_point x + 1) xs) + 1))%N.
  Proof.
    unfold k_points.
    induction xs as [|x xs IH].
    - time_step.
    - time_unfold T_points. time_cbn.
      destruct (B.point x); nia.
  Qed.
  Lemma T_forward_plan_le : forall o xs,
    (T_forward o xs <= k_forward *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
        L.work o (opt_vals xs) + T.twork o xs + 1)%nat))%N.
  Proof.
    exact T_forward_le.
  Qed.
  Lemma T_backward_split : forall o r xs, (T_backward o r xs <= k_backward *
    (T.T_bwd o r xs + N.of_nat ((length xs)%nat) +
     match T.bwd o r xs with
     | Some ys => N.of_nat ((length ys)%nat) + T_meet_all xs ys
     | None => 0
     end + 1))%N.
  Proof.
    intros o r xs. unfold k_backward. time_unfold T_backward.
    destruct (T.bwd o r xs) as [ys|]; [|nia].
    pose proof (Datatypes.T_length_le ys) as Hys.
    pose proof (Datatypes.T_length_le xs) as Hxs.
    pose proof (Nat.T_eqb_le (length ys) (length xs)) as Heq.
    destruct (Nat.eqb (length ys) (length xs)); nia.
  Qed.
  Lemma T_guard_split : forall g xs, (T_guard g xs <= k_guard *
    (T.T_grd g xs + N.of_nat ((length xs)%nat) +
     match T.grd g xs with
     | Some ys => N.of_nat ((length ys)%nat) + T_meet_all xs ys
     | None => 0
     end + 1))%N.
  Proof.
    intros g xs. unfold k_guard. time_unfold T_guard.
    destruct (T.grd g xs) as [ys|]; [|nia].
    pose proof (Datatypes.T_length_le ys) as Hys.
    pose proof (Datatypes.T_length_le xs) as Hxs.
    pose proof (Nat.T_eqb_le (length ys) (length xs)) as Heq.
    destruct (Nat.eqb (length ys) (length xs)); nia.
  Qed.
End HarnessT.
