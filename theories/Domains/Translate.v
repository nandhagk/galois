(** * Value domain translation

    Translation reuses a value domain under operator and guard mappings.
    For example, a source operator can dispatch to a target operator before transfer.
    Builds on: LangSig and ValueSig. *)

From Stdlib Require Import List NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Domains Require Import LangSig ValueSig.

Module Type LANG_MORPHISM_OPS := LangSig.LANG_MORPHISM_OPS.

Module TranslateCode (L1 L2 : LANG_OPS) (F : LANG_MORPHISM_OPS L1 L2)
    (D : VALUE_DOMAIN_OPS L2) <: VALUE_DOMAIN_OPS L1.
  Definition t := D.t.
  Definition leb := D.leb.
  Definition bot := D.bot.
  Definition is_bot := D.is_bot.
  Definition join := D.join.
  Definition top := D.top.
  Definition meet := D.meet.
  Definition wparam := D.wparam.
  Definition widen := D.widen.
  Definition narrow := D.narrow.
  Definition forward (o : L1.op) (xs : list t) := D.forward (F.op o) xs.
  Definition backward (o : L1.op) (r : t) (xs : list t) := D.backward (F.op o) r xs.
  Definition guard (g : L1.guard) (xs : list t) := D.guard (F.guard g) xs.
End TranslateCode.

Module Translate (L1 L2 : LANG) (F : LANG_MORPHISM L1 L2)
    (D : VALUE_DOMAIN L2) <: VALUE_DOMAIN L1.
  Include TranslateCode L1 L2 F D.
  Definition wrank := D.wrank.
  Definition gamma (a : t) (c : L1.val) := D.gamma a (F.value c).
  Definition leb_refl := D.leb_refl.
  Definition leb_trans := D.leb_trans.
  Definition bot_least := D.bot_least.
  Definition is_bot_bot := D.is_bot_bot.
  Definition is_bot_least := D.is_bot_least.
  Definition join_ub_l := D.join_ub_l.
  Definition join_ub_r := D.join_ub_r.
  Definition top_greatest := D.top_greatest.
  Definition meet_lb_l := D.meet_lb_l.
  Definition widen_ub_l := D.widen_ub_l.
  Definition widen_ub_r := D.widen_ub_r.
  Definition widen_stable := D.widen_stable.
  Definition wrank_widen := D.wrank_widen.
  Definition wrank_widen_le := D.wrank_widen_le.
  Definition narrow_between := D.narrow_between.
  Definition gamma_mono a b c := D.gamma_mono a b (F.value c).
  Definition gamma_bot c := D.gamma_bot (F.value c).
  Definition gamma_top c := D.gamma_top (F.value c).
  Definition gamma_meet a b c := D.gamma_meet a b (F.value c).
  Definition is_bot_sound a c := D.is_bot_sound a (F.value c).
  Definition is_bot_below := D.is_bot_below.

  (** Source operands represent their mapped concrete values in the target domain. *)
  Local Lemma arguments_to : forall xs cs,
    Forall2 gamma xs cs -> Forall2 D.gamma xs (map F.value cs).
  Proof.
    intros xs cs Hxs. induction Hxs; cbn [map]; constructor; assumption.
  Qed.

  (** Target facts on mapped values describe the original source operands. *)
  Local Lemma arguments_from : forall xs cs,
    Forall2 D.gamma xs (map F.value cs) -> Forall2 gamma xs cs.
  Proof.
    intros xs cs. revert xs. induction cs as [|c cs IH]; intros xs Hxs.
    - inversion Hxs. constructor.
    - inversion Hxs as [|a v tail vs Ha Htail]; subst.
      constructor; [exact Ha|]. now apply IH.
  Qed.

  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L1.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hxs Heval. unfold gamma, forward.
    eapply D.forward_sound; [exact (arguments_to xs cs Hxs)|].
    rewrite F.eval_commutes, Heval. reflexivity.
  Qed.
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L1.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hxs Heval Hr. apply arguments_from.
    eapply D.backward_sound; [exact (arguments_to xs cs Hxs)| |exact Hr].
    rewrite F.eval_commutes, Heval. reflexivity.
  Qed.
  Definition backward_refines o := D.backward_refines (F.op o).
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L1.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hxs Hguard. apply arguments_from.
    apply D.guard_sound; [exact (arguments_to xs cs Hxs)|].
    now apply F.guard_preserves.
  Qed.
  Definition guard_refines g := D.guard_refines (F.guard g).
End Translate.

Module TranslateT (L1 L2 : LANG_T) (F : LANG_MORPHISM_T L1 L2)
    (D : VALUE_DOMAIN_T L2) <: VALUE_DOMAIN_T L1.
  Include Translate L1 L2 F D.
  TimeFun leb.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat := D.size a.
  Definition work (o : L1.op) (xs : list t) : nat :=
    F.op_work o + D.work (F.op o) xs + 1.
  Definition gwork (g : L1.guard) (xs : list t) : nat :=
    F.guard_work g + D.gwork (F.guard g) xs + 1.
  Definition wsize (p : wparam) : nat := D.wsize p.
  Definition wunits (a : t) : nat := D.wunits a.
  Definition c_val : N := (D.c_val + F.c_morphism + 4)%N.
  Definition c_lat : N := c_val.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, c_val. lia.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (D.T_leb_le a b). time_unfold T_leb.
    unfold size, c_val in *. nia.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (D.T_join_le a b). time_unfold T_join.
    unfold size, c_val in *. nia.
  Qed.
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (D.T_meet_le a b). time_unfold T_meet.
    unfold size, c_val in *. nia.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intro a. pose proof (D.T_is_bot_le a). time_unfold T_is_bot.
    unfold size, c_val in *. nia.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. pose proof (D.T_widen_le p a b). time_unfold T_widen.
    unfold size, wsize, c_val in *. nia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (D.T_narrow_le a b). time_unfold T_narrow.
    unfold size, c_val in *. nia.
  Qed.
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. pose proof (F.T_op_le o). pose proof (D.T_forward_le (F.op o) xs).
    time_unfold T_forward. time_cbn. unfold work, t, c_val in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. pose proof (F.T_op_le o).
    pose proof (D.T_backward_le (F.op o) r xs).
    time_unfold T_backward. time_cbn. unfold work, size, t, c_val in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. pose proof (F.T_guard_le g). pose proof (D.T_guard_le (F.guard g) xs).
    time_unfold T_guard. time_cbn. unfold gwork, t, c_val in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. pose proof (D.forward_size (F.op o) xs).
    unfold size, forward, work, t, c_val in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (D.meet_size a b).
    unfold size, meet, c_val in *. nia.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (D.join_size a b).
    unfold size, join, c_val in *. nia.
  Qed.
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <=
      c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. pose proof (D.widen_size p a b).
    unfold size, widen, wsize, c_val in *. nia.
  Qed.
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. pose proof (D.backward_size (F.op o) r xs).
    change (N.of_nat (fold_right Nat.add 0%nat (map D.size (D.backward (F.op o) r xs))) <=
      c_val * N.of_nat (work o xs + D.size r + 1))%N.
    unfold work, t, c_val in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. pose proof (D.guard_size (F.guard g) xs).
    change (N.of_nat (fold_right Nat.add 0%nat (map D.size (D.guard (F.guard g) xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
    unfold gwork, t, c_val in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof.
    intros o xs. pose proof (D.work_sizes (F.op o) xs).
    change (fold_right Nat.add 0%nat (map D.size xs) <= work o xs)%nat.
    unfold work, t in *. lia.
  Qed.
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    intros g xs. pose proof (D.gwork_sizes (F.guard g) xs).
    change (fold_right Nat.add 0%nat (map D.size xs) <= gwork g xs)%nat.
    unfold gwork, t in *. lia.
  Qed.
End TranslateT.
