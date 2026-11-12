(** * Transfer harness

    The harness combines concrete singleton evaluation with abstract transfer tables.
    For example, an unmodeled forward operation returns top.
    Builds on: HarnessSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std BigO.
From Galois.Domains Require Import LangSig HarnessSig.

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
  Definition meet_lb_r := B.meet_lb_r.
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

  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted. (* CONVERT: forward_sound: The variable no_empty was not found. *)

  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted. (* CONVERT: backward_sound: The variable bwd_sound was not found in the current environment. *)

  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted. (* CONVERT: backward_refines: The variable entry_refines was not found in the current environment. *)

  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted.

  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
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
  Definition c_val : N := 1%N. (* STUB *)
  Definition c_lat : N := c_val.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. reflexivity. Qed.
  Lemma T_leb_le : forall a b, (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b, (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_meet_le : forall a b, (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b, (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <= c_val *
      N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof. Admitted. (* STUB *)
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof. Admitted. (* STUB *)

  Definition c_harness : N := 1%N. (* STUB *)
  Lemma T_points_le : forall xs,
    (T_points xs <= c_harness *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_meet_all_le : forall xs ys,
    (T_meet_all xs ys <= c_harness *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) +
        fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Definition k_points : N := 1%N. (* STUB *)
  Definition k_meet : N := 1%N. (* STUB *)
  Definition k_forward : N := 1%N. (* STUB *)
  Definition k_backward : N := 1%N. (* STUB *)
  Definition k_guard : N := 1%N. (* STUB *)
  Lemma F0_gamma : forall a c, gamma a c <-> B.gamma a c.
  Proof. Admitted. (* STUB *)
  Lemma F0_leb : forall a b, leb a b = B.leb a b.
  Proof. Admitted. (* STUB *)
  Lemma F0_join : forall a b, join a b = B.join a b.
  Proof. Admitted. (* STUB *)
  Lemma F0_meet : forall a b, meet a b = B.meet a b.
  Proof. Admitted. (* STUB *)
  Lemma F0_size : forall a, size a = B.bsize a.
  Proof. Admitted. (* STUB *)
  Lemma F0_work : forall o xs, work o xs =
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
    L.work o (opt_vals xs) + T.twork o xs.
  Proof. Admitted. (* STUB *)
  Lemma F0_gwork : forall g xs, gwork g xs =
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs + T.tgwork g xs.
  Proof. Admitted. (* STUB *)
  Lemma F1_points_sound : forall xs cs vs,
    Forall2 B.gamma xs cs -> points xs = Some vs -> vs = cs.
  Proof. Admitted. (* STUB *)
  Lemma F2_no_bot : forall xs cs,
    Forall2 B.gamma xs cs -> existsb B.is_bot xs = false.
  Proof. Admitted. (* STUB *)
  Lemma F3_meet_all_sound : forall xs ys cs, length ys = length xs ->
    Forall2 B.gamma xs cs -> Forall2 B.gamma ys cs ->
    Forall2 B.gamma (meet_all xs ys) cs.
  Proof. Admitted. (* STUB *)
  Lemma F4_meet_all_refines : forall xs ys,
    Forall2 (fun y x => B.leb y x = true) (meet_all xs ys) xs.
  Proof. Admitted. (* STUB *)
  Lemma T1_points : forall xs, (T_points xs <=
    k_points * (fold_right N.add 0 (map (fun x => B.T_point x + 1) xs) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_forward : forall o xs,
    (T_forward o xs <= k_forward *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
        L.work o (opt_vals xs) + T.twork o xs + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_backward : forall o r xs, (T_backward o r xs <= k_backward *
    (T.T_bwd o r xs + N.of_nat ((length xs)%nat) +
     match T.bwd o r xs with
     | Some ys => N.of_nat ((length ys)%nat) + T_meet_all xs ys
     | None => 0
     end + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_guard : forall g xs, (T_guard g xs <= k_guard *
    (T.T_grd g xs + N.of_nat ((length xs)%nat) +
     match T.grd g xs with
     | Some ys => N.of_nat ((length ys)%nat) + T_meet_all xs ys
     | None => 0
     end + 1))%N.
  Proof. Admitted. (* STUB *)
End HarnessT.
