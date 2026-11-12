(** * Flat constant domain code

    Flat values distinguish bottom, one value and top.
    For example, joining distinct singleton values returns top.
    Builds on: ConstSig and the concrete language operations. *)

From Stdlib Require Import List ZArith Bool Lia.
From Argent Require Import Time Std BigO.
From Galois.Bits Require Import Word Fun Op.
From Galois.Domains Require Import ConstSig LangSig WordSig.
Import List.ListNotations.

Module ConstCode (L : LANG_OPS) (E : VAL_EQ_OPS L) <: CONST_OPS L E.
  Definition t := flat L.val.
  Definition wparam := unit.
  Definition leb (a b : t) : bool :=
    match a, b with
    | FBot, _ => true
    | _, FTop => true
    | FVal x, FVal y => E.eqb x y
    | _, _ => false
    end.
  Definition bot : t := FBot.
  Definition top : t := FTop.
  Definition is_bot (a : t) := match a with FBot => true | _ => false end.
  Definition join (a b : t) : t :=
    match a, b with
    | FBot, _ => b
    | _, FBot => a
    | FVal x, FVal y => if E.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition meet (a b : t) : t :=
    match a, b with
    | FBot, _ | _, FBot => FBot
    | FTop, _ => b
    | _, FTop => a
    | FVal x, FVal y => if E.eqb x y then a else FBot
    end.
  Definition widen (_ : unit) (a b : t) := join a b.
  Definition narrow (a _ : t) := a.
  Definition point (a : t) := match a with FVal x => Some x | _ => None end.
  Definition abst (v : L.val) : t := FVal v.
  Fixpoint points (xs : list t) : option (list L.val) :=
    match xs with
    | [] => Some []
    | FVal x :: rest =>
      match points rest with
      | Some vs => Some (x :: vs)
      | None => None
      end
    | _ => None
    end.
  Definition forward (o : L.op) (xs : list t) : t :=
    if existsb is_bot xs then FBot else
      match points xs with
      | Some vs => match L.eval o vs with Some v => FVal v | None => FBot end
      | None => FTop
      end.
  Definition backward (_ : L.op) (_ : t) (xs : list t) := xs.
  Definition guard (_ : L.guard) (xs : list t) := xs.
End ConstCode.

Module ConstWordCode (L : WORD_LANGUAGE_OPS)
    <: (WORD_PAYLOAD_OPS L with Definition p := flat Z).
  Definition p := flat Z.
  Definition pleb (_ : positive) (a b : p) : bool :=
    match a, b with
    | FBot, _ => true
    | _, FTop => true
    | FVal x, FVal y => Z.eqb x y
    | _, _ => false
    end.
  Definition pjoin (_ : positive) (a b : p) : p :=
    match a, b with
    | FBot, _ => b
    | _, FBot => a
    | FVal x, FVal y => if Z.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition pmeet (_ : positive) (a b : p) : p :=
    match a, b with
    | FBot, _ | _, FBot => FBot
    | FTop, _ => b
    | _, FTop => a
    | FVal x, FVal y => if Z.eqb x y then a else FBot
    end.
  Definition pbot (_ : positive) : p := FBot.
  Definition ptop (_ : positive) : p := FTop.
  Definition pis_bot (_ : positive) (a : p) :=
    match a with FBot => true | _ => false end.
  Definition pconst (w : positive) (z : Z) : p := FVal (Word.wrap w z).
  Definition ppoint (_ : positive) (a : p) : option Z :=
    match a with FVal z => Some z | _ => None end.
  Definition pwparam := unit.
  Definition pwiden (_ : pwparam) w a b := pjoin w a b.
  Definition pnarrow w a b := pmeet w a b.
End ConstWordCode.

Module ConstWordTableCode (L : WORD_LANGUAGE_OPS)
    (W : WORD_PAYLOAD_OPS L with Definition p := flat Z) <: WORD_TABLE_OPS L W.
  Definition const_is (a : flat Z) (z : Z) :=
    match a with FVal x => Z.eqb x z | _ => false end.
  Definition shortcut (o : L.op) (a b : positive * W.p) : option Z :=
    match o with
    | bvmul | bvand =>
      if const_is (snd a) 0 || const_is (snd b) 0 then Some 0 else None
    | bvor =>
      if const_is (snd a) (modulus (fst a) - 1) ||
         const_is (snd b) (modulus (fst a) - 1)
      then Some (modulus (fst a) - 1) else None
    | bvshl | bvlshr | bvashr | bvurem =>
      if const_is (snd a) 0 then Some 0 else None
    | _ => None
    end%Z.
  Definition inverse (f : Z -> Z) (a : flat Z) : flat Z :=
    match a with FVal z => FVal (f z) | _ => FTop end.
  Definition inverse_pair w (f g : Z -> Z) (a b : W.p) :=
    [W.pmeet w a (inverse f b); W.pmeet w b (inverse g a)].
  Definition backward_one o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(_, a)], FVal r =>
      [W.pmeet rw a (FVal (match o with bvnot => wnot rw r | _ => wneg rw r end))]
    | _, _ => map snd xs
    end.
  Definition backward_two o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(w, a); (_, b)], FVal r =>
      match o with
      | bveq => if Z.eqb r 1 then [W.pmeet rw a b; W.pmeet rw b a] else [a; b]
      | bvne => if Z.eqb r 0 then [W.pmeet rw a b; W.pmeet rw b a] else [a; b]
      | bvadd => inverse_pair rw (fun z => wsub w r z) (fun z => wsub w r z) a b
      | bvsub => inverse_pair rw (fun z => wadd w r z) (fun z => wsub w z r) a b
      | bvxor => inverse_pair rw (fun z => wxor w r z) (fun z => wxor w r z) a b
      | _ => [a; b]
      end
    | _, _ => map snd xs
    end%Z.
  Definition wfwd o (_ : positive) (xs : list (positive * W.p)) : option W.p :=
    match o, xs with
    | (bvmul | bvand | bvor | bvshl | bvlshr | bvashr | bvurem), [a; b] =>
      Some (match shortcut o a b with Some c => FVal c | None => FTop end)
    | _, _ => None
    end.
  Definition wbwd o rw q (xs : list (positive * W.p)) : option (list W.p) :=
    match o, xs with
    | (bvnot | bvneg), [_] => Some (backward_one o rw q xs)
    | (bveq | bvne | bvadd | bvsub | bvxor), [_; _] => Some (backward_two o rw q xs)
    | _, _ => None
    end.
End ConstWordTableCode.

Local Close Scope Z_scope.

Module Z.
  TimeFun Z.size_nat.
End Z.

Module Const (L : LANG) (E : VAL_EQ L) <: CONST L E.
  Include ConstCode L E.
  Include CONST_SPEC L E.
  Definition gamma := flat_gamma.
  Definition wrank (_ : wparam) (a : t) : nat := 2 - level a.
  (** Reflected equality is reflexive. *)
  Lemma eqb_refl : forall a, E.eqb a a = true.
  Proof.
    intro a; apply E.eqb_spec; reflexivity.
  Qed.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros [|a|]; cbn [leb]; try reflexivity. apply E.eqb_spec. reflexivity. Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|a|] [|b|] [|c|]; cbn [leb]; intros Hab Hbc;
      try discriminate; try reflexivity.
    apply E.eqb_spec in Hab. subst b. exact Hbc.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros [|a|]; reflexivity. Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|a|] [|b|]; cbn [leb join]; try reflexivity;
      try (apply E.eqb_spec; reflexivity).
    destruct (E.eqb a b); cbn [leb]; [apply E.eqb_spec|]; reflexivity.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|a|] [|b|]; cbn [leb join]; try reflexivity;
      try (apply E.eqb_spec; reflexivity).
    destruct (E.eqb a b) eqn:Hab; cbn [leb].
    - apply E.eqb_spec in Hab. subst b. apply E.eqb_spec. reflexivity.
    - reflexivity.
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof. intros [|a|]; reflexivity. Qed.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros [|x|] [|y|]; cbn [meet leb]; try reflexivity;
      try (apply E.eqb_spec; reflexivity).
    destruct (E.eqb x y); cbn [leb]; auto.
    apply E.eqb_spec. reflexivity.
  Qed.
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intro q. unfold widen. intros [|a|] [|b|]; cbn [leb join]; try reflexivity;
      try apply eqb_refl.
    destruct (E.eqb a b) eqn:Hab; cbn [leb];
      [apply eqb_refl | reflexivity].
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intro q. unfold widen. intros [|a|] [|b|]; cbn [leb join]; try reflexivity;
      try apply eqb_refl.
    destruct (E.eqb a b) eqn:Hab; cbn [leb].
    + apply E.eqb_spec in Hab; subst b; apply eqb_refl.
    + reflexivity.
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* CONVERT: height_wrank: The variable join_rank_grows was not found in the current environment. *)
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* CONVERT: height_wrank: The variable rank_monotone was not found in the current environment. *)
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hba. split; cbn [narrow]; eauto using leb_refl.
  Qed.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    intros [|a|] [|b|] c Hab Hc; cbn [leb gamma flat_gamma] in *;
      try contradiction; try discriminate; try exact I.
    apply E.eqb_spec in Hab. subst b. exact Hc.
  Qed.
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c Hfalse; exact Hfalse.
  Qed.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intro c; exact I.
  Qed.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    intros a b c.
    destruct a as [|x|], b as [|y|]; cbn [gamma flat_gamma meet];
      intros Ha Hb; try contradiction; try assumption.
    subst x y. rewrite (proj2 (E.eqb_spec c c) eq_refl). reflexivity.
  Qed.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros [|z|] c He Hg; try discriminate. exact Hg.
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof. Admitted.
  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted. (* CONVERT: forward_sound: The variable no_empty was not found in the current environment. *)
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hxs Heval Ha. clear Heval Ha.
    induction Hxs as [|x d xs ds Hx Hxs IH]; cbn; constructor.
    - exact Hx.
    - exact IH.
  Qed.
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. induction xs as [|x xs IH]; cbn; constructor.
    - exact (leb_refl x).
    - exact IH.
  Qed.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
End Const.

Module ConstT (L : LANG_T) (E : VAL_EQ_T L) <: CONST_ALL L E.
  Include Const L E.
  TimeFun leb.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun point.
  TimeFun abst.
  TimeFun points.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat :=
    match a with FVal c => E.vsize c | _ => 0 end.
  Definition work (o : L.op) (xs : list t) : nat :=
    match points xs with
    | Some vs =>
      L.work o vs + length xs +
      match L.eval o vs with Some c => E.vsize c | None => 0 end + 1
    | None => length xs + 1
    end.
  Definition gwork (_ : L.guard) (xs : list t) : nat := length xs + 1.
  Definition wsize (_ : wparam) : nat := 0.
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
  Lemma T_forward_le : forall o xs, (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_guard_le : forall g xs, (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
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
    (N.of_nat (size (widen p a b)) <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma work_sizes : forall o xs, fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof. Admitted. (* STUB *)
  Lemma gwork_sizes : forall g xs, fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof. Admitted. (* STUB *)

  Definition c_const : N := 1%N. (* STUB *)
  Lemma T_point_le : forall a, (T_point a <= c_const)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_abst_le : forall c, (T_abst c <= c_const)%N.
  Proof. Admitted. (* STUB *)
  Lemma forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat ((work (fst ox) (snd ox))%nat))
    (fun ox => T_forward (fst ox) (snd ox)))%N.
  Proof. Admitted. (* STUB *)

  Definition k_const_points : N := 1%N. (* STUB *)
  Definition k_const_forward : N := 1%N. (* STUB *)
  Lemma F1_gamma : forall a c, gamma a c <-> flat_gamma a c.
  Proof. Admitted. (* STUB *)
  Lemma F2_widen : forall p a b, widen p a b = join a b.
  Proof. Admitted. (* STUB *)
  Lemma F3_wrank : forall p a, wrank p a = 2 - level a.
  Proof. Admitted. (* STUB *)
  Lemma F4_rank_le : forall a, level a <= 2.
  Proof. Admitted. (* STUB *)
  Lemma F5_points_sound : forall xs cs vs,
    Forall2 gamma xs cs -> points xs = Some vs -> vs = cs.
  Proof. Admitted. (* STUB *)
  Lemma F6_point : forall a, point a = match a with FVal c => Some c | _ => None end.
  Proof. Admitted. (* STUB *)
  Lemma F7_abst : forall c, abst c = FVal c.
  Proof. Admitted. (* STUB *)
  Lemma T1_points : forall xs,
    (T_points xs <= k_const_points * N.of_nat (length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_forward_points : forall o xs cs, points xs = Some cs ->
    (T_forward o xs <= k_const_forward *
      (N.of_nat (length xs) + L.T_eval o cs +
       match L.eval o cs with Some c => T_abst c | None => 0 end + 1))%N.
  Proof. Admitted. (* STUB *)
End ConstT.

Module ConstWord (L : WORD_LANGUAGE) <: CONST_WORD_PAYLOAD L.
  Include ConstWordCode L.
  Definition pgamma (_ : positive) (a : p) (z : Z) : Prop :=
    match a with FBot => False | FVal x => z = x | FTop => True end.
  Definition pwrank (_ : pwparam) (_ : positive) (a : p) : nat :=
    match a with FBot => 2 | FVal _ => 1 | FTop => 0 end.
  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof.
    intros q w. unfold pwiden. intros [|a|] [|b|]; cbn [pleb pjoin]; try reflexivity;
      try apply Z.eqb_refl.
    destruct (Z.eqb a b) eqn:Hab; cbn [pleb];
      [apply Z.eqb_refl | reflexivity].
  Qed.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w. unfold pwiden. intros [|a|] [|b|]; cbn [pleb pjoin]; try reflexivity;
      try apply Z.eqb_refl.
    destruct (Z.eqb a b) eqn:Hab; cbn [pleb].
    + apply Z.eqb_eq in Hab; subst b; apply Z.eqb_refl.
    + reflexivity.
  Qed.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: height_wrank: The variable pleb_trans was not found in the current environment. *)
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: height_wrank: The variable rank_monotone was not found in the current environment. *)
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. intros w [|a|]; cbn [pleb]; auto using Z.eqb_refl. Qed.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w [|a|] [|b|] [|c|]; cbn [pleb]; intros Hab Hbc;
      try discriminate; try reflexivity.
    apply Z.eqb_eq in Hab. subst b. exact Hbc.
  Qed.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. intros w [|a|]; reflexivity. Qed.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof. intros w [|a|]; reflexivity. Qed.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof.
    intros w [|a|] [|b|]; cbn [pleb pjoin]; try reflexivity; try apply Z.eqb_refl.
    destruct (Z.eqb a b); cbn [pleb]; auto using Z.eqb_refl.
  Qed.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof.
    intros w [|a|] [|b|]; cbn [pleb pjoin]; try reflexivity; try apply Z.eqb_refl.
    destruct (Z.eqb a b) eqn:Hab; cbn [pleb].
    - apply Z.eqb_eq in Hab. subst b. apply Z.eqb_refl.
    - reflexivity.
  Qed.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.
    intros w a b.
    destruct a as [|x|], b as [|y|]; cbn [pmeet pleb];
      try reflexivity; try apply Z.eqb_refl.
    destruct (Z.eqb x y); cbn [pleb]; auto using Z.eqb_refl.
  Qed.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w [|a|] [|b|] z Hab Hc; cbn [pleb pgamma] in *;
      try contradiction; try discriminate; try exact I.
    apply Z.eqb_eq in Hab. subst b. exact Hc.
  Qed.
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. intros w z H. exact H. Qed.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. intros. exact I. Qed.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    intros w a b z.
    destruct a as [|x|], b as [|y|]; cbn [pgamma pmeet];
      intros Ha Hb; try contradiction; try assumption.
    subst x y. now rewrite Z.eqb_refl.
  Qed.
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w [|z|] c He Hg; try discriminate. exact Hg.
  Qed.
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof. intros. reflexivity. Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof.
    intros w [|x|] z v Hpoint Hword Hgamma; cbn in Hpoint; try discriminate.
    inversion Hpoint; subst. exact Hgamma.
  Qed.
End ConstWord.

Module ConstWordT (L : WORD_LANGUAGE_T) <: CONST_WORD_PAYLOAD_T L.
  Include ConstWord L.
  TimeFun pleb.
  TimeFun pjoin.
  TimeFun pmeet.
  TimeFun pbot.
  TimeFun ptop.
  TimeFun pis_bot.
  TimeFun pconst.
  TimeFun ppoint.
  TimeFun pwiden.
  TimeFun pnarrow.

  Definition psize (_ : positive) (a : p) : nat :=
    match a with FVal z => Z.size_nat z | _ => 0 end.
  Definition pwsize (_ : pwparam) : nat := 0.
  Definition c_payload : N := 1%N. (* STUB *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
End ConstWordT.

Module ConstWordTable (L : WORD_LANGUAGE) (W : CONST_WORD_PAYLOAD L) <: CONST_WORD_TABLE L W.
  Include ConstWordTableCode L W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* CONVERT: const_table_laws: No product even after head-reduction. *)
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted. (* CONVERT: const_table_laws: No product even after head-reduction. *)
End ConstWordTable.

Module ConstWordTableT (L : WORD_LANGUAGE_T) (W : CONST_WORD_PAYLOAD_T L)
    <: CONST_WORD_TABLE_T L W.
  Include ConstWordTable L W.
  TimeFun const_is.
  TimeFun shortcut.
  TimeFun inverse.
  TimeFun inverse_pair.
  TimeFun backward_one.
  TimeFun backward_two.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_word_table : N := 1%N. (* STUB *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
End ConstWordTableT.
