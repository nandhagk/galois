(** * Flat constant domain code

    Flat values distinguish bottom, one value and top.
    For example, joining distinct singleton values returns top.
    Builds on: ConstSig and the concrete language operations. *)

From Stdlib Require Import List ZArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Bits Require Import Word Fun Op Testbit Arith.
From Galois.Domains Require Import ConstSig LangSig WordSig BitsLang.
Import List.ListNotations WordAlgebra.

Module ConstWordFast.
  Definition wrap_fast (w : positive) (z : Z) : Z := Z.land z (Z.ones (Zpos w)).
  TimeFun wrap_fast.

  (** The mask implements the specified modular word reduction. *)
  Lemma wrap_fast_agrees : forall w z, wrap_fast w z = Word.wrap w z.
  Proof.
    intros w z. symmetry. rewrite Word.wrap_mod. unfold wrap_fast, modulus.
    symmetry. apply Z.land_ones. lia.
  Qed.

  (** The width mask is itself a normalized word. *)
  Lemma mask_is_word w : is_word w (Z.ones (Zpos w)).
  Proof.
    unfold is_word. rewrite Z.ones_equiv, <- Z.sub_1_r.
    fold (modulus w). pose proof (modulus_pos w). lia.
  Qed.

  (** The mask has no bits above its declared width. *)
  Lemma mask_size w : (Z.size_nat (Z.ones (Zpos w)) <= Pos.to_nat w)%nat.
  Proof.
    apply WordTime.word_size_bound, mask_is_word.
  Qed.

  (** Building the mask takes linear time in its numeric width. *)
  Lemma mask_time w : (Z.T_ones (Zpos w) <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    pose proof (Z.T_shiftl_le 1 (Zpos w)) as Hshift.
    pose proof (Z.T_pred_le (Z.shiftl 1 (Zpos w))) as Hpred.
    assert (Hsize : (N.of_nat (Z.size_nat (Z.shiftl 1 (Zpos w))) <=
      N.of_nat (Pos.to_nat w + 1))%N).
    { apply time_of_nat_le. rewrite Z.shiftl_1_l.
      apply WordTime.word_modulus_size_bound. }
    time_unfold Z.T_ones. rewrite Nat2N.inj_add in *.
    time_cbn_all. rewrite positive_nat_N in *. nia.
  Qed.

  (** Masking reads the width mask and raw integer only linearly. *)
  Lemma wrap_fast_time w z :
    (T_wrap_fast w z <= 32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
  Proof.
    pose proof (mask_time w) as Hmask.
    pose proof (Z.T_land_le z (Z.ones (Zpos w))) as Hland.
    pose proof (time_of_nat_le _ _ (mask_size w)) as Hsize.
    time_unfold T_wrap_fast. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
End ConstWordFast.

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
  Definition wrap_fast := ConstWordFast.wrap_fast.
  Definition normalise (w : positive) (a : W.p) : W.p :=
    match a with
    | FVal z => FVal (wrap_fast w z)
    | _ => a
    end.
  Definition normalise_operands (xs : list (positive * W.p)) :=
    map (fun wp => (fst wp, normalise (fst wp) (snd wp))) xs.
  Definition const_is (a : flat Z) (z : Z) :=
    match a with FVal x => Z.eqb x z | _ => false end.
  Definition shortcut (o : L.op) (a b : positive * W.p) : option Z :=
    let a := (fst a, normalise (fst a) (snd a)) in
    let b := (fst b, normalise (fst b) (snd b)) in
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
  Definition backward_one_values o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(_, a)], FVal r =>
      [W.pmeet rw a (FVal (match o with bvnot => wnot rw r | _ => wneg rw r end))]
    | _, _ => map snd xs
    end.
  Definition backward_two_values o rw (q : W.p) (xs : list (positive * W.p)) :=
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
  Definition backward_one o rw (q : W.p) (xs : list (positive * W.p)) :
      option (list W.p) :=
    let q := normalise rw q in
    let xs := normalise_operands xs in
    match o, xs with
    | (bvnot | bvneg), [_] => Some (backward_one_values o rw q xs)
    | _, _ => None
    end.
  Definition backward_two o rw (q : W.p) (xs : list (positive * W.p)) :
      option (list W.p) :=
    let q := normalise rw q in
    let xs := normalise_operands xs in
    match o, xs with
    | (bveq | bvne | bvadd | bvsub | bvxor), [_; _] =>
      Some (backward_two_values o rw q xs)
    | _, _ => None
    end.
  Definition wfwd o (_ : positive) (xs : list (positive * W.p)) : option W.p :=
    match o, xs with
    | (bvmul | bvand | bvor | bvshl | bvlshr | bvashr | bvurem), [a; b] =>
      Some (match shortcut o a b with Some c => FVal c | None => FTop end)
    | _, _ => None
    end.
  Definition wbwd o rw q (xs : list (positive * W.p)) : option (list W.p) :=
    match o, xs with
    | (bvnot | bvneg), [_] => backward_one o rw q xs
    | (bveq | bvne | bvadd | bvsub | bvxor), [_; _] => backward_two o rw q xs
    | _, _ => None
    end.
End ConstWordTableCode.

Local Close Scope Z_scope.

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
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [|a|] b Hbot; try discriminate. reflexivity.
  Qed.
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
  Proof.
    intros [|a|] [|b|]; cbn [meet leb]; try reflexivity; try apply eqb_refl.
    destruct (E.eqb a b) eqn:Hab; cbn [leb]; auto.
  Qed.

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
  Proof.
    intros p [|a|] [|b|]; cbn [leb widen join]; intro Hba;
      try discriminate; try reflexivity.
    apply E.eqb_spec in Hba. subst b. now rewrite eqb_refl.
  Qed.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|a|] [|b|]; unfold wrank; cbn [is_bot leb widen join level];
      intros Hbot Hba; try discriminate; try lia.
    destruct (E.eqb a b) eqn:Hab; cbn [level]; [|lia].
    apply E.eqb_spec in Hab. subst b. rewrite eqb_refl in Hba. discriminate.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p [|a|] [|b|]; unfold wrank; cbn [is_bot widen join level];
      intro Hbot; try discriminate; try lia.
    destruct (E.eqb a b); cbn [level]; lia.
  Qed.
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
  Proof.
    intros [|a|] [|b|]; cbn [leb is_bot]; congruence.
  Qed.

  (** Represented operand lists contain no recognized bottom. *)
  Local Lemma no_bot : forall xs cs,
    Forall2 gamma xs cs -> existsb is_bot xs = false.
  Proof.
    intros xs cs Hxs. induction Hxs as [|a c xs cs Ha Hxs IH].
    - reflexivity.
    - destruct a; cbn [gamma flat_gamma] in Ha; try contradiction;
        cbn [existsb is_bot]; exact IH.
  Qed.

  (** Collecting singleton operands identifies their represented values. *)
  Lemma points_sound_aux : forall xs cs vs,
    Forall2 gamma xs cs -> points xs = Some vs -> vs = cs.
  Proof.
    intros xs cs vs Hxs. revert vs.
    induction Hxs as [|a c xs cs Ha Hxs IH]; intros vs Hpoints.
    - inversion Hpoints. reflexivity.
    - destruct a as [|a|]; cbn [points] in Hpoints; try discriminate.
      cbn [gamma flat_gamma] in Ha. subst c.
      destruct (points xs) as [tail|] eqn:Htail; try discriminate.
      inversion Hpoints; subst vs. f_equal. now apply IH.
  Qed.
  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hxs Heval. unfold forward.
    rewrite (no_bot xs cs Hxs). destruct (points xs) as [vs|] eqn:Hpoints.
    - pose proof (points_sound_aux xs cs vs Hxs Hpoints) as ->.
      rewrite Heval. reflexivity.
    - exact I.
  Qed.
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
  Proof.
    intros g xs cs Hxs _. exact Hxs.
  Qed.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. induction xs as [|a xs IH]; constructor; auto using leb_refl.
  Qed.
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
    let operands := fold_right Nat.add 0%nat (map size xs) in
    match points xs with
    | Some vs =>
      L.work o vs + operands + length xs +
        match L.eval o vs with Some c => E.vsize c | None => 0 end + 1
    | None => operands + length xs + 1
    end.
  Definition gwork (_ : L.guard) (xs : list t) : nat :=
    fold_right Nat.add 0%nat (map size xs) + length xs + 1.
  Definition wsize (_ : wparam) : nat := 0.
  Definition wunits (_ : t) : nat := 0.

  (** Collecting singleton payloads visits at most one cell per operand. *)
  Local Lemma points_time_bound : forall xs,
    (T_points xs <= N.of_nat (length xs + 1))%N.
  Proof.
    induction xs as [|[|a|] xs IH]; time_unfold T_points; time_cbn;
      rewrite ?Nat2N.inj_succ, ?Nat2N.inj_add in *; time_cbn_all; lia.
  Qed.

  (** Bottom recognition charges one constant-time test per visited operand. *)
  Local Lemma bot_scan_time_bound : forall xs,
    (List.T_existsb is_bot T_is_bot xs <= 3 * N.of_nat (length xs + 1))%N.
  Proof.
    induction xs as [|x xs IH].
    - time_step.
    - time_unfold List.T_existsb. time_simpl. time_cbn.
      try time_unfold T_is_bot.
      change (List.T_existsb is_bot (fun _ : t => 1%N) xs <=
        3 * N.of_nat (length xs + 1))%N in IH.
      rewrite ?Nat2N.inj_succ, ?Nat2N.inj_add in *; time_cbn_all.
      lia.
  Qed.

  Definition c_val : N := (E.c_eq + L.c_lang + 8)%N.
  Definition c_lat : N := c_val.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, c_val. lia.
  Qed.
  Lemma T_leb_le : forall a b, (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|a|] [|b|]; time_unfold T_leb; time_cbn; cbn [size]; unfold c_val;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (E.T_eqb_le a b). rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_join_le : forall a b, (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    apply T_leb_le.
  Qed.
  Lemma T_meet_le : forall a b, (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    apply T_leb_le.
  Qed.
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intro a. time_unfold T_is_bot. unfold c_val.
    rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p [|a|] [|b|]; time_unfold T_widen; time_unfold T_join;
      time_cbn; cbn [size wsize]; unfold c_val;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (E.T_eqb_le a b). rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_narrow_le : forall a b, (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. time_unfold T_narrow. unfold c_val.
    rewrite ?Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma T_forward_le : forall o xs, (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. pose proof (points_time_bound xs) as Hpoints.
    pose proof (bot_scan_time_bound xs) as Hscan.
    change (List.T_existsb is_bot (fun x => T_is_bot x) xs <=
      3 * N.of_nat (length xs + 1))%N in Hscan.
    time_unfold T_forward. time_cbn. unfold work, t, c_val in *.
    destruct (points xs) as [cs|] eqn:Hcollect.
    - pose proof (L.T_eval_le o cs) as Heval.
      destruct (@existsb (flat L.val) is_bot xs);
        rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
    - destruct (@existsb (flat L.val) is_bot xs);
        rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. time_unfold T_backward. unfold c_val.
    rewrite ?Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma T_guard_le : forall g xs, (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. time_unfold T_guard. unfold c_val.
    rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. unfold forward, work, t, c_val.
    destruct (@existsb (flat L.val) is_bot xs); destruct (points xs) as [cs|];
      try destruct (L.eval o cs); cbn [size];
      rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|a|] [|b|]; cbn [meet size]; try destruct (E.eqb a b);
      cbn [size]; unfold c_val; rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|a|] [|b|]; cbn [join size]; try destruct (E.eqb a b);
      cbn [size]; unfold c_val; rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. unfold widen, wsize. rewrite Nat.add_0_r. apply join_size.
  Qed.
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. unfold backward, work, t, c_val.
    destruct (points xs); rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. unfold guard, gwork, t, c_val.
    rewrite ?Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma work_sizes : forall o xs, fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof.
    intros o xs. unfold work, t. destruct (points xs); lia.
  Qed.
  Lemma gwork_sizes : forall g xs, fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    intros g xs. unfold gwork, t. lia.
  Qed.

  Definition c_const : N := 1%N.
  Lemma T_point_le : forall a, (T_point a <= c_const)%N.
  Proof.
    intro a. time_unfold T_point. unfold c_const. lia.
  Qed.
  Lemma T_abst_le : forall c, (T_abst c <= c_const)%N.
  Proof.
    intro c. time_unfold T_abst. unfold c_const. lia.
  Qed.
  Lemma forward_complexity : (bigO (fun _ => True)
    (fun ox => N.of_nat ((work (fst ox) (snd ox))%nat))
    (fun ox => T_forward (fst ox) (snd ox)))%N.
  Proof.
    exists c_val. intros [o xs] _. cbn [fst snd].
    pose proof (T_forward_le o xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.

  Definition k_const_points : N := 1%N.
  Definition k_const_forward : N := 8%N.
  Lemma gamma_def : forall a c, gamma a c <-> flat_gamma a c.
  Proof.
    reflexivity.
  Qed.
  Lemma widen_def : forall p a b, widen p a b = join a b.
  Proof.
    reflexivity.
  Qed.
  Lemma wrank_def : forall p a, wrank p a = 2 - level a.
  Proof.
    reflexivity.
  Qed.
  Lemma level_le : forall a, level a <= 2.
  Proof.
    intros [|a|]; cbn [level]; lia.
  Qed.
  Lemma points_sound : forall xs cs vs,
    Forall2 gamma xs cs -> points xs = Some vs -> vs = cs.
  Proof.
    apply points_sound_aux.
  Qed.
  Lemma point_def : forall a, point a = match a with FVal c => Some c | _ => None end.
  Proof.
    reflexivity.
  Qed.
  Lemma abst_def : forall c, abst c = FVal c.
  Proof.
    reflexivity.
  Qed.
  Lemma T_points_le : forall xs,
    (T_points xs <= k_const_points * N.of_nat (length xs + 1))%N.
  Proof.
    intro xs. unfold k_const_points. rewrite N.mul_1_l. apply points_time_bound.
  Qed.
  Lemma T_forward_split : forall o xs cs, points xs = Some cs ->
    (T_forward o xs <= k_const_forward *
      (N.of_nat (length xs) + L.T_eval o cs +
       match L.eval o cs with Some c => T_abst c | None => 0 end + 1))%N.
  Proof.
    intros o xs cs Hcollect. pose proof (points_time_bound xs) as Hpoints.
    pose proof (bot_scan_time_bound xs) as Hscan.
    change (List.T_existsb is_bot (fun x => T_is_bot x) xs <=
      3 * N.of_nat (length xs + 1))%N in Hscan.
    time_unfold T_forward. time_cbn. rewrite Hcollect.
    unfold t in *.
    destruct (@existsb (flat L.val) is_bot xs); destruct (L.eval o cs);
      unfold k_const_forward in *;
      rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  Qed.
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
  Proof.
    intros q w [|a|] [|b|]; cbn [pleb pwiden pjoin]; intro Hba;
      try discriminate; try reflexivity.
    apply Z.eqb_eq in Hba. subst b. now rewrite Z.eqb_refl.
  Qed.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w [|a|] [|b|]; cbn [pis_bot pleb pwiden pjoin pwrank];
      intros Hbot Hba; try discriminate; try lia.
    destruct (Z.eqb a b) eqn:Hab; cbn [pwrank]; [|lia].
    apply Z.eqb_eq in Hab. subst b. rewrite Z.eqb_refl in Hba. discriminate.
  Qed.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof.
    intros q w [|a|] [|b|]; cbn [pis_bot pwiden pjoin pwrank];
      intro Hbot; try discriminate; try lia.
    destruct (Z.eqb a b); cbn [pwrank]; lia.
  Qed.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof.
    intros w [|a|] [|b|]; cbn [pleb pnarrow pmeet]; intro Hba;
      try discriminate; try (split; reflexivity).
    - apply Z.eqb_eq in Hba. subst b. rewrite Z.eqb_refl.
      cbn [pleb]. now rewrite Z.eqb_refl.
    - split; [apply Z.eqb_refl|reflexivity].
  Qed.
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
  Proof.
    reflexivity.
  Qed.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof.
    intros w [|a|] b Hbot; try discriminate. reflexivity.
  Qed.
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
  Proof.
    intros w [|a|] [|b|]; cbn [pmeet pleb]; try reflexivity; try apply Z.eqb_refl.
    destruct (Z.eqb a b) eqn:Hab; cbn [pleb]; auto.
  Qed.
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
  Proof.
    intros w [|a|] [|b|]; cbn [pleb pis_bot]; congruence.
  Qed.
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
  (** A constant payload denotes its stored integer. *)
  Lemma pgamma_const_def : forall w a z, pgamma w a z <->
    match a with FBot => False | FVal x => z = x | FTop => True end.
  Proof.
    reflexivity.
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

  Definition psize (w : positive) (a : p) : nat :=
    Pos.to_nat w + match a with FVal z => Z.size_nat z | _ => 0 end + 1.
  Definition pwsize (_ : pwparam) : nat := 0.
  Definition c_payload : N := 256%N.
  (** Constant payload size includes the width and raw integer bits. *)
  Lemma psize_const_def : forall w a, psize w a =
    Pos.to_nat w + match a with FVal z => Z.size_nat z | _ => 0 end + 1.
  Proof.
    reflexivity.
  Qed.
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w [|a|] [|b|]; unfold pjoin, psize; try destruct (Z.eqb a b);
      time_cbn; unfold c_payload; rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w [|a|] [|b|]; unfold pmeet, psize; try destruct (Z.eqb a b);
      time_cbn; unfold c_payload; rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b. unfold pwiden, pwsize. rewrite Nat.add_0_r. apply pjoin_size.
  Qed.
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    apply pmeet_size.
  Qed.
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w [|a|] [|b|]; time_unfold T_pwiden; time_unfold T_pjoin;
      time_cbn; unfold psize, pwsize, c_payload;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (Z.T_eqb_le a b). rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w [|a|] [|b|]; time_unfold T_pnarrow; time_unfold T_pmeet;
      time_cbn; unfold psize, c_payload;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (Z.T_eqb_le a b). rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w [|a|] [|b|]; time_unfold T_pleb; time_cbn; unfold psize, c_payload;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (Z.T_eqb_le a b). rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    apply T_pleb_le.
  Qed.
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    apply T_pleb_le.
  Qed.
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. time_unfold T_pis_bot. unfold c_payload.
    rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. time_unfold T_ppoint. unfold c_payload.
    rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.
  Lemma T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
  Proof.
    intros w z. pose proof (WordTime.word_wrap_time_bound w z) as Hwrap.
    time_unfold T_pconst. unfold c_payload.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_ptop. unfold c_payload.
    rewrite Nat2N.inj_pow, Nat2N.inj_add. time_cbn. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_pbot. unfold c_payload.
    rewrite Nat2N.inj_pow, Nat2N.inj_add. time_cbn. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold ptop, psize, c_payload.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add. time_cbn. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold pbot, psize, c_payload.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add. time_cbn. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z.
    assert (Hsize : (N.of_nat (Z.size_nat (wrap w z)) <= N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply WordTime.word_wrap_size_bound. }
    unfold pconst, psize, c_payload.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add. time_cbn. nia.
  Qed.
End ConstWordT.

Module ConstWordTable (L : WORD_LANGUAGE) (W : CONST_WORD_PAYLOAD L) <: CONST_WORD_TABLE L W.
  Include ConstWordTableCode L W.
  Local Open Scope Z_scope.

  (** Flat payload meaning does not depend on the surrounding width. *)
  Local Lemma pgamma_width : forall w v a z,
    W.pgamma w a z <-> W.pgamma v a z.
  Proof.
    intros w v a z. rewrite !W.pgamma_const_def. reflexivity.
  Qed.

  (** A payload representing a word is already normalized at that word's width. *)
  Local Lemma normalise_id : forall w a z,
    L.is_word w z -> W.pgamma w a z -> normalise w a = a.
  Proof.
    intros w [|a|] z Hz Ha; try reflexivity.
    apply W.pgamma_const_def in Ha. cbn in Ha. subst z.
    cbn [normalise]. unfold wrap_fast.
    rewrite ConstWordFast.wrap_fast_agrees, wrap_id by exact Hz. reflexivity.
  Qed.

  (** Normalization preserves every operand in a represented word list. *)
  Local Lemma normalise_operands_id : forall xs cs,
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs -> normalise_operands xs = xs.
  Proof.
    intros xs cs Hxs. induction Hxs as [|[w a] [v z] xs cs Ha Hxs IH].
    - reflexivity.
    - destruct Ha as [Hw [Hz Ha]]. cbn in Hw, Hz, Ha. subst v.
      cbn [normalise_operands map fst snd].
      rewrite (normalise_id w a z Hz Ha). f_equal. exact IH.
  Qed.

  (** A recognized constant identifies the represented integer. *)
  Local Lemma const_is_sound : forall w a z c,
    W.pgamma w a z -> const_is a c = true -> z = c.
  Proof.
    intros w [|a|] z c Ha His; apply W.pgamma_const_def in Ha;
      cbn [const_is] in His; cbn in Ha; try contradiction; try discriminate.
    apply Z.eqb_eq in His. congruence.
  Qed.

  (** Recognizing either operand supplies the corresponding constant equation. *)
  Local Lemma const_either : forall w a b x y c,
    W.pgamma w a x -> W.pgamma w b y ->
    const_is a c || const_is b c = true -> x = c \/ y = c.
  Proof.
    intros w a b x y c Ha Hb Htest. apply orb_true_iff in Htest as [Htest|Htest].
    - left. exact (const_is_sound w a x c Ha Htest).
    - right. exact (const_is_sound w b y c Hb Htest).
  Qed.

  (** Each successful shortcut is an annihilator for the concrete operation. *)
  Local Lemma shortcut_at_width : forall o w a b x y rw z c,
    is_word w x -> is_word w y -> W.pgamma w a x -> W.pgamma w b y ->
    eval_op o [(w, x); (w, y)] = Some (rw, z) ->
    shortcut o (w, a) (w, b) = Some c -> z = c.
  Proof.
    intros o w a b x y rw z c Hx Hy Ha Hb Heval Hshortcut.
    unfold shortcut in Hshortcut. cbn [fst snd] in Hshortcut.
    rewrite (normalise_id w a x Hx Ha), (normalise_id w b y Hy Hb) in Hshortcut.
    destruct o; cbn [fst snd] in Hshortcut; try discriminate.
    all: repeat match type of Hshortcut with
      | (if ?test then _ else _) = _ => destruct test eqn:Htest; [|discriminate]
      end; inversion Hshortcut; subst c.
    - pose proof (const_either w a b x y 0 Ha Hb Htest) as Hzero.
      rewrite (eval_op_fun2 bvmul w x y BMul eq_refl) in Heval.
      inversion Heval; subst rw z. destruct Hzero as [-> | ->].
      + exact (proj1 (const_zero_ops w y Hy)).
      + rewrite wmul_comm. exact (proj1 (const_zero_ops w x Hx)).
    - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
      rewrite (eval_op_fun2 bvurem w 0 y BUrem eq_refl) in Heval.
      inversion Heval; subst rw z.
      exact (proj2 (proj2 (proj2 (proj2 (const_zero_ops w y Hy))))).
    - pose proof (const_either w a b x y 0 Ha Hb Htest) as Hzero.
      rewrite (eval_op_fun2 bvand w x y BAnd eq_refl) in Heval.
      inversion Heval; subst rw z. destruct Hzero as [-> | ->].
      + now apply const_zero_bits.
      + rewrite wand_comm. now apply const_zero_bits.
    - pose proof (const_either w a b x y _ Ha Hb Htest) as Hones.
      rewrite (eval_op_fun2 bvor w x y BOr eq_refl) in Heval.
      inversion Heval; subst rw z. destruct Hones as [-> | ->].
      + now apply const_ones_bits.
      + rewrite wor_comm. now apply const_ones_bits.
    - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
      rewrite (eval_op_fun2 bvshl w 0 y BShl eq_refl) in Heval.
      inversion Heval; subst rw z. exact (proj1 (proj2 (const_zero_ops w y Hy))).
    - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
      rewrite (eval_op_fun2 bvlshr w 0 y BLshr eq_refl) in Heval.
      inversion Heval; subst rw z. exact (proj1 (proj2 (proj2 (const_zero_ops w y Hy)))).
    - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
      rewrite (eval_op_fun2 bvashr w 0 y BAshr eq_refl) in Heval.
      inversion Heval; subst rw z.
      exact (proj1 (proj2 (proj2 (proj2 (const_zero_ops w y Hy))))).
  Qed.

  (** A successful shortcut identifies the result on its represented operands. *)
  Lemma shortcut_sound_aux : forall o a b k cs rw z,
    shortcut o a b = Some k ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) [a; b] cs ->
    L.eval_op o cs = Some (rw, z) -> z = k.
  Proof.
    intros o [w a] [v b] k cs rw z Hshortcut Hxs Heval.
    inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
    inversion Htail as [|? [vy y] ? ? Hhead' Hnil]; subst. inversion Hnil; subst.
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Ha, Hb. subst wx vy.
    change (eval_op o [(w, x); (v, y)] = Some (rw, z)) in Heval.
    assert (Hw : w = v).
    { destruct o; cbn [shortcut] in Hshortcut; try discriminate;
        match type of Heval with
        | eval_op ?op _ = _ =>
          eapply (eval_op_fun2_width op _ w v x y (rw, z));
            [reflexivity|exact Heval]
        end. }
    subst v. exact (shortcut_at_width o w a b x y rw z k Hx Hy Ha Hb Heval Hshortcut).
  Qed.

  (** Applying an inverse to a known operand retains its computed preimage. *)
  Local Lemma inverse_sound : forall w f a x y,
    W.pgamma w a y -> x = f y -> W.pgamma w (inverse f a) x.
  Proof.
    intros w f [|a|] x y Ha Hxy; apply W.pgamma_const_def in Ha;
      apply W.pgamma_const_def; cbn [inverse] in *;
      try contradiction; try exact I. now subst y.
  Qed.

  (** The table may meet at the result width because flat meaning ignores widths. *)
  Local Lemma meet_at_width : forall w rw a b z,
    W.pgamma w a z -> W.pgamma w b z -> W.pgamma w (W.pmeet rw a b) z.
  Proof.
    intros w rw a b z Ha Hb. apply (proj1 (pgamma_width rw w _ _)).
    apply W.pgamma_meet; apply (proj1 (pgamma_width w rw _ _)); assumption.
  Qed.

  (** Unary inverse entries retain their represented operand. *)
  Local Lemma backward_one_values_sound : forall o rw q xs cs z,
    (o = bvnot \/ o = bvneg) -> length xs = 1%nat ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) (backward_one_values o rw q xs)) cs.
  Proof.
    intros o rw q xs cs z Ho Hlen Hxs Heval Hq.
    destruct xs as [|[w a] [|wp rest]]; cbn in Hlen; try discriminate.
    inversion Hxs as [|? [v x] ? ? Hhead Hnil]; subst. inversion Hnil; subst.
    destruct Hhead as [Hw [Hx Ha]]. cbn in Hw, Hx, Ha. subst v.
    change (eval_op o [(w, x)] = Some (rw, z)) in Heval.
    apply W.pgamma_const_def in Hq. destruct q as [|r|]; [contradiction| |].
    - cbn in Hq. subst r. destruct Ho as [-> | ->].
      + rewrite (eval_op_fun1 bvnot w x UNot eq_refl) in Heval.
        inversion Heval; subst rw z. cbn [backward_one_values map combine fst snd].
        constructor; [|constructor]. apply W.pgamma_meet; [exact Ha|].
        apply W.pgamma_const_def. cbn. symmetry. now apply wnot_involutive.
      + rewrite (eval_op_fun1 bvneg w x UNeg eq_refl) in Heval.
        inversion Heval; subst rw z. cbn [backward_one_values map combine fst snd].
        constructor; [|constructor]. apply W.pgamma_meet; [exact Ha|].
        apply W.pgamma_const_def. cbn. symmetry. now apply const_neg_inverse.
    - cbn [backward_one_values map combine fst snd]. constructor; [exact Ha|constructor].
  Qed.

  (** Pairing two payload facts preserves both operand positions. *)
  Local Lemma pair_sound : forall w a b x y,
    W.pgamma w a x -> W.pgamma w b y ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      [(w, a); (w, b)] [(w, x); (w, y)].
  Proof.
    intros w a b x y Ha Hb. constructor; [exact Ha|].
    constructor; [exact Hb|constructor].
  Qed.

  (** Successful equality constraints retain both operands at their original width. *)
  Local Lemma backward_comparison_sound : forall o rw w a b x y z,
    (o = bveq \/ o = bvne) -> is_word w x -> is_word w y ->
    W.pgamma w a x -> W.pgamma w b y ->
    eval_op o [(w, x); (w, y)] = Some (rw, z) ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine [w; w] (backward_two_values o rw (FVal z) [(w, a); (w, b)]))
      [(w, x); (w, y)].
  Proof.
    intros o rw w a b x y z Ho Hx Hy Ha Hb Heval. destruct Ho as [-> | ->].
    - rewrite (eval_op_cmp bveq w x y CEq eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite !wrap_id in Heval by assumption.
      destruct (x =? y) eqn:Hxy; inversion Heval; subst rw z;
        cbn [backward_two_values combine fst snd].
      + apply Z.eqb_eq in Hxy. subst y. apply pair_sound; apply meet_at_width; assumption.
      + apply pair_sound; assumption.
    - rewrite (eval_op_cmp bvne w x y CNe eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite !wrap_id in Heval by assumption.
      destruct (x =? y) eqn:Hxy; inversion Heval; subst rw z;
        cbn [backward_two_values combine fst snd].
      + apply Z.eqb_eq in Hxy. subst y. apply pair_sound; apply meet_at_width; assumption.
      + apply pair_sound; assumption.
  Qed.

  (** Add, subtract and xor inverses retain their represented operands. *)
  Local Lemma backward_arithmetic_sound : forall o rw w a b x y z,
    (o = bvadd \/ o = bvsub \/ o = bvxor) -> is_word w x -> is_word w y ->
    W.pgamma w a x -> W.pgamma w b y ->
    eval_op o [(w, x); (w, y)] = Some (rw, z) ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine [w; w] (backward_two_values o rw (FVal z) [(w, a); (w, b)]))
      [(w, x); (w, y)].
  Proof.
    intros o rw w a b x y z Ho Hx Hy Ha Hb Heval. destruct Ho as [-> | [-> | ->]].
    - rewrite (eval_op_fun2 bvadd w x y BAdd eq_refl) in Heval.
      inversion Heval; subst rw z.
      cbn [backward_two_values inverse_pair combine fst snd eval_binary_tag].
      apply pair_sound; apply W.pgamma_meet; try assumption.
      + apply (inverse_sound w _ b x y Hb). symmetry. now apply const_add_inverse.
      + apply (inverse_sound w _ a y x Ha). rewrite wadd_comm.
        symmetry. now apply const_add_inverse.
    - rewrite (eval_op_fun2 bvsub w x y BSub eq_refl) in Heval.
      inversion Heval; subst rw z.
      cbn [backward_two_values inverse_pair combine fst snd eval_binary_tag].
      apply pair_sound; apply W.pgamma_meet; try assumption.
      + apply (inverse_sound w _ b x y Hb). symmetry. now apply const_sub_inverse_left.
      + apply (inverse_sound w _ a y x Ha). symmetry. now apply const_sub_inverse_right.
    - rewrite (eval_op_fun2 bvxor w x y BXor eq_refl) in Heval.
      inversion Heval; subst rw z.
      cbn [backward_two_values inverse_pair combine fst snd eval_binary_tag].
      apply pair_sound; apply W.pgamma_meet; try assumption.
      + apply (inverse_sound w _ b x y Hb). symmetry. now apply const_xor_inverse.
      + apply (inverse_sound w _ a y x Ha). rewrite (wxor_comm w x y).
        symmetry. now apply const_xor_inverse.
  Qed.

  (** Binary inverse entries retain both represented operands. *)
  Local Lemma backward_two_values_sound : forall o rw q xs cs z,
    (o = bveq \/ o = bvne \/ o = bvadd \/ o = bvsub \/ o = bvxor) ->
    length xs = 2%nat ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) (backward_two_values o rw q xs)) cs.
  Proof.
    intros o rw q xs cs z Ho Hlen Hxs Heval Hq.
    destruct xs as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate.
    inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
    inversion Htail as [|? [vy y] ? ? Hhead' Hnil]; subst. inversion Hnil; subst.
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wx vy.
    change (eval_op o [(w, x); (v, y)] = Some (rw, z)) in Heval.
    assert (Hw : w = v).
    { destruct Ho as [-> | [-> | [-> | [-> | ->]]]];
        match type of Heval with
        | eval_op ?op _ = _ =>
          first [eapply (eval_op_fun2_width op _ w v x y (rw, z));
              [reflexivity|exact Heval] |
            eapply (eval_op_cmp_width op _ w v x y (rw, z));
              [reflexivity|exact Heval]]
        end. }
    subst v. apply W.pgamma_const_def in Hq. destruct q as [|r|]; [contradiction| |].
    - cbn in Hq. subst r.
      assert (Hcases : (o = bveq \/ o = bvne) \/
        (o = bvadd \/ o = bvsub \/ o = bvxor)) by tauto.
      destruct Hcases as [Hcomparison|Harithmetic].
      + eapply backward_comparison_sound; eassumption.
      + eapply backward_arithmetic_sound; eassumption.
    - cbn [backward_two_values map combine fst snd].
      constructor; [exact Ha|]. constructor; [exact Hb|constructor].
  Qed.

  (** The checked unary wrapper retains every represented operand. *)
  Lemma backward_one_sound_aux : forall o rw q xs ys cs z,
    backward_one o rw q xs = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) ys) cs.
  Proof.
    intros o rw q xs ys cs z Hentry Hxs Heval Hq.
    pose proof (proj1 (L.eval_op_is_word o cs rw z Heval)) as Hz.
    unfold backward_one in Hentry.
    rewrite (normalise_id rw q z Hz Hq),
      (normalise_operands_id xs cs Hxs) in Hentry.
    destruct o; destruct xs as [|a [|b rest]]; try discriminate;
      injection Hentry as <-.
    all: match type of Heval with
      | L.eval_op ?op _ = _ =>
        eapply (backward_one_values_sound op rw q [a] cs z)
      end; [tauto|reflexivity|exact Hxs|exact Heval|exact Hq].
  Qed.

  (** The checked binary wrapper retains every represented operand. *)
  Lemma backward_two_sound_aux : forall o rw q xs ys cs z,
    backward_two o rw q xs = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) ys) cs.
  Proof.
    intros o rw q xs ys cs z Hentry Hxs Heval Hq.
    pose proof (proj1 (L.eval_op_is_word o cs rw z Heval)) as Hz.
    unfold backward_two in Hentry.
    rewrite (normalise_id rw q z Hz Hq),
      (normalise_operands_id xs cs Hxs) in Hentry.
    destruct o; destruct xs as [|a [|b [|c rest]]]; try discriminate;
      injection Hentry as <-.
    all: match type of Heval with
      | L.eval_op ?op _ = _ =>
        eapply (backward_two_values_sound op rw q [a; b] cs z)
      end; [tauto|reflexivity|exact Hxs|exact Heval|exact Hq].
  Qed.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wps cs z r Hentry Hxs Heval. unfold wfwd in Hentry.
    destruct o; destruct wps as [|a [|b [|c rest]]]; try discriminate.
    all: match type of Hentry with
      | context [shortcut ?op ?a ?b] =>
        destruct (shortcut op a b) as [k|] eqn:Hshortcut
      end; injection Hentry as <-; apply W.pgamma_const_def; try exact I.
    all: eapply shortcut_sound_aux; eassumption.
  Qed.
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof.
    intros o rw q wps ys cs z Hentry Hxs Heval Hq. unfold wbwd in Hentry.
    destruct o; destruct wps as [|a [|b [|c rest]]]; try discriminate.
    all: first [eapply backward_one_sound_aux; eassumption |
      eapply backward_two_sound_aux; eassumption].
  Qed.
End ConstWordTable.

Module ConstWordTableT (L : WORD_LANGUAGE_T) (W : CONST_WORD_PAYLOAD_T L)
    <: CONST_WORD_TABLE_ALL L W.
  Include ConstWordTable L W.
  TimeFun wrap_fast.
  TimeFun normalise.
  TimeFun normalise_operands.
  TimeFun const_is.
  TimeFun shortcut.
  TimeFun inverse.
  TimeFun inverse_pair.
  TimeFun backward_one_values.
  TimeFun backward_two_values.
  TimeFun backward_one.
  TimeFun backward_two.
  TimeFun wfwd.
  TimeFun wbwd.

  (** Normalizing one payload reads its raw representation linearly. *)
  Local Lemma normalise_time w a : (T_normalise w a <= 64 * N.of_nat (W.psize w a))%N.
  Proof.
    rewrite W.psize_const_def. destruct a as [|z|]; time_unfold T_normalise;
      time_cbn; rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (ConstWordFast.wrap_fast_time w z) as Htime.
    time_unfold T_wrap_fast. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** A normalized flat payload stores at most one word of raw bits. *)
  Local Lemma normalise_size w a :
    (W.psize w (normalise w a) <= 2 * Pos.to_nat w + 1)%nat.
  Proof.
    rewrite W.psize_const_def. destruct a as [|z|]; cbn [normalise]; try lia.
    unfold wrap_fast. rewrite ConstWordFast.wrap_fast_agrees.
    pose proof (WordTime.word_wrap_size_bound w z). lia.
  Qed.
  (** Testing a normalized constant reads only its bounded word bits. *)
  Local Lemma normalise_const_is_time w a z :
    (T_const_is (normalise w a) z <= 2 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    destruct a as [|x|]; cbn [normalise]; time_unfold T_const_is; time_cbn;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (Z.T_eqb_le (wrap_fast w x) z) as Hcompare.
    assert (Hsize : (N.of_nat (Z.size_nat (wrap_fast w x)) <= N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. unfold wrap_fast. rewrite ConstWordFast.wrap_fast_agrees.
      apply WordTime.word_wrap_size_bound. }
    nia.
  Qed.
  (** Constructing the all-ones value charges the numeric width linearly. *)
  Local Lemma ones_time w :
    (T_modulus w + Z.T_sub (modulus w) 1 <= 32 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    pose proof (WordTime.word_modulus_time_bound w) as Hmod.
    pose proof (Z.T_sub_le (modulus w) 1) as Hsub.
    pose proof (time_of_nat_le _ _ (WordTime.word_modulus_size_bound w)) as Hsize.
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** A shortcut reads two raw payloads and performs bounded width work. *)
  Local Lemma shortcut_time o a b :
    (T_shortcut o a b <= 256 * N.of_nat
      (W.psize (fst a) (snd a) + W.psize (fst b) (snd b) +
        Pos.to_nat (fst a) + Pos.to_nat (fst b) + 1))%N.
  Proof.
    destruct a as [w a], b as [v b].
    pose proof (normalise_time w a) as Ha.
    pose proof (normalise_time v b) as Hb.
    pose proof (normalise_const_is_time w a 0) as Ha0.
    pose proof (normalise_const_is_time v b 0) as Hb0.
    pose proof (normalise_const_is_time w a (modulus w - 1)) as Ha1.
    pose proof (normalise_const_is_time v b (modulus w - 1)) as Hb1.
    pose proof (ones_time w) as Hones.
    time_unfold T_shortcut. unfold Datatypes.T_fst, Datatypes.T_snd, Datatypes.T_orb.
    destruct o; time_cbn; rewrite ?Nat2N.inj_add in *; time_cbn_all;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end; nia.
  Qed.
  (** The linear shortcut charge fits its declared quadratic width budget. *)
  Local Lemma shortcut_quadratic_time o a b :
    (T_shortcut o a b <= 512 * N.of_nat
      (((Pos.to_nat (fst a) + Pos.to_nat (fst b) + 1) ^ 2 +
        W.psize (fst a) (snd a) + W.psize (fst b) (snd b))%nat))%N.
  Proof.
    eapply N.le_trans; [apply shortcut_time|].
    apply N.mul_le_mono; [lia|]. apply time_of_nat_le. cbn [Nat.pow]. nia.
  Qed.
  (** A shortcut returns zero or an all-ones value at the first operand width. *)
  Local Lemma shortcut_result_size o a b z : shortcut o a b = Some z ->
    (Z.size_nat z <= Pos.to_nat (fst a))%nat.
  Proof.
    destruct a as [w a], b as [v b]. unfold shortcut. cbn [fst snd].
    destruct o; repeat match goal with
      |- context [if ?test then _ else _] => destruct test
      end; intros H; try discriminate; injection H as <-; cbn [fst Z.size_nat]; try lia.
    apply WordTime.word_size_bound. unfold is_word.
    pose proof (modulus_pos w). lia.
  Qed.
  (** Forward dispatch adds one tick to its possible binary shortcut. *)
  Local Lemma wfwd_clock_shape o rw xs :
    (T_wfwd o rw xs <= 1 + match xs with [a; b] => T_shortcut o a b | _ => 0 end)%N.
  Proof.
    destruct o; destruct xs as [|a [|b [|c rest]]];
      time_unfold T_wfwd; time_cbn; lia.
  Qed.
  (** Forward table evaluation fits a linear width and raw-payload budget. *)
  Local Lemma wfwd_linear_time o rw xs :
    (T_wfwd o rw xs <= 512 * N.of_nat
      (Pos.to_nat rw + fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) +
        fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs) + 1))%N.
  Proof.
    eapply N.le_trans; [apply wfwd_clock_shape|].
    destruct xs as [|a [|b [|c rest]]]; time_cbn;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (shortcut_time o a b).
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The declared quadratic table work contains the corresponding linear charge. *)
  Local Lemma table_linear_work rw xs :
    (N.of_nat
      (Pos.to_nat rw + fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) +
        fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs) + 1) <=
      N.of_nat
      ((Pos.to_nat rw + fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) + 1)^2 +
        fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs)))%N.
  Proof.
    apply time_of_nat_le. cbn [Nat.pow]. nia.
  Qed.
  (** Forward dispatch returns top or a successful binary shortcut value. *)
  Local Lemma wfwd_result_shape o rw xs r : wfwd o rw xs = Some r ->
    r = FTop \/ exists a b z, xs = [a; b] /\ shortcut o a b = Some z /\ r = FVal z.
  Proof.
    unfold wfwd. destruct o; destruct xs as [|a [|b [|c rest]]];
      try discriminate; destruct (shortcut _ a b) as [z|] eqn:Hshortcut;
      intros H; injection H as <-.
    all: first [solve [right; eauto 8]|now left].
  Qed.
  (** A forward result fits within the result width and operand budget. *)
  Local Lemma wfwd_linear_size o rw xs r : wfwd o rw xs = Some r ->
    (W.psize rw r <= Pos.to_nat rw +
      fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) +
      fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs) + 1)%nat.
  Proof.
    intros Hentry. apply wfwd_result_shape in Hentry.
    destruct Hentry as [->|[a [b [z [-> [Hshortcut ->]]]]]]; rewrite W.psize_const_def.
    - cbn. lia.
    - pose proof (shortcut_result_size o a b z Hshortcut).
      cbn [map fold_right]. lia.
  Qed.

  (** A flat payload stores raw bits only in its singleton case. *)
  Local Definition payload_bits (a : W.p) : nat :=
    match a with FVal z => Z.size_nat z | _ => 0 end.
  (** The operand width budget sums the numeric tags. *)
  Local Definition operand_widths (xs : list (positive * W.p)) : nat :=
    fold_right Nat.add 0 (map (fun wp => Pos.to_nat (fst wp)) xs).
  (** The raw payload budget sums the declared sizes. *)
  Local Definition operand_payloads (xs : list (positive * W.p)) : nat :=
    fold_right Nat.add 0 (map (fun wp => W.psize (fst wp) (snd wp)) xs).
  (** The declared payload size separates its width and raw integer bits. *)
  Local Lemma psize_bits w a : W.psize w a = Pos.to_nat w + payload_bits a + 1.
  Proof.
    apply W.psize_const_def.
  Qed.
  (** Normalization bounds the stored bits by the operand width. *)
  Local Lemma normalise_bits w a : (payload_bits (normalise w a) <= Pos.to_nat w)%nat.
  Proof.
    destruct a as [|z|]; cbn [normalise payload_bits]; try lia.
    unfold wrap_fast. rewrite ConstWordFast.wrap_fast_agrees.
    apply WordTime.word_wrap_size_bound.
  Qed.
  (** Normalization preserves the sum of operand widths. *)
  Local Lemma normalise_widths xs : operand_widths (normalise_operands xs) = operand_widths xs.
  Proof.
    unfold operand_widths, normalise_operands. rewrite map_map.
    reflexivity.
  Qed.
  (** Normalization preserves the operand-list length. *)
  Local Lemma normalise_length xs : length (normalise_operands xs) = length xs.
  Proof.
    unfold normalise_operands. apply length_map.
  Qed.
  (** Each list cell adds normalization and five traversal ticks. *)
  Local Lemma normalise_list_succ w a xs :
    T_normalise_operands ((w, a) :: xs) =
      (T_normalise_operands xs + T_normalise w a + 5)%N.
  Proof.
    time_unfold T_normalise_operands. unfold ListDef.T_map.
    unfold Datatypes.T_fst, Datatypes.T_snd. time_cbn. nia.
  Qed.
  (** List normalization reads the raw payload budget linearly. *)
  Local Lemma normalise_list_time xs :
    (T_normalise_operands xs <= 128 * N.of_nat (operand_payloads xs + 1))%N.
  Proof.
    induction xs as [|[w a] xs IH].
    - time_unfold T_normalise_operands. unfold ListDef.T_map, operand_payloads.
      time_cbn. lia.
    - rewrite normalise_list_succ.
      pose proof (normalise_time w a) as Hhead.
      assert (Hpositive : (1 <= W.psize w a)%nat) by (rewrite psize_bits; lia).
      change (T_normalise_operands xs + T_normalise w a + 5 <=
        128 * N.of_nat (W.psize w a + operand_payloads xs + 1))%N.
      rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** Projecting operand payloads takes two ticks per list cell. *)
  Local Lemma points_map_time xs :
    (ListDef.T_map snd (fun wp : positive * W.p => Datatypes.T_snd wp) xs <=
      2 * N.of_nat (length xs) + 1)%N.
  Proof.
    apply (ListDef.T_map_le snd (fun wp : positive * W.p => Datatypes.T_snd wp) 1 xs).
    intro wp. apply Datatypes.T_snd_le.
  Qed.
  (** Positive operand widths pay for the number of list cells. *)
  Local Lemma width_count xs : (length xs <= operand_widths xs)%nat.
  Proof.
    induction xs as [|[w a] xs IH]; cbn [length operand_widths map fold_right fst snd].
    - lia.
    - pose proof (Pos2Nat.is_pos w). unfold operand_widths in IH. lia.
  Qed.
  (** Two width-bounded payloads fit a common squared work budget. *)
  Local Lemma meet_input_budget b rw a c :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat ->
    (payload_bits a <= b)%nat -> (payload_bits c <= b)%nat ->
    (N.of_nat (W.psize rw a + W.psize rw c + 1) <=
      7 * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Ha Hc.
    assert (Hnat : (W.psize rw a + W.psize rw c + 1 <= 7 * (b ^ 2))%nat).
    { rewrite !psize_bits. cbn [Nat.pow]. nia. }
    pose proof (time_of_nat_le _ _ Hnat) as Hcast.
    rewrite Nat2N.inj_mul in Hcast. exact Hcast.
  Qed.
  (** A payload meet scales the common work budget by its payload constant. *)
  Local Lemma meet_time_budget b rw a c :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat ->
    (payload_bits a <= b)%nat -> (payload_bits c <= b)%nat ->
    (W.T_pmeet rw a c <= (7 * W.c_payload) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Ha Hc. pose proof (W.T_pmeet_le rw a c) as Htime.
    pose proof (meet_input_budget b rw a c Hb Hrw Ha Hc) as Hsize.
    assert (Hscaled : (W.c_payload * N.of_nat (W.psize rw a + W.psize rw c + 1) <=
      W.c_payload * (7 * N.of_nat (b ^ 2)))%N).
    { apply N.mul_le_mono_l. exact Hsize. }
    nia.
  Qed.
  (** A meet result remains bounded when read at another bounded operand width. *)
  Local Lemma meet_size_budget b rw target a c :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat -> (Pos.to_nat target <= b)%nat ->
    (payload_bits a <= b)%nat -> (payload_bits c <= b)%nat ->
    (N.of_nat (W.psize target (W.pmeet rw a c)) <=
      (8 * (W.c_payload + 1)) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Htarget Ha Hc. pose proof (W.pmeet_size rw a c) as Hmeet.
    pose proof (meet_input_budget b rw a c Hb Hrw Ha Hc) as Hsize.
    assert (Hscaled : (W.c_payload * N.of_nat (W.psize rw a + W.psize rw c + 1) <=
      W.c_payload * (7 * N.of_nat (b ^ 2)))%N).
    { apply N.mul_le_mono_l. exact Hsize. }
    pose proof (WordTime.time_square_floor (Pos.to_nat target) b Htarget Hb) as Hwidth.
    assert (Hresult : (N.of_nat (W.psize rw (W.pmeet rw a c)) <=
      7 * W.c_payload * N.of_nat (b ^ 2))%N) by nia.
    clear Hmeet Hscaled Hsize.
    rewrite !psize_bits, ?Nat2N.inj_add in Hresult |- *.
    nia.
  Qed.

  (** Applying an inverse adds one tick to its bounded callback. *)
  Local Lemma inverse_time_budget b f tf a k :
    (1 <= b)%nat -> (payload_bits a <= b)%nat ->
    (forall z, (Z.size_nat z <= b)%nat -> (tf z <= k * N.of_nat (b ^ 2))%N) ->
    (T_inverse f tf a <= (k + 1) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Ha Hf. pose proof (WordTime.time_square_floor 1 b Hb Hb) as Hone.
    set (budget := N.of_nat (b ^ 2)) in *. clearbody budget.
    destruct a as [|z|]; cbn [payload_bits] in Ha;
      time_unfold T_inverse; time_cbn; try nia.
    pose proof (Hf z Ha). nia.
  Qed.
  (** An inverse whose outputs have bounded raw bits preserves that bound. *)
  Local Lemma inverse_bits_budget b f a :
    (forall z, (Z.size_nat (f z) <= b)%nat) -> (payload_bits (inverse f a) <= b)%nat.
  Proof.
    intro Hf. destruct a as [|z|]; cbn [inverse payload_bits]; auto; lia.
  Qed.
  (** Unary inverse clocks fit a common quadratic bound on widths and raw bits. *)
  Local Lemma unary_cost_budget b rw r o :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat -> (Z.size_nat r <= b)%nat ->
    ((match o with bvnot => T_wnot rw r | _ => T_wneg rw r end) <=
      2048 * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Hr.
    assert (Hnot : (T_wnot rw r <= 1152 * N.of_nat (b ^ 2))%N).
    { eapply WordTime.time_square_scale with (c := 128%N) (k := 3%nat);
        [apply WordTime.word_not_time_bound|lia]. }
    assert (Hneg : (T_wneg rw r <= 1152 * N.of_nat (b ^ 2))%N).
    { eapply WordTime.time_square_scale with (c := 128%N) (k := 3%nat);
        [apply WordTime.word_neg_time_bound|lia]. }
    set (budget := N.of_nat (b ^ 2)) in *. clearbody budget.
    destruct o; nia.
  Qed.
  (** Unary inverse results stay within the bounded result width. *)
  Local Lemma unary_bits_budget b rw r o : (Pos.to_nat rw <= b)%nat ->
    (payload_bits (FVal (match o with bvnot => wnot rw r | _ => wneg rw r end)) <= b)%nat.
  Proof.
    intro Hrw.
    pose proof (WordTime.word_size_bound rw (wnot rw r) (wnot_is_word rw r)) as Hnot.
    assert (Hneg : (Z.size_nat (wneg rw r) <= Pos.to_nat rw)%nat).
    { apply WordTime.word_size_bound, wrap_is_word. }
    destruct o; cbn [payload_bits]; lia.
  Qed.
  (** Add, subtract and xor inverses fit a shared quadratic input budget. *)
  Local Lemma binary_cost_budget b w x y :
    (1 <= b)%nat -> (Pos.to_nat w <= b)%nat ->
    (Z.size_nat x <= b)%nat -> (Z.size_nat y <= b)%nat ->
    (T_wadd w x y <= 8192 * N.of_nat (b ^ 2))%N /\
    (T_wsub w x y <= 8192 * N.of_nat (b ^ 2))%N /\
    (T_wxor w x y <= 8192 * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hw Hx Hy. split.
    - eapply WordTime.time_square_scale with (c := 512%N) (k := 4%nat);
        [apply WordTime.word_add_time_bound|lia].
    - split.
      + eapply WordTime.time_square_scale with (c := 512%N) (k := 4%nat);
          [apply WordTime.word_sub_time_bound|lia].
      + eapply N.le_trans with (m := (4096 * N.of_nat (b ^ 2))%N).
        * eapply WordTime.time_square_scale with (c := 256%N) (k := 4%nat);
            [apply WordTime.word_xor_time_bound|lia].
        * apply N.mul_le_mono_r. lia.
  Qed.
  (** Two inverse callbacks and their payload meets fit one common budget. *)
  Local Lemma inverse_pair_time_budget b rw f tf g tg a c :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat ->
    (payload_bits a <= b)%nat -> (payload_bits c <= b)%nat ->
    (forall z, (Z.size_nat z <= b)%nat ->
      (tf z <= 8193 * N.of_nat (b ^ 2))%N) ->
    (forall z, (Z.size_nat z <= b)%nat ->
      (tg z <= 8193 * N.of_nat (b ^ 2))%N) ->
    (forall z, (Z.size_nat (f z) <= b)%nat) ->
    (forall z, (Z.size_nat (g z) <= b)%nat) ->
    (T_inverse_pair rw f tf g tg a c <=
      (32768 * (W.c_payload + 1)) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Ha Hc Htf Htg Hf Hg.
    pose proof (inverse_time_budget b f tf c 8193 Hb Hc Htf) as Hif.
    pose proof (inverse_time_budget b g tg a 8193 Hb Ha Htg) as Hig.
    pose proof (inverse_bits_budget b f c Hf) as Hfsize.
    pose proof (inverse_bits_budget b g a Hg) as Hgsize.
    pose proof (meet_time_budget b rw a (inverse f c) Hb Hrw Ha Hfsize) as Hmf.
    pose proof (meet_time_budget b rw c (inverse g a) Hb Hrw Hc Hgsize) as Hmg.
    pose proof (WordTime.time_square_floor 1 b Hb Hb) as Hone.
    time_unfold T_inverse_pair.
    set (budget := N.of_nat (b ^ 2)) in *. clearbody budget. nia.
  Qed.

  (** Unary inverse dispatch fits the normalized width budget. *)
  Local Lemma values_one_time_budget b o rw q xs :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat -> (payload_bits q <= b)%nat ->
    Forall (fun wp => (Pos.to_nat (fst wp) <= b)%nat /\
      (payload_bits (snd wp) <= b)%nat) xs -> (length xs <= b)%nat ->
    (T_backward_one_values o rw q xs <=
      (4096 * (W.c_payload + 1)) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Hq Hxs Hlen.
    pose proof (points_map_time xs) as Hmap.
    pose proof (time_of_nat_le _ _ Hlen) as Hcount.
    pose proof (WordTime.time_square_floor b b (Nat.le_refl b) Hb) as Hfloor.
    pose proof (WordTime.time_square_floor 1 b Hb Hb) as Hone.
    pose proof (unary_cost_budget b) as Hoperation.
    pose proof (unary_bits_budget b) as Hresult.
    pose proof (meet_time_budget b) as Hmeet.
    set (budget := N.of_nat (b ^ 2)) in *. clearbody budget.
    destruct xs as [|[w a] rest].
    - time_unfold T_backward_one_values. time_cbn. nia.
    - destruct rest as [|wp tail].
      + destruct (Forall_inv Hxs) as [Hw Ha]. cbn [fst snd] in Ha.
        destruct q as [|r|]; cbn [payload_bits] in Hq;
          time_unfold T_backward_one_values; time_cbn; try nia.
        pose proof (Hoperation rw r o Hb Hrw Hq) as Hop.
        pose proof (Hresult rw r o Hrw) as Hsize.
        pose proof (Hmeet rw a
          (FVal (match o with bvnot => wnot rw r | _ => wneg rw r end))
          Hb Hrw Ha Hsize) as Hcost.
        nia.
      + time_unfold T_backward_one_values. time_cbn. nia.
  Qed.
  (** Every normalized operand fits the total input width budget. *)
  Local Lemma normalise_operands_bound b xs : (operand_widths xs <= b)%nat ->
    Forall (fun wp => (Pos.to_nat (fst wp) <= b)%nat /\
      (payload_bits (snd wp) <= b)%nat) (normalise_operands xs).
  Proof.
    induction xs as [|[w a] xs IH]; intro Hsum;
      cbn [normalise_operands map fst snd]; constructor.
    - cbn [fst snd].
      change (Pos.to_nat w + operand_widths xs <= b)%nat in Hsum.
      split; [lia|]. eapply Nat.le_trans; [apply normalise_bits|lia].
    - apply IH. change (Pos.to_nat w + operand_widths xs <= b)%nat in Hsum. lia.
  Qed.

  (** Each supported binary inverse pair fits the common arithmetic budget. *)
  Local Lemma inverse_binary_time_budget b rw w r a c :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat -> (Pos.to_nat w <= b)%nat ->
    (Z.size_nat r <= b)%nat -> (payload_bits a <= b)%nat ->
    (payload_bits c <= b)%nat ->
    (T_inverse_pair rw (fun z => wsub w r z) (fun z => 1 + T_wsub w r z)%N
       (fun z => wsub w r z) (fun z => 1 + T_wsub w r z)%N a c <=
       32768 * (W.c_payload + 1) * N.of_nat (b ^ 2))%N /\
    (T_inverse_pair rw (fun z => wadd w r z) (fun z => 1 + T_wadd w r z)%N
       (fun z => wsub w z r) (fun z => 1 + T_wsub w z r)%N a c <=
       32768 * (W.c_payload + 1) * N.of_nat (b ^ 2))%N /\
    (T_inverse_pair rw (fun z => wxor w r z) (fun z => 1 + T_wxor w r z)%N
       (fun z => wxor w r z) (fun z => 1 + T_wxor w r z)%N a c <=
       32768 * (W.c_payload + 1) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Hw Hr Ha Hc.
    pose proof (binary_cost_budget b) as Hbinary.
    pose proof (inverse_pair_time_budget b rw) as Hpair.
    pose proof (WordTime.time_square_floor 1 b Hb Hb) as Hone.
    set (budget := N.of_nat (b ^ 2)) in *. clearbody budget.
    change (1 <= budget)%N in Hone.
    assert (Hadd : forall z, (Z.size_nat z <= b)%nat ->
      (1 + T_wadd w r z <= 8193 * budget)%N).
    { intros z Hz. destruct (Hbinary w r z Hb Hw Hr Hz) as [Hcost _]. nia. }
    assert (Hsub : forall z, (Z.size_nat z <= b)%nat ->
      (1 + T_wsub w r z <= 8193 * budget)%N).
    { intros z Hz. destruct (Hbinary w r z Hb Hw Hr Hz) as [_ [Hcost _]]. nia. }
    assert (Hreverse : forall z, (Z.size_nat z <= b)%nat ->
      (1 + T_wsub w z r <= 8193 * budget)%N).
    { intros z Hz. destruct (Hbinary w z r Hb Hw Hz Hr) as [_ [Hcost _]]. nia. }
    assert (Hxor : forall z, (Z.size_nat z <= b)%nat ->
      (1 + T_wxor w r z <= 8193 * budget)%N).
    { intros z Hz. destruct (Hbinary w r z Hb Hw Hr Hz) as [_ [_ Hcost]]. nia. }
    assert (Haddbits : forall z, (Z.size_nat (wadd w r z) <= b)%nat).
    { intro z. eapply Nat.le_trans; [apply WordTime.word_wrap_size_bound|exact Hw]. }
    assert (Hsubbits : forall z, (Z.size_nat (wsub w r z) <= b)%nat).
    { intro z. eapply Nat.le_trans; [apply WordTime.word_wrap_size_bound|exact Hw]. }
    assert (Hreversebits : forall z, (Z.size_nat (wsub w z r) <= b)%nat).
    { intro z. eapply Nat.le_trans; [apply WordTime.word_wrap_size_bound|exact Hw]. }
    assert (Hxorbits : forall z, (Z.size_nat (wxor w r z) <= b)%nat).
    { intro z. eapply Nat.le_trans; [apply WordTime.word_size_bound, wxor_is_word|exact Hw]. }
    split.
    - eapply Hpair; eassumption.
    - split; eapply Hpair; eassumption.
  Qed.

  (** Binary backward dispatch pays for both inverse calls and all fallback list traversals. *)
  Local Lemma values_two_time_budget b o rw q xs :
    (1 <= b)%nat -> (Pos.to_nat rw <= b)%nat -> (payload_bits q <= b)%nat ->
    Forall (fun wp => (Pos.to_nat (fst wp) <= b /\ payload_bits (snd wp) <= b)%nat) xs ->
    (length xs <= b)%nat ->
    (T_backward_two_values o rw q xs <=
      65536 * (W.c_payload + 1) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Hb Hrw Hq Hxs Hlength.
    pose proof (points_map_time xs) as Hmap.
    pose proof (WordTime.time_square_floor (length xs) b Hlength Hb) as Hlengthbudget.
    pose proof (WordTime.time_square_floor (payload_bits q) b Hq Hb) as Hqbudget.
    pose proof (WordTime.time_square_floor 1 b Hb Hb) as Hone.
    pose proof (meet_time_budget b) as Hmeet.
    pose proof (inverse_binary_time_budget b) as Hinverse.
    set (budget := N.of_nat (b ^ 2)) in *. clearbody budget.
    change (1 <= budget)%N in Hone.
    destruct xs as [|[wa a] [|[wb c] [|wp xs]]].
    - time_unfold T_backward_two_values. time_cbn. nia.
    - time_unfold T_backward_two_values. time_cbn. nia.
    - destruct q as [|r|].
      + time_unfold T_backward_two_values. time_cbn. nia.
      + cbn [payload_bits] in Hq, Hqbudget.
        pose proof (Forall_inv Hxs) as Ha.
        pose proof (Forall_inv (Forall_inv_tail Hxs)) as Hc.
        cbn [fst snd] in Ha, Hc. destruct Ha as [Hwa Ha], Hc as [Hwb Hc].
        pose proof (Hmeet rw a c Hb Hrw Ha Hc) as Hac.
        pose proof (Hmeet rw c a Hb Hrw Hc Ha) as Hca.
        destruct (Hinverse rw wa r a c Hb Hrw Hwa Hq Ha Hc) as [Hadd [Hsub Hxor]].
        pose proof (Z.T_eqb_le r 1) as Heq.
        pose proof (Z.T_eqb_le r 0) as Hne.
        destruct o; time_unfold T_backward_two_values; time_cbn.
        all: try match goal with
          | |- context [if ?guard then _ else _] => destruct guard
          end; nia.
      + time_unfold T_backward_two_values. time_cbn. nia.
    - time_unfold T_backward_two_values. time_cbn. nia.
  Qed.

  (** Normalized inverse calls share a quadratic budget in the sum of widths. *)
  Local Lemma inverse_words_time_bound o rw q xs :
    (T_backward_one_values o rw (normalise rw q) (normalise_operands xs) +
     T_backward_two_values o rw (normalise rw q) (normalise_operands xs) <=
      69632 * (W.c_payload + 1) *
        N.of_nat ((Pos.to_nat rw + operand_widths xs + 1)^2))%N.
  Proof.
    set (b := (Pos.to_nat rw + operand_widths xs + 1)%nat).
    assert (Hb : (1 <= b)%nat) by (unfold b; lia).
    assert (Hrw : (Pos.to_nat rw <= b)%nat) by (unfold b; lia).
    assert (Hq : (payload_bits (normalise rw q) <= b)%nat).
    { eapply Nat.le_trans; [apply normalise_bits|exact Hrw]. }
    assert (Hxs : Forall (fun wp => (Pos.to_nat (fst wp) <= b)%nat /\
      (payload_bits (snd wp) <= b)%nat) (normalise_operands xs)).
    { apply normalise_operands_bound. unfold b. lia. }
    assert (Hlength : (length (normalise_operands xs) <= b)%nat).
    { rewrite normalise_length. pose proof (width_count xs). unfold b. lia. }
    pose proof (values_one_time_budget b o rw (normalise rw q)
      (normalise_operands xs) Hb Hrw Hq Hxs Hlength) as Hone.
    pose proof (values_two_time_budget b o rw (normalise rw q)
      (normalise_operands xs) Hb Hrw Hq Hxs Hlength) as Htwo.
    fold b. set (budget := N.of_nat (b ^ 2)) in *. clearbody budget. nia.
  Qed.

  (** Unary dispatch charges normalization before its optional inverse call. *)
  Local Lemma wbwrap_one_clock o rw q xs :
    (T_backward_one o rw q xs <= 4 + T_normalise rw q + T_normalise_operands xs +
      T_backward_one_values o rw (normalise rw q) (normalise_operands xs))%N.
  Proof.
    time_unfold T_backward_one.
    destruct o; destruct (normalise_operands xs) as [|a [|b rest]];
      time_cbn; lia.
  Qed.

  (** Binary dispatch charges normalization before its optional inverse call. *)
  Local Lemma wbwrap_two_clock o rw q xs :
    (T_backward_two o rw q xs <= 4 + T_normalise rw q + T_normalise_operands xs +
      T_backward_two_values o rw (normalise rw q) (normalise_operands xs))%N.
  Proof.
    time_unfold T_backward_two.
    destruct o; destruct (normalise_operands xs) as [|a [|b [|c rest]]];
      time_cbn; lia.
  Qed.

  (** The positive width square absorbs fixed wrapper overhead. *)
  Local Lemma wbwrap_width_positive rw xs :
    (1 <= N.of_nat ((Pos.to_nat rw + operand_widths xs + 1)^2))%N.
  Proof.
    change (N.of_nat 1 <= N.of_nat ((Pos.to_nat rw + operand_widths xs + 1)^2))%N.
    apply time_of_nat_le. cbn [Nat.pow]. nia.
  Qed.

  (** The unused inverse coefficient covers both linear scans and wrapper overhead. *)
  Local Lemma wbwrap_budget_algebra c width request operands : (1 <= width)%N ->
    (69632 * (c + 1) * width + 128 * request + 256 * operands + 264 <=
      131072 * (c + 1) * (width + request + operands))%N.
  Proof.
    intros Hpositive.
    assert (Hwidth_coefficient : (69632 * (c + 1) + 264 <= 131072 * (c + 1))%N)
      by nia.
    assert (Hwidth : ((69632 * (c + 1) + 264) * width <=
      (131072 * (c + 1)) * width)%N).
    { now apply N.mul_le_mono_r. }
    assert (Hrequest : (128 * request <= (131072 * (c + 1)) * request)%N).
    { apply N.mul_le_mono_r. nia. }
    assert (Hoperands : (256 * operands <= (131072 * (c + 1)) * operands)%N).
    { apply N.mul_le_mono_r. nia. }
    assert (Hoverhead : (264 <= 264 * width)%N).
    { replace 264%N with (264 * 1)%N at 1 by reflexivity.
      now apply N.mul_le_mono_l. }
    rewrite N.mul_add_distr_r in Hwidth.
    replace (131072 * (c + 1) * (width + request + operands))%N with
      ((131072 * (c + 1)) * width + (131072 * (c + 1)) * request +
        (131072 * (c + 1)) * operands)%N by ring.
    lia.
  Qed.

  (** The two wrappers share the inverse budget and each read normalization once. *)
  Local Lemma wbwrap_combined o rw q xs :
    (T_backward_one_values o rw (normalise rw q) (normalise_operands xs) +
     T_backward_two_values o rw (normalise rw q) (normalise_operands xs) <=
      69632 * (W.c_payload + 1) *
        N.of_nat ((Pos.to_nat rw + operand_widths xs + 1)^2))%N ->
    (T_backward_one o rw q xs + T_backward_two o rw q xs <=
      131072 * (W.c_payload + 1) * N.of_nat
        ((Pos.to_nat rw + operand_widths xs + 1)^2 +
          W.psize rw q + operand_payloads xs))%N.
  Proof.
    intros Hinverse.
    pose proof (wbwrap_one_clock o rw q xs) as Hone.
    pose proof (wbwrap_two_clock o rw q xs) as Htwo.
    pose proof (normalise_time rw q) as Hrequest.
    pose proof (normalise_list_time xs) as Hoperands.
    pose proof (wbwrap_width_positive rw xs) as Hpositive.
    eapply N.le_trans with (m :=
      (69632 * (W.c_payload + 1) *
        N.of_nat ((Pos.to_nat rw + operand_widths xs + 1)^2) +
        128 * N.of_nat (W.psize rw q) +
        256 * N.of_nat (operand_payloads xs) + 264)%N).
    - rewrite !Nat2N.inj_add in Hoperands. time_cbn_all. lia.
    - rewrite !Nat2N.inj_add. now apply wbwrap_budget_algebra.
  Qed.

  (** Backward table dispatch invokes at most one wrapper and adds one tick. *)
  Local Lemma wbwrap_table_clock o rw q xs :
    (T_wbwd o rw q xs <= 1 + T_backward_one o rw q xs + T_backward_two o rw q xs)%N.
  Proof.
    time_unfold T_wbwd.
    destruct o; destruct xs as [|a [|b [|c rest]]]; time_cbn; lia.
  Qed.


  (** The larger table coefficient pays one additional dispatch tick. *)
  Local Lemma wbwrap_table_margin c budget : (1 <= budget)%N ->
    (1 + 131072 * (c + 1) * budget <= 524288 * (c + 1) * budget)%N.
  Proof.
    intros Hpositive.
    assert (Hcoefficient : (131072 * (c + 1) + 1 <= 524288 * (c + 1))%N) by nia.
    assert (Hscaled : ((131072 * (c + 1) + 1) * budget <=
      (524288 * (c + 1)) * budget)%N).
    { now apply N.mul_le_mono_r. }
    rewrite N.mul_add_distr_r in Hscaled. lia.
  Qed.

  (** Both public wrappers fit the coefficient reserved for backward transfer. *)
  Local Lemma backward_pair_time_bound o rw q xs :
    (T_backward_one o rw q xs + T_backward_two o rw q xs <=
      131072 * (W.c_payload + 1) * N.of_nat
        ((Pos.to_nat rw + operand_widths xs + 1)^2 +
          W.psize rw q + operand_payloads xs))%N.
  Proof.
    apply wbwrap_combined, inverse_words_time_bound.
  Qed.

  Definition c_word_table : N := (524288 * (W.c_payload + 1))%N.
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs. eapply N.le_trans; [apply wfwd_linear_time|].
    eapply N.le_trans.
    - apply N.mul_le_mono_l, table_linear_work.
    - apply N.mul_le_mono_r. unfold c_word_table. nia.
  Qed.
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs. pose proof (backward_pair_time_bound o rw q xs) as Hcombined.
    pose proof (wbwrap_table_clock o rw q xs) as Hclock.
    pose proof (wbwrap_width_positive rw xs) as Hpositive.
    change (1 <= N.of_nat ((Pos.to_nat rw + operand_widths xs + 1)^2))%N
      in Hpositive.
    assert (Hbudget : (1 <= N.of_nat
      ((Pos.to_nat rw + operand_widths xs + 1)^2 +
        W.psize rw q + operand_payloads xs))%N).
    { rewrite !Nat2N.inj_add. lia. }
    pose proof (wbwrap_table_margin W.c_payload _ Hbudget) as Hmargin.
    unfold c_word_table, operand_widths, operand_payloads in *. lia.
  Qed.
  Definition k_const_word : N := (131072 * (W.c_payload + 1))%N.
  (** Normalised inverse arithmetic reads bounded word payloads. *)
  Lemma T_backward_values_le : forall o rw q xs,
    (T_backward_one_values o rw (normalise rw q) (normalise_operands xs) +
     T_backward_two_values o rw (normalise rw q) (normalise_operands xs) <=
      k_const_word * N.of_nat
        (((Pos.to_nat rw +
          fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2)%nat))%N.
  Proof.
    intros o rw q xs. eapply N.le_trans; [apply inverse_words_time_bound|].
    apply N.mul_le_mono_r. unfold k_const_word. nia.
  Qed.

  (** Normalisation reads the width mask and raw literal once. *)
  Lemma T_wrap_fast_le : forall w z,
    (T_wrap_fast w z <= k_const_word *
      N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
  Proof.
    intros w z. pose proof (ConstWordFast.wrap_fast_time w z) as Htime.
    time_unfold T_wrap_fast. unfold k_const_word.
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Fast wrapping preserves the specified modular reduction. *)
  Lemma wrap_fast_def : forall w z, wrap_fast w z = L.wrap w z.
  Proof.
    apply ConstWordFast.wrap_fast_agrees.
  Qed.

  Lemma shortcut_sound : forall o a b z cs rw v,
    shortcut o a b = Some z ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) (a :: b :: nil) cs ->
    L.eval_op o cs = Some (rw, v) -> v = z.
  Proof.
    apply shortcut_sound_aux.
  Qed.
  Lemma backward_one_sound : forall o rw q xs ys cs z,
    backward_one o rw q xs = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) ys) cs.
  Proof.
    apply backward_one_sound_aux.
  Qed.
  Lemma backward_two_sound : forall o rw q xs ys cs z,
    backward_two o rw q xs = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) ys) cs.
  Proof.
    apply backward_two_sound_aux.
  Qed.
  Lemma T_shortcut_le : forall o a b, (T_shortcut o a b <=
    k_const_word * N.of_nat
      (((Pos.to_nat (fst a) + Pos.to_nat (fst b) + 1) ^ 2 +
        W.psize (fst a) (snd a) + W.psize (fst b) (snd b))%nat))%N.
  Proof.
    intros o a b. eapply N.le_trans; [apply shortcut_quadratic_time|].
    apply N.mul_le_mono_r. unfold k_const_word. nia.
  Qed.
  Lemma T_backward_one_le : forall o rw q xs,
    (T_backward_one o rw q xs <= k_const_word * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs. pose proof (backward_pair_time_bound o rw q xs) as Hcombined.
    unfold k_const_word, operand_widths, operand_payloads in *. lia.
  Qed.
  Lemma T_backward_two_le : forall o rw q xs,
    (T_backward_two o rw q xs <= k_const_word * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs. pose proof (backward_pair_time_bound o rw q xs) as Hcombined.
    unfold k_const_word, operand_widths, operand_payloads in *. lia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (W.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs r Hentry.
    eapply N.le_trans; [apply time_of_nat_le; eapply wfwd_linear_size; exact Hentry|].
    eapply N.le_trans; [apply table_linear_work|].
    unfold c_word_table. nia.
  Qed.
  (** Backward output sizes count the raw bits of flat singleton payloads. *)
  Local Definition wbsize_raw (a : W.p) : nat :=
    match a with FVal z => Z.size_nat z | _ => 0 end.
  (** Backward size work sums the original operand widths. *)
  Local Definition wbsize_widths (xs : list (positive * W.p)) : nat :=
    fold_right Nat.add 0 (map (fun wp => Pos.to_nat (fst wp)) xs).
  (** The returned list is measured at its original operand widths. *)
  Local Definition wbsize_result (xs : list (positive * W.p)) (ys : list W.p) : nat :=
    length ys + fold_right Nat.add 0
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys)).

  (** Payload size separates the target width from stored raw bits. *)
  Local Lemma wbsize_raw_equation w a :
    W.psize w a = Pos.to_nat w + wbsize_raw a + 1.
  Proof.
    apply W.psize_const_def.
  Qed.

  (** Normalization bounds raw bits by the original operand width. *)
  Local Lemma wbsize_normalise w a : (wbsize_raw (normalise w a) <= Pos.to_nat w)%nat.
  Proof.
    destruct a as [|z|]; cbn [normalise wbsize_raw]; try lia.
    unfold wrap_fast. rewrite ConstWordFast.wrap_fast_agrees.
    apply WordTime.word_wrap_size_bound.
  Qed.

  (** An inverse with bounded outputs produces a bounded flat payload. *)
  Local Lemma wbsize_inverse budget f a :
    (forall z, (Z.size_nat (f z) <= budget)%nat) ->
    (wbsize_raw (inverse f a) <= budget)%nat.
  Proof.
    intros Hf. destruct a; cbn [inverse wbsize_raw]; auto; lia.
  Qed.

  (** A bounded unchanged payload fits the common quadratic size budget. *)
  Local Lemma wbsize_plain budget w a :
    (1 <= budget)%nat -> (Pos.to_nat w <= budget)%nat ->
    (wbsize_raw a <= budget)%nat ->
    (N.of_nat (W.psize w a) <=
      (8 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    intros Hb Hw Ha.
    assert (Hsmall_nat : (W.psize w a <= 3 * budget ^ 2)%nat).
    { rewrite wbsize_raw_equation. cbn [Nat.pow]. nia. }
    pose proof (time_of_nat_le _ _ Hsmall_nat) as Hsmall.
    rewrite Nat2N.inj_mul in Hsmall. time_cbn_all.
    nia.
  Qed.

  (** A meet result fits the budget at any bounded original operand width. *)
  Local Lemma wbsize_meet budget rw target a b :
    (1 <= budget)%nat -> (Pos.to_nat rw <= budget)%nat ->
    (Pos.to_nat target <= budget)%nat ->
    (wbsize_raw a <= budget)%nat -> (wbsize_raw b <= budget)%nat ->
    (N.of_nat (W.psize target (W.pmeet rw a b)) <=
      (8 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    apply meet_size_budget.
  Qed.

  (** One returned payload and its list cell fit the backward size budget. *)
  Local Lemma wbsize_single budget w original a :
    (1 <= budget)%nat ->
    (N.of_nat (W.psize w a) <=
      (8 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N ->
    (N.of_nat (wbsize_result [(w, original)] [a]) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    intros Hb Ha.
    pose proof (WordTime.time_square_floor 1 budget Hb Hb) as Hone.
    cbn [wbsize_result map fst snd combine fold_right length].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ; time_cbn_all; nia.
  Qed.

  (** Two returned payloads and their list cells fit the backward size budget. *)
  Local Lemma wbsize_pair budget w v original_a original_b a b :
    (1 <= budget)%nat ->
    (N.of_nat (W.psize w a) <=
      (8 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N ->
    (N.of_nat (W.psize v b) <=
      (8 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N ->
    (N.of_nat (wbsize_result [(w, original_a); (v, original_b)] [a; b]) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    intros Hb Ha Hbb.
    pose proof (WordTime.time_square_floor 1 budget Hb Hb) as Hone.
    cbn [wbsize_result map fst snd combine fold_right length].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ; time_cbn_all; nia.
  Qed.

  (** Every unary inverse result has bounded size at the operand width. *)
  Local Lemma wbsize_one_values budget o rw w original a q :
    (1 <= budget)%nat -> (Pos.to_nat rw <= budget)%nat ->
    (Pos.to_nat w <= budget)%nat -> (wbsize_raw a <= budget)%nat ->
    (N.of_nat (wbsize_result [(w, original)] (backward_one_values o rw q [(w, a)])) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    intros Hb Hrw Hw Ha.
    destruct q as [|r|]; cbn [backward_one_values map snd].
    - apply wbsize_single; [exact Hb|]. now apply wbsize_plain.
    - apply wbsize_single; [exact Hb|]. apply wbsize_meet; try assumption.
      cbn [wbsize_raw]. eapply Nat.le_trans; [|exact Hrw].
      apply WordTime.word_size_bound. destruct o; first [apply wnot_is_word|apply wrap_is_word].
    - apply wbsize_single; [exact Hb|]. now apply wbsize_plain.
  Qed.

  (** Binary inverse meets retain bounded sizes at both original widths. *)
  Local Lemma wbsize_inverse_pair budget rw w v original_a original_b a b f g :
    (1 <= budget)%nat -> (Pos.to_nat rw <= budget)%nat ->
    (Pos.to_nat w <= budget)%nat -> (Pos.to_nat v <= budget)%nat ->
    (wbsize_raw a <= budget)%nat -> (wbsize_raw b <= budget)%nat ->
    (forall z, (Z.size_nat (f z) <= budget)%nat) ->
    (forall z, (Z.size_nat (g z) <= budget)%nat) ->
    (N.of_nat (wbsize_result [(w, original_a); (v, original_b)]
      (inverse_pair rw f g a b)) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    intros Hb Hrw Hw Hv Ha Hbb Hf Hg. unfold inverse_pair.
    apply wbsize_pair; [exact Hb| |]; apply wbsize_meet; try assumption;
      now apply wbsize_inverse.
  Qed.

  (** Each binary inverse family fits the common width-only result budget. *)
  Local Lemma wbsize_two_values budget o rw w v original_a original_b a b q :
    (1 <= budget)%nat -> (Pos.to_nat rw <= budget)%nat ->
    (Pos.to_nat w <= budget)%nat -> (Pos.to_nat v <= budget)%nat ->
    (wbsize_raw a <= budget)%nat -> (wbsize_raw b <= budget)%nat ->
    (N.of_nat (wbsize_result [(w, original_a); (v, original_b)]
      (backward_two_values o rw q [(w, a); (v, b)])) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N.
  Proof.
    intros Hb Hrw Hw Hv Ha Hbb.
    assert (Hplain : (N.of_nat (wbsize_result [(w, original_a); (v, original_b)] [a; b]) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N).
    { apply wbsize_pair; [exact Hb| |]; now apply wbsize_plain. }
    assert (Hmeet : (N.of_nat (wbsize_result [(w, original_a); (v, original_b)]
      [W.pmeet rw a b; W.pmeet rw b a]) <=
      (32 * (W.c_payload + 1)) * N.of_nat (budget ^ 2))%N).
    { apply wbsize_pair; [exact Hb| |]; now apply wbsize_meet. }
    destruct q as [|r|]; cbn [backward_two_values map snd]; try exact Hplain.
    destruct o; cbn [backward_two_values]; try exact Hplain;
      try (destruct (Z.eqb r 1); assumption);
      try (destruct (Z.eqb r 0); assumption).
    all: apply wbsize_inverse_pair; try assumption.
    all: intros z; eapply Nat.le_trans; [|exact Hw].
    all: apply WordTime.word_size_bound; first [apply wxor_is_word|apply wrap_is_word].
  Qed.

  (** The public backward-table budget contains the stronger width-only bound. *)
  Local Lemma wbsize_final_budget rw q xs :
    ((32 * (W.c_payload + 1)) *
       N.of_nat ((Pos.to_nat rw + wbsize_widths xs + 1)^2) <=
     c_word_table * N.of_nat
      ((Pos.to_nat rw + wbsize_widths xs + 1)^2 + W.psize rw q +
        fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs)))%N.
  Proof.
    apply N.mul_le_mono.
    - unfold c_word_table. nia.
    - apply time_of_nat_le. lia.
  Qed.

  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0 (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs ys Hentry.
    change (N.of_nat (wbsize_result xs ys) <=
      c_word_table * N.of_nat
        ((Pos.to_nat rw + wbsize_widths xs + 1)^2 + W.psize rw q +
          fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs)))%N.
    eapply N.le_trans; [|apply wbsize_final_budget].
    destruct xs as [|[w a] [|[v b] [|extra rest]]]; destruct o;
      cbn [wbwd] in Hentry; try discriminate;
      cbn [backward_one backward_two normalise_operands map fst snd] in Hentry;
      injection Hentry as <-.
    all: first
      [apply (wbsize_one_values _ bvnot rw w a (normalise w a) (normalise rw q))
      |apply (wbsize_one_values _ bvneg rw w a (normalise w a) (normalise rw q))
      |apply (wbsize_two_values _ bvadd rw w v a b
        (normalise w a) (normalise v b) (normalise rw q))
      |apply (wbsize_two_values _ bvsub rw w v a b
        (normalise w a) (normalise v b) (normalise rw q))
      |apply (wbsize_two_values _ bvxor rw w v a b
        (normalise w a) (normalise v b) (normalise rw q))
      |apply (wbsize_two_values _ bveq rw w v a b
        (normalise w a) (normalise v b) (normalise rw q))
      |apply (wbsize_two_values _ bvne rw w v a b
        (normalise w a) (normalise v b) (normalise rw q))].
    all: cbn [wbsize_widths map fst snd fold_right]; try lia.
    all: eapply Nat.le_trans; [apply wbsize_normalise|lia].
  Qed.
End ConstWordTableT.
