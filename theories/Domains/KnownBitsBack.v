(** * Known-bit backward operations

    Backward transfers refine operand masks from a known result mask.
    For example, a known sum can refine the first operand when the second is fixed.
    Builds on: KnownBitsSig and the bit-vector operations. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Op Fun Testbit Arith.
From Galois.Domains Require Import WordSig KnownBitsSig KnownBits KnownBitsOps BitsLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Definition tnum_project (sw rw : width) (g : Z -> Z) (q : tnum) : tnum :=
  Tnum (tnum_wrap sw (g (tnum_wrap rw (zeros q)))) (tnum_wrap sw (g (tnum_wrap rw (ones q)))).
TimeFun tnum_project.

Definition tnum_inverse_shift (o : op) : op :=
  match o with
  | bvshl => bvlshr
  | bvlshr | bvashr => bvshl
  | bvrotl => bvrotr
  | bvrotr => bvrotl
  | _ => o
  end.
TimeFun tnum_inverse_shift.

Definition tnum_and_back (w : width) (q b : tnum) : tnum :=
  Tnum (tnum_wand w (zeros q) (ones b)) (tnum_wrap w (ones q)).
TimeFun tnum_and_back.

Definition tnum_or_back (w : width) (q b : tnum) : tnum :=
  Tnum (tnum_wrap w (zeros q)) (tnum_wand w (ones q) (zeros b)).
TimeFun tnum_or_back.

Definition tnum_sign_project (sw rw : width) (n : Z) (q : tnum) : tnum :=
  Tnum (if Z.shiftr (tnum_wrap rw (zeros q)) n =? 0 then 0 else half sw)
    (if Z.shiftr (tnum_wrap rw (ones q)) n =? 0 then 0 else half sw).
TimeFun tnum_sign_project.

Definition tnum_back_shift (o : op) (w : width) (k : Z) (q : tnum) : tnum :=
  let copied := tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q in
  match o with
  | bvashr => tnum_meet w copied (tnum_sign_project w w (Z.max 0 (Zpos w - 1 - k)) q)
  | _ => copied
  end.
TimeFun tnum_back_shift.

Definition tnum_back_sext (sw rw : width) (q : tnum) : tnum :=
  tnum_meet sw (tnum_project sw rw (fun m => m) q)
    (tnum_sign_project sw rw (Zpos sw - 1) q).
TimeFun tnum_back_sext.

Definition tnum_lower (w : width) (l : Z) : tnum :=
  tnum_not w (tnum_upper w (tnum_wnot w l)).
TimeFun tnum_lower.

Definition tnum_order_back (strict : bool) (w : width) (q a b : tnum) : tnum * tnum :=
  let d := if strict then 1 else 0 in
  if Z.testbit (ones q) 0 then
    (tnum_upper w (tnum_max w b - d), tnum_lower w (tnum_min w a + d))
  else if Z.testbit (zeros q) 0 then
    (tnum_lower w (tnum_min w b + (1 - d)), tnum_upper w (tnum_max w a - (1 - d)))
  else (tnum_top, tnum_top).
TimeFun tnum_order_back.

Definition tnum_project_variable (o : op) (w : width) (b q : tnum) : tnum :=
  let inv := tnum_inverse_shift o in
  let zero := tnum_variable_raw inv w (Tnum 0 (zeros q)) b in
  let one := tnum_variable_raw inv w (Tnum 0 (ones q)) b in
  Tnum (ones zero) (ones one).
TimeFun tnum_project_variable.

Definition tnum_back_variable_shift (o : op) (w : width) (b q : tnum) : tnum :=
  let copied := tnum_project_variable o w b q in
  match o with
  | bvashr => tnum_meet w copied
      (tnum_sign_project w w (Z.max 0 (Zpos w - 1 - tnum_min w b)) q)
  | _ => copied
  end.
TimeFun tnum_back_variable_shift.

Definition tnum_backward_raw (o : op) (wps : list (width * tnum))
    (rw : width) (q : tnum) : list tnum :=
  match o, wps with
  | bvnot, [(w, _)] => [tnum_not w q]
  | (bvzext _ | bvtrunc _), [(w, _)] => [tnum_project w rw (fun m => m) q]
  | bvsext _, [(w, _)] => [tnum_back_sext w rw q]
  | bvextract _ lo, [(w, _)] => [tnum_project w rw (fun m => Z.shiftl m (Z.of_nat lo)) q]
  | bvand, [(w, a); (v, b)] => [tnum_and_back w q b; tnum_and_back v q a]
  | bvor, [(w, a); (v, b)] => [tnum_or_back w q b; tnum_or_back v q a]
  | bvxor, [(w, a); (v, b)] => [tnum_xor w q b; tnum_xor v q a]
  | bvadd, [(w, a); (v, b)] => [tnum_sub w q b; tnum_sub v q a]
  | bvsub, [(w, a); (v, b)] => [tnum_add w q b; tnum_sub v a q]
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(w, _); (v, b)] =>
    match tnum_constant v b with
    | Some k => [tnum_back_shift o w k q; b]
    | None => [tnum_back_variable_shift o w b q; b]
    end
  | bveq, [(_, a); (_, b)] => if Z.testbit (ones q) 0 then [b; a] else [a; b]
  | bvult, [(w, a); (_, b)] =>
    let p := tnum_order_back true w q a b in [fst p; snd p]
  | bvule, [(w, a); (_, b)] =>
    let p := tnum_order_back false w q a b in [fst p; snd p]
  | bvconcat, [(w, _); (v, _)] =>
    [tnum_project w rw (fun m => Z.shiftr m (Zpos v)) q;
      tnum_project v rw (fun m => m) q]
  | _, _ => map snd wps
  end.
TimeFun tnum_backward_raw.

Fixpoint tnum_refine (wps : list (width * tnum)) (qs : list tnum) : list tnum :=
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => tnum_meet w a q :: tnum_refine rest tail
  | (_, a) :: rest, [] => a :: tnum_refine rest []
  end.
TimeFun tnum_refine.

(** Reject an extraction offset before converting it or constructing its power.
    Every well-typed extraction passes this width-bounded check. *)
Definition tnum_table_bounded (o : op) (xs : list (width * tnum)) : bool :=
  match o, xs with
  | bvextract _ lo, [(w, _)] => Nat.ltb lo (Pos.to_nat w)
  | _, _ => true
  end.
TimeFun tnum_table_bounded.

Module KnownBitsTableCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_OPS L C) <: WORD_TABLE_OPS L K.
  Module Ops := KnownBitsOpsCode L C K.
  Include Ops.
  Definition wfwd (o : L.op) (rw : positive) (xs : list (positive * K.p)) : option K.p :=
    if Nat.eqb (length xs) (arity o) then
      if tnum_table_bounded o xs then Some (tnum_forward_raw o xs rw) else None
    else None.
  Definition wbwd (o : L.op) (rw : positive) (q : K.p)
      (xs : list (positive * K.p)) : option (list K.p) :=
    if Nat.eqb (length xs) (arity o) then
      if tnum_table_bounded o xs then Some (tnum_refine xs (tnum_backward_raw o xs rw q))
      else None
    else None.
End KnownBitsTableCode.

(** Successful width checking always admits the guarded table computation. *)
Lemma tnum_table_bounded_width : forall o xs rw,
  result_width o (map fst xs) = Some rw -> tnum_table_bounded o xs = true.
Proof.
  intros o xs rw Hwidth. destruct o; try reflexivity.
  destruct xs as [|[w a] [|[v b] rest]]; try reflexivity.
  cbn [result_width map fst] in Hwidth.
  destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)) eqn:Hbounds;
    [|discriminate].
  apply andb_true_iff in Hbounds. destruct Hbounds as [Hlo Hhi].
  apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
  cbn [tnum_table_bounded]. apply Nat.ltb_lt. lia.
Qed.

(** Unary comparison stops after traversing the shorter, right-hand argument. *)
Lemma tnum_leb_right_time : forall n m,
  (Nat.T_leb n m <= N.of_nat m + 1)%N.
Proof.
  intros n m; revert n. induction m as [|m IH]; intros [|n];
    time_unfold Nat.T_leb; time_cbn; rewrite ?Nat2N.inj_succ; try lia.
  specialize (IH n). lia.
Qed.

(** Checking an extraction offset never traverses more than its operand width. *)
Lemma tnum_ltb_right_time : forall n m,
  (Op.Nat.T_ltb n m <= N.of_nat m + 3)%N.
Proof.
  intros n m. pose proof (tnum_leb_right_time (S n) m).
  time_unfold Op.Nat.T_ltb. time_cbn. lia.
Qed.

(** The table guard has a width-only cost, including rejected raw offsets. *)
Lemma tnum_table_bounded_time : forall o xs,
  (T_tnum_table_bounded o xs <= 16 * N.of_nat
    ((fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1)%nat))%N.
Proof.
  intros o xs. destruct o; try (time_unfold T_tnum_table_bounded; time_cbn; nia).
  destruct xs as [|[w a] [|wp xs]];
    time_unfold T_tnum_table_bounded; time_cbn; try nia.
  pose proof (tnum_ltb_right_time lo (Pos.to_nat w)).
  pose proof (WordTime.positive_to_nat_time_bound w).
  cbn [map fold_right fst]. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_table_bounded_time.


Theorem tnum_refine_equation : forall wps qs,
  tnum_refine wps qs =
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => tnum_meet w a q :: tnum_refine rest tail
  | (_, a) :: rest, [] => a :: tnum_refine rest []
  end.
Proof.
  intros [|[w a] rest] [|q tail]; reflexivity.
Qed.
Theorem tnum_refine_length : forall wps qs, length (tnum_refine wps qs) = length wps.
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q tail];
    rewrite tnum_refine_equation; cbn [length]; [reflexivity|reflexivity| |];
    f_equal; apply IH.
Qed.

Theorem tnum_refine_refines : forall wps qs,
  Forall2 (fun wp q => tnum_leb (fst wp) q (snd wp) = true)
    wps (tnum_refine wps qs).
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q tail];
    rewrite tnum_refine_equation; constructor; try apply IH.
  - apply tnum_leb_bits. split; auto.
  - apply tnum_meet_lower_left.
Qed.

Definition kb_payload_sound (wp : width * tnum) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ tnum_gamma (fst wp) (snd wp) (snd y).

Theorem tnum_refine_sound : forall wps ys qs,
  Forall2 kb_payload_sound wps ys ->
  Forall2 (fun wp_y q => tnum_gamma (fst (fst wp_y)) q (snd (snd wp_y)))
    (combine wps ys) qs ->
  Forall2 (fun p y => tnum_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (tnum_refine wps qs)) ys.
Proof.
  intros wps ys qs Hgamma. revert qs.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; intros qs Hqs.
  - destruct qs; constructor.
  - inversion Hqs as [|wp_y q rest' qs' Hq Hrest]; subst qs.
    destruct Hhead as [Hwv [Hx Ha]]. cbn in Hwv, Hx, Ha, Hq. subst v.
    rewrite tnum_refine_equation. cbn [combine map fst snd]. constructor.
    + now apply tnum_meet_sound.
    + now apply IH.
Qed.
Definition tnum_projects (sw rw : width) (f g : Z -> Z) : Prop :=
  forall i m, 0 <= i < Zpos sw -> is_word rw m -> Z.testbit (g m) i = true ->
    exists j, 0 <= j < Zpos rw /\ Z.testbit m j = true /\
      forall x, is_word sw x -> Z.testbit (f x) j = Z.testbit x i.

Theorem tnum_project_sound : forall sw rw f g q x,
  tnum_projects sw rw f g -> is_word sw x -> tnum_gamma rw q (f x) ->
  tnum_gamma sw (tnum_project sw rw g q) x.
Proof.
  intros sw rw f g q x Hproject Hx Hq. apply tnum_gamma_bits in Hq.
  destruct Hq as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_project zeros ones] in Hbit;
    rewrite !tnum_wrap_agrees, tnum_wrap_bit in Hbit by exact Hi.
  - destruct (Hproject i _ Hi (wrap_is_word rw _) Hbit) as [j [Hj [Hm Hcopy]]].
    rewrite tnum_wrap_bit in Hm by exact Hj. rewrite <- Hcopy by exact Hx. now apply Hz.
  - destruct (Hproject i _ Hi (wrap_is_word rw _) Hbit) as [j [Hj [Hm Hcopy]]].
    rewrite tnum_wrap_bit in Hm by exact Hj. rewrite <- Hcopy by exact Hx. now apply Ho.
Qed.

Lemma tnum_inverse_source : forall o w k i j,
  tnum_shift_op o -> 0 <= k -> 0 <= i < Zpos w ->
  tnum_source (tnum_inverse_shift o) w k i = Some j ->
  tnum_source o w k j = Some i.
Proof.
  intros o w k i j Ho Hk Hi Hsource.
  destruct Ho as [Ho|[Ho|[Ho|[Ho|Ho]]]]; subst o;
    cbn [tnum_inverse_shift tnum_source] in Hsource |- *.
  - destruct (i + k <? Zpos w) eqn:Hsmall; [|discriminate].
    injection Hsource as <-. rewrite (proj2 (Z.leb_le k (i + k))) by lia. f_equal. lia.
  - destruct (k <=? i) eqn:Hsmall; [apply Z.leb_le in Hsmall|discriminate].
    injection Hsource as <-. rewrite (proj2 (Z.ltb_lt (i - k + k) (Zpos w))) by lia.
    f_equal. lia.
  - destruct (k <=? i) eqn:Hsmall; [apply Z.leb_le in Hsmall|discriminate].
    injection Hsource as <-. change (Some (Z.min (i - k + k) (Zpos w - 1)) = Some i).
    f_equal. lia.
  - injection Hsource as <-. rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
    replace (i + k - k) with i by ring. now rewrite Z.mod_small by exact Hi.
  - injection Hsource as <-. rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia.
    replace (i - k + k) with i by ring. now rewrite Z.mod_small by exact Hi.
Qed.

Lemma tnum_projects_shift : forall o w k,
  tnum_shift_op o -> 0 <= k ->
  tnum_projects w w (tnum_scalar_value o w k)
    (tnum_scalar_value (tnum_inverse_shift o) w k).
Proof.
  intros o w k Ho Hk i m Hi Hm Hbit.
  rewrite tnum_scalar_bits in Hbit by assumption.
  destruct (tnum_source (tnum_inverse_shift o) w k i) as [j|] eqn:Hsource;
    [|discriminate].
  exists j. pose proof (tnum_source_range _ w k i j Hk Hi Hsource) as Hj.
  split; [exact Hj|]. split; [exact Hbit|]. intros x Hx.
  rewrite tnum_scalar_bits by assumption.
  now rewrite (tnum_inverse_source o w k i j Ho Hk Hi Hsource).
Qed.

Lemma tnum_projects_resize : forall sw rw,
  tnum_projects sw rw (wrap rw) (fun m => m).
Proof.
  intros sw rw i m Hi Hm Hbit.
  assert (Hlow : i < Zpos rw).
  { destruct (Z_lt_ge_dec i (Zpos rw)); [assumption|].
    rewrite (word_bits_high rw m i Hm ltac:(lia)) in Hbit. discriminate. }
  exists i. split; [lia|]. split; [exact Hbit|].
  intros x Hx. apply tnum_wrap_bit. lia.
Qed.

Lemma tnum_projects_sext_low : forall sw rw,
  tnum_projects sw rw (fun x => wrap rw (signed sw x)) (fun m => m).
Proof.
  intros sw rw i m Hi Hm Hbit.
  assert (Hlow : i < Zpos rw).
  { destruct (Z_lt_ge_dec i (Zpos rw)); [assumption|].
    rewrite (word_bits_high rw m i Hm ltac:(lia)) in Hbit. discriminate. }
  exists i. split; [lia|]. split; [exact Hbit|]. intros x Hx.
  rewrite tnum_wrap_bit, signed_bits by (try assumption; lia).
  now rewrite (proj2 (Z.ltb_lt i (Zpos sw))) by lia.
Qed.

Lemma tnum_projects_extract : forall sw rw lo,
  0 <= lo ->
  tnum_projects sw rw (fun x => wrap rw (x / 2 ^ lo)) (fun m => Z.shiftl m lo).
Proof.
  intros sw rw lo Hlo i m Hi Hm Hbit. rewrite Z.shiftl_spec in Hbit by lia.
  assert (Hsource : 0 <= i - lo < Zpos rw).
  { split.
    - destruct (Z_le_gt_dec 0 (i - lo)); [assumption|].
      rewrite Z.testbit_neg_r in Hbit by lia. discriminate.
    - destruct (Z_lt_ge_dec (i - lo) (Zpos rw)); [assumption|].
      rewrite (word_bits_high rw m (i - lo) Hm ltac:(lia)) in Hbit. discriminate. }
  exists (i - lo). split; [exact Hsource|]. split; [exact Hbit|]. intros x Hx.
  rewrite tnum_wrap_bit, Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Theorem tnum_and_back_sound : forall w q b x y,
  tnum_gamma w b y -> tnum_gamma w q (wand w x y) ->
  tnum_gamma w (tnum_and_back w q b) x.
Proof.
  intros w q b x y Hb Hq. apply tnum_gamma_bits in Hb, Hq.
  destruct Hb as [Hbz Hbo], Hq as [Hqz Hqo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_and_back zeros ones] in Hbit.
  - rewrite tnum_wand_agrees, tnum_and_bit in Hbit by exact Hi.
    apply andb_true_iff in Hbit as [Hq Hb].
    specialize (Hqz i Hi Hq). rewrite tnum_and_bit, (Hbo i Hi Hb), andb_true_r
      in Hqz by exact Hi. exact Hqz.
  - rewrite tnum_wrap_agrees, tnum_wrap_bit in Hbit by exact Hi.
    specialize (Hqo i Hi Hbit).
    rewrite tnum_and_bit in Hqo by exact Hi. apply andb_true_iff in Hqo. tauto.
Qed.

Theorem tnum_or_back_sound : forall w q b x y,
  tnum_gamma w b y -> tnum_gamma w q (wor w x y) ->
  tnum_gamma w (tnum_or_back w q b) x.
Proof.
  intros w q b x y Hb Hq. apply tnum_gamma_bits in Hb, Hq.
  destruct Hb as [Hbz Hbo], Hq as [Hqz Hqo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_or_back zeros ones] in Hbit.
  - rewrite tnum_wrap_agrees, tnum_wrap_bit in Hbit by exact Hi.
    specialize (Hqz i Hi Hbit).
    rewrite tnum_or_bit in Hqz by exact Hi. apply orb_false_iff in Hqz. tauto.
  - rewrite tnum_wand_agrees, tnum_and_bit in Hbit by exact Hi.
    apply andb_true_iff in Hbit as [Hq Hb].
    specialize (Hqo i Hi Hq). rewrite tnum_or_bit, (Hbz i Hi Hb), orb_false_r
      in Hqo by exact Hi. exact Hqo.
Qed.

Lemma tnum_xor_zero : forall w x, is_word w x -> wxor w x 0 = x.
Proof.
  intros w x Hx. apply (word_ext w); [apply wxor_is_word|exact Hx|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite tnum_xor_bit, Z.bits_0, xorb_false_r by lia. reflexivity.
  - rewrite !(word_bits_high w) by (try apply wxor_is_word; try exact Hx; lia). reflexivity.
Qed.

Theorem tnum_xor_back_sound : forall w q b x y,
  is_word w x -> tnum_gamma w b y -> tnum_gamma w q (wxor w x y) ->
  tnum_gamma w (tnum_xor w q b) x.
Proof.
  intros w q b x y Hx Hb Hq.
  pose proof (tnum_xor_sound w q b (wxor w x y) y Hq Hb) as Hback.
  rewrite <- wxor_assoc, wxor_self, tnum_xor_zero in Hback by exact Hx. exact Hback.
Qed.

Lemma tnum_add_sub_cancel : forall w x y, is_word w x -> is_word w y ->
  wsub w (wadd w x y) y = x /\ wadd w (wsub w x y) y = x /\
  wsub w x (wsub w x y) = y.
Proof.
  intros w x y Hx Hy. rewrite !wsub_value, !wadd_value.
  assert (Hsub : forall a b, is_word w b -> wrap w (wrap w a - b) = wrap w (a - b)).
  { intros a b Hb. rewrite (wrap_sub w a b), (wrap_id w b Hb). reflexivity. }
  assert (Hadd : forall a b, is_word w b -> wrap w (wrap w a + b) = wrap w (a + b)).
  { intros a b Hb. rewrite (wrap_add w a b), (wrap_id w b Hb). reflexivity. }
  split.
  - rewrite Hsub by exact Hy. replace (x + y - y) with x by ring. now apply wrap_id.
  - split.
    + rewrite Hadd by exact Hy. replace (x - y + y) with x by ring. now apply wrap_id.
    + transitivity (wrap w (x - (x - y))).
      * rewrite (wrap_sub w x (x - y)), (wrap_id w x Hx). reflexivity.
      * replace (x - (x - y)) with y by ring. now apply wrap_id.
Qed.

Theorem tnum_add_back_sound : forall w q a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w q (wadd w x y) ->
  tnum_gamma w (tnum_sub w q b) x /\ tnum_gamma w (tnum_sub w q a) y.
Proof.
  intros w q a b x y Hx Hy Ha Hb Hq. split.
  - rewrite <- (proj1 (tnum_add_sub_cancel w x y Hx Hy)). now apply tnum_sub_sound.
  - rewrite wadd_comm in Hq. rewrite <- (proj1 (tnum_add_sub_cancel w y x Hy Hx)).
    now apply tnum_sub_sound.
Qed.

Theorem tnum_sub_back_sound : forall w q a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w q (wsub w x y) ->
  tnum_gamma w (tnum_add w q b) x /\ tnum_gamma w (tnum_sub w a q) y.
Proof.
  intros w q a b x y Hx Hy Ha Hb Hq. split.
  - rewrite <- (proj1 (proj2 (tnum_add_sub_cancel w x y Hx Hy))). now apply tnum_add_sound.
  - rewrite <- (proj2 (proj2 (tnum_add_sub_cancel w x y Hx Hy))).
    apply tnum_sub_sound;
      [exact (word_fun2_is_word bvsub BSub w x y eq_refl)|exact Ha|exact Hq].
Qed.

Lemma tnum_high_set_bit : forall rw m n,
  is_word rw m -> 0 <= n -> Z.shiftr m n <> 0 ->
  exists j, n <= j < Zpos rw /\ Z.testbit m j = true.
Proof.
  intros rw m n Hm Hn Hnonzero.
  assert (Hnonneg : 0 <= Z.shiftr m n) by (apply Z.shiftr_nonneg; exact (proj1 Hm)).
  pose proof (Z.bit_log2 (Z.shiftr m n) ltac:(lia)) as Hbit.
  pose proof (Z.log2_nonneg (Z.shiftr m n)) as Hlog.
  rewrite Z.shiftr_spec in Hbit by exact Hlog.
  exists (Z.log2 (Z.shiftr m n) + n). split; [|exact Hbit]. split; [lia|].
  destruct (Z_lt_ge_dec (Z.log2 (Z.shiftr m n) + n) (Zpos rw)); [assumption|].
  rewrite (word_bits_high rw m (Z.log2 (Z.shiftr m n) + n) Hm ltac:(lia)) in Hbit.
  discriminate.
Qed.

Lemma tnum_sign_project_sound : forall sw rw n q x z,
  0 <= n -> tnum_gamma rw q z ->
  (forall j, n <= j < Zpos rw -> Z.testbit z j = Z.testbit x (Zpos sw - 1)) ->
  tnum_gamma sw (tnum_sign_project sw rw n q) x.
Proof.
  intros sw rw n q x z Hn Hq Hfill. apply tnum_gamma_bits in Hq.
  destruct Hq as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_sign_project zeros ones] in Hbit; rewrite tnum_wrap_agrees in Hbit.
  - destruct (Z.shiftr (wrap rw (zeros q)) n =? 0) eqn:Hnone;
      [rewrite Z.bits_0 in Hbit; discriminate|].
    apply Z.eqb_neq in Hnone.
    destruct (tnum_high_set_bit rw _ n (wrap_is_word rw _) Hn Hnone) as [j [Hj Hset]].
    rewrite tnum_half_value, Z.pow2_bits_eqb in Hbit by lia.
    apply Z.eqb_eq in Hbit. subst i. rewrite <- (Hfill j Hj). apply Hz; [lia|].
    rewrite <- (tnum_wrap_bit rw (zeros q) j ltac:(lia)). exact Hset.
  - destruct (Z.shiftr (wrap rw (ones q)) n =? 0) eqn:Hnone;
      [rewrite Z.bits_0 in Hbit; discriminate|].
    apply Z.eqb_neq in Hnone.
    destruct (tnum_high_set_bit rw _ n (wrap_is_word rw _) Hn Hnone) as [j [Hj Hset]].
    rewrite tnum_half_value, Z.pow2_bits_eqb in Hbit by lia.
    apply Z.eqb_eq in Hbit. subst i. rewrite <- (Hfill j Hj). apply Ho; [lia|].
    rewrite <- (tnum_wrap_bit rw (ones q) j ltac:(lia)). exact Hset.
Qed.

Theorem tnum_back_shift_sound : forall o w f k q x,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w k -> is_word w x ->
  tnum_gamma w q (eval_binary_tag f w x k) -> tnum_gamma w (tnum_back_shift o w k q) x.
Proof.
  intros o w f k q x Ho Hf Hk Hx Hq.
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx) in Hq.
  assert (Hcopied : tnum_gamma w
    (tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q) x).
  { eapply tnum_project_sound; [apply tnum_projects_shift; [exact Ho|exact (proj1 Hk)]|
      exact Hx|exact Hq]. }
  unfold tnum_back_shift. destruct o; try exact Hcopied.
  apply tnum_meet_sound; [exact Hcopied|].
  apply (tnum_sign_project_sound w w (Z.max 0 (Zpos w - 1 - k)) q x
    (tnum_scalar_value bvashr w k x)); [lia|exact Hq|].
  intros j Hj. rewrite tnum_scalar_bits by (try assumption; unfold is_word in Hk; lia).
  change (Z.testbit x (Z.min (j + k) (Zpos w - 1)) = Z.testbit x (Zpos w - 1)).
  f_equal. lia.
Qed.

Theorem tnum_back_sext_sound : forall sw rw q x,
  is_word sw x -> tnum_gamma rw q (wrap rw (signed sw x)) ->
  tnum_gamma sw (tnum_back_sext sw rw q) x.
Proof.
  intros sw rw q x Hx Hq. apply tnum_meet_sound.
  - eapply tnum_project_sound; [apply tnum_projects_sext_low|exact Hx|exact Hq].
  - apply (tnum_sign_project_sound sw rw (Zpos sw - 1) q x
      (wrap rw (signed sw x))); [lia|exact Hq|].
    intros j Hj. rewrite tnum_wrap_bit, signed_bits by (try assumption; lia).
    destruct (j <? Zpos sw) eqn:Hlow.
    + apply Z.ltb_lt in Hlow. f_equal. lia.
    + apply msb_testbit.
Qed.

Lemma tnum_boolean_sound : forall q (b : bool),
  tnum_gamma 1%positive q (if b then 1 else 0) ->
  (Z.testbit (ones q) 0 = true -> b = true) /\
  (Z.testbit (zeros q) 0 = true -> b = false).
Proof.
  intros q b Hq. apply tnum_gamma_bits in Hq. destruct Hq as [Hz Ho].
  split; intro Hbit; destruct b; try reflexivity.
  - specialize (Ho 0 ltac:(lia) Hbit). discriminate.
  - specialize (Hz 0 ltac:(lia) Hbit). discriminate.
Qed.

Lemma tnum_not_value : forall w x, is_word w x -> wnot w x = modulus w - 1 - x.
Proof.
  intros w x Hx. rewrite wnot_lnot, (wrap_id w x Hx), lnot_value, wrap_mod.
  symmetry. apply Z.mod_unique with (q := -1).
  - left. unfold is_word in Hx. lia.
  - ring.
Qed.

Lemma tnum_lower_sound : forall w l x,
  is_word w x -> 0 <= l <= x -> tnum_gamma w (tnum_lower w l) x.
Proof.
  intros w l x Hx Hl. unfold tnum_lower. rewrite tnum_wnot_agrees.
  assert (Hlword : is_word w l) by (unfold is_word in *; lia).
  rewrite <- (wnot_involutive w x Hx). apply tnum_not_sound, tnum_upper_sound.
  rewrite !tnum_not_value by assumption. unfold is_word in Hx. lia.
Qed.

Theorem tnum_order_back_sound : forall (strict : bool) w q a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive q (if (if strict then x <? y else x <=? y) then 1 else 0) ->
  tnum_gamma w (fst (tnum_order_back strict w q a b)) x /\
  tnum_gamma w (snd (tnum_order_back strict w q a b)) y.
Proof.
  intros strict w q a b x y Hx Hy Ha Hb Hq.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hax.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hby.
  assert (Hamin : 0 <= tnum_min w a).
  { unfold tnum_min. rewrite tnum_wrap_agrees. apply wrap_is_word. }
  assert (Hbmin : 0 <= tnum_min w b).
  { unfold tnum_min. rewrite tnum_wrap_agrees. apply wrap_is_word. }
  destruct (tnum_boolean_sound q _ Hq) as [Htrue Hfalse]. unfold tnum_order_back.
  destruct (Z.testbit (ones q) 0) eqn:Hone.
  - specialize (Htrue eq_refl). destruct strict; cbn in Htrue |- *;
      [apply Z.ltb_lt in Htrue|apply Z.leb_le in Htrue]; split;
      first [apply tnum_upper_sound; unfold is_word in Hx; lia|
        apply tnum_lower_sound; [exact Hy|lia]].
  - destruct (Z.testbit (zeros q) 0) eqn:Hzero; [|split; apply tnum_top_sound].
    specialize (Hfalse eq_refl). destruct strict; cbn in Hfalse |- *;
      [apply Z.ltb_ge in Hfalse|apply Z.leb_gt in Hfalse]; split;
      first [apply tnum_lower_sound; [exact Hx|lia]|
        apply tnum_upper_sound; unfold is_word in Hy; lia].
Qed.

Lemma tnum_project_variable_sound : forall o w b q x k,
  tnum_shift_op o -> is_word w x -> is_word w k -> tnum_gamma w b k ->
  tnum_gamma w q (tnum_scalar_value o w k x) ->
  tnum_gamma w (tnum_project_variable o w b q) x.
Proof.
  intros o w b q x k Ho Hx Hk Hb Hq.
  apply (tnum_gamma_monotone w
    (tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q)).
  - pose proof (tnum_variable_raw_amount_bound (tnum_inverse_shift o) w
      (Tnum 0 (zeros q)) b k Hk Hb) as Hz.
    pose proof (tnum_variable_raw_amount_bound (tnum_inverse_shift o) w
      (Tnum 0 (ones q)) b k Hk Hb) as Hone.
    apply tnum_leb_bits in Hz, Hone. destruct Hz as [_ Hz], Hone as [_ Hone].
    unfold tnum_project_variable.
    apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [tnum_project zeros ones]; rewrite tnum_wrap_agrees, tnum_wrap_bit by exact Hi.
    + specialize (Hz i Hi Hbit). unfold tnum_scalar, tnum_map, tnum_min in Hz.
      cbn [ones] in Hz. rewrite tnum_wrap_agrees, tnum_wrap_bit in Hz by exact Hi.
      exact Hz.
    + specialize (Hone i Hi Hbit). unfold tnum_scalar, tnum_map, tnum_min in Hone.
      cbn [ones] in Hone. rewrite tnum_wrap_agrees, tnum_wrap_bit in Hone by exact Hi.
      exact Hone.
  - eapply tnum_project_sound; [apply tnum_projects_shift; [exact Ho|exact (proj1 Hk)]|
      exact Hx|exact Hq].
Qed.

Theorem tnum_back_variable_shift_sound : forall o w f b q x k,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w x -> is_word w k ->
  tnum_gamma w b k -> tnum_gamma w q (eval_binary_tag f w x k) ->
  tnum_gamma w (tnum_back_variable_shift o w b q) x.
Proof.
  intros o w f b q x k Ho Hf Hx Hk Hb Hq.
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx) in Hq.
  pose proof (tnum_project_variable_sound o w b q x k Ho Hx Hk Hb Hq) as Hcopied.
  unfold tnum_back_variable_shift. destruct o; try exact Hcopied.
  apply tnum_meet_sound; [exact Hcopied|].
  pose proof (tnum_unsigned_bounds w b k Hk Hb) as Hbounds.
  apply (tnum_sign_project_sound w w (Z.max 0 (Zpos w - 1 - tnum_min w b)) q x
    (tnum_scalar_value bvashr w k x)); [lia|exact Hq|].
  intros j Hj. rewrite tnum_scalar_bits by (try assumption; unfold is_word in Hk; lia).
  change (Z.testbit x (Z.min (j + k) (Zpos w - 1)) = Z.testbit x (Zpos w - 1)).
  f_equal. lia.
Qed.

Theorem tnum_concat_back_sound : forall w v q x y,
  is_word w x -> is_word v y ->
  tnum_gamma (w + v)%positive q (x * modulus v + y) ->
  tnum_gamma w (tnum_project w (w + v)%positive (fun m => Z.shiftr m (Zpos v)) q) x /\
  tnum_gamma v (tnum_project v (w + v)%positive (fun m => m) q) y.
Proof.
  intros w v q x y Hx Hy Hq. split.
  - apply (tnum_project_sound w (w + v)%positive
      (fun z => z * modulus v + y)); [|exact Hx|exact Hq].
    intros i m Hi Hm Hbit. rewrite Z.shiftr_spec in Hbit by lia.
    exists (i + Zpos v). split; [rewrite Pos2Z.inj_add; lia|]. split; [exact Hbit|].
    intros z Hz. rewrite modulus_value, split_sum_bits by
      (try (rewrite <- modulus_value; exact Hy); lia).
    rewrite (proj2 (Z.ltb_ge (i + Zpos v) (Zpos v))) by lia. f_equal. lia.
  - apply (tnum_project_sound v (w + v)%positive
      (fun z => x * modulus v + z)); [|exact Hy|exact Hq].
    intros i m Hi Hm Hbit. exists i. split; [rewrite Pos2Z.inj_add; lia|].
    split; [exact Hbit|]. intros z Hz. rewrite modulus_value, split_sum_bits by
      (try (rewrite <- modulus_value; exact Hz); lia).
    now rewrite (proj2 (Z.ltb_lt i (Zpos v))) by lia.
Qed.

Lemma tnum_backward_one_sound : forall o w a x rw z q,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun p v => tnum_gamma w p v) (tnum_backward_raw o [(w, a)] rw q) [x].
Proof.
  intros o w a x rw z q Hx Ha Heval Hq. destruct o.
  all: unfold tnum_backward_raw; constructor; [|constructor].
  all: try exact Ha.
  - rewrite (eval_op_fun1 bvnot w x UNot eq_refl) in Heval. injection Heval as <- <-.
    rewrite <- (wnot_involutive w x Hx). now apply tnum_not_sound.
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_resize|exact Hx|exact Hq].
  - rewrite eval_op_sext in Heval. injection Heval as <- <-. now apply tnum_back_sext_sound.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_resize|exact Hx|exact Hq].
  - rewrite eval_op_extract in Heval.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)); [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_extract; lia|exact Hx|exact Hq].
Qed.

Lemma tnum_backward_shift_sound : forall o w f a b x y q,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w q (eval_binary_tag f w x y) ->
  Forall2 (fun p v => tnum_gamma w p v) (tnum_backward_raw o [(w, a); (w, b)] w q) [x; y].
Proof.
  intros o w f a b x y q Ho Hf Hx Hy Ha Hb Hq.
  assert (Hknown : forall k, tnum_constant w b = Some k ->
    tnum_gamma w (tnum_back_shift o w k q) x).
  { intros k Hconstant. pose proof (tnum_constant_value w b y k Hy Hb Hconstant) as Hyk.
    subst k. now apply (tnum_back_shift_sound o w f). }
  assert (Hvariable : tnum_gamma w (tnum_back_variable_shift o w b q) x).
  { now apply (tnum_back_variable_shift_sound o w f b q x y). }
  destruct Ho as [Ho|[Ho|[Ho|[Ho|Ho]]]]; subst o;
    unfold tnum_backward_raw; destruct (tnum_constant w b) as [k|] eqn:Hconstant.
  all: constructor; [first [now apply Hknown|exact Hvariable]|
    constructor; [exact Hb|constructor]].
Qed.

Lemma tnum_backward_fun2_sound : forall o w f a b x y q,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w q (eval_binary_tag f w x y) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] w q) [x; y].
Proof.
  intros o w f a b x y q Hf Hx Hy Ha Hb Hq. destruct o;
    try discriminate Hf; injection Hf as <-;
    try (change (Forall2 (fun p v => tnum_gamma w p v) [a; b] [x; y]);
      constructor; [exact Ha|constructor; [exact Hb|constructor]]);
    try solve [eapply tnum_backward_shift_sound; try eassumption; try reflexivity;
      unfold tnum_shift_op; tauto].
  - destruct (tnum_add_back_sound w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - destruct (tnum_sub_back_sound w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - constructor; [now apply (tnum_and_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wand_comm in Hq.
    now apply (tnum_and_back_sound w q a y x).
  - constructor; [now apply (tnum_or_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wor_comm in Hq.
    now apply (tnum_or_back_sound w q a y x).
  - constructor; [now apply (tnum_xor_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wxor_comm in Hq.
    now apply (tnum_xor_back_sound w q a y x).
Qed.


Lemma tnum_backward_cmp_sound : forall o w f a b x y q,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive q (if eval_comparison_tag f w x y then 1 else 0) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] 1%positive q) [x; y].
Proof.
  intros o w f a b x y q Hf Hx Hy Ha Hb Hq.
  destruct o; try discriminate Hf; injection Hf as <-; cbn [eval_comparison_tag] in Hq.
  - unfold tnum_backward_raw.
    destruct (Z.testbit (ones q) 0) eqn:Htrue.
    + apply tnum_boolean_sound in Hq. destruct Hq as [Hq _]. specialize (Hq Htrue).
      apply Z.eqb_eq in Hq. rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
      subst y. constructor; [exact Hb|constructor; [exact Ha|constructor]].
    + constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - rewrite wult_value, (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
    destruct (tnum_order_back_sound true w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - rewrite wule_value, (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
    destruct (tnum_order_back_sound false w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
Qed.

Lemma tnum_backward_two_sound : forall o w v a b x y rw z q,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) -> tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine [(w, a); (v, b)] [(w, x); (v, y)])
    (tnum_backward_raw o [(w, a); (v, b)] rw q).
Proof.
  intros o w v a b x y rw z q Hx Hy Ha Hb Heval Hq.
  destruct (word_fun2 o) as [f|] eqn:Hf.
  - pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
    rewrite (eval_op_fun2 o v x y f Hf) in Heval. injection Heval as <- <-.
    pose proof (tnum_backward_fun2_sound o v f a b x y q Hf Hx Hy Ha Hb Hq) as Hback.
    inversion Hback as [|p x' ps xs Hl Htail]; subst.
    inversion Htail as [|p' y' ps' xs' Hr Hnil]; subst.
    inversion Hnil; subst.
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - destruct (word_cmp o) as [f|] eqn:Hcmp.
    + pose proof (eval_op_cmp_width o f w v x y (rw, z) Hcmp Heval) as ->.
      rewrite (eval_op_cmp o v x y f Hcmp) in Heval. injection Heval as <- <-.
      pose proof (tnum_backward_cmp_sound o v f a b x y q Hcmp Hx Hy Ha Hb Hq) as Hback.
      inversion Hback as [|p x' ps xs Hl Htail]; subst.
      inversion Htail as [|p' y' ps' xs' Hr Hnil]; subst.
      inversion Hnil; subst.
      constructor; [exact Hl|constructor; [exact Hr|constructor]].
    + destruct o; try discriminate Hf; try discriminate Hcmp;
        try (constructor; [exact Ha|constructor; [exact Hb|constructor]]).
      rewrite eval_op_concat in Heval. injection Heval as <- <-.
      rewrite (wrap_id w x Hx), (wrap_id v y Hy) in Hq.
      apply (proj1 (tnum_gamma_wrap (w + v)%positive q (x * modulus v + y))) in Hq.
      destruct (tnum_concat_back_sound w v q x y Hx Hy Hq) as [Hl Hr].
      constructor; [exact Hl|constructor; [exact Hr|constructor]].
Qed.

Lemma tnum_backward_identity_sound : forall wps ys,
  Forall2 kb_payload_sound wps ys ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (map snd wps).
Proof.
  intros wps ys Hgamma.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; cbn; constructor.
  - exact (proj2 (proj2 Hhead)).
  - exact IH.
Qed.
Theorem tnum_backward_raw_sound : forall o wps ys rw z q,
  Forall2 kb_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (tnum_backward_raw o wps rw q).
Proof.
  intros o wps ys rw z q Hgamma Heval Hq.
  destruct wps as [|[w a] [|[v b] [|wp rest]]].
  - destruct o; constructor.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    pose proof (tnum_backward_one_sound o w a x rw z q Hx Ha Heval Hq) as Hback.
    inversion Hback as [|p x' ps xs Hl Hnil]; subst. inversion Hnil; subst.
    constructor; [exact Hl|constructor].
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (tnum_backward_two_sound o w v a b x y rw z q Hx Hy Ha Hb Heval Hq).
  - destruct o; unfold tnum_backward_raw;
      apply tnum_backward_identity_sound; exact Hgamma.
Qed.

Lemma tnum_refine_word_sound : forall xs cs qs,
  Forall2 kb_payload_sound xs cs ->
  Forall2 (fun wp_y q => tnum_gamma (fst (fst wp_y)) q (snd (snd wp_y)))
    (combine xs cs) qs ->
  Forall2 (fun p c => tnum_gamma (fst c) p (snd c)) (tnum_refine xs qs) cs.
Proof.
  intros xs cs qs Hpayload. revert qs.
  induction Hpayload as [|[w a] [v z] xs cs Hhead Htail IH]; intros qs Hqs.
  - inversion Hqs; subst. rewrite tnum_refine_equation. constructor.
  - inversion Hqs as [|p q ps qs' Hq Hrest]; subst.
    destruct Hhead as [Hwidth [Hz Ha]]. cbn [fst snd] in Hwidth, Ha, Hq. subst v.
    rewrite tnum_refine_equation. constructor.
    + apply tnum_meet_sound; assumption.
    + now apply IH.
Qed.

Module KnownBitsTable (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (K : KNOWN_BITS L C)
    <: KNOWN_BITS_TABLE L C K.
  Include KnownBitsTableCode L C K.
  Module ForwardSound := KnownBitsSuppliedForwardProof L C K.
  (** A width-checked forward request keeps the original transfer result. *)
  Lemma wfwd_width_checked : forall o rw xs,
    L.result_width o (map fst xs) = Some rw ->
    wfwd o rw xs = Some (tnum_forward_raw o xs rw).
  Proof.
    intros o rw xs Hwidth.
    pose proof (result_width_arity o (map fst xs) rw Hwidth) as Harity.
    rewrite length_map in Harity. unfold wfwd.
    rewrite Harity, Nat.eqb_refl, (tnum_table_bounded_width o xs rw Hwidth).
    reflexivity.
  Qed.
  (** A width-checked backward request keeps the original refined operands. *)
  Lemma wbwd_width_checked : forall o rw q xs,
    L.result_width o (map fst xs) = Some rw ->
    wbwd o rw q xs = Some (tnum_refine xs (tnum_backward_raw o xs rw q)).
  Proof.
    intros o rw q xs Hwidth.
    pose proof (result_width_arity o (map fst xs) rw Hwidth) as Harity.
    rewrite length_map in Harity. unfold wbwd.
    rewrite Harity, Nat.eqb_refl, (tnum_table_bounded_width o xs rw Hwidth).
    reflexivity.
  Qed.
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      K.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> K.pgamma rw r z.
  Proof.
    intros o rw wps cs z r Hforward Hgamma Heval.
    unfold wfwd in Hforward.
    destruct (Nat.eqb (length wps) (arity o)); [|discriminate].
    destruct (tnum_table_bounded o wps); [|discriminate].
    injection Hforward as <-.
    apply (proj2 (K.gamma_tnum _ _ _)).
    eapply ForwardSound.tnum_forward_raw_sound; [|exact Heval].
    eapply Forall2_impl; [|exact Hgamma].
    intros wp c [Hw [Hx Ha]]. unfold tnum_payload_sound.
    split; [exact Hw|]. split; [exact Hx|].
    now apply (proj1 (K.gamma_tnum _ _ _)).
  Qed.
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      K.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> K.pgamma rw q z ->
    Forall2 (fun wp c => K.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof.
    intros o rw q wps ys cs z Hback Hgamma Heval Hq.
    unfold wbwd in Hback.
    destruct (Nat.eqb (length wps) (arity o)); [|discriminate].
    destruct (tnum_table_bounded o wps); [|discriminate].
    injection Hback as <-.
    assert (Hpayload : Forall2 kb_payload_sound wps cs).
    { clear Heval Hq.
      induction Hgamma as [|wp c wps cs Hhead Htail IH]; constructor.
      - destruct Hhead as [Hw [Hx Ha]].
        unfold kb_payload_sound. split; [exact Hw|]. split; [exact Hx|].
        now apply (proj1 (K.gamma_tnum _ _ _)).
      - exact IH. }
    apply (proj1 (K.gamma_tnum rw q z)) in Hq.
    pose proof (tnum_backward_raw_sound o wps cs rw z q Hpayload Heval Hq) as Hraw.
    pose proof (tnum_refine_sound wps cs _ Hpayload Hraw) as Hresult.
    eapply Forall2_impl; [|exact Hresult].
    intros wp c Hhead. now apply (proj2 (K.gamma_tnum _ _ _)).
  Qed.

End KnownBitsTable.

(** Projection normalizes each output mask to its source width. *)
Lemma back_project_bits : forall sw rw f q,
  (tnum_bits (tnum_project sw rw f q) <= 2 * Pos.to_nat sw)%nat.
Proof.
  intros sw rw f q. apply tnum_bounded_bits; cbn [tnum_project zeros ones];
    rewrite tnum_wrap_agrees; apply wrap_is_word.
Qed.

(** A backward conjunction returns two bounded masks. *)
Lemma back_and_bits : forall w q b,
  (tnum_bits (tnum_and_back w q b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w q b. apply tnum_bounded_bits; cbn [tnum_and_back zeros ones].
  - rewrite tnum_wand_agrees. apply wand_is_word.
  - rewrite tnum_wrap_agrees. apply wrap_is_word.
Qed.

(** A backward disjunction returns two bounded masks. *)
Lemma back_or_bits : forall w q b,
  (tnum_bits (tnum_or_back w q b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w q b. apply tnum_bounded_bits; cbn [tnum_or_back zeros ones].
  - rewrite tnum_wrap_agrees. apply wrap_is_word.
  - rewrite tnum_wand_agrees. apply wand_is_word.
Qed.

(** Sign projection stores either zero or the single source sign bit. *)
Lemma back_sign_bits : forall sw rw n q,
  (tnum_bits (tnum_sign_project sw rw n q) <= 2 * Pos.to_nat sw)%nat.
Proof.
  intros sw rw n q. pose proof (WordTime.word_half_size_bound sw) as Hhalf.
  unfold tnum_sign_project, tnum_bits; cbn [zeros ones].
  destruct (Z.shiftr (tnum_wrap rw (zeros q)) n =? 0),
    (Z.shiftr (tnum_wrap rw (ones q)) n =? 0);
    try change (Z.size_nat 0) with 0%nat in *; lia.
Qed.

(** A fixed inverse shift finishes with bounded projection or bounded meet. *)
Lemma back_shift_bits : forall o w k q,
  (tnum_bits (tnum_back_shift o w k q) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros o w k q. destruct o; cbn [tnum_back_shift];
    first [apply back_project_bits|apply tnum_meet_bits].
Qed.

(** Backward sign extension finishes with a normalized meet. *)
Lemma back_sext_bits : forall sw rw q,
  (tnum_bits (tnum_back_sext sw rw q) <= 2 * Pos.to_nat sw)%nat.
Proof. intros. apply tnum_meet_bits. Qed.

(** A lower-bound mask is normalized by its final negation. *)
Lemma back_lower_bits : forall w l,
  (tnum_bits (tnum_lower w l) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_not_bits. Qed.

(** Two variable projections retain at most the combined bounded result masks. *)
Lemma back_project_variable_bits : forall o w b q,
  (tnum_bits (tnum_project_variable o w b q) <= 4 * Pos.to_nat w)%nat.
Proof.
  intros o w b q.
  pose proof (tnum_variable_raw_bits (tnum_inverse_shift o) w
    (Tnum 0 (zeros q)) b) as Hzero.
  pose proof (tnum_variable_raw_bits (tnum_inverse_shift o) w
    (Tnum 0 (ones q)) b) as Hone.
  unfold tnum_project_variable, tnum_bits in *; cbn [zeros ones] in *; lia.
Qed.

(** Variable inverse shifts retain their projection bound through optional meet. *)
Lemma back_variable_bits : forall o w b q,
  (tnum_bits (tnum_back_variable_shift o w b q) <= 4 * Pos.to_nat w)%nat.
Proof.
  intros o w b q. destruct o; cbn [tnum_back_variable_shift];
    try apply back_project_variable_bits.
  eapply Nat.le_trans; [apply tnum_meet_bits|lia].
Qed.

(** Both inverse order bounds store masks at the first operand's width. *)
Lemma back_order_bits : forall strict w q a b,
  (tnum_bits (fst (tnum_order_back strict w q a b)) +
    tnum_bits (snd (tnum_order_back strict w q a b)) <= 4 * Pos.to_nat w)%nat.
Proof.
  intros strict w q a b. destruct strict;
    unfold tnum_order_back;
    destruct (Z.testbit (ones q) 0), (Z.testbit (zeros q) 0);
    cbn [fst snd].
  all: match goal with
  | |- (tnum_bits ?left + tnum_bits ?right <= _)%nat =>
    assert (Hleft : (tnum_bits left <= 2 * Pos.to_nat w)%nat) by
      first [apply tnum_upper_bits|apply back_lower_bits|apply tnum_top_bits];
    assert (Hright : (tnum_bits right <= 2 * Pos.to_nat w)%nat) by
      first [apply tnum_upper_bits|apply back_lower_bits|apply tnum_top_bits];
    lia
  end.
Qed.

(** Raw backward results add only bounded masks to any copied input masks. *)
Lemma back_raw_bits : forall o rw q (xs : list (width * tnum)),
  (fold_right Nat.add 0 (map tnum_bits (tnum_backward_raw o xs rw q)) <=
    fold_right Nat.add 0 (map (fun x => tnum_bits (snd x)) xs) +
    4 * fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs))%nat.
Proof.
  intros o rw q [|[w a] [|[v b] [|[u c] xs]]].
  - destruct o; cbn [tnum_backward_raw map fold_right]; lia.
  - destruct o; cbn [tnum_backward_raw map fold_right fst snd];
      rewrite ?Nat.add_0_r; try lia.
    all: match goal with
    | |- (tnum_bits ?result <= _)%nat =>
      assert (Hresult : (tnum_bits result <= 2 * Pos.to_nat w)%nat) by
        first [apply tnum_not_bits|apply back_project_bits|apply back_sext_bits];
      lia
    end.
  - destruct o; cbn [tnum_backward_raw map fold_right fst snd];
      rewrite ?Nat.add_0_r; try lia.
    all: try solve [match goal with
    | |- context [tnum_constant ?count_width ?amount] =>
      destruct (tnum_constant count_width amount);
      cbn [map fold_right]; rewrite ?Nat.add_0_r;
      match goal with
      | |- (tnum_bits ?result + _ <= _)%nat =>
        assert (Hresult : (tnum_bits result <= 4 * Pos.to_nat w)%nat) by
          first [apply back_variable_bits|
            eapply Nat.le_trans; [apply back_shift_bits|lia]];
        lia
      end
    end].
    all: try solve [destruct (Z.testbit (ones q) 0);
      cbn [map fold_right]; rewrite ?Nat.add_0_r; lia].
    all: try solve [match goal with
    | |- context [tnum_order_back ?strict ?width ?result ?left ?right] =>
      pose proof (back_order_bits strict width result left right); lia
    end].
    all: match goal with
    | |- (tnum_bits ?left + tnum_bits ?right <= _)%nat =>
      assert (Hleft : (tnum_bits left <= 2 * (Pos.to_nat w + Pos.to_nat v))%nat) by
        (eapply Nat.le_trans;
          [first [apply back_and_bits|apply back_or_bits|apply tnum_xor_bits|
            apply tnum_add_bits|apply tnum_sub_bits|apply back_project_bits]|lia]);
      assert (Hright : (tnum_bits right <= 2 * (Pos.to_nat w + Pos.to_nat v))%nat) by
        (eapply Nat.le_trans;
          [first [apply back_and_bits|apply back_or_bits|apply tnum_xor_bits|
            apply tnum_add_bits|apply tnum_sub_bits|apply back_project_bits]|lia]);
      lia
    end.
  - destruct o; cbn [tnum_backward_raw]; rewrite map_map; lia.
Qed.

(** Projection pays for two callbacks, two output masks and linear input reads. *)
Lemma back_project_time : forall sw rw f Tf q,
  (T_tnum_project sw rw f Tf q <=
    Tf (tnum_wrap rw (zeros q)) +
    T_tnum_wrap sw (f (tnum_wrap rw (zeros q))) +
    Tf (tnum_wrap rw (ones q)) +
    T_tnum_wrap sw (f (tnum_wrap rw (ones q))) +
    128 * N.of_nat (Pos.to_nat rw + tnum_bits q + 1))%N.
Proof.
  intros sw rw f Tf q.
  pose proof (tnum_wrap_time rw (zeros q)) as Hzero.
  pose proof (tnum_wrap_time rw (ones q)) as Hone.
  pose proof (tnum_zeros_time q) as Hz.
  pose proof (tnum_ones_projection_time q) as Ho.
  time_unfold T_tnum_project; cbn beta iota zeta.
  unfold tnum_bits. rewrite ?Nat2N.inj_add in *. lia.
Qed.

(** A common budget combines the two projected callbacks and the raw input reads. *)
Lemma back_project_time_budget : forall sw rw f Tf q k budget,
  (N.of_nat (Pos.to_nat rw + tnum_bits q + 1) <= budget)%N ->
  (forall x, is_word rw x ->
    (Tf x + T_tnum_wrap sw (f x) <= k * budget)%N) ->
  (T_tnum_project sw rw f Tf q <= (2 * k + 128) * budget)%N.
Proof.
  intros sw rw f Tf q k budget Hinput Hcallback.
  pose proof (back_project_time sw rw f Tf q) as Hproject.
  pose proof (Hcallback (tnum_wrap rw (zeros q))
    ltac:(rewrite tnum_wrap_agrees; apply wrap_is_word)) as Hzero.
  pose proof (Hcallback (tnum_wrap rw (ones q))
    ltac:(rewrite tnum_wrap_agrees; apply wrap_is_word)) as Hone.
  clear Hcallback.
  replace ((2 * k + 128) * budget)%N with
    (2 * (k * budget) + 128 * budget)%N by (clear; ring).
  lia.
Qed.

(** Copying normalized result masks between widths has a linear projection clock. *)
Lemma back_project_identity_time : forall sw rw Tf q,
  (forall x, (Tf x <= 16)%N) ->
  (T_tnum_project sw rw (fun x => x) Tf q <=
    512 * N.of_nat (Pos.to_nat sw + Pos.to_nat rw + tnum_bits q + 1))%N.
Proof.
  intros sw rw Tf q Hcallback.
  pose proof (back_project_time sw rw (fun x => x) Tf q) as Hproject.
  pose proof (Hcallback (tnum_wrap rw (zeros q))) as Hzero.
  pose proof (Hcallback (tnum_wrap rw (ones q))) as Hone.
  pose proof (tnum_wrap_bits rw (zeros q)) as Hzbits.
  pose proof (tnum_wrap_bits rw (ones q)) as Hobits.
  pose proof (tnum_wrap_time sw (tnum_wrap rw (zeros q))) as Hzwrap.
  pose proof (tnum_wrap_time sw (tnum_wrap rw (ones q))) as Howrap.
  cbn beta iota zeta in Hproject.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.

(** A bounded amount's stored bits pay for scalar projection and its output mask. *)
Lemma back_scalar_callback_time : forall o w k d x,
  (Z.size_nat k <= d)%nat -> is_word w x ->
  (64 + T_tnum_scalar_value o w k x +
    T_tnum_wrap w (tnum_scalar_value o w k x) <=
    32768 * N.of_nat ((Pos.to_nat w + d + 1) ^ 2))%N.
Proof.
  intros o w k d x Hk Hword.
  pose proof (tnum_word_bits w x Hword) as Hxbits.
  pose proof (tnum_word_bits w _ (tnum_scalar_word o w k x)) as Hresult.
  pose proof (tnum_positive_bits w) as Hwidth.
  pose proof (tnum_scalar_value_time o w k x) as Hscalar.
  pose proof (tnum_wrap_time w (tnum_scalar_value o w k x)) as Hwrap.
  assert (Hproduct : ((Z.size_nat k + 1) * (Pos.size_nat w + 1) <=
    (Pos.to_nat w + d + 1) ^ 2)%nat).
  { clear -Hk Hwidth. cbn [Nat.pow]. nia. }
  pose proof (time_of_nat_le _ _ Hproduct) as Hdivision.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + d + 1)
    (Pos.to_nat w + d + 1) ltac:(lia) ltac:(lia)) as Hlinear.
  rewrite ?Nat2N.inj_add in *.
  set (square := N.of_nat ((Pos.to_nat w + d + 1) ^ 2)) in *.
  clearbody square. lia.
Qed.

(** Scalar inverse projection keeps the raw result-mask charge linear. *)
Lemma back_project_scalar_time : forall o w k d Tf q,
  (Z.size_nat k <= d)%nat ->
  (forall x, (Tf x <= 64 + T_tnum_scalar_value o w k x)%N) ->
  (T_tnum_project w w (tnum_scalar_value o w k) Tf q <=
    131072 * N.of_nat ((Pos.to_nat w + d + 1) ^ 2 + tnum_bits q))%N.
Proof.
  intros o w k d Tf q Hk Hcallback.
  set (budget := N.of_nat ((Pos.to_nat w + d + 1) ^ 2 + tnum_bits q)).
  assert (Hsquare : (N.of_nat ((Pos.to_nat w + d + 1) ^ 2) <= budget)%N).
  { unfold budget. rewrite Nat2N.inj_add. lia. }
  assert (Hinput : (N.of_nat (Pos.to_nat w + tnum_bits q + 1) <= budget)%N).
  { clear -w d q budget.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1)
      (Pos.to_nat w + d + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  assert (Hproject : (T_tnum_project w w (tnum_scalar_value o w k) Tf q <=
    (2 * 32768 + 128) * budget)%N).
  { apply (back_project_time_budget w w (tnum_scalar_value o w k) Tf q 32768 budget);
      [exact Hinput|].
    intros x Hx. pose proof (Hcallback x) as Hcall.
    pose proof (back_scalar_callback_time o w k d x Hk Hx) as Hvalue.
    eapply N.le_trans; [|apply N.mul_le_mono_l; exact Hsquare]. lia. }
  fold budget. clearbody budget. lia.
Qed.

(** Splitting a concatenation shifts normalized result masks by one operand width. *)
Lemma back_project_shiftr_time : forall sw rw v Tf q,
  (forall x, is_word rw x ->
    (Tf x <= 64 + Std.Z.T_shiftr x (Zpos v))%N) ->
  (T_tnum_project sw rw (fun x => Z.shiftr x (Zpos v)) Tf q <=
    2048 * N.of_nat
      (Pos.to_nat sw + Pos.to_nat rw + Pos.to_nat v + tnum_bits q + 1))%N.
Proof.
  intros sw rw v Tf q Hcallback.
  assert (Hzword : is_word rw (tnum_wrap rw (zeros q))).
  { rewrite tnum_wrap_agrees. apply wrap_is_word. }
  assert (Howord : is_word rw (tnum_wrap rw (ones q))).
  { rewrite tnum_wrap_agrees. apply wrap_is_word. }
  pose proof (Hcallback _ Hzword) as Hzero.
  pose proof (Hcallback _ Howord) as Hone.
  pose proof (tnum_wrap_bits rw (zeros q)) as Hzbits.
  pose proof (tnum_wrap_bits rw (ones q)) as Hobits.
  pose proof (tnum_shiftr_bits _ (Zpos v) (proj1 Hzword) ltac:(lia)) as Hzshiftbits.
  pose proof (tnum_shiftr_bits _ (Zpos v) (proj1 Howord) ltac:(lia)) as Hoshiftbits.
  pose proof (tnum_shiftr_time _ (Zpos v) (proj1 Hzword) ltac:(lia)) as Hzshift.
  pose proof (tnum_shiftr_time _ (Zpos v) (proj1 Howord) ltac:(lia)) as Hoshift.
  pose proof (tnum_wrap_time sw (Z.shiftr (tnum_wrap rw (zeros q)) (Zpos v))) as Hzwrap.
  pose proof (tnum_wrap_time sw (Z.shiftr (tnum_wrap rw (ones q)) (Zpos v))) as Howrap.
  pose proof (back_project_time sw rw (fun x => Z.shiftr x (Zpos v)) Tf q) as Hproject.
  clear Hcallback Hzword Howord.
  cbn beta iota zeta in Hproject.
  change (Z.to_nat (Zpos v)) with (Pos.to_nat v) in *.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.

(** An accepted extraction offset bounds conversion, left shift and projection. *)
Lemma back_project_shiftl_time : forall sw rw lo Tf q,
  (lo < Pos.to_nat sw)%nat ->
  (forall x, is_word rw x ->
    (Tf x <= 64 + Op.Z.T_of_nat lo + Std.Z.T_shiftl x (Z.of_nat lo))%N) ->
  (T_tnum_project sw rw (fun x => Z.shiftl x (Z.of_nat lo)) Tf q <=
    4096 * N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2 + tnum_bits q))%N.
Proof.
  intros sw rw lo Tf q Hlo Hcallback.
  set (square := N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2)).
  set (budget := N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2 + tnum_bits q)).
  assert (Hsquare : (square <= budget)%N).
  { unfold square, budget. rewrite Nat2N.inj_add. lia. }
  assert (Hlinear : (N.of_nat (Pos.to_nat sw + Pos.to_nat rw + 1) <= square)%N).
  { unfold square. apply WordTime.time_square_floor; lia. }
  assert (Hinput : (N.of_nat (Pos.to_nat rw + tnum_bits q + 1) <= budget)%N).
  { unfold budget. rewrite ?Nat2N.inj_add in *. unfold square in *. lia. }
  assert (Hconvert : (Op.Z.T_of_nat lo <= 8 * square)%N).
  { unfold square. eapply WordTime.time_square_weaken;
      [apply WordTime.natural_to_integer_time_bound|lia]. }
  clearbody square budget.
  assert (Hproject : (T_tnum_project sw rw (fun x => Z.shiftl x (Z.of_nat lo)) Tf q <=
    (2 * 256 + 128) * budget)%N).
  { apply (back_project_time_budget sw rw (fun x => Z.shiftl x (Z.of_nat lo))
      Tf q 256 budget); [exact Hinput|].
    intros x Hword. pose proof (Hcallback x Hword) as Hcall.
    pose proof (tnum_word_bits rw x Hword) as Hbits.
    pose proof (tnum_shiftl_bits x (Z.of_nat lo) ltac:(lia)) as Hshiftbits.
    pose proof (tnum_shiftl_time x (Z.of_nat lo) ltac:(lia)) as Hshift.
    pose proof (tnum_wrap_time sw (Z.shiftl x (Z.of_nat lo))) as Hwrap.
    rewrite Nat2Z.id in Hshiftbits, Hshift.
    clear Hcallback Hword.
    rewrite ?Nat2N.inj_add in *. lia. }
  lia.
Qed.

(** Backward conjunction reads the result and the other operand once. *)
Lemma back_and_time : forall w q b,
  (T_tnum_and_back w q b <=
    512 * N.of_nat (Pos.to_nat w + tnum_bits q + tnum_bits b + 1))%N.
Proof.
  intros w q b. time_unfold T_tnum_and_back; time_cbn; time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound back_and_time.

(** Backward disjunction reads the result and the other operand once. *)
Lemma back_or_time : forall w q b,
  (T_tnum_or_back w q b <=
    512 * N.of_nat (Pos.to_nat w + tnum_bits q + tnum_bits b + 1))%N.
Proof.
  intros w q b. time_unfold T_tnum_or_back; time_cbn; time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound back_or_time.

(** A lower-bound mask constructs one bounded upper mask and negates it. *)
Lemma back_lower_time : forall w l,
  (T_tnum_lower w l <= 8192 * N.of_nat (Pos.to_nat w + Z.size_nat l + 1))%N.
Proof.
  intros w l.
  assert (Hword : is_word w (tnum_wnot w l)).
  { rewrite tnum_wnot_agrees. apply wnot_is_word. }
  pose proof (tnum_word_bits w _ Hword) as Hbits.
  pose proof (table_upper_time w (tnum_wnot w l) (proj1 Hword)) as Hupper.
  pose proof (tnum_upper_bits w (tnum_wnot w l)) as Hupperbits.
  pose proof (tnum_not_time w (tnum_upper w (tnum_wnot w l))) as Hnot.
  pose proof (tnum_wnot_time w l) as Hcomplement.
  time_unfold T_tnum_lower; cbn beta iota zeta.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound back_lower_time.

(** A negative upper endpoint has constant bit length and still fits a linear clock. *)
Lemma back_upper_time : forall w h,
  (T_tnum_upper w h <= 4096 * N.of_nat (Pos.to_nat w + Z.size_nat h + 1))%N.
Proof.
  intros w [|p|p].
  - pose proof (table_upper_time w 0 ltac:(lia)) as Htime. lia.
  - pose proof (table_upper_time w (Zpos p) ltac:(lia)) as Htime. lia.
  - pose proof (table_bitlen_time (Zneg p)) as Hlength.
    pose proof (tnum_ones_time 1 ltac:(lia)) as Hones.
    pose proof (tnum_wnot_time w (Z.ones 1)) as Hcomplement.
    time_unfold T_tnum_upper; cbn beta iota zeta.
    change (tnum_bitlen (Zneg p)) with 1 in *.
    change (Z.ones 1) with 1 in *.
    change (Z.to_nat 1) with 1%nat in *.
    change (Z.size_nat 1) with 1%nat in *.
    rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound back_upper_time.

(** A bounded nonnegative sign offset costs linear work in the two widths. *)
Lemma back_sign_time : forall sw rw n q, 0 <= n <= Zpos sw ->
  (T_tnum_sign_project sw rw n q <=
    512 * N.of_nat (Pos.to_nat sw + Pos.to_nat rw + tnum_bits q + 1))%N.
Proof.
  intros sw rw n q Hn.
  assert (Hcount : (Z.to_nat n <= Pos.to_nat sw)%nat).
  { change (Z.to_nat n <= Z.to_nat (Zpos sw))%nat. apply Z2Nat.inj_le; lia. }
  assert (Hzword : is_word rw (tnum_wrap rw (zeros q))).
  { rewrite tnum_wrap_agrees. apply wrap_is_word. }
  assert (Howord : is_word rw (tnum_wrap rw (ones q))).
  { rewrite tnum_wrap_agrees. apply wrap_is_word. }
  pose proof (tnum_wrap_bits rw (zeros q)) as Hzbits.
  pose proof (tnum_wrap_bits rw (ones q)) as Hobits.
  pose proof (tnum_shiftr_bits _ n (proj1 Hzword) (proj1 Hn)) as Hzshiftbits.
  pose proof (tnum_shiftr_bits _ n (proj1 Howord) (proj1 Hn)) as Hoshiftbits.
  pose proof (tnum_shiftr_time _ n (proj1 Hzword) (proj1 Hn)) as Hzshift.
  pose proof (tnum_shiftr_time _ n (proj1 Howord) (proj1 Hn)) as Hoshift.
  pose proof (Std.Z.T_eqb_le (Z.shiftr (tnum_wrap rw (zeros q)) n) 0) as Hzeq.
  pose proof (Std.Z.T_eqb_le (Z.shiftr (tnum_wrap rw (ones q)) n) 0) as Hoeq.
  pose proof (tnum_wrap_time rw (zeros q)) as Hzwrap.
  pose proof (tnum_wrap_time rw (ones q)) as Howrap.
  pose proof (WordTime.word_half_time_bound sw) as Hhalf.
  pose proof (tnum_zeros_time q) as Hz.
  pose proof (tnum_ones_projection_time q) as Ho.
  time_unfold T_tnum_sign_project; cbn beta iota zeta.
  destruct (Z.shiftr (tnum_wrap rw (zeros q)) n =? 0),
    (Z.shiftr (tnum_wrap rw (ones q)) n =? 0);
    cbn beta iota zeta;
    unfold tnum_bits in *; rewrite ?Nat2N.inj_add in *;
    try change (Z.size_nat 0) with 0%nat in *; lia.
Qed.

(** Inverse sign extension combines two linear projections and one bounded meet. *)
Lemma back_sext_time : forall sw rw q,
  (T_tnum_back_sext sw rw q <=
    8192 * N.of_nat (Pos.to_nat sw + Pos.to_nat rw + tnum_bits q + 1))%N.
Proof.
  intros sw rw q. set (n := Zpos sw - 1).
  assert (Hn : 0 <= n <= Zpos sw) by (unfold n; lia).
  pose proof (back_sign_time sw rw n q Hn) as Hsign.
  pose proof (back_project_bits sw rw (fun x => x) q) as Hprojectbits.
  pose proof (back_sign_bits sw rw n q) as Hsignbits.
  set (project := tnum_project sw rw (fun x => x) q) in *.
  set (sign := tnum_sign_project sw rw n q) in *.
  pose proof (tnum_meet_time sw project sign) as Hmeet.
  pose proof (Std.Z.T_sub_le (Zpos sw) 1) as Hsubtract.
  pose proof (tnum_positive_bits sw) as Hwidth.
  time_unfold T_tnum_back_sext; cbn beta iota zeta.
  match goal with
  | |- context [T_tnum_project _ _ _ ?Tf _] =>
    pose proof (back_project_identity_time sw rw Tf q
      ltac:(intros; cbn beta iota zeta; lia)) as Hproject
  end.
  fold n project sign. clearbody n project sign.
  change (Z.size_nat (Zpos sw)) with (Pos.size_nat sw) in *.
  try change (Z.size_nat 1) with 1%nat in *.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound back_sext_time.

(** Selecting the opposite shift or rotation inspects one operator constructor. *)
Lemma back_inverse_time : forall o, (T_tnum_inverse_shift o <= 16)%N.
Proof. intros o. destruct o; time_unfold T_tnum_inverse_shift; time_cbn; lia. Qed.
TimeBound back_inverse_time.

(** A recognized shift count pays through its width, with raw result masks linear. *)
Lemma back_shift_time : forall o w v k q, is_word v k ->
  (T_tnum_back_shift o w k q <= 524288 * N.of_nat
    ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits q))%N.
Proof.
  intros o w v k q Hword.
  pose proof (tnum_word_bits v k Hword) as Hkbits.
  set (t := Zpos w - 1).
  set (offset := t - k).
  set (n := Z.max 0 offset).
  assert (Hn : 0 <= n <= Zpos w).
  { unfold n, offset, t. split; [apply Z.le_max_l|apply Z.max_lub; destruct Hword; lia]. }
  pose proof (back_sign_time w w n q Hn) as Hsign.
  pose proof (back_sign_bits w w n q) as Hsignbits.
  set (inv := tnum_inverse_shift o).
  pose proof (back_project_bits w w (tnum_scalar_value inv w k) q) as Hprojectbits.
  set (project := tnum_project w w (tnum_scalar_value inv w k) q) in *.
  set (sign := tnum_sign_project w w n q) in *.
  pose proof (tnum_meet_time w project sign) as Hmeet.
  pose proof (back_inverse_time o) as Hinverse.
  pose proof (tnum_difference_bits (Zpos w) 1) as Htbits.
  pose proof (tnum_difference_bits t k) as Hoffsetbits.
  fold t in Htbits. fold offset in Hoffsetbits.
  pose proof (Std.Z.T_sub_le (Zpos w) 1) as Ht.
  pose proof (Std.Z.T_sub_le t k) as Hoffset.
  pose proof (Std.Z.T_max_le 0 offset) as Hmaximum.
  pose proof (tnum_positive_bits w) as Hwidth.
  set (budget := N.of_nat ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits q)).
  assert (Hlinear : (N.of_nat
    (Pos.to_nat w + Pos.to_nat v + tnum_bits q + 1) <= budget)%N).
  { clear -w v q budget.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + Pos.to_nat v + 1)
      (Pos.to_nat w + Pos.to_nat v + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  time_unfold T_tnum_back_shift; cbn beta iota zeta. fold inv.
  match goal with
  | |- context [T_tnum_project _ _ _ ?Tf _] =>
    pose proof (back_project_scalar_time inv w k (Pos.to_nat v) Tf q Hkbits
      ltac:(intros; cbn beta iota zeta; lia)) as Hproject
  end.
  fold t offset n project sign budget.
  fold budget in Hproject.
  clear Hword Hn. clearbody t offset n inv project sign budget.
  destruct o; cbn beta iota zeta;
    change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in *;
    try change (Z.size_nat 0) with 0%nat in *;
    try change (Z.size_nat 1) with 1%nat in *;
    rewrite ?Nat2N.inj_add in *; lia.
Qed.

(** Variable projection invokes the raw shift algorithm twice with linear raw-mask charges. *)
Lemma back_project_variable_time : forall o w b q,
  (T_tnum_project_variable o w b q <= 67108864 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + tnum_bits b + tnum_bits q))%N.
Proof.
  intros o w b q. set (inv := tnum_inverse_shift o).
  pose proof (tnum_variable_raw_general_time inv w (Tnum 0 (zeros q)) b) as Hzero.
  pose proof (tnum_variable_raw_general_time inv w (Tnum 0 (ones q)) b) as Hone.
  pose proof (WordTime.time_square_floor 1 (Pos.to_nat w + 1)
    ltac:(lia) ltac:(lia)) as Hpositive.
  time_unfold T_tnum_project_variable; cbn beta iota zeta. fold inv.
  time_pose. unfold tnum_bits in *; cbn [zeros ones] in *.
  try change (Z.size_nat 0) with 0%nat in *.
  rewrite ?Nat2N.inj_add in *.
  set (square := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  clearbody inv square.
  try change (N.of_nat 1) with 1%N in *.
  lia.
Qed.
TimeBound back_project_variable_time.

(** Variable inverse shifting adds one width-bounded sign projection when necessary. *)
Lemma back_variable_time : forall o w b q,
  (T_tnum_back_variable_shift o w b q <= 134217728 * N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + tnum_bits b + tnum_bits q))%N.
Proof.
  intros o w b q.
  pose proof (tnum_min_word w b) as Hminimum.
  pose proof (tnum_min_bits w b) as Hminbits.
  pose proof (tnum_min_time w b) as Hmin.
  set (minimum := tnum_min w b) in *.
  set (t := Zpos w - 1).
  set (offset := t - minimum).
  set (n := Z.max 0 offset).
  assert (Hn : 0 <= n <= Zpos w).
  { unfold n, offset, t. split;
      [apply Z.le_max_l|apply Z.max_lub; destruct Hminimum; lia]. }
  pose proof (back_sign_time w w n q Hn) as Hsign.
  pose proof (back_sign_bits w w n q) as Hsignbits.
  pose proof (back_project_variable_time o w b q) as Hproject.
  pose proof (back_project_variable_bits o w b q) as Hprojectbits.
  set (project := tnum_project_variable o w b q) in *.
  set (sign := tnum_sign_project w w n q) in *.
  pose proof (tnum_meet_time w project sign) as Hmeet.
  pose proof (tnum_difference_bits (Zpos w) 1) as Htbits.
  pose proof (tnum_difference_bits t minimum) as Hoffsetbits.
  fold t in Htbits. fold offset in Hoffsetbits.
  pose proof (Std.Z.T_sub_le (Zpos w) 1) as Ht.
  pose proof (Std.Z.T_sub_le t minimum) as Hoffset.
  pose proof (Std.Z.T_max_le 0 offset) as Hmaximum.
  pose proof (tnum_positive_bits w) as Hwidth.
  set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits b + tnum_bits q)).
  assert (Hlinear : (N.of_nat
    (Pos.to_nat w + tnum_bits b + tnum_bits q + 1) <= budget)%N).
  { clear -w b q budget.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + 1)
      (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  time_unfold T_tnum_back_variable_shift; cbn beta iota zeta.
  fold minimum t offset n project sign budget.
  fold budget in Hproject.
  clear Hminimum Hn. clearbody minimum t offset n project sign budget.
  destruct o; cbn beta iota zeta; unfold tnum_bits in *;
    change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in *;
    try change (Z.size_nat 0) with 0%nat in *;
    try change (Z.size_nat 1) with 1%nat in *;
    rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound back_variable_time.

(** Inverse order bounds inspect four endpoints and construct two linear masks. *)
Lemma back_order_time : forall strict w q a b,
  (T_tnum_order_back strict w q a b <= 65536 * N.of_nat
    (Pos.to_nat w + tnum_bits q + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros strict w q a b.
  set (d := if strict then 1 else 0).
  set (e := 1 - d).
  assert (Hdbits : (Z.size_nat d <= 1)%nat).
  { unfold d; destruct strict.
    - change (1 <= 1)%nat; lia.
    - change (0 <= 1)%nat; lia. }
  assert (Hebits : (Z.size_nat e <= 1)%nat).
  { unfold e, d; destruct strict.
    - change (0 <= 1)%nat; lia.
    - change (1 <= 1)%nat; lia. }
  pose proof (tnum_min_bits w a) as Hminabits.
  pose proof (tnum_max_bits w a) as Hmaxabits.
  pose proof (tnum_min_bits w b) as Hminbbits.
  pose proof (tnum_max_bits w b) as Hmaxbbits.
  pose proof (tnum_sum_bits (tnum_min w a) d) as Hl1bits.
  pose proof (tnum_difference_bits (tnum_max w b) d) as Hu1bits.
  pose proof (tnum_sum_bits (tnum_min w b) e) as Hl2bits.
  pose proof (tnum_difference_bits (tnum_max w a) e) as Hu2bits.
  set (l1 := tnum_min w a + d) in *.
  set (u1 := tnum_max w b - d) in *.
  set (l2 := tnum_min w b + e) in *.
  set (u2 := tnum_max w a - e) in *.
  pose proof (back_lower_time w l1) as Hl1.
  pose proof (back_upper_time w u1) as Hu1.
  pose proof (back_lower_time w l2) as Hl2.
  pose proof (back_upper_time w u2) as Hu2.
  pose proof (tnum_min_time w a) as Hmina.
  pose proof (tnum_max_time w a) as Hmaxa.
  pose proof (tnum_min_time w b) as Hminb.
  pose proof (tnum_max_time w b) as Hmaxb.
  pose proof (Std.Z.T_add_le (tnum_min w a) d) as Hsum1.
  pose proof (Std.Z.T_sub_le (tnum_max w b) d) as Hsub1.
  pose proof (Std.Z.T_add_le (tnum_min w b) e) as Hsum2.
  pose proof (Std.Z.T_sub_le (tnum_max w a) e) as Hsub2.
  pose proof (Std.Z.T_sub_le 1 d) as Hdifference.
  pose proof (tnum_testbit_time (ones q) 0) as Htestone.
  pose proof (tnum_testbit_time (zeros q) 0) as Htestzero.
  pose proof (tnum_zeros_time q) as Hz.
  pose proof (tnum_ones_projection_time q) as Ho.
  time_unfold T_tnum_order_back; cbn beta iota zeta.
  fold d e l1 u1 l2 u2. clearbody d e l1 u1 l2 u2.
  destruct strict; destruct (Z.testbit (ones q) 0), (Z.testbit (zeros q) 0);
    cbn beta iota zeta; unfold tnum_bits in *;
    try change (Z.size_nat 0) with 0%nat in *;
    try change (Z.size_nat 1) with 1%nat in *;
    rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound back_order_time.

(** Refinement scans each operand once and pays for the masks that it meets. *)
Lemma back_refine_time : forall (xs : list (width * tnum)) qs,
  (T_tnum_refine xs qs <= 512 * N.of_nat
    (length xs + fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) +
      fold_right Nat.add 0%nat (map (fun x => tnum_bits (snd x)) xs) +
      fold_right Nat.add 0%nat (map tnum_bits qs) + 1))%N.
Proof.
  induction xs as [|[w a] xs IH]; intros [|q qs].
  - time_unfold T_tnum_refine; time_cbn. lia.
  - time_unfold T_tnum_refine; time_cbn.
    cbn [length map fold_right fst snd]. rewrite ?Nat2N.inj_add. lia.
  - specialize (IH []). time_unfold T_tnum_refine; time_cbn.
    cbn [length map fold_right fst snd] in *.
    rewrite ?Nat2N.inj_succ, ?Nat2N.inj_add in *. lia.
  - specialize (IH qs). pose proof (tnum_meet_time w a q) as Hmeet.
    time_unfold T_tnum_refine; time_cbn.
    cbn [length map fold_right fst snd] in *.
    rewrite ?Nat2N.inj_succ, ?Nat2N.inj_add in *. lia.
Qed.

(** Copying the payload projection has linear list cost. *)
Lemma back_copy_time : forall (xs : list (width * tnum)),
  (ListDef.T_map (@snd width tnum)
    (fun x => @Datatypes.T_snd width tnum x) xs <=
    4 * N.of_nat (length xs + 1))%N.
Proof.
  intro xs. pose proof (ListDef.T_map_le (@snd width tnum)
    (fun x => @Datatypes.T_snd width tnum x) 1 xs
    ltac:(intros [w a]; time_step)) as Hmap.
  rewrite Nat2N.inj_add. lia.
Qed.

(** The arity table inspects one constructor and ignores its numeric metadata. *)
Lemma back_arity_time : forall o, (Op.T_arity o <= 16)%N.
Proof. intro o. destruct o; time_unfold Op.T_arity; time_cbn; lia. Qed.
TimeBound back_arity_time.

(** Every operand contributes at least one unit to the sum of widths. *)
Lemma back_operand_count : forall (xs : list (width * tnum)),
  (length xs <= fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs))%nat.
Proof.
  induction xs as [|[w a] xs IH]; cbn [length map fold_right fst]; [lia|].
  pose proof (Pos2Nat.is_pos w). lia.
Qed.

(** Unary backward dispatch uses one bounded projection or a linear mask transfer. *)
Lemma back_raw_one_time : forall o rw w a q,
  tnum_table_bounded o [(w, a)] = true ->
  (T_tnum_backward_raw o [(w, a)] rw q <= 1048576 * N.of_nat
    ((Pos.to_nat rw + Pos.to_nat w + 1) ^ 2 + tnum_bits q + tnum_bits a))%N.
Proof.
  intros o rw w a q Hguard.
  set (budget := N.of_nat
    ((Pos.to_nat rw + Pos.to_nat w + 1) ^ 2 + tnum_bits q + tnum_bits a)).
  assert (Hlinear : (N.of_nat
    (Pos.to_nat w + Pos.to_nat rw + tnum_bits q + tnum_bits a + 1) <= budget)%N).
  { clear -w rw a q budget.
    pose proof (WordTime.time_square_floor (Pos.to_nat w + Pos.to_nat rw + 1)
      (Pos.to_nat rw + Pos.to_nat w + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  assert (Hsquare : (N.of_nat
    ((Pos.to_nat w + Pos.to_nat rw + 1) ^ 2 + tnum_bits q) <= budget)%N).
  { unfold budget. replace (Pos.to_nat w + Pos.to_nat rw + 1)%nat with
      (Pos.to_nat rw + Pos.to_nat w + 1)%nat by lia.
    rewrite ?Nat2N.inj_add. lia. }
  assert (Hpositive : (1 <= budget)%N).
  { rewrite ?Nat2N.inj_add in Hlinear. lia. }
  pose proof (tnum_not_time w q) as Hnot.
  pose proof (back_sext_time w rw q) as Hsext.
  pose proof (back_copy_time [(w, a)]) as Hcopy.
  (* Share the normalized callback spelling with the generated dispatch clock. *)
  revert Hcopy. time_simpl. intro Hcopy.
  cbn [length] in Hcopy. clearbody budget.
  destruct o; time_unfold T_tnum_backward_raw; cbn beta iota zeta;
    try solve [time_simpl; rewrite ?Nat2N.inj_add in *; lia].
  all: match goal with
  | |- context [T_tnum_project ?sw ?dw ?f ?Tf ?input] =>
    first
    [ pose proof (back_project_identity_time sw dw Tf input
        ltac:(intros; cbn beta iota zeta; lia)) as Hproject;
      time_simpl; rewrite ?Nat2N.inj_add in *; lia
    | match f with
      | (fun x => Z.shiftl x (Z.of_nat ?offset)) =>
        assert (Hoffset : (offset < Pos.to_nat sw)%nat) by
          (cbn [tnum_table_bounded] in Hguard; apply Nat.ltb_lt; exact Hguard);
        pose proof (back_project_shiftl_time sw dw offset Tf input Hoffset
          ltac:(intros; cbn beta iota zeta; lia)) as Hproject;
        assert (Hwide : (T_tnum_project sw dw f Tf input <= 4096 * budget)%N) by
          (eapply N.le_trans; [exact Hproject|]; apply N.mul_le_mono_l; exact Hsquare);
        time_simpl; lia
      end ]
  end.
Qed.

(** Recognizing a shift count pays once before choosing one inverse-transfer algorithm. *)
Lemma back_counted_shift_time : forall o w v b q,
  (T_tnum_constant v b +
    match tnum_constant v b with
    | Some k => T_tnum_back_shift o w k q
    | None => T_tnum_back_variable_shift o w b q
    end <= 201326592 * N.of_nat
      ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits q + tnum_bits b))%N.
Proof.
  intros o w v b q.
  set (budget := N.of_nat
    ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits q + tnum_bits b)).
  assert (Hlinear : (N.of_nat (Pos.to_nat v + tnum_bits b + 1) <= budget)%N).
  { clear -w v b q budget.
    pose proof (WordTime.time_square_floor (Pos.to_nat v + 1)
      (Pos.to_nat w + Pos.to_nat v + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  assert (Hscalar : (N.of_nat
    ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits q) <= budget)%N).
  { unfold budget. rewrite ?Nat2N.inj_add. lia. }
  assert (Hvariable : (N.of_nat
    ((Pos.to_nat w + 1) ^ 2 + tnum_bits b + tnum_bits q) <= budget)%N).
  { unfold budget. apply time_of_nat_le. clear -w v b q. cbn [Nat.pow]. nia. }
  pose proof (tnum_constant_time v b) as Hconstant_time.
  assert (Hvariable_time :
    (T_tnum_back_variable_shift o w b q <= 134217728 * budget)%N).
  { eapply N.le_trans; [apply back_variable_time|].
    apply N.mul_le_mono_l. exact Hvariable. }
  clearbody budget.
  destruct (tnum_constant v b) as [k|] eqn:Hconstant; cbn beta iota zeta.
  - assert (Hword : is_word v k).
    { eapply tnum_constant_result_word. exact Hconstant. }
    assert (Hscalar_time : (T_tnum_back_shift o w k q <= 524288 * budget)%N).
    { eapply N.le_trans; [apply (back_shift_time o w v k q Hword)|].
      apply N.mul_le_mono_l. exact Hscalar. }
    lia.
  - lia.
Qed.

(** Two-operand dispatch charges one quadratic width budget and linear raw mask sizes. *)
Lemma back_raw_two_time : forall o rw w v a b q,
  (T_tnum_backward_raw o [(w, a); (v, b)] rw q <= 268435456 * N.of_nat
    ((Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v + 1) ^ 2 +
      tnum_bits q + tnum_bits a + tnum_bits b))%N.
Proof.
  intros o rw w v a b q.
  set (budget := N.of_nat
    ((Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v + 1) ^ 2 +
      tnum_bits q + tnum_bits a + tnum_bits b)).
  assert (Hlinear : (N.of_nat
    (Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v +
      tnum_bits q + tnum_bits a + tnum_bits b + 1) <= budget)%N).
  { clear -rw w v a b q budget.
    pose proof (WordTime.time_square_floor
      (Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v + 1)
      (Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  assert (Hshift_input : (N.of_nat
    ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits q + tnum_bits b) <= budget)%N).
  { unfold budget. apply time_of_nat_le.
    clear -rw w v a b q. cbn [Nat.pow]. nia. }
  assert (Hshift : (T_tnum_constant v b +
    match tnum_constant v b with
    | Some k => T_tnum_back_shift o w k q
    | None => T_tnum_back_variable_shift o w b q
    end <= 201326592 * budget)%N).
  { eapply N.le_trans; [apply back_counted_shift_time|].
    apply N.mul_le_mono_l. exact Hshift_input. }
  assert (Hpositive : (1 <= budget)%N).
  { rewrite ?Nat2N.inj_add in Hlinear. lia. }
  pose proof (back_copy_time [(w, a); (v, b)]) as Hcopy.
  revert Hcopy. time_simpl. intro Hcopy.
  pose proof (tnum_testbit_time (ones q) 0) as Htest.
  cbn [length] in Hcopy.
  change (Z.size_nat 0) with 0%nat in Htest.
  clear Hshift_input. clearbody budget.
  destruct o; time_unfold T_tnum_backward_raw; cbn beta iota zeta;
    try solve [time_simpl; time_pose; unfold tnum_bits in *;
      rewrite ?Nat2N.inj_add in *; lia].
  all: try match goal with
  | |- context [tnum_constant ?count_width ?amount] =>
    destruct (tnum_constant count_width amount) as [k|] eqn:Hconstant;
      try rewrite Hconstant in Hshift;
      cbn beta iota zeta in Hshift;
      time_simpl; lia
  end.
  all: try match goal with
  | |- context [Z.testbit (ones ?result) 0] =>
    destruct (Z.testbit (ones result) 0);
      time_simpl; unfold tnum_bits in *; rewrite ?Nat2N.inj_add in *; lia
  end.
  all: match goal with
  | |- context [T_tnum_project ?sw ?dw
      (fun m => Z.shiftr m (Zpos ?amount_width)) ?Tf ?result] =>
    pose proof (back_project_shiftr_time sw dw amount_width Tf result
      ltac:(intros; cbn beta iota zeta; lia)) as Hhigh
  end.
  all: match goal with
  | |- context [T_tnum_project ?sw ?dw (fun m => m) ?Tf ?result] =>
    pose proof (back_project_identity_time sw dw Tf result
      ltac:(intros; cbn beta iota zeta; lia)) as Hlow
  end.
  all: time_simpl; rewrite ?Nat2N.inj_add in *; lia.
Qed.

(** Every list shape pays at most the binary transfer budget or a linear projection copy. *)
Lemma back_raw_time : forall o rw q (xs : list (width * tnum)),
  tnum_table_bounded o xs = true ->
  (T_tnum_backward_raw o xs rw q <= 536870912 * N.of_nat
    ((Pos.to_nat rw + fold_right Nat.add 0%nat
      (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 + tnum_bits q +
      fold_right Nat.add 0%nat (map (fun x => tnum_bits (snd x)) xs)))%N.
Proof.
  intros o rw q xs Hguard.
  pose proof (back_operand_count xs) as Hcount.
  pose proof (back_copy_time xs) as Hcopy.
  set (widths := fold_right Nat.add 0%nat
    (map (fun x => Pos.to_nat (fst x)) xs)) in *.
  set (bits := fold_right Nat.add 0%nat
    (map (fun x => tnum_bits (snd x)) xs)) in *.
  set (budget := N.of_nat ((Pos.to_nat rw + widths + 1) ^ 2 + tnum_bits q + bits)).
  assert (Hlinear : (N.of_nat (length xs + 1) <= budget)%N).
  { pose proof (WordTime.time_square_floor (length xs + 1)
      (Pos.to_nat rw + widths + 1) ltac:(lia) ltac:(lia)).
    unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
  assert (Hpositive : (1 <= budget)%N).
  { rewrite Nat2N.inj_add in Hlinear. lia. }
  assert (Hcopywide :
    (ListDef.T_map (@snd width tnum)
      (fun x => @Datatypes.T_snd width tnum x) xs <= 4 * budget)%N) by lia.
  revert Hcopywide. time_simpl. intro Hcopywide.
  clear Hcount Hcopy Hlinear.
  destruct xs as [|[w a] [|[v b] [|x xs]]].
  - clearbody budget. destruct o;
      time_unfold T_tnum_backward_raw; cbn beta iota zeta; time_simpl; lia.
  - pose proof (back_raw_one_time o rw w a q Hguard) as Hraw.
    assert (Hshape : (N.of_nat
      ((Pos.to_nat rw + Pos.to_nat w + 1) ^ 2 + tnum_bits q + tnum_bits a) = budget)%N).
    { unfold budget, widths, bits. cbn [map fold_right fst snd].
      now rewrite !Nat.add_0_r. }
    rewrite Hshape in Hraw. clearbody budget. lia.
  - pose proof (back_raw_two_time o rw w v a b q) as Hraw.
    assert (Hshape : (N.of_nat
      ((Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v + 1) ^ 2 +
        tnum_bits q + tnum_bits a + tnum_bits b) = budget)%N).
    { unfold budget, widths, bits. cbn [map fold_right fst snd].
      now rewrite !Nat.add_0_r, !Nat.add_assoc. }
    rewrite Hshape in Hraw. clearbody budget. lia.
  - clearbody widths bits budget. destruct o;
      time_unfold T_tnum_backward_raw; cbn beta iota zeta; time_simpl; lia.
Qed.

Module KnownBitsTableClock (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) (K : KNOWN_BITS_T L C).
  Include KnownBitsTable L C K.
  TimeFun tnum_forward_raw.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_word_table : N := K.c_tnum + 1073741824.

  (** The shared constant preserves each previously proved unscaled storage bound. *)
  Lemma word_table_scale : forall n, (n <= c_word_table * n)%N.
  Proof.
    intro n. rewrite <- (N.mul_1_l n) at 1.
    apply N.mul_le_mono_r. unfold c_word_table. lia.
  Qed.
  Module ForwardClock := KnownBitsForwardClockProof L C K.

  (** Every operand contributes at least one bit of width. *)
  Local Lemma operand_count_width : forall (xs : list (positive * K.p)),
    (length xs <= fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs))%nat.
  Proof.
    induction xs as [|[w a] xs IH]; cbn [length map fold_right fst]; [lia|].
    pose proof (Pos2Nat.is_pos w). lia.
  Qed.

  (** Stored payload size includes every raw mask bit in the operand list. *)
  Local Lemma operand_bits_size : forall (xs : list (positive * K.p)),
    (fold_right Nat.add 0 (map (fun x => tnum_bits (snd x)) xs) <=
      fold_right Nat.add 0 (map (fun x => K.psize (fst x) (snd x)) xs))%nat.
  Proof.
    induction xs as [|[w a] xs IH]; cbn [map fold_right fst snd]; [lia|].
    rewrite K.psize_bits. lia.
  Qed.

  (** The two generated forward companions are definitionally the same clock. *)
  Local Lemma forward_clock_agrees : forall o xs rw,
    T_tnum_forward_raw o xs rw = ForwardClock.Raw.T_tnum_forward_raw o xs rw.
  Proof. intros. reflexivity. Qed.

  (** The accepted guard supplies the sole offset premise of raw forward timing. *)
  Local Lemma forward_raw_budget : forall o rw xs,
    tnum_table_bounded o xs = true ->
    (T_tnum_forward_raw o xs rw <= (K.c_tnum + 1048576) * N.of_nat
      ((Pos.to_nat rw + fold_right Nat.add 0%nat
        (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0%nat (map (fun x => tnum_bits (snd x)) xs)))%N.
  Proof.
    intros o rw xs Hguard. rewrite forward_clock_agrees.
    apply ForwardClock.forward_raw_time.
    intros hi lo w a Hop Hxs. subst o xs.
    cbn [tnum_table_bounded] in Hguard. now apply Nat.ltb_lt in Hguard.
  Qed.

  (** Table dispatch adds a linear arity check and bounded guard to the raw clock. *)
  Lemma forward_time_budget : forall o rw (xs : list (positive * K.p)),
    (T_wfwd o rw xs <= (K.c_tnum + 2097152) * N.of_nat
      ((Pos.to_nat rw + fold_right Nat.add 0%nat
        (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0%nat (map (fun x => K.psize (fst x) (snd x)) xs)))%N.
  Proof.
    intros o rw xs.
    pose proof (operand_count_width xs) as Hcount.
    pose proof (operand_bits_size xs) as Hbits.
    set (widths := fold_right Nat.add 0%nat
      (map (fun x => Pos.to_nat (fst x)) xs)) in *.
    set (bits := fold_right Nat.add 0%nat
      (map (fun x => tnum_bits (snd x)) xs)) in *.
    set (sizes := fold_right Nat.add 0%nat
      (map (fun x => K.psize (fst x) (snd x)) xs)) in *.
    set (budget := N.of_nat ((Pos.to_nat rw + widths + 1) ^ 2 + sizes)).
    assert (Hlinear : (N.of_nat (widths + 1) <= budget)%N).
    { pose proof (WordTime.time_square_floor (widths + 1)
        (Pos.to_nat rw + widths + 1) ltac:(lia) ltac:(lia)).
      unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
    assert (Hrawsize :
      (N.of_nat ((Pos.to_nat rw + widths + 1) ^ 2 + bits) <= budget)%N).
    { unfold budget. apply time_of_nat_le. lia. }
    assert (Hpositive : (1 <= budget)%N).
    { rewrite ?Nat2N.inj_add in Hlinear. lia. }
    assert (HcountN : (N.of_nat (length xs) <= N.of_nat widths)%N).
    { apply time_of_nat_le. exact Hcount. }
    assert (Hlength : (Datatypes.T_length xs <= budget)%N).
    { pose proof (Datatypes.T_length_le xs). rewrite ?Nat2N.inj_add in Hlinear. lia. }
    assert (Heqb : (Nat.T_eqb (length xs) (arity o) <= budget)%N).
    { pose proof (Nat.T_eqb_le (length xs) (arity o)).
      rewrite ?Nat2N.inj_add in Hlinear. lia. }
    assert (Hguardtime : (T_tnum_table_bounded o xs <= 16 * budget)%N).
    { pose proof (tnum_table_bounded_time o xs) as Hguard.
      fold widths in Hguard. eapply N.le_trans; [exact Hguard|].
      apply N.mul_le_mono_l. exact Hlinear. }
    pose proof (back_arity_time o) as Harity.
    time_unfold T_wfwd; cbn beta iota zeta.
    destruct (Nat.eqb (length xs) (arity o)); cbn beta iota zeta.
    - destruct (tnum_table_bounded o xs) eqn:Hguard; cbn beta iota zeta.
      + pose proof (forward_raw_budget o rw xs Hguard) as Hraw.
        fold widths bits in Hraw.
        assert (Hrawwide :
          (T_tnum_forward_raw o xs rw <= (K.c_tnum + 1048576) * budget)%N).
        { eapply N.le_trans; [exact Hraw|]. apply N.mul_le_mono_l. exact Hrawsize. }
        clearbody budget. rewrite !N.mul_add_distr_r in Hrawwide |- *. lia.
      + clearbody budget. rewrite N.mul_add_distr_r. lia.
    - clearbody budget. rewrite N.mul_add_distr_r. lia.
  Qed.

  (** Backward dispatch pays for one raw transfer and one bounded refinement scan. *)
  Lemma backward_time_budget : forall o rw q (xs : list (positive * K.p)),
    (T_wbwd o rw q xs <= 805306368 * N.of_nat
      ((Pos.to_nat rw + fold_right Nat.add 0%nat
        (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 + K.psize rw q +
        fold_right Nat.add 0%nat (map (fun x => K.psize (fst x) (snd x)) xs)))%N.
  Proof.
    intros o rw q xs.
    pose proof (operand_count_width xs) as Hcount.
    pose proof (operand_bits_size xs) as Hbits.
    pose proof (back_raw_bits o rw q xs) as Hresultbits.
    assert (Hqbits : (tnum_bits q <= K.psize rw q)%nat).
    { rewrite K.psize_bits. lia. }
    set (widths := fold_right Nat.add 0%nat
      (map (fun x => Pos.to_nat (fst x)) xs)) in *.
    set (bits := fold_right Nat.add 0%nat
      (map (fun x => tnum_bits (snd x)) xs)) in *.
    set (sizes := fold_right Nat.add 0%nat
      (map (fun x => K.psize (fst x) (snd x)) xs)) in *.
    set (raw := tnum_backward_raw o xs rw q) in *.
    set (rawbits := fold_right Nat.add 0%nat (map tnum_bits raw)) in *.
    change (length xs <= widths)%nat in Hcount.
    change (bits <= sizes)%nat in Hbits.
    change (rawbits <= bits + 4 * widths)%nat in Hresultbits.
    set (budget := N.of_nat ((Pos.to_nat rw + widths + 1) ^ 2 + K.psize rw q + sizes)).
    assert (Hlinear : (N.of_nat (widths + sizes + 1) <= budget)%N).
    { pose proof (WordTime.time_square_floor (widths + 1)
        (Pos.to_nat rw + widths + 1) ltac:(lia) ltac:(lia)).
      unfold budget. rewrite ?Nat2N.inj_add in *. lia. }
    assert (Hrawsize :
      (N.of_nat ((Pos.to_nat rw + widths + 1) ^ 2 + tnum_bits q + bits) <= budget)%N).
    { unfold budget. apply time_of_nat_le. lia. }
    assert (Hpositive : (1 <= budget)%N).
    { rewrite ?Nat2N.inj_add in Hlinear. lia. }
    clearbody budget.
    assert (HcountN : (N.of_nat (length xs) <= N.of_nat widths)%N).
    { apply time_of_nat_le. exact Hcount. }
    assert (Hlength : (Datatypes.T_length xs <= budget)%N).
    { pose proof (Datatypes.T_length_le xs). rewrite ?Nat2N.inj_add in Hlinear. lia. }
    assert (Heqb : (Nat.T_eqb (length xs) (arity o) <= budget)%N).
    { pose proof (Nat.T_eqb_le (length xs) (arity o)).
      rewrite ?Nat2N.inj_add in Hlinear. lia. }
    assert (Hguardtime : (T_tnum_table_bounded o xs <= 16 * budget)%N).
    { pose proof (tnum_table_bounded_time o xs) as Hguard.
      change (T_tnum_table_bounded o xs <= 16 * N.of_nat (widths + 1))%N in Hguard.
      eapply N.le_trans; [exact Hguard|].
      apply N.mul_le_mono_l.
      eapply N.le_trans; [|exact Hlinear]. apply time_of_nat_le.
      change (widths + 1 <= widths + sizes + 1)%nat. lia. }
    assert (Hrefine : (T_tnum_refine xs raw <= 8192 * budget)%N).
    { pose proof (back_refine_time xs raw) as Htime.
      change (T_tnum_refine xs raw <= 512 * N.of_nat
        (length xs + widths + bits + rawbits + 1))%N in Htime.
      assert (Hinput :
        (length xs + widths + bits + rawbits + 1 <= 8 * (widths + sizes + 1))%nat).
      { clearbody widths bits sizes rawbits. lia. }
      apply time_of_nat_le in Hinput.
      rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add in Hinput, Htime, Hlinear.
      try change (N.of_nat 8) with 8%N in Hinput. lia. }
    pose proof (back_arity_time o) as Harity.
    time_unfold T_wbwd; cbn beta iota zeta. fold raw.
    destruct (Nat.eqb (length xs) (arity o)); cbn beta iota zeta.
    - destruct (tnum_table_bounded o xs) eqn:Hguard; cbn beta iota zeta.
      + pose proof (back_raw_time o rw q xs Hguard) as Hraw.
        change (T_tnum_backward_raw o xs rw q <= 536870912 * N.of_nat
          ((Pos.to_nat rw + widths + 1) ^ 2 + tnum_bits q + bits))%N in Hraw.
        assert (Hrawwide : (T_tnum_backward_raw o xs rw q <= 536870912 * budget)%N).
        { eapply N.le_trans; [exact Hraw|]. apply N.mul_le_mono_l. exact Hrawsize. }
        lia.
      + lia.
    - lia.
  Qed.

  (** Refinement adds at most two normalized masks per operand width. *)
  Local Lemma refine_storage : forall (xs : list (positive * K.p)) (qs : list tnum),
    (fold_right Nat.add 0
      (map (fun wy => K.psize (fst wy) (snd wy))
        (combine (map fst xs) (tnum_refine xs qs))) <=
      fold_right Nat.add 0 (map (fun x => K.psize (fst x) (snd x)) xs) +
      2 * fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs))%nat.
  Proof.
    induction xs as [|[w a] xs IH]; intros [|q qs];
      rewrite tnum_refine_equation; cbn [map combine fold_right fst snd]; try lia.
    - specialize (IH []). lia.
    - specialize (IH qs). pose proof (tnum_meet_bits w a q) as Hbits.
      rewrite (K.psize_bits w (tnum_meet w a q)), (K.psize_bits w a). lia.
  Qed.
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        K.psize rw q + fold_right Nat.add 0 (map (fun x => K.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs. eapply N.le_trans; [apply backward_time_budget|].
    apply N.mul_le_mono_r. unfold c_word_table. lia.
  Qed.
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => K.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
        (((Pos.to_nat rw + fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
          K.psize rw q + fold_right Nat.add 0
            (map (fun x => K.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs ys Hback. unfold wbwd in Hback.
    destruct (Nat.eqb (length xs) (arity o)); [|discriminate].
    destruct (tnum_table_bounded o xs); [|discriminate].
    injection Hback as <-.
    eapply N.le_trans; [|apply word_table_scale].
    rewrite <- N.compare_le_iff, <- Nat2N.inj_compare, Nat.compare_le_iff.
    rewrite tnum_refine_length.
    pose proof (refine_storage xs (tnum_backward_raw o xs rw q)) as Hstorage.
    pose proof (operand_count_width xs) as Hlength.
    pose proof (Pos2Nat.is_pos rw) as Hwidth.
    set (widths := fold_right Nat.add 0%nat (map (fun x : positive * K.p =>
      Pos.to_nat (fst x)) xs)) in *.
    assert (Hsquare : (3 * widths <= (Pos.to_nat rw + widths + 1) ^ 2)%nat).
    { assert (Hsmall : (3 * widths <= (widths + 2) ^ 2)%nat).
      { cbn [Nat.pow]. nia. }
      assert (Hlarge : ((widths + 2) ^ 2 <= (Pos.to_nat rw + widths + 1) ^ 2)%nat).
      { apply Nat.pow_le_mono_l. lia. }
      lia. }
    set (inputs := fold_right Nat.add 0%nat
      (map (fun x : positive * K.p => K.psize (fst x) (snd x)) xs)).
    set (outputs := fold_right Nat.add 0%nat
      (map (fun wy : positive * K.p => K.psize (fst wy) (snd wy))
        (combine (map fst xs) (tnum_refine xs (tnum_backward_raw o xs rw q))))).
    change (outputs <= inputs + 2 * widths)%nat in Hstorage.
    change (length xs <= widths)%nat in Hlength.
    change (length xs + outputs <=
      (Pos.to_nat rw + widths + 1) ^ 2 + K.psize rw q + inputs)%nat.
    clearbody widths inputs outputs.
    lia.
  Qed.
End KnownBitsTableClock.

Module KnownBitsTableT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_T L C) <: KNOWN_BITS_TABLE_T L C K.
  Include KnownBitsTableClock L C K.

  Local Lemma forward_one_bits : forall o rw w a,
    (tnum_bits (tnum_forward_raw o [(w, a)] rw) <= 2 * Pos.to_nat rw)%nat.
  Proof.
    intros o rw w a.
    pose proof (K.tnum_unary_bits rw a) as [Hnot [Hneg Hnormalise]].
    destruct o; cbn [tnum_forward_raw];
      first [exact Hnot|exact Hneg|apply tnum_count_bits|apply tnum_map_bits|
        apply tnum_top_bits].
  Qed.

  Local Lemma forward_two_bits : forall o rw w v a b,
    (tnum_bits (tnum_forward_raw o [(w, a); (v, b)] rw) <=
      2 * (Pos.to_nat rw + Pos.to_nat w + Pos.to_nat v))%nat.
  Proof.
    intros o rw w v a b.
    pose proof (K.tnum_binary_bits rw a b) as [Hadd [Hsub [Hand [Hor [Hxor Hmul]]]]].
    pose proof (K.tnum_stage_bits MulLow o rw a b) as [Hchoice Hvariable].
    pose proof (tnum_top_bits rw) as Htop.
    pose proof (Pos2Nat.is_pos rw) as Hwidth.
    destruct o; cbn [tnum_forward_raw]; try lia.
    all: try match goal with
    | |- context [tnum_udiv ?w ?a ?b] =>
      pose proof (tnum_udiv_bits w a b) as Hbound; lia
    | |- context [tnum_urem ?w ?a] =>
      pose proof (tnum_urem_bits w a) as Hbound; lia
    | |- context [tnum_srem ?w ?a] =>
      pose proof (tnum_srem_bits w a) as Hbound; lia
    | |- context [tnum_compare ?tag ?w ?a ?b] =>
      pose proof (tnum_compare_bits tag w a b) as Hbound;
        change (tnum_bits (tnum_compare tag w a b) <= 2)%nat in Hbound; lia
    | |- context [tnum_concat ?w ?v ?a ?b] =>
      pose proof (tnum_concat_bits w v a b) as Hbound;
        rewrite Pos2Nat.inj_add in Hbound; lia
    end.
    destruct (Pos.eqb w rw && Pos.eqb v rw); [lia|].
    pose proof (tnum_mul_bits rw a b). lia.
  Qed.

  Local Lemma forward_three_bits : forall o rw w v u a b c,
    (tnum_bits (tnum_forward_raw o [(w, a); (v, b); (u, c)] rw) <=
      2 * Pos.to_nat rw)%nat.
  Proof.
    intros o rw w v u a b c. destruct o; cbn [tnum_forward_raw];
      first [apply tnum_ite_bits|apply tnum_top_bits].
  Qed.

  (** Forward storage is bounded even for unchecked result-width requests. *)
  Local Lemma forward_storage : forall o rw (xs : list (positive * K.p)),
    (tnum_bits (tnum_forward_raw o xs rw) <=
      2 * (Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs)))%nat.
  Proof.
    intros o rw [|[w a] [|[v b] [|[u c] [|wp xs]]]];
      cbn [map fold_right fst snd].
    - rewrite Nat.add_0_r. destruct o; apply tnum_top_bits.
    - eapply Nat.le_trans; [apply forward_one_bits|lia].
    - eapply Nat.le_trans; [apply forward_two_bits|lia].
    - eapply Nat.le_trans; [apply forward_three_bits|lia].
    - pose proof (tnum_top_bits rw) as Htop.
      destruct o; (eapply Nat.le_trans; [exact Htop|lia]).
  Qed.
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0
          (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0
          (map (fun x => K.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs. eapply N.le_trans; [apply forward_time_budget|].
    apply N.mul_le_mono_r. unfold c_word_table. lia.
  Qed.
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (K.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0
          (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0
          (map (fun x => K.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs r Hforward. unfold wfwd in Hforward.
    destruct (Nat.eqb (length xs) (arity o)); [|discriminate].
    destruct (tnum_table_bounded o xs); [|discriminate].
    injection Hforward as <-.
    eapply N.le_trans; [|apply word_table_scale].
    rewrite <- N.compare_le_iff, <- Nat2N.inj_compare, Nat.compare_le_iff.
    rewrite K.psize_bits.
    pose proof (forward_storage o rw xs) as Hstorage.
    pose proof (Pos2Nat.is_pos rw) as Hwidth. cbn [Nat.pow]. nia.
  Qed.
End KnownBitsTableT.
