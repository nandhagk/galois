(** * Difference-bound matrices

    Sparse matrices store finite bounds and interpret missing entries as infinity.
    For example, a zero-to-variable entry bounds that variable from above.
    Builds on: ZoneSig and keyed map operations. *)

From Stdlib Require Import List Bool NArith ZArith Lia ArithRing.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig MapSig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig ZoneSig.
Local Open Scope nat_scope.

(** Finite interval endpoints add; an absent endpoint remains unbounded. *)
Definition rel_add_bounds (a b : bnd * bnd) : bnd * bnd :=
  (match fst a, fst b with Fin x, Fin y => Fin (x + y)%Z | _, _ => NegInf end,
   match snd a, snd b with Fin x, Fin y => Fin (x + y)%Z | _, _ => PosInf end).
TimeFun rel_add_bounds.

(** Scaling reverses endpoints exactly when the coefficient is negative. *)
Definition rel_scale_bounds (c : Z) (a : bnd * bnd) : bnd * bnd :=
  if (c =? 0)%Z then (Fin 0%Z, Fin 0%Z) else
  let lo := if (0 <=? c)%Z then fst a else snd a in
  let hi := if (0 <=? c)%Z then snd a else fst a in
  (match lo with Fin x => Fin (c * x)%Z | _ => NegInf end,
   match hi with Fin x => Fin (c * x)%Z | _ => PosInf end).
TimeFun rel_scale_bounds.

(** Each coefficient is queried once, and the constant starts the sum. *)
Definition rel_form_bounds {X : Type} (ranges : X -> bnd * bnd)
    (f : lin X) : bnd * bnd :=
  fold_right (fun p acc => rel_add_bounds (rel_scale_bounds (snd p) (ranges (fst p))) acc)
    (Fin (cst f), Fin (cst f)) (coef f).
TimeFun rel_form_bounds.

(** A valid wrapping interval bounds every modular result. *)
Definition rel_wrap_bounds (r : wrapr) (a : bnd * bnd) : bnd * bnd :=
  match r with
  | NoWrap => a
  | WrapTo lo hi => if (lo <=? hi)%Z then (Fin lo, Fin hi) else (NegInf, PosInf)
  end.
TimeFun rel_wrap_bounds.

(** An affine result may be used without wrapping when both endpoints fit. *)
Definition rel_wrap_exact (r : wrapr) (a : bnd * bnd) : bool :=
  match r with
  | NoWrap => true
  | WrapTo lo hi =>
    match a with
    | (Fin l, Fin h) => andb (lo <=? l)%Z (h <=? hi)%Z
    | _ => false
    end
  end.
TimeFun rel_wrap_exact.

Lemma rel_add_bounds_sound : forall a b x y,
  in_bnd (fst a) (snd a) x -> in_bnd (fst b) (snd b) y ->
  in_bnd (fst (rel_add_bounds a b)) (snd (rel_add_bounds a b)) (x + y)%Z.
Proof.
  intros [al ah] [bl bh] x y Ha Hb.
  unfold rel_add_bounds, in_bnd in *.
  destruct al, ah, bl, bh; cbn in *; intuition lia.
Qed.

Lemma rel_scale_bounds_sound : forall c a x,
  in_bnd (fst a) (snd a) x ->
  in_bnd (fst (rel_scale_bounds c a)) (snd (rel_scale_bounds c a)) (c * x)%Z.
Proof.
  intros c [lo hi] x Hx. unfold rel_scale_bounds.
  destruct (c =? 0)%Z eqn:Hc.
  - apply Z.eqb_eq in Hc. subst c. unfold in_bnd. cbn. lia.
  - destruct (0 <=? c)%Z eqn:Hsign;
      [apply Z.leb_le in Hsign|apply Z.leb_gt in Hsign];
      unfold in_bnd in *; destruct lo, hi; cbn in *; intuition nia.
Qed.

Lemma rel_form_bounds_sound : forall (X : Type) ranges (f : lin X) v,
  (forall x, in_bnd (fst (ranges x)) (snd (ranges x)) (v x)) ->
  in_bnd (fst (rel_form_bounds ranges f)) (snd (rel_form_bounds ranges f)) (eval_lin v f).
Proof.
  intros X ranges [cs c] v Hr. unfold rel_form_bounds, eval_lin. cbn [coef cst].
  induction cs as [|[x a] cs IH].
  - change (in_bnd (Fin c) (Fin c) c). unfold in_bnd. lia.
  - change (in_bnd
      (fst (rel_add_bounds (rel_scale_bounds a (ranges x))
        (rel_form_bounds ranges (Lin X cs c))))
      (snd (rel_add_bounds (rel_scale_bounds a (ranges x))
        (rel_form_bounds ranges (Lin X cs c))))
      (a * v x + eval_coef v cs + c)%Z).
    replace (a * v x + eval_coef v cs + c)%Z with (a * v x + (eval_coef v cs + c))%Z by ring.
    apply rel_add_bounds_sound; [apply rel_scale_bounds_sound, Hr|exact IH].
Qed.

Lemma rel_wrap_bounds_sound : forall r a z,
  in_bnd (fst a) (snd a) z ->
  in_bnd (fst (rel_wrap_bounds r a)) (snd (rel_wrap_bounds r a)) (wrap_into r z).
Proof.
  intros [|lo hi] a z Hz; [exact Hz|].
  unfold rel_wrap_bounds. destruct (lo <=? hi)%Z eqn:Hbounds.
  - apply Z.leb_le in Hbounds. unfold wrap_into, in_bnd. cbn.
    pose proof (Z.mod_pos_bound (z - lo) (hi - lo + 1) ltac:(lia)). lia.
  - unfold in_bnd. cbn. tauto.
Qed.

Lemma rel_wrap_exact_sound : forall r a z,
  in_bnd (fst a) (snd a) z -> rel_wrap_exact r a = true -> wrap_into r z = z.
Proof.
  intros [|lo hi] [l h] z Hz Hexact; [reflexivity|].
  unfold rel_wrap_exact in Hexact.
  destruct l, h; cbn in Hexact; try discriminate Hexact.
  apply andb_true_iff in Hexact. destruct Hexact as [Hl Hh].
  apply Z.leb_le in Hl. apply Z.leb_le in Hh. unfold in_bnd in Hz. cbn in Hz.
  unfold wrap_into. rewrite Z.mod_small by lia. lia.
Qed.

(** Finite endpoints are measured by their absolute values, independently of sign. *)
Definition rel_bound_abs (upper : nat) (b : bnd) : Prop :=
  match b with Fin z => Z.abs_nat z < upper | _ => True end.

Definition rel_bounds_abs (upper : nat) (bounds : bnd * bnd) : Prop :=
  rel_bound_abs upper (fst bounds) /\ rel_bound_abs upper (snd bounds).

Lemma rel_abs_add : forall x y, Z.abs_nat (x + y)%Z <= Z.abs_nat x + Z.abs_nat y.
Proof.
  intros x y. apply (proj2 (Nat2Z.inj_le _ _)).
  rewrite Nat2Z.inj_add, !Zabs2Nat.id_abs. apply Z.abs_triangle.
Qed.

(** Endpoint addition adds the two magnitude bounds. *)
Lemma rel_bounds_abs_add : forall a b upper_a upper_b,
  rel_bounds_abs upper_a a -> rel_bounds_abs upper_b b ->
  rel_bounds_abs (upper_a + upper_b) (rel_add_bounds a b).
Proof.
  intros [al ah] [bl bh] upper_a upper_b Ha Hb.
  unfold rel_add_bounds, rel_bounds_abs, rel_bound_abs in *.
  destruct al, ah, bl, bh; cbn [fst snd] in *;
    intuition (eapply Nat.le_lt_trans; [apply rel_abs_add|lia]).
Qed.

(** Scalar multiplication multiplies magnitude bounds, with zero handled exactly. *)
Lemma rel_bounds_abs_scale : forall c bounds upper_c upper_x,
  Z.abs_nat c < upper_c -> rel_bounds_abs upper_x bounds ->
  0 < upper_c -> 0 < upper_x ->
  rel_bounds_abs (upper_c * upper_x) (rel_scale_bounds c bounds).
Proof.
  intros c [lo hi] upper_c upper_x Hc Hbounds Hpc Hpx.
  unfold rel_scale_bounds. destruct (c =? 0)%Z eqn:Hcz.
  - change (0 < upper_c * upper_x /\ 0 < upper_c * upper_x). nia.
  - destruct (0 <=? c)%Z;
      unfold rel_bounds_abs, rel_bound_abs in *;
      destruct lo, hi; cbn [fst snd] in *;
      rewrite ?Zabs2Nat.inj_mul; intuition nia.
Qed.

(** An affine interval is bounded by the sum of its coefficient products and its constant. *)
Lemma rel_form_bounds_abs : forall (X : Type) ranges (f : lin X) upper_c upper_x,
  Z.abs_nat (cst f) < upper_c ->
  Forall (fun p => Z.abs_nat (snd p) < upper_c) (coef f) ->
  (forall x, rel_bounds_abs upper_x (ranges x)) ->
  0 < upper_c -> 0 < upper_x ->
  rel_bounds_abs ((length (coef f) + 1) * upper_c * upper_x)
    (rel_form_bounds ranges f).
Proof.
  intros X ranges [cs c] upper_c upper_x Hc.
  cbn [cst] in Hc.
  induction cs as [|[x a] cs IH]; intros Hcoeff Hr Hpc Hpx.
  - change (rel_bounds_abs ((0 + 1) * upper_c * upper_x) (Fin c, Fin c)).
    unfold rel_bounds_abs, rel_bound_abs. cbn [fst snd]. nia.
  - inversion Hcoeff as [|p ps Ha Htail]; subst.
    change (rel_bounds_abs ((S (length cs) + 1) * upper_c * upper_x)
      (rel_add_bounds (rel_scale_bounds a (ranges x))
        (rel_form_bounds ranges (Lin X cs c)))).
    replace ((S (length cs) + 1) * upper_c * upper_x) with
      (upper_c * upper_x + (length cs + 1) * upper_c * upper_x) by nia.
    apply rel_bounds_abs_add.
    + apply rel_bounds_abs_scale; try assumption. apply Hr.
    + now apply IH.
Qed.

(** Increasing a magnitude allowance preserves every finite endpoint bound. *)
Lemma rel_bounds_abs_mono : forall lower upper bounds,
  lower <= upper -> rel_bounds_abs lower bounds -> rel_bounds_abs upper bounds.
Proof.
  intros lower upper [lo hi] Hle Hbounds.
  unfold rel_bounds_abs, rel_bound_abs in *.
  destruct lo, hi; cbn [fst snd] in *; intuition lia.
Qed.

(** Timing helpers for interval folds use only the accumulators that the fold reaches. *)
Lemma rel_zbits_least : forall z bits,
  Z.abs_nat z < 2 ^ bits -> Z.size_nat z <= bits.
Proof.
  intros [|p|p] bits Hbound; cbn [Z.abs_nat Z.size_nat] in *.
  - lia.
  - now apply Pos.size_nat_least.
  - now apply Pos.size_nat_least.
Qed.

(** A right fold needs a callback bound only at its actual suffix results. *)
Lemma rel_fold_right_time : forall (A B : Type) (f : B -> A -> A)
    (tf : B -> A -> N) initial xs charge,
  (forall before x after, xs = before ++ x :: after ->
    (tf x (fold_right f initial after) <= charge)%N) ->
  (Std.List.T_fold_right f tf initial xs <=
    (charge + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A B f tf initial xs charge. induction xs as [|x xs IH]; intro Hbound.
  - time_step.
  - pose proof (Hbound nil x xs eq_refl) as Hhead.
    assert (Htail : (Std.List.T_fold_right f tf initial xs <=
      (charge + 1) * N.of_nat (length xs) + 1)%N).
    { apply IH. intros before y after Heq.
      apply (Hbound (x :: before) y after). cbn [app]. now rewrite Heq. }
    time_step.
Qed.

(** A common bit budget bounds the two factors in the derived integer product clock. *)
Lemma rel_mul_time_budget : forall a b budget,
  (N.of_nat (Z.size_nat a + Z.size_nat b + 1) <= budget)%N ->
  (Z.T_mul a b <= 2 * (budget * budget))%N.
Proof.
  intros a b budget Hbudget. rewrite !Nat2N.inj_add in Hbudget.
  eapply N.le_trans; [apply Z.T_mul_le|].
  replace (2 * (budget * budget))%N with (budget * (2 * budget))%N by ring.
  apply N.mul_le_mono; lia.
Qed.

(** Endpoint addition is linear in the two finite endpoint bit allowances. *)
Lemma rel_add_bounds_time : forall a b bits_a bits_b,
  rel_bounds_abs (2 ^ bits_a) a -> rel_bounds_abs (2 ^ bits_b) b ->
  (T_rel_add_bounds a b <= 16 * N.of_nat (bits_a + bits_b + 1))%N.
Proof.
  intros [al ah] [bl bh] bits_a bits_b Ha Hb.
  unfold rel_bounds_abs, rel_bound_abs in Ha, Hb.
  destruct al, ah, bl, bh; cbn [fst snd] in Ha, Hb;
    destruct Ha as [Hal Hah]; destruct Hb as [Hbl Hbh];
    try apply rel_zbits_least in Hal; try apply rel_zbits_least in Hah;
    try apply rel_zbits_least in Hbl; try apply rel_zbits_least in Hbh;
    time_step.
Qed.

(** Scaling has a quadratic allowance for the coefficient and finite endpoints. *)
Lemma rel_scale_bounds_time : forall c bounds bits_c bits_x,
  Z.size_nat c <= bits_c -> rel_bounds_abs (2 ^ bits_x) bounds ->
  (T_rel_scale_bounds c bounds <= 32 * N.of_nat ((bits_c + bits_x + 1)^2))%N.
Proof.
  intros c [lo hi] bits_c bits_x Hc Hbounds.
  set (budget := N.of_nat (bits_c + bits_x + 1)).
  assert (Hpositive : (1 <= budget)%N) by (unfold budget; lia).
  assert (Hsquare : N.of_nat ((bits_c + bits_x + 1)^2) = (budget * budget)%N).
  { unfold budget. cbn [Nat.pow]. rewrite Nat.mul_1_r, Nat2N.inj_mul. reflexivity. }
  rewrite Hsquare.
  assert (Hunit : (1 <= budget * budget)%N).
  { change (1 * 1 <= budget * budget)%N. now apply N.mul_le_mono. }
  assert (Hlinear : (budget <= budget * budget)%N).
  { replace budget with (1 * budget)%N at 1 by ring.
    apply N.mul_le_mono_r. exact Hpositive. }
  assert (Hcoefficient : (N.of_nat (Z.size_nat c) + 1 <= budget * budget)%N).
  { eapply N.le_trans; [|exact Hlinear]. unfold budget. rewrite !Nat2N.inj_add. lia. }
  assert (Hproduct : forall z, Z.abs_nat z < 2 ^ bits_x ->
    (Z.T_mul c z <= 2 * (budget * budget))%N).
  { intros z Hz. apply rel_mul_time_budget. unfold budget. apply time_of_nat_le.
    pose proof (rel_zbits_least z bits_x Hz). lia. }
  pose proof (Z.T_eqb_le c 0%Z) as Hequal.
  pose proof (Z.T_leb_le 0%Z c) as Hsign.
  change (Z.T_leb 0%Z c <= 4)%N in Hsign.
  set (charge := (budget * budget)%N) in *. clearbody charge.
  unfold T_rel_scale_bounds.
  destruct (c =? 0)%Z eqn:Hcz; [time_simpl; time_cbn; lia|].
  destruct (0 <=? c)%Z eqn:Hsgn; destruct lo, hi;
    unfold rel_bounds_abs, rel_bound_abs in Hbounds;
    cbn [fst snd] in Hbounds; destruct Hbounds as [Hlo Hhi];
    try pose proof (Hproduct _ Hlo) as Hmullo;
    try pose proof (Hproduct _ Hhi) as Hmulhi;
    time_simpl; time_cbn; lia.
Qed.

(** Wrapping checks its explicitly stored endpoints once. *)
Lemma rel_wrap_bounds_time : forall r bounds bits,
  (match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end) <= bits ->
  (T_rel_wrap_bounds r bounds <= 8 * N.of_nat (bits + 1))%N.
Proof.
  intros [|lo hi] bounds bits Hbits; cbn in Hbits; time_step.
Qed.

(** Exactness checks charge a wrapping endpoint and the computed upper endpoint. *)
Lemma rel_wrap_exact_time : forall r bounds bits_r bits_a,
  (match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end) <= bits_r ->
  rel_bounds_abs (2 ^ bits_a) bounds ->
  (T_rel_wrap_exact r bounds <= 16 * N.of_nat (bits_r + bits_a + 1))%N.
Proof.
  intros [|wl wh] [lo hi] bits_r bits_a Hr Ha; [time_step|].
  cbn in Hr. unfold rel_bounds_abs, rel_bound_abs in Ha.
  destruct lo, hi; cbn [fst snd] in Ha; destruct Ha as [Hlo Hhi];
    try apply rel_zbits_least in Hlo; try apply rel_zbits_least in Hhi; time_step.
Qed.

(** Finite bounds with an absent value interpreted as positive infinity. *)
Module RelationalPathBounds.
  Definition below (a b : option Z) : Prop :=
    match a, b with
    | Some x, Some y => (x <= y)%Z
    | None, Some _ => False
    | _, None => True
    end.

  Definition minimum (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => Some (Z.min x y)
    | None, _ => b
    | _, None => a
    end.

  Definition plus (a b : option Z) : option Z :=
    match a, b with Some x, Some y => Some (x + y)%Z | _, _ => None end.

  Lemma below_refl : forall a, below a a.
  Proof. intros [a|]; cbn [below]; lia || exact I. Qed.

  Lemma below_trans : forall a b c, below a b -> below b c -> below a c.
  Proof.
    intros [a|] [b|] [c|]; cbn [below]; intros; try contradiction; try exact I; lia.
  Qed.

  Lemma below_antisym : forall a b, below a b -> below b a -> a = b.
  Proof.
    intros [a|] [b|]; cbn [below]; intros; try contradiction; try reflexivity.
    f_equal. lia.
  Qed.

  Lemma minimum_glb : forall d a b,
    below d (minimum a b) <-> below d a /\ below d b.
  Proof.
    intros [d|] [a|] [b|]; cbn [below minimum]; try tauto.
    destruct (Z_le_dec a b); [rewrite Z.min_l by lia|rewrite Z.min_r by lia]; lia.
  Qed.

  Lemma minimum_l : forall a b, below (minimum a b) a.
  Proof.
    intros a b. exact (proj1 (proj1 (minimum_glb (minimum a b) a b)
      (below_refl (minimum a b)))).
  Qed.

  Lemma minimum_r : forall a b, below (minimum a b) b.
  Proof.
    intros a b. exact (proj2 (proj1 (minimum_glb (minimum a b) a b)
      (below_refl (minimum a b)))).
  Qed.

  Lemma minimum_idem : forall a, minimum a a = a.
  Proof.
    intro a. apply below_antisym; [apply minimum_l|].
    apply minimum_glb. split; apply below_refl.
  Qed.

  Lemma minimum_when_below : forall a b, below a b -> minimum a b = a.
  Proof.
    intros a b Hab. apply below_antisym; [apply minimum_l|].
    apply minimum_glb. split; [apply below_refl|exact Hab].
  Qed.

  Lemma plus_comm : forall a b, plus a b = plus b a.
  Proof.
    intros [a|] [b|]; cbn [plus]; try reflexivity. f_equal. lia.
  Qed.

  Lemma plus_assoc : forall a b c, plus (plus a b) c = plus a (plus b c).
  Proof.
    intros [a|] [b|] [c|]; cbn [plus]; try reflexivity. f_equal. lia.
  Qed.

  Lemma plus_zero_l : forall a, plus (Some 0%Z) a = a.
  Proof. intros [a|]; reflexivity. Qed.

  Lemma plus_zero_r : forall a, plus a (Some 0%Z) = a.
  Proof. intro a. rewrite plus_comm. apply plus_zero_l. Qed.

  Lemma plus_mono : forall a b c d,
    below a b -> below c d -> below (plus a c) (plus b d).
  Proof.
    intros [a|] [b|] [c|] [d|]; cbn [below plus]; intros;
      try contradiction; try exact I; lia.
  Qed.

  Lemma plus_minimum_r : forall a b c,
    plus (minimum a b) c = minimum (plus a c) (plus b c).
  Proof.
    intros [a|] [b|] [c|]; cbn [plus minimum]; try reflexivity.
    destruct (Z_le_dec a b).
    - rewrite !Z.min_l by lia. reflexivity.
    - rewrite !Z.min_r by lia. reflexivity.
  Qed.

  Lemma plus_minimum_l : forall a b c,
    plus a (minimum b c) = minimum (plus a b) (plus a c).
  Proof.
    intros a b c. rewrite (plus_comm a (minimum b c)), plus_minimum_r.
    now rewrite (plus_comm b a), (plus_comm c a).
  Qed.

  Lemma minimum_value : forall a b z, minimum a b = Some z -> a = Some z \/ b = Some z.
  Proof.
    intros [a|] [b|] z H; cbn [minimum] in H; try discriminate.
    - destruct (Z_le_dec a b).
      + rewrite Z.min_l in H by lia. now left.
      + rewrite Z.min_r in H by lia. now right.
    - now left.
    - now right.
  Qed.

  Lemma plus_value : forall a b z, plus a b = Some z ->
    exists x y, a = Some x /\ b = Some y /\ z = (x + y)%Z.
  Proof.
    intros [a|] [b|] z H; cbn [plus] in H; try discriminate.
    inversion H; subst z. exists a, b. auto.
  Qed.

  Lemma below_finite : forall a z, below a (Some z) ->
    exists y, a = Some y /\ (y <= z)%Z.
  Proof.
    intros [a|] z H; cbn [below] in H; [exists a; auto|contradiction].
  Qed.

  Definition floyd {A : Type} (r : A -> A -> option Z) (k i j : A) : option Z :=
    minimum (r i j) (plus (r i k) (r k j)).

  Definition closed_at {A : Type} (r : A -> A -> option Z) (k : A) : Prop :=
    forall i j, below (r i j) (plus (r i k) (r k j)).

  Lemma floyd_below_old : forall A (r : A -> A -> option Z) k i j,
    below (floyd r k i j) (r i j).
  Proof. intros. apply minimum_l. Qed.

  Lemma floyd_below_path : forall A (r : A -> A -> option Z) k i j,
    below (floyd r k i j) (plus (r i k) (r k j)).
  Proof. intros. apply minimum_r. Qed.

  Lemma floyd_to_pivot : forall A (r : A -> A -> option Z) k i,
    r k k = Some 0%Z -> floyd r k i k = r i k.
  Proof.
    intros A r k i Hkk. unfold floyd. rewrite Hkk, plus_zero_r. apply minimum_idem.
  Qed.

  Lemma floyd_from_pivot : forall A (r : A -> A -> option Z) k j,
    r k k = Some 0%Z -> floyd r k k j = r k j.
  Proof.
    intros A r k j Hkk. unfold floyd. rewrite Hkk, plus_zero_l. apply minimum_idem.
  Qed.

  (** A nonnegative pivot cycle lets a round preserve every previous triangle closure. *)
  Lemma floyd_preserves_closed : forall A (r : A -> A -> option Z) k p,
    r k k = Some 0%Z -> closed_at r p -> closed_at (floyd r k) p.
  Proof.
    intros A r k p Hkk Hp i j.
    unfold floyd. rewrite plus_minimum_r, !plus_minimum_l, !minimum_glb.
    split; split.
    - eapply below_trans; [apply minimum_l|apply Hp].
    - rewrite <- plus_assoc.
      eapply below_trans; [apply minimum_r|].
      apply plus_mono; [apply Hp|apply below_refl].
    - rewrite plus_assoc.
      eapply below_trans; [apply minimum_r|].
      apply plus_mono; [apply below_refl|apply Hp].
    - assert (Hcycle : below (Some 0%Z) (plus (r k p) (r p k))).
      { pose proof (Hp k k) as Hcycle. now rewrite Hkk in Hcycle. }
      replace (plus (plus (r i k) (r k p)) (plus (r p k) (r k j))) with
        (plus (plus (r i k) (plus (r k p) (r p k))) (r k j))
        by (rewrite !plus_assoc; reflexivity).
      eapply below_trans; [apply minimum_r|].
      replace (plus (r i k) (r k j)) with
        (plus (plus (r i k) (Some 0%Z)) (r k j)) by (rewrite plus_zero_r; reflexivity).
      apply plus_mono; [|apply below_refl].
      apply plus_mono; [apply below_refl|exact Hcycle].
  Qed.

  Lemma floyd_closes_pivot : forall A (r : A -> A -> option Z) k,
    r k k = Some 0%Z -> closed_at (floyd r k) k.
  Proof.
    intros A r k Hkk i j. rewrite floyd_to_pivot, floyd_from_pivot by exact Hkk.
    apply floyd_below_path.
  Qed.

  Lemma floyd_preserves_zero : forall A (r : A -> A -> option Z) k p,
    r k k = Some 0%Z -> r p p = Some 0%Z -> closed_at r p ->
    floyd r k p p = Some 0%Z.
  Proof.
    intros A r k p Hkk Hpp Hp. unfold floyd. rewrite Hpp.
    apply minimum_when_below. rewrite plus_comm.
    pose proof (Hp k k) as Hcycle. now rewrite Hkk in Hcycle.
  Qed.
  (** A chain lists internal vertices and always contains at least one original edge. *)
  Fixpoint chain {A : Type} (e : A -> A -> option Z) (i : A)
      (ks : list A) (j : A) : option Z :=
    match ks with
    | nil => e i j
    | k :: rest => plus (e i k) (chain e k rest j)
    end.

  Lemma chain_app : forall A (e : A -> A -> option Z) before after i k j,
    chain e i (before ++ k :: after) j =
      plus (chain e i before k) (chain e k after j).
  Proof.
    intros A e before. induction before as [|p before IH]; intros after i k j.
    - reflexivity.
    - cbn [chain app]. rewrite IH, plus_assoc. reflexivity.
  Qed.

  (** Triangle closure bounds every chain through the processed vertices. *)
  Lemma chain_bound : forall A (e r : A -> A -> option Z) processed,
    (forall i j, below (r i j) (e i j)) ->
    (forall k, In k processed -> closed_at r k) ->
    forall ks i j, incl ks processed -> below (r i j) (chain e i ks j).
  Proof.
    intros A e r processed Hmono Hclosed ks.
    induction ks as [|k ks IH]; intros i j Hks.
    - apply Hmono.
    - cbn [chain]. eapply below_trans.
      + exact (Hclosed k (Hks k (or_introl eq_refl)) i j).
      + apply plus_mono; [apply Hmono|].
        apply IH. intros p Hp. apply Hks. now right.
  Qed.

  (** Summing a finite chain charges its number of original edges. *)
  Lemma chain_abs : forall A (e : A -> A -> option Z) upper,
    (forall i j z, e i j = Some z -> Z.abs_nat z <= upper) ->
    forall ks i j z, chain e i ks j = Some z ->
      Z.abs_nat z <= (length ks + 1) * upper.
  Proof.
    intros A e upper Hbound ks. induction ks as [|k ks IH]; intros i j z Hchain.
    - cbn [chain] in Hchain. pose proof (Hbound i j z Hchain). cbn [length]. lia.
    - cbn [chain] in Hchain. apply plus_value in Hchain.
      destruct Hchain as [a [b [Hfirst [Hrest Hz]]]]. subst z.
      pose proof (Hbound i k a Hfirst) as Ha.
      pose proof (IH k j b Hrest) as Hb.
      pose proof (rel_abs_add a b) as Hsum. cbn [length]. nia.
  Qed.

  (** Every prefix vertex is the source of an original edge. *)
  Lemma chain_sources : forall A (e : A -> A -> option Z) (P : A -> Prop),
    (forall i j z, e i j = Some z -> P i) ->
    forall ks i j z, chain e i ks j = Some z ->
      forall x, In x (i :: ks) -> P x.
  Proof.
    intros A e P Hsource ks. induction ks as [|k ks IH]; intros i j z Hchain x Hx.
    - destruct Hx as [Heq|Hx]; [subst x|contradiction].
      eapply Hsource. exact Hchain.
    - cbn [chain] in Hchain. apply plus_value in Hchain.
      destruct Hchain as [a [b [Hfirst [Hrest Hz]]]].
      destruct Hx as [Heq|Hx].
      + subst x. eapply Hsource. exact Hfirst.
      + exact (IH k j b Hrest x Hx).
  Qed.

  (** A suffix of a minimum chain is itself minimum once its first pivot is closed. *)
  Lemma path_suffix_exact : forall A (e r : A -> A -> option Z) processed,
    (forall i j, below (r i j) (e i j)) ->
    (forall k, In k processed -> closed_at r k) ->
    forall i k j ks a b, In k processed -> incl ks processed ->
      e i k = Some a -> chain e k ks j = Some b ->
      r i j = Some (a + b)%Z -> r k j = Some b.
  Proof.
    intros A e r processed Hmono Hclosed i k j ks a b Hk Hks Hfirst Hrest Hentry.
    pose proof (Hmono i k) as Hprefix. rewrite Hfirst in Hprefix.
    destruct (below_finite _ a Hprefix) as [a' [Ha' Hlea]].
    pose proof (chain_bound A e r processed Hmono Hclosed ks k j Hks) as Hsuffix.
    rewrite Hrest in Hsuffix.
    destruct (below_finite _ b Hsuffix) as [b' [Hb' Hleb]].
    pose proof (Hclosed k Hk i j) as Htriangle.
    rewrite Hentry, Ha', Hb' in Htriangle. cbn [below plus] in Htriangle.
    assert (Hb : b' = b) by lia. now subst b'.
  Qed.

  (** A minimum chain can erase every repeat before its final endpoint. *)
  Lemma simple_minimum_chain : forall A
      (decide : forall x y : A, {x = y} + {x <> y})
      (e r : A -> A -> option Z) processed,
    (forall i j, below (r i j) (e i j)) ->
    (forall k, In k processed -> closed_at r k) ->
    (forall k, In k processed -> r k k = Some 0%Z) ->
    forall ks i j d, incl ks processed ->
      r i j = Some d -> chain e i ks j = Some d ->
      exists shortened, incl shortened ks /\ NoDup (i :: shortened) /\
        chain e i shortened j = Some d.
  Proof.
    intros A decide e r processed Hmono Hclosed Hzero.
    assert (Hall : forall n ks, length ks < n ->
      forall i j d, incl ks processed ->
        r i j = Some d -> chain e i ks j = Some d ->
        exists shortened, incl shortened ks /\ NoDup (i :: shortened) /\
          chain e i shortened j = Some d).
    { induction n as [|n IH]; intros ks Hlength i j d Hks Hentry Hchain.
      - lia.
      - destruct (in_dec decide i ks) as [Hloop|Hfresh].
        + apply in_split in Hloop. destruct Hloop as [before [after Heq]]. subst ks.
          assert (Hi : In i processed).
          { apply Hks. apply in_or_app. right. now left. }
          assert (Hbefore : incl before processed).
          { intros x Hx. apply Hks. apply in_or_app. now left. }
          assert (Hafter : incl after processed).
          { intros x Hx. apply Hks. apply in_or_app. right. now right. }
          rewrite chain_app in Hchain. apply plus_value in Hchain.
          destruct Hchain as [cycle [rest [Hcycle [Hrest Hd]]]].
          pose proof (chain_bound A e r processed Hmono Hclosed before i i Hbefore)
            as Hcycle_bound.
          rewrite (Hzero i Hi), Hcycle in Hcycle_bound. cbn [below] in Hcycle_bound.
          pose proof (chain_bound A e r processed Hmono Hclosed after i j Hafter)
            as Hrest_bound.
          rewrite Hentry, Hrest in Hrest_bound. cbn [below] in Hrest_bound.
          assert (Hsame : rest = d) by lia.
          assert (Hshort : length after < n).
          { rewrite length_app in Hlength. cbn [length] in Hlength. lia. }
          assert (Hafter_value : chain e i after j = Some d).
          { now rewrite <- Hsame. }
          destruct (IH after Hshort i j d Hafter Hentry Hafter_value)
            as [shortened [Hincl [Hnodup Hvalue]]].
          exists shortened. split.
          * intros x Hx. apply in_or_app. right. right. now apply Hincl.
          * now split.
        + destruct ks as [|k rest].
          * exists nil. split; [intros x Hx; contradiction|].
            split; [constructor; [intro Hx; contradiction|constructor]|exact Hchain].
          * cbn [chain] in Hchain. apply plus_value in Hchain.
            destruct Hchain as [a [b [Hfirst [Hrest Hd]]]].
            assert (Hk : In k processed) by (apply Hks; now left).
            assert (Hrest_incl : incl rest processed).
            { intros x Hx. apply Hks. now right. }
            assert (Hcurrent : r i j = Some (a + b)%Z) by (now rewrite <- Hd).
            pose proof (path_suffix_exact A e r processed Hmono Hclosed
              i k j rest a b Hk Hrest_incl Hfirst Hrest Hcurrent) as Hsuffix.
            assert (Hshort : length rest < n) by (cbn [length] in Hlength; lia).
            destruct (IH rest Hshort k j b Hrest_incl Hsuffix Hrest)
              as [shortened [Hincl [Hnodup Hvalue]]].
            exists (k :: shortened). split.
            -- intros x [Hx|Hx]; [now left|right; now apply Hincl].
            -- split.
               ++ constructor; [|exact Hnodup]. intro Hx. apply Hfresh.
                  destruct Hx as [Hx|Hx]; [now left|right; now apply Hincl].
               ++ cbn [chain]. rewrite Hfirst, Hvalue. cbn [plus]. f_equal. lia. }
    intros ks i j d Hks Hentry Hchain.
    exact (Hall (S (length ks)) ks ltac:(lia) i j d Hks Hentry Hchain).
  Qed.
  Definition seed {A : Type} (decide : forall x y : A, {x = y} + {x <> y})
      (r : A -> A -> option Z) (k i j : A) : option Z :=
    if decide i k then
      if decide j k then minimum (Some 0%Z) (r k k) else r i j
    else r i j.

  Lemma seed_diag : forall A decide (r : A -> A -> option Z) k,
    seed decide r k k k = minimum (Some 0%Z) (r k k).
  Proof.
    intros A decide r k. unfold seed. destruct (decide k k); congruence.
  Qed.

  Lemma seed_away : forall A decide (r : A -> A -> option Z) k i j,
    i <> k \/ j <> k -> seed decide r k i j = r i j.
  Proof.
    intros A decide r k i j Haway. unfold seed.
    destruct (decide i k), (decide j k); intuition congruence.
  Qed.

  Lemma seed_below : forall A decide (r : A -> A -> option Z) k i j,
    below (seed decide r k i j) (r i j).
  Proof.
    intros A decide r k i j. unfold seed.
    destruct (decide i k) as [Hi|Hi]; [subst i|apply below_refl].
    destruct (decide j k) as [Hj|Hj]; [subst j; apply minimum_r|apply below_refl].
  Qed.

  Lemma seed_existing_zero : forall A decide (r : A -> A -> option Z) k,
    r k k = Some 0%Z -> forall i j, seed decide r k i j = r i j.
  Proof.
    intros A decide r k Hkk i j. unfold seed.
    destruct (decide i k) as [Hi|Hi]; [subst i|reflexivity].
    destruct (decide j k) as [Hj|Hj]; [subst j|reflexivity].
    rewrite Hkk. apply minimum_idem.
  Qed.

  Lemma seed_success_zero : forall A decide (r : A -> A -> option Z) k,
    (forall d, floyd (seed decide r k) k k k = Some d -> (0 <= d)%Z) ->
    seed decide r k k k = Some 0%Z.
  Proof.
    intros A decide r k Hsuccess. unfold floyd in Hsuccess.
    rewrite !seed_diag in Hsuccess |- *.
    destruct (r k k) as [d|]; [|reflexivity].
    cbn [minimum plus] in Hsuccess |- *.
    pose proof (Hsuccess (Z.min (Z.min 0 d) (Z.min 0 d + Z.min 0 d)) eq_refl)
      as Hnonneg.
    pose proof (Z.le_min_l 0 d) as Hupper.
    pose proof (Z.le_min_l (Z.min 0 d) (Z.min 0 d + Z.min 0 d)) as Hlower.
    f_equal. lia.
  Qed.

  Definition path_witness {A : Type} (e : A -> A -> option Z)
      (processed : list A) (i j : A) (d : Z) : Prop :=
    (i = j /\ d = 0%Z) \/
    exists ks, incl ks processed /\ chain e i ks j = Some d.

  Lemma path_witness_mono : forall A (e : A -> A -> option Z) ps qs i j d,
    incl ps qs -> path_witness e ps i j d -> path_witness e qs i j d.
  Proof.
    intros A e ps qs i j d Hincl [Hid|[ks [Hks Hchain]]].
    - now left.
    - right. exists ks. split; [|exact Hchain].
      intros x Hx. apply Hincl. now apply Hks.
  Qed.

  Lemma path_witness_plus : forall A (e : A -> A -> option Z) ps i k j a b,
    path_witness e ps i k a -> path_witness e ps k j b ->
    path_witness e (k :: ps) i j (a + b)%Z.
  Proof.
    intros A e ps i k j a b Hleft Hright.
    assert (Hgrow : incl ps (k :: ps)) by (intros x Hx; now right).
    destruct Hleft as [[Hi Ha]|[left [Hleft Hleft_value]]].
    - subst i a. replace (0 + b)%Z with b by lia.
      exact (path_witness_mono A e ps (k :: ps) k j b Hgrow Hright).
    - destruct Hright as [[Hj Hb]|[right [Hright Hright_value]]].
      + subst j b. replace (a + 0)%Z with a by lia.
        apply (path_witness_mono A e ps (k :: ps) i k a Hgrow).
        right. exists left. now split.
      + right. exists (left ++ k :: right). split.
        * intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[Hx|Hx]].
          -- right. now apply Hleft.
          -- now left.
          -- right. now apply Hright.
        * rewrite chain_app, Hleft_value, Hright_value. reflexivity.
  Qed.

  Record invariant {A : Type} (e r : A -> A -> option Z) (processed : list A) : Prop := {
    invariant_below : forall i j, below (r i j) (e i j);
    invariant_closed : forall k, In k processed -> closed_at r k;
    invariant_zero : forall k, In k processed -> r k k = Some 0%Z;
    invariant_path : forall i j d, r i j = Some d -> path_witness e processed i j d
  }.

  Lemma invariant_initial : forall A (e : A -> A -> option Z), invariant e e nil.
  Proof.
    intros A e. constructor.
    - intros. apply below_refl.
    - intros k Hk. contradiction.
    - intros k Hk. contradiction.
    - intros i j d Hentry. right. exists nil. split.
      + intros x Hx. contradiction.
      + exact Hentry.
  Qed.

  Lemma invariant_ext : forall A (e r s : A -> A -> option Z) ps,
    (forall i j, r i j = s i j) -> invariant e r ps -> invariant e s ps.
  Proof.
    intros A e r s ps Heq [Hbelow Hclosed Hzero Hpath]. constructor.
    - intros i j. rewrite <- Heq. apply Hbelow.
    - intros k Hk i j. rewrite <- !Heq. now apply Hclosed.
    - intros k Hk. rewrite <- Heq. now apply Hzero.
    - intros i j d Hentry. apply Hpath. now rewrite Heq.
  Qed.

  Lemma invariant_seed : forall A decide (e r : A -> A -> option Z) ps k,
    invariant e r ps -> invariant e (seed decide r k) ps.
  Proof.
    intros A decide e r ps k [Hbelow Hclosed Hzero Hpath]. constructor.
    - intros i j. eapply below_trans; [apply seed_below|apply Hbelow].
    - intros p Hp. destruct (decide p k) as [Heq|Hne].
      + subst p. intros i j. rewrite !seed_existing_zero by (now apply Hzero).
        now apply Hclosed.
      + intros i j. rewrite (seed_away A decide r k i p) by (right; exact Hne).
        rewrite (seed_away A decide r k p j) by (left; exact Hne).
        eapply below_trans; [apply seed_below|now apply Hclosed].
    - intros p Hp. destruct (decide p k) as [Heq|Hne].
      + subst p. rewrite seed_existing_zero by (now apply Hzero). now apply Hzero.
      + rewrite seed_away by (now left). now apply Hzero.
    - intros i j d Hentry. unfold seed in Hentry.
      destruct (decide i k) as [Hi|Hi]; [subst i|now apply Hpath].
      destruct (decide j k) as [Hj|Hj]; [subst j|now apply Hpath].
      apply minimum_value in Hentry. destruct Hentry as [Hentry|Hentry].
      + inversion Hentry; subst d. left. now split.
      + now apply Hpath.
  Qed.

  Lemma invariant_floyd : forall A (e r : A -> A -> option Z) ps k,
    invariant e r ps -> r k k = Some 0%Z -> invariant e (floyd r k) (k :: ps).
  Proof.
    intros A e r ps k [Hbelow Hclosed Hzero Hpath] Hkk. constructor.
    - intros i j. eapply below_trans; [apply floyd_below_old|apply Hbelow].
    - intros p [Hp|Hp].
      + subst p. now apply floyd_closes_pivot.
      + apply floyd_preserves_closed; [exact Hkk|now apply Hclosed].
    - intros p [Hp|Hp].
      + subst p. rewrite floyd_from_pivot by exact Hkk. exact Hkk.
      + apply floyd_preserves_zero; [exact Hkk|now apply Hzero|now apply Hclosed].
    - intros i j d Hentry. apply minimum_value in Hentry.
      destruct Hentry as [Hold|Hvia].
      + apply (path_witness_mono A e ps (k :: ps) i j d).
        * intros x Hx. now right.
        * now apply Hpath.
      + apply plus_value in Hvia. destruct Hvia as [a [b [Ha [Hb Hd]]]]. subst d.
        apply path_witness_plus; now apply Hpath.
  Qed.

  Lemma invariant_successful_round : forall A decide (e r : A -> A -> option Z) ps k,
    invariant e r ps ->
    (forall d, floyd (seed decide r k) k k k = Some d -> (0 <= d)%Z) ->
    invariant e (floyd (seed decide r k) k) (k :: ps).
  Proof.
    intros A decide e r ps k Hinv Hsuccess. apply invariant_floyd.
    - now apply invariant_seed.
    - now apply seed_success_zero.
  Qed.
End RelationalPathBounds.


Module ZoneCode (X : KEY_OPS) (K : KEY_OPS with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_OPS K) (L : LANG_OPS) (F : LINEARIZE_OPS X L) <: ZONE_OPS X K M L F.
  Definition dbm := M.t (M.t Z).
  Definition t := reach dbm.
  Definition wparam := nat.

  Definition row_of (r : option (M.t Z)) : M.t Z :=
    match r with Some row => row | None => M.empty end.

  Definition bound_leb (a b : option Z) : bool :=
    match a, b with
    | _, None => true
    | Some x, Some y => (x <=? y)%Z
    | None, Some _ => false
    end.

  Definition row_leb (a b : option (M.t Z)) : bool :=
    M.forall2b bound_leb (row_of a) (row_of b).

  Definition leb (a b : t) : bool :=
    match a, b with
    | Unreached, _ => true
    | Reached _, Unreached => false
    | Reached ma, Reached mb => M.forall2b row_leb ma mb
    end.

  Definition bot : t := Unreached.

  Definition is_bot (s : t) : bool :=
    match s with Unreached => true | Reached _ => false end.

  Definition bound_join (a b : option Z) : option Z :=
    match a, b with Some x, Some y => Some (Z.max x y) | _, _ => None end.

  Definition row_join (a b : option (M.t Z)) : option (M.t Z) :=
    match a, b with
    | Some x, Some y => Some (M.merge bound_join x y)
    | _, _ => None
    end.

  Definition join (a b : t) : t :=
    match a, b with
    | Unreached, _ => b
    | _, Unreached => a
    | Reached ma, Reached mb => Reached (M.merge row_join ma mb)
    end.

  Definition top : t := Reached M.empty.

  Definition bound_meet (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => Some (Z.min x y)
    | None, _ => b
    | _, None => a
    end.

  Definition row_meet (a b : option (M.t Z)) : option (M.t Z) :=
    match a, b with
    | Some x, Some y => Some (M.merge bound_meet x y)
    | None, _ => b
    | _, None => a
    end.

  Definition meet (a b : t) : t :=
    match a, b with
    | Reached ma, Reached mb => Reached (M.merge row_meet ma mb)
    | _, _ => Unreached
    end.

  Definition bound_widen (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => if (y <=? x)%Z then Some x else None
    | _, _ => None
    end.

  Definition row_widen (a b : option (M.t Z)) : option (M.t Z) :=
    match a with
    | Some x => Some (M.merge bound_widen x (row_of b))
    | None => None
    end.

  Definition widen (_ : wparam) (a b : t) : t :=
    if leb b a then a else
      match a, b with
      | Unreached, _ => b
      | _, Unreached => a
      | Reached ma, Reached mb => Reached (M.merge row_widen ma mb)
      end.

  Definition narrow (a b : t) : t := meet a b.

  Definition forget_row (x : X.t) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row => Some (M.remove (Some x) row)
    | None => None
    end.

  Definition havoc (x : X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.merge (forget_row x) (M.remove (Some x) m) M.empty)
    end.

  Definition entry (m : dbm) (i j : K.t) : option Z :=
    match M.get i m with Some row => M.get j row | None => None end.

  Definition variable_bounds (m : dbm) (x : X.t) : bnd * bnd :=
    (match entry m (Some x) None with Some d => Fin (-d)%Z | None => NegInf end,
     match entry m None (Some x) with Some d => Fin d | None => PosInf end).

  Definition form_bounds (m : dbm) (f : lin X.t) : bnd * bnd :=
    rel_form_bounds (variable_bounds m) f.

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s with
    | Unreached => (NegInf, PosInf)
    | Reached m =>
      match F.lin_of e with
      | Some (f, r) => rel_wrap_bounds r (form_bounds m f)
      | None => (NegInf, PosInf)
      end
    end.

  Definition lower_bound (d : Z) (old : option Z) : Z :=
    match old with Some z => Z.min d z | None => d end.

  Definition add_cons (i j : K.t) (d : Z) (m : dbm) : dbm :=
    let row := row_of (M.get i m) in
    M.set i (M.set j (lower_bound d (M.get j row)) row) m.

  Definition via_bound (a : Z) (old next : option Z) : option Z :=
    match next with
    | Some z => Some (lower_bound (a + z)%Z old)
    | None => old
    end.

  Definition round_row (k : K.t) (pivot : M.t Z) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row =>
      Some (match M.get k row with
        | Some a => M.merge (via_bound a) row pivot
        | None => row
        end)
    | None => None
    end.

  Definition relax_round (k : K.t) (m : dbm) : dbm :=
    M.merge (round_row k (row_of (M.get k m))) m M.empty.

  Definition column_present (k : K.t) (row : M.t Z) : bool :=
    match M.get k row with Some _ => true | None => false end.

  Definition pivot_present (k : K.t) (m : dbm) : bool :=
    match M.get k m with
    | Some _ => true
    | None => M.existsb (column_present k) m
    end.

  (** Materialize the zero walk only when its code already belongs to the matrix. *)
  Definition fw_round (k : K.t) (m : dbm) : dbm :=
    let seed := if pivot_present k m then add_cons k k 0%Z m else m in
    relax_round k seed.

  Definition remember_key (acc : M.t unit * list K.t) (k : K.t)
      : M.t unit * list K.t :=
    match M.get k (fst acc) with
    | Some _ => acc
    | None => (M.set k tt (fst acc), k :: snd acc)
    end.

  (** A map-backed set preserves the signature's reverse first-occurrence order. *)
  Definition pivot_keys (m : dbm) : list K.t :=
    let es := M.elements m in
    snd (fold_left remember_key
      (map fst es ++ flat_map (fun kv => map fst (M.elements (snd kv))) es)
      (M.empty, nil)).

  Definition nonnegative (k : K.t) (m : dbm) : bool :=
    match entry m k k with Some d => (0 <=? d)%Z | None => true end.

  Fixpoint close_pivots (ks : list K.t) (m : dbm) : t :=
    match ks with
    | nil => Reached m
    | k :: ks =>
      let next := fw_round k m in
      if nonnegative k next then close_pivots ks next else Unreached
    end.

  Definition close (m : dbm) : t :=
    let ks := pivot_keys m in
    match close_pivots ks m with
    | Unreached => Unreached
    | Reached next =>
      if forallb (fun k => nonnegative k next) ks then Reached next else Unreached
    end.

  Definition increment_row (i : K.t) (d : Z) (exit : M.t Z)
      (r : option (M.t Z)) (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row =>
      Some (match M.get i row with
        | Some a => M.merge (via_bound (a + d)%Z) row exit
        | None => row
        end)
    | None => None
    end.

  (** Each new path uses the inserted edge between its old prefix and suffix. *)
  Definition incr_close (i j : K.t) (d : Z) (m : dbm) : t :=
    let seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m)) in
    let next := M.merge (increment_row i d (row_of (M.get j seed))) seed M.empty in
    if andb (nonnegative i next) (nonnegative j next) then Reached next else Unreached.

  (** A difference has at most one positive and one negative unit coefficient. *)
  Definition difference_pair (cs : list (X.t * Z)) : option (K.t * K.t) :=
    match cs with
    | nil => Some (None, None)
    | (x, a) :: nil =>
      if (a =? 1)%Z then Some (None, Some x) else
      if (a =? -1)%Z then Some (Some x, None) else None
    | (x, a) :: (y, b) :: nil =>
      if andb (a =? 1)%Z (b =? -1)%Z then Some (Some y, Some x) else
      if andb (a =? -1)%Z (b =? 1)%Z then Some (Some x, Some y) else None
    | _ => None
    end.

  (** Recognizing bounded coefficient patterns avoids traversing unsupported forms. *)
  Definition difference_forms (l r : lin X.t) : option (K.t * K.t) :=
    match coef l, coef r with
    | nil, rs =>
      match difference_pair rs with Some (i, j) => Some (j, i) | None => None end
    | ls, nil => difference_pair ls
    | (x, a) :: nil, (y, b) :: nil =>
      if andb (a =? 1)%Z (b =? 1)%Z then Some (Some y, Some x) else
      if andb (a =? -1)%Z (b =? -1)%Z then Some (Some x, Some y) else None
    | _, _ => None
    end.

  Definition form_exact (m : dbm) (f : lin X.t) (r : wrapr) : bool :=
    match r with
    | NoWrap => true
    | _ => rel_wrap_exact r (form_bounds m f)
    end.

  Definition refine (i j : K.t) (d : Z) (s : t) : t :=
    match s with Unreached => Unreached | Reached m => incr_close i j d m end.

  Definition assume_cmp (c : cmp) (i j : K.t) (d : Z) (s : t) : t :=
    match c with
    | CLe => refine i j d s
    | CLt => refine i j (d - 1)%Z s
    | CEq => refine j i (-d)%Z (refine i j d s)
    end.

  Definition assume_atom (s : t) (a : atom X.t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      match difference_forms (al a) (ar a) with
      | None => s
      | Some (i, j) =>
        if andb (form_exact m (al a) (alw a)) (form_exact m (ar a) (arw a)) then
          assume_cmp (acmp a) i j (cst (ar a) - cst (al a))%Z s
        else s
      end
    end.

  Definition assume (g : L.guard) (es : list (term L.op X.t)) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached _ => fold_left assume_atom (F.atoms_of g es) s
    end.

  Definition copy_source (f : lin X.t) : option K.t :=
    match coef f with
    | nil => Some None
    | (x, a) :: nil => if (a =? 1)%Z then Some (Some x) else None
    | _ => None
    end.

  Definition shift_column_row (x : X.t) (d : Z)
      (r : option (M.t Z)) (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row =>
      Some (match M.get (Some x) row with
        | Some old => M.set (Some x) (old + d)%Z row
        | None => row
        end)
    | None => None
    end.

  Definition shift_columns (x : X.t) (d : Z) (m : dbm) : dbm :=
    M.merge (shift_column_row x d) m M.empty.

  Definition shift_bound (d : Z) (old : option Z) (_ : option Z) : option Z :=
    match old with Some z => Some (z - d)%Z | None => None end.

  (** Self assignment shifts one column up and the corresponding row down. *)
  Definition shift (x : X.t) (d : Z) (m : dbm) : dbm :=
    let next := shift_columns x d m in
    match M.get (Some x) next with
    | Some row => M.set (Some x) (M.merge (shift_bound d) row M.empty) next
    | None => next
    end.

  Definition assign_copy (x : X.t) (source : K.t) (d : Z) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      if K.eqb source (Some x) then Reached (shift x d m) else
      refine (Some x) source (-d)%Z (refine source (Some x) d (havoc x s))
    end.

  Definition add_range (x : X.t) (bounds : bnd * bnd) (s : t) : t :=
    let lower := match fst bounds with
      | Fin lo => refine (Some x) None (-lo)%Z s
      | _ => s
      end in
    match snd bounds with
    | Fin hi => refine None (Some x) hi lower
    | _ => lower
    end.

  Definition assign (x : X.t) (e : term L.op X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      match F.lin_of e with
      | None => havoc x s
      | Some (f, r) =>
        let bounds := form_bounds m f in
        match copy_source f with
        | Some source =>
          if rel_wrap_exact r bounds then assign_copy x source (cst f) s else
          add_range x (rel_wrap_bounds r bounds) (havoc x s)
        | None => add_range x (rel_wrap_bounds r bounds) (havoc x s)
        end
      end
    end.
End ZoneCode.

Module Zone (X : KEY) (K : KEY with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) <: ZONE X K M L N F.
  Include ZoneCode X K M L F.
  (** Rank counts finite entries at stored codes, independently of labels. *)
  Definition wrank (_ : wparam) (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0 (map (fun p =>
        match M.find p m with Some row => length (M.codes row) | None => 0 end) (M.codes m))
    end.
  Definition vz (v : X.t -> Z) (i : K.t) : Z :=
    match i with None => 0%Z | Some x => v x end.
  Definition models (m : dbm) (v : X.t -> Z) : Prop :=
    forall i j d, entry m i j = Some d -> (vz v j - vz v i <= d)%Z.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached m => models m v end.

  (** An absent row supplies no finite bound. *)
  Lemma get_row_of : forall r k,
    M.get k (row_of r) = match r with Some row => M.get k row | None => None end.
  Proof.
    intros [row|] k; [reflexivity|apply M.get_empty].
  Qed.

  (** Insertion changes only the selected entry, taking its minimum with the new bound. *)
  Lemma entry_add_cons : forall i j d m a b,
    entry (add_cons i j d m) a b =
    if K.eqb a i then
      if K.eqb b j then Some (lower_bound d (entry m i j)) else entry m a b
    else entry m a b.
  Proof.
    intros i j d m a b. unfold entry, add_cons.
    destruct (K.eqb_spec a i) as [Ha | Ha].
    - subst a. rewrite M.get_set_same.
      destruct (K.eqb_spec b j) as [Hb | Hb].
      + subst b. rewrite M.get_set_same, get_row_of. reflexivity.
      + rewrite M.get_set_other by exact Hb. apply get_row_of.
    - rewrite M.get_set_other by exact Ha. reflexivity.
  Qed.

  (** A minimum retains every value below both its finite operands. *)
  Lemma lower_bound_holds : forall value d old,
    (value <= d)%Z -> (forall z, old = Some z -> (value <= z)%Z) ->
    (value <= lower_bound d old)%Z.
  Proof.
    intros value d [z|] Hnew Hold; cbn [lower_bound].
    - apply Z.min_glb; [exact Hnew|apply Hold; reflexivity].
    - exact Hnew.
  Qed.

  (** Adding a satisfied constraint preserves the numeric store. *)
  Lemma models_add_cons : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> models (add_cons i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew a b z Hentry.
    rewrite entry_add_cons in Hentry.
    destruct (K.eqb_spec a i) as [Ha | Ha].
    - subst a. destruct (K.eqb_spec b j) as [Hb | Hb].
      + subst b. inversion Hentry; subst z.
        apply lower_bound_holds; [exact Hnew|]. intros old Hold. now apply Hmodel.
      + now apply Hmodel.
    - now apply Hmodel.
  Qed.

  (** A row relaxation selects the old bound or the two-edge path through its pivot. *)
  Lemma entry_relax_round : forall k m i j,
    entry (relax_round k m) i j =
    match entry m i k with
    | Some a => via_bound a (entry m i j) (entry m k j)
    | None => entry m i j
    end.
  Proof.
    intros k m i j. unfold relax_round, entry.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get i m) as [row|]; cbn [round_row].
    - destruct (M.get k row) as [a|]; [|reflexivity].
      rewrite M.get_merge by reflexivity. rewrite get_row_of. reflexivity.
    - reflexivity.
  Qed.

  (** Relaxation retains values below the old bound and the proposed path bound. *)
  Lemma via_bound_holds : forall value a old next,
    (forall d, old = Some d -> (value <= d)%Z) ->
    (forall z, next = Some z -> (value <= a + z)%Z) ->
    forall d, via_bound a old next = Some d -> (value <= d)%Z.
  Proof.
    intros value a old [z|] Hold Hnext d Hentry; cbn [via_bound] in Hentry.
    - inversion Hentry; subst d. apply lower_bound_holds.
      + apply Hnext. reflexivity.
      + exact Hold.
    - now apply Hold.
  Qed.

  (** Every path added by one sparse round follows from two existing edges. *)
  Lemma relax_round_models : forall k m v, models m v -> models (relax_round k m) v.
  Proof.
    intros k m v Hmodel i j d Hentry. rewrite entry_relax_round in Hentry.
    destruct (entry m i k) as [a|] eqn:Hik.
    - eapply via_bound_holds; [| |exact Hentry].
      + intros old Hold. now apply Hmodel.
      + intros z Hkj. pose proof (Hmodel i k a Hik).
        pose proof (Hmodel k j z Hkj). lia.
    - now apply Hmodel.
  Qed.

  (** Adding a zero walk and relaxing through it preserves every model. *)
  Lemma fw_round_models : forall k m v, models m v -> models (fw_round k m) v.
  Proof.
    intros k m v Hmodel. unfold fw_round. apply relax_round_models.
    destruct (pivot_present k m); [|exact Hmodel].
    apply models_add_cons; [exact Hmodel|lia].
  Qed.

  (** A matrix with a model cannot have a negative diagonal. *)
  Lemma nonnegative_models : forall k m v, models m v -> nonnegative k m = true.
  Proof.
    intros k m v Hmodel. unfold nonnegative.
    destruct (entry m k k) as [d|] eqn:Hentry; [|reflexivity].
    apply Z.leb_le. specialize (Hmodel k k d Hentry). lia.
  Qed.

  (** Every completed prefix of the pivot loop preserves the original model. *)
  Lemma close_pivots_models : forall ks m v,
    models m v -> ngamma (close_pivots ks m) v.
  Proof.
    intro ks. induction ks as [|k ks IH]; intros m v Hmodel; cbn [close_pivots].
    - exact Hmodel.
    - pose proof (fw_round_models k m v Hmodel) as Hnext.
      rewrite (nonnegative_models k (fw_round k m) v Hnext). now apply IH.
  Qed.

  (** The full closure loop and its final diagonal check preserve every model. *)
  Lemma close_models : forall m v, models m v -> ngamma (close m) v.
  Proof.
    intros m v Hmodel. unfold close.
    pose proof (close_pivots_models (pivot_keys m) m v Hmodel) as Hnext.
    destruct (close_pivots (pivot_keys m) m) as [|next]; [exact Hnext|].
    assert (Hdiag : forallb (fun k => nonnegative k next) (pivot_keys m) = true).
    { apply forallb_forall. intros k Hkey. now apply (nonnegative_models k next v). }
    rewrite Hdiag. exact Hnext.
  Qed.

  (** An incremental update combines an incoming prefix, the new edge and an outgoing suffix. *)
  Lemma entry_increment : forall i j d m a b,
    entry (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) a b =
    match entry m a i with
    | Some prefix => via_bound (prefix + d)%Z (entry m a b) (entry m j b)
    | None => entry m a b
    end.
  Proof.
    intros i j d m a b. unfold entry.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get a m) as [row|]; cbn [increment_row].
    - destruct (M.get i row) as [prefix|]; [|reflexivity].
      rewrite M.get_merge by reflexivity. rewrite get_row_of. reflexivity.
    - reflexivity.
  Qed.

  (** Every incremental path follows from the matrix and the added constraint. *)
  Lemma increment_models : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z ->
    models (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) v.
  Proof.
    intros i j d m v Hmodel Hnew a b bound Hentry. rewrite entry_increment in Hentry.
    destruct (entry m a i) as [prefix|] eqn:Hai.
    - eapply via_bound_holds; [| |exact Hentry].
      + intros old Hold. now apply Hmodel.
      + intros z Hjb. pose proof (Hmodel a i prefix Hai).
        pose proof (Hmodel j b z Hjb). lia.
    - now apply Hmodel.
  Qed.

  (** Incremental closure and its diagonal checks preserve each model of the new constraint. *)
  Lemma incr_close_models : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew.
    assert (Hseed : models (add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m))) v).
    { apply models_add_cons; [|exact Hnew].
      apply models_add_cons; [|lia]. apply models_add_cons; [exact Hmodel|lia]. }
    pose proof (increment_models i j d _ v Hseed Hnew) as Hnext.
    unfold incr_close.
    rewrite (nonnegative_models i _ v Hnext), (nonnegative_models j _ v Hnext).
    exact Hnext.
  Qed.

  (** Forgetting removes exactly the row and column of the chosen variable. *)
  Lemma entry_havoc : forall x m i j,
    entry (M.merge (forget_row x) (M.remove (Some x) m) M.empty) i j =
    if K.eqb i (Some x) then None else
      if K.eqb j (Some x) then None else entry m i j.
  Proof.
    intros x m i j. unfold entry. rewrite M.get_merge by reflexivity.
    rewrite M.get_empty. destruct (K.eqb_spec i (Some x)) as [Hi | Hi].
    - subst i. rewrite M.get_remove_same. reflexivity.
    - rewrite M.get_remove_other by exact Hi.
      destruct (M.get i m) as [row|]; cbn [forget_row].
      + destruct (K.eqb_spec j (Some x)) as [Hj | Hj].
        * subst j. apply M.get_remove_same.
        * apply M.get_remove_other. exact Hj.
      + destruct (K.eqb j (Some x)); reflexivity.
  Qed.

  (** A variable update leaves every other zone coordinate unchanged. *)
  Lemma vz_update_other : forall x st c i,
    i <> Some x ->
    vz (fun y => N.num (upd X.eqb st x c y)) i = vz (fun y => N.num (st y)) i.
  Proof.
    intros x st c [y|] Hne; [|reflexivity].
    change (N.num (if X.eqb y x then c else st y) = N.num (st y)).
    destruct (X.eqb_spec y x) as [Heq | Heq]; [subst y; contradiction Hne; reflexivity|].
    reflexivity.
  Qed.

  (** The assigned coordinate reads the new numeric value. *)
  Lemma vz_update_same : forall x st c,
    vz (fun y => N.num (upd X.eqb st x c y)) (Some x) = N.num c.
  Proof.
    intros x st c. unfold vz, upd.
    destruct (X.eqb_spec x x); [reflexivity|congruence].
  Qed.

  (** Column translation changes exactly the finite entries targeting the assigned variable. *)
  Lemma entry_shift_columns : forall x d m i j,
    entry (shift_columns x d m) i j =
    if K.eqb j (Some x) then option_map (fun z => (z + d)%Z) (entry m i j)
    else entry m i j.
  Proof.
    intros x d m i j. unfold entry, shift_columns.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get i m) as [row|]; cbn [shift_column_row].
    - destruct (M.get (Some x) row) as [old|] eqn:Hcol.
      + destruct (K.eqb_spec j (Some x)) as [Hj|Hj].
        * subst j. rewrite M.get_set_same, Hcol. reflexivity.
        * rewrite M.get_set_other by exact Hj. reflexivity.
      + destruct (K.eqb_spec j (Some x)) as [Hj|Hj].
        * subst j. now rewrite Hcol.
        * reflexivity.
    - destruct (K.eqb j (Some x)); reflexivity.
  Qed.

  (** Row translation subtracts the offset after the column translation. *)
  Lemma entry_shift : forall x d m i j,
    entry (shift x d m) i j =
    if K.eqb i (Some x) then
      option_map (fun z => (z - d)%Z) (entry (shift_columns x d m) i j)
    else entry (shift_columns x d m) i j.
  Proof.
    intros x d m i j. unfold shift.
    destruct (M.get (Some x) (shift_columns x d m)) as [row|] eqn:Hrow.
    - destruct (K.eqb_spec i (Some x)) as [Hi|Hi].
      + subst i. unfold entry. rewrite M.get_set_same, Hrow.
        rewrite M.get_merge by reflexivity. rewrite M.get_empty.
        destruct (M.get j row); reflexivity.
      + unfold entry. rewrite M.get_set_other by exact Hi. reflexivity.
    - destruct (K.eqb_spec i (Some x)) as [Hi|Hi]; [subst i|reflexivity].
      unfold entry. now rewrite Hrow.
  Qed.

  (** Translating one variable preserves every old constraint under its concrete update. *)
  Lemma shift_models : forall x offset m st c,
    models m (fun y => N.num (st y)) ->
    N.num c = (N.num (st x) + offset)%Z ->
    models (shift x offset m) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x offset m st c Hmodel Hvalue i j d Hentry.
    rewrite entry_shift, !entry_shift_columns in Hentry.
    destruct (K.eqb_spec i (Some x)) as [Hi|Hi];
      destruct (K.eqb_spec j (Some x)) as [Hj|Hj].
    - subst i j. destruct (entry m (Some x) (Some x)) as [z|] eqn:Hz;
        [|discriminate Hentry].
      inversion Hentry; subst d. specialize (Hmodel (Some x) (Some x) z Hz).
      cbn [vz] in Hmodel |- *. lia.
    - subst i. destruct (entry m (Some x) j) as [z|] eqn:Hz;
        [|discriminate Hentry].
      inversion Hentry; subst d. specialize (Hmodel (Some x) j z Hz).
      rewrite vz_update_same, (vz_update_other x st c j Hj).
      cbn [vz] in Hmodel. lia.
    - subst j. destruct (entry m i (Some x)) as [z|] eqn:Hz;
        [|discriminate Hentry].
      inversion Hentry; subst d. specialize (Hmodel i (Some x) z Hz).
      rewrite vz_update_same, (vz_update_other x st c i Hi).
      cbn [vz] in Hmodel. lia.
    - destruct (entry m i j) as [z|] eqn:Hz; [|discriminate Hentry].
      inversion Hentry; subst d. rewrite !vz_update_other by assumption.
      exact (Hmodel i j z Hz).
  Qed.

  (** Raw entry lookup ignores labels and also treats an absent row as empty. *)
  Definition raw_entry (m : dbm) (p q : positive) : option Z :=
    M.find q (row_of (M.find p m)).

  Lemma row_leb_spec : forall a b,
    row_leb a b = true <->
    forall q, bound_leb (M.find q (row_of a)) (M.find q (row_of b)) = true.
  Proof.
    intros a b. unfold row_leb. apply M.forall2b_spec. reflexivity.
  Qed.

  Lemma row_leb_empty : row_leb None None = true.
  Proof.
    apply row_leb_spec. intros q. cbn [row_of]. rewrite M.find_empty. reflexivity.
  Qed.

  (** Entrywise comparison visits actual codes, including codes with inconsistent labels. *)
  Lemma leb_entries : forall ma mb,
    leb (Reached ma) (Reached mb) = true <->
    forall p q, bound_leb (raw_entry ma p q) (raw_entry mb p q) = true.
  Proof.
    intros ma mb. cbn [leb].
    rewrite (M.forall2b_spec _ _ row_leb ma mb row_leb_empty).
    split; intros H p; apply row_leb_spec; apply H.
  Qed.

  Lemma raw_entry_empty : forall p q, raw_entry M.empty p q = None.
  Proof.
    intros p q. unfold raw_entry. rewrite M.find_empty. apply M.find_empty.
  Qed.

  Lemma raw_entry_get : forall m i j,
    raw_entry m (K.encode i) (K.encode j) = entry m i j.
  Proof.
    intros m i j. unfold raw_entry, entry.
    rewrite <- (M.get_find _ i m). destruct (M.get i m) as [row|]; cbn [row_of].
    - symmetry. apply M.get_find.
    - apply M.find_empty.
  Qed.

  Lemma bound_leb_refl : forall a, bound_leb a a = true.
  Proof.
    intros [z|]; cbn [bound_leb]; [apply Z.leb_refl|reflexivity].
  Qed.

  Lemma bound_leb_trans : forall a b c,
    bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_leb]; try congruence.
    repeat rewrite Z.leb_le. lia.
  Qed.

  Lemma raw_entry_join : forall ma mb p q,
    raw_entry (M.merge row_join ma mb) p q =
    bound_join (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_join row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_empty. destruct (M.find q ra); reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma raw_entry_meet : forall ma mb p q,
    raw_entry (M.merge row_meet ma mb) p q =
    bound_meet (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_meet row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_empty. destruct (M.find q ra); reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma raw_entry_widen : forall ma mb p q,
    raw_entry (M.merge row_widen ma mb) p q =
    bound_widen (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_widen row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_merge by reflexivity. reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma bound_join_ub_l : forall a b, bound_leb a (bound_join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_join]; try reflexivity.
    apply Z.leb_le, Z.le_max_l.
  Qed.

  Lemma bound_join_ub_r : forall a b, bound_leb b (bound_join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_join]; try reflexivity.
    apply Z.leb_le, Z.le_max_r.
  Qed.

  Lemma bound_meet_lb_l : forall a b, bound_leb (bound_meet a b) a = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_meet]; try reflexivity.
    - apply Z.leb_le, Z.le_min_l.
    - apply Z.leb_refl.
  Qed.

  Lemma bound_meet_greatest : forall a b c,
    bound_leb c a = true -> bound_leb c b = true ->
    bound_leb c (bound_meet a b) = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_leb bound_meet]; try congruence.
    repeat rewrite Z.leb_le. intros Ha Hb. apply Z.min_glb; assumption.
  Qed.

  Lemma bound_widen_ub_l : forall a b, bound_leb a (bound_widen a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_widen bound_leb]; try reflexivity.
    destruct (b <=? a)%Z; cbn [bound_leb]; [apply Z.leb_refl|reflexivity].
  Qed.

  Lemma bound_widen_ub_r : forall a b, bound_leb b (bound_widen a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_widen bound_leb]; try reflexivity.
    destruct (b <=? a)%Z eqn:Hle; cbn [bound_leb]; [exact Hle|reflexivity].
  Qed.

  (** Every sparse matrix compares below itself, even when labels are inconsistent. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros [|m]; [reflexivity|]. apply leb_entries. intros p q. apply bound_leb_refl.
  Qed.

  (** Entrywise comparison is transitive. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|ma] [|mb] [|mc]; cbn [leb]; try congruence.
    change (leb (Reached ma) (Reached mb) = true ->
      leb (Reached mb) (Reached mc) = true -> leb (Reached ma) (Reached mc) = true).
    rewrite !leb_entries. intros Hab Hbc p q. eapply bound_leb_trans; [apply Hab|apply Hbc].
  Qed.

  (** The unreachable state is below every state. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros a. reflexivity.
  Qed.

  (** The bottom predicate recognizes the unreachable constructor. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.

  (** Every state recognized as bottom is least. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [|ma] b Hbot; [reflexivity|discriminate Hbot].
  Qed.

  (** Joining weakens every bound supplied by the left state. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|ma] [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros p q. rewrite raw_entry_join. apply bound_join_ub_l.
  Qed.

  (** Joining weakens every bound supplied by the right state. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|ma] [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros p q. rewrite raw_entry_join. apply bound_join_ub_r.
  Qed.

  (** The empty matrix imposes no upper bounds. *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros [|m]; [reflexivity|]. apply leb_entries. intros p q.
    rewrite raw_entry_empty. destruct (raw_entry m p q); reflexivity.
  Qed.

  (** Widening keeps or discards each old finite bound. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle; [apply leb_refl|].
    destruct a as [|ma], b as [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros i j. rewrite raw_entry_widen. apply bound_widen_ub_l.
  Qed.

  (** A retained old bound is also an upper bound for the candidate. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle; [exact Hle|].
    destruct a as [|ma], b as [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros i j. rewrite raw_entry_widen. apply bound_widen_ub_r.
  Qed.

  (** A stable candidate returns the exact old representation. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hle. unfold widen. now rewrite Hle.
  Qed.
  (** A row contributes the distinct pairs formed from its actual stored codes. *)
  Definition row_entry_codes (m : dbm) (p : positive) : list (positive * positive) :=
    match M.find p m with
    | Some row => map (pair p) (M.codes row)
    | None => nil
    end.

  (** Finite-entry counting ignores stored labels at both map levels. *)
  Definition entry_codes (m : dbm) : list (positive * positive) :=
    flat_map (row_entry_codes m) (M.codes m).

  (** The first coordinate of every row entry is its outer stored code. *)
  Lemma row_entry_first : forall m p pq, In pq (row_entry_codes m p) -> fst pq = p.
  Proof.
    intros m p pq Hin. unfold row_entry_codes in Hin.
    destruct (M.find p m) as [row|]; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin]]. now subst pq.
  Qed.

  (** Pairing distinct column codes with one row code preserves distinctness. *)
  Lemma paired_codes_nodup : forall (p : positive) (qs : list positive),
    NoDup qs -> NoDup (map (pair p) qs).
  Proof.
    intros p qs Hcodes. induction Hcodes as [|q qs Hfresh Hcodes IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [r [Heq Hr]]. injection Heq as Heq. subst r. exact (Hfresh Hr).
  Qed.

  (** Distinct outer codes yield disjoint lists of finite-entry coordinates. *)
  Lemma rows_entry_nodup : forall m ps, NoDup ps ->
    NoDup (flat_map (row_entry_codes m) ps).
  Proof.
    intros m ps Hcodes. induction Hcodes as [|p ps Hfresh Hcodes IH].
    - constructor.
    - cbn [flat_map]. apply NoDup_app; [|exact IH|].
      + unfold row_entry_codes. destruct (M.find p m) as [row|].
        * apply paired_codes_nodup, M.codes_nodup.
        * constructor.
      + intros pq Hfirst Htail. apply in_flat_map in Htail.
        destruct Htail as [q [Hq Hentry]].
        pose proof (row_entry_first m p pq Hfirst) as Hp.
        pose proof (row_entry_first m q pq Hentry) as Hsame.
        apply Hfresh. rewrite <- Hp, Hsame. exact Hq.
  Qed.

  (** No finite raw-code coordinate is counted twice. *)
  Lemma entry_codes_nodup : forall m, NoDup (entry_codes m).
  Proof.
    intro m. unfold entry_codes. apply rows_entry_nodup, M.codes_nodup.
  Qed.

  (** A coordinate occurs exactly when its raw entry is finite. *)
  Lemma entry_codes_spec : forall m p q,
    In (p, q) (entry_codes m) <-> raw_entry m p q <> None.
  Proof.
    intros m p q. split.
    - intro Hin. unfold entry_codes in Hin. apply in_flat_map in Hin.
      destruct Hin as [i [Hi Hin]]. unfold row_entry_codes in Hin.
      destruct (M.find i m) as [row|] eqn:Hrow; [|contradiction].
      apply in_map_iff in Hin. destruct Hin as [j [Heq Hj]].
      injection Heq as Hip Hjq. subst i j.
      unfold raw_entry. rewrite Hrow. cbn [row_of]. now apply M.codes_spec.
    - intro Hentry. unfold raw_entry in Hentry.
      destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hentry.
      + unfold entry_codes. apply in_flat_map. exists p. split.
        * apply M.codes_spec. rewrite Hrow. discriminate.
        * unfold row_entry_codes. rewrite Hrow. apply in_map_iff. exists q.
          split; [reflexivity|now apply M.codes_spec].
      + rewrite M.find_empty in Hentry. contradiction.
  Qed.

  (** The flattened coordinate count is the released widening rank. *)
  Lemma entry_codes_rank : forall p m, length (entry_codes m) = wrank p (Reached m).
  Proof.
    intros p m. unfold entry_codes, wrank.
    induction (M.codes m) as [|q qs IH].
    - reflexivity.
    - cbn [flat_map map fold_right]. rewrite length_app, IH.
      unfold row_entry_codes. destruct (M.find q m); cbn; rewrite ?length_map; reflexivity.
  Qed.

  (** Every finite entry retained by widening was already finite in the old matrix. *)
  Lemma widen_codes_incl : forall ma mb,
    incl (entry_codes (M.merge row_widen ma mb)) (entry_codes ma).
  Proof.
    intros ma mb [p q] Hin. apply entry_codes_spec in Hin. apply entry_codes_spec.
    rewrite raw_entry_widen in Hin.
    destruct (raw_entry ma p q) as [d|]; [discriminate|].
    cbn [bound_widen] in Hin. contradiction.
  Qed.

  (** A failed finite Boolean scan provides a member on which its predicate fails. *)
  Lemma forallb_failure : forall (A : Type) (test : A -> bool) xs,
    forallb test xs = false -> exists x, In x xs /\ test x = false.
  Proof.
    intros A test xs. induction xs as [|x xs IH]; intro Hfalse.
    - discriminate Hfalse.
    - cbn in Hfalse. destruct (test x) eqn:Hx.
      + destruct (IH Hfalse) as [y [Hy Htest]]. exists y. split; [now right|exact Htest].
      + exists x. split; [now left|exact Hx].
  Qed.

  (** Failure of entrywise inclusion identifies an old finite bound that widening discards. *)
  Lemma leb_failure_entry : forall ma mb,
    leb (Reached mb) (Reached ma) = false ->
    exists p q, raw_entry ma p q <> None /\
      bound_leb (raw_entry mb p q) (raw_entry ma p q) = false.
  Proof.
    intros ma mb Hfalse.
    destruct (forallb (fun pq =>
      bound_leb (raw_entry mb (fst pq) (snd pq)) (raw_entry ma (fst pq) (snd pq)))
      (entry_codes ma)) eqn:Hscan.
    - assert (Htrue : leb (Reached mb) (Reached ma) = true).
      { apply leb_entries. intros p q.
        destruct (raw_entry ma p q) as [d|] eqn:Hentry.
        - rewrite forallb_forall in Hscan.
          assert (Hin : In (p, q) (entry_codes ma)).
          { apply entry_codes_spec. rewrite Hentry. discriminate. }
          specialize (Hscan (p, q) Hin). cbn in Hscan. now rewrite Hentry in Hscan.
        - destruct (raw_entry mb p q); reflexivity. }
      congruence.
    - apply forallb_failure in Hscan. destruct Hscan as [[p q] [Hin Hfailed]].
      exists p, q. split; [now apply entry_codes_spec|exact Hfailed].
  Qed.

  (** An unstable finite old bound is dropped by the widening callback. *)
  Lemma bound_widen_drops : forall a b,
    bound_leb b a = false -> bound_widen a b = None.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_widen]; try congruence.
    intro Hle. now rewrite Hle.
  Qed.

  (** Every unstable widening removes at least one distinct stored coordinate. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|ma] [|mb] Hbot Hunstable; try discriminate.
    unfold widen. rewrite Hunstable.
    change (wrank p (Reached (M.merge row_widen ma mb)) < wrank p (Reached ma)).
    destruct (leb_failure_entry ma mb Hunstable) as [i [j [Hfinite Hfailed]]].
    assert (Hmissing : ~ In (i, j) (entry_codes (M.merge row_widen ma mb))).
    { intro Hin. apply entry_codes_spec in Hin. rewrite raw_entry_widen in Hin.
      rewrite (bound_widen_drops _ _ Hfailed) in Hin. contradiction. }
    assert (Hlength : length ((i, j) :: entry_codes (M.merge row_widen ma mb)) <=
      length (entry_codes ma)).
    { apply NoDup_incl_length.
      - constructor; [exact Hmissing|apply entry_codes_nodup].
      - intros pq [Hpq | Hin].
        + subst pq. now apply entry_codes_spec.
        + exact (widen_codes_incl ma mb pq Hin). }
    change (S (length (entry_codes (M.merge row_widen ma mb))) <=
      length (entry_codes ma)) in Hlength.
    rewrite (entry_codes_rank p (M.merge row_widen ma mb)) in Hlength.
    rewrite (entry_codes_rank p ma) in Hlength. exact Hlength.
  Qed.

  (** Stable widening preserves rank and unstable widening strictly lowers it. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hstable.
    - rewrite (widen_stable p a b Hstable). reflexivity.
    - apply Nat.lt_le_incl. now apply wrank_widen.
  Qed.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros [|ma] [|mb] Hle; try (split; reflexivity); try discriminate Hle.
    pose proof (proj1 (leb_entries mb ma) Hle) as Hentries.
    split; apply leb_entries; intros p q; cbn [narrow meet].
    - rewrite raw_entry_meet. apply bound_meet_greatest; [apply Hentries|apply bound_leb_refl].
    - rewrite raw_entry_meet. apply bound_meet_lb_l.
  Qed.

  (** Every bound accepted by comparison follows from a source bound. *)
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof.
    intros [|ma] [|mb] v Hle Hmodel; try contradiction; try discriminate Hle.
    pose proof (proj1 (leb_entries ma mb) Hle) as Hentries. intros i j d Hentry.
    specialize (Hentries (K.encode i) (K.encode j)).
    rewrite !raw_entry_get, Hentry in Hentries.
    destruct (entry ma i j) as [c|] eqn:Hsource; [|discriminate Hentries].
    cbn [bound_leb] in Hentries. apply Z.leb_le in Hentries.
    specialize (Hmodel i j c Hsource). lia.
  Qed.

  (** The unreachable constructor has no numeric models. *)
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof.
    intros v Hmodel. exact Hmodel.
  Qed.

  (** Every numeric store satisfies an empty matrix. *)
  Lemma ngamma_top : forall v, ngamma top v.
  Proof.
    intros v i j d Hentry. unfold entry in Hentry.
    rewrite M.get_empty in Hentry. discriminate Hentry.
  Qed.
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x [|m] st c Hmodel; [exact Hmodel|].
    intros i j d Hentry. rewrite entry_havoc in Hentry.
    destruct (K.eqb_spec i (Some x)) as [Hi | Hi]; [discriminate Hentry|].
    destruct (K.eqb_spec j (Some x)) as [Hj | Hj]; [discriminate Hentry|].
    rewrite !vz_update_other by assumption. now apply Hmodel.
  Qed.
  (** Unary entries supply lower and upper bounds for each variable. *)
  Lemma variable_bounds_sound : forall m v x, models m v ->
    in_bnd (fst (variable_bounds m x)) (snd (variable_bounds m x)) (v x).
  Proof.
    intros m v x Hmodel. unfold variable_bounds.
    destruct (entry m (Some x) None) as [lo|] eqn:Hlo;
      destruct (entry m None (Some x)) as [hi|] eqn:Hhi;
      cbn [fst snd in_bnd]; split; try exact I.
    - pose proof (Hmodel (Some x) None lo Hlo). cbn [vz] in *. lia.
    - pose proof (Hmodel None (Some x) hi Hhi). cbn [vz] in *. lia.
    - pose proof (Hmodel (Some x) None lo Hlo). cbn [vz] in *. lia.
    - pose proof (Hmodel None (Some x) hi Hhi). cbn [vz] in *. lia.
  Qed.

  Lemma form_bounds_sound : forall m v f, models m v ->
    in_bnd (fst (form_bounds m f)) (snd (form_bounds m f)) (eval_lin v f).
  Proof.
    intros m v f Hmodel. apply rel_form_bounds_sound.
    intro x. now apply variable_bounds_sound.
  Qed.

  (** Recognized coefficient lists denote exactly their selected difference. *)
  Lemma difference_pair_sound : forall cs v i j,
    difference_pair cs = Some (i, j) -> eval_coef v cs = (vz v j - vz v i)%Z.
  Proof.
    intros cs v i j Hpair.
    destruct cs as [|[x a] cs].
    - inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
    - destruct cs as [|[y b] cs].
      + unfold difference_pair in Hpair.
        destruct (a =? 1)%Z eqn:Ha.
        * apply Z.eqb_eq in Ha. subst a. inversion Hpair; subst.
          unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (a =? -1)%Z eqn:Hneg; [|discriminate Hpair].
          apply Z.eqb_eq in Hneg. subst a. inversion Hpair; subst.
          unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
      + destruct cs as [|p cs]; [|discriminate Hpair].
        unfold difference_pair in Hpair.
        destruct (andb (a =? 1)%Z (b =? -1)%Z) eqn:Hsigns.
        * apply andb_true_iff in Hsigns. destruct Hsigns as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (andb (a =? -1)%Z (b =? 1)%Z) eqn:Hother;
            [|discriminate Hpair].
          apply andb_true_iff in Hother. destruct Hother as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  (** Recognition subtracts the two coefficient sums without changing their meaning. *)
  Lemma difference_forms_sound : forall l r v i j,
    difference_forms l r = Some (i, j) ->
    (eval_coef v (coef l) - eval_coef v (coef r) = vz v j - vz v i)%Z.
  Proof.
    intros [ls lc] [rs rc] v i j Hpair. unfold difference_forms in Hpair.
    cbn [coef] in Hpair |- *. destruct ls as [|[x a] xs].
    - destruct (difference_pair rs) as [[u w]|] eqn:Hrecognized;
        [|discriminate Hpair].
      pose proof (difference_pair_sound rs v u w Hrecognized) as Hvalue.
      inversion Hpair; subst. unfold eval_coef in *. cbn in *. lia.
    - destruct rs as [|[y b] ys].
      + pose proof (difference_pair_sound ((x, a) :: xs) v i j Hpair) as Hvalue.
        unfold eval_coef in *. cbn in *. lia.
      + destruct xs as [|p xs], ys as [|q ys]; try discriminate Hpair.
        destruct (andb (a =? 1)%Z (b =? 1)%Z) eqn:Hsigns.
        * apply andb_true_iff in Hsigns. destruct Hsigns as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (andb (a =? -1)%Z (b =? -1)%Z) eqn:Hother;
            [|discriminate Hpair].
          apply andb_true_iff in Hother. destruct Hother as [Ha Hb].
          apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hb. subst a b.
          inversion Hpair; subst. unfold eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  (** An accepted range check justifies interpreting a wrapped form as an integer form. *)
  Lemma form_exact_sound : forall m f r v, models m v -> form_exact m f r = true ->
    wrap_into r (eval_lin v f) = eval_lin v f.
  Proof.
    intros m f [|lo hi] v Hmodel Hexact; [reflexivity|].
    apply (rel_wrap_exact_sound (WrapTo lo hi) (form_bounds m f)).
    - now apply form_bounds_sound.
    - exact Hexact.
  Qed.

  (** A refinement retains every current model satisfying the new difference bound. *)
  Lemma refine_sound : forall i j d s v, ngamma s v ->
    (vz v j - vz v i <= d)%Z -> ngamma (refine i j d s) v.
  Proof.
    intros i j d [|m] v Hmodel Hbound; [exact Hmodel|].
    now apply incr_close_models.
  Qed.

  Lemma assume_cmp_sound : forall c i j d s v, ngamma s v ->
    (match c with
     | CLe => (vz v j - vz v i <= d)%Z
     | CLt => (vz v j - vz v i < d)%Z
     | CEq => (vz v j - vz v i = d)%Z
     end) -> ngamma (assume_cmp c i j d s) v.
  Proof.
    intros [| |] i j d s v Hmodel Hbound; unfold assume_cmp.
    - now apply refine_sound.
    - apply refine_sound; [exact Hmodel|lia].
    - apply refine_sound; [apply refine_sound; [exact Hmodel|lia]|lia].
  Qed.

  (** Each supported atom contributes only difference constraints implied by that atom. *)
  Lemma assume_atom_sound : forall s a v, ngamma s v -> atom_holds v a ->
    ngamma (assume_atom s a) v.
  Proof.
    intros [|m] a v Hmodel Hatom; [exact Hmodel|].
    unfold assume_atom. destruct (difference_forms (al a) (ar a))
      as [[i j]|] eqn:Hpair; [|exact Hmodel].
    destruct (andb (form_exact m (al a) (alw a))
      (form_exact m (ar a) (arw a))) eqn:Hexact; [|exact Hmodel].
    apply andb_true_iff in Hexact. destruct Hexact as [Hl Hr].
    unfold atom_holds in Hatom.
    rewrite (form_exact_sound m (al a) (alw a) v Hmodel Hl),
      (form_exact_sound m (ar a) (arw a) v Hmodel Hr) in Hatom.
    pose proof (difference_forms_sound (al a) (ar a) v i j Hpair) as Hdiff.
    apply assume_cmp_sound; [exact Hmodel|].
    unfold eval_lin in Hatom. destruct (acmp a); lia.
  Qed.

  (** A sequence of satisfied atoms retains the same concrete model. *)
  Lemma assume_atoms_sound : forall atoms s v, ngamma s v ->
    Forall (atom_holds v) atoms -> ngamma (fold_left assume_atom atoms s) v.
  Proof.
    induction atoms as [|a atoms IH]; intros s v Hmodel Hatoms.
    - exact Hmodel.
    - inversion Hatoms as [|a' atoms' Ha Htail]; subst.
      apply IH; [now apply assume_atom_sound|exact Htail].
  Qed.

  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof.
    intros g es [|m] st cs Hmodel Heval Hholds; [exact Hmodel|].
    apply assume_atoms_sound; [exact Hmodel|].
    now apply (F.atoms_sound g es st cs).
  Qed.

  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof.
    intros e [|m] st c Hmodel Heval; [contradiction|].
    unfold range. destruct (F.lin_of e) as [[f r]|] eqn:Hlinear.
    - rewrite (F.lin_sound st e c f r Heval Hlinear).
      apply rel_wrap_bounds_sound. now apply form_bounds_sound.
    - unfold in_bnd. cbn. tauto.
  Qed.

  (** A recognized source is either the zero node or a variable with coefficient one. *)
  Lemma copy_source_sound : forall f source v, copy_source f = Some source ->
    eval_lin v f = (vz v source + cst f)%Z.
  Proof.
    intros [cs c] source v Hsource. unfold copy_source in Hsource.
    cbn [coef] in Hsource. destruct cs as [|[x a] cs].
    - inversion Hsource; subst. unfold eval_lin, eval_coef, vz. cbn. reflexivity.
    - destruct cs as [|p cs]; [|discriminate Hsource].
      destruct (a =? 1)%Z eqn:Ha; [|discriminate Hsource].
      apply Z.eqb_eq in Ha. subst a. inversion Hsource; subst.
      unfold eval_lin, eval_coef, vz. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  (** Exact copy transfer handles self-translation separately from forgetting. *)
  Lemma assign_copy_sound : forall x source d s st c,
    ngamma s (fun y => N.num (st y)) ->
    N.num c = (vz (fun y => N.num (st y)) source + d)%Z ->
    ngamma (assign_copy x source d s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x source d [|m] st c Hmodel Hvalue; [exact Hmodel|].
    unfold assign_copy. destruct (K.eqb_spec source (Some x)) as [Heq|Hne].
    - subst source. now apply shift_models.
    - apply refine_sound.
      + apply refine_sound.
        * now apply havoc_sound.
        * rewrite vz_update_same, (vz_update_other x st c source Hne). lia.
      + rewrite vz_update_same, (vz_update_other x st c source Hne). lia.
  Qed.

  (** Adding finite range endpoints retains every value inside those endpoints. *)
  Lemma add_range_sound : forall x bounds s v, ngamma s v ->
    in_bnd (fst bounds) (snd bounds) (v x) -> ngamma (add_range x bounds s) v.
  Proof.
    intros x [lo hi] s v Hmodel Hbounds. unfold add_range, in_bnd in *.
    destruct lo, hi; cbn [fst snd] in *; try contradiction;
      repeat (apply refine_sound; [|cbn [vz]; lia]); exact Hmodel.
  Qed.

  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x e [|m] st c Hmodel Heval; [exact Hmodel|].
    unfold assign. destruct (F.lin_of e) as [[f r]|] eqn:Hlinear;
      [|now apply havoc_sound].
    pose proof (F.lin_sound st e c f r Heval Hlinear) as Hvalue.
    pose proof (form_bounds_sound m (fun y => N.num (st y)) f Hmodel) as Hbounds.
    assert (Hwrapped : in_bnd
      (fst (rel_wrap_bounds r (form_bounds m f)))
      (snd (rel_wrap_bounds r (form_bounds m f))) (N.num c)).
    { rewrite Hvalue. now apply rel_wrap_bounds_sound. }
    destruct (copy_source f) as [source|] eqn:Hsource.
    - destruct (rel_wrap_exact r (form_bounds m f)) eqn:Hexact.
      + apply assign_copy_sound; [exact Hmodel|].
        rewrite Hvalue, (rel_wrap_exact_sound r (form_bounds m f) _ Hbounds Hexact).
        now apply copy_source_sound.
      + apply add_range_sound; [now apply havoc_sound|].
        change (in_bnd (fst (rel_wrap_bounds r (form_bounds m f)))
          (snd (rel_wrap_bounds r (form_bounds m f)))
          (vz (fun y => N.num (upd X.eqb st x c y)) (Some x))).
        now rewrite vz_update_same.
    - apply add_range_sound; [now apply havoc_sound|].
      change (in_bnd (fst (rel_wrap_bounds r (form_bounds m f)))
        (snd (rel_wrap_bounds r (form_bounds m f)))
        (vz (fun y => N.num (upd X.eqb st x c y)) (Some x))).
      now rewrite vz_update_same.
  Qed.
  Lemma entry_spec : forall m i j,
    entry m i j = match M.get i m with Some row => M.get j row | None => None end.
  Proof.
    reflexivity.
  Qed.

  (** Reached matrices use the difference semantics. *)
  Lemma ngamma_reached : forall m v, ngamma (Reached m) v <-> models m v.
  Proof.
    reflexivity.
  Qed.

  (** Unreachable matrices have no numeric models. *)
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof.
    intros v Hmodel. exact Hmodel.
  Qed.
End Zone.

Module ZoneT (X : KEY_T) (K : KEY_T with Definition t := option X.t
      with Definition encode := option_code X.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    <: ZONE_ALL X K M L N F.
  Include Zone X K M L N F.
  Definition wsize (_ : wparam) : nat := 0.
  Definition rows (m : dbm) : list (M.t Z) :=
    flat_map (fun p => match M.find p m with Some r => r :: nil | None => nil end) (M.codes m).
  Definition support (m : dbm) : list positive :=
    fold_left (fun acc p => if existsb (Pos.eqb p) acc then acc else p :: acc)
      (M.codes m ++ flat_map M.codes (rows m)) nil.
  Definition supp (m : dbm) : nat := length (support m).
  Definition b (m : dbm) : nat := fold_right Nat.max 0 (map Pos.size_nat (support m)).
  Definition ell (m : dbm) : nat := fold_right Nat.max 0 (flat_map (fun r =>
    map (fun q => match M.find q r with Some z => Z.size_nat z | None => 0 end) (M.codes r))
    (rows m)).
  Definition skel (m : dbm) : nat := M.nodes m + fold_right Nat.add 0 (map M.nodes (rows m)).
  Definition skels (s : t) : nat := match s with Unreached => 0 | Reached m => skel m end.
  Definition keys (m : dbm) : list K.t :=
    fold_left (fun acc x => if existsb (K.eqb x) acc then acc else x :: acc)
      (map fst (M.elements m) ++
       flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m)) nil.
  TimeFun keys.
  Definition dbm_wf (m : dbm) : Prop :=
    M.wf m /\ forall p r, M.find p m = Some r -> M.wf r.
  Definition ns (s : t) := match s with Unreached => 0 | Reached m => supp m end.
  Definition bs (s : t) := match s with Unreached => 0 | Reached m => b m end.
  Definition ells (s : t) := match s with Unreached => 0 | Reached m => ell m end.
  Definition size (s : t) : nat :=
    (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Definition lin_bits (e : term L.op X.t) : nat :=
    match F.lin_of e with
    | Some (f, r) =>
      fold_right Nat.max (Z.size_nat (cst f))
        (map (fun p => Z.size_nat (snd p)) (coef f)) +
      match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end
    | None => 0
    end.
  Definition wunits (s : t) : nat := (ns s + 1) ^ 2.
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) +
      skels s +
      (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    length (F.atoms_of g es) * (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
      (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
      N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition range_bits (e : term L.op X.t) (s : t) : nat :=
    ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
  TimeFun row_of.
  TimeFun bound_leb.
  TimeFun row_leb.
  TimeFun bound_join.
  TimeFun row_join.
  TimeFun bound_meet.
  TimeFun row_meet.
  TimeFun bound_widen.
  TimeFun row_widen.
  TimeFun forget_row.
  TimeFun lower_bound.
  TimeFun via_bound.
  TimeFun round_row.
  TimeFun column_present.
  TimeFun pivot_present.
  TimeFun remember_key.
  TimeFun pivot_keys.
  TimeFun bot.
  TimeFun top.
  TimeFun meet.
  TimeFun leb.
  TimeFun join.
  TimeFun is_bot.
  TimeFun widen.
  TimeFun narrow.
  TimeFun havoc.
  TimeFun entry.
  TimeFun variable_bounds.
  TimeFun form_bounds.
  TimeFun range.
  TimeFun add_cons.
  TimeFun relax_round.
  TimeFun fw_round.
  TimeFun nonnegative.
  TimeFun close_pivots.
  TimeFun close.
  TimeFun increment_row.
  TimeFun incr_close.
  TimeFun difference_pair.
  TimeFun difference_forms.
  TimeFun form_exact.
  TimeFun refine.
  TimeFun assume_cmp.
  TimeFun assume_atom.
  TimeFun assume.
  TimeFun copy_source.
  TimeFun shift_column_row.
  TimeFun shift_columns.
  TimeFun shift_bound.
  TimeFun shift.
  TimeFun assign_copy.
  TimeFun add_range.
  TimeFun assign.
  (** One coefficient covers the two sparse-map levels and widening's inclusion check. *)
  Definition c_lat : N := (256 * (M.c_map + 1) * (M.c_map + 1))%N.
  (** The common lattice coefficient is positive. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. nia.
  Qed.
  (** Numeric transfers pay for map operations and the two key equality tests. *)
  Definition c_num : N :=
    (16777216 * (M.c_map + K.c_key + X.c_key + 1) *
      (M.c_map + K.c_key + X.c_key + 1))%N.
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Matrix primitives share one concrete constant for lookup and update costs. *)
  Definition c_zone : N := (65536 * (M.c_map + 1) * (M.c_map + 1))%N.

  Lemma T_row_of_le : forall r, (T_row_of r <= 1)%N.
  Proof.
    intros [row|]; time_step.
  Qed.

  Lemma T_lower_bound_le : forall d old,
    (T_lower_bound d old <= N.of_nat (Z.size_nat d) + 5)%N.
  Proof.
    intros d [z|]; time_step.
  Qed.

  Lemma T_entry_le : forall m i j,
    (T_entry m i j <= c_zone * N.of_nat (K.bits i + K.bits j + 1))%N.
  Proof.
    intros m i j. unfold c_zone. time_step.
  Qed.
  Lemma T_add_cons_le : forall i j d m,
    (T_add_cons i j d m <= c_zone * N.of_nat
      (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  Proof.
    intros i j d m. unfold c_zone. time_step.
  Qed.
  Definition closed (m : dbm) : Prop :=
    (forall i, In (K.encode i) (support m) -> entry m i i = Some 0%Z) /\
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z).
  Fixpoint chain_weight (m : dbm) (i : K.t) (ks : list K.t) (j : K.t) : option Z :=
    match ks with
    | nil => entry m i j
    | k :: ks =>
      match entry m i k, chain_weight m k ks j with
      | Some a, Some z => Some (a + z)%Z
      | _, _ => None
      end
    end.
  Definition same_entries (a b : t) : Prop :=
    match a, b with
    | Reached ma, Reached mb => forall i j, entry ma i j = entry mb i j
    | Unreached, Unreached => True
    | _, _ => False
    end.
  Definition k_zone : N := (1024 * (M.c_map + 1) * (M.c_map + 1))%N.

  (** Deduplication retains exactly the input and accumulator members. *)
  Lemma dedup_membership : forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) -> forall xs acc x,
    In x (fold_left (fun seen y => if existsb (eqb y) seen then seen else y :: seen)
      xs acc) <-> In x xs \/ In x acc.
  Proof.
    intros A eqb Heq xs. induction xs as [|a xs IH]; intros acc x.
    - cbn. tauto.
    - cbn [fold_left]. destruct (existsb (eqb a) acc) eqn:Hseen.
      + assert (Ha : In a acc).
        { apply existsb_exists in Hseen. destruct Hseen as [y [Hy Hay]].
          apply Heq in Hay. now subst y. }
        rewrite IH. cbn [In]. split.
        * tauto.
        * intros [[Hax | Hin] | Hin].
          -- subst x. now right.
          -- now left.
          -- now right.
      + rewrite IH. cbn [In]. tauto.
  Qed.

  (** Deduplication preserves a duplicate-free accumulator. *)
  Lemma dedup_nodup : forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) -> forall xs acc,
    NoDup acc ->
    NoDup (fold_left (fun seen y => if existsb (eqb y) seen then seen else y :: seen)
      xs acc).
  Proof.
    intros A eqb Heq xs. induction xs as [|a xs IH]; intros acc Hacc.
    - exact Hacc.
    - cbn [fold_left]. destruct (existsb (eqb a) acc) eqn:Hseen; apply IH.
      + exact Hacc.
      + constructor; [|exact Hacc]. intro Ha.
        assert (Hfound : existsb (eqb a) acc = true).
        { apply existsb_exists. exists a. split; [exact Ha|apply Heq; reflexivity]. }
        congruence.
  Qed.

  (** Support contains every outer code and every code of a stored row. *)
  Lemma support_spec : forall m p,
    In p (support m) <-> In p (M.codes m) \/ In p (flat_map M.codes (rows m)).
  Proof.
    intros m p. unfold support.
    rewrite (dedup_membership positive Pos.eqb Pos.eqb_eq), in_app_iff.
    cbn. tauto.
  Qed.

  (** A list maximum bounds each selected member. *)
  Lemma maximum_member : forall (A : Type) (f : A -> nat) xs x,
    In x xs -> f x <= fold_right Nat.max 0 (map f xs).
  Proof.
    intros A f xs. induction xs as [|a xs IH]; intros x Hin.
    - contradiction.
    - cbn in Hin |- *. destruct Hin as [Hax | Hin].
      + subst x. apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH x Hin)|apply Nat.le_max_r].
  Qed.

  (** A uniform bound on summands bounds their sum by length times that bound. *)
  Lemma sum_members_bound : forall (A : Type) (f : A -> nat) xs upper,
    (forall x, In x xs -> f x <= upper) ->
    fold_right Nat.add 0 (map f xs) <= length xs * upper.
  Proof.
    intros A f xs. induction xs as [|a xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. assert (Ha : f a <= upper) by (apply Hbound; now left).
      assert (Htail : fold_right Nat.add 0 (map f xs) <= length xs * upper).
      { apply IH. intros x Hin. apply Hbound. now right. }
      lia.
  Qed.

  (** Every supported code fits the matrix key-bit bound. *)
  Lemma support_bits : forall m p, In p (support m) -> Pos.size_nat p <= b m.
  Proof.
    intros m p Hin. unfold b. now apply maximum_member.
  Qed.

  (** Distinct stored codes inject into any support containing them. *)
  Lemma codes_support_length : forall A (r : M.t A) m,
    (forall p, In p (M.codes r) -> In p (support m)) -> length (M.codes r) <= supp m.
  Proof.
    intros A r m Hin. unfold supp. apply NoDup_incl_length.
    - apply M.codes_nodup.
    - exact Hin.
  Qed.

  (** A map whose codes lie in the support has a bounded skeleton. *)
  Lemma nodes_support : forall A (r : M.t A) m,
    (forall p, In p (M.codes r) -> In p (support m)) ->
    M.nodes r <= supp m * (b m + 1).
  Proof.
    intros A r m Hin.
    pose proof (M.nodes_le_codes A r) as Hnodes.
    pose proof (codes_support_length A r m Hin) as Hlength.
    assert (Hsum : fold_right Nat.add 0
      (map (fun p => Pos.size_nat p + 1) (M.codes r)) <=
      length (M.codes r) * (b m + 1)).
    { apply sum_members_bound. intros p Hp.
      pose proof (support_bits m p (Hin p Hp)). lia. }
    nia.
  Qed.

  (** Row collection retains at most one row for each outer code. *)
  Lemma rows_length : forall m, length (rows m) <= length (M.codes m).
  Proof.
    intro m. unfold rows. induction (M.codes m) as [|p ps IH].
    - reflexivity.
    - cbn. destruct (M.find p m); cbn; lia.
  Qed.

  (** Every successful raw row lookup is present in the row collection. *)
  Lemma row_in_rows : forall m p row, M.find p m = Some row -> In row (rows m).
  Proof.
    intros m p row Hrow. unfold rows. apply in_flat_map. exists p. split.
    - apply M.codes_spec. rewrite Hrow. discriminate.
    - rewrite Hrow. now left.
  Qed.

  (** The stored codes cover the skeleton even when labels do not match their codes. *)
  Lemma skel_le : forall m, skel m <= (supp m + 1)^2 * (b m + 1).
  Proof.
    intro m.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Houter) as Hlength.
    pose proof (rows_length m) as Hrows.
    assert (Hsum : fold_right Nat.add 0 (map M.nodes (rows m)) <=
      length (rows m) * (supp m * (b m + 1))).
    { apply sum_members_bound. intros row Hrow. apply nodes_support.
      intros p Hp. apply support_spec. right. apply in_flat_map.
      exists row. now split. }
    unfold skel. cbn [Nat.pow]. nia.
  Qed.
  (** A collected row is witnessed by a successful lookup at an outer stored code. *)
  Lemma rows_find : forall m row,
    In row (rows m) <-> exists p, M.find p m = Some row.
  Proof.
    intros m row. split.
    - intro Hin. unfold rows in Hin. apply in_flat_map in Hin.
      destruct Hin as [p [Hp Hin]]. destruct (M.find p m) as [r|] eqn:Hrow.
      + cbn in Hin. destruct Hin as [Heq | Hempty]; [subst r|contradiction].
        now exists p.
      + contradiction.
    - intros [p Hrow]. exact (row_in_rows m p row Hrow).
  Qed.

  (** Support records row codes and column codes independently of their stored labels. *)
  Lemma support_find : forall m p, In p (support m) <->
    M.find p m <> None \/ exists q, raw_entry m q p <> None.
  Proof.
    intros m p. rewrite support_spec. split.
    - intros [Houter | Hinner].
      + left. now apply M.codes_spec.
      + right. apply in_flat_map in Hinner. destruct Hinner as [row [Hrow Hp]].
        apply rows_find in Hrow. destruct Hrow as [q Hrow]. exists q.
        unfold raw_entry. rewrite Hrow. cbn [row_of]. now apply M.codes_spec.
    - intros [Houter | [q Hinner]].
      + left. now apply M.codes_spec.
      + right. unfold raw_entry in Hinner.
        destruct (M.find q m) as [row|] eqn:Hrow; cbn [row_of] in Hinner.
        * apply in_flat_map. exists row. split.
          -- exact (row_in_rows m q row Hrow).
          -- now apply M.codes_spec.
        * rewrite M.find_empty in Hinner. contradiction.
  Qed.

  (** The deduplicated support contains each stored code once. *)
  Lemma support_nodup : forall m, NoDup (support m).
  Proof.
    intro m. unfold support. apply (dedup_nodup positive Pos.eqb Pos.eqb_eq).
    constructor.
  Qed.

  (** A common upper bound for list members bounds their maximum. *)
  Lemma maximum_bound : forall (A : Type) (f : A -> nat) xs upper,
    (forall x, In x xs -> f x <= upper) -> fold_right Nat.max 0 (map f xs) <= upper.
  Proof.
    intros A f xs. induction xs as [|x xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. apply Nat.max_lub.
      + apply Hbound. now left.
      + apply IH. intros y Hin. apply Hbound. now right.
  Qed.

  (** Equal support membership gives equal support size and key-bit bounds. *)
  Lemma support_sizes : forall ma mb,
    (forall p, In p (support ma) <-> In p (support mb)) ->
    supp ma = supp mb /\ b ma = b mb.
  Proof.
    intros ma mb Hsame. split.
    - unfold supp. apply Nat.le_antisymm; apply NoDup_incl_length;
        try apply support_nodup.
      + intros p Hin. now apply Hsame.
      + intros p Hin. now apply Hsame.
    - apply Nat.le_antisymm.
      + unfold b at 1. apply maximum_bound. intros p Hin.
        apply support_bits. now apply Hsame.
      + unfold b at 1. apply maximum_bound. intros p Hin.
        apply support_bits. now apply Hsame.
  Qed.

  (** Constraint insertion preserves all outer codes and adds its source code. *)
  Lemma find_add_cons_presence : forall i j d m p,
    M.find p (add_cons i j d m) <> None <-> p = K.encode i \/ M.find p m <> None.
  Proof.
    intros i j d m p. unfold add_cons. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hkey.
    - apply Pos.eqb_eq in Hkey. subst p. split; [intros; now left|intros; discriminate].
    - apply Pos.eqb_neq in Hkey. tauto.
  Qed.

  (** Constraint insertion changes finite-entry presence only at its supplied coordinates. *)
  Lemma raw_add_cons_presence : forall i j d m p q,
    raw_entry (add_cons i j d m) p q <> None <->
    (p = K.encode i /\ q = K.encode j) \/ raw_entry m p q <> None.
  Proof.
    intros i j d m p q. unfold raw_entry, add_cons. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hrow.
    - apply Pos.eqb_eq in Hrow. subst p. cbn [row_of]. rewrite M.find_set.
      destruct (Pos.eqb q (K.encode j)) eqn:Hcol.
      + apply Pos.eqb_eq in Hcol. subst q. split.
        * intros. left. now split.
        * intros. discriminate.
      + apply Pos.eqb_neq in Hcol. rewrite M.get_find. tauto.
    - apply Pos.eqb_neq in Hrow. tauto.
  Qed.

  (** Insertion adds only its two endpoint codes to the support. *)
  Lemma support_add_cons : forall i j d m p,
    In p (support (add_cons i j d m)) <->
    p = K.encode i \/ p = K.encode j \/ In p (support m).
  Proof.
    intros i j d m p. split.
    - intro Hin. apply support_find in Hin. destruct Hin as [Hrow | [q Hentry]].
      + apply find_add_cons_presence in Hrow. destruct Hrow as [Heq | Hrow].
        * now left.
        * right. right. apply support_find. now left.
      + apply raw_add_cons_presence in Hentry. destruct Hentry as [[Hq Hp] | Hentry].
        * right. now left.
        * right. right. apply support_find. right. now exists q.
    - intros [Hrow | [Hcol | Hin]]; apply support_find.
      + left. apply find_add_cons_presence. now left.
      + right. exists (K.encode i). apply raw_add_cons_presence. left. now split.
      + apply support_find in Hin. destruct Hin as [Hrow | [q Hentry]].
        * left. apply find_add_cons_presence. now right.
        * right. exists q. apply raw_add_cons_presence. now right.
  Qed.

  (** The pivot test recognizes precisely the supplied key's membership in raw support. *)
  Lemma pivot_present_support : forall k m,
    pivot_present k m = true <-> In (K.encode k) (support m).
  Proof.
    intros k m. unfold pivot_present. rewrite M.get_find.
    destruct (M.find (K.encode k) m) as [row|] eqn:Hrow.
    - split; [intros|reflexivity]. apply support_find. left. rewrite Hrow. discriminate.
    - rewrite (M.existsb_spec (M.t Z) (column_present k) m). split.
      + intros [p [row [Hp Hcol]]]. apply support_find. right. exists p.
        unfold raw_entry. rewrite Hp. cbn [row_of].
        unfold column_present in Hcol. rewrite M.get_find in Hcol.
        destruct (M.find (K.encode k) row); congruence.
      + intro Hin. apply support_find in Hin. destruct Hin as [Hfound | [p Hentry]].
        * rewrite Hrow in Hfound. contradiction.
        * unfold raw_entry in Hentry. destruct (M.find p m) as [r|] eqn:Hp.
          -- exists p, r. split; [exact Hp|]. unfold column_present. rewrite M.get_find.
             cbn [row_of] in Hentry. destruct (M.find (K.encode k) r); congruence.
          -- cbn [row_of] in Hentry. rewrite M.find_empty in Hentry. contradiction.
  Qed.

  (** Relaxation retains precisely the existing outer rows. *)
  Lemma find_relax_presence : forall k m p,
    M.find p (relax_round k m) <> None <-> M.find p m <> None.
  Proof.
    intros k m p. unfold relax_round. rewrite M.find_merge by reflexivity.
    rewrite M.find_empty. destruct (M.find p m); cbn [round_row]; split; congruence.
  Qed.

  (** A relaxed coordinate is old or joins an incoming and an outgoing pivot edge. *)
  Lemma raw_relax_presence : forall k m p q,
    raw_entry (relax_round k m) p q <> None <->
    raw_entry m p q <> None \/
      (raw_entry m p (K.encode k) <> None /\ raw_entry m (K.encode k) q <> None).
  Proof.
    intros k m p q. unfold raw_entry, relax_round.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [round_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode k) row) as [a|] eqn:Hentry.
      + rewrite M.find_merge by reflexivity.
        destruct (M.find q row), (M.find q (row_of (M.find (K.encode k) m)));
          cbn [via_bound]; intuition congruence.
      + tauto.
    - rewrite !M.find_empty. tauto.
  Qed.

  (** Relaxing through a pivot adds no code and deletes no supported code. *)
  Lemma support_relax : forall k m p,
    In p (support (relax_round k m)) <-> In p (support m).
  Proof.
    intros k m p. rewrite !support_find. split.
    - intros [Hrow | [q Hentry]].
      + left. now apply find_relax_presence in Hrow.
      + apply raw_relax_presence in Hentry. right.
        destruct Hentry as [Hentry | [Hprefix Hsuffix]].
        * now exists q.
        * now exists (K.encode k).
    - intros [Hrow | [q Hentry]].
      + left. now apply find_relax_presence.
      + right. exists q. apply raw_relax_presence. now left.
  Qed.

  (** Materializing an already-supported pivot diagonal leaves support unchanged. *)
  Lemma support_round : forall k m p,
    In p (support (fw_round k m)) <-> In p (support m).
  Proof.
    intros k m p. unfold fw_round. rewrite support_relax.
    destruct (pivot_present k m) eqn:Hpresent; [|reflexivity].
    apply pivot_present_support in Hpresent. rewrite support_add_cons.
    split.
    - intros [Heq | [Heq | Hin]]; subst; assumption.
    - intro Hin. right. now right.
  Qed.

  (** Every member of a list is bounded by its maximum. *)
  Lemma maximum_raw_member : forall xs n,
    In n xs -> n <= fold_right Nat.max 0 xs.
  Proof.
    intros xs. induction xs as [|x xs IH]; intros n Hin.
    - contradiction.
    - cbn in Hin. cbn. destruct Hin as [Heq | Hin].
      + subst n. apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH n Hin)|apply Nat.le_max_r].
  Qed.

  (** A uniform upper bound for a list bounds its maximum. *)
  Lemma maximum_raw_bound : forall xs upper,
    (forall n, In n xs -> n <= upper) -> fold_right Nat.max 0 xs <= upper.
  Proof.
    intros xs. induction xs as [|x xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. apply Nat.max_lub.
      + apply Hbound. now left.
      + apply IH. intros n Hin. apply Hbound. now right.
  Qed.

  (** Every finite raw entry satisfies the matrix's integer-bit bound. *)
  Lemma ell_entry : forall m p q z,
    raw_entry m p q = Some z -> Z.size_nat z <= ell m.
  Proof.
    intros m p q z Hentry. unfold raw_entry in Hentry.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hentry.
    - unfold ell. apply maximum_raw_member. apply in_flat_map.
      exists row. split; [exact (row_in_rows m p row Hrow)|].
      apply in_map_iff. exists q. split.
      + now rewrite Hentry.
      + apply M.codes_spec. rewrite Hentry. discriminate.
    - rewrite M.find_empty in Hentry. discriminate.
  Qed.

  (** Bounding every finite raw entry bounds the matrix's integer-bit maximum. *)
  Lemma ell_bound : forall m upper,
    (forall p q z, raw_entry m p q = Some z -> Z.size_nat z <= upper) ->
    ell m <= upper.
  Proof.
    intros m upper Hbound. unfold ell. apply maximum_raw_bound.
    intros n Hin. apply in_flat_map in Hin. destruct Hin as [row [Hrow Hin]].
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hq]].
    apply rows_find in Hrow. destruct Hrow as [p Hrow].
    destruct (M.find q row) as [z|] eqn:Hentry.
    - subst n. apply (Hbound p q z). unfold raw_entry. rewrite Hrow. exact Hentry.
    - cbn in Heq. lia.
  Qed.

  (** An integer's absolute value fits strictly below its bit-length power of two. *)
  Lemma zbits_upper : forall z, Z.abs_nat z < 2 ^ Z.size_nat z.
  Proof.
    intros [|p|p]; cbn [Z.abs_nat Z.size_nat].
    - change (0 < 1). lia.
    - apply Pos.size_nat_upper.
    - apply Pos.size_nat_upper.
  Qed.

  (** Any strict power-of-two bound also bounds the integer's bit length. *)
  Lemma zbits_least : forall z n,
    Z.abs_nat z < 2 ^ n -> Z.size_nat z <= n.
  Proof.
    intros [|p|p] n Hbound; cbn [Z.abs_nat Z.size_nat] in *.
    - lia.
    - now apply Pos.size_nat_least.
    - now apply Pos.size_nat_least.
  Qed.

  (** A bit allowance is equivalently a strict magnitude allowance. *)
  Lemma zbits_abs_bound : forall z bits,
    Z.size_nat z <= bits -> Z.abs_nat z < 2 ^ bits.
  Proof.
    intros z bits Hbits. eapply Nat.lt_le_trans; [apply zbits_upper|].
    apply Nat.pow_le_mono_r; lia.
  Qed.

  (** The constant seed and every coefficient are bounded by the form maximum. *)
  Lemma form_bits_constant : forall f, Z.size_nat (cst f) <= F.form_bits f.
  Proof.
    intros [cs c]. unfold F.form_bits. cbn [coef cst].
    induction cs as [|p cs IH]; cbn; [lia|].
    eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
  Qed.

  Lemma form_bits_coefficient : forall f p,
    In p (coef f) -> Z.size_nat (snd p) <= F.form_bits f.
  Proof.
    intros [cs c] p. unfold F.form_bits. cbn [coef cst].
    induction cs as [|q cs IH]; intros Hin; [contradiction|].
    cbn in Hin |- *. destruct Hin as [Heq|Hin].
    - subst q. pose proof (Nat.le_max_l
        (X.bits (fst p) + Z.size_nat (snd p))
        (fold_right Nat.max (Z.size_nat c)
          (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) cs))). lia.
    - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
  Qed.

  (** Negation does not change an integer's stored magnitude. *)
  Lemma zbits_opp : forall z, Z.size_nat (-z)%Z = Z.size_nat z.
  Proof. intros [|p|p]; reflexivity. Qed.

  Lemma variable_bounds_abs : forall m x,
    rel_bounds_abs (2 ^ ell m) (variable_bounds m x).
  Proof.
    intros m x. unfold variable_bounds, rel_bounds_abs, rel_bound_abs.
    destruct (entry m (Some x) None) as [lo|] eqn:Hlo;
      destruct (entry m None (Some x)) as [hi|] eqn:Hhi;
      cbn [fst snd]; split; try exact I; apply zbits_abs_bound.
    - rewrite zbits_opp. eapply ell_entry. rewrite raw_entry_get. exact Hlo.
    - eapply ell_entry. rewrite raw_entry_get. exact Hhi.
    - rewrite zbits_opp. eapply ell_entry. rewrite raw_entry_get. exact Hlo.
    - eapply ell_entry. rewrite raw_entry_get. exact Hhi.
  Qed.

  (** Summing at most n products adds only log2(n) plus one magnitude bit. *)
  Lemma affine_magnitude_allowance : forall count nodes coeff_bits entry_bits,
    count <= nodes -> 1 <= nodes ->
    (count + 1) * 2 ^ coeff_bits * 2 ^ entry_bits <=
      2 ^ (entry_bits + coeff_bits + Nat.log2 nodes + 2).
  Proof.
    intros count nodes coeff_bits entry_bits Hcount Hnodes.
    pose proof (Nat.log2_spec nodes ltac:(lia)) as [_ Hlog].
    assert (Hcountpow : count + 1 <= 2 ^ (Nat.log2 nodes + 1)).
    { replace (Nat.log2 nodes + 1) with (S (Nat.log2 nodes)) by lia. lia. }
    assert (Hproduct : (count + 1) * 2 ^ coeff_bits * 2 ^ entry_bits <=
      2 ^ (Nat.log2 nodes + 1) * 2 ^ coeff_bits * 2 ^ entry_bits).
    { apply Nat.mul_le_mono_r. apply Nat.mul_le_mono_r. exact Hcountpow. }
    eapply Nat.le_trans; [exact Hproduct|].
    rewrite <- !Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
  Qed.

  (** Recognized affine intervals respect the logarithmic range bit allowance. *)
  Lemma form_range_abs : forall e m f r,
    F.lin_of e = Some (f, r) ->
    rel_bounds_abs (2 ^ range_bits e (Reached m)) (form_bounds m f).
  Proof.
    intros e m f r Hlin. destruct (F.lin_of_size e f r Hlin) as [Hcount Hbits].
    assert (Hposc : 0 < 2 ^ F.bits_e e).
    { pose proof (Nat.pow_nonzero 2 (F.bits_e e) ltac:(lia)). lia. }
    assert (Hposx : 0 < 2 ^ ell m).
    { pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia. }
    eapply rel_bounds_abs_mono.
    - unfold range_bits, ells. apply affine_magnitude_allowance; [exact Hcount|].
      destruct e; cbn [tsize]; lia.
    - unfold form_bounds. apply rel_form_bounds_abs; try assumption.
      + apply zbits_abs_bound. pose proof (form_bits_constant f). lia.
      + apply Forall_forall. intros p Hin. apply zbits_abs_bound.
        pose proof (form_bits_coefficient f p Hin). lia.
      + apply variable_bounds_abs.
  Qed.

  (** A valid wrapping interval is bounded by its explicitly charged endpoints. *)
  Lemma wrap_range_abs : forall r bounds bits,
    F.wrap_bits r <= bits -> rel_bounds_abs (2 ^ bits) bounds ->
    rel_bounds_abs (2 ^ bits) (rel_wrap_bounds r bounds).
  Proof.
    intros [|lo hi] bounds bits Hbits Hbounds; [exact Hbounds|].
    unfold F.wrap_bits in Hbits. unfold rel_wrap_bounds.
    destruct (lo <=? hi)%Z; unfold rel_bounds_abs, rel_bound_abs;
      cbn [fst snd]; split; try exact I; apply zbits_abs_bound; lia.
  Qed.

  Lemma range_abs : forall e s,
    rel_bounds_abs (2 ^ range_bits e s) (range e s).
  Proof.
    intros e [|m]; [split; exact I|].
    unfold range. destruct (F.lin_of e) as [[f r]|] eqn:Hlin; [|split; exact I].
    apply wrap_range_abs.
    - destruct (F.lin_of_size e f r Hlin) as [_ Hbits]. unfold range_bits. lia.
    - now apply (form_range_abs e m f r).
  Qed.

  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof.
    intros e s. pose proof (range_abs e s) as Hrange.
    assert (Hbits :
      match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
      match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end <=
      2 * range_bits e s).
    { unfold rel_bounds_abs, rel_bound_abs in Hrange.
      destruct (fst (range e s)), (snd (range e s));
        destruct Hrange as [Hlo Hhi]; try apply zbits_least in Hlo;
        try apply zbits_least in Hhi; lia. }
    assert (Hconstant : (2 <= c_num)%N) by (unfold c_num; nia).
    eapply N.le_trans; [apply time_of_nat_le; exact Hbits|].
    rewrite Nat2N.inj_mul. rewrite Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.

  (** Adding two integers with a common bit bound needs at most one further bit. *)
  Lemma zbits_add_bound : forall x y upper,
    Z.size_nat x <= upper -> Z.size_nat y <= upper ->
    Z.size_nat (x + y)%Z <= upper + 1.
  Proof.
    intros x y upper Hx Hy.
    pose proof (zbits_upper x) as Hxabs. pose proof (zbits_upper y) as Hyabs.
    assert (Hxp : 2 ^ Z.size_nat x <= 2 ^ upper).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hyp : 2 ^ Z.size_nat y <= 2 ^ upper).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Htriangle : Z.abs_nat (x + y)%Z <= Z.abs_nat x + Z.abs_nat y).
    { apply (proj2 (Nat2Z.inj_le _ _)).
      rewrite Nat2Z.inj_add, !Zabs2Nat.id_abs. apply Z.abs_triangle. }
    apply zbits_least. replace (upper + 1) with (S upper) by lia.
    cbn [Nat.pow]. lia.
  Qed.

  (** Tightening a bound selects one of its inputs and preserves their common bit bound. *)
  Lemma lower_bound_size : forall d old upper,
    Z.size_nat d <= upper ->
    (forall z, old = Some z -> Z.size_nat z <= upper) ->
    Z.size_nat (lower_bound d old) <= upper.
  Proof.
    intros d [z|] upper Hd Hold; cbn [lower_bound].
    - destruct (Z.leb_spec0 d z) as [Hle | Hgt].
      + now rewrite Z.min_l by exact Hle.
      + rewrite Z.min_r by lia. apply Hold. reflexivity.
    - exact Hd.
  Qed.

  (** Insertion changes only the supplied raw coordinate, retaining its tighter bound. *)
  Lemma raw_entry_add_cons : forall i j d m p q,
    raw_entry (add_cons i j d m) p q =
    if Pos.eqb p (K.encode i) then
      if Pos.eqb q (K.encode j) then Some (lower_bound d (raw_entry m p q))
      else raw_entry m p q
    else raw_entry m p q.
  Proof.
    intros i j d m p q. unfold raw_entry, add_cons. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hrow; [|reflexivity].
    apply Pos.eqb_eq in Hrow. subst p. cbn [row_of]. rewrite M.find_set.
    destruct (Pos.eqb q (K.encode j)) eqn:Hcol.
    - apply Pos.eqb_eq in Hcol. subst q. now rewrite !M.get_find.
    - now rewrite M.get_find.
  Qed.

  (** Inserting one constraint preserves a common bit bound for old and new entries. *)
  Lemma ell_add_cons : forall i j d m upper,
    ell m <= upper -> Z.size_nat d <= upper -> ell (add_cons i j d m) <= upper.
  Proof.
    intros i j d m upper Hm Hd. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_add_cons in Hentry.
    destruct (Pos.eqb p (K.encode i)).
    - destruct (Pos.eqb q (K.encode j)).
      + injection Hentry as <-. apply lower_bound_size; [exact Hd|].
        intros old Hold. eapply Nat.le_trans; [eapply ell_entry; exact Hold|exact Hm].
      + eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
    - eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
  Qed.

  (** Raw relaxation considers the old edge and the two edges through the pivot. *)
  Lemma raw_entry_relax : forall k m p q,
    raw_entry (relax_round k m) p q =
    match raw_entry m p (K.encode k) with
    | Some a => via_bound a (raw_entry m p q) (raw_entry m (K.encode k) q)
    | None => raw_entry m p q
    end.
  Proof.
    intros k m p q. unfold raw_entry, relax_round.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|]; cbn [round_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode k) row).
      + now rewrite M.find_merge by reflexivity.
      + reflexivity.
    - now rewrite !M.find_empty.
  Qed.

  (** One sparse relaxation adds at most one bit to the maximum stored bound. *)
  Lemma ell_relax : forall k m, ell (relax_round k m) <= ell m + 1.
  Proof.
    intros k m. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_relax in Hentry.
    destruct (raw_entry m p (K.encode k)) as [a|] eqn:Ha.
    - unfold via_bound in Hentry.
      destruct (raw_entry m (K.encode k) q) as [c|] eqn:Hc.
      + injection Hentry as <-. apply lower_bound_size.
        * apply zbits_add_bound; [exact (ell_entry m p (K.encode k) a Ha)|
            exact (ell_entry m (K.encode k) q c Hc)].
        * intros old Hold. pose proof (ell_entry m p q old Hold). lia.
      + pose proof (ell_entry m p q z Hentry). lia.
    - pose proof (ell_entry m p q z Hentry). lia.
  Qed.

  (** An incremental path update retains exactly the existing outer rows. *)
  Lemma find_increment_presence : forall i j d m p,
    M.find p (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) <> None <->
    M.find p m <> None.
  Proof.
    intros i j d m p. rewrite M.find_merge by reflexivity.
    rewrite M.find_empty. destruct (M.find p m); cbn [increment_row]; split; congruence.
  Qed.

  (** A new finite coordinate joins a prefix into the source and a suffix from the target. *)
  Lemma raw_increment_presence : forall i j d m p q,
    raw_entry (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) p q <>
      None <-> raw_entry m p q <> None \/
      (raw_entry m p (K.encode i) <> None /\ raw_entry m (K.encode j) q <> None).
  Proof.
    intros i j d m p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|]; cbn [increment_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode i) row).
      + rewrite M.find_merge by reflexivity.
        destruct (M.find q row), (M.find q (row_of (M.find (K.encode j) m)));
          cbn [via_bound]; intuition congruence.
      + tauto.
    - rewrite !M.find_empty. tauto.
  Qed.

  (** The path update uses only codes already present in its input support. *)
  Lemma support_increment : forall i j d m p,
    In p (support (M.merge (increment_row i d (row_of (M.get j m))) m M.empty)) <->
    In p (support m).
  Proof.
    intros i j d m p. rewrite !support_find. split.
    - intros [Hrow | [q Hentry]].
      + left. now apply find_increment_presence in Hrow.
      + apply raw_increment_presence in Hentry. right.
        destruct Hentry as [Hentry | [Hprefix Hsuffix]].
        * now exists q.
        * now exists (K.encode j).
    - intros [Hrow | [q Hentry]].
      + left. now apply find_increment_presence.
      + right. exists q. apply raw_increment_presence. now left.
  Qed.

  (** Two possible new endpoint codes bound both support count and key bits. *)
  Lemma support_endpoints : forall i j ma mb,
    (forall p, In p (support ma) ->
      p = K.encode i \/ p = K.encode j \/ In p (support mb)) ->
    supp ma <= supp mb + 2 /\
    b ma <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j)).
  Proof.
    intros i j ma mb Hsupport. split.
    - assert (Hincl : incl (support ma) (K.encode i :: K.encode j :: support mb)).
      { intros p Hin. destruct (Hsupport p Hin) as [Heq | [Heq | Hin']];
          cbn; intuition congruence. }
      pose proof (NoDup_incl_length (support_nodup ma) Hincl) as Hlength.
      unfold supp. cbn in Hlength. lia.
    - unfold b at 1. apply maximum_bound. intros p Hin.
      destruct (Hsupport p Hin) as [Heq | [Heq | Hin']].
      + subst p. change (K.bits i <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j))).
        eapply Nat.le_trans; [apply Nat.le_max_l|apply Nat.le_max_r].
      + subst p. change (K.bits j <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j))).
        eapply Nat.le_trans; [apply Nat.le_max_r|apply Nat.le_max_r].
      + eapply Nat.le_trans; [exact (support_bits mb p Hin')|apply Nat.le_max_l].
  Qed.

  (** Each incremental candidate uses an old prefix, the inserted bound, and an old suffix. *)
  Lemma raw_entry_increment : forall i j d m p q,
    raw_entry (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) p q =
    match raw_entry m p (K.encode i) with
    | Some a => via_bound (a + d)%Z (raw_entry m p q) (raw_entry m (K.encode j) q)
    | None => raw_entry m p q
    end.
  Proof.
    intros i j d m p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|]; cbn [increment_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode i) row).
      + now rewrite M.find_merge by reflexivity.
      + reflexivity.
    - now rewrite !M.find_empty.
  Qed.

  (** An incremental path update needs at most two further integer bits. *)
  Lemma ell_increment : forall i j d m upper,
    ell m <= upper -> Z.size_nat d <= upper ->
    ell (M.merge (increment_row i d (row_of (M.get j m))) m M.empty) <= upper + 2.
  Proof.
    intros i j d m upper Hm Hd. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_increment in Hentry.
    destruct (raw_entry m p (K.encode i)) as [a|] eqn:Ha.
    - unfold via_bound in Hentry.
      destruct (raw_entry m (K.encode j) q) as [c|] eqn:Hc.
      + injection Hentry as <-. apply lower_bound_size.
        * assert (Habits : Z.size_nat a <= upper).
          { pose proof (ell_entry m p (K.encode i) a Ha). lia. }
          assert (Hcbits : Z.size_nat c <= upper + 1).
          { pose proof (ell_entry m (K.encode j) q c Hc). lia. }
          pose proof (zbits_add_bound a d upper Habits Hd) as Had.
          pose proof (zbits_add_bound (a + d)%Z c (upper + 1) Had Hcbits). lia.
        * intros old Hold. pose proof (ell_entry m p q old Hold). lia.
      + pose proof (ell_entry m p q z Hentry). lia.
    - pose proof (ell_entry m p q z Hentry). lia.
  Qed.

  Lemma grow_incr_close : forall i j d m m', incr_close i j d m = Reached m' ->
    supp m' <= supp m + 2 /\
    b m' <= Nat.max (b m) (Nat.max (K.bits i) (K.bits j)) /\
    ell m' <= Nat.max (ell m) (Z.size_nat d) + 2.
  Proof.
    intros i j d m m' Hclose. unfold incr_close in Hclose.
    set (seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m))) in *.
    set (next := M.merge (increment_row i d (row_of (M.get j seed))) seed M.empty) in *.
    destruct (andb (nonnegative i next) (nonnegative j next)); [|discriminate].
    injection Hclose as <-.
    assert (Hsupport : forall p, In p (support next) ->
      p = K.encode i \/ p = K.encode j \/ In p (support m)).
    { intros p Hin. unfold next in Hin. apply support_increment in Hin.
      unfold seed in Hin. rewrite !support_add_cons in Hin. tauto. }
    destruct (support_endpoints i j next m Hsupport) as [Hcount Hbits].
    split; [exact Hcount|]. split; [exact Hbits|].
    unfold next. apply ell_increment; [|apply Nat.le_max_r].
    unfold seed. apply ell_add_cons; [|apply Nat.le_max_r].
    apply ell_add_cons; [|cbn [Z.size_nat]; lia].
    apply ell_add_cons; [apply Nat.le_max_l|cbn [Z.size_nat]; lia].
  Qed.

  (** Widening units cover the squared support size. *)
  Lemma F_wunits : forall s, wunits s = (ns s + 1) ^ 2.
  Proof.
    reflexivity.
  Qed.
  (** Assumption work charges incremental closure for every emitted atom. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat (length (F.atoms_of g es) *
        (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
        (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1)) +
      F.T_atoms_of g es)%N.
  Proof.
    intros g es s. unfold assume_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) =
      N.of_nat ((ns s + 1)^2 *
        (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s +
        (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) +
      F.T_lin_of e)%N.
  Proof.
    intros x e s. unfold assign_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Lemma F_havoc_work : forall x s,
    havoc_work x s = (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Proof.
    reflexivity.
  Qed.
  Lemma F_join_entry : forall ma mb i j,
    match join (Reached ma) (Reached mb) with
    | Reached mj => entry mj i j =
        match entry ma i j, entry mb i j with
        | Some x, Some y => Some (Z.max x y)
        | _, _ => None
        end
    | Unreached => False
    end.
  Proof.
    intros ma mb i j. cbn [join].
    change (entry (M.merge row_join ma mb) i j =
      bound_join (entry ma i j) (entry mb i j)).
    rewrite <- !raw_entry_get. apply raw_entry_join.
  Qed.
  Lemma fw_round_implied : forall k m v, models m v -> models (fw_round k m) v.
  Proof.
    exact fw_round_models.
  Qed.
  (** Retrieving a row, with an empty fallback, preserves map consistency. *)
  Lemma row_of_wf : forall m k,
    dbm_wf m -> M.wf (row_of (M.get k m)).
  Proof.
    intros m k [_ Hrows]. rewrite M.get_find.
    destruct (M.find (K.encode k) m) as [row|] eqn:Hrow; cbn [row_of].
    - exact (Hrows (K.encode k) row Hrow).
    - apply M.wf_empty.
  Qed.

  (** A row-wise map update preserves consistency when each returned row does. *)
  Lemma dbm_merge_wf : forall
      (f : option (M.t Z) -> option (M.t Z) -> option (M.t Z)) m,
    f None None = None -> dbm_wf m ->
    (forall old row, M.wf old -> f (Some old) None = Some row -> M.wf row) ->
    dbm_wf (M.merge f m M.empty).
  Proof.
    intros f m Hnone [Houter Hrows] Hf. split.
    - apply M.wf_merge; [exact Houter|apply M.wf_empty].
    - intros p row Hrow. rewrite M.find_merge in Hrow by exact Hnone.
      rewrite M.find_empty in Hrow.
      destruct (M.find p m) as [old|] eqn:Hold.
      + eapply Hf; [exact (Hrows p old Hold)|exact Hrow].
      + rewrite Hnone in Hrow. discriminate.
  Qed.

  (** Insertion retains consistent outer labels and consistent inner rows. *)
  Lemma add_cons_wf : forall i j d m,
    dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof.
    intros i j d m Hwf. destruct Hwf as [Houter Hrows]. unfold add_cons. split.
    - apply M.wf_set. exact Houter.
    - intros p row Hrow. rewrite M.find_set in Hrow.
      destruct (Pos.eqb p (K.encode i)).
      + injection Hrow as <-. apply M.wf_set. apply row_of_wf. now split.
      + exact (Hrows p row Hrow).
  Qed.

  (** Sparse relaxation merges only consistent source and pivot rows. *)
  Lemma relax_wf : forall k m, dbm_wf m -> dbm_wf (relax_round k m).
  Proof.
    intros k m Hwf. unfold relax_round. apply dbm_merge_wf;
      [reflexivity|exact Hwf|].
    intros old row Hold Hrow. cbn [round_row] in Hrow.
    destruct (M.get k old).
    - injection Hrow as <-. apply M.wf_merge; [exact Hold|].
      now apply row_of_wf.
    - injection Hrow as <-. exact Hold.
  Qed.

  (** An incremental path update merges only consistent source and exit rows. *)
  Lemma increment_wf : forall i j d m,
    dbm_wf m ->
    dbm_wf (M.merge (increment_row i d (row_of (M.get j m))) m M.empty).
  Proof.
    intros i j d m Hwf. apply dbm_merge_wf; [reflexivity|exact Hwf|].
    intros old row Hold Hrow. cbn [increment_row] in Hrow.
    destruct (M.get i old).
    - injection Hrow as <-. apply M.wf_merge; [exact Hold|].
      now apply row_of_wf.
    - injection Hrow as <-. exact Hold.
  Qed.

  Lemma wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  Proof.
    intros k m Hwf. unfold fw_round. apply relax_wf.
    destruct (pivot_present k m); [now apply add_cons_wf|exact Hwf].
  Qed.
  Lemma wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof.
    exact add_cons_wf.
  Qed.
  Lemma wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  Proof.
    intros i j d m Hwf. unfold incr_close.
    set (seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m))).
    set (next := M.merge (increment_row i d (row_of (M.get j seed))) seed M.empty).
    destruct (andb (nonnegative i next) (nonnegative j next)); [|exact I].
    unfold next. apply increment_wf. unfold seed.
    apply add_cons_wf, add_cons_wf, add_cons_wf. exact Hwf.
  Qed.
  Lemma close_sound : forall m v, models m v -> ngamma (close m) v.
  Proof.
    exact close_models.
  Qed.
  Lemma close_bot : forall m, close m = Unreached -> forall v, ~ models m v.
  Proof.
    intros m Hclose v Hmodel. pose proof (close_sound m v Hmodel) as Hnext.
    rewrite Hclose in Hnext. exact Hnext.
  Qed.
  Lemma incr_close_sound : forall i j d m v,
    models m v -> (vz v j - vz v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof.
    exact incr_close_models.
  Qed.
  Lemma close_shortest : forall m m' i j, dbm_wf m -> close m = Reached m' -> i <> j ->
    (forall d, entry m' i j = Some d -> exists ks, chain_weight m i ks j = Some d) /\
    (forall ks d, chain_weight m i ks j = Some d ->
       exists d', entry m' i j = Some d' /\ (d' <= d)%Z).
  Proof. Admitted. (* STUB *)
  Lemma incr_close_eq : forall m i j d, dbm_wf m -> closed m ->
    same_entries (incr_close i j d m) (close (add_cons i j d m)).
  Proof. Admitted. (* STUB *)
  Lemma bits_close_le : forall m m', close m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  (** State size charges all stored numeric data. *)
  Lemma F_size : forall s, size s = (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Proof.
    reflexivity.
  Qed.
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat ((tsize e + 1) *
      (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) + F.T_lin_of e)%N.
  Proof.
    intros e s. unfold range_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Lemma F_range_bits : forall e s,
    range_bits e s = ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
  Proof.
    reflexivity.
  Qed.
  Fixpoint fw_trace (ks : list K.t) (m : dbm) : list (K.t * dbm) :=
    match ks with
    | nil => nil
    | k :: ks =>
      let m' := fw_round k m in
      (k, m) ::
        match entry m' k k with
        | Some d => if (d <? 0)%Z then nil else fw_trace ks m'
        | None => fw_trace ks m'
        end
    end.
  TimeFun fw_trace.
  (** Reflected key equality supplies the Boolean test used by deduplication. *)
  Lemma key_eqb_true : forall x y, K.eqb x y = true <-> x = y.
  Proof.
    intros x y. destruct (K.eqb_spec x y); split; congruence.
  Qed.

  (** Consistent stored labels name codes actually present in their map. *)
  Lemma elements_code : forall A (m : M.t A) k, M.wf m ->
    In k (map fst (M.elements m)) -> In (K.encode k) (M.codes m).
  Proof.
    intros A m k Hwf Hin. apply in_map_iff in Hin.
    destruct Hin as [[q value] [Hq Hin]]. cbn in Hq. subst q.
    apply M.codes_spec. rewrite <- (M.get_find A k m).
    pose proof (proj1 (M.elements_spec A m k value Hwf) Hin) as Hget.
    rewrite Hget. discriminate.
  Qed.

  (** Pivot collection keeps each key once. *)
  Lemma keys_nodup : forall m, NoDup (keys m).
  Proof.
    intro m. unfold keys. apply (dedup_nodup K.t K.eqb key_eqb_true).
    constructor.
  Qed.

  (** Injective encoding preserves distinct pivot keys. *)
  Lemma encoded_keys_nodup : forall ks, NoDup ks -> NoDup (map K.encode ks).
  Proof.
    intros ks Hkeys. induction Hkeys as [|k ks Hfresh Hkeys IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [q [Hcode Hq]]. apply K.encode_inj in Hcode.
      subst q. exact (Hfresh Hq).
  Qed.

  (** Each consistent pivot label names a code in the matrix support. *)
  Lemma keys_support : forall m k, dbm_wf m -> In k (keys m) ->
    In (K.encode k) (support m).
  Proof.
    intros m k [Houter Hrows] Hkey. unfold keys in Hkey.
    rewrite (dedup_membership K.t K.eqb key_eqb_true) in Hkey.
    destruct Hkey as [Hkey | Hempty]; [|contradiction].
    apply in_app_iff in Hkey. apply support_spec. destruct Hkey as [Hkey | Hkey].
    - left. now apply elements_code.
    - right. apply in_flat_map in Hkey.
      destruct Hkey as [[i row] [Hrow Hkey]]. cbn in Hkey.
      pose proof (proj1 (M.elements_spec (M.t Z) m i row Houter) Hrow) as Hget.
      rewrite M.get_find in Hget.
      apply in_flat_map. exists row. split.
      + exact (row_in_rows m (K.encode i) row Hget).
      + apply elements_code; [exact (Hrows (K.encode i) row Hget)|exact Hkey].
  Qed.
  Lemma bits_fw_round_step : forall k m, ell (fw_round k m) <= ell m + 1.
  Proof.
    intros k m. unfold fw_round. destruct (pivot_present k m).
    - eapply Nat.le_trans; [apply ell_relax|].
      assert (Hseed : ell (add_cons k k 0%Z m) <= ell m).
      { apply ell_add_cons; [lia|cbn [Z.size_nat]; lia]. }
      lia.
    - apply ell_relax.
  Qed.
  Lemma path_key_dec : forall x y : K.t, {x = y} + {x <> y}.
  Proof.
    intros x y. destruct (K.eqb_spec x y); [now left|now right].
  Defined.

  (** The executable seed is the abstract zero-diagonal insertion. *)
  Lemma entry_path_seed : forall k m i j,
    entry (add_cons k k 0%Z m) i j =
      RelationalPathBounds.seed path_key_dec (entry m) k i j.
  Proof.
    intros k m i j. rewrite entry_add_cons. unfold RelationalPathBounds.seed.
    destruct (K.eqb_spec i k) as [Hi|Hi];
      destruct (path_key_dec i k) as [Hi'|Hi']; try contradiction.
    - subst i. destruct (K.eqb_spec j k) as [Hj|Hj];
        destruct (path_key_dec j k) as [Hj'|Hj']; try contradiction.
      + subst j. destruct (entry m k k); reflexivity.
      + reflexivity.
    - reflexivity.
  Qed.

  (** Sparse merging agrees pointwise with the abstract Floyd step. *)
  Lemma entry_path_floyd : forall k m i j,
    entry (relax_round k m) i j = RelationalPathBounds.floyd (entry m) k i j.
  Proof.
    intros k m i j. rewrite entry_relax_round. unfold RelationalPathBounds.floyd.
    destruct (entry m i k), (entry m i j), (entry m k j);
      cbn [via_bound lower_bound RelationalPathBounds.minimum RelationalPathBounds.plus];
      try reflexivity. f_equal. apply Z.min_comm.
  Qed.

  Lemma entry_fw_present : forall k m, pivot_present k m = true -> forall i j,
    entry (fw_round k m) i j =
      RelationalPathBounds.floyd
        (RelationalPathBounds.seed path_key_dec (entry m) k) k i j.
  Proof.
    intros k m Hpresent i j. unfold fw_round. rewrite Hpresent, entry_path_floyd.
    unfold RelationalPathBounds.floyd. now rewrite !entry_path_seed.
  Qed.

  (** Both endpoints of a finite entry are in the raw code support. *)
  Lemma entry_source_support : forall m i j d, entry m i j = Some d ->
    In (K.encode i) (support m).
  Proof.
    intros m i j d Hentry. unfold entry in Hentry.
    destruct (M.get i m) as [row|] eqn:Hrow; [|discriminate].
    apply support_find. left. rewrite <- (M.get_find (M.t Z) i m), Hrow. discriminate.
  Qed.

  Lemma entry_target_support : forall m i j d, entry m i j = Some d ->
    In (K.encode j) (support m).
  Proof.
    intros m i j d Hentry. apply support_find. right. exists (K.encode i).
    rewrite raw_entry_get, Hentry. discriminate.
  Qed.

  Lemma entry_fw_absent : forall k m, pivot_present k m = false -> forall i j,
    entry (fw_round k m) i j = entry m i j.
  Proof.
    intros k m Habsent i j.
    assert (Hcolumn : entry m i k = None).
    { destruct (entry m i k) as [d|] eqn:Hentry; [|reflexivity].
      pose proof (entry_target_support m i k d Hentry) as Hsupport.
      apply pivot_present_support in Hsupport. congruence. }
    unfold fw_round. now rewrite Habsent, entry_relax_round, Hcolumn.
  Qed.

  (** A successful actual round extends the processed-path invariant. *)
  Lemma fw_round_path_invariant : forall initial m ps k,
    RelationalPathBounds.invariant (entry initial) (entry m) ps ->
    (forall d, entry (fw_round k m) k k = Some d -> (0 <= d)%Z) ->
    exists ps', RelationalPathBounds.invariant (entry initial) (entry (fw_round k m)) ps'.
  Proof.
    intros initial m ps k Hinv Hnonnegative.
    destruct (pivot_present k m) eqn:Hpresent.
    - exists (k :: ps). eapply RelationalPathBounds.invariant_ext.
      + intros i j. symmetry. now apply entry_fw_present.
      + apply RelationalPathBounds.invariant_successful_round; [exact Hinv|].
        intros d Hdiag. apply Hnonnegative. now rewrite (entry_fw_present k m Hpresent).
    - exists ps. eapply RelationalPathBounds.invariant_ext; [|exact Hinv].
      intros i j. symmetry. now apply entry_fw_absent.
  Qed.

  (** Every recorded state precedes the first rejected pivot cycle. *)
  Lemma fw_trace_path_invariant : forall ks initial m ps k a,
    dbm_wf m -> RelationalPathBounds.invariant (entry initial) (entry m) ps ->
    In (k, a) (fw_trace ks m) -> dbm_wf a /\
      exists ps', RelationalPathBounds.invariant (entry initial) (entry a) ps'.
  Proof.
    induction ks as [|p ks IH]; intros initial m ps k a Hwf Hinv Hin.
    - contradiction.
    - cbn [fw_trace] in Hin. destruct Hin as [Heq|Hin].
      + inversion Heq; subst k a. split; [exact Hwf|now exists ps].
      + assert (Hnext_wf : dbm_wf (fw_round p m)) by (now apply wf_fw_round).
        destruct (entry (fw_round p m) p p) as [d|] eqn:Hdiag.
        * destruct (d <? 0)%Z eqn:Hnegative; [contradiction|].
          apply Z.ltb_ge in Hnegative.
          assert (Hsuccess : forall z, entry (fw_round p m) p p = Some z -> (0 <= z)%Z).
          { intros z Hz. rewrite Hdiag in Hz. inversion Hz. lia. }
          destruct (fw_round_path_invariant initial m ps p Hinv Hsuccess) as [ps' Hnext].
          exact (IH initial (fw_round p m) ps' k a Hnext_wf Hnext Hin).
        * assert (Hsuccess : forall z, entry (fw_round p m) p p = Some z -> (0 <= z)%Z).
          { intros z Hz. rewrite Hdiag in Hz. discriminate. }
          destruct (fw_round_path_invariant initial m ps p Hinv Hsuccess) as [ps' Hnext].
          exact (IH initial (fw_round p m) ps' k a Hnext_wf Hnext Hin).
  Qed.

  (** A minimum path has no more original edges than the initial support has codes. *)
  Lemma path_invariant_entry_bits : forall initial current ps,
    RelationalPathBounds.invariant (entry initial) current ps ->
    forall i j d, current i j = Some d ->
      Z.size_nat d <= ell initial + Nat.log2 (supp initial) + 1.
  Proof.
    intros initial current ps [Hbelow Hclosed Hzero Hpath] i j d Hentry.
    destruct (Hpath i j d Hentry) as [[Heq Hz]|[ks [Hks Hchain]]].
    - subst d. cbn [Z.size_nat]. lia.
    - destruct (RelationalPathBounds.simple_minimum_chain K.t path_key_dec
        (entry initial) current ps Hbelow Hclosed Hzero ks i j d Hks Hentry Hchain)
        as [shortened [Hincl [Hnodup Hvalue]]].
      assert (Hlength : length (i :: shortened) <= supp initial).
      { unfold supp. rewrite <- (length_map K.encode (i :: shortened)).
        apply NoDup_incl_length; [now apply encoded_keys_nodup|].
        intros code Hcode. apply in_map_iff in Hcode.
        destruct Hcode as [x [Hcode Hx]]. subst code.
        eapply (RelationalPathBounds.chain_sources K.t (entry initial)
          (fun q => In (K.encode q) (support initial))).
        - intros p q z Hz. now apply (entry_source_support initial p q z).
        - exact Hvalue.
        - exact Hx. }
      assert (Hedge : forall p q z, entry initial p q = Some z ->
        Z.abs_nat z <= 2 ^ ell initial).
      { intros p q z Hz. apply Nat.lt_le_incl. apply zbits_abs_bound.
        apply (ell_entry initial (K.encode p) (K.encode q) z).
        now rewrite raw_entry_get. }
      pose proof (RelationalPathBounds.chain_abs K.t (entry initial)
        (2 ^ ell initial) Hedge shortened i j d Hvalue) as Habs.
      assert (Hpositive : 0 < supp initial) by (cbn [length] in Hlength; lia).
      pose proof (Nat.log2_spec (supp initial) Hpositive) as [_ Hlog].
      assert (Hpower : 0 < 2 ^ ell initial).
      { pose proof (Nat.pow_nonzero 2 (ell initial) ltac:(lia)). lia. }
      apply zbits_least.
      replace (ell initial + Nat.log2 (supp initial) + 1) with
        (S (Nat.log2 (supp initial)) + ell initial) by lia.
      rewrite Nat.pow_add_r. cbn [length] in Hlength.
      eapply Nat.le_lt_trans; [exact Habs|].
      apply Nat.mul_lt_mono_pos_r; [exact Hpower|lia].
  Qed.

  (** Well-formed raw entries have source and target keys. *)
  Lemma wf_raw_entry_keys : forall m p q d, dbm_wf m -> raw_entry m p q = Some d ->
    exists i j, K.encode i = p /\ K.encode j = q /\ entry m i j = Some d.
  Proof.
    intros m p q d [Houter Hrows] Hraw.
    unfold raw_entry in Hraw. destruct (M.find p m) as [row|] eqn:Hrow;
      cbn [row_of] in Hraw.
    - destruct (M.wf_find (M.t Z) m p row Houter Hrow) as [i Hi].
      destruct (M.wf_find Z row q d (Hrows p row Hrow) Hraw) as [j Hj].
      exists i, j. split; [exact Hi|]. split; [exact Hj|].
      rewrite <- raw_entry_get, Hi, Hj. unfold raw_entry. now rewrite Hrow.
    - rewrite M.find_empty in Hraw. discriminate.
  Qed.

  Lemma bits_fw_trace_le : forall ks m k a, dbm_wf m ->
    In (k, a) (fw_trace ks m) ->
    ell a <= ell m + Nat.log2 (supp m) + 1.
  Proof.
    intros ks m k a Hwf Hin.
    destruct (fw_trace_path_invariant ks m m nil k a Hwf
      (RelationalPathBounds.invariant_initial K.t (entry m)) Hin) as [Hawf [ps Hpath]].
    apply ell_bound. intros p q d Hraw.
    destruct (wf_raw_entry_keys a p q d Hawf Hraw) as [i [j [Hi [Hj Hentry]]]].
    exact (path_invariant_entry_bits m (entry a) ps Hpath i j d Hentry).
  Qed.
  Lemma supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  Proof.
    intros k m. apply support_sizes, support_round.
  Qed.

  (** The Boolean list scan recognizes key membership through the key equality law. *)
  Lemma key_existsb : forall k ks, existsb (K.eqb k) ks = true <-> In k ks.
  Proof.
    intros k ks. rewrite existsb_exists. split.
    - intros [x [Hx Heq]]. apply key_eqb_true in Heq. now subst x.
    - intro Hk. exists k. split; [exact Hk|apply key_eqb_true; reflexivity].
  Qed.

  Definition keyset_matches (seen : M.t unit) (ks : list K.t) : Prop :=
    forall k, M.get k seen <> None <-> In k ks.

  (** Inserting a remembered key preserves the membership correspondence. *)
  Lemma keyset_add_matches : forall seen ks k,
    keyset_matches seen ks -> keyset_matches (M.set k tt seen) (k :: ks).
  Proof.
    intros seen ks k Hmatch q. destruct (K.eqb_spec q k) as [Heq|Hne].
    - subst q. rewrite M.get_set_same. cbn [In]. split.
      + intros. now left.
      + intros. discriminate.
    - rewrite M.get_set_other by exact Hne. rewrite (Hmatch q). cbn [In].
      split; [intro Hin; now right|]. intros [Heq|Hin]; [|exact Hin].
      exfalso. apply Hne. now symmetry.
  Qed.

  (** The map-backed fold preserves the signature's reverse first-occurrence order. *)
  Lemma remember_fold_keys : forall xs seen ks,
    keyset_matches seen ks ->
    snd (fold_left remember_key xs (seen, ks)) =
    fold_left (fun acc x => if existsb (K.eqb x) acc then acc else x :: acc) xs ks.
  Proof.
    intro xs. induction xs as [|k xs IH]; intros seen ks Hmatch; [reflexivity|].
    cbn [fold_left]. destruct (M.get k seen) as [u|] eqn:Hget.
    - assert (Hremember : remember_key (seen, ks) k = (seen, ks)).
      { unfold remember_key. cbn [fst snd]. now rewrite Hget. }
      assert (Hseen : existsb (K.eqb k) ks = true).
      { apply key_existsb, (proj1 (Hmatch k)). rewrite Hget. discriminate. }
      rewrite Hremember, Hseen. now apply IH.
    - assert (Hremember : remember_key (seen, ks) k = (M.set k tt seen, k :: ks)).
      { unfold remember_key. cbn [fst snd]. now rewrite Hget. }
      assert (Hseen : existsb (K.eqb k) ks = false).
      { destruct (existsb (K.eqb k) ks) eqn:Hseen; [|reflexivity].
        apply key_existsb in Hseen. apply (proj2 (Hmatch k)) in Hseen.
        contradiction. }
      rewrite Hremember, Hseen. apply IH. now apply keyset_add_matches.
  Qed.

  (** Executable pivot enumeration agrees with the frozen specification even on raw maps. *)
  Lemma pivot_keys_eq_keys : forall m, pivot_keys m = keys m.
  Proof.
    intro m. unfold pivot_keys, keys. apply remember_fold_keys.
    intro k. rewrite M.get_empty. cbn [In]. tauto.
  Qed.

  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Lemma keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  Proof.
    intros m Hwf. unfold supp.
    rewrite <- (length_map K.encode (keys m)). apply NoDup_incl_length.
    - apply encoded_keys_nodup, keys_nodup.
    - intros p Hin. apply in_map_iff in Hin. destruct Hin as [k [Hcode Hkey]].
      subst p. now apply keys_support.
  Qed.
  (** A missing value contributes no stored weight. *)
  Definition option_weight {A : Type} (w : A -> nat) (a : option A) : nat :=
    match a with Some x => w x | None => 0 end.

  (** Summed weights account for stored payloads independently of their labels. *)
  Definition sum_weight {A : Type} (w : A -> nat) (xs : list A) : nat :=
    fold_right Nat.add 0 (map w xs).

  (** A map's payload weight ranges over its distinct stored codes. *)
  Definition stored_weight {A : Type} (w : A -> nat) (m : M.t A) : nat :=
    sum_weight (fun p => option_weight w (M.find p m)) (M.codes m).

  (** A sparse map pays for its skeleton, bindings, and stored payloads separately. *)
  Definition code_work {A : Type} (w : A -> nat) (m : M.t A) : nat :=
    M.nodes m + length (M.codes m) + stored_weight w m.

  (** List concatenation adds the two weight sums. *)
  Lemma sum_weight_app : forall (A : Type) (w : A -> nat) xs ys,
    sum_weight w (xs ++ ys) = sum_weight w xs + sum_weight w ys.
  Proof.
    intros A w xs. induction xs as [|x xs IH]; intro ys.
    - reflexivity.
    - change (w x + sum_weight w (xs ++ ys) =
        w x + sum_weight w xs + sum_weight w ys). rewrite IH. lia.
  Qed.

  (** Pointwise addition distributes over the weight sum. *)
  Lemma sum_weight_add : forall (A : Type) (f g : A -> nat) xs,
    sum_weight (fun x => f x + g x) xs = sum_weight f xs + sum_weight g xs.
  Proof.
    intros A f g xs. induction xs as [|x xs IH].
    - reflexivity.
    - change (f x + g x + sum_weight (fun y => f y + g y) xs =
        f x + sum_weight f xs + (g x + sum_weight g xs)). rewrite IH. lia.
  Qed.

  (** Unit weights count list members. *)
  Lemma sum_weight_one : forall (A : Type) (xs : list A),
    sum_weight (fun _ => 1) xs = length xs.
  Proof.
    intros A xs. induction xs as [|x xs IH]; [reflexivity|].
    change (1 + sum_weight (fun _ : A => 1) xs = S (length xs)). now rewrite IH.
  Qed.

  (** A duplicate-free sublist cannot have a larger nonnegative weight sum. *)
  Lemma sum_weight_incl : forall (A : Type) (w : A -> nat) xs ys,
    NoDup xs -> incl xs ys -> sum_weight w xs <= sum_weight w ys.
  Proof.
    intros A w xs. induction xs as [|x xs IH]; intros ys Hnodup Hincl.
    - change (0 <= sum_weight w ys). lia.
    - apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hfresh Hnodup].
      assert (Hx : In x ys) by (apply Hincl; now left).
      apply in_split in Hx. destruct Hx as [before [after Heq]]. subst ys.
      assert (Hrest : incl xs (before ++ after)).
      { intros y Hy. specialize (Hincl y (or_intror Hy)).
        apply in_app_iff in Hincl. apply in_app_iff.
        destruct Hincl as [Hin | [Heq | Hin]].
        - now left.
        - subst y. contradiction.
        - now right. }
      pose proof (IH (before ++ after) Hnodup Hrest) as Hsum.
      rewrite !sum_weight_app in Hsum |- *.
      change (w x + sum_weight w xs <=
        sum_weight w before + (w x + sum_weight w after)). lia.
  Qed.

  (** Removing absent lookups does not change their summed payload weight. *)
  Lemma sum_lookup_filter : forall (A : Type) (w : A -> nat) (m : M.t A) xs,
    sum_weight (fun p => option_weight w (M.find p m)) xs =
    sum_weight (fun p => option_weight w (M.find p m))
      (filter (fun p => match M.find p m with Some _ => true | None => false end) xs).
  Proof.
    intros A w m xs. unfold sum_weight. induction xs as [|p xs IH]; [reflexivity|].
    cbn [map fold_right filter]. destruct (M.find p m) eqn:Hlookup;
      cbn [option_weight map fold_right]; rewrite ?Hlookup;
      cbn [option_weight]; now rewrite IH.
  Qed.

  (** Looking up distinct codes can charge each stored payload at most once. *)
  Lemma stored_weight_bound : forall (A : Type) (w : A -> nat) (m : M.t A) xs,
    NoDup xs -> sum_weight (fun p => option_weight w (M.find p m)) xs <=
      stored_weight w m.
  Proof.
    intros A w m xs Hnodup. rewrite sum_lookup_filter. unfold stored_weight.
    apply sum_weight_incl.
    - now apply NoDup_filter.
    - intros p Hin. apply filter_In in Hin. destruct Hin as [_ Hpresent].
      apply M.codes_spec. destruct (M.find p m); congruence.
  Qed.

  (** Scanning both code lists charges each payload at most twice. *)
  Lemma pair_stored_weight_bound : forall (A B : Type) (wa : A -> nat) (wb : B -> nat)
      (ma : M.t A) (mb : M.t B),
    sum_weight (fun p => option_weight wa (M.find p ma) +
      option_weight wb (M.find p mb) + 1) (M.codes ma ++ M.codes mb) <=
    2 * stored_weight wa ma + 2 * stored_weight wb mb +
      length (M.codes ma) + length (M.codes mb).
  Proof.
    intros A B wa wb ma mb.
    pose proof (stored_weight_bound A wa ma (M.codes mb) (M.codes_nodup B mb)) as Ha.
    pose proof (stored_weight_bound B wb mb (M.codes ma) (M.codes_nodup A ma)) as Hb.
    rewrite sum_weight_app. repeat rewrite sum_weight_add. rewrite !sum_weight_one.
    unfold stored_weight in *. lia.
  Qed.

  (** Pointwise callback bounds sum to the corresponding weighted list bound. *)
  Lemma time_sum_bound : forall (A : Type) (xs : list A) (f : A -> N) (w : A -> nat) c,
    (forall x, In x xs -> (f x <= c * N.of_nat (w x))%N) ->
    (fold_right N.add 0%N (map f xs) <= c * N.of_nat (sum_weight w xs))%N.
  Proof.
    intros A xs. induction xs as [|x xs IH]; intros f w c Hbound.
    - change (0 <= c * 0)%N. nia.
    - assert (Hx : (f x <= c * N.of_nat (w x))%N) by (apply Hbound; now left).
      assert (Hxs : (fold_right N.add 0%N (map f xs) <=
        c * N.of_nat (sum_weight w xs))%N).
      { apply IH. intros y Hin. apply Hbound. now right. }
      change (f x + fold_right N.add 0%N (map f xs) <=
        c * N.of_nat (w x + sum_weight w xs))%N.
      rewrite Nat2N.inj_add. nia.
  Qed.

  (** Sparse callback sums separate skeleton work from the payload weights they visit. *)
  Lemma map_sum_time_bound : forall (A B : Type) (wa : A -> nat) (wb : B -> nat)
      (tf : option A -> option B -> N) (ma : M.t A) (mb : M.t B) c clock,
    (forall a b, (tf a b <= c * N.of_nat (option_weight wa a +
      option_weight wb b + 1))%N) ->
    (clock <= M.c_map * ((tf None None + 1) * N.of_nat (M.nodes ma + M.nodes mb + 1) +
      fold_right N.add 0%N
        (map (fun p => tf (M.find p ma) (M.find p mb)) (M.codes ma ++ M.codes mb))))%N ->
    (clock <= M.c_map * (c + 1) * 2 * N.of_nat (code_work wa ma + code_work wb mb + 1))%N.
  Proof.
    intros A B wa wb tf ma mb c clock Hbound Hclock.
    pose proof (Hbound None None) as Hempty.
    change (tf None None <= c * 1)%N in Hempty. rewrite N.mul_1_r in Hempty.
    assert (Hsum : (fold_right N.add 0%N
        (map (fun p => tf (M.find p ma) (M.find p mb)) (M.codes ma ++ M.codes mb)) <=
      c * N.of_nat (sum_weight (fun p => (option_weight wa (M.find p ma) +
        option_weight wb (M.find p mb) + 1)%nat) (M.codes ma ++ M.codes mb)))%N).
    { apply time_sum_bound. intros p _. apply Hbound. }
    pose proof (pair_stored_weight_bound A B wa wb ma mb) as Hweight.
    assert (Hsum' : (fold_right N.add 0%N
        (map (fun p => tf (M.find p ma) (M.find p mb)) (M.codes ma ++ M.codes mb)) <=
      c * N.of_nat (2 * stored_weight wa ma + 2 * stored_weight wb mb +
        length (M.codes ma) + length (M.codes mb)))%N).
    { eapply N.le_trans; [exact Hsum|]. apply N.mul_le_mono_l. lia. }
    eapply N.le_trans; [exact Hclock|].
    replace (M.c_map * (c + 1) * 2 * N.of_nat (code_work wa ma + code_work wb mb + 1))%N
      with (M.c_map * (2 * (c + 1) *
        N.of_nat (code_work wa ma + code_work wb mb + 1)))%N by ring.
    apply N.mul_le_mono_l. clear Hclock Hsum Hbound Hweight.
    unfold code_work. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  (** The map merge clock is bounded by each input's own code work. *)
  Lemma T_merge_code_work : forall (A B C : Type)
      (f : option A -> option B -> option C) tf (wa : A -> nat) (wb : B -> nat) ma mb c,
    (forall a b, (tf a b <= c * N.of_nat (option_weight wa a +
      option_weight wb b + 1))%N) ->
    (M.T_merge f tf ma mb <= M.c_map * (c + 1) * 2 *
      N.of_nat (code_work wa ma + code_work wb mb + 1))%N.
  Proof.
    intros A B C f tf wa wb ma mb c Hbound. eapply map_sum_time_bound;
      [exact Hbound|apply M.T_merge_sum_le].
  Qed.

  (** Relational scanning has the same sparse code-work bound as merging. *)
  Lemma T_forall2b_code_work : forall (A B : Type)
      (f : option A -> option B -> bool) tf (wa : A -> nat) (wb : B -> nat) ma mb c,
    (forall a b, (tf a b <= c * N.of_nat (option_weight wa a +
      option_weight wb b + 1))%N) ->
    (M.T_forall2b f tf ma mb <= M.c_map * (c + 1) * 2 *
      N.of_nat (code_work wa ma + code_work wb mb + 1))%N.
  Proof.
    intros A B f tf wa wb ma mb c Hbound. eapply map_sum_time_bound;
      [exact Hbound|apply M.T_forall2b_sum_le].
  Qed.

  (** A bound comparison pays only for its present integer operands. *)
  Lemma T_bound_leb_le : forall a b,
    (T_bound_leb a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.

  (** A bound join pays only for its present integer operands. *)
  Lemma T_bound_join_le : forall a b,
    (T_bound_join a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.

  (** A bound meet pays only for its present integer operands. *)
  Lemma T_bound_meet_le : forall a b,
    (T_bound_meet a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.

  (** A bound widening pays only for its present integer operands. *)
  Lemma T_bound_widen_le : forall a b,
    (T_bound_widen a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.
  (** Empty maps enumerate no stored code. *)
  Lemma codes_empty : forall A, M.codes (@M.empty A) = nil.
  Proof.
    intro A. destruct (M.codes (@M.empty A)) as [|p ps] eqn:Hcodes; [reflexivity|].
    exfalso. assert (Hp : In p (M.codes (@M.empty A))).
    { rewrite Hcodes. now left. }
    apply M.codes_spec in Hp. rewrite M.find_empty in Hp. contradiction.
  Qed.

  (** Empty maps carry no payload weight. *)
  Lemma stored_weight_empty : forall (A : Type) (w : A -> nat),
    stored_weight w M.empty = 0.
  Proof.
    intros A w. unfold stored_weight. rewrite codes_empty. reflexivity.
  Qed.

  (** Empty maps contribute no skeleton, binding, or payload work. *)
  Lemma code_work_empty : forall (A : Type) (w : A -> nat), code_work w M.empty = 0.
  Proof.
    intros A w. unfold code_work. rewrite M.nodes_empty, codes_empty, stored_weight_empty.
    reflexivity.
  Qed.

  (** Replacing a missing row by the empty map preserves its zero work contribution. *)
  Lemma code_work_row_of : forall r,
    code_work Z.size_nat (row_of r) = option_weight (code_work Z.size_nat) r.
  Proof.
    intros [row|]; [reflexivity|apply code_work_empty].
  Qed.

  (** A common coefficient covers scalar work and one sparse row traversal. *)
  Definition row_time_factor : N := (32 * (M.c_map + 1))%N.

  (** Row comparison charges the two rows' own finite entries. *)
  Lemma T_row_leb_le : forall a b,
    (T_row_leb a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    pose proof (T_forall2b_code_work Z Z bound_leb (fun x y => T_bound_leb x y)
      Z.size_nat Z.size_nat
      (row_of a) (row_of b) 8%N T_bound_leb_le) as Hscan.
    rewrite !code_work_row_of in Hscan. unfold row_time_factor. time_step.
  Qed.

  (** Row join charges the two rows' own finite entries. *)
  Lemma T_row_join_le : forall a b,
    (T_row_join a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    destruct a as [ra|], b as [rb|].
    - pose proof (T_merge_code_work Z Z Z bound_join (fun x y => T_bound_join x y)
        Z.size_nat Z.size_nat
        ra rb 8%N T_bound_join_le) as Hmerge. unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
  Qed.

  (** Row meet charges the two rows' own finite entries. *)
  Lemma T_row_meet_le : forall a b,
    (T_row_meet a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    destruct a as [ra|], b as [rb|].
    - pose proof (T_merge_code_work Z Z Z bound_meet (fun x y => T_bound_meet x y)
        Z.size_nat Z.size_nat
        ra rb 8%N T_bound_meet_le) as Hmerge. unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
  Qed.

  (** Row widening charges the two rows' own finite entries. *)
  Lemma T_row_widen_le : forall a b,
    (T_row_widen a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    destruct a as [ra|].
    - pose proof (T_merge_code_work Z Z Z bound_widen (fun x y => T_bound_widen x y)
        Z.size_nat Z.size_nat
        ra (row_of b) 8%N T_bound_widen_le) as Hmerge.
      rewrite code_work_row_of in Hmerge. unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
  Qed.

  (** Pointwise weight bounds lift to their list sums. *)
  Lemma sum_weight_mono : forall (A : Type) (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) -> sum_weight f xs <= sum_weight g xs.
  Proof.
    intros A f g xs. induction xs as [|x xs IH]; intro Hbound; [reflexivity|].
    assert (Hx : f x <= g x) by (apply Hbound; now left).
    assert (Hxs : sum_weight f xs <= sum_weight g xs).
    { apply IH. intros y Hin. apply Hbound. now right. }
    change (f x + sum_weight f xs <= g x + sum_weight g xs). lia.
  Qed.

  (** Constant weights multiply the list length. *)
  Lemma sum_weight_const : forall (A : Type) (xs : list A) n,
    sum_weight (fun _ => n) xs = length xs * n.
  Proof.
    intros A xs. induction xs as [|x xs IH]; intro n; [reflexivity|].
    change (n + sum_weight (fun _ : A => n) xs = S (length xs) * n).
    rewrite IH. lia.
  Qed.

  (** Summing outer payloads agrees with summing the collected rows. *)
  Lemma stored_weight_rows : forall (w : M.t Z -> nat) m,
    stored_weight w m = sum_weight w (rows m).
  Proof.
    intros w m. unfold stored_weight, sum_weight, rows.
    induction (M.codes m) as [|p ps IH]; [reflexivity|].
    cbn [map fold_right flat_map]. destruct (M.find p m) eqn:Hrow;
      cbn [option_weight map fold_right app]; now rewrite IH.
  Qed.

  (** Each collected row's finite-entry bits are bounded by the matrix maximum. *)
  Lemma stored_row_bits_bound : forall m p row,
    M.find p m = Some row -> stored_weight Z.size_nat row <=
      length (M.codes row) * ell m.
  Proof.
    intros m p row Hrow. unfold stored_weight, sum_weight. apply sum_members_bound.
    intros q Hq. destruct (M.find q row) as [z|] eqn:Hentry.
    - change (Z.size_nat z <= ell m). apply (ell_entry m p q z).
      unfold raw_entry. rewrite Hrow. exact Hentry.
    - change (0 <= ell m). lia.
  Qed.

  (** A collected row pays for its skeleton and at most one entry per supported code. *)
  Lemma row_code_work_bound : forall m row, In row (rows m) ->
    code_work Z.size_nat row <= M.nodes row + supp m * (ell m + 1).
  Proof.
    intros m row Hin.
    assert (Hsupport : forall q, In q (M.codes row) -> In q (support m)).
    { intros q Hq. apply support_spec. right. apply in_flat_map. exists row. now split. }
    pose proof (codes_support_length Z row m Hsupport) as Hlength.
    apply rows_find in Hin. destruct Hin as [p Hrow].
    pose proof (stored_row_bits_bound m p row Hrow) as Hbits.
    unfold code_work. nia.
  Qed.

  (** The public quadratic size covers raw code work and the complete sparse skeleton. *)
  Lemma matrix_code_work_le : forall m,
    code_work (code_work Z.size_nat) m <= size (Reached m).
  Proof.
    intro m.
    assert (Houter : length (M.codes m) <= supp m).
    { apply codes_support_length. intros p Hp. apply support_spec. now left. }
    pose proof (rows_length m) as Hrows.
    assert (Hsum : sum_weight (code_work Z.size_nat) (rows m) <=
      sum_weight (fun row => M.nodes row + supp m * (ell m + 1)) (rows m)).
    { apply sum_weight_mono. intros row Hin. now apply row_code_work_bound. }
    rewrite sum_weight_add, sum_weight_const in Hsum.
    change (sum_weight (code_work Z.size_nat) (rows m) <=
      sum_weight M.nodes (rows m) + length (rows m) * (supp m * (ell m + 1))) in Hsum.
    assert (Hprod : length (rows m) * (supp m * (ell m + 1)) <=
      supp m * (supp m * (ell m + 1))).
    { apply Nat.mul_le_mono_r. lia. }
    unfold code_work at 1. rewrite stored_weight_rows.
    change (M.nodes m + length (M.codes m) + sum_weight (code_work Z.size_nat) (rows m) <=
      (supp m + 1)^2 * (b m + ell m + 1) +
      (M.nodes m + sum_weight M.nodes (rows m))). cbn [Nat.pow]. nia.
  Qed.

  (** A matrix traversal adds one outer sparse-map pass to the row bound. *)
  Definition matrix_time_factor : N := (M.c_map * (row_time_factor + 1) * 2 + 8)%N.

  (** Comparing two reached matrices is linear in their nested code work. *)
  Lemma T_leb_matrix_le : forall ma mb,
    (T_leb (Reached ma) (Reached mb) <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    assert (Hwork : (1 <= N.of_nat (code_work (code_work Z.size_nat) ma +
      code_work (code_work Z.size_nat) mb + 1))%N) by lia.
    pose proof (T_forall2b_code_work (M.t Z) (M.t Z) row_leb (fun x y => T_row_leb x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_leb_le)
      as Hscan. unfold matrix_time_factor. time_step.
  Qed.

  (** Joining two reached matrices is linear in their nested code work. *)
  Lemma T_join_matrix_le : forall ma mb,
    (T_join (Reached ma) (Reached mb) <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    assert (Hwork : (1 <= N.of_nat (code_work (code_work Z.size_nat) ma +
      code_work (code_work Z.size_nat) mb + 1))%N) by lia.
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) row_join (fun x y => T_row_join x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_join_le)
      as Hmerge. unfold matrix_time_factor. time_step.
  Qed.

  (** Meeting two reached matrices is linear in their nested code work. *)
  Lemma T_meet_matrix_le : forall ma mb,
    (T_meet (Reached ma) (Reached mb) <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    assert (Hwork : (1 <= N.of_nat (code_work (code_work Z.size_nat) ma +
      code_work (code_work Z.size_nat) mb + 1))%N) by lia.
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) row_meet (fun x y => T_row_meet x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_meet_le)
      as Hmerge. unfold matrix_time_factor. time_step.
  Qed.

  (** The widening update itself is linear in its two input matrices' code work. *)
  Lemma T_widen_merge_le : forall ma mb,
    (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) row_widen (fun x y => T_row_widen x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_widen_le)
      as Hmerge. unfold matrix_time_factor. nia.
  Qed.

  (** A matrix pass has a positive coefficient even when the map clock is zero. *)
  Lemma matrix_time_factor_pos : (1 <= matrix_time_factor)%N.
  Proof.
    unfold matrix_time_factor. nia.
  Qed.

  (** The lattice coefficient covers both widening passes and constant dispatch work. *)
  Lemma matrix_time_factor_lat : (2 * matrix_time_factor + 8 <= c_lat)%N.
  Proof.
    unfold matrix_time_factor, row_time_factor, c_lat. nia.
  Qed.

  (** Comparison dispatch and sparse scanning fit the matrix coefficient. *)
  Lemma T_leb_base_le : forall a b,
    (T_leb a b <= matrix_time_factor * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|ma] [|mb].
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - eapply N.le_trans; [apply T_leb_matrix_le|]. apply N.mul_le_mono_l.
      apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
        apply matrix_code_work_le.
  Qed.

  (** Join dispatch and sparse merging fit the matrix coefficient. *)
  Lemma T_join_base_le : forall a b,
    (T_join a b <= matrix_time_factor * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|ma] [|mb].
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - eapply N.le_trans; [apply T_join_matrix_le|]. apply N.mul_le_mono_l.
      apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
        apply matrix_code_work_le.
  Qed.

  (** Meet dispatch and sparse merging fit the matrix coefficient. *)
  Lemma T_meet_base_le : forall a b,
    (T_meet a b <= matrix_time_factor * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|ma] [|mb].
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - eapply N.le_trans; [apply T_meet_matrix_le|]. apply N.mul_le_mono_l.
      apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
        apply matrix_code_work_le.
  Qed.

  (** The widening merge is bounded by the public sizes of its two matrices. *)
  Lemma T_widen_merge_size : forall ma mb,
    (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <= matrix_time_factor *
      N.of_nat (size (Reached ma) + size (Reached mb) + 1))%N.
  Proof.
    intros ma mb. eapply N.le_trans; [apply T_widen_merge_le|].
    apply N.mul_le_mono_l.
    apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
      apply matrix_code_work_le.
  Qed.

  (** The public inclusion clock is linear in the two raw matrix sizes. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply T_leb_base_le|]. apply N.mul_le_mono_r.
    pose proof matrix_time_factor_lat. lia.
  Qed.

  (** The public join clock is linear in the two raw matrix sizes. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply T_join_base_le|]. apply N.mul_le_mono_r.
    pose proof matrix_time_factor_lat. lia.
  Qed.

  (** Bottom recognition takes constant work within the lattice size bound. *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_lat * N.of_nat (size s + 1))%N.
  Proof.
    intro s. assert (Hclock : (T_is_bot s <= 1)%N).
    { destruct s; time_step. }
    eapply N.le_trans; [exact Hclock|].
    change (1 * 1 <= c_lat * N.of_nat (size s + 1))%N.
    apply N.mul_le_mono; [exact c_lat_pos|lia].
  Qed.

  (** Widening pays for one inclusion check and at most one sparse merge. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b. unfold wsize.
    rewrite Nat.mul_0_r, Nat.add_0_l, Nat.add_0_r.
    pose proof (T_leb_base_le b a) as Hcompare.
    replace (size b + size a + 1) with (size a + size b + 1) in Hcompare by lia.
    set (work := N.of_nat (size a + size b + 1)) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hmerge : forall ma mb, a = Reached ma -> b = Reached mb ->
      (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <=
        matrix_time_factor * work)%N).
    { intros ma mb Ha Hb. subst a b. unfold work. apply T_widen_merge_size. }
    assert (Hbudget : ((2 * matrix_time_factor + 8) * work <= c_lat * work)%N).
    { apply N.mul_le_mono_r. exact matrix_time_factor_lat. }
    clearbody work. unfold T_widen. cbn beta iota zeta.
    destruct (leb b a); cbn beta iota zeta.
    - nia.
    - destruct a as [|ma], b as [|mb]; cbn beta iota zeta.
      + nia.
      + nia.
      + nia.
      + specialize (Hmerge ma mb eq_refl eq_refl). nia.
  Qed.

  (** Narrowing uses the meet clock within the common lattice size bound. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (T_meet_base_le a b) as Hmeet.
    set (work := N.of_nat (size a + size b + 1)) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hbudget : ((2 * matrix_time_factor + 8) * work <= c_lat * work)%N).
    { apply N.mul_le_mono_r. exact matrix_time_factor_lat. }
    clearbody work. unfold T_narrow. cbn beta iota zeta. nia.
  Qed.
  (** Optional zero weights vanish independently of presence. *)
  Lemma option_weight_zero : forall (A : Type) (a : option A),
    option_weight (fun _ => 0) a = 0.
  Proof.
    intros A [a|]; reflexivity.
  Qed.

  (** Stored payload weights inherit a bound established at each successful lookup. *)
  Lemma stored_weight_uniform : forall (A : Type) (w : A -> nat) (m : M.t A) upper,
    (forall p a, M.find p m = Some a -> w a <= upper) ->
    stored_weight w m <= length (M.codes m) * upper.
  Proof.
    intros A w m upper Hbound. unfold stored_weight, sum_weight. apply sum_members_bound.
    intros p Hp. destruct (M.find p m) as [a|] eqn:Ha.
    - change (w a <= upper). exact (Hbound p a Ha).
    - change (0 <= upper). lia.
  Qed.

  (** Zero payload weights leave only skeleton and binding work. *)
  Lemma code_work_zero : forall (A : Type) (m : M.t A),
    code_work (fun _ => 0) m = M.nodes m + length (M.codes m).
  Proof.
    intros A m.
    assert (Hweight : stored_weight (fun _ : A => 0) m <= length (M.codes m) * 0).
    { apply stored_weight_uniform. intros p a Ha. lia. }
    unfold code_work. nia.
  Qed.

  (** A retrieved row uses only the matrix's supported codes. *)
  Lemma row_lookup_support : forall m k p,
    In p (M.codes (row_of (M.get k m))) -> In p (support m).
  Proof.
    intros m k p Hp. apply M.codes_spec in Hp. apply support_find. right.
    exists (K.encode k). unfold raw_entry. now rewrite <- M.get_find.
  Qed.

  (** Each finite entry in a retrieved row satisfies the matrix bit bound. *)
  Lemma row_lookup_bits : forall m k p z,
    M.find p (row_of (M.get k m)) = Some z -> Z.size_nat z <= ell m.
  Proof.
    intros m k p z Hentry. apply (ell_entry m (K.encode k) p z).
    unfold raw_entry. now rewrite <- M.get_find.
  Qed.

  (** A supported row's shifted payload work is bounded by its support and bit maxima. *)
  Lemma code_work_bits_bound : forall m row shift upper,
    (forall p, In p (M.codes row) -> In p (support m)) ->
    (forall p z, M.find p row = Some z -> Z.size_nat z <= upper) ->
    code_work (fun z => shift + Z.size_nat z + 1) row <=
      supp m * (b m + upper + shift + 3).
  Proof.
    intros m row shift upper Hsupport Hbits.
    pose proof (nodes_support Z row m Hsupport) as Hnodes.
    pose proof (codes_support_length Z row m Hsupport) as Hcount.
    assert (Hweight : stored_weight (fun z => shift + Z.size_nat z + 1) row <=
      length (M.codes row) * (shift + upper + 1)).
    { apply stored_weight_uniform. intros p z Hentry.
      pose proof (Hbits p z Hentry). lia. }
    unfold code_work. nia.
  Qed.

  (** Sum bit length is bounded by the two operand bit lengths and one carry bit. *)
  Lemma zbits_add_sum : forall a d,
    Z.size_nat (a + d)%Z <= Z.size_nat a + Z.size_nat d + 1.
  Proof.
    intros a d. apply zbits_add_bound; lia.
  Qed.

  (** Lookup has a small internal coefficient for composition inside closure. *)
  Lemma T_entry_small : forall m i j,
    (T_entry m i j <= 4 * (M.c_map + 1) * N.of_nat (K.bits i + K.bits j + 1))%N.
  Proof.
    intros m i j. time_step.
  Qed.

  (** Insertion has a small internal coefficient independent of old entry bit lengths. *)
  Lemma T_add_cons_small : forall i j d m,
    (T_add_cons i j d m <= 16 * (M.c_map + 1) *
      N.of_nat (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  Proof.
    intros i j d m. time_step.
  Qed.

  (** Diagonal testing compares zero first, so it pays only for the supplied key. *)
  Lemma T_nonnegative_small : forall k m,
    (T_nonnegative k m <= 16 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k m. pose proof (T_entry_small m k k) as Hentry. time_step.
  Qed.

  (** Column-presence testing performs one key lookup. *)
  Lemma T_column_present_small : forall k row,
    (T_column_present k row <= 4 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k row. time_step.
  Qed.

  (** An existential scan pays only for callbacks at stored payloads. *)
  Lemma T_existsb_code_work : forall (A : Type) (f : A -> bool) tf
      (w : A -> nat) (m : M.t A) c,
    (forall a, (tf a <= c * N.of_nat (w a))%N) ->
    (M.T_existsb f tf m <= M.c_map * (c + 1) * N.of_nat (code_work w m + 1))%N.
  Proof.
    intros A f tf w m c Hbound. pose proof (M.T_existsb_sum_le A f tf m) as Hclock.
    assert (Hsum : (fold_right N.add 0%N (map (fun p =>
      match M.find p m with Some a => tf a | None => 0%N end) (M.codes m)) <=
      c * N.of_nat (stored_weight w m))%N).
    { unfold stored_weight. apply time_sum_bound. intros p Hp.
      destruct (M.find p m) as [a|].
      - change (tf a <= c * N.of_nat (w a))%N. apply Hbound.
      - change (0 <= c * N.of_nat 0)%N. nia. }
    eapply N.le_trans; [exact Hclock|].
    replace (M.c_map * (c + 1) * N.of_nat (code_work w m + 1))%N with
      (M.c_map * ((c + 1) * N.of_nat (code_work w m + 1)))%N by ring.
    apply N.mul_le_mono_l. clear Hclock Hbound.
    unfold code_work. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Path relaxation charges prefix bits only when a finite suffix is processed. *)
  Lemma T_via_bound_le : forall a old next,
    (T_via_bound a old next <= 8 * N.of_nat
      (option_weight (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) next + 1))%N.
  Proof.
    intros a old [z|].
    - pose proof (zbits_add_sum a z) as Hsum. destruct old;
        unfold option_weight; time_step.
    - destruct old; unfold option_weight; time_step.
  Qed.

  (** A pivot row update pays for lookup, the source skeleton, and finite pivot payloads. *)
  Definition pivot_row_work (k : K.t) (pivot row : M.t Z) : nat :=
    K.bits k + 1 + code_work (fun _ : Z => 0) row +
      match M.get k row with
      | Some a => code_work (fun z => Z.size_nat a + Z.size_nat z + 1) pivot
      | None => 0
      end.

  (** An inserted edge adds its arithmetic cost to the same sparse row accounting. *)
  Definition increment_row_work (i : K.t) (d : Z) (exit row : M.t Z) : nat :=
    K.bits i + Z.size_nat d + 1 + code_work (fun _ : Z => 0) row +
      match M.get i row with
      | Some a => Z.size_nat a +
          code_work (fun z => Z.size_nat (a + d)%Z + Z.size_nat z + 1) exit
      | None => 0
      end.

  (** A variable key adds one constructor bit to the underlying variable encoding. *)
  Lemma some_key_bits : forall x, K.bits (Some x) = X.bits x + 1.
  Proof.
    intro x. change (S (X.bits x) = X.bits x + 1). lia.
  Qed.

  (** Forgetting one column charges only a key removal at each present row. *)
  Lemma T_forget_row_le : forall x a b,
    (T_forget_row x a b <= (M.c_map + 4) * N.of_nat
      (option_weight (fun _ : M.t Z => (K.bits (Some x) + 1)%nat) a + 1))%N.
  Proof.
    intros x [row|] b; cbn [option_weight]; time_step.
  Qed.

  (** Removing an outer binding leaves only codes from the original support. *)
  Lemma removed_codes_support : forall m k p,
    In p (M.codes (M.remove k m)) -> In p (support m).
  Proof.
    intros m k p Hp. apply M.codes_spec in Hp. rewrite M.find_remove in Hp.
    destruct (Pos.eqb p (K.encode k)); [contradiction|].
    apply support_spec. left. now apply M.codes_spec.
  Qed.

  (** The havoc traversal charges one source node and one key cost per surviving row. *)
  Lemma havoc_code_work_bound : forall m x,
    code_work (fun _ : M.t Z => (K.bits (Some x) + 1)%nat) (M.remove (Some x) m) <=
      supp m * (b m + X.bits x + 4).
  Proof.
    intros m x.
    pose proof (codes_support_length (M.t Z) (M.remove (Some x) m) m
      (removed_codes_support m (Some x))) as Hcount.
    pose proof (nodes_support (M.t Z) (M.remove (Some x) m) m
      (removed_codes_support m (Some x))) as Hnodes.
    pose proof (stored_weight_uniform (M.t Z)
      (fun _ : M.t Z => (K.bits (Some x) + 1)%nat) (M.remove (Some x) m)
      (K.bits (Some x) + 1) ltac:(intros; apply Nat.le_refl)) as Hweight.
    unfold code_work. rewrite some_key_bits in *. nia.
  Qed.

  (** A small concrete coefficient suffices for the raw havoc implementation. *)
  Lemma T_havoc_small : forall x m,
    (T_havoc x (Reached m) <= 32 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1))%N.
  Proof.
    intros x m.
    assert (Hcallback : forall a b,
      (T_forget_row x a b <= (M.c_map + 4) * N.of_nat
        (option_weight (fun _ : M.t Z => (K.bits (Some x) + 1)%nat) a +
          option_weight (fun _ : M.t Z => 0%nat) b + 1))%N).
    { intros a b. rewrite option_weight_zero, Nat.add_0_r. apply T_forget_row_le. }
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) (forget_row x)
      (fun a b => T_forget_row x a b)
      (fun _ : M.t Z => (K.bits (Some x) + 1)%nat) (fun _ : M.t Z => 0)
      (M.remove (Some x) m) M.empty (M.c_map + 4)%N Hcallback) as Hmerge.
    rewrite code_work_empty in Hmerge.
    pose proof (havoc_code_work_bound m x) as Hwork.
    set (work := N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1)).
    assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
    assert (Hmerge' : (M.T_merge (forget_row x)
      (fun a b => T_forget_row x a b) (M.remove (Some x) m) M.empty <=
      M.c_map * (M.c_map + 5) * 2 * work)%N).
    { eapply N.le_trans; [exact Hmerge|].
      replace (M.c_map + 4 + 1)%N with (M.c_map + 5)%N by ring.
      apply N.mul_le_mono_l. unfold work. apply time_of_nat_le. nia. }
    assert (Hremove : (M.T_remove (Some x) m <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_remove_le|].
      apply N.mul_le_mono_l. unfold work. rewrite some_key_bits.
      apply time_of_nat_le. nia. }
    assert (Hsum : (1 + (M.T_remove (Some x) m +
      M.T_merge (forget_row x) (fun a b => T_forget_row x a b)
        (M.remove (Some x) m) M.empty) <=
      (1 + M.c_map + M.c_map * (M.c_map + 5) * 2) * work)%N).
    { rewrite !N.mul_add_distr_r. rewrite N.mul_1_l. lia. }
    assert (Hcoefficient : (1 + M.c_map + M.c_map * (M.c_map + 5) * 2 <=
      32 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    unfold T_havoc. cbn beta iota zeta.
    eapply N.le_trans; [exact Hsum|].
    apply N.mul_le_mono_r. exact Hcoefficient.
  Qed.

  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x [|m].
    - assert (Hconstant : (1 <= c_num)%N) by (unfold c_num; nia).
      assert (Hwork : (1 <= N.of_nat (havoc_work x Unreached + 1))%N) by lia.
      unfold T_havoc. cbn beta iota zeta. nia.
    - pose proof (T_havoc_small x m) as Htime.
      assert (Hwork : (supp m + 1) * (b m + X.bits x + 4) + 1 <=
        4 * (havoc_work x (Reached m) + 1)).
      { unfold havoc_work, ns, bs, ells, skels. cbn [Nat.pow]. nia. }
      assert (Hcast : (N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1) <=
        4 * N.of_nat (havoc_work x (Reached m) + 1))%N).
      { replace (4 * N.of_nat (havoc_work x (Reached m) + 1))%N with
          (N.of_nat (4 * (havoc_work x (Reached m) + 1)))
          by (rewrite Nat2N.inj_mul; reflexivity).
        apply time_of_nat_le. exact Hwork. }
      assert (Hcoefficient : (32 * (M.c_map + 1) * (M.c_map + 1) * 4 <= c_num)%N).
      { unfold c_num. nia. }
      eapply N.le_trans; [exact Htime|].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hcast|].
      rewrite N.mul_assoc. apply N.mul_le_mono_r. exact Hcoefficient.
  Qed.

  (** A pivot callback charges finite source rows with their own sparse update work. *)
  Lemma T_round_row_le : forall k pivot a b,
    (T_round_row k pivot a b <= row_time_factor *
      N.of_nat (option_weight (pivot_row_work k pivot) a + 1))%N.
  Proof.
    intros k pivot [row|] ignored.
    - cbn [option_weight]. unfold pivot_row_work.
      destruct (M.get k row) as [a|] eqn:Ha.
      + assert (Hcallback : forall old next,
          (T_via_bound a old next <= 8 * N.of_nat
            (option_weight (fun _ : Z => 0%nat) old +
             option_weight (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) next + 1))%N).
        { intros old next. rewrite option_weight_zero. apply T_via_bound_le. }
        pose proof (T_merge_code_work Z Z Z (via_bound a)
          (fun x y => T_via_bound a x y) (fun _ : Z => 0)
          (fun z => Z.size_nat a + Z.size_nat z + 1) row pivot 8%N Hcallback) as Hmerge.
        pose proof (M.T_get_le Z k row) as Hget.
        set (lookup_bits := K.bits k + 1) in *.
        set (source_work := code_work (fun _ : Z => 0) row) in *.
        set (pivot_work := code_work (fun z => Z.size_nat a + Z.size_nat z + 1) pivot) in *.
        clearbody lookup_bits source_work pivot_work. clear Hcallback.
        unfold T_round_row. cbn beta iota zeta. rewrite Ha. cbn beta iota zeta.
        set (get_clock := M.T_get k row) in *.
        set (merge_clock := M.T_merge (via_bound a)
          (fun x y => T_via_bound a x y) row pivot) in *.
        clearbody get_clock merge_clock. clear Ha.
        unfold row_time_factor.
        repeat rewrite Nat2N.inj_add in Hget.
        repeat rewrite Nat2N.inj_add in Hmerge.
        repeat rewrite Nat2N.inj_add.
        set (work := (N.of_nat lookup_bits + N.of_nat source_work +
          N.of_nat pivot_work + 1)%N).
        match goal with
        | |- N.le ?clock _ => change (clock <= 32 * (M.c_map + 1) * work)%N
        end.
        assert (Hunit : (1 <= work)%N) by (unfold work; lia).
        assert (Hget_work : (get_clock <= M.c_map * work)%N).
        { eapply N.le_trans; [exact Hget|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hmerge_work : (merge_clock <= M.c_map * (8 + 1) * 2 * work)%N).
        { eapply N.le_trans; [exact Hmerge|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hbudget : ((M.c_map + M.c_map * (8 + 1) * 2 + 1) * work <=
          32 * (M.c_map + 1) * work)%N).
        { apply N.mul_le_mono_r. lia. }
        repeat rewrite N.mul_add_distr_r in Hbudget.
        rewrite N.mul_1_l in Hbudget.
        clear Hget Hmerge. clearbody work. lia.
      + pose proof (M.T_get_le Z k row) as Hget.
        set (lookup_bits := K.bits k + 1) in *.
        set (source_work := code_work (fun _ : Z => 0) row) in *.
        clearbody lookup_bits source_work.
        unfold T_round_row. cbn beta iota zeta. rewrite Ha. cbn beta iota zeta.
        set (get_clock := M.T_get k row) in *. clearbody get_clock. clear Ha.
        unfold row_time_factor.
        repeat rewrite Nat2N.inj_add in Hget.
        repeat rewrite Nat2N.inj_add.
        set (work := (N.of_nat lookup_bits + N.of_nat source_work + 0 + 1)%N).
        match goal with
        | |- N.le ?clock _ => change (clock <= 32 * (M.c_map + 1) * work)%N
        end.
        assert (Hunit : (1 <= work)%N) by (unfold work; lia).
        assert (Hget_work : (get_clock <= M.c_map * work)%N).
        { eapply N.le_trans; [exact Hget|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hbudget : ((M.c_map + 1) * work <= 32 * (M.c_map + 1) * work)%N).
        { apply N.mul_le_mono_r. lia. }
        rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
        clear Hget. clearbody work. lia.
    - unfold row_time_factor. time_step.
  Qed.

  (** An incremental callback charges the inserted-bound addition once for each finite row. *)
  Lemma T_increment_row_le : forall i d exit a b,
    (T_increment_row i d exit a b <= row_time_factor *
      N.of_nat (option_weight (increment_row_work i d exit) a + 1))%N.
  Proof.
    intros i d exit [row|] ignored.
    - cbn [option_weight]. unfold increment_row_work.
      destruct (M.get i row) as [a|] eqn:Ha.
      + assert (Hcallback : forall old next,
          (T_via_bound (a + d)%Z old next <= 8 * N.of_nat
            (option_weight (fun _ : Z => 0%nat) old +
             option_weight (fun z =>
               (Z.size_nat (a + d)%Z + Z.size_nat z + 1)%nat) next + 1))%N).
        { intros old next. rewrite option_weight_zero. apply T_via_bound_le. }
        pose proof (T_merge_code_work Z Z Z (via_bound (a + d)%Z)
          (fun x y => T_via_bound (a + d)%Z x y) (fun _ : Z => 0)
          (fun z => Z.size_nat (a + d)%Z + Z.size_nat z + 1) row exit 8%N Hcallback)
          as Hmerge.
        pose proof (M.T_get_le Z i row) as Hget. pose proof (Z.T_add_le a d) as Hadd.
        set (key_bits := K.bits i) in *.
        set (edge_bits := Z.size_nat d) in *.
        set (prefix_bits := Z.size_nat a) in *.
        set (source_work := code_work (fun _ : Z => 0) row) in *.
        set (exit_work := code_work
          (fun z => Z.size_nat (a + d)%Z + Z.size_nat z + 1) exit) in *.
        clearbody key_bits edge_bits prefix_bits source_work exit_work. clear Hcallback.
        unfold T_increment_row. cbn beta iota zeta. rewrite Ha. cbn beta iota zeta.
        set (get_clock := M.T_get i row) in *.
        set (add_clock := Z.T_add a d) in *.
        set (merge_clock := M.T_merge (via_bound (a + d)%Z)
          (fun x y => T_via_bound (a + d)%Z x y) row exit) in *.
        clearbody get_clock add_clock merge_clock. clear Ha.
        unfold row_time_factor.
        repeat rewrite Nat2N.inj_add in Hget.
        repeat rewrite Nat2N.inj_add in Hadd.
        repeat rewrite Nat2N.inj_add in Hmerge.
        repeat rewrite Nat2N.inj_add.
        set (work := (N.of_nat key_bits + N.of_nat edge_bits + 1 +
          N.of_nat source_work + (N.of_nat prefix_bits + N.of_nat exit_work) + 1)%N).
        match goal with
        | |- N.le ?clock _ => change (clock <= 32 * (M.c_map + 1) * work)%N
        end.
        assert (Hunit : (1 <= work)%N) by (unfold work; lia).
        assert (Hget_work : (get_clock <= M.c_map * work)%N).
        { eapply N.le_trans; [exact Hget|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hadd_work : (add_clock <= 3 * work)%N).
        { unfold work. lia. }
        assert (Hmerge_work : (merge_clock <= M.c_map * (8 + 1) * 2 * work)%N).
        { eapply N.le_trans; [exact Hmerge|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hbudget : ((M.c_map + 3 + M.c_map * (8 + 1) * 2 + 1) * work <=
          32 * (M.c_map + 1) * work)%N).
        { apply N.mul_le_mono_r. lia. }
        repeat rewrite N.mul_add_distr_r in Hbudget.
        rewrite N.mul_1_l in Hbudget.
        clear Hget Hadd Hmerge. clearbody work. lia.
      + pose proof (M.T_get_le Z i row) as Hget.
        set (key_bits := K.bits i) in *.
        set (edge_bits := Z.size_nat d) in *.
        set (source_work := code_work (fun _ : Z => 0) row) in *.
        clearbody key_bits edge_bits source_work.
        unfold T_increment_row. cbn beta iota zeta. rewrite Ha. cbn beta iota zeta.
        set (get_clock := M.T_get i row) in *. clearbody get_clock. clear Ha.
        unfold row_time_factor.
        repeat rewrite Nat2N.inj_add in Hget.
        repeat rewrite Nat2N.inj_add.
        set (work := (N.of_nat key_bits + N.of_nat edge_bits + 1 +
          N.of_nat source_work + 0 + 1)%N).
        match goal with
        | |- N.le ?clock _ => change (clock <= 32 * (M.c_map + 1) * work)%N
        end.
        assert (Hunit : (1 <= work)%N) by (unfold work; lia).
        assert (Hget_work : (get_clock <= M.c_map * work)%N).
        { eapply N.le_trans; [exact Hget|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hbudget : ((M.c_map + 1) * work <= 32 * (M.c_map + 1) * work)%N).
        { apply N.mul_le_mono_r. lia. }
        rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
        clear Hget. clearbody work. lia.
    - unfold row_time_factor. time_step.
  Qed.
  (** A finite source row bounds each prefix by the matrix's integer-bit maximum. *)
  Lemma row_get_bits : forall m p row k a,
    M.find p m = Some row -> M.get k row = Some a -> Z.size_nat a <= ell m.
  Proof.
    intros m p row k a Hrow Ha. apply (ell_entry m p (K.encode k) a).
    unfold raw_entry. rewrite Hrow. cbn [row_of]. now rewrite <- M.get_find.
  Qed.

  (** Pivot work charges each source skeleton once and one supported pivot row. *)
  Lemma pivot_row_work_bound : forall m k row, In row (rows m) ->
    pivot_row_work k (row_of (M.get k m)) row <=
      M.nodes row + K.bits k + 1 + supp m * (b m + 2 * ell m + 4).
  Proof.
    intros m k row Hin.
    assert (Hsupport : forall q, In q (M.codes row) -> In q (support m)).
    { intros q Hq. apply support_spec. right. apply in_flat_map. exists row. now split. }
    pose proof (codes_support_length Z row m Hsupport) as Hcount.
    apply rows_find in Hin. destruct Hin as [p Hrow].
    unfold pivot_row_work. rewrite code_work_zero.
    replace (supp m * (b m + 2 * ell m + 4)) with
      (supp m + supp m * (b m + 2 * ell m + 3)) by ring.
    destruct (M.get k row) as [a|] eqn:Ha.
    - pose proof (row_get_bits m p row k a Hrow Ha) as Hprefix.
      pose proof (code_work_bits_bound m (row_of (M.get k m)) (Z.size_nat a) (ell m)
        (row_lookup_support m k) (row_lookup_bits m k)) as Hexit.
      assert (Hexit_cap : code_work (fun z => Z.size_nat a + Z.size_nat z + 1)
        (row_of (M.get k m)) <= supp m * (b m + 2 * ell m + 3)).
      { eapply Nat.le_trans; [exact Hexit|]. apply Nat.mul_le_mono_l. lia. }
      clear Hexit Hrow Ha Hsupport. lia.
    - lia.
  Qed.

  (** Incremental row work adds the new-edge bits to the supported prefix and suffix. *)
  Lemma increment_row_work_bound : forall m i j d row, In row (rows m) ->
    increment_row_work i d (row_of (M.get j m)) row <=
      M.nodes row + K.bits i + Z.size_nat d + ell m + 1 +
      supp m * (b m + 2 * ell m + Z.size_nat d + 5).
  Proof.
    intros m i j d row Hin.
    assert (Hsupport : forall q, In q (M.codes row) -> In q (support m)).
    { intros q Hq. apply support_spec. right. apply in_flat_map. exists row. now split. }
    pose proof (codes_support_length Z row m Hsupport) as Hcount.
    apply rows_find in Hin. destruct Hin as [p Hrow].
    unfold increment_row_work. rewrite code_work_zero.
    replace (supp m * (b m + 2 * ell m + Z.size_nat d + 5)) with
      (supp m + supp m * (b m + 2 * ell m + Z.size_nat d + 4)) by ring.
    destruct (M.get i row) as [a|] eqn:Ha.
    - pose proof (row_get_bits m p row i a Hrow Ha) as Hprefix.
      pose proof (zbits_add_sum a d) as Hsum.
      pose proof (code_work_bits_bound m (row_of (M.get j m))
        (Z.size_nat (a + d)%Z) (ell m) (row_lookup_support m j) (row_lookup_bits m j))
        as Hexit.
      assert (Hexit_cap : code_work
        (fun z => Z.size_nat (a + d)%Z + Z.size_nat z + 1) (row_of (M.get j m)) <=
        supp m * (b m + 2 * ell m + Z.size_nat d + 4)).
      { eapply Nat.le_trans; [exact Hexit|]. apply Nat.mul_le_mono_l. lia. }
      clear Hexit Hrow Ha Hsupport Hsum. lia.
    - lia.
  Qed.

  (** A positive quadratic budget covers the number of supported codes. *)
  Lemma quadratic_work_count : forall n payload, 1 <= payload ->
    n <= (n + 1)^2 * payload.
  Proof.
    intros n payload Hpositive. eapply Nat.le_trans with ((n + 1)^2).
    - cbn [Nat.pow]. nia.
    - replace ((n + 1)^2) with (((n + 1)^2) * 1) at 1 by ring.
      now apply Nat.mul_le_mono_l.
  Qed.

  (** Summing a linear row allowance over the support yields a quadratic allowance. *)
  Lemma quadratic_work_rows : forall n payload factor rowwork,
    rowwork <= factor * (n + 1) * payload ->
    n * rowwork <= factor * (n + 1)^2 * payload.
  Proof.
    intros n payload factor rowwork Hrow.
    eapply Nat.le_trans; [apply Nat.mul_le_mono_l; exact Hrow|].
    replace (n * (factor * (n + 1) * payload)) with
      (factor * (n * (n + 1)) * payload) by ring.
    apply Nat.mul_le_mono_r, Nat.mul_le_mono_l. cbn [Nat.pow]. nia.
  Qed.

  (** Pivot lookup and payload units fit four linear support allowances. *)
  Lemma pivot_scalar_work_bound : forall n bb kk ee,
    kk + 1 + n * (bb + 2 * ee + 4) <= 4 * (n + 1) * (bb + kk + ee + 1).
  Proof.
    intros n bb kk ee. nia.
  Qed.

  (** Incremental lookup and payload units fit six linear support allowances. *)
  Lemma increment_scalar_work_bound : forall n bb kk ee dd,
    kk + dd + ee + 1 + n * (bb + 2 * ee + dd + 5) <=
      6 * (n + 1) * (bb + kk + ee + dd + 1).
  Proof.
    intros n bb kk ee dd. nia.
  Qed.

  (** Summing pivot callbacks preserves an additive charge for the source skeleton. *)
  Lemma pivot_matrix_work_bound : forall m k,
    code_work (pivot_row_work k (row_of (M.get k m))) m <=
      6 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1).
  Proof.
    intros m k.
    assert (Hcount : length (M.codes m) <= supp m).
    { apply codes_support_length. intros p Hp. apply support_spec. now left. }
    pose proof (rows_length m) as Hrows.
    assert (Hsum : sum_weight (pivot_row_work k (row_of (M.get k m))) (rows m) <=
      sum_weight (fun row => M.nodes row +
        (K.bits k + 1 + supp m * (b m + 2 * ell m + 4))) (rows m)).
    { apply sum_weight_mono. intros row Hin.
      pose proof (pivot_row_work_bound m k row Hin). lia. }
    rewrite sum_weight_add, sum_weight_const in Hsum.
    change (sum_weight (pivot_row_work k (row_of (M.get k m))) (rows m) <=
      sum_weight M.nodes (rows m) + length (rows m) *
        (K.bits k + 1 + supp m * (b m + 2 * ell m + 4))) in Hsum.
    assert (Hprod : length (rows m) * (K.bits k + 1 +
      supp m * (b m + 2 * ell m + 4)) <=
      supp m * (K.bits k + 1 + supp m * (b m + 2 * ell m + 4))).
    { apply Nat.mul_le_mono_r. lia. }
    pose proof (skel_le m) as Hskel.
    change (M.nodes m + sum_weight M.nodes (rows m) <=
      (supp m + 1)^2 * (b m + 1)) in Hskel.
    unfold code_work at 1. rewrite stored_weight_rows.
    set (units := (supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
    replace (6 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1)) with
      (6 * units) by (unfold units; ring).
    assert (Hcount_units : supp m <= units).
    { unfold units. apply quadratic_work_count. lia. }
    assert (Hskel_units : M.nodes m + sum_weight M.nodes (rows m) <= units).
    { eapply Nat.le_trans; [exact Hskel|]. unfold units. apply Nat.mul_le_mono_l. lia. }
    assert (Hprod_units : length (rows m) * (K.bits k + 1 +
      supp m * (b m + 2 * ell m + 4)) <= 4 * units).
    { eapply Nat.le_trans; [exact Hprod|]. unfold units.
      replace (4 * ((supp m + 1)^2 * (b m + K.bits k + ell m + 1))) with
        (4 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1)) by ring.
      apply quadratic_work_rows, pivot_scalar_work_bound. }
    clear Hskel Hprod Hrows. clearbody units. lia.
  Qed.

  (** Incremental callback work remains quadratic in raw support and linear in bit bounds. *)
  Lemma increment_matrix_work_bound : forall m i j d,
    code_work (increment_row_work i d (row_of (M.get j m))) m <=
      8 * (supp m + 1)^2 * (b m + K.bits i + ell m + Z.size_nat d + 1).
  Proof.
    intros m i j d.
    assert (Hcount : length (M.codes m) <= supp m).
    { apply codes_support_length. intros p Hp. apply support_spec. now left. }
    pose proof (rows_length m) as Hrows.
    assert (Hsum : sum_weight (increment_row_work i d (row_of (M.get j m))) (rows m) <=
      sum_weight (fun row => M.nodes row + (K.bits i + Z.size_nat d + ell m + 1 +
        supp m * (b m + 2 * ell m + Z.size_nat d + 5))) (rows m)).
    { apply sum_weight_mono. intros row Hin.
      pose proof (increment_row_work_bound m i j d row Hin). lia. }
    rewrite sum_weight_add, sum_weight_const in Hsum.
    change (sum_weight (increment_row_work i d (row_of (M.get j m))) (rows m) <=
      sum_weight M.nodes (rows m) + length (rows m) * (K.bits i + Z.size_nat d + ell m + 1 +
        supp m * (b m + 2 * ell m + Z.size_nat d + 5))) in Hsum.
    assert (Hprod : length (rows m) * (K.bits i + Z.size_nat d + ell m + 1 +
      supp m * (b m + 2 * ell m + Z.size_nat d + 5)) <=
      supp m * (K.bits i + Z.size_nat d + ell m + 1 +
        supp m * (b m + 2 * ell m + Z.size_nat d + 5))).
    { apply Nat.mul_le_mono_r. lia. }
    pose proof (skel_le m) as Hskel.
    change (M.nodes m + sum_weight M.nodes (rows m) <=
      (supp m + 1)^2 * (b m + 1)) in Hskel.
    unfold code_work at 1. rewrite stored_weight_rows.
    set (units := (supp m + 1)^2 * (b m + K.bits i + ell m + Z.size_nat d + 1)).
    replace (8 * (supp m + 1)^2 * (b m + K.bits i + ell m + Z.size_nat d + 1)) with
      (8 * units) by (unfold units; ring).
    assert (Hcount_units : supp m <= units).
    { unfold units. apply quadratic_work_count. lia. }
    assert (Hskel_units : M.nodes m + sum_weight M.nodes (rows m) <= units).
    { eapply Nat.le_trans; [exact Hskel|]. unfold units. apply Nat.mul_le_mono_l. lia. }
    assert (Hprod_units : length (rows m) * (K.bits i + Z.size_nat d + ell m + 1 +
      supp m * (b m + 2 * ell m + Z.size_nat d + 5)) <= 6 * units).
    { eapply Nat.le_trans; [exact Hprod|]. unfold units.
      replace (6 * ((supp m + 1)^2 * (b m + K.bits i + ell m + Z.size_nat d + 1))) with
        (6 * (supp m + 1)^2 * (b m + K.bits i + ell m + Z.size_nat d + 1)) by ring.
      apply quadratic_work_rows, increment_scalar_work_bound. }
    clear Hskel Hprod Hrows. clearbody units. lia.
  Qed.

  (** A nonempty support grid covers one payload allowance. *)
  Lemma quadratic_payload_le : forall n payload,
    payload <= (n + 1)^2 * payload.
  Proof.
    intros n payload. replace payload with (1 * payload) at 1 by ring.
    apply Nat.mul_le_mono_r. cbn [Nat.pow]. nia.
  Qed.

  (** A merge against an empty right input charges only present left payloads. *)
  Lemma T_merge_left_code_work : forall (A B C : Type)
      (f : option A -> option B -> option C) tf (w : A -> nat) (m : M.t A) c,
    (forall a b, (tf a b <= c * N.of_nat (option_weight w a + 1))%N) ->
    (M.T_merge f tf m (@M.empty B) <= M.c_map * (c + 1) * 2 *
      N.of_nat (code_work w m + 1))%N.
  Proof.
    intros A B C f tf w m c Hbound.
    assert (Hcallback : forall a b,
      (tf a b <= c * N.of_nat (option_weight w a +
        option_weight (fun _ : B => 0%nat) b + 1))%N).
    { intros a b. rewrite option_weight_zero, Nat.add_0_r. apply Hbound. }
    pose proof (T_merge_code_work A B C f tf w (fun _ : B => 0) m M.empty c Hcallback)
      as Hmerge. rewrite code_work_empty, Nat.add_0_r in Hmerge. exact Hmerge.
  Qed.

  (** A sparse pivot update uses a quadratic raw-support work budget. *)
  Definition relax_time_factor : N := (512 * (M.c_map + 1) * (M.c_map + 1))%N.

  (** One relaxation pays for one pivot-row lookup and the supported row updates. *)
  Lemma T_relax_round_small : forall k m,
    (T_relax_round k m <= relax_time_factor * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof.
    intros k m.
    set (units := (supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
    change (T_relax_round k m <= relax_time_factor * N.of_nat units)%N.
    assert (Hkey : K.bits k + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (pivot_matrix_work_bound m k) as Hmatrix.
    replace (6 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1)) with
      (6 * units) in Hmatrix by (unfold units; ring).
    assert (Hdata : code_work (pivot_row_work k (row_of (M.get k m))) m + 1 <= 7 * units).
    { lia. }
    pose proof (time_of_nat_le _ _ Hdata) as HdataN. rewrite Nat2N.inj_mul in HdataN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    clear Hpositive Hkey Hmatrix Hdata. clearbody work. clear units.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (round_row k (row_of (M.get k m)))
      (fun x y => T_round_row k (row_of (M.get k m)) x y)
      (pivot_row_work k (row_of (M.get k m))) m row_time_factor
      (T_round_row_le k (row_of (M.get k m)))) as Hmerge.
    assert (Hmerge' : (M.T_merge (round_row k (row_of (M.get k m)))
      (fun x y => T_round_row k (row_of (M.get k m)) x y) m M.empty <=
      M.c_map * (row_time_factor + 1) * 2 * (7 * work))%N).
    { eapply N.le_trans; [exact Hmerge|]. apply N.mul_le_mono_l. exact HdataN. }
    assert (Hget : (M.T_get k m <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|]. apply N.mul_le_mono_l. exact HkeyN. }
    pose proof (T_row_of_le (M.get k m)) as Hrow.
    assert (Hcoefficient : (M.c_map * (row_time_factor + 1) * 2 * 7 + M.c_map + 4 <=
      relax_time_factor)%N).
    { unfold row_time_factor, relax_time_factor. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    clear Hmerge HdataN HkeyN Hcoefficient.
    replace (M.c_map * (row_time_factor + 1) * 2 * (7 * work))%N with
      ((M.c_map * (row_time_factor + 1) * 2 * 7) * work)%N in Hmerge' by ring.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    unfold T_relax_round. cbn beta iota zeta. lia.
  Qed.

  (** Pivot-presence checking charges lookup bits only at finite outer rows. *)
  Lemma T_pivot_present_small : forall k m,
    (T_pivot_present k m <= 8 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat
      (M.nodes m + length (M.codes m) * (K.bits k + 2) + K.bits k + 1))%N.
  Proof.
    intros k m.
    set (units := M.nodes m + length (M.codes m) * (K.bits k + 2) + K.bits k + 1).
    change (T_pivot_present k m <=
      8 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    assert (Hpositive : 1 <= units) by (unfold units; lia).
    assert (Hkey : K.bits k + 1 <= units) by (unfold units; lia).
    assert (Hweight : stored_weight (fun _ : M.t Z => K.bits k + 1) m <=
      length (M.codes m) * (K.bits k + 1)).
    { apply stored_weight_uniform. intros p row Hrow. lia. }
    assert (Hdata : code_work (fun _ : M.t Z => K.bits k + 1) m + 1 <= units).
    { unfold code_work, units.
      replace (length (M.codes m) * (K.bits k + 2)) with
        (length (M.codes m) * (K.bits k + 1) + length (M.codes m)) by ring.
      lia. }
    pose proof (time_of_nat_le _ _ Hdata) as HdataN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    clear Hpositive Hkey Hweight Hdata. clearbody work. clear units.
    pose proof (T_existsb_code_work (M.t Z) (column_present k)
      (fun row => T_column_present k row) (fun _ : M.t Z => K.bits k + 1)
      m (4 * (M.c_map + 1))%N (T_column_present_small k)) as Hscan.
    assert (Hscan' : (M.T_existsb (column_present k) (fun row => T_column_present k row) m <=
      M.c_map * (4 * (M.c_map + 1) + 1) * work)%N).
    { eapply N.le_trans; [exact Hscan|]. apply N.mul_le_mono_l. exact HdataN. }
    assert (Hget : (M.T_get k m <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|]. apply N.mul_le_mono_l. exact HkeyN. }
    assert (Hcoefficient : (M.c_map * (4 * (M.c_map + 1) + 1) + M.c_map + 4 <=
      8 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    clear Hscan HdataN HkeyN Hcoefficient.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    unfold T_pivot_present. cbn beta iota zeta.
    destruct (M.get k m); cbn beta iota zeta; lia.
  Qed.

  (** Pivot-presence work fits the same quadratic budget as the round. *)
  Lemma pivot_test_work_bound : forall k m,
    M.nodes m + length (M.codes m) * (K.bits k + 2) + K.bits k + 1 <=
      3 * ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
  Proof.
    intros k m.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Hsupport) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Hsupport) as Hcount.
    cbn [Nat.pow]. nia.
  Qed.

  (** Materializing a supported diagonal changes neither support count nor key-bit maximum. *)
  Lemma seed_round_sizes : forall k m, pivot_present k m = true ->
    supp (add_cons k k 0%Z m) = supp m /\ b (add_cons k k 0%Z m) = b m.
  Proof.
    intros k m Hpresent. apply pivot_present_support in Hpresent. apply support_sizes.
    intro p. rewrite support_add_cons. split.
    - intros [Heq | [Heq | Hin]]; subst; assumption.
    - intro Hin. right. now right.
  Qed.

  (** A complete pivot round fits the raw-support budget, including its presence test. *)
  Lemma T_fw_round_raw : forall k m,
    (T_fw_round k m <= k_zone * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof.
    intros k m.
    set (units := (supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
    change (T_fw_round k m <= k_zone * N.of_nat units)%N.
    assert (Hkey : K.bits k + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (pivot_test_work_bound k m) as Htest.
    fold units in Htest.
    pose proof (time_of_nat_le _ _ Htest) as HtestN. rewrite Nat2N.inj_mul in HtestN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hpresent : (T_pivot_present k m <=
      24 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_pivot_present_small|].
      replace (24 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (8 * (M.c_map + 1) * (M.c_map + 1) * (3 * work))%N by ring.
      apply N.mul_le_mono_l. exact HtestN. }
    assert (Hinsert : (T_add_cons k k 0%Z m <= 32 * (M.c_map + 1) * work)%N).
    { pose proof (T_add_cons_small k k 0%Z m) as Hadd.
      replace (K.bits k + K.bits k + Z.size_nat 0%Z + 1) with
        (K.bits k + K.bits k + 1) in Hadd by (cbn [Z.size_nat]; lia).
      repeat rewrite Nat2N.inj_add in Hadd.
      repeat rewrite Nat2N.inj_add in HkeyN.
      eapply N.le_trans; [exact Hadd|].
      replace (32 * (M.c_map + 1) * work)%N with
        (16 * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l. lia. }
    assert (Hcoefficient : (relax_time_factor +
      24 * (M.c_map + 1) * (M.c_map + 1) + 32 * (M.c_map + 1) + 8 <= k_zone)%N).
    { unfold relax_time_factor, k_zone. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    destruct (pivot_present k m) eqn:Hcheck.
    - destruct (seed_round_sizes k m Hcheck) as [Hsupport Hbits].
      assert (Hell : ell (add_cons k k 0%Z m) <= ell m).
      { apply ell_add_cons; [lia|change (0 <= ell m); lia]. }
      assert (Hrelax : (T_relax_round k (add_cons k k 0%Z m) <=
        relax_time_factor * work)%N).
      { eapply N.le_trans; [apply T_relax_round_small|]. apply N.mul_le_mono_l.
        unfold work, units. apply time_of_nat_le. rewrite Hsupport, Hbits.
        apply Nat.mul_le_mono_l. lia. }
      clear Hpositive Hkey Htest HtestN HkeyN Hcoefficient Hsupport Hbits Hell.
      clearbody work. clear units. unfold T_fw_round. rewrite Hcheck.
      cbn beta iota zeta. lia.
    - pose proof (T_relax_round_small k m) as Hrelax.
      change (T_relax_round k m <= relax_time_factor * work)%N in Hrelax.
      clear Hpositive Hkey Htest HtestN HkeyN Hcoefficient.
      clearbody work. clear units. unfold T_fw_round. rewrite Hcheck.
      cbn beta iota zeta. lia.
  Qed.

  (** A consistent pivot round satisfies the promised quadratic timing bound. *)
  Lemma T1_fw_round : forall k m, dbm_wf m ->
    (T_fw_round k m <= k_zone * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof.
    intros k m Hwf. apply T_fw_round_raw.
  Qed.

  (** An incremental pass pays for one exit lookup and its sparse path updates. *)
  Lemma increment_pass_clock_le : forall i j d m,
    (M.T_get j m + T_row_of (M.get j m) +
      M.T_merge (increment_row i d (row_of (M.get j m)))
        (fun x y => T_increment_row i d (row_of (M.get j m)) x y) m M.empty <=
      1024 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat
        ((supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)))%N.
  Proof.
    intros i j d m.
    set (units := (supp m + 1)^2 *
      (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)).
    assert (Hkey : K.bits j + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (increment_matrix_work_bound m i j d) as Hmatrix.
    assert (Hmatrix_units : code_work (increment_row_work i d (row_of (M.get j m))) m <=
      8 * units).
    { eapply Nat.le_trans; [exact Hmatrix|]. unfold units.
      replace (8 * ((supp m + 1)^2 *
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1))) with
        (8 * (supp m + 1)^2 *
          (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)) by ring.
      apply Nat.mul_le_mono_l. lia. }
    assert (Hdata : code_work (increment_row_work i d (row_of (M.get j m))) m + 1 <=
      9 * units).
    { lia. }
    pose proof (time_of_nat_le _ _ Hdata) as HdataN. rewrite Nat2N.inj_mul in HdataN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    change (M.T_get j m + T_row_of (M.get j m) +
      M.T_merge (increment_row i d (row_of (M.get j m)))
        (fun x y => T_increment_row i d (row_of (M.get j m)) x y) m M.empty <=
      1024 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    clear Hpositive Hkey Hmatrix Hmatrix_units Hdata. clearbody work. clear units.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (increment_row i d (row_of (M.get j m)))
      (fun x y => T_increment_row i d (row_of (M.get j m)) x y)
      (increment_row_work i d (row_of (M.get j m))) m row_time_factor
      (T_increment_row_le i d (row_of (M.get j m)))) as Hmerge.
    assert (Hmerge' : (M.T_merge (increment_row i d (row_of (M.get j m)))
      (fun x y => T_increment_row i d (row_of (M.get j m)) x y) m M.empty <=
      M.c_map * (row_time_factor + 1) * 2 * (9 * work))%N).
    { eapply N.le_trans; [exact Hmerge|]. apply N.mul_le_mono_l. exact HdataN. }
    assert (Hget : (M.T_get j m <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|]. apply N.mul_le_mono_l. exact HkeyN. }
    pose proof (T_row_of_le (M.get j m)) as Hrow.
    assert (Hcoefficient : (M.c_map * (row_time_factor + 1) * 2 * 9 + M.c_map + 4 <=
      1024 * (M.c_map + 1) * (M.c_map + 1))%N).
    { unfold row_time_factor. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    replace (M.c_map * (row_time_factor + 1) * 2 * (9 * work))%N with
      ((M.c_map * (row_time_factor + 1) * 2 * 9) * work)%N in Hmerge' by ring.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    clear Hmerge HdataN HkeyN Hcoefficient. lia.
  Qed.

  (** Seeding the two endpoint diagonals adds only those endpoints and the new bound bits. *)
  Lemma increment_seed_bounds : forall i j d m,
    let seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m)) in
    supp seed <= supp m + 2 /\
    b seed <= Nat.max (b m) (Nat.max (K.bits i) (K.bits j)) /\
    ell seed <= Nat.max (ell m) (Z.size_nat d).
  Proof.
    intros i j d m. cbn beta iota zeta.
    set (seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m))).
    assert (Hsupport : forall p, In p (support seed) ->
      p = K.encode i \/ p = K.encode j \/ In p (support m)).
    { intros p Hin. unfold seed in Hin. rewrite !support_add_cons in Hin. tauto. }
    destruct (support_endpoints i j seed m Hsupport) as [Hcount Hbits].
    split; [exact Hcount|]. split; [exact Hbits|].
    unfold seed. apply ell_add_cons; [|apply Nat.le_max_r].
    apply ell_add_cons; [|change (0 <= Nat.max (ell m) (Z.size_nat d)); lia].
    apply ell_add_cons; [apply Nat.le_max_l|
      change (0 <= Nat.max (ell m) (Z.size_nat d)); lia].
  Qed.

  (** Incremental closure charges its seed, one path pass, and two constant-sign checks. *)
  Lemma T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_zone * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat))%N.
  Proof.
    intros i j d m.
    replace (c_zone * N.of_nat ((supp m + 1)^2) *
      N.of_nat (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1))%N with
      (c_zone * N.of_nat ((supp m + 1)^2 *
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)))%N
      by (rewrite (Nat2N.inj_mul ((supp m + 1)^2)
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)); ring).
    set (units := (supp m + 1)^2 *
      (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)).
    set (seed := add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m))).
    set (next := M.merge (increment_row i d (row_of (M.get j seed))) seed M.empty).
    assert (Hkey : K.bits i + K.bits j + Z.size_nat d + 1 <= units)
      by (unfold units; eapply Nat.le_trans; [|apply quadratic_payload_le]; lia).
    assert (Hpositive : 1 <= units) by lia.
    destruct (increment_seed_bounds i j d m) as [Hcount [Hbits Hell]].
    fold seed in Hcount, Hbits, Hell.
    assert (Hbcap : Nat.max (b m) (Nat.max (K.bits i) (K.bits j)) <=
      b m + K.bits i + K.bits j).
    { apply Nat.max_lub; [lia|apply Nat.max_lub; lia]. }
    assert (Hecap : Nat.max (ell m) (Z.size_nat d) <= ell m + Z.size_nat d).
    { apply Nat.max_lub; lia. }
    assert (Hsquare : (supp seed + 1)^2 <= 9 * (supp m + 1)^2)
      by (cbn [Nat.pow]; nia).
    assert (Hpayload : b seed + K.bits i + K.bits j + ell seed + Z.size_nat d + 1 <=
      2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)) by lia.
    assert (Hpasswork : (supp seed + 1)^2 *
      (b seed + K.bits i + K.bits j + ell seed + Z.size_nat d + 1) <= 18 * units).
    { eapply Nat.le_trans; [apply Nat.mul_le_mono; [exact Hsquare|exact Hpayload]|].
      unfold units. nia. }
    pose proof (time_of_nat_le _ _ Hpasswork) as HpassN.
    replace (N.of_nat (18 * units)) with (18 * N.of_nat units)%N in HpassN
      by (rewrite (Nat2N.inj_mul 18 units); reflexivity).
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hpass : (M.T_get j seed + T_row_of (M.get j seed) +
      M.T_merge (increment_row i d (row_of (M.get j seed)))
        (fun x y => T_increment_row i d (row_of (M.get j seed)) x y) seed M.empty <=
      18432 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply increment_pass_clock_le|].
      replace (18432 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (1024 * (M.c_map + 1) * (M.c_map + 1) * (18 * work))%N by ring.
      apply N.mul_le_mono_l. exact HpassN. }
    assert (Hinsert : forall x y z state,
      K.bits x + K.bits y + Z.size_nat z + 1 <= 2 * units ->
      (T_add_cons x y z state <= 32 * (M.c_map + 1) * work)%N).
    { intros x y z state Hsize. eapply N.le_trans; [apply T_add_cons_small|].
      pose proof (time_of_nat_le _ _ Hsize) as HsizeN. rewrite Nat2N.inj_mul in HsizeN.
      fold work in HsizeN.
      replace (32 * (M.c_map + 1) * work)%N with
        (16 * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l. exact HsizeN. }
    assert (Hi : (T_add_cons i i 0%Z m <= 32 * (M.c_map + 1) * work)%N).
    { apply Hinsert. cbn [Z.size_nat]. lia. }
    assert (Hj : (T_add_cons j j 0%Z (add_cons i i 0%Z m) <=
      32 * (M.c_map + 1) * work)%N).
    { apply Hinsert. cbn [Z.size_nat]. lia. }
    assert (Hij : (T_add_cons i j d (add_cons j j 0%Z (add_cons i i 0%Z m)) <=
      32 * (M.c_map + 1) * work)%N).
    { apply Hinsert. lia. }
    assert (Hdiag : forall k, K.bits k + 1 <= units ->
      (T_nonnegative k next <= 16 * (M.c_map + 1) * work)%N).
    { intros k Hsize. eapply N.le_trans; [apply T_nonnegative_small|].
      apply N.mul_le_mono_l. unfold work. now apply time_of_nat_le. }
    assert (Hdi : (T_nonnegative i next <= 16 * (M.c_map + 1) * work)%N).
    { apply Hdiag. lia. }
    assert (Hdj : (T_nonnegative j next <= 16 * (M.c_map + 1) * work)%N).
    { apply Hdiag. lia. }
    assert (Hcoefficient : (18432 * (M.c_map + 1) * (M.c_map + 1) +
      128 * (M.c_map + 1) + 16 <= c_zone)%N) by (unfold c_zone; nia).
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    clear Hpositive Hkey Hcount Hbits Hell Hbcap Hecap Hsquare Hpayload Hpasswork
      HpassN HkeyN Hinsert Hdiag Hcoefficient.
    clearbody work. clear units. unfold T_incr_close. cbn beta iota zeta.
    fold seed next. time_simpl. cbn beta iota zeta.
    destruct (andb (nonnegative i next) (nonnegative j next)); cbn beta iota zeta; lia.
  Qed.

  (** Consistent labels inject into any raw support containing their stored codes. *)
  Lemma elements_support_length : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    length (M.elements r) <= supp m.
  Proof.
    intros A r m Hwf Hsupport.
    assert (Hlength : length (map K.encode (map fst (M.elements r))) <= supp m).
    { unfold supp. apply NoDup_incl_length.
      - apply encoded_keys_nodup. now apply M.elements_nodup.
      - intros p Hin. apply in_map_iff in Hin. destruct Hin as [k [Hcode Hkey]].
        subst p. apply Hsupport. now apply elements_code. }
    now rewrite !length_map in Hlength.
  Qed.

  (** The bit length of a consistent stored label is bounded by its raw support. *)
  Lemma elements_support_bits : forall A (r : M.t A) m k a, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    In (k, a) (M.elements r) -> K.bits k <= b m.
  Proof.
    intros A r m k a Hwf Hsupport Hin. unfold K.bits. apply support_bits, Hsupport.
    apply elements_code; [exact Hwf|]. apply in_map_iff. exists (k, a). now split.
  Qed.

  (** Consistent label weight is bounded by raw support size and key bits. *)
  Lemma weight_support_bound : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    M.weight r <= supp m * (b m + 1).
  Proof.
    intros A r m Hwf Hsupport.
    pose proof (elements_support_length A r m Hwf Hsupport) as Hlength.
    assert (Hweight : M.weight r <= length (M.elements r) * (b m + 1)).
    { unfold M.weight. apply sum_members_bound. intros [k a] Hin. cbn [fst].
      pose proof (elements_support_bits A r m k a Hwf Hsupport Hin) as Hbits.
      unfold K.bits in Hbits. lia. }
    eapply Nat.le_trans; [exact Hweight|]. now apply Nat.mul_le_mono_r.
  Qed.

  (** Enumerating consistent labels fits the same raw support and key-bit budget. *)
  Lemma T_elements_support : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    (M.T_elements r <= M.c_map * N.of_nat (supp m * (b m + 1) + 1))%N.
  Proof.
    intros A r m Hwf Hsupport.
    eapply N.le_trans; [now apply M.T_elements_le|].
    apply N.mul_le_mono_l, time_of_nat_le.
    pose proof (weight_support_bound A r m Hwf Hsupport) as Hweight. lia.
  Qed.

  (** Projecting enumerated keys adds only a linear pass to label enumeration. *)
  Lemma T_element_keys_le : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    (M.T_elements r + ListDef.T_map (@fst K.t A) (fun p => Datatypes.T_fst p)
      (M.elements r) + 1 <=
      (M.c_map + 4) * N.of_nat ((supp m + 1) * (b m + 1)))%N.
  Proof.
    intros A r m Hwf Hsupport.
    pose proof (elements_support_length A r m Hwf Hsupport) as Hlength.
    pose proof (T_elements_support A r m Hwf Hsupport) as Helements.
    pose proof (@ListDef.T_map_le (K.t * A) K.t (@fst K.t A)
      (fun p => Datatypes.T_fst p) 1%N (M.elements r)
      (fun p => Datatypes.T_fst_le p)) as Hmap.
    set (work := N.of_nat ((supp m + 1) * (b m + 1))).
    assert (HlengthN : (N.of_nat (length (M.elements r)) + 1 <= work)%N).
    { replace (N.of_nat (length (M.elements r)) + 1)%N with
        (N.of_nat (length (M.elements r) + 1)) by (rewrite Nat2N.inj_add; reflexivity).
      unfold work. apply time_of_nat_le. nia. }
    assert (HdataN : (N.of_nat (supp m * (b m + 1) + 1) <= work)%N).
    { unfold work. apply time_of_nat_le. nia. }
    assert (Helements_work : (M.T_elements r <= M.c_map * work)%N).
    { eapply N.le_trans; [exact Helements|]. now apply N.mul_le_mono_l. }
    match goal with
    | |- N.le ?clock _ => change (clock <= (M.c_map + 4) * work)%N
    end.
    rewrite N.mul_add_distr_r.
    clear Hlength Helements HdataN. clearbody work. lia.
  Qed.

  (** Each enumerated matrix row is consistent and lies inside the matrix support. *)
  Lemma elements_row_support : forall m k row, dbm_wf m ->
    In (k, row) (M.elements m) -> M.wf row /\
      (forall p, In p (M.codes row) -> In p (support m)).
  Proof.
    intros m k row [Houter Hrows] Hin.
    pose proof (proj1 (M.elements_spec (M.t Z) m k row Houter) Hin) as Hget.
    rewrite M.get_find in Hget. split.
    - exact (Hrows (K.encode k) row Hget).
    - intros p Hp. apply support_spec. right. apply in_flat_map. exists row. split.
      + exact (row_in_rows m (K.encode k) row Hget).
      + exact Hp.
  Qed.

  (** Flattening lists of uniformly bounded length multiplies the two list counts. *)
  Lemma flat_map_length_bound : forall A B (f : A -> list B) xs n,
    (forall x, In x xs -> length (f x) <= n) ->
    length (flat_map f xs) <= length xs * n.
  Proof.
    intros A B f xs. induction xs as [|x xs IH]; intros n Hbound.
    - cbn. lia.
    - cbn [flat_map length]. rewrite length_app.
      assert (Hhead : length (f x) <= n) by (apply Hbound; now left).
      assert (Htail : length (flat_map f xs) <= length xs * n).
      { apply IH. intros y Hy. apply Hbound. now right. }
      lia.
  Qed.

  (** The raw pivot-label list precedes duplicate removal in the executable collector. *)
  Definition pivot_inputs (m : dbm) : list K.t :=
    map fst (M.elements m) ++
      flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m).

  (** The pivot input list has at most one outer and one inner label per supported pair. *)
  Lemma pivot_inputs_length : forall m, dbm_wf m ->
    length (pivot_inputs m) + 1 <= (supp m + 1)^2.
  Proof.
    intros m Hwf.
    assert (Houter : length (M.elements m) <= supp m).
    { apply elements_support_length; [exact (proj1 Hwf)|].
      intros p Hp. apply support_spec. now left. }
    assert (Hinner : length (flat_map (fun kv => map fst (M.elements (snd kv)))
      (M.elements m)) <= length (M.elements m) * supp m).
    { apply flat_map_length_bound. intros [k row] Hin. cbn [snd]. rewrite length_map.
      destruct (elements_row_support m k row Hwf Hin) as [Hrow Hsupport].
      now apply elements_support_length. }
    unfold pivot_inputs. rewrite length_app, length_map. cbn [Nat.pow]. nia.
  Qed.

  (** Every pivot-input label has the key-bit bound of the original matrix. *)
  Lemma pivot_inputs_bits : forall m k, dbm_wf m ->
    In k (pivot_inputs m) -> K.bits k <= b m.
  Proof.
    intros m k Hwf Hin. unfold pivot_inputs in Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - apply in_map_iff in Hin. destruct Hin as [[q row] [Heq Hin]]. cbn in Heq. subst q.
      apply (elements_support_bits (M.t Z) m m k row (proj1 Hwf)); [|exact Hin].
      intros p Hp. apply support_spec. now left.
    - apply in_flat_map in Hin. destruct Hin as [[q row] [Hrow Hin]]. cbn [snd] in Hin.
      apply in_map_iff in Hin. destruct Hin as [[p z] [Heq Hin]]. cbn in Heq. subst p.
      destruct (elements_row_support m q row Hwf Hrow) as [Hrow_wf Hsupport].
      exact (elements_support_bits Z row m k z Hrow_wf Hsupport Hin).
  Qed.

  (** Mapping needs a callback bound only at members of its actual input. *)
  Lemma map_clock_members : forall A B (f : A -> B) tf c xs,
    Forall (fun x => (tf x <= c)%N) xs ->
    (ListDef.T_map f tf xs <= (c + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; time_step.
  Qed.

  (** An accumulator fold needs a uniform bound only for the input values it visits. *)
  Lemma fold_left_clock_members : forall A B (f : A -> B -> A) tf c xs,
    Forall (fun x => forall acc, (tf acc x <= c)%N) xs -> forall acc,
    (List.T_fold_left f tf xs acc <= (c + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; intro acc; time_step.
  Qed.

  (** A Boolean scan needs callback bounds only at members of its input list. *)
  Lemma forallb_clock_members : forall A (f : A -> bool) tf c xs,
    Forall (fun x => (tf x <= c)%N) xs ->
    (List.T_forallb f tf xs <= (c + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; time_step.
  Qed.

  (** Flattening pays a callback and one concatenation per outer input value. *)
  Lemma flat_map_clock_members : forall A B (f : A -> list B) tf c n xs,
    Forall (fun x => (tf x <= c)%N /\ length (f x) <= n) xs ->
    (List.T_flat_map f tf xs <=
      (c + N.of_nat n + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f tf c n xs Hbounds.
    induction Hbounds as [|x xs [Hhead Hlength] Htail IH].
    - time_step.
    - pose proof (time_of_nat_le _ _ Hlength) as HlengthN. time_step.
  Qed.

  (** Remembering a key charges its encoded key length independently of accumulated keys. *)
  Lemma T_remember_key_le : forall acc k,
    (T_remember_key acc k <= 8 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros [seen ks] k. time_step.
  Qed.

  (** The map-backed deduplication fold pays each input's key bits once. *)
  Lemma T_remember_fold_le : forall ks acc bb,
    (forall k, In k ks -> K.bits k <= bb) ->
    (List.T_fold_left remember_key (fun a k => T_remember_key a k) ks acc <=
      16 * (M.c_map + 1) * N.of_nat ((length ks + 1) * (bb + 1)))%N.
  Proof.
    intros ks acc bb Hbits.
    assert (Hcallback : Forall (fun k => forall a,
      (T_remember_key a k <= 8 * (M.c_map + 1) * N.of_nat (bb + 1))%N) ks).
    { apply Forall_forall. intros k Hin a.
      eapply N.le_trans; [apply T_remember_key_le|].
      apply N.mul_le_mono_l, time_of_nat_le. pose proof (Hbits k Hin). lia. }
    pose proof (fold_left_clock_members (M.t unit * list K.t) K.t remember_key
      (fun a k => T_remember_key a k) (8 * (M.c_map + 1) * N.of_nat (bb + 1))%N
      ks Hcallback acc) as Hfold.
    clear Hbits Hcallback.
    rewrite (Nat2N.inj_mul (length ks + 1) (bb + 1)), Nat2N.inj_add.
    set (count := N.of_nat (length ks)) in *.
    set (bits := N.of_nat (bb + 1)) in *.
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    clearbody count bits.
    set (work := ((count + 1) * bits)%N).
    assert (Hunit : (1 <= work)%N) by (unfold work; nia).
    assert (Hper : (8 * (M.c_map + 1) * bits + 1 <=
      9 * (M.c_map + 1) * bits)%N) by nia.
    assert (Hfold_work : (List.T_fold_left remember_key
      (fun a k => T_remember_key a k) ks acc <= 9 * (M.c_map + 1) * work + 1)%N).
    { eapply N.le_trans; [exact Hfold|]. apply N.add_le_mono_r.
      eapply N.le_trans; [apply N.mul_le_mono_r; exact Hper|].
      replace (9 * (M.c_map + 1) * work)%N with
        (9 * (M.c_map + 1) * bits * (count + 1))%N by (unfold work; ring).
      apply N.mul_le_mono_l. lia. }
    match goal with
    | |- N.le ?clock _ => change (clock <= 16 * (M.c_map + 1) * work)%N
    end.
    assert (Hbudget : ((9 * (M.c_map + 1) + 1) * work <=
      16 * (M.c_map + 1) * work)%N).
    { apply N.mul_le_mono_r. lia. }
    rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
    clear Hfold Hper Hbits. clearbody work. lia.
  Qed.

  (** The trace stops at the same negative diagonal as the executable pivot loop. *)
  Lemma fw_trace_nonnegative : forall k ks m,
    fw_trace (k :: ks) m = (k, m) ::
      if nonnegative k (fw_round k m) then fw_trace ks (fw_round k m) else nil.
  Proof.
    intros k ks m. cbn [fw_trace]. unfold nonnegative.
    destruct (entry (fw_round k m) k k) as [z|]; [|reflexivity].
    destruct (z <? 0)%Z eqn:Hneg; destruct (0 <=? z)%Z eqn:Hnonneg;
      try reflexivity.
    - apply Z.ltb_lt in Hneg. apply Z.leb_le in Hnonneg. lia.
    - apply Z.ltb_ge in Hneg. apply Z.leb_gt in Hnonneg. lia.
  Qed.

  (** The trace cost records precisely the rounds performed by the executable loop. *)
  Definition trace_cost (ks : list K.t) (m : dbm) : N :=
    fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km)) (fw_trace ks m)).

  (** One trace entry pays its round and continues exactly when the diagonal is nonnegative. *)
  Lemma trace_cost_cons : forall k ks m,
    trace_cost (k :: ks) m = (T_fw_round k m +
      if nonnegative k (fw_round k m) then trace_cost ks (fw_round k m) else 0)%N.
  Proof.
    intros k ks m. unfold trace_cost at 1. rewrite fw_trace_nonnegative.
    cbn [map fold_right fst snd]. destruct (nonnegative k (fw_round k m)); reflexivity.
  Qed.

  (** Each key has a diagonal-check budget independent of the current matrix entries. *)
  Definition diagonal_budget (k : K.t) : N :=
    (16 * (M.c_map + 1) * N.of_nat (K.bits k + 1) + 4)%N.

  Definition scan_budget (ks : list K.t) : N := fold_right N.add 0%N (map diagonal_budget ks).

  (** The pivot loop pays its traced rounds, one diagonal check per key, and loop overhead. *)
  Lemma T_close_pivots_trace : forall ks m,
    (T_close_pivots ks m <= trace_cost ks m + scan_budget ks + 1)%N.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m.
    - unfold trace_cost, scan_budget. cbn [fw_trace map fold_right]. time_step.
    - rewrite trace_cost_cons.
      change (T_close_pivots (k :: ks) m <=
        T_fw_round k m +
          (if nonnegative k (fw_round k m) then trace_cost ks (fw_round k m) else 0) +
        (diagonal_budget k + scan_budget ks) + 1)%N.
      pose proof (T_nonnegative_small k (fw_round k m)) as Hdiag.
      specialize (IH (fw_round k m)).
      time_unfold (@T_close_pivots). cbn beta iota zeta.
      destruct (nonnegative k (fw_round k m)); cbn beta iota zeta;
        unfold diagonal_budget; lia.
  Qed.

  (** The final diagonal scan fits the same per-key budget as the pivot loop. *)
  Lemma T_diagonal_scan_le : forall ks m,
    (List.T_forallb (fun k => nonnegative k m) (fun k => (1 + T_nonnegative k m)%N) ks <=
      scan_budget ks + 1)%N.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m.
    - unfold scan_budget. cbn [map fold_right]. time_step.
    - change (List.T_forallb (fun k => nonnegative k m) (fun k => (1 + T_nonnegative k m)%N)
        (k :: ks) <= diagonal_budget k + scan_budget ks + 1)%N.
      pose proof (T_nonnegative_small k m) as Hdiag. specialize (IH m).
      unfold diagonal_budget. time_step.
  Qed.

  (** Uniform key bits bound the sum of diagonal budgets. *)
  Lemma scan_budget_bound : forall ks bb,
    (forall k, In k ks -> K.bits k <= bb) ->
    (scan_budget ks <= 20 * (M.c_map + 1) * N.of_nat (length ks * (bb + 1)))%N.
  Proof.
    intros ks bb Hbits.
    assert (Hpoint : forall k, In k ks ->
      (diagonal_budget k <= 20 * (M.c_map + 1) * N.of_nat (bb + 1))%N).
    { intros k Hin. pose proof (Hbits k Hin) as Hkey.
      assert (HkeyN : (N.of_nat (K.bits k + 1) <= N.of_nat (bb + 1))%N)
        by (apply time_of_nat_le; lia).
      assert (Hunit : (1 <= N.of_nat (bb + 1))%N) by lia.
      pose proof (N.mul_le_mono_l _ _ (16 * (M.c_map + 1))%N HkeyN) as Hscaled.
      unfold diagonal_budget. nia. }
    pose proof (time_sum_bound K.t ks diagonal_budget (fun _ => bb + 1)
      (20 * (M.c_map + 1))%N Hpoint) as Hsum.
    now rewrite sum_weight_const in Hsum.
  Qed.

  (** The deduplicated pivot scan fits the matrix's initial quadratic work. *)
  Lemma scan_budget_keys : forall m, dbm_wf m ->
    (scan_budget (keys m) <= 20 * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m Hwf. eapply N.le_trans; [apply (scan_budget_bound (keys m) (b m))|].
    - intros k Hin. unfold K.bits. apply support_bits. now apply keys_support.
    - apply N.mul_le_mono_l, time_of_nat_le.
      pose proof (keys_le m Hwf) as Hlength. cbn [Nat.pow]. nia.
  Qed.

  (** Collecting and deduplicating pivot labels fits the initial quadratic key budget. *)
  Lemma T_pivot_keys_le : forall m, dbm_wf m ->
    (T_pivot_keys m <= 64 * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 * (b m + 1)))%N.
  Proof.
    intros m Hwf.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (elements_support_length (M.t Z) m m (proj1 Hwf) Hsupport) as Hlength.
    pose proof (pivot_inputs_length m Hwf) as Hinputs.
    set (rowwork := N.of_nat ((supp m + 1) * (b m + 1))).
    set (work := N.of_nat ((supp m + 1)^2 * (b m + 1))).
    assert (Hpositive : 1 <= (supp m + 1)^2 * (b m + 1))
      by (cbn [Nat.pow]; nia).
    pose proof (time_of_nat_le _ _ Hpositive) as Hunit.
    change (1 <= work)%N in Hunit.
    assert (Hrowunit : (N.of_nat (supp m) + 1 <= rowwork)%N).
    { replace (N.of_nat (supp m) + 1)%N with (N.of_nat (supp m + 1))
        by (rewrite Nat2N.inj_add; reflexivity).
      unfold rowwork. apply time_of_nat_le. nia. }
    assert (Hrowwork : (rowwork <= work)%N).
    { unfold rowwork, work. apply time_of_nat_le. cbn [Nat.pow]. nia. }
    assert (Hrowprod : (rowwork * N.of_nat (length (M.elements m)) <= work)%N).
    { unfold rowwork, work. rewrite <- Nat2N.inj_mul.
      apply time_of_nat_le. cbn [Nat.pow]. nia. }
    pose proof (T_element_keys_le (M.t Z) m m (proj1 Hwf) Hsupport) as Houter.
    assert (Houter_work : (M.T_elements m + ListDef.T_map (@fst K.t (M.t Z))
      (fun p => Datatypes.T_fst p) (M.elements m) + 1 <= (M.c_map + 4) * work)%N).
    { eapply N.le_trans; [exact Houter|]. now apply N.mul_le_mono_l. }
    pose proof (T_remember_fold_le (pivot_inputs m) (M.empty, nil) (b m)
      (fun k Hin => pivot_inputs_bits m k Hwf Hin)) as Hremember.
    assert (Hremember_work : (List.T_fold_left remember_key
      (fun a k => T_remember_key a k) (pivot_inputs m) (M.empty, nil) <=
      16 * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [exact Hremember|]. apply N.mul_le_mono_l.
      unfold work. apply time_of_nat_le. now apply Nat.mul_le_mono_r. }
    assert (Happ_work : (Datatypes.T_app (map fst (M.elements m))
      (flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m)) <= work)%N).
    { eapply N.le_trans; [apply Datatypes.T_app_le|]. rewrite length_map.
      replace (N.of_nat (length (M.elements m)) + 1)%N with
        (N.of_nat (length (M.elements m) + 1)) by (rewrite Nat2N.inj_add; reflexivity).
      unfold work. apply time_of_nat_le. cbn [Nat.pow]. nia. }
    unfold T_pivot_keys. cbn beta iota zeta.
    match goal with
    | |- context [List.T_flat_map ?f ?tf (M.elements m)] =>
      assert (Hrows : Forall (fun kv =>
        (tf kv <= (M.c_map + 5) * rowwork)%N /\ length (f kv) <= supp m)
        (M.elements m));
      [ apply Forall_forall; intros [k row] Hin;
        destruct (elements_row_support m k row Hwf Hin) as [Hrow Hrow_support]; split;
        [ pose proof (T_element_keys_le Z row m Hrow Hrow_support) as Hrow_clock;
          fold rowwork in Hrow_clock;
          cbv beta delta [Datatypes.T_fst] in Hrow_clock;
          cbn beta iota zeta; time_simpl; cbn [fst snd];
          replace ((M.c_map + 5) * rowwork)%N with
            ((M.c_map + 4) * rowwork + rowwork)%N by ring; lia
        | cbn [snd]; rewrite length_map; now apply elements_support_length ]
      | pose proof (flat_map_clock_members (K.t * M.t Z) K.t f tf
          ((M.c_map + 5) * rowwork)%N (supp m) (M.elements m) Hrows) as Hflat;
        assert (Hper : ((M.c_map + 5) * rowwork + N.of_nat (supp m) + 2 <=
          (M.c_map + 7) * rowwork)%N);
        [ replace ((M.c_map + 7) * rowwork)%N with
            ((M.c_map + 5) * rowwork + 2 * rowwork)%N by ring; lia
        | assert (Hflat_work : (List.T_flat_map f tf (M.elements m) <=
            (M.c_map + 8) * work)%N);
          [ eapply N.le_trans; [exact Hflat|];
            eapply N.le_trans with
              ((M.c_map + 7) * rowwork * N.of_nat (length (M.elements m)) + 1)%N;
            [ apply N.add_le_mono_r, N.mul_le_mono_r; exact Hper
            | replace ((M.c_map + 7) * rowwork * N.of_nat (length (M.elements m)) + 1)%N
                with ((M.c_map + 7) * (rowwork * N.of_nat (length (M.elements m))) + 1)%N
                by ring;
              eapply N.le_trans with ((M.c_map + 7) * work + 1)%N;
              [ apply N.add_le_mono_r, N.mul_le_mono_l; exact Hrowprod
              | replace ((M.c_map + 8) * work)%N with
                  ((M.c_map + 7) * work + work)%N by ring; lia ] ]
          | clear Hrows Hflat Hper ] ] ]
    end.
    assert (Hbudget : ((M.c_map + 4 + (M.c_map + 8) + 1 +
      16 * (M.c_map + 1) + 4) * work <= 64 * (M.c_map + 1) * work)%N).
    { apply N.mul_le_mono_r. lia. }
    repeat rewrite N.mul_add_distr_r in Hbudget.
    rewrite N.mul_add_distr_r in Houter_work, Hflat_work.
    cbv beta delta [Datatypes.T_fst Datatypes.T_snd] in Houter_work, Hflat_work.
    time_simpl. fold (pivot_inputs m).
    match goal with
    | |- N.le ?clock _ => change (clock <= 64 * (M.c_map + 1) * work)%N
    end.
    clear Houter Hremember Hlength Hinputs Hpositive Hrowunit Hrowwork Hrowprod.
    clearbody rowwork work. lia.
  Qed.

  (** Closure adds collection and scan work to the exact cost of its performed rounds. *)
  Lemma T_close_additive : forall m, dbm_wf m ->
    (T_close m <= trace_cost (keys m) m + 128 * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m Hwf.
    set (work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))).
    replace (128 * (M.c_map + 1) * work)%N with
      (128 * ((M.c_map + 1) * work))%N by ring.
    assert (Hpositive : 1 <= (supp m + 1)^2 * (b m + ell m + 1))
      by (cbn [Nat.pow]; nia).
    pose proof (time_of_nat_le _ _ Hpositive) as Hunit.
    change (1 <= work)%N in Hunit.
    assert (Hcollect : (T_pivot_keys m <= 64 * ((M.c_map + 1) * work))%N).
    { eapply N.le_trans; [now apply T_pivot_keys_le|].
      replace (64 * ((M.c_map + 1) * work))%N with
        (64 * (M.c_map + 1) * work)%N by ring.
      apply N.mul_le_mono_l. unfold work. apply time_of_nat_le, Nat.mul_le_mono_l. lia. }
    pose proof (scan_budget_keys m Hwf) as Hscan.
    change (scan_budget (keys m) <= 20 * (M.c_map + 1) * work)%N in Hscan.
    replace (20 * (M.c_map + 1) * work)%N with (20 * ((M.c_map + 1) * work))%N
      in Hscan by ring.
    pose proof (T_close_pivots_trace (keys m) m) as Hloop.
    assert (Hdiagonal : forall next,
      (List.T_forallb (fun k => nonnegative k next) (fun k => (1 + T_nonnegative k next)%N)
        (keys m) <= 20 * ((M.c_map + 1) * work) + 1)%N).
    { intro next. pose proof (T_diagonal_scan_le (keys m) next). lia. }
    assert (Hkeyunit : (1 <= (M.c_map + 1) * work)%N).
    { change (1 * 1 <= (M.c_map + 1) * work)%N. apply N.mul_le_mono; lia. }
    set (rounds := trace_cost (keys m) m) in *.
    set (keywork := ((M.c_map + 1) * work)%N) in *.
    clear Hpositive Hunit. clearbody work keywork rounds.
    unfold T_close. cbn beta iota zeta. rewrite pivot_keys_eq_keys.
    destruct (close_pivots (keys m) m) as [|next]; cbn beta iota zeta; time_simpl.
    - lia.
    - pose proof (Hdiagonal next). lia.
  Qed.

  (** The plan coefficient covers the additive collection and scan coefficient. *)
  Lemma k_zone_frame_le : (128 * (M.c_map + 1) <= k_zone)%N.
  Proof.
    unfold k_zone. nia.
  Qed.

  (** Closure pays for collecting pivots, its exact round trace, and diagonal scans. *)
  Lemma T2_close : forall m, dbm_wf m ->
    (T_close m <= k_zone * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
  Proof.
    intros m Hwf. pose proof (T_close_additive m Hwf) as Htime.
    set (work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))) in *.
    change (T_close m <= k_zone * (work + trace_cost (keys m) m))%N.
    set (rounds := trace_cost (keys m) m) in *.
    pose proof k_zone_frame_le as Hcoefficient.
    assert (Hconstant : (1 <= k_zone)%N) by lia.
    assert (Hframe : (128 * (M.c_map + 1) * work <= k_zone * work)%N)
      by (now apply N.mul_le_mono_r).
    assert (Hrounds : (rounds <= k_zone * rounds)%N).
    { replace rounds with (1 * rounds)%N at 1 by ring. now apply N.mul_le_mono_r. }
    rewrite N.mul_add_distr_l. lia.
  Qed.
  (** Early exit records no more rounds than the supplied pivot list. *)
  Lemma fw_trace_length : forall ks m, length (fw_trace ks m) <= length ks.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m.
    - cbn [fw_trace length]. lia.
    - rewrite fw_trace_nonnegative. cbn [length].
      destruct (nonnegative k (fw_round k m)); cbn [length].
      + pose proof (IH (fw_round k m)). lia.
      + lia.
  Qed.

  (** Traced keys come from the pivot list and every traced matrix retains raw support sizes. *)
  Lemma fw_trace_resources : forall ks m k a, In (k, a) (fw_trace ks m) ->
    In k ks /\ supp a = supp m /\ b a = b m.
  Proof.
    intro ks. induction ks as [|p ks IH]; intros m k a Hin.
    - contradiction.
    - rewrite fw_trace_nonnegative in Hin. cbn [In] in Hin.
      destruct Hin as [Heq|Hin].
      + injection Heq as Hkey Hstate. subst k a. split; [now left|]. now split.
      + destruct (nonnegative p (fw_round p m)); [|contradiction].
        destruct (IH (fw_round p m) k a Hin) as [Hkey [Hsupport Hbits]].
        destruct (supp_fw_round p m) as [Hround_support Hround_bits].
        split; [now right|]. split; congruence.
  Qed.

  (** At most one support-sized family of quadratic allowances fits a cubic allowance. *)
  Lemma quadratic_cubic_budget : forall n count payload, count <= n + 1 ->
    ((n + 1)^2 * payload) * count <= (n + 1)^3 * payload.
  Proof.
    intros n count payload Hcount.
    replace (((n + 1)^2 * payload) * count) with
      ((count * (n + 1)^2) * payload) by ring.
    apply Nat.mul_le_mono_r.
    change (count * (n + 1)^2 <= (n + 1) * (n + 1)^2).
    now apply Nat.mul_le_mono_r.
  Qed.

  (** Preserved support and logarithmic entry growth bound every performed round uniformly. *)
  Lemma traced_round_time_le : forall m k a, dbm_wf m ->
    In (k, a) (fw_trace (keys m) m) ->
    (T_fw_round k a <= 2 * k_zone * N.of_nat
      ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof.
    intros m k a Hwf Hin.
    destruct (fw_trace_resources (keys m) m k a Hin) as [Hkey [Hsupport Hbits]].
    assert (Hkey_bits : K.bits k <= b m).
    { unfold K.bits. apply support_bits. now apply keys_support. }
    pose proof (bits_fw_trace_le (keys m) m k a Hwf Hin) as Hell.
    eapply N.le_trans; [apply T_fw_round_raw|].
    replace (2 * k_zone * N.of_nat
      ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)))%N with
      (k_zone * (2 * N.of_nat
        ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1))))%N by ring.
    apply N.mul_le_mono_l.
    replace (2 * N.of_nat
      ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)))%N with
      (N.of_nat (2 * ((supp m + 1)^2 *
        (b m + ell m + Nat.log2 (supp m) + 1))))
      by (rewrite Nat2N.inj_mul; reflexivity).
    apply time_of_nat_le. rewrite Hsupport, Hbits.
    replace (2 * ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1))) with
      ((supp m + 1)^2 * (2 * (b m + ell m + Nat.log2 (supp m) + 1))) by ring.
    apply Nat.mul_le_mono_l. lia.
  Qed.

  (** Summing the performed rounds needs only one additional factor of support size. *)
  Lemma trace_cost_cubic : forall m, dbm_wf m ->
    (trace_cost (keys m) m <= 2 * k_zone * N.of_nat
      ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof.
    intros m Hwf.
    set (xs := fw_trace (keys m) m).
    set (units := (supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)).
    assert (Hpoint : forall km, In km xs ->
      (T_fw_round (fst km) (snd km) <= 2 * k_zone * N.of_nat units)%N).
    { intros [k a] Hin. cbn [fst snd]. unfold units.
      unfold xs in Hin. now apply traced_round_time_le. }
    assert (Hsum : (fold_right N.add 0%N
      (map (fun km => T_fw_round (fst km) (snd km)) xs) <=
      (2 * k_zone * N.of_nat units) * N.of_nat (length xs))%N).
    { pose proof (time_sum_bound (K.t * dbm) xs
        (fun km => T_fw_round (fst km) (snd km)) (fun _ => 1%nat)
        (2 * k_zone * N.of_nat units)%N) as Hbound.
      assert (Hcallback : forall km, In km xs ->
        (T_fw_round (fst km) (snd km) <=
          (2 * k_zone * N.of_nat units) * N.of_nat 1)%N).
      { intros km Hin. change (T_fw_round (fst km) (snd km) <=
          (2 * k_zone * N.of_nat units) * 1)%N.
        rewrite N.mul_1_r. now apply Hpoint. }
      specialize (Hbound Hcallback). now rewrite sum_weight_one in Hbound. }
    assert (Hlength : length xs <= supp m).
    { unfold xs. eapply Nat.le_trans; [apply fw_trace_length|]. now apply keys_le. }
    assert (Hunits : units * length xs <=
      (supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)).
    { unfold units. apply quadratic_cubic_budget. lia. }
    pose proof (time_of_nat_le _ _ Hunits) as Hcast.
    rewrite (Nat2N.inj_mul units (length xs)) in Hcast.
    unfold trace_cost. fold xs.
    eapply N.le_trans; [exact Hsum|].
    replace ((2 * k_zone * N.of_nat units) * N.of_nat (length xs))%N with
      (2 * k_zone * (N.of_nat units * N.of_nat (length xs)))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** The public closure coefficient covers round updates and additive traversal overhead. *)
  Lemma c_zone_closure_coefficient :
    (2 * k_zone + 128 * (M.c_map + 1) <= c_zone)%N.
  Proof.
    unfold k_zone, c_zone. nia.
  Qed.

  (** Full closure has cubic support work and the promised logarithmic entry-bit allowance. *)
  Lemma T_close_le : forall m, dbm_wf m ->
    (T_close m <= c_zone * N.of_nat (((supp m + 1)^3)%nat) *
      N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  Proof.
    intros m Hwf.
    replace (c_zone * N.of_nat ((supp m + 1)^3) *
      N.of_nat (b m + ell m + Nat.log2 (supp m) + 1))%N with
      (c_zone * N.of_nat ((supp m + 1)^3 *
        (b m + ell m + Nat.log2 (supp m) + 1)))%N
      by (rewrite (Nat2N.inj_mul ((supp m + 1)^3)
        (b m + ell m + Nat.log2 (supp m) + 1)); ring).
    pose proof (T_close_additive m Hwf) as Htime.
    pose proof (trace_cost_cubic m Hwf) as Htrace.
    set (work := N.of_nat ((supp m + 1)^3 *
      (b m + ell m + Nat.log2 (supp m) + 1))) in *.
    assert (Hinitial_nat : (supp m + 1)^2 * (b m + ell m + 1) <=
      (supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)).
    { eapply Nat.le_trans with
        ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)).
      - apply Nat.mul_le_mono_l. lia.
      - pose proof (quadratic_cubic_budget (supp m) 1
          (b m + ell m + Nat.log2 (supp m) + 1) ltac:(lia)) as Hdegree.
        now rewrite Nat.mul_1_r in Hdegree. }
    pose proof (time_of_nat_le _ _ Hinitial_nat) as Hinitial.
    change (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) <= work)%N in Hinitial.
    pose proof (N.mul_le_mono_l _ _ (128 * (M.c_map + 1))%N Hinitial) as Hframe.
    pose proof (N.mul_le_mono_r _ _ work c_zone_closure_coefficient) as Hbudget.
    rewrite N.mul_add_distr_r in Hbudget.
    set (initial_work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))) in *.
    clear Hinitial_nat Hinitial. clearbody work initial_work. lia.
  Qed.

  (** Range arithmetic combines key, entry, source-form and accumulation bits. *)
  Definition range_payload (e : term L.op X.t) (m : dbm) : nat :=
    b m + ell m + F.bits_e e + Nat.log2 (tsize e) + 1.

  (** The interval arithmetic charge is the square of its combined bit allowance. *)
  Definition range_unit (e : term L.op X.t) (m : dbm) : N :=
    N.of_nat ((range_payload e m ^ 2)%nat).

  (** Every range arithmetic allowance contains one unit for fixed work. *)
  Lemma range_payload_positive : forall e m, 1 <= range_payload e m.
  Proof.
    intros e m. unfold range_payload. lia.
  Qed.

  (** A positive squared allowance also pays for linear arithmetic. *)
  Lemma range_unit_linear : forall e m,
    (N.of_nat (range_payload e m) <= range_unit e m)%N.
  Proof.
    intros e m. unfold range_unit. apply time_of_nat_le.
    pose proof (range_payload_positive e m) as Hpositive.
    cbn [Nat.pow]. rewrite Nat.mul_1_r.
    replace (range_payload e m) with (range_payload e m * 1) at 1 by lia.
    apply Nat.mul_le_mono; [apply Nat.le_refl|exact Hpositive].
  Qed.

  (** The arithmetic charge is nonzero on every source term and state. *)
  Lemma range_unit_positive : forall e m, (1 <= range_unit e m)%N.
  Proof.
    intros e m. eapply N.le_trans; [|apply range_unit_linear].
    change (N.of_nat 1%nat <= N.of_nat (range_payload e m))%N.
    apply time_of_nat_le. apply range_payload_positive.
  Qed.

  (** Every mentioned key fits the maximum charged by its linear form. *)
  Lemma form_bits_key : forall f p,
    In p (coef f) -> X.bits (fst p) <= F.form_bits f.
  Proof.
    intros [cs c] p. unfold F.form_bits. cbn [coef cst].
    induction cs as [|q cs IH]; intros Hin; [contradiction|].
    cbn in Hin |- *. destruct Hin as [Heq|Hin].
    - subst q. pose proof (Nat.le_max_l
        (X.bits (fst p) + Z.size_nat (snd p))
        (fold_right Nat.max (Z.size_nat c)
          (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) cs))). lia.
    - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
  Qed.

  (** A source form's suffix accumulators retain the same logarithmic bit allowance. *)
  Lemma form_fragment_abs : forall e m f r cs,
    F.lin_of e = Some (f, r) -> incl cs (coef f) -> length cs <= tsize e ->
    rel_bounds_abs (2 ^ range_bits e (Reached m))
      (rel_form_bounds (variable_bounds m) (Lin X.t cs (cst f))).
  Proof.
    intros e m f r cs Hlin Hincl Hcount.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply rel_bounds_abs_mono with
      (lower := (length cs + 1) * 2 ^ F.bits_e e * 2 ^ ell m).
    - unfold range_bits, ells. apply affine_magnitude_allowance; [exact Hcount|].
      destruct e; cbn [tsize]; lia.
    - apply rel_form_bounds_abs.
      + cbn [cst]. apply zbits_abs_bound.
        eapply Nat.le_trans; [exact (form_bits_constant f)|]. lia.
      + cbn [coef]. apply Forall_forall. intros p Hin. apply zbits_abs_bound.
        eapply Nat.le_trans; [exact (form_bits_coefficient f p (Hincl p Hin))|]. lia.
      + apply variable_bounds_abs.
      + pose proof (Nat.pow_nonzero 2 (F.bits_e e) ltac:(lia)). lia.
      + pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia.
  Qed.

  (** Two sparse lookups and a sign change charge the queried key length. *)
  Lemma T_variable_bounds_small : forall m x,
    (T_variable_bounds m x <=
      64 * (M.c_map + 1) * N.of_nat ((X.bits x + 1)%nat))%N.
  Proof.
    intros m x.
    pose proof (T_entry_small m (Some x) None) as Hlower.
    pose proof (T_entry_small m None (Some x)) as Hupper.
    rewrite some_key_bits in Hlower, Hupper.
    change (K.bits None) with 1%nat in Hlower, Hupper.
    set (key_bits := X.bits x) in *. clearbody key_bits.
    time_unfold (@T_variable_bounds). time_simpl. time_cbn.
    time_cases; time_simpl; time_cbn;
      try match goal with |- context [Z.T_opp ?z] => pose proof (Z.T_opp_le z) end;
      rewrite ?Nat2N.inj_add in *; nia.
  Qed.
  (** A smaller linear allowance fits the shared squared range charge. *)
  Lemma range_linear_charge : forall e m bits,
    bits <= range_payload e m -> (N.of_nat bits <= range_unit e m)%N.
  Proof.
    intros e m bits Hbits. eapply N.le_trans; [|apply range_unit_linear].
    now apply time_of_nat_le.
  Qed.

  (** Squaring a smaller bit allowance preserves the range budget. *)
  Lemma range_square_charge : forall e m bits,
    bits <= range_payload e m -> (N.of_nat (bits ^ 2) <= range_unit e m)%N.
  Proof.
    intros e m bits Hbits. unfold range_unit. apply time_of_nat_le.
    cbn [Nat.pow]. rewrite !Nat.mul_1_r. now apply Nat.mul_le_mono.
  Qed.

  (** A coefficient key lookup fits one range arithmetic charge. *)
  Lemma T_variable_bounds_range : forall e m x,
    X.bits x <= F.bits_e e ->
    (T_variable_bounds m x <= 64 * (M.c_map + 1) * range_unit e m)%N.
  Proof.
    intros e m x Hbits. eapply N.le_trans; [apply T_variable_bounds_small|].
    apply N.mul_le_mono_l. apply range_linear_charge. unfold range_payload. lia.
  Qed.

  (** Coefficient multiplication uses the source and matrix endpoint bit allowances. *)
  Lemma T_scale_bounds_range : forall e m c x,
    Z.size_nat c <= F.bits_e e ->
    (T_rel_scale_bounds c (variable_bounds m x) <= 32 * range_unit e m)%N.
  Proof.
    intros e m c x Hbits.
    eapply N.le_trans.
    - apply rel_scale_bounds_time with (bits_c := F.bits_e e) (bits_x := ell m).
      + exact Hbits.
      + apply variable_bounds_abs.
    - apply N.mul_le_mono_l. apply range_square_charge. unfold range_payload. lia.
  Qed.

  (** Adding a product to a source suffix costs a linear fraction of the squared budget. *)
  Lemma T_add_bounds_range : forall e m a acc,
    rel_bounds_abs (2 ^ (F.bits_e e + ell m)) a ->
    rel_bounds_abs (2 ^ range_bits e (Reached m)) acc ->
    (T_rel_add_bounds a acc <= 48 * range_unit e m)%N.
  Proof.
    intros e m a acc Ha Hacc.
    eapply N.le_trans; [exact (rel_add_bounds_time _ _ _ _ Ha Hacc)|].
    replace (48 * range_unit e m)%N with (16 * (3 * range_unit e m))%N by ring.
    apply N.mul_le_mono_l.
    eapply N.le_trans with (N.of_nat (3 * range_payload e m)).
    - apply time_of_nat_le. unfold range_bits, ells, range_payload. lia.
    - rewrite Nat2N.inj_mul. change (3 * N.of_nat (range_payload e m) <=
        3 * range_unit e m)%N.
      apply N.mul_le_mono_l. apply range_unit_linear.
  Qed.

  (** Source wrap endpoints are already part of the charged linearization bits. *)
  Lemma T_wrap_bounds_range : forall e m f r bounds,
    F.lin_of e = Some (f, r) ->
    (T_rel_wrap_bounds r bounds <= 8 * range_unit e m)%N.
  Proof.
    intros e m f r bounds Hlin.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply N.le_trans.
    - apply rel_wrap_bounds_time with (bits := F.bits_e e).
      change (F.wrap_bits r <= F.bits_e e). lia.
    - apply N.mul_le_mono_l. apply range_linear_charge. unfold range_payload. lia.
  Qed.

  (** Each actual form-fold step has bounded queries, products and suffix addition. *)
  Lemma form_bounds_step_time : forall e m f r p after,
    F.lin_of e = Some (f, r) -> In p (coef f) -> incl after (coef f) ->
    length after <= tsize e ->
    (16 + T_variable_bounds m (fst p) +
      T_rel_scale_bounds (snd p) (variable_bounds m (fst p)) +
      T_rel_add_bounds (rel_scale_bounds (snd p) (variable_bounds m (fst p)))
        (rel_form_bounds (variable_bounds m) (Lin X.t after (cst f))) <=
      512 * (M.c_map + 1) * range_unit e m)%N.
  Proof.
    intros e m f r p after Hlin Hin Hincl Hcount.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    assert (Hkey : X.bits (fst p) <= F.bits_e e).
    { pose proof (form_bits_key f p Hin). lia. }
    assert (Hcoefficient : Z.size_nat (snd p) <= F.bits_e e).
    { pose proof (form_bits_coefficient f p Hin). lia. }
    assert (Hproduct : rel_bounds_abs (2 ^ (F.bits_e e + ell m))
      (rel_scale_bounds (snd p) (variable_bounds m (fst p)))).
    { rewrite Nat.pow_add_r. apply rel_bounds_abs_scale.
      - now apply zbits_abs_bound.
      - apply variable_bounds_abs.
      - pose proof (Nat.pow_nonzero 2 (F.bits_e e) ltac:(lia)). lia.
      - pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia. }
    pose proof (form_fragment_abs e m f r after Hlin Hincl Hcount) as Hsuffix.
    pose proof (T_variable_bounds_range e m (fst p) Hkey) as Hquery.
    pose proof (T_scale_bounds_range e m (snd p) (fst p) Hcoefficient) as Hscale.
    pose proof (T_add_bounds_range e m _ _ Hproduct Hsuffix) as Hadd.
    assert (Hcharge : (range_unit e m <= (M.c_map + 1) * range_unit e m)%N).
    { replace (range_unit e m) with (1 * range_unit e m)%N at 1 by ring.
      apply N.mul_le_mono_r. lia. }
    pose proof (N.mul_le_mono_l _ _ 32%N Hcharge) as Hscale_charge.
    pose proof (N.mul_le_mono_l _ _ 48%N Hcharge) as Hadd_charge.
    pose proof (range_unit_positive e m) as Hpositive.
    replace (64 * (M.c_map + 1) * range_unit e m)%N with
      (64 * ((M.c_map + 1) * range_unit e m))%N in Hquery by ring.
    replace (512 * (M.c_map + 1) * range_unit e m)%N with
      (512 * ((M.c_map + 1) * range_unit e m))%N by ring.
    set (charge := ((M.c_map + 1) * range_unit e m)%N) in *.
    clear Hbits Hkey Hcoefficient Hproduct Hsuffix. clearbody charge. lia.
  Qed.

  (** Summing bounded steps and the fold frame adds one source-size factor. *)
  Lemma range_fold_budget : forall fold_cost count nodes unit : N,
    (1 <= unit)%N -> (count <= nodes)%N ->
    (fold_cost <= (512 * unit + 1) * count + 1)%N ->
    (8 + fold_cost <= 1024 * unit * (nodes + 1))%N.
  Proof.
    intros fold_cost count nodes unit Hunit Hcount Hfold.
    assert (Hcount_unit : (count <= unit * count)%N).
    { replace count with (1 * count)%N at 1 by ring.
      apply N.mul_le_mono_r. exact Hunit. }
    assert (Hproduct : (unit * count <= unit * nodes)%N).
    { now apply N.mul_le_mono_l. }
    replace ((512 * unit + 1) * count + 1)%N with
      (512 * (unit * count) + count + 1)%N in Hfold by ring.
    replace (1024 * unit * (nodes + 1))%N with
      (1024 * (unit * nodes) + 1024 * unit)%N by ring.
    set (count_charge := (unit * count)%N) in *.
    set (node_charge := (unit * nodes)%N) in *.
    clearbody count_charge node_charge. lia.
  Qed.
End ZoneT.
