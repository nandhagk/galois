(** * Bounded disjunctive states

    Lists of alternatives represent a union and compact when the capacity is exceeded.
    For example, cap one joins two alternatives into one state.
    Builds on: DisjunctionSig, StateSig and the lattice interfaces. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig.
Import List.ListNotations.
Local Open Scope nat_scope.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module Nat.
  TimeFun Nat.pred.
End Nat.

(** * Value-join accounting shared by state combinations *)

Module ValueJoinBudget (L : LANG_T) (V : VALUE_DOMAIN_T L) (C : CAP).
  Definition growth : N := (2 * (V.c_val + 1))%N.
  Definition base_scale : N :=
    (growth ^ N.of_nat (C.k + 1) * (N.of_nat (V.size V.bot) + 1))%N.
  Definition coefficient : N :=
    (16 * (base_scale + N.of_nat (C.k + 1) + 1))%N.

  (** Mapping charges one cell plus the supplied clock at each alternative. *)
  Lemma map_clock {A B} (f : A -> B) (T_f : A -> N) xs :
    ListDef.T_map f T_f xs =
      (fold_right N.add 0%N (map (fun x => T_f x + 1)%N xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; time_unfold @ListDef.T_map;
      cbn [map fold_right]; rewrite ?IH; lia.
  Qed.

  (** Memberwise cost bounds add without increasing the common coefficient. *)
  Lemma sum_cost {A} (f : A -> N) (work : A -> nat) c xs :
    (forall x, In x xs -> (f x <= c * N.of_nat (work x))%N) ->
    (fold_right N.add 0%N (map f xs) <=
      c * N.of_nat (fold_right Nat.add 0%nat (map work xs)))%N.
  Proof.
    induction xs as [|x xs IH]; intro Hcost; cbn [map fold_right]; [lia |].
    specialize (IH (fun y Hy => Hcost y (or_intror Hy))).
    pose proof (Hcost x (or_introl eq_refl)); rewrite Nat2N.inj_add; nia.
  Qed.

  (** One value join pays for its clock, its result size and one traversal step. *)
  Lemma join_step a b tail :
    (V.T_join a b + 1 + N.of_nat (V.size (V.join a b)) + tail + 1 <=
      growth * (N.of_nat (V.size a) + N.of_nat (V.size b) + tail + 2))%N.
  Proof.
    pose proof (V.T_join_le a b) as Hclock; pose proof (V.join_size a b) as Hsize.
    unfold growth; repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** A fold's actual accumulator bounds the total work of all its value joins. *)
  Lemma join_fold {A} (f : A -> V.t) xs : forall a ticks,
    (fst (fold_left (fun acc x =>
      ((fst acc + V.T_join (snd acc) (f x) + 1)%N, V.join (snd acc) (f x)))
      xs (ticks, a)) <= ticks + growth ^ N.of_nat (length xs) *
      N.of_nat (V.size a + fold_right Nat.add 0%nat
        (map (fun x => V.size (f x) + 1)%nat xs) + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intros a ticks.
    - cbn [fold_left fst length map fold_right]; rewrite N.pow_0_r; nia.
    - specialize (IH (V.join a (f x)) (ticks + V.T_join a (f x) + 1)%N).
      pose proof (join_step a (f x)
        (N.of_nat (fold_right Nat.add 0%nat (map (fun x => V.size (f x) + 1)%nat xs))))
        as Hstep.
      set (scale := (growth ^ N.of_nat (length xs))%N) in *.
      assert (Hpositive : (1 <= scale)%N).
      { unfold scale; assert (Hnonzero : growth <> 0%N) by
          (unfold growth; lia).
        pose proof (N.pow_nonzero growth (N.of_nat (length xs)) Hnonzero); lia. }
      pose proof (N.mul_le_mono_l _ _ scale Hstep) as Hscaled.
      pose proof (N.mul_le_mono_r 1 scale (V.T_join a (f x) + 1)%N Hpositive) as Hpaid.
      cbn [fold_left fst snd length map fold_right].
      rewrite Nat2N.inj_succ, N.pow_succ_r'; fold scale.
      repeat rewrite Nat2N.inj_add in IH |- *.
      replace (growth * scale)%N with (scale * growth)%N by ring.
      repeat rewrite N.mul_add_distr_l in IH, Hscaled, Hpaid.
      rewrite N.mul_1_l in Hpaid; nia.
  Qed.

  (** The value-join budget of a capped input is linear in its input value sizes. *)
  Lemma joins_capped {A} (f : A -> V.t) xs : length xs <= C.k ->
    (fst (fold_left (fun acc x =>
      ((fst acc + V.T_join (snd acc) (f x) + 1)%N, V.join (snd acc) (f x)))
      xs (0%N, V.bot)) <= coefficient *
      N.of_nat (fold_right Nat.add 0%nat (map (fun x => V.size (f x) + 1)%nat xs) + 1))%N.
  Proof.
    intro Hcap; pose proof (join_fold f xs V.bot 0%N) as Hfold.
    assert (Hgrowth : growth <> 0%N) by (unfold growth; lia).
    assert (Hpower : (growth ^ N.of_nat (length xs) <=
      growth ^ N.of_nat (C.k + 1))%N).
    { apply N.pow_le_mono_r; [exact Hgrowth | lia]. }
    set (mass := N.of_nat (fold_right Nat.add 0%nat
      (map (fun x => V.size (f x) + 1)%nat xs) + 1)) in *.
    assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
    assert (Hinput : (N.of_nat (V.size V.bot + fold_right Nat.add 0%nat
      (map (fun x => V.size (f x) + 1)%nat xs) + 1) <=
      (N.of_nat (V.size V.bot) + 1) * mass)%N).
    { unfold mass; repeat rewrite Nat2N.inj_add; nia. }
    pose proof (N.mul_le_mono _ _ _ _ Hpower Hinput) as Hbudget.
    unfold coefficient, base_scale; nia.
  Qed.

  (** Fold timing separates callback work from the actual value-join sequence. *)
  Lemma fold_clock {A} (f : A -> V.t) (T_f : A -> N) xs : forall a ticks,
    (List.T_fold_left (fun a x => V.join a (f x))
      (fun a x => 1 + (T_f x + V.T_join a (f x)))%N xs a + ticks =
      fold_right N.add 0%N (map (fun x => T_f x + 1)%N xs) +
      fst (fold_left (fun acc x =>
        ((fst acc + V.T_join (snd acc) (f x) + 1)%N, V.join (snd acc) (f x)))
        xs (ticks, a)) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intros a ticks.
    - time_unfold @List.T_fold_left; cbn [fold_left fst map fold_right]; lia.
    - specialize (IH (V.join a (f x)) (ticks + V.T_join a (f x) + 1)%N).
      time_unfold @List.T_fold_left; cbn [fold_left fst snd map fold_right]; lia.
  Qed.
End ValueJoinBudget.

Lemma replace_first_length {A} (is_bot : A -> bool) (f : A -> A) xs :
  length (replace_first is_bot f xs) = length xs.
Proof.
  induction xs as [|x rest IH]; simpl; auto.
  destruct (is_bot x); simpl; now rewrite ?IH.
Qed.

Module StateDisjunctionCode (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP) (P : SharedDisjunction.DISJUNCTION_OPS S C)
    <: DISJUNCTION_OPS X L V S C P.
  Definition t := P.t.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top := P.clip [S.top].
  Definition collapse (xs : list S.t) : S.t :=
    match xs with [] => S.bot | x :: rest => fold_left S.join rest x end.
  Fixpoint compact_tail (n : nat) (xs : list S.t) : list S.t :=
    match n, xs with
    | S m, x :: rest => x :: compact_tail m rest
    | _, _ => [collapse xs]
    end.
  Definition compact (n : nat) (xs : list S.t) : list S.t :=
    if Nat.eqb n C.k then proj1_sig (P.clip xs)
    else if Nat.leb (length xs) n then xs else compact_tail (Nat.pred n) xs.
  Definition meet (a b : t) : t :=
    P.clip (flat_map (fun x => map (S.meet x) (proj1_sig b)) (proj1_sig a)).
  Definition wparam := S.wparam.
  Definition widen (p : wparam) (a b : t) : t.
  Proof.
    destruct a as [old Hbound].
    destruct (leb b (exist _ old Hbound)) eqn:Hstable.
    - exact (exist _ old Hbound).
    - destruct (is_bot (exist _ old Hbound)) eqn:Hempty.
      + exact b.
      + destruct (forallb S.is_bot old) eqn:Hbottom.
        * exact (P.clip [S.top]).
        * refine (exist _ (replace_first S.is_bot
          (fun x => S.widen p x (collapse (x :: uncovered S.leb old (proj1_sig b)))) old) _).
          now rewrite replace_first_length.
  Defined.
  Definition narrow (a _ : t) := a.

  Definition map_bounded (f : S.t -> S.t) (d : t) : t.
  Proof.
    destruct d as [xs Hbound].
    refine (exist _ (map f xs) _).
    now rewrite length_map.
  Defined.

  Definition assign x e (d : t) := map_bounded (S.assign x e) d.
  Definition havoc x (d : t) := map_bounded (S.havoc x) d.
  Definition assume g es (d : t) := map_bounded (S.assume g es) d.
  Definition eval e (d : t) := fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
End StateDisjunctionCode.

Module StateDisjunction (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (P : SharedDisjunction.DISJUNCTION S C)
    <: DISJUNCTION X L V S C P.
  Include StateDisjunctionCode X L V S C P.
  Definition gamma (d : t) (st : X.t -> L.val) : Prop :=
    Exists (fun s => S.gamma s st) (proj1_sig d).
  Definition wrank (p : wparam) (d : t) : nat :=
    fold_right Nat.add 0 (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.

  (** Every fold result covers its initial accumulator. *)
  Lemma fold_join_start : forall xs a, S.leb a (fold_left S.join xs a) = true.
  Proof.
    induction xs as [|x xs IH]; intro a; cbn [fold_left].
    - apply S.leb_refl.
    - eapply S.leb_trans; [apply S.join_ub_l | apply IH].
  Qed.

  (** Every member of a fold's input is below its result. *)
  Lemma fold_join_member : forall xs a x, In x xs ->
    S.leb x (fold_left S.join xs a) = true.
  Proof.
    induction xs as [|y xs IH]; intros a x Hin; cbn in Hin; [contradiction |].
    cbn [fold_left]; destruct Hin as [<- | Hin].
    - eapply S.leb_trans; [apply S.join_ub_r | apply fold_join_start].
    - apply IH; exact Hin.
  Qed.

  (** Collapse covers every raw alternative, including a singleton. *)
  Lemma collapse_upper : forall xs x, In x xs -> S.leb x (collapse xs) = true.
  Proof.
    intros [|a xs] x Hin; cbn [collapse] in *; [contradiction |].
    destruct Hin as [<- | Hin]; auto using fold_join_start, fold_join_member.
  Qed.

  (** Prefix compaction keeps each input below a returned alternative. *)
  Lemma compact_tail_covers : forall n xs x, In x xs ->
    exists y, In y (compact_tail n xs) /\ S.leb x y = true.
  Proof.
    induction n as [|n IH]; intros xs x Hin.
    - exists (collapse xs); split; [now left | now apply collapse_upper].
    - destruct xs as [|a xs]; [contradiction |].
      cbn [compact_tail]; destruct Hin as [<- | Hin].
      + exists a; split; [now left | apply S.leb_refl].
      + destruct (IH xs x Hin) as [y [Hy Hle]].
        exists y; split; [now right | exact Hle].
  Qed.

  (** A compacted suffix contributes at most one extra alternative. *)
  Lemma compact_tail_length : forall n xs, length (compact_tail n xs) <= n + 1.
  Proof.
    induction n as [|n IH]; intros [|x xs]; cbn [compact_tail length]; try lia.
    specialize (IH xs); lia.
  Qed.

  (** The raw widening equation exposes only the chosen branch's alternatives. *)
  Lemma widen_raw : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    if forallb S.is_bot (proj1_sig a) then [S.top] else
    replace_first S.is_bot
      (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))))
      (proj1_sig a).
  Proof.
    intros p [xs Hbound] b; unfold widen; cbn [proj1_sig].
    destruct (leb b (exist _ xs Hbound)); [reflexivity |].
    destruct (is_bot (exist _ xs Hbound)); [reflexivity |].
    destruct (forallb S.is_bot xs); [|reflexivity].
    apply P.clip_small; cbn; exact C.k_pos.
  Qed.

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
    intro a; apply P.leb_spec; intros x Hin; exists S.top; split.
    - unfold top; rewrite P.clip_small; [now left | cbn; exact C.k_pos].
    - apply S.top_greatest.
  Qed.

  (** Replacing an alternative by an upper bound preserves raw coverage. *)
  Lemma replace_first_covers : forall f xs,
    (forall x, In x xs -> S.leb x (f x) = true) ->
    forall x, In x xs ->
    exists y, In y (replace_first S.is_bot f xs) /\ S.leb x y = true.
  Proof.
    intros f xs; induction xs as [|a xs IH]; intros Hupper x Hin; [contradiction |].
    cbn [replace_first]; destruct (S.is_bot a).
    - destruct Hin as [<- | Hin].
      + exists a; split; [now left | apply S.leb_refl].
      + destruct (IH (fun y Hy => Hupper y (or_intror Hy)) x Hin) as [y [Hy Hle]].
        exists y; split; [now right | exact Hle].
    - destruct Hin as [<- | Hin].
      + exists (f a); split; [now left | apply Hupper; now left].
      + exists x; split; [now right | apply S.leb_refl].
  Qed.

  (** A list with a nonbottom alternative contains the selected replacement. *)
  Lemma replace_first_selected : forall f xs, forallb S.is_bot xs = false ->
    exists x, In x xs /\ S.is_bot x = false /\ In (f x) (replace_first S.is_bot f xs).
  Proof.
    intros f xs; induction xs as [|a xs IH]; intro Hnonbottom; [discriminate |].
    cbn [forallb] in Hnonbottom; cbn [replace_first]; destruct (S.is_bot a) eqn:Ha.
    - cbn in Hnonbottom; destruct (IH Hnonbottom) as [x [Hin [Hx Hselected]]].
      exists x; repeat split; auto; now right.
    - exists a; repeat split; auto; now left.
  Qed.

  (** Each candidate is already covered or occurs in the uncovered list. *)
  Lemma candidate_covered_or_new : forall old new y, In y new ->
    (exists x, In x old /\ S.leb y x = true) \/ In y (uncovered S.leb old new).
  Proof.
    intros old new y Hin; destruct (existsb (S.leb y) old) eqn:Hcovered.
    - left; now apply existsb_exists.
    - right; apply filter_In; split; [exact Hin | now rewrite Hcovered].
  Qed.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b; apply P.leb_spec; intros x Hin; rewrite widen_raw.
    destruct (leb b a); [exists x; split; [exact Hin | apply S.leb_refl] |].
    destruct (is_bot a) eqn:Hempty.
    - apply P.is_bot_spec in Hempty; rewrite Hempty in Hin; contradiction.
    - destruct (forallb S.is_bot (proj1_sig a)).
      + exists S.top; split; [now left | apply S.top_greatest].
      + apply replace_first_covers; [intros; apply S.widen_ub_l | exact Hin].
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b; destruct (leb b a) eqn:Hstable.
    - apply P.leb_spec; intros y Hin; rewrite widen_raw, Hstable.
      exact (proj1 (P.leb_spec b a) Hstable y Hin).
    - apply P.leb_spec; intros y Hin; rewrite widen_raw, Hstable.
      destruct (is_bot a); [exists y; split; [exact Hin | apply S.leb_refl] |].
      destruct (forallb S.is_bot (proj1_sig a)) eqn:Hnonbottom.
      + exists S.top; split; [now left | apply S.top_greatest].
      + destruct (candidate_covered_or_new (proj1_sig a) (proj1_sig b) y Hin)
          as [[x [Hx Hle]] | Hnew].
        * destruct (replace_first_covers
            (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a)
              (proj1_sig b)))) (proj1_sig a)
            (fun x _ => S.widen_ub_l p x _) x Hx) as [z [Hz Hxz]].
          exists z; split; [exact Hz | eapply S.leb_trans; eassumption].
        * destruct (replace_first_selected
            (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a)
              (proj1_sig b)))) (proj1_sig a) Hnonbottom) as [x [Hx [Hbot Hselected]]].
          eexists; split; [exact Hselected |].
          eapply S.leb_trans; [|apply S.widen_ub_r].
          apply collapse_upper; now right.
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p [xs Hbound] b Hstable; unfold widen; now rewrite Hstable.
  Qed.

  (** A failed coverage scan exhibits a candidate with no covering old alternative. *)
  Lemma uncovered_witness : forall a b, leb b a = false ->
    exists y, In y (uncovered S.leb (proj1_sig a) (proj1_sig b)).
  Proof.
    intros a b Hstrict.
    assert (Hscan : forallb (fun y => existsb (S.leb y) (proj1_sig a))
      (proj1_sig b) = false).
    { destruct (forallb (fun y => existsb (S.leb y) (proj1_sig a))
        (proj1_sig b)) eqn:Hscan; [|reflexivity].
      assert (Hcovered : leb b a = true).
      { apply P.leb_spec; intros y Hin; apply existsb_exists.
        apply forallb_forall with (x := y) in Hscan; assumption. }
      congruence. }
    revert Hscan; generalize (proj1_sig b); clear Hstrict b.
    intros ys; induction ys as [|y ys IH]; intro Hscan; [discriminate |].
    cbn [forallb] in Hscan.
    destruct (existsb (S.leb y) (proj1_sig a)) eqn:Hy.
    - cbn in Hscan; destruct (IH Hscan) as [z Hz].
      exists z; apply filter_In in Hz; apply filter_In; destruct Hz as [Hz Hbad].
      split; [now right | exact Hbad].
    - exists y; apply filter_In; split; [now left | now rewrite Hy].
  Qed.

  (** Joining an uncovered candidate cannot stay below any old alternative. *)
  Lemma collapse_strict : forall old new x,
    In x old -> (exists y, In y (uncovered S.leb old new)) ->
    S.leb (collapse (x :: uncovered S.leb old new)) x = false.
  Proof.
    intros old new x Hx [y Hy]; apply Bool.not_true_is_false; intro Hle.
    pose proof Hy as Hfilter; apply filter_In in Hfilter; destruct Hfilter as [_ Hbad].
    assert (Hcovered : existsb (S.leb y) old = true).
    { apply existsb_exists; exists x; split; [exact Hx |].
      eapply S.leb_trans; [|exact Hle].
      apply collapse_upper; now right. }
    rewrite Hcovered in Hbad; discriminate.
  Qed.

  (** A strict widening result cannot be recognized as bottom. *)
  Lemma strict_widen_nonbottom : forall p x c, S.leb c x = false ->
    S.is_bot (S.widen p x c) = false.
  Proof.
    intros p x c Hstrict; apply Bool.not_true_is_false; intro Hbottom.
    assert (Hle : S.leb c x = true).
    { eapply S.leb_trans with (b := S.widen p x c).
      - apply S.widen_ub_r.
      - apply S.is_bot_least; exact Hbottom. }
    congruence.
  Qed.

  (** Changing the selected nonbottom lowers the sum and keeps a nonbottom alternative. *)
  Lemma replace_first_rank : forall p f xs,
    forallb S.is_bot xs = false ->
    (forall x, In x xs -> S.is_bot x = false ->
      S.wrank p (f x) < S.wrank p x /\ S.is_bot (f x) = false) ->
    fold_right Nat.add 0 (map (S.wrank p) (replace_first S.is_bot f xs)) <
      fold_right Nat.add 0 (map (S.wrank p) xs) /\
    forallb S.is_bot (replace_first S.is_bot f xs) = false.
  Proof.
    intros p f xs; induction xs as [|a xs IH]; intros Hnonbottom Hstep;
      [discriminate |].
    cbn [forallb] in Hnonbottom; cbn [replace_first]; destruct (S.is_bot a) eqn:Ha.
    - cbn in Hnonbottom.
      destruct (IH Hnonbottom (fun x Hx => Hstep x (or_intror Hx))) as [Hrank Hbot].
      cbn [map fold_right forallb]; rewrite Ha, Hbot; split; [lia | reflexivity].
    - destruct (Hstep a (or_introl eq_refl) Ha) as [Hrank Hbot].
      cbn [map fold_right forallb]; rewrite Hbot; split; [lia | reflexivity].
  Qed.

  (** A strict update of a nonempty list rules out a recognized bottom top. *)
  Lemma strict_top_nonbottom : forall a b, is_bot a = false -> leb b a = false ->
    S.is_bot S.top = false.
  Proof.
    intros a b Hnonempty Hstrict; apply Bool.not_true_is_false; intro Htop.
    destruct (proj1_sig a) as [|x xs] eqn:Hxs.
    - assert (Hempty : is_bot a = true) by (apply P.is_bot_spec; exact Hxs).
      congruence.
    - assert (Hcovered : leb b a = true).
      { apply P.leb_spec; intros y Hy; exists x; split; [rewrite Hxs; now left |].
        eapply S.leb_trans; [apply S.top_greatest | now apply S.is_bot_least]. }
      congruence.
  Qed.

  (** An unstable widening from a nonbottom strictly decreases rank. *)
  (* F2-22 replaced the former twoStateDisj aligned-pair rank route with uncovered
     alternatives, and F2-30 supplies the size and widening-unit capabilities it needs. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p a b Hnonempty Hstrict; unfold wrank.
    rewrite widen_raw, Hstrict, Hnonempty.
    destruct (forallb S.is_bot (proj1_sig a)) eqn:Hbottom.
    - pose proof (strict_top_nonbottom a b Hnonempty Hstrict) as Htop.
      cbn [map fold_right forallb]; rewrite Htop; cbn; lia.
    - pose proof (uncovered_witness a b Hstrict) as Huncovered.
      destruct (replace_first_rank p
        (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a)
          (proj1_sig b)))) (proj1_sig a) Hbottom) as [Hrank Hbot].
      + intros x Hx Hnotbot.
        pose proof (collapse_strict (proj1_sig a) (proj1_sig b) x Hx Huncovered) as Hgrowth.
        split; [now apply S.wrank_widen | now apply strict_widen_nonbottom].
      + rewrite Hbot; lia.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hnonbottom; destruct (leb b a) eqn:Hstable.
    - rewrite widen_stable by exact Hstable; lia.
    - pose proof (wrank_widen p a b Hnonbottom Hstable); lia.
  Qed.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle; split; [exact Hle | apply leb_refl].
  Qed.

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof.
    intros a b st Hle Hgamma; apply Exists_exists in Hgamma.
    destruct Hgamma as [x [Hin Hx]].
    destruct (proj1 (P.leb_spec a b) Hle x Hin) as [y [Hy Hxy]].
    apply Exists_exists; exists y; split; [exact Hy |].
    eapply S.gamma_mono; eassumption.
  Qed.
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intros st Hgamma; unfold gamma, bot in Hgamma; rewrite P.bot_raw in Hgamma.
    inversion Hgamma.
  Qed.
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof.
    intro st; unfold gamma, top; rewrite P.clip_small.
    - constructor; apply S.gamma_top.
    - cbn; exact C.k_pos.
  Qed.
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof.
    intros x e [xs Hbound] st c Hgamma Heval; apply Exists_exists in Hgamma.
    destruct Hgamma as [a [Hin Ha]].
    apply Exists_exists; exists (S.assign x e a); split.
    - apply in_map; exact Hin.
    - eapply S.assign_sound; eassumption.
  Qed.
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof.
    intros x [xs Hbound] st c Hgamma; apply Exists_exists in Hgamma.
    destruct Hgamma as [a [Hin Ha]].
    apply Exists_exists; exists (S.havoc x a); split.
    - apply in_map; exact Hin.
    - apply S.havoc_sound; exact Ha.
  Qed.
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof.
    intros g es [xs Hbound] st cs Hgamma Heval Hholds; apply Exists_exists in Hgamma.
    destruct Hgamma as [a [Hin Ha]].
    apply Exists_exists; exists (S.assume g es a); split.
    - apply in_map; exact Hin.
    - eapply S.assume_sound; eassumption.
  Qed.
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof.
    intros e [xs Hbound] st c Hgamma Heval; unfold eval; cbn [proj1_sig].
    assert (Hfold : forall ys acc, V.gamma acc c \/ Exists (fun s => S.gamma s st) ys ->
      V.gamma (fold_left (fun a s => V.join a (S.eval e s)) ys acc) c).
    { induction ys as [|a ys IH]; intros acc Hcovered; cbn [fold_left].
      - destruct Hcovered as [Hacc | Hnone]; [exact Hacc | inversion Hnone].
      - apply IH; destruct Hcovered as [Hacc | Hsome].
        + left; eapply V.gamma_mono; [apply V.join_ub_l | exact Hacc].
        + inversion Hsome as [a' rest Ha | a' rest Hrest]; subst.
          * left; eapply V.gamma_mono; [apply V.join_ub_r |].
            eapply S.eval_sound; eassumption.
          * right; exact Hrest. }
    apply Hfold; right; exact Hgamma.
  Qed.
  Lemma gamma_alternatives : forall d st,
    gamma d st <-> Exists (fun s => S.gamma s st) (proj1_sig d).
  Proof.
    reflexivity.
  Qed.
  Lemma leb_hoare : forall a b, leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  Proof.
    intros a b; apply eq_true_iff_eq; rewrite P.leb_spec, forallb_forall.
    split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
  Qed.
  Lemma join_compact : forall a b, join a b = P.clip (proj1_sig a ++ proj1_sig b).
  Proof.
    exact P.join_clip.
  Qed.
  Lemma compact_cap : forall d, compact C.k d = proj1_sig (P.clip d).
  Proof.
    intro d; unfold compact; now rewrite Nat.eqb_refl.
  Qed.
  Lemma compact_covers : forall n d x, In x d ->
    exists y, In y (compact n d) /\ S.leb x y = true.
  Proof.
    intros n d x Hin; unfold compact; destruct (Nat.eqb n C.k).
    - apply P.clip_covers; [exact C.k_pos | exact Hin].
    - destruct (Nat.leb (length d) n).
      + exists x; split; [exact Hin | apply S.leb_refl].
      + now apply compact_tail_covers.
  Qed.
  Lemma compact_len : forall n d, length (compact n d) <= Nat.max n 1.
  Proof.
    intros n d; unfold compact; destruct (Nat.eqb n C.k) eqn:Hcap.
    - apply Nat.eqb_eq in Hcap; subst n.
      pose proof (proj2_sig (P.clip d)) as Hbound; apply Nat.leb_le in Hbound; lia.
    - destruct (Nat.leb (length d) n) eqn:Hlength.
      + apply Nat.leb_le in Hlength; lia.
      + pose proof (compact_tail_length (Nat.pred n) d); destruct n; cbn in *; lia.
  Qed.
  Lemma collapse_covers : forall xs x, In x xs -> S.leb x (collapse xs) = true.
  Proof.
    exact collapse_upper.
  Qed.
End StateDisjunction.

Module StateDisjunctionT (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C)
    <: DISJUNCTION_ALL X L V S JS JU C P.
  Module Plain := StateDisjunction X L V S C P.
  Include Plain.
  Module ValueJoins := ValueJoinBudget L V C.
  Definition T_leb : t -> t -> N := P.T_leb.
  Definition T_join : t -> t -> N := P.T_join.
  Definition T_is_bot : t -> N := P.T_is_bot.
  TimeFun top.
  TimeFun collapse.
  TimeFun compact_tail.
  TimeFun compact.
  TimeFun widen.
  TimeFun narrow.
  TimeFun map_bounded.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.
  Definition size : t -> nat := P.size.
  Local Definition state_growth : N := (2 * (S.c_lat + 1))%N.
  Local Definition state_scale : N := state_growth ^ N.of_nat (C.k + 2).
  Definition c_disjunction : N :=
    (16 * (state_scale + N.of_nat (S.size S.bot + S.wunits S.bot) + 1))%N.
  Definition k_disjunction : N := ValueJoins.coefficient.
  Definition c_lat : N :=
    (64 * (P.c_lat + S.c_lat + 1) * (c_disjunction + 1) * (k_disjunction + 1) *
      N.of_nat ((C.k + 1) * (C.k + 1)) * (N.of_nat (S.size S.top) + 1))%N.
  Definition c_state : N :=
    (16 * (S.c_state + k_disjunction + 1) * (k_disjunction + 1))%N.
  Definition wsize : wparam -> nat := S.wsize.
  Definition wunits (d : t) : nat :=
    fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  Definition assign_work (x : X.t) (e : term L.op X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  Definition havoc_work (x : X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  Definition eval_work (e : term L.op X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).

  Definition eval_joins (e : term L.op X.t) (xs : list S.t) : N :=
    fst (fold_left (fun acc s =>
      ((fst acc + V.T_join (snd acc) (S.eval e s) + 1)%N,
       V.join (snd acc) (S.eval e s))) xs (0%N, V.bot)).

  (** Both fixed coefficients reserve the constant cost of a wrapper. *)
  Local Lemma coefficients_positive : (16 <= c_disjunction /\ 16 <= k_disjunction)%N.
  Proof.
    unfold c_disjunction, k_disjunction, ValueJoins.coefficient; split; nia.
  Qed.

  (** The lattice coefficient includes its inherited component's coefficient. *)
  Local Lemma lattice_coefficient : (1 <= c_lat /\ P.c_lat <= c_lat)%N.
  Proof.
    assert (Hcap : (1 <= N.of_nat ((C.k + 1) * (C.k + 1)))%N) by lia.
    unfold c_lat; split; nia.
  Qed.

  (** Evaluation's derived clock separates component evaluations and actual joins. *)
  Local Lemma eval_clock : forall e d, T_eval e d =
    (fold_right N.add 0%N (map (fun s => S.T_eval e s + 1)%N (proj1_sig d)) +
      eval_joins e (proj1_sig d) + 3)%N.
  Proof.
    intros e [xs Hbound]; pose proof
      (ValueJoins.fold_clock (S.eval e) (S.T_eval e) xs V.bot 0%N) as Hfold.
    time_unfold @T_eval; time_unfold @Specif.T_proj1_sig.
    cbn [proj1_sig]; unfold eval_joins; lia.
  Qed.

  (** Every evaluated value size fits in the published evaluation work sum. *)
  Local Lemma evaluation_sizes : forall e xs,
    fold_right Nat.add 0%nat (map (fun s => V.size (S.eval e s) + 1)%nat xs) <=
    fold_right Nat.add 0%nat
      (map (fun s => S.eval_work e s + V.size (S.eval e s) + 1)%nat xs).
  Proof.
    intros e xs; induction xs as [|x xs IH]; cbn [map fold_right]; lia.
  Qed.

  (** Raw alternative size includes one cell for every stored state. *)
  Local Definition state_mass (xs : list S.t) : nat :=
    fold_right (fun x rest => S.size x + 1 + rest)%nat 0%nat xs.

  (** The raw size is the sum of state sizes and the alternative count. *)
  Local Lemma state_mass_values : forall xs, state_mass xs =
    fold_right Nat.add 0%nat (map S.size xs) + length xs.
  Proof.
    intro xs; induction xs as [|x xs IH]; unfold state_mass in *;
      cbn [map fold_right length]; lia.
  Qed.

  (** One state join accounts for both computation and the resulting representation. *)
  Local Lemma state_join_step a b tail :
    (1 + S.T_join a b + N.of_nat (S.size (S.join a b)) + tail + 1 <=
      state_growth * (N.of_nat (S.size a) + N.of_nat (S.size b) + tail + 2))%N.
  Proof.
    pose proof (S.T_join_le a b) as Hclock; pose proof (JS.join_size a b) as Hsize.
    unfold state_growth; repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** A state fold controls its clock and output size by a fixed growth factor. *)
  Local Lemma state_fold_budget xs : forall a,
    (List.T_fold_left S.join S.T_join xs a +
      N.of_nat (S.size (fold_left S.join xs a)) + 1 <=
      state_growth ^ N.of_nat (length xs + 1) *
        N.of_nat (S.size a + state_mass xs + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intro a.
    - time_unfold @List.T_fold_left; cbn [fold_left length state_mass fold_right].
      rewrite N.pow_1_r; repeat rewrite Nat2N.inj_add; unfold state_growth; nia.
    - specialize (IH (S.join a x)).
      pose proof (state_join_step a x (N.of_nat (state_mass xs))) as Hstep.
      set (scale := (state_growth ^ N.of_nat (length xs + 1))%N) in *.
      assert (Hpositive : (1 <= scale)%N).
      { unfold scale; assert (Hnonzero : state_growth <> 0%N) by
          (unfold state_growth; lia).
        pose proof (N.pow_nonzero state_growth (N.of_nat (length xs + 1)) Hnonzero); lia. }
      pose proof (N.mul_le_mono_l _ _ scale Hstep) as Hscaled.
      pose proof (N.mul_le_mono_r 1 scale (1 + S.T_join a x)%N Hpositive) as Hpaid.
      time_unfold @List.T_fold_left; cbn [fold_left length].
      replace (Datatypes.S (length xs) + 1) with (Datatypes.S (length xs + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r'; fold scale.
      change (state_mass (x :: xs)) with (S.size x + 1 + state_mass xs).
      repeat rewrite Nat2N.inj_add in IH |- *.
      replace (state_growth * scale)%N with (scale * state_growth)%N by ring.
      repeat rewrite N.mul_add_distr_l in IH, Hscaled, Hpaid.
      rewrite N.mul_1_l in Hpaid; nia.
  Qed.

  (** A capped collapse pays for its clock and output size together. *)
  Local Lemma collapse_budget xs : length xs <= C.k + 1 ->
    (T_collapse xs + N.of_nat (S.size (collapse xs)) <= c_disjunction *
      N.of_nat (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof.
    intro Hcap; destruct xs as [|x xs].
    - time_unfold @T_collapse; cbn [collapse map fold_right length].
      unfold c_disjunction; rewrite Nat2N.inj_add; nia.
    - pose proof (state_fold_budget xs x) as Hfold.
      change (List.T_fold_left S.join S.T_join xs x) with
        (List.T_fold_left S.join (fun a b => S.T_join a b) xs x) in Hfold.
      assert (Hpower : (state_growth ^ N.of_nat (length xs + 1) <= state_scale)%N).
      { unfold state_scale; apply N.pow_le_mono_r.
        - unfold state_growth; lia.
        - cbn [length] in Hcap; lia. }
      assert (Hcoefficient : (state_scale <= c_disjunction)%N) by
        (unfold c_disjunction; nia).
      pose proof (N.mul_le_mono_r _ _ (N.of_nat (S.size x + state_mass xs + 1))
        (N.le_trans _ _ _ Hpower Hcoefficient)) as Hscaled.
      time_unfold @T_collapse; cbn [collapse map fold_right length].
      rewrite state_mass_values in Hfold, Hscaled.
      repeat rewrite Nat2N.inj_add in *; rewrite ?Nat2N.inj_succ in *; nia.
  Qed.

  (** A join fold increases widening units by at most the same fixed growth factor. *)
  Local Lemma state_fold_units xs : forall a,
    (N.of_nat (S.wunits (fold_left S.join xs a)) + 1 <=
      state_growth ^ N.of_nat (length xs) *
      N.of_nat (S.wunits a + fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intro a.
    - cbn [fold_left length map fold_right]; rewrite N.pow_0_r;
        repeat rewrite Nat2N.inj_add; nia.
    - specialize (IH (S.join a x)); pose proof (JU.join_wunits a x) as Hjoin.
      assert (Hstep : (N.of_nat (S.wunits (S.join a x) +
          fold_right Nat.add 0%nat (map S.wunits xs) + 1) <=
        state_growth * N.of_nat (S.wunits a + S.wunits x +
          fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N).
      { unfold state_growth; repeat rewrite Nat2N.inj_add in *; nia. }
      pose proof (N.mul_le_mono_l _ _ (state_growth ^ N.of_nat (length xs)) Hstep)
        as Hscaled.
      cbn [fold_left length map fold_right]; rewrite Nat2N.inj_succ, N.pow_succ_r'.
      repeat rewrite Nat2N.inj_add in *; nia.
  Qed.

  Lemma T_collapse_le : forall xs, length xs <= C.k + 1 ->
    (T_collapse xs <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof.
    intros xs Hcap; pose proof (collapse_budget xs Hcap); lia.
  Qed.
  Lemma collapse_size : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.size (collapse xs)) <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof.
    intros xs Hcap; pose proof (collapse_budget xs Hcap); lia.
  Qed.
  Lemma collapse_wunits : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.wunits (collapse xs)) <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof.
    intros [|x xs] Hcap.
    - cbn [collapse map fold_right]; unfold c_disjunction; rewrite Nat2N.inj_add; nia.
    - pose proof (state_fold_units xs x) as Hfold.
      assert (Hpower : (state_growth ^ N.of_nat (length xs) <= state_scale)%N).
      { unfold state_scale; apply N.pow_le_mono_r.
        - unfold state_growth; lia.
        - cbn [length] in Hcap; lia. }
      assert (Hcoefficient : (state_scale <= c_disjunction)%N) by
        (unfold c_disjunction; nia).
      pose proof (N.mul_le_mono_r _ _
        (N.of_nat (S.wunits x + fold_right Nat.add 0%nat (map S.wunits xs) + 1))
        (N.le_trans _ _ _ Hpower Hcoefficient)) as Hscaled.
      cbn [collapse map fold_right]; nia.
  Qed.

  (** Boolean existential traversal charges each callback and two scalar steps. *)
  Local Lemma exists_clock {A} (f : A -> bool) (T_f : A -> N) xs :
    (List.T_existsb f T_f xs <=
      2 * (fold_right N.add 0%N (map (fun x => T_f x + 1)%N xs) + 1))%N.
  Proof.
    induction xs as [|x xs IH]; time_unfold @List.T_existsb; time_simpl;
      cbn [map fold_right]; nia.
  Qed.

  (** Boolean universal traversal has a linear cell and callback budget. *)
  Local Lemma forall_clock {A} (f : A -> bool) (T_f : A -> N) xs :
    (List.T_forallb f T_f xs <= 2 *
      (fold_right N.add 0%N (map T_f xs) + N.of_nat (length xs) + 1))%N.
  Proof.
    induction xs as [|x xs IH]; time_unfold @List.T_forallb; time_simpl;
      cbn [map fold_right length]; rewrite ?Nat2N.inj_succ; nia.
  Qed.

  (** Pairwise comparison work includes a unit for every examined pair. *)
  Local Definition scan_work (old new : list S.t) : N :=
    fold_right N.add 0%N (map (fun y => fold_right N.add 0%N
      (map (fun x => S.T_leb y x + 1)%N old)) new).

  (** Filtering candidates costs at most a constant times their comparison scan. *)
  Local Lemma uncovered_clock old new : old <> [] ->
    (T_uncovered S.leb S.T_leb old new <= 8 * (scan_work old new + 1))%N.
  Proof.
    intro Hnonempty.
    assert (Hfilter : (List.T_filter (fun y => negb (existsb (S.leb y) old))
        (fun y => 1 + (List.T_existsb (S.leb y) (fun x => S.T_leb y x) old +
          Datatypes.T_negb (existsb (S.leb y) old)))%N new <=
        7 * scan_work old new + 1)%N).
    { induction new as [|y ys IH].
      - time_unfold @List.T_filter; unfold scan_work; cbn [map fold_right]; lia.
      - pose proof (exists_clock (S.leb y) (fun x => S.T_leb y x) old) as Hrow.
        assert (Hrowpos : (1 <= fold_right N.add 0%N
          (map (fun x => S.T_leb y x + 1)%N old))%N).
        { destruct old as [|x xs]; [contradiction |]; cbn [map fold_right]; nia. }
        cbv [Datatypes.T_negb] in IH.
        time_unfold @List.T_filter; time_simpl; unfold scan_work in *;
          cbn [map fold_right]; destruct (negb (existsb (S.leb y) old)); nia. }
    time_unfold @T_uncovered; nia.
  Qed.

  (** The replacement traversal charges its shared callback setup only once. *)
  Local Lemma replace_clock {A} (bot : A -> bool) (T_bot : A -> N)
      (f : A -> A) (T_f work : A -> N) common xs :
    (forall x, In x xs -> (T_f x <= common + work x)%N) ->
    (T_replace_first bot T_bot f T_f xs <=
      fold_right N.add 0%N (map T_bot xs) + N.of_nat (length xs) + 1 + common +
      fold_right N.add 0%N (map work xs))%N.
  Proof.
    induction xs as [|x xs IH]; intro Hcalls.
    - time_unfold @T_replace_first; cbn [map fold_right length]; nia.
    - specialize (IH (fun y Hy => Hcalls y (or_intror Hy))).
      pose proof (Hcalls x (or_introl eq_refl)) as Hcall.
      time_unfold @T_replace_first; cbn [map fold_right length].
      rewrite Nat2N.inj_succ; destruct (bot x); nia.
  Qed.

  (** The public widening plan combines tests, scans and possible receiver updates. *)
  Local Definition widen_budget p (a b : t) : N :=
    (T_leb b a + T_is_bot a + P.T_clip [S.top] + N.of_nat (length (proj1_sig a) + 1) +
      fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) +
      scan_work (proj1_sig a) (proj1_sig b) +
      fold_right N.add 0%N (map (fun x =>
        let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
        T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
        (proj1_sig a)))%N.

  (** Every widening branch is paid by the same public scan budget. *)
  Local Lemma widen_clock : forall p a b,
    (T_widen p a b <= k_disjunction * widen_budget p a b)%N.
  Proof.
    intros p [old Hbound] b; pose proof (proj2 coefficients_positive) as Hcoefficient.
    pose proof (forall_clock S.is_bot (fun x => S.T_is_bot x) old) as Hforall.
    change (fold_right N.add 0%N (map (fun x => S.T_is_bot x) old)) with
      (fold_right N.add 0%N (map S.T_is_bot old)) in Hforall.
    time_unfold @T_widen; unfold widen_budget; cbn [proj1_sig].
    rewrite Nat2N.inj_add.
    destruct (leb b (exist _ old Hbound)) eqn:Hstable; [nia |].
    destruct (is_bot (exist _ old Hbound)) eqn:Hempty; [nia |].
    destruct (forallb S.is_bot old) eqn:Hbottom; [nia |].
    assert (Hnonempty : old <> []).
    { intro Heq; assert (Hbot : is_bot (exist _ old Hbound) = true).
      { apply P.is_bot_spec; exact Heq. } congruence. }
    pose proof (uncovered_clock old (proj1_sig b) Hnonempty) as Hscan.
    pose proof (replace_clock S.is_bot (fun x => S.T_is_bot x)
      (fun x => S.widen p x (collapse (x :: uncovered S.leb old (proj1_sig b))))
      (fun x => 1 + (Specif.T_proj1_sig b + T_uncovered S.leb
        (fun y z => S.T_leb y z) old (proj1_sig b) +
        T_collapse (x :: uncovered S.leb old (proj1_sig b)) +
        S.T_widen p x (collapse (x :: uncovered S.leb old (proj1_sig b)))))%N
      (fun x => T_collapse (x :: uncovered S.leb old (proj1_sig b)) +
        S.T_widen p x (collapse (x :: uncovered S.leb old (proj1_sig b))))%N
      (T_uncovered S.leb S.T_leb old (proj1_sig b) + 2)%N old) as Hreplace.
    assert (Hcalls : forall x, In x old ->
      (1 + (Specif.T_proj1_sig b + T_uncovered S.leb
        (fun y z => S.T_leb y z) old (proj1_sig b) +
        T_collapse (x :: uncovered S.leb old (proj1_sig b)) +
        S.T_widen p x (collapse (x :: uncovered S.leb old (proj1_sig b)))) <=
        T_uncovered S.leb S.T_leb old (proj1_sig b) + 2 +
        (T_collapse (x :: uncovered S.leb old (proj1_sig b)) +
          S.T_widen p x (collapse (x :: uncovered S.leb old (proj1_sig b)))))%N).
    { intros x Hin; time_unfold @Specif.T_proj1_sig.
      change (T_uncovered S.leb S.T_leb old (proj1_sig b)) with
        (T_uncovered S.leb (fun y z => S.T_leb y z) old (proj1_sig b)).
      lia. }
    specialize (Hreplace Hcalls).
    change (T_uncovered S.leb S.T_leb old (proj1_sig b)) with
      (T_uncovered S.leb (fun y z => S.T_leb y z) old (proj1_sig b)) in *.
    change (fold_right N.add 0%N (map (fun x => S.T_is_bot x) old)) with
      (fold_right N.add 0%N (map S.T_is_bot old)) in Hreplace.
    nia.
  Qed.

  (** A uniform member budget bounds a complete sum of callback costs. *)
  Local Lemma sum_uniform {A} (f : A -> N) xs budget :
    (forall x, In x xs -> (f x <= budget)%N) ->
    (fold_right N.add 0%N (map f xs) <= N.of_nat (length xs) * budget)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hcalls; cbn [map fold_right length]; [lia |].
    specialize (IH (fun y Hy => Hcalls y (or_intror Hy))).
    pose proof (Hcalls x (or_introl eq_refl)); rewrite Nat2N.inj_succ; nia.
  Qed.

  (** Every member's nonnegative weight fits in the entire list sum. *)
  Local Lemma sum_member {A} (f : A -> nat) xs x : In x xs ->
    f x <= fold_right Nat.add 0%nat (map f xs).
  Proof.
    induction xs as [|y xs IH]; intro Hin; [contradiction |].
    cbn [map fold_right]; destruct Hin as [<- | Hin]; [lia | specialize (IH Hin); lia].
  Qed.

  (** Removing alternatives cannot increase the sum of their nonnegative weights. *)
  Local Lemma sum_filter {A} (f : A -> nat) pred xs :
    fold_right Nat.add 0%nat (map f (filter pred xs)) <=
      fold_right Nat.add 0%nat (map f xs).
  Proof.
    induction xs as [|x xs IH]; cbn [filter map fold_right]; [lia |].
    destruct (pred x); cbn [map fold_right]; lia.
  Qed.

  (** The shared disjunction size is its raw alternative mass plus a terminal unit. *)
  Local Lemma size_mass : forall d, size d = state_mass (proj1_sig d) + 1.
  Proof.
    intros [xs Hbound]; change
      (fold_right (fun x rest => S.size x + 1 + rest)%nat 1%nat xs = state_mass xs + 1).
    clear Hbound; unfold state_mass; induction xs as [|x xs IH]; cbn [fold_right]; lia.
  Qed.

  (** Every member's size and units fit the disjunction's corresponding measure. *)
  Local Lemma member_measures : forall d x, In x (proj1_sig d) ->
    S.size x <= size d /\ S.wunits x <= wunits d.
  Proof.
    intros d x Hin; split.
    - pose proof (sum_member S.size (proj1_sig d) x Hin).
      rewrite size_mass, state_mass_values; lia.
    - exact (sum_member S.wunits (proj1_sig d) x Hin).
  Qed.

  (** A receiver and its uncovered candidates fit the combined state-size budget. *)
  Local Lemma receiver_budget : forall a b x, In x (proj1_sig a) ->
    let xs := x :: uncovered S.leb (proj1_sig a) (proj1_sig b) in
    length xs <= C.k + 1 /\
    fold_right Nat.add 0%nat (map S.size xs) + length xs + 1 <= size a + size b + 1 /\
    fold_right Nat.add 0%nat (map S.wunits xs) + 1 <= wunits a + wunits b + 1.
  Proof.
    intros a b x Hin; cbn [map fold_right length].
    pose proof (member_measures a x Hin) as [Hsize Hunits].
    pose proof (filter_length (fun y => negb (existsb (S.leb y) (proj1_sig a)))
      (proj1_sig b)) as Hlength.
    pose proof (sum_filter S.size
      (fun y => negb (existsb (S.leb y) (proj1_sig a))) (proj1_sig b)) as Hsizes.
    pose proof (sum_filter S.wunits
      (fun y => negb (existsb (S.leb y) (proj1_sig a))) (proj1_sig b)) as Hunit_sum.
    assert (Hcap : length (proj1_sig b) <= C.k) by (apply Nat.leb_le; exact (proj2_sig b)).
    rewrite (size_mass b), state_mass_values; unfold uncovered, wunits in *; split; [lia |].
    split; lia.
  Qed.

  (** This coefficient accounts for cap bounds, joins and the fixed top representation. *)
  Local Definition lattice_factor : N :=
    ((P.c_lat + S.c_lat + 1) * (c_disjunction + 1) *
      N.of_nat ((C.k + 1) * (C.k + 1)) * (N.of_nat (S.size S.top) + 1))%N.

  (** The shared lattice factor dominates each scan and receiver coefficient. *)
  Local Lemma lattice_factors :
    (1 <= lattice_factor /\ P.c_lat <= lattice_factor /\
     S.c_lat * N.of_nat (C.k + 1) <= lattice_factor /\
     (S.c_lat + 1) * N.of_nat (C.k + 1) * N.of_nat (C.k + 1) <= lattice_factor /\
     (S.c_lat + 1) * (c_disjunction + 1) * N.of_nat (C.k + 1) <= lattice_factor /\
     P.c_lat * (N.of_nat (S.size S.top) + 1) <= lattice_factor)%N.
  Proof.
    assert (Hcap : (1 <= N.of_nat (C.k + 1))%N) by lia.
    unfold lattice_factor; rewrite Nat2N.inj_mul.
    set (cap := N.of_nat (C.k + 1)) in *.
    assert (Hsquare : (cap <= cap * cap)%N) by nia.
    repeat split.
    - change (1 * 1 * 1 * 1 <=
        (P.c_lat + S.c_lat + 1) * (c_disjunction + 1) * (cap * cap) *
          (N.of_nat (S.size S.top) + 1))%N.
      apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono; lia | lia] | lia].
    - replace P.c_lat with (P.c_lat * 1 * 1 * 1)%N at 1 by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono; lia | lia] | lia].
    - replace (S.c_lat * cap)%N with (S.c_lat * 1 * cap * 1)%N by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono; lia | lia] | lia].
    - replace ((S.c_lat + 1) * cap * cap)%N with
        ((S.c_lat + 1) * 1 * (cap * cap) * 1)%N by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono; lia | lia] | lia].
    - replace ((S.c_lat + 1) * (c_disjunction + 1) * cap)%N with
        ((S.c_lat + 1) * (c_disjunction + 1) * cap * 1)%N at 1 by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono; lia | lia] | lia].
    - replace (P.c_lat * (N.of_nat (S.size S.top) + 1))%N with
        (P.c_lat * 1 * 1 * (N.of_nat (S.size S.top) + 1))%N at 1 by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono; lia | lia] | lia].
  Qed.

  (** The published widening measure includes all state and parameter work. *)
  Local Definition widen_measure p (a b : t) : nat :=
    ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1))%nat.

  (** One potential receiver's collapse and widening fit the combined input measure. *)
  Local Lemma receiver_clock : forall p a b x, In x (proj1_sig a) ->
    (T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) +
      S.T_widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))) <=
      6 * (S.c_lat + 1) * (c_disjunction + 1) * N.of_nat (widen_measure p a b))%N.
  Proof.
    intros p a b x Hin.
    destruct (receiver_budget a b x Hin) as [Hcap [Hsize Hunits]].
    destruct (member_measures a x Hin) as [Hxsize Hxunits].
    set (xs := x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in *.
    pose proof (T_collapse_le xs Hcap) as Hcollapse.
    pose proof (collapse_size xs Hcap) as Hresult_size.
    pose proof (collapse_wunits xs Hcap) as Hresult_units.
    set (budget := N.of_nat (widen_measure p a b)).
    assert (Hsize_budget : (N.of_nat (size a + size b + 1) <= budget)%N) by
      (unfold budget, widen_measure; lia).
    assert (Hparam : (N.of_nat (wsize p) <= budget)%N) by
      (unfold budget, widen_measure; lia).
    assert (Hpositive : (1 <= budget)%N) by (unfold budget, widen_measure; lia).
    assert (Hunit_budget : (N.of_nat (wunits a + wunits b + 1) *
      N.of_nat (wsize p) <= budget)%N).
    { clear -budget; unfold budget, widen_measure; repeat rewrite Nat2N.inj_add;
        repeat rewrite Nat2N.inj_mul; nia. }
    assert (Hcollapse_bound : (T_collapse xs <= c_disjunction * budget)%N).
    { eapply N.le_trans; [exact Hcollapse | apply N.mul_le_mono_l].
      eapply N.le_trans; [|exact Hsize_budget]; lia. }
    assert (Hsize_bound : (N.of_nat (S.size (collapse xs)) <= c_disjunction * budget)%N).
    { eapply N.le_trans; [exact Hresult_size | apply N.mul_le_mono_l].
      eapply N.le_trans; [|exact Hsize_budget]; lia. }
    assert (Hunits_bound : (N.of_nat (S.wunits (collapse xs)) <=
      c_disjunction * N.of_nat (wunits a + wunits b + 1))%N).
    { eapply N.le_trans; [exact Hresult_units | apply N.mul_le_mono_l]; lia. }
    assert (Hunit_sum : (N.of_nat (S.wunits x + S.wunits (collapse xs)) <=
      (c_disjunction + 1) * N.of_nat (wunits a + wunits b + 1))%N).
    { clear -Hunits_bound Hxunits; repeat rewrite Nat2N.inj_add in *; nia. }
    pose proof (N.mul_le_mono_r _ _ (N.of_nat (wsize p)) Hunit_sum) as Hunit_product.
    pose proof (N.mul_le_mono_l _ _ (c_disjunction + 1)%N Hunit_budget) as Hunit_paid.
    assert (Hinput : (N.of_nat ((S.wunits x + S.wunits (collapse xs)) * wsize p +
      (S.size x + S.size (collapse xs) + wsize p + 1)) <=
      4 * (c_disjunction + 1) * budget)%N).
    { clear -Hunit_product Hunit_paid Hxsize Hsize_bound Hsize_budget Hparam Hpositive;
      repeat rewrite Nat2N.inj_add in *; repeat rewrite Nat2N.inj_mul; nia. }
    pose proof (S.T_widen_le p x (collapse xs)) as Hwiden.
    pose proof (N.mul_le_mono_l _ _ S.c_lat Hinput) as Hscaled.
    change (S.wsize p) with (wsize p) in Hwiden.
    clear -Hcollapse_bound Hwiden Hscaled.
    nia.
  Qed.

  (** The cap turns all nested scans and receiver updates into a fixed factor. *)
  Local Lemma widen_budget_bound : forall p a b,
    (widen_budget p a b <= 16 * lattice_factor * N.of_nat (widen_measure p a b))%N.
  Proof.
    intros p a b.
    destruct lattice_factors as [Hfactor [Hshared [Hcomponent [Hscan [Hreceiver Htop]]]]].
    set (budget := N.of_nat (widen_measure p a b)).
    assert (Hpositive : (1 <= budget)%N) by (unfold budget, widen_measure; lia).
    assert (Hsizes : (N.of_nat (size a + size b + 1) <= budget)%N) by
      (unfold budget, widen_measure; lia).
    assert (Hcap_a : length (proj1_sig a) <= C.k) by
      (apply Nat.leb_le; exact (proj2_sig a)).
    assert (Hcap_b : length (proj1_sig b) <= C.k) by
      (apply Nat.leb_le; exact (proj2_sig b)).
    assert (Hcompare : (T_leb b a <= lattice_factor * budget)%N).
    { eapply N.le_trans; [apply P.T_leb_le |].
      apply N.mul_le_mono; [exact Hshared |].
      change (N.of_nat (size b + size a + 1) <= budget)%N.
      eapply N.le_trans; [|exact Hsizes]; lia. }
    assert (Hempty : (T_is_bot a <= lattice_factor * budget)%N).
    { eapply N.le_trans; [apply P.T_is_bot_le |].
      apply N.mul_le_mono; [exact Hshared |].
      change (N.of_nat (size a + 1) <= budget)%N.
      eapply N.le_trans; [|exact Hsizes]; lia. }
    assert (Hclip : (P.T_clip [S.top] <= 2 * lattice_factor * budget)%N).
    { assert (Hcap : length [S.top] <= 2 * C.k) by
        (cbn [length]; pose proof C.k_pos; lia).
      pose proof (P.T_clip_le [S.top] Hcap) as Hclock.
      cbn [length fold_right] in Hclock.
      assert (Hbase : (P.T_clip [S.top] <=
        2 * (P.c_lat * (N.of_nat (S.size S.top) + 1)))%N).
      { clear -Hclock; repeat rewrite Nat2N.inj_add in Hclock; nia. }
      clear -Hbase Htop Hpositive; nia. }
    assert (Hlength : (N.of_nat (length (proj1_sig a) + 1) <=
      lattice_factor * budget)%N).
    { assert (Hlen : (N.of_nat (length (proj1_sig a) + 1) <= budget)%N).
      { eapply N.le_trans; [|exact Hsizes].
        rewrite (size_mass a), state_mass_values; lia. }
      clear -Hlen Hfactor; nia. }
    assert (Hbottoms : (fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) <=
      lattice_factor * budget)%N).
    { pose proof (sum_uniform S.T_is_bot (proj1_sig a) (S.c_lat * budget)%N) as Hsum.
      assert (Hcalls : forall x, In x (proj1_sig a) ->
        (S.T_is_bot x <= S.c_lat * budget)%N).
      { intros x Hin; pose proof (proj1 (member_measures a x Hin)) as Hsize.
        eapply N.le_trans; [apply S.T_is_bot_le | apply N.mul_le_mono_l].
        eapply N.le_trans; [|exact Hsizes]; lia. }
      specialize (Hsum Hcalls).
      assert (Hcap_sum : (fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) <=
        N.of_nat (C.k + 1) * (S.c_lat * budget))%N).
      { eapply N.le_trans; [exact Hsum | apply N.mul_le_mono_r]; lia. }
      clear -Hcap_sum Hcomponent; nia. }
    assert (Hscans : (scan_work (proj1_sig a) (proj1_sig b) <=
      lattice_factor * budget)%N).
    { assert (Hcells : forall y x, In y (proj1_sig b) -> In x (proj1_sig a) ->
        (S.T_leb y x + 1 <= (S.c_lat + 1) * budget)%N).
      { intros y x Hy Hx.
        pose proof (proj1 (member_measures a x Hx)) as Hxsize.
        pose proof (proj1 (member_measures b y Hy)) as Hysize.
        assert (Hclock : (S.T_leb y x <= S.c_lat * budget)%N).
        { eapply N.le_trans; [apply S.T_leb_le | apply N.mul_le_mono_l].
          eapply N.le_trans; [|exact Hsizes]; lia. }
        clear -Hclock Hpositive; nia. }
      assert (Hrows : forall y, In y (proj1_sig b) ->
        (fold_right N.add 0%N (map (fun x => S.T_leb y x + 1)%N (proj1_sig a)) <=
          N.of_nat (C.k + 1) * ((S.c_lat + 1) * budget))%N).
      { intros y Hy; eapply N.le_trans.
        - apply sum_uniform; intros x Hx; exact (Hcells y x Hy Hx).
        - apply N.mul_le_mono_r; lia. }
      pose proof (sum_uniform
        (fun y => fold_right N.add 0%N (map (fun x => S.T_leb y x + 1)%N (proj1_sig a)))
        (proj1_sig b) (N.of_nat (C.k + 1) * ((S.c_lat + 1) * budget))%N Hrows) as Hsum.
      assert (Hcap_sum : (scan_work (proj1_sig a) (proj1_sig b) <=
        N.of_nat (C.k + 1) * (N.of_nat (C.k + 1) * ((S.c_lat + 1) * budget)))%N).
      { eapply N.le_trans; [exact Hsum | apply N.mul_le_mono_r]; lia. }
      clear -Hcap_sum Hscan; nia. }
    assert (Hreceivers : (fold_right N.add 0%N (map (fun x =>
      let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
      T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
      (proj1_sig a)) <= 6 * lattice_factor * budget)%N).
    { pose proof (sum_uniform (fun x =>
        let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
        T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)%N
        (proj1_sig a) (6 * (S.c_lat + 1) * (c_disjunction + 1) * budget)%N
        (receiver_clock p a b)) as Hsum.
      assert (Hcap_sum : (fold_right N.add 0%N (map (fun x =>
        let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
        T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
        (proj1_sig a)) <= N.of_nat (C.k + 1) *
        (6 * (S.c_lat + 1) * (c_disjunction + 1) * budget))%N).
      { eapply N.le_trans; [exact Hsum | apply N.mul_le_mono_r]; lia. }
      clear -Hcap_sum Hreceiver; nia. }
    unfold widen_budget.
    clear -Hcompare Hempty Hclip Hlength Hbottoms Hscans Hreceivers.
    cbv zeta in Hreceivers.
    nia.
  Qed.

  (** Assignment work is the component work of every alternative. *)
  Lemma assign_work_alternatives : forall x e d, assign_work x e d =
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  (** Havoc work is the component work of every alternative. *)
  Lemma havoc_work_alternatives : forall x d, havoc_work x d =
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  (** Assumption work is the component work of every alternative. *)
  Lemma assume_work_alternatives : forall g es d, assume_work g es d =
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  (** Evaluation work is the component work and the value size of every alternative. *)
  Lemma eval_work_alternatives : forall e d, eval_work e d =
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    exact (proj1 lattice_coefficient).
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; eapply N.le_trans; [apply P.T_leb_le |].
    apply N.mul_le_mono_r; exact (proj2 lattice_coefficient).
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; eapply N.le_trans; [apply P.T_join_le |].
    apply N.mul_le_mono_r; exact (proj2 lattice_coefficient).
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intro a; eapply N.le_trans; [apply P.T_is_bot_le |].
    apply N.mul_le_mono_r; exact (proj2 lattice_coefficient).
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b; pose proof (widen_clock p a b) as Hclock.
    pose proof (widen_budget_bound p a b) as Hbudget.
    pose proof (N.mul_le_mono_l _ _ k_disjunction Hbudget) as Hscaled.
    assert (Hcoefficient : c_lat = (64 * lattice_factor * (k_disjunction + 1))%N).
    { unfold c_lat, lattice_factor; ring. }
    rewrite Hcoefficient; change (N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1))) with
      (N.of_nat (widen_measure p a b)).
    nia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; pose proof c_lat_pos; time_unfold @T_narrow; nia.
  Qed.
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof.
    intros x e [xs Hbound].
    pose proof (ValueJoins.sum_cost (fun s => S.T_assign x e s + 1)%N
      (fun s => S.assign_work x e s + 1)%nat (S.c_state + 1)%N xs) as Hsum.
    assert (Hcalls : forall s, In s xs ->
      (S.T_assign x e s + 1 <= (S.c_state + 1) * N.of_nat (S.assign_work x e s + 1))%N).
    { intros s Hin; pose proof (S.T_assign_le x e s); nia. }
    specialize (Hsum Hcalls).
    time_unfold @T_assign; time_unfold @T_map_bounded.
    cbn [proj1_sig]; rewrite ValueJoins.map_clock.
    unfold c_state, assign_work; cbn [proj1_sig]; rewrite Nat2N.inj_add; nia.
  Qed.
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x [xs Hbound].
    pose proof (ValueJoins.sum_cost (fun s => S.T_havoc x s + 1)%N
      (fun s => S.havoc_work x s + 1)%nat (S.c_state + 1)%N xs) as Hsum.
    assert (Hcalls : forall s, In s xs ->
      (S.T_havoc x s + 1 <= (S.c_state + 1) * N.of_nat (S.havoc_work x s + 1))%N).
    { intros s Hin; pose proof (S.T_havoc_le x s); nia. }
    specialize (Hsum Hcalls).
    time_unfold @T_havoc; time_unfold @T_map_bounded.
    cbn [proj1_sig]; rewrite ValueJoins.map_clock.
    unfold c_state, havoc_work; cbn [proj1_sig]; rewrite Nat2N.inj_add; nia.
  Qed.
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es [xs Hbound].
    pose proof (ValueJoins.sum_cost (fun s => S.T_assume g es s + 1)%N
      (fun s => S.assume_work g es s + 1)%nat (S.c_state + 1)%N xs) as Hsum.
    assert (Hcalls : forall s, In s xs ->
      (S.T_assume g es s + 1 <= (S.c_state + 1) * N.of_nat (S.assume_work g es s + 1))%N).
    { intros s Hin; pose proof (S.T_assume_le g es s); nia. }
    specialize (Hsum Hcalls).
    time_unfold @T_assume; time_unfold @T_map_bounded.
    cbn [proj1_sig]; rewrite ValueJoins.map_clock.
    unfold c_state, assume_work; cbn [proj1_sig]; rewrite Nat2N.inj_add; nia.
  Qed.
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof.
    intros e [xs Hbound]; assert (Hcap : length xs <= C.k) by now apply Nat.leb_le.
    pose proof (ValueJoins.sum_cost (fun s => S.T_eval e s + 1)%N
      (fun s => S.eval_work e s + V.size (S.eval e s) + 1)%nat
      (S.c_state + 1)%N xs) as Hsum.
    assert (Hcalls : forall s, In s xs -> (S.T_eval e s + 1 <=
      (S.c_state + 1) * N.of_nat (S.eval_work e s + V.size (S.eval e s) + 1))%N).
    { intros s Hin; pose proof (S.T_eval_le e s); repeat rewrite Nat2N.inj_add in *; nia. }
    specialize (Hsum Hcalls).
    pose proof (ValueJoins.joins_capped (S.eval e) xs Hcap) as Hjoins.
    pose proof (evaluation_sizes e xs) as Hsizes.
    rewrite eval_clock; unfold eval_work, eval_joins, k_disjunction in *; cbn [proj1_sig].
    unfold c_state, k_disjunction; repeat rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_assign_alternatives : forall x e d,
    (T_assign x e d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_assign x e s + 1) (proj1_sig d)) + 1))%N.
  Proof.
    intros x e [xs Hbound]; pose proof (proj1 coefficients_positive).
    time_unfold @T_assign; time_unfold @T_map_bounded; cbn [proj1_sig].
    rewrite ValueJoins.map_clock; nia.
  Qed.
  Lemma T_havoc_alternatives : forall x d,
    (T_havoc x d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_havoc x s + 1) (proj1_sig d)) + 1))%N.
  Proof.
    intros x [xs Hbound]; pose proof (proj1 coefficients_positive).
    time_unfold @T_havoc; time_unfold @T_map_bounded; cbn [proj1_sig].
    rewrite ValueJoins.map_clock; nia.
  Qed.
  Lemma T_assume_alternatives : forall g es d,
    (T_assume g es d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_assume g es s + 1) (proj1_sig d)) + 1))%N.
  Proof.
    intros g es [xs Hbound]; pose proof (proj1 coefficients_positive).
    time_unfold @T_assume; time_unfold @T_map_bounded; cbn [proj1_sig].
    rewrite ValueJoins.map_clock; nia.
  Qed.
  Lemma c_lat_shared : (P.c_lat <= c_lat)%N.
  Proof.
    exact (proj2 lattice_coefficient).
  Qed.
  Lemma wunits_alternatives : forall d,
    wunits d = fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  Lemma widen_bigO : bigO (X := wparam * t * t) (fun _ => True)
    (fun '(p, a, b) => N.of_nat ((wunits a + wunits b) * wsize p + (size a + size b + wsize p)))
    (fun '(p, a, b) => T_widen p a b).
  Proof. Admitted. (* STUB *)
  Lemma narrow_bigO : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_narrow (fst ab) (snd ab)).
  Proof. Admitted. (* STUB *)
  Lemma assign_bigO : bigO (X := X.t * term L.op X.t * t) (fun _ => True)
    (fun '(x, e, d) => N.of_nat (assign_work x e d)) (fun '(x, e, d) => T_assign x e d).
  Proof. Admitted. (* STUB *)
  Lemma havoc_bigO : bigO (X := X.t * t) (fun _ => True)
    (fun '(x, d) => N.of_nat (havoc_work x d)) (fun '(x, d) => T_havoc x d).
  Proof. Admitted. (* STUB *)
  Lemma assume_bigO : bigO (X := L.guard * list (term L.op X.t) * t) (fun _ => True)
    (fun '(gd, es, d) => N.of_nat (assume_work gd es d)) (fun '(gd, es, d) => T_assume gd es d).
  Proof. Admitted. (* STUB *)
  Lemma eval_bigO : bigO (X := term L.op X.t * t) (fun _ => True)
    (fun '(e, d) => N.of_nat (eval_work e d)) (fun '(e, d) => T_eval e d).
  Proof. Admitted. (* STUB *)
  Lemma collapse_bigO : bigO (fun xs : list S.t => length xs <= C.k + 1)
    (fun xs => N.of_nat (fold_right Nat.add 0%nat (map S.size xs) + length xs)) T_collapse.
  Proof. Admitted. (* STUB *)
  Lemma wsize_component : forall p, wsize p = S.wsize p.
  Proof.
    reflexivity.
  Qed.
  Lemma F2_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    if forallb S.is_bot (proj1_sig a) then [S.top] else
    replace_first S.is_bot
      (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))))
      (proj1_sig a).
  Proof.
    exact widen_raw.
  Qed.
  Lemma F3_rank : forall p d, wrank p d =
    fold_right Nat.add 0%nat (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.
  Proof.
    reflexivity.
  Qed.
  Lemma F4_assign : forall x e d,
    proj1_sig (assign x e d) = map (S.assign x e) (proj1_sig d).
  Proof.
    intros x e [xs Hbound]; reflexivity.
  Qed.
  Lemma F5_havoc : forall x d,
    proj1_sig (havoc x d) = map (S.havoc x) (proj1_sig d).
  Proof.
    intros x [xs Hbound]; reflexivity.
  Qed.
  Lemma F6_assume : forall g es d,
    proj1_sig (assume g es d) = map (S.assume g es) (proj1_sig d).
  Proof.
    intros g es [xs Hbound]; reflexivity.
  Qed.
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_disjunction *
      (T_leb b a + T_is_bot a + P.T_clip [S.top] + N.of_nat (length (proj1_sig a) + 1) +
       fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) +
       fold_right N.add 0%N (map (fun y => fold_right N.add 0%N
         (map (fun x => S.T_leb y x + 1) (proj1_sig a))) (proj1_sig b)) +
       fold_right N.add 0%N (map (fun x =>
         let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
         T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
         (proj1_sig a))))%N.
  Proof.
    exact widen_clock.
  Qed.
  (** Evaluation joins the values of the alternatives from bottom. *)
  Lemma F7_eval : forall e d,
    eval e d = fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
  Proof.
    reflexivity.
  Qed.
  (** Evaluation charges each alternative's evaluation and the value joins. *)
  Lemma T2_eval : forall e d, (T_eval e d <= k_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_eval e s + 1) (proj1_sig d)) +
     eval_joins e (proj1_sig d) + 1))%N.
  Proof.
    intros e d; rewrite eval_clock; pose proof (proj2 coefficients_positive); nia.
  Qed.
  (** The value joins of a capped list charge the sizes of the evaluated values. *)
  Lemma T3_eval_joins : forall e xs, length xs <= C.k ->
    (eval_joins e xs <= k_disjunction * N.of_nat (fold_right Nat.add 0%nat
      (map (fun s => (V.size (S.eval e s) + 1)%nat) xs) + 1))%N.
  Proof.
    intros e xs Hcap; exact (ValueJoins.joins_capped (S.eval e) xs Hcap).
  Qed.
End StateDisjunctionT.

(* The landed lattice source exposed the following raw-list equations. The shared
   bounded carrier now supplies P.clip. Its laws allow different oversized-list
   covers, so the exact raw suffix equation is not implied by the reviewed P.
Theorem compact_equation {A} k (L : lattice A) xs :
  compact k L xs =
    if Nat.leb (length xs) k then xs
    else firstn (k - 1) xs ++ [join_all L (skipn (k - 1) xs)].

   The state widening grows the first nonbottom alternative using uncovered candidates.
   The landed lattice widening used a single collapse and its equation is a different claim.
Theorem widen_disjunction {A} k (L : lattice A) xs ys :
  widen (disjunction k L) xs ys =
    if disjunction_leb L ys xs then xs
    else [widen L (join_all L xs) (join_all L (xs ++ ys))].

   The old selective-join and invariant-based rank bundles used lattice_laws,
   lub_laws, concretisation_laws and widening_rank_on records, which are no longer
   the shared bounded component interface. Their original claims were:
Theorem disjunction_lub k :
  (forall a b, leb L (join L a b) a = true \/ leb L (join L a b) b = true) ->
  lub_laws (disjunction k L).
Theorem monotone_join_all {A} (L : lattice A) xs ys :
  lattice_laws L -> lub_laws L ->
  Forall2 (fun x y => leb L x y = true) xs ys ->
  leb L (join_all L xs) (join_all L ys) = true.
Theorem disjunction_gamma_laws {A C} k (L : lattice A) (G : concretisation A C) :
  concretisation_laws L G ->
  concretisation_laws (disjunction k L) (disjunction_gamma G).
Theorem disjunction_bot_empty {A C} k (L : lattice A) (G : concretisation A C) :
  bottom_empty (disjunction k L) (disjunction_gamma G).
Theorem disjunction_wrank k : widening_rank_on (disjunction k L) (Forall inv).
*)

(* The landed cost statements below refer to the removed Cost monad and raw-list
   lattice. The later timing part derives clocks for the reviewed bounded carrier.
Theorem compact_ticks k xs :
  Cost.ticks (compact_c k L xs) =
    (N.of_nat (length xs) + 1 +
      if Nat.leb (length xs) k then 0 else
        Cost.ticks (compact_tail_c (k - 1) L xs))%N.
Theorem disjunction_cost_bounded k m :
  cost_bounded_on (disjunction k L) (fun xs => Forall inv xs /\ length xs <= m)
    (((2 * N.of_nat m + 1) * (2 * N.of_nat m + 1)) * (c + 6))%N.
Theorem disjunction_cost_bigO {X} k (xs ys : X -> list A) :
  (forall x, Forall inv (xs x)) -> (forall x, Forall inv (ys x)) ->
  bigO
    (fun x => let n := (N.of_nat (length (xs x)) + N.of_nat (length (ys x)) + 1)%N in
      (n * n)%N)
    (fun x =>
      (Cost.ticks (leb_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (join_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (widen_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (narrow_c (disjunction k L) (xs x) (ys x)))%N).
*)

Module StateDisjunctionClaims (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (P : SharedDisjunction.DISJUNCTION S C).
  Include StateDisjunction X L V S C P.

  Theorem join_all_equation xs :
    collapse xs = match xs with [] => S.bot | x :: rest => fold_left S.join rest x end.
  Proof. destruct xs; reflexivity. Qed.

  Theorem disjunction_leb_equation a b : leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  Proof.
    apply leb_hoare.
  Qed.

  Theorem disjunction_leb_spec a b : leb a b = true <->
    forall x, In x (proj1_sig a) ->
      exists y, In y (proj1_sig b) /\ S.leb x y = true.
Proof.
  rewrite disjunction_leb_equation, forallb_forall.
  split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
Qed.

  Theorem join_disjunction a b : join a b = P.clip (proj1_sig a ++ proj1_sig b).
  Proof.
    apply join_compact.
  Qed.

  Theorem disjunction_join_size a b : length (proj1_sig (join a b)) <= C.k.
  Proof.
    apply Nat.leb_le; exact (proj2_sig (join a b)).
  Qed.

  Theorem join_all_upper xs x : In x xs -> S.leb x (collapse xs) = true.
  Proof.
    apply collapse_covers.
  Qed.
End StateDisjunctionClaims.

(* The old fold equation named a charged helper whose pure value is now collapse.
Theorem fold_join_equation {A} (L : lattice A) xs a :
  Cost.value (fold_join_c L xs a) = fold_left (join L) xs a.

   The old closure statements quantified over closed_on and lattice_laws record
   bundles. The reviewed bounded state interface supplies neither such invariant
   provider nor its preservation contract for an arbitrary P.clip.
Theorem join_all_closed xs : Forall inv xs -> inv (join_all L xs).
Theorem disjunction_closed k : closed_on (disjunction k L) (Forall inv).
Theorem disjunction_laws k : lattice_laws (disjunction k L).
*)
