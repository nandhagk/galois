(** * Fixed-budget integer interval operations

    Raw results are normalized and cut outward before entering the carrier.
    For example, a large upper endpoint becomes positive infinity.
    Builds on: CutIntervalSig and the shared interval operations. *)

From Stdlib Require Import List ZArith NArith Bool Lia Eqdep_dec.
From Argent Require Import Time Tactics Std.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig CutIntervalSig Interval.

Definition pack_cut (bits : nat) (raw : itv) : cut_itv bits :=
  match cut_interval_ok bits raw as ok return cut_interval_ok bits raw = ok -> cut_itv bits with
  | true => fun proof => exist _ raw proof
  | false => fun _ => exist _ IBot eq_refl
  end eq_refl.
TimeFun pack_cut.

(** Endpoint membership is shared by raw and bounded intervals. *)
Definition cut_member (a : itv) (z : Z) : Prop :=
  match a with IBot => False | I lo hi => in_bnd lo hi z end.

(** Reflected endpoint order is reflexive. *)
Lemma cut_bound_refl : forall b, cut_bound_leb b b = true.
Proof.
  intros [|z|]; cbn [cut_bound_leb]; try reflexivity; apply Z.leb_refl.
Qed.

(** Reflected endpoint order is transitive. *)
Lemma cut_bound_trans : forall a b c,
  cut_bound_leb a b = true -> cut_bound_leb b c = true ->
  cut_bound_leb a c = true.
Proof.
  intros [|a|] [|b|] [|c|]; cbn [cut_bound_leb];
    intros Hab Hbc; try discriminate; try reflexivity.
  apply Z.leb_le in Hab, Hbc. apply Z.leb_le. lia.
Qed.

(** Finite endpoint comparisons express inclusive interval membership. *)
Lemma cut_bound_order : forall lo hi z,
  in_bnd lo hi z <->
    cut_bound_leb lo (Fin z) = true /\ cut_bound_leb (Fin z) hi = true.
Proof.
  intros [|lo|] [|hi|] z; unfold in_bnd; cbn [cut_bound_leb];
    rewrite ?Z.leb_le; intuition congruence.
Qed.

(** Raw endpoint inclusion retains every represented integer. *)
Lemma cut_member_mono : forall a b z,
  cut_leb a b = true -> cut_member a z -> cut_member b z.
Proof.
  intros [|lo hi] [|lo' hi'] z Hle Hmember;
    cbn [cut_leb cut_member] in *; try contradiction; try discriminate.
  apply andb_true_iff in Hle as [Hlo Hhi].
  apply cut_bound_order in Hmember as [Hlower Hupper].
  apply cut_bound_order. split; eapply cut_bound_trans; eassumption.
Qed.

(** An interval with a represented integer has a normalized nonempty shape. *)
Lemma cut_member_shape : forall a z, cut_member a z -> cut_shape_ok a = true.
Proof.
  intros [|[|lo|] [|hi|]] z Hmember;
    cbv [cut_member cut_shape_ok in_bnd] in *; intuition try congruence.
  apply Z.leb_le. lia.
Qed.

(** Every normalized nonbottom interval contains an integer. *)
Lemma cut_shape_member : forall lo hi,
  cut_shape_ok (I lo hi) = true -> exists z, in_bnd lo hi z.
Proof.
  intros [|lo|] [|hi|] Hshape; cbn [cut_shape_ok] in Hshape;
    try discriminate.
  - exists hi. unfold in_bnd. intuition lia.
  - exists 0%Z. unfold in_bnd. intuition.
  - exists lo. apply Z.leb_le in Hshape. unfold in_bnd. intuition lia.
  - exists lo. unfold in_bnd. intuition lia.
Qed.

(** A normalized interval has ordered endpoints. *)
Lemma cut_shape_order : forall lo hi,
  cut_shape_ok (I lo hi) = true -> cut_bound_leb lo hi = true.
Proof.
  intros [|lo|] [|hi|]; cbn [cut_shape_ok cut_bound_leb];
    intros Hshape; try discriminate; try reflexivity; exact Hshape.
Qed.

(** The Boolean carrier check is exactly shape validity and the endpoint budget. *)
Lemma cut_valid_parts : forall bits a,
  cut_interval_ok bits a = true <->
    cut_shape_ok a = true /\ interval_bits a <= bits.
Proof.
  intros bits [|[|lo|] [|hi|]];
    cbn [cut_interval_ok cut_shape_ok cut_endpoint_ok interval_bits];
    rewrite ?andb_true_iff, ?Nat.leb_le, ?Nat.max_lub_iff; intuition (try congruence; lia).
Qed.

(** A finite greatest lower endpoint comes from one of the two checked endpoints. *)
Lemma cut_lower_endpoint_valid : forall bits a b z,
  cut_endpoint_ok bits a = true -> cut_endpoint_ok bits b = true ->
  cut_bound_leb a (Fin z) = true -> cut_bound_leb b (Fin z) = true ->
  (forall x, cut_bound_leb a (Fin x) = true -> cut_bound_leb b (Fin x) = true ->
    (x <= z)%Z -> (z <= x)%Z) -> cut_endpoint_ok bits (Fin z) = true.
Proof.
  intros bits [|a|] [|b|] z Ha Hb Haz Hbz Hgreatest;
    cbn [cut_endpoint_ok cut_bound_leb] in *; try discriminate.
  - assert (Hminus : (z - 1 <= z)%Z) by lia.
    specialize (Hgreatest (z - 1)%Z eq_refl eq_refl Hminus). lia.
  - apply Z.leb_le in Hbz.
    specialize (Hgreatest b eq_refl (Z.leb_refl b) Hbz).
    assert (z = b) by lia. now subst z.
  - apply Z.leb_le in Haz.
    specialize (Hgreatest a (Z.leb_refl a) eq_refl Haz).
    assert (z = a) by lia. now subst z.
  - apply Z.leb_le in Haz, Hbz. destruct (Z_le_dec a b) as [Hab | Hba].
    + assert (Hab' : (a <=? b)%Z = true) by (apply Z.leb_le; exact Hab).
      specialize (Hgreatest b Hab' (Z.leb_refl b) Hbz).
      assert (z = b) by lia. now subst z.
    + assert (Hba' : (b <=? a)%Z = true) by (apply Z.leb_le; lia).
      specialize (Hgreatest a (Z.leb_refl a) Hba' Haz).
      assert (z = a) by lia. now subst z.
Qed.

(** A finite least upper endpoint comes from one of the two checked endpoints. *)
Lemma cut_upper_endpoint_valid : forall bits a b z,
  cut_endpoint_ok bits a = true -> cut_endpoint_ok bits b = true ->
  cut_bound_leb (Fin z) a = true -> cut_bound_leb (Fin z) b = true ->
  (forall x, cut_bound_leb (Fin x) a = true -> cut_bound_leb (Fin x) b = true ->
    (z <= x)%Z -> (x <= z)%Z) -> cut_endpoint_ok bits (Fin z) = true.
Proof.
  intros bits [|a|] [|b|] z Ha Hb Hza Hzb Hleast;
    cbn [cut_endpoint_ok cut_bound_leb] in *; try discriminate.
  - apply Z.leb_le in Hza, Hzb. destruct (Z_le_dec a b) as [Hab | Hba].
    + assert (Hab' : (a <=? b)%Z = true) by (apply Z.leb_le; exact Hab).
      specialize (Hleast a (Z.leb_refl a) Hab' Hza).
      assert (z = a) by lia. now subst z.
    + assert (Hba' : (b <=? a)%Z = true) by (apply Z.leb_le; lia).
      specialize (Hleast b Hba' (Z.leb_refl b) Hzb).
      assert (z = b) by lia. now subst z.
  - apply Z.leb_le in Hza.
    specialize (Hleast a (Z.leb_refl a) eq_refl Hza).
    assert (z = a) by lia. now subst z.
  - apply Z.leb_le in Hzb.
    specialize (Hleast b eq_refl (Z.leb_refl b) Hzb).
    assert (z = b) by lia. now subst z.
  - assert (Hplus : (z <= z + 1)%Z) by lia.
    specialize (Hleast (z + 1)%Z eq_refl eq_refl Hplus). lia.
Qed.

(** Any nonempty interval denoting the exact intersection retains the endpoint budget. *)
Lemma cut_meet_valid : forall bits a b m,
  cut_interval_ok bits a = true -> cut_interval_ok bits b = true ->
  cut_leb m a = true -> cut_leb m b = true ->
  (forall z, cut_member a z -> cut_member b z -> cut_member m z) ->
  cut_shape_ok m = true -> cut_interval_ok bits m = true.
Proof.
  intros bits [|alo ahi] [|blo bhi] [|lo hi] Ha Hb Hma Hmb Hmeet Hshape;
    try reflexivity; try discriminate.
  apply andb_true_iff in Hma as [HloA HhiA].
  apply andb_true_iff in Hmb as [HloB HhiB].
  unfold cut_interval_ok in Ha, Hb |- *.
  apply andb_true_iff in Ha as [_ Ha]. apply andb_true_iff in Ha as [Halo Hahi].
  apply andb_true_iff in Hb as [_ Hb]. apply andb_true_iff in Hb as [Hblo Hbhi].
  rewrite Hshape. cbn [andb]. apply andb_true_iff.
  pose proof (cut_shape_order lo hi Hshape) as Horder. split.
  - destruct lo as [|z|]; [reflexivity | | discriminate].
    eapply cut_lower_endpoint_valid; [exact Halo | exact Hblo | exact HloA | exact HloB |].
    intros x Hax Hbx Hxz.
    assert (Hxh : cut_bound_leb (Fin x) hi = true).
    { eapply cut_bound_trans with (b := Fin z);
        [change ((x <=? z)%Z = true); apply Z.leb_le; exact Hxz |].
      exact Horder. }
    assert (Hxa : cut_member (I alo ahi) x).
    { apply cut_bound_order. split; [exact Hax |].
      eapply cut_bound_trans; eassumption. }
    assert (Hxb : cut_member (I blo bhi) x).
    { apply cut_bound_order. split; [exact Hbx |].
      eapply cut_bound_trans; eassumption. }
    specialize (Hmeet x Hxa Hxb). apply cut_bound_order in Hmeet as [Hzx _].
    now apply Z.leb_le in Hzx.
  - destruct hi as [|z|]; [destruct lo; discriminate | | reflexivity].
    eapply cut_upper_endpoint_valid; [exact Hahi | exact Hbhi | exact HhiA | exact HhiB |].
    intros x Hxa Hxb Hzx.
    assert (Hlx : cut_bound_leb lo (Fin x) = true).
    { eapply cut_bound_trans; [exact Horder |].
      change ((z <=? x)%Z = true). now apply Z.leb_le. }
    assert (Hax : cut_member (I alo ahi) x).
    { apply cut_bound_order. split; [|exact Hxa].
      eapply cut_bound_trans; eassumption. }
    assert (Hbx : cut_member (I blo bhi) x).
    { apply cut_bound_order. split; [|exact Hxb].
      eapply cut_bound_trans; eassumption. }
    specialize (Hmeet x Hax Hbx). apply cut_bound_order in Hmeet as [_ Hxz].
    now apply Z.leb_le in Hxz.
Qed.

(** The projected value retains its Boolean subtype invariant. *)
Lemma cut_raw_valid : forall bits (a : cut_itv bits),
  cut_interval_ok bits (cut_raw a) = true.
Proof.
  intros bits [a Hvalid]. exact Hvalid.
Qed.

(** Packing chooses the checked representation or the canonical empty interval. *)
Lemma pack_cut_choice : forall bits a,
  cut_raw (pack_cut bits a) = if cut_interval_ok bits a then a else IBot.
Proof.
  intros bits a.
  assert (Hchoice : forall (ok : bool) (Hok : cut_interval_ok bits a = ok),
    cut_raw
      ((match ok as checked return cut_interval_ok bits a = checked -> cut_itv bits with
        | true => fun proof => exist _ a proof
        | false => fun _ => exist _ IBot eq_refl
        end) Hok) = if ok then a else IBot).
  { intros [] Hok; reflexivity. }
  exact (Hchoice (cut_interval_ok bits a) eq_refl).
Qed.

(** Packing a checked representation keeps that representation. *)
Lemma pack_cut_agrees : forall bits a,
  cut_interval_ok bits a = true -> cut_raw (pack_cut bits a) = a.
Proof.
  intros bits a Hvalid. now rewrite pack_cut_choice, Hvalid.
Qed.

(** Boolean proof fields do not distinguish two copies of the same interval. *)
Lemma cut_raw_injective : forall bits (a b : cut_itv bits),
  cut_raw a = cut_raw b -> a = b.
Proof.
  intros bits [a Ha] [b Hb] Heq. cbn [cut_raw] in Heq. subst b.
  f_equal. apply UIP_dec. decide equality.
Qed.

(** Outward cutting preserves every integer in the raw interval. *)
Lemma cut_interval_sound : forall bits a z,
  cut_member a z -> cut_member (cut_interval bits a) z.
Proof.
  intros bits a z Hmember.
  pose proof (cut_member_shape a z Hmember) as Hshape.
  unfold cut_interval. rewrite Hshape.
  destruct a as [|lo hi]; [contradiction |].
  cbn [cut_member] in *. apply cut_bound_order in Hmember as [Hlo Hhi].
  apply cut_bound_order. unfold cut_lower, cut_upper. split.
  - destruct (cut_endpoint_ok bits lo); [exact Hlo | reflexivity].
  - destruct (cut_endpoint_ok bits hi); [exact Hhi | reflexivity].
Qed.

(** Every outward-cut interval passes its carrier check. *)
Lemma cut_interval_valid : forall bits a,
  cut_interval_ok bits (cut_interval bits a) = true.
Proof.
  intros bits a. unfold cut_interval.
  destruct (cut_shape_ok a) eqn:Hshape; [|reflexivity].
  destruct a as [|lo hi]; [reflexivity |].
  assert (Hnew : cut_shape_ok (I (cut_lower bits lo) (cut_upper bits hi)) = true).
  { destruct (cut_shape_member lo hi Hshape) as [z Hz].
    pose proof (cut_interval_sound bits (I lo hi) z Hz) as Hmember.
    unfold cut_interval in Hmember. rewrite Hshape in Hmember.
    exact (cut_member_shape _ z Hmember). }
  unfold cut_interval_ok. rewrite Hnew. cbn [andb]. apply andb_true_iff. split.
  - unfold cut_lower. destruct (cut_endpoint_ok bits lo) eqn:Hlo;
      [exact Hlo | reflexivity].
  - unfold cut_upper. destruct (cut_endpoint_ok bits hi) eqn:Hhi;
      [exact Hhi | reflexivity].
Qed.

(** Cutting a checked interval is the identity. *)
Lemma cut_interval_fixed : forall bits a,
  cut_interval_ok bits a = true -> cut_interval bits a = a.
Proof.
  intros bits [|lo hi] Hvalid; [reflexivity |].
  unfold cut_interval_ok in Hvalid.
  apply andb_true_iff in Hvalid as [Hshape Hendpoints].
  apply andb_true_iff in Hendpoints as [Hlo Hhi].
  unfold cut_interval, cut_lower, cut_upper. now rewrite Hshape, Hlo, Hhi.
Qed.

(** A small raw interval is changed only when its shape is empty. *)
Lemma cut_interval_small : forall bits a,
  interval_bits a <= bits ->
  cut_interval bits a = if cut_shape_ok a then a else IBot.
Proof.
  intros bits a Hbits. destruct (cut_shape_ok a) eqn:Hshape.
  - apply cut_interval_fixed, cut_valid_parts. split; assumption.
  - unfold cut_interval. now rewrite Hshape.
Qed.

(** A normalized lower operand remains below an outward-cut upper operand. *)
Lemma cut_interval_upper : forall bits old a,
  cut_shape_ok old = true -> cut_leb old a = true ->
  cut_leb old (cut_interval bits a) = true.
Proof.
  intros bits [|lo hi] a Hshape Hle; [reflexivity |].
  destruct (cut_shape_member lo hi Hshape) as [z Hz].
  pose proof (cut_member_mono (I lo hi) a z Hle Hz) as Ha.
  pose proof (cut_member_shape a z Ha) as Hshapea.
  unfold cut_interval. rewrite Hshapea.
  destruct a as [|alo ahi]; [discriminate |].
  cbn [cut_leb] in Hle |- *. apply andb_true_iff in Hle as [Hlo Hhi].
  apply andb_true_iff. unfold cut_lower, cut_upper. split.
  - destruct (cut_endpoint_ok bits alo); [exact Hlo | reflexivity].
  - destruct (cut_endpoint_ok bits ahi); [exact Hhi | destruct hi; reflexivity].
Qed.

(** Inward cutoff remains below the original operand. *)
Lemma cut_within_refines : forall bits old a,
  cut_leb a old = true -> cut_leb (cut_within bits old a) old = true.
Proof.
  intros bits old a Hle. unfold cut_within.
  destruct (cut_shape_ok a); [|reflexivity].
  destruct a as [|lo hi], old as [|olo ohi]; cbn [cut_leb] in *;
    try discriminate; try reflexivity.
  apply andb_true_iff in Hle as [Hlo Hhi]. apply andb_true_iff. split.
  - destruct (cut_endpoint_ok bits lo); [exact Hlo | apply cut_bound_refl].
  - destruct (cut_endpoint_ok bits hi); [exact Hhi | apply cut_bound_refl].
Qed.

(** Inward cutoff preserves integers represented by both its arguments. *)
Lemma cut_within_sound : forall bits old a z,
  cut_member old z -> cut_member a z -> cut_member (cut_within bits old a) z.
Proof.
  intros bits old a z Hold Ha.
  pose proof (cut_member_shape a z Ha) as Hshape.
  unfold cut_within. rewrite Hshape.
  destruct old as [|olo ohi], a as [|lo hi]; try contradiction.
  cbn [cut_member] in *. apply cut_bound_order in Hold as [Holo Hohi].
  apply cut_bound_order in Ha as [Hlo Hhi]. apply cut_bound_order. split.
  - destruct (cut_endpoint_ok bits lo); assumption.
  - destruct (cut_endpoint_ok bits hi); assumption.
Qed.

(** Inward cutoff produces a checked interval when refining a checked operand. *)
Lemma cut_within_valid : forall bits old a,
  cut_interval_ok bits old = true -> cut_leb a old = true ->
  cut_interval_ok bits (cut_within bits old a) = true.
Proof.
  intros bits old a Hvalid Hle. unfold cut_within.
  destruct (cut_shape_ok a) eqn:Hshape; [|reflexivity].
  destruct a as [|lo hi], old as [|olo ohi]; try reflexivity.
  assert (Hnew : cut_shape_ok
    (I (if cut_endpoint_ok bits lo then lo else olo)
       (if cut_endpoint_ok bits hi then hi else ohi)) = true).
  { destruct (cut_shape_member lo hi Hshape) as [z Hz].
    pose proof (cut_member_mono (I lo hi) (I olo ohi) z Hle Hz) as Hold.
    pose proof (cut_within_sound bits (I olo ohi) (I lo hi) z Hold Hz) as Hmember.
    unfold cut_within in Hmember. rewrite Hshape in Hmember.
    exact (cut_member_shape _ z Hmember). }
  unfold cut_interval_ok in Hvalid |- *.
  apply andb_true_iff in Hvalid as [_ Hendpoints].
  apply andb_true_iff in Hendpoints as [Holo Hohi].
  rewrite Hnew. cbn [andb]. apply andb_true_iff. split.
  - destruct (cut_endpoint_ok bits lo) eqn:Hlo; assumption.
  - destruct (cut_endpoint_ok bits hi) eqn:Hhi; assumption.
Qed.

Module CutIntervalCode (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_OPS)
    (T : THRESHOLDS_OPS) (R : INTERVAL_OPS L T) <: CUT_INTERVAL_OPS C L.
  Definition t := cut_itv C.bits.
  Definition wparam := ttree.

  Definition cut (a : itv) : t :=
    pack_cut C.bits (cut_interval C.bits a).

  Definition bot : t := exist _ IBot eq_refl.
  Definition top : t := exist _ (I NegInf PosInf) eq_refl.
  Definition leb (a b : t) := R.leb (cut_raw a) (cut_raw b).
  Definition is_bot (a : t) := R.is_bot (cut_raw a).
  Definition join (a b : t) := cut (R.join (cut_raw a) (cut_raw b)).
  Definition meet (a b : t) := cut (R.meet (cut_raw a) (cut_raw b)).
  Definition widen q (a b : t) := cut (R.widen q (cut_raw a) (cut_raw b)).
  Definition narrow (a b : t) := cut (R.narrow (cut_raw a) (cut_raw b)).
  Definition forward o (xs : list t) := cut (R.forward o (map cut_raw xs)).
  Definition backward o (r : t) (xs : list t) :=
    map (fun yx => pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))
      (combine (R.backward o (cut_raw r) (map cut_raw xs)) (map cut_raw xs)).
  Definition guard g (xs : list t) :=
    map (fun yx => pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))
      (combine (R.guard g (map cut_raw xs)) (map cut_raw xs)).
End CutIntervalCode.

Module CutInterval (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE)
    (T : THRESHOLDS) (R : INTERVAL L T) (RL : CUT_RAW_LINK_LAWS L T R) <: CUT_INTERVAL C L.
  Include CutIntervalCode C L T R.
  Include CUT_INTERVAL_SPEC C L.
  Definition gamma := in_cut.
  Definition wrank q (a : t) := R.interval_wrank q (cut_raw a).

  (** Cutting stores exactly the total outward-cut representation. *)
  Lemma cut_agrees : forall a, cut_raw (cut a) = cut_interval C.bits a.
  Proof.
    intro a. apply pack_cut_agrees, cut_interval_valid.
  Qed.

  (** Every carrier value has a normalized shape and bounded endpoints. *)
  Lemma carrier_invariant : forall (a : t),
    cut_shape_ok (cut_raw a) = true /\ interval_bits (cut_raw a) <= C.bits.
  Proof.
    intro a. apply cut_valid_parts, cut_raw_valid.
  Qed.

  (** Cutting an existing carrier value preserves its projection. *)
  Lemma cut_fixed : forall (a : t), cut_raw (cut (cut_raw a)) = cut_raw a.
  Proof.
    intro a. rewrite cut_agrees. apply cut_interval_fixed, cut_raw_valid.
  Qed.

  (** Cutting preserves every represented integer. *)
  Lemma cut_sound : forall a z,
    (match a with IBot => False | I lo hi => in_bnd lo hi z end) ->
    (match cut_raw (cut a) with IBot => False | I lo hi => in_bnd lo hi z end).
  Proof.
    intros a z. rewrite cut_agrees. apply cut_interval_sound.
  Qed.

  (** The raw-domain link identifies the bounded concretization. *)
  Lemma gamma_raw : forall a z, gamma a z <-> R.gamma (cut_raw a) z.
  Proof.
    intros a z. rewrite RL.raw_gamma. reflexivity.
  Qed.

  (** Raw-domain membership survives the outward wrapper. *)
  Lemma raw_cut_sound : forall a z, R.gamma a z -> gamma (cut a) z.
  Proof.
    intros a z Ha. apply RL.raw_gamma in Ha.
    unfold gamma, in_cut. apply cut_sound. exact Ha.
  Qed.

  (** Normalization and outward endpoints never increase threshold rank. *)
  Lemma cut_rank_nonincreasing : forall q a,
    R.interval_wrank q (cut_interval C.bits a) <= R.interval_wrank q a.
  Proof.
    intros q a. unfold cut_interval.
    destruct (cut_shape_ok a); [|destruct a; cbn [R.interval_wrank]; lia].
    destruct a as [|lo hi]; [reflexivity |].
    unfold cut_lower, cut_upper.
    destruct lo as [|lo|], hi as [|hi|]; cbn [cut_endpoint_ok];
      repeat match goal with
      | |- context [Nat.leb ?n ?m] => destruct (Nat.leb n m)
      end;
      cbn [R.interval_wrank]; lia.
  Qed.

  (** Every value is below itself in the supplied raw order. *)
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intro a. apply R.leb_refl.
  Qed.

  (** The supplied raw order composes through the projections. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c. apply R.leb_trans.
  Qed.

  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intro a.
    unfold leb.
    rewrite RL.raw_leb.
    reflexivity.
  Qed.

  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    change (R.is_bot IBot = true).
    assert (Hbot : R.bot = IBot).
    { generalize (R.bot_least IBot).
      rewrite RL.raw_leb.
      destruct R.bot as [|lo hi]; cbn; intro Hleb; congruence. }
    rewrite <- Hbot.
    exact R.is_bot_bot.
  Qed.

  (** A recognized bottom is below every bounded value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b. apply R.is_bot_least.
  Qed.

  (** The outward wrapper retains the raw join's left upper bound. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b. unfold leb, join. rewrite RL.raw_leb, cut_agrees.
    apply cut_interval_upper; [exact (proj1 (carrier_invariant a)) |].
    rewrite <- RL.raw_leb. apply R.join_ub_l.
  Qed.

  (** The outward wrapper retains the raw join's right upper bound. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b. unfold leb, join. rewrite RL.raw_leb, cut_agrees.
    apply cut_interval_upper; [exact (proj1 (carrier_invariant b)) |].
    rewrite <- RL.raw_leb. apply R.join_ub_r.
  Qed.

  (** Two infinite endpoints contain every bounded interval. *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intro a. unfold leb. rewrite RL.raw_leb.
    destruct (cut_raw a) as [|lo [|hi|]]; reflexivity.
  Qed.

  (** The raw meet's semantics force every retained endpoint into the carrier budget. *)
  Lemma meet_refines_both : forall a b,
    leb (meet a b) a = true /\ leb (meet a b) b = true.
  Proof.
    intros a b.
    pose proof (R.meet_lb_l (cut_raw a) (cut_raw b)) as Hleft.
    pose proof (R.meet_lb_r (cut_raw a) (cut_raw b)) as Hright.
    rewrite RL.raw_leb in Hleft, Hright.
    unfold leb, meet. rewrite !RL.raw_leb, !cut_agrees.
    destruct (cut_shape_ok (R.meet (cut_raw a) (cut_raw b))) eqn:Hshape.
    - assert (Hvalid : cut_interval_ok C.bits (R.meet (cut_raw a) (cut_raw b)) = true).
      { eapply cut_meet_valid with (a := cut_raw a) (b := cut_raw b);
          [apply cut_raw_valid | apply cut_raw_valid | exact Hleft | exact Hright | |exact Hshape].
        intros z Ha Hb. apply RL.raw_gamma. apply R.gamma_meet;
          apply RL.raw_gamma; assumption. }
      rewrite (cut_interval_fixed _ _ Hvalid). split; assumption.
    - unfold cut_interval. rewrite Hshape. split; reflexivity.
  Qed.

  (** Meeting stays below its left bounded operand. *)
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros a b. exact (proj1 (meet_refines_both a b)).
  Qed.

  (** Meeting stays below its right bounded operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof.
    intros a b. exact (proj2 (meet_refines_both a b)).
  Qed.

  (** The outward wrapper retains the previous widening value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold leb, widen. rewrite RL.raw_leb, cut_agrees.
    apply cut_interval_upper; [exact (proj1 (carrier_invariant a)) |].
    rewrite <- RL.raw_leb. apply R.widen_ub_l.
  Qed.

  (** The outward wrapper retains the candidate widening value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold leb, widen. rewrite RL.raw_leb, cut_agrees.
    apply cut_interval_upper; [exact (proj1 (carrier_invariant b)) |].
    rewrite <- RL.raw_leb. apply R.widen_ub_r.
  Qed.

  (** A stable raw widening is unchanged by the carrier projection. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hle. unfold widen. rewrite R.widen_stable by exact Hle.
    apply cut_raw_injective, cut_fixed.
  Qed.

  (** An unstable raw widening decreases rank before the outward cutoff. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p a b Hbot Hle.
    pose proof (R.wrank_widen p (cut_raw a) (cut_raw b) Hbot Hle) as Hrank.
    rewrite !RL.raw_wrank in Hrank.
    unfold wrank, widen. rewrite cut_agrees.
    eapply Nat.le_lt_trans; [apply cut_rank_nonincreasing | exact Hrank].
  Qed.

  (** Outward cutoff preserves the raw widening's nonincrease of rank. *)
  Lemma wrank_widen_le : forall p a b,
    is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot.
    pose proof (R.wrank_widen_le p (cut_raw a) (cut_raw b) Hbot) as Hrank.
    rewrite !RL.raw_wrank in Hrank.
    unfold wrank, widen. rewrite cut_agrees.
    eapply Nat.le_trans; [apply cut_rank_nonincreasing | exact Hrank].
  Qed.

  (** The raw narrowing already fits the endpoint budget and stays between its operands. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle.
    destruct (R.narrow_between (cut_raw a) (cut_raw b) Hle) as [Hlower Hupper].
    rewrite RL.raw_leb in Hlower, Hupper.
    assert (Hbits : interval_bits (R.narrow (cut_raw a) (cut_raw b)) <= C.bits).
    { eapply Nat.le_trans; [apply RL.raw_narrow_bits |].
      apply Nat.max_lub;
        [exact (proj2 (carrier_invariant a)) | exact (proj2 (carrier_invariant b))]. }
    unfold leb, narrow. rewrite !RL.raw_leb, !cut_agrees. split.
    - apply cut_interval_upper; [exact (proj1 (carrier_invariant b)) | exact Hlower].
    - rewrite (cut_interval_small _ _ Hbits).
      destruct (cut_shape_ok (R.narrow (cut_raw a) (cut_raw b)));
        [exact Hupper | reflexivity].
  Qed.

  (** Raw inclusion preserves the same concrete integer interpretation. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    intros a b c Hle Ha. apply gamma_raw.
    eapply R.gamma_mono; [exact Hle | apply gamma_raw; exact Ha].
  Qed.

  (** The bounded bottom contains no integer. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c Hmember. exact Hmember.
  Qed.

  (** The bounded top contains every integer. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intro c. split; trivial.
  Qed.

  (** Raw meet soundness survives the outward wrapper. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    intros a b c Ha Hb. unfold meet. apply raw_cut_sound, R.gamma_meet;
      apply gamma_raw; assumption.
  Qed.

  (** Raw bottom recognition excludes every represented integer. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros a c Hbot Ha. eapply R.is_bot_sound; [exact Hbot |].
    apply gamma_raw. exact Ha.
  Qed.

  (** Bottom recognition is downward closed in the raw order. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    intros a b. apply R.is_bot_below.
  Qed.

  (** Pointwise membership transfers to the projected operand list. *)
  Lemma gamma_raw_list : forall xs cs,
    Forall2 gamma xs cs -> Forall2 R.gamma (map cut_raw xs) cs.
  Proof.
    intros xs cs Hmembers. induction Hmembers as [|x c xs cs Hx Hxs IH];
      cbn [map]; constructor; [now apply gamma_raw | exact IH].
  Qed.

  (** The forward raw-domain result contains every successful evaluation. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hmembers Heval. unfold forward. apply raw_cut_sound.
    eapply R.forward_sound; [apply gamma_raw_list; exact Hmembers | exact Heval].
  Qed.

  (** Packing inward-cut results preserves their original operand positions and order. *)
  Lemma cut_list_refines : forall xs ys,
    Forall2 (fun y x => R.leb y x = true) ys (map cut_raw xs) ->
    Forall2 (fun y x => leb y x = true)
      (map (fun yx => pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))
        (combine ys (map cut_raw xs))) xs.
  Proof.
    induction xs as [|x xs IH]; intros ys Hrefines; destruct ys as [|y ys];
      inversion Hrefines as [|y' x' ys' xs' Hle Htail]; subst;
      cbn [map combine]; constructor.
    - unfold leb. rewrite RL.raw_leb.
      rewrite pack_cut_agrees.
      + apply cut_within_refines. now rewrite <- RL.raw_leb.
      + apply cut_within_valid; [apply cut_raw_valid | now rewrite <- RL.raw_leb].
    - apply IH. exact Htail.
  Qed.

  (** Packing inward-cut results preserves every compatible concrete operand. *)
  Lemma cut_list_sound : forall xs ys cs,
    Forall2 (fun y x => R.leb y x = true) ys (map cut_raw xs) ->
    Forall2 gamma xs cs -> Forall2 R.gamma ys cs ->
    Forall2 gamma
      (map (fun yx => pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))
        (combine ys (map cut_raw xs))) cs.
  Proof.
    intros xs ys cs Hrefines Hmembers Hraw. revert ys Hrefines Hraw.
    induction Hmembers as [|x z xs cs Hx Hxs IH]; intros ys Hrefines Hraw;
      destruct ys as [|y ys]; inversion Hrefines as [|y' x' ys' xs' Hle Htail]; subst;
      inversion Hraw as [|y' z' ys' cs' Hy Hys]; subst;
      cbn [map combine]; constructor.
    - change (cut_member (cut_raw (pack_cut C.bits (cut_within C.bits (cut_raw x) y))) z).
      rewrite pack_cut_agrees.
      + apply cut_within_sound; [exact Hx | apply RL.raw_gamma; exact Hy].
      + apply cut_within_valid; [apply cut_raw_valid | now rewrite <- RL.raw_leb].
    - eapply IH; eassumption.
  Qed.

  (** Raw backward soundness and inward cutoff retain compatible operands. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hmembers Heval Hr. unfold backward.
    apply cut_list_sound; [apply R.backward_refines | exact Hmembers |].
    eapply R.backward_sound; [apply gamma_raw_list; exact Hmembers | exact Heval |].
    apply gamma_raw. exact Hr.
  Qed.

  (** Backward results refine each bounded operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. unfold backward. apply cut_list_refines, R.backward_refines.
  Qed.

  (** Raw guard soundness and inward cutoff retain satisfying operands. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hmembers Hholds. unfold guard.
    apply cut_list_sound; [apply R.guard_refines | exact Hmembers |].
    apply R.guard_sound; [apply gamma_raw_list; exact Hmembers | exact Hholds].
  Qed.

  (** Guard results refine each bounded operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. unfold guard. apply cut_list_refines, R.guard_refines.
  Qed.
End CutInterval.

Module CutIntervalRaw (L : Z_LANGUAGE_T) (T : THRESHOLDS_T).
  Module R := IntervalT L T.
  Module Link <: CUT_RAW_LINK L T R.
    Lemma raw_leb : forall a b, R.leb a b = cut_leb a b.
    Proof. reflexivity. Qed.
    Lemma raw_gamma : forall a z, R.gamma a z <-> R.in_itv a z.
    Proof. reflexivity. Qed.
    Lemma raw_wrank : forall q a, R.wrank q a = R.interval_wrank q a.
    Proof. reflexivity. Qed.
    Lemma raw_narrow_bits : forall a b,
      interval_bits (R.narrow a b) <= Nat.max (interval_bits a) (interval_bits b).
    Proof.
      intros [|l h] [|l' h']; cbn; try lia.
      destruct l, h, l', h'; cbn; lia.
    Qed.
    Lemma raw_work : forall o xs, R.work o xs =
      fold_right Nat.add 0 (map interval_bits xs) + length xs +
        (fold_right Nat.add 0 (map interval_bits xs) + 1) ^ 2 +
        match L.view o with ZConst z => Z.size_nat z | _ => 0 end.
    Proof. reflexivity. Qed.
    Lemma raw_gwork : forall g xs, R.gwork g xs =
      fold_right Nat.add 0 (map interval_bits xs) + length xs +
        (fold_right Nat.add 0 (map interval_bits xs) + 1) ^ 2.
    Proof. reflexivity. Qed.
    End Link.
End CutIntervalRaw.

(** A positive bit-count scan pays exactly once for each binary digit. *)
Lemma cut_positive_scan : forall p,
  Std.Pos.T_size_nat p = N.of_nat (Pos.size_nat p).
Proof.
  induction p as [p IH|p IH|].
  - change (1 + Std.Pos.T_size_nat p = N.of_nat (S (Pos.size_nat p)))%N.
    rewrite IH, Nat2N.inj_succ. lia.
  - change (1 + Std.Pos.T_size_nat p = N.of_nat (S (Pos.size_nat p)))%N.
    rewrite IH, Nat2N.inj_succ. lia.
  - reflexivity.
Qed.

(** Reading an integer size adds one sign-constructor inspection to its digit scan. *)
Lemma cut_integer_scan : forall z,
  Word.Z.T_size_nat z = (1 + N.of_nat (Z.size_nat z))%N.
Proof.
  intros [|p|p]; unfold Word.Z.T_size_nat; cbn beta iota zeta;
    cbn [Z.size_nat]; rewrite ?cut_positive_scan; reflexivity.
Qed.

(** Checking an endpoint pays for all of its finite bits. *)
Lemma cut_endpoint_scan_lower : forall bits b,
  (N.of_nat (match b with Fin z => Z.size_nat z | _ => 0 end) <=
    T_cut_endpoint_ok bits b)%N.
Proof.
  intros bits [|z|]; unfold T_cut_endpoint_ok; cbn beta iota zeta;
    rewrite ?cut_integer_scan; lia.
Qed.

(** Unary comparison stops after at most the endpoint's own bit count. *)
Lemma cut_endpoint_scan_upper : forall bits b,
  (T_cut_endpoint_ok bits b <=
    2 * N.of_nat (match b with Fin z => Z.size_nat z | _ => 0 end) + 3)%N.
Proof.
  intros bits [|z|]; unfold T_cut_endpoint_ok; cbn beta iota zeta; try lia.
  pose proof (Std.Nat.T_leb_le (Z.size_nat z) bits) as Hcompare.
  rewrite cut_integer_scan. lia.
Qed.

(** The only nonconstant shape test compares the two finite endpoints. *)
Lemma cut_shape_scan_upper : forall a,
  (T_cut_shape_ok a <= 8 * (N.of_nat (interval_bits a) + 1))%N.
Proof.
  intros [|[|lo|] [|hi|]]; unfold T_cut_shape_ok;
    cbn beta iota zeta; cbn [interval_bits]; try lia.
  pose proof (Std.Z.T_leb_le lo hi) as Hcompare.
  pose proof (Nat.le_max_l (Z.size_nat lo) (Z.size_nat hi)) as Hlower.
  lia.
Qed.

(** The carrier check scans two endpoints and tests their shape. *)
Lemma cut_valid_scan_upper : forall bits a,
  (T_cut_interval_ok bits a <= 24 * (N.of_nat (interval_bits a) + 1))%N.
Proof.
  intros bits [|lo hi]; [vm_compute; congruence|].
  pose proof (cut_shape_scan_upper (I lo hi)) as Hshape.
  pose proof (cut_endpoint_scan_upper bits lo) as Hlo.
  pose proof (cut_endpoint_scan_upper bits hi) as Hhi.
  assert (Hlower :
    (match lo with Fin z => Z.size_nat z | _ => 0 end) <= interval_bits (I lo hi)).
  { apply Nat.le_max_l. }
  assert (Hupper :
    (match hi with Fin z => Z.size_nat z | _ => 0 end) <= interval_bits (I lo hi)).
  { apply Nat.le_max_r. }
  unfold T_cut_interval_ok. cbn beta iota zeta. time_simpl. lia.
Qed.

(** Packing performs its Boolean check and adds constant constructor overhead. *)
Lemma cut_pack_scan_upper : forall bits a,
  (T_pack_cut bits a <= 32 * (N.of_nat (interval_bits a) + 1))%N.
Proof.
  intros bits a.
  pose proof (cut_valid_scan_upper bits a) as Hcheck.
  unfold T_pack_cut. cbn beta iota zeta.
  destruct (cut_interval_ok bits a); cbn beta iota zeta; lia.
Qed.

(** Outward cutoff is linear in the inspected raw endpoints. *)
Lemma cut_interval_scan_upper : forall bits a,
  (T_cut_interval bits a <= 32 * (N.of_nat (interval_bits a) + 1))%N.
Proof.
  intros bits [|lo hi].
  - vm_compute; congruence.
  - pose proof (cut_shape_scan_upper (I lo hi)) as Hshape.
    pose proof (cut_endpoint_scan_upper bits lo) as Hlo.
    pose proof (cut_endpoint_scan_upper bits hi) as Hhi.
    assert (Hlower :
      (match lo with Fin z => Z.size_nat z | _ => 0 end) <= interval_bits (I lo hi)).
    { apply Nat.le_max_l. }
    assert (Hupper :
      (match hi with Fin z => Z.size_nat z | _ => 0 end) <= interval_bits (I lo hi)).
    { apply Nat.le_max_r. }
    unfold T_cut_interval, T_cut_lower, T_cut_upper.
    destruct (cut_shape_ok (I lo hi)); cbn beta iota zeta; lia.
Qed.

(** Inward cutoff reads the candidate endpoints and only selects old endpoints. *)
Lemma cut_within_scan_upper : forall bits old a,
  (T_cut_within bits old a <= 32 * (N.of_nat (interval_bits a) + 1))%N.
Proof.
  intros bits old [|lo hi].
  - destruct old; vm_compute; congruence.
  - pose proof (cut_shape_scan_upper (I lo hi)) as Hshape.
    pose proof (cut_endpoint_scan_upper bits lo) as Hlo.
    pose proof (cut_endpoint_scan_upper bits hi) as Hhi.
    assert (Hlower :
      (match lo with Fin z => Z.size_nat z | _ => 0 end) <= interval_bits (I lo hi)).
    { apply Nat.le_max_l. }
    assert (Hupper :
      (match hi with Fin z => Z.size_nat z | _ => 0 end) <= interval_bits (I lo hi)).
    { apply Nat.le_max_r. }
    unfold T_cut_within.
    destruct (cut_shape_ok (I lo hi)); destruct old;
      cbn beta iota zeta; lia.
Qed.

(** The endpoint tests pay for every bit that survives an outward cutoff. *)
Lemma cut_interval_result_scan : forall bits a,
  (N.of_nat (interval_bits (cut_interval bits a)) <= T_cut_interval bits a)%N.
Proof.
  intros bits a. unfold cut_interval.
  destruct (cut_shape_ok a) eqn:Hshape; [|apply N.le_0_l].
  destruct a as [|lo hi]; [apply N.le_0_l|].
  pose proof (cut_endpoint_scan_lower bits lo) as Hlo.
  pose proof (cut_endpoint_scan_lower bits hi) as Hhi.
  assert (Hlower :
    (N.of_nat (match cut_lower bits lo with Fin z => Z.size_nat z | _ => 0 end) <=
      T_cut_endpoint_ok bits lo)%N).
  { unfold cut_lower. destruct (cut_endpoint_ok bits lo); [exact Hlo|apply N.le_0_l]. }
  assert (Hupper :
    (N.of_nat (match cut_upper bits hi with Fin z => Z.size_nat z | _ => 0 end) <=
      T_cut_endpoint_ok bits hi)%N).
  { unfold cut_upper. destruct (cut_endpoint_ok bits hi); [exact Hhi|apply N.le_0_l]. }
  cbn [interval_bits]. rewrite Nat2N.inj_max.
  unfold T_cut_interval, T_cut_lower, T_cut_upper.
  rewrite Hshape. cbn beta iota zeta. apply N.max_lub; lia.
Qed.

(** A checked fallback is smaller than an endpoint that exceeds the same cutoff. *)
Lemma cut_selected_endpoint_scan : forall bits old b,
  cut_endpoint_ok bits old = true ->
  (N.of_nat (match (if cut_endpoint_ok bits b then b else old) with
             | Fin z => Z.size_nat z | _ => 0 end) <= T_cut_endpoint_ok bits b)%N.
Proof.
  intros bits old b Hold.
  pose proof (cut_endpoint_scan_lower bits b) as Hscan.
  destruct (cut_endpoint_ok bits b) eqn:Hnew; [exact Hscan|].
  assert (Holdbits : (match old with Fin z => Z.size_nat z | _ => 0 end) <= bits).
  { destruct old as [|z|]; cbn [cut_endpoint_ok] in Hold; try lia.
    now apply Nat.leb_le in Hold. }
  assert (Hnewbits : bits < (match b with Fin z => Z.size_nat z | _ => 0 end)).
  { destruct b as [|z|]; cbn [cut_endpoint_ok] in Hnew; try discriminate.
    now apply Nat.leb_gt in Hnew. }
  lia.
Qed.

(** The candidate's endpoint scans pay for every selected refinement endpoint. *)
Lemma cut_within_result_scan : forall bits old a,
  cut_interval_ok bits old = true ->
  (N.of_nat (interval_bits (cut_within bits old a)) <= T_cut_within bits old a)%N.
Proof.
  intros bits old a Hold. unfold cut_within.
  destruct (cut_shape_ok a) eqn:Hshape; [|apply N.le_0_l].
  destruct a as [|lo hi]; [destruct old; apply N.le_0_l|].
  destruct old as [|olo ohi]; [apply N.le_0_l|].
  apply andb_true_iff in Hold as [_ Hendpoints].
  apply andb_true_iff in Hendpoints as [Holdlo Holdhi].
  pose proof (cut_selected_endpoint_scan bits olo lo Holdlo) as Hlo.
  pose proof (cut_selected_endpoint_scan bits ohi hi Holdhi) as Hhi.
  cbn [interval_bits]. rewrite Nat2N.inj_max.
  unfold T_cut_within. rewrite Hshape. cbn beta iota zeta.
  apply N.max_lub; lia.
Qed.

(** Rechecking an outward result is paid by the original cutoff's scans. *)
Lemma cut_pack_interval_scan : forall bits a,
  (T_pack_cut bits (cut_interval bits a) <= 32 * (T_cut_interval bits a + 1))%N.
Proof.
  intros bits a.
  pose proof (cut_pack_scan_upper bits (cut_interval bits a)) as Hpack.
  pose proof (cut_interval_result_scan bits a) as Hbits.
  lia.
Qed.

(** Rechecking an inward result is paid even when its shape is rejected. *)
Lemma cut_pack_within_scan : forall bits old a,
  cut_interval_ok bits old = true ->
  (T_pack_cut bits (cut_within bits old a) <= 32 * (T_cut_within bits old a + 1))%N.
Proof.
  intros bits old a Hold.
  pose proof (cut_pack_scan_upper bits (cut_within bits old a)) as Hpack.
  pose proof (cut_within_result_scan bits old a Hold) as Hbits.
  lia.
Qed.

(** Projecting a carrier list performs one projection and one list step per operand. *)
Lemma cut_projection_scan : forall bits (xs : list (cut_itv bits)),
  (Std.ListDef.T_map cut_raw (@T_cut_raw bits) xs <= 2 * N.of_nat (length xs) + 1)%N.
Proof.
  intros bits xs.
  apply (Std.ListDef.T_map_le (@cut_raw bits) (@T_cut_raw bits) 1 xs).
  intro a. reflexivity.
Qed.

Module CutIntervalT (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_T)
    (T : THRESHOLDS_T) (R : INTERVAL_ALL L T) (RL : CUT_RAW_LINK L T R)
    <: CUT_INTERVAL_ALL C L T R RL.
  Include CutInterval C L T R RL.

  TimeFun cut.
  TimeFun bot.
  TimeFun top.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat := interval_bits (cut_raw a).
  Definition wsize (q : wparam) : nat :=
    (T.depth q + 1) * (T.tree_bits q + 1) + C.bits.
  Definition wunits (_ : t) : nat := 0.
  Definition work := transfer_work.
  Definition gwork := guard_work.

  Definition k_cut : N := 1024%N.
  Definition c_val : N := (4 * (k_cut + 1)^2 * (R.c_val + 1))%N.
  Definition c_lat : N := c_val.
  Definition c_cut : N := (k_cut * (k_cut + 1))%N.

  (** Projecting packed refinements preserves every paired inward result. *)
  Lemma refinement_projections : forall (xs : list t) (ys : list itv),
    Forall2 (fun y old => R.leb y old = true) ys (map cut_raw xs) ->
    map cut_raw
      (map (fun yx => pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))
        (combine ys (map cut_raw xs))) =
    map (fun yx => cut_within C.bits (snd yx) (fst yx))
      (combine ys (map cut_raw xs)).
  Proof.
    induction xs as [|x xs IH]; intros ys Hrefines.
    - inversion Hrefines. reflexivity.
    - inversion Hrefines as [|y old ys' olds' Hhead Htail]; subst.
      cbn [map combine fst snd].
      assert (Hvalid : cut_interval_ok C.bits (cut_within C.bits (cut_raw x) y) = true).
      { apply cut_within_valid; [apply cut_raw_valid|].
        rewrite <- RL.raw_leb. exact Hhead. }
      rewrite (pack_cut_agrees C.bits _ Hvalid).
      f_equal. apply IH. exact Htail.
  Qed.

  (** Concrete membership uses the projected inclusive interval. *)
  Lemma F_gamma : forall a z, gamma a z <-> in_cut a z.
  Proof.
    intros a z. reflexivity.
  Qed.
  (** Inclusion compares normalized bounded projections directly. *)
  Lemma F_leb : forall a b, leb a b = R.leb (cut_raw a) (cut_raw b).
  Proof.
    intros a b. reflexivity.
  Qed.
  (** Bottom has the normalized empty representation. *)
  Lemma F_bot : cut_raw bot = IBot.
  Proof.
    reflexivity.
  Qed.
  (** Top has two infinite endpoints. *)
  Lemma F_top : cut_raw top = I NegInf PosInf.
  Proof.
    reflexivity.
  Qed.
  (** Bottom recognition agrees with the raw domain. *)
  Lemma F_is_bot : forall a, is_bot a = R.is_bot (cut_raw a).
  Proof.
    intro a. reflexivity.
  Qed.
  (** Joining cuts the raw join before it enters the bounded carrier. *)
  Lemma F_join : forall a b,
    cut_raw (join a b) = cut_interval C.bits (R.join (cut_raw a) (cut_raw b)).
  Proof.
    intros a b. apply cut_agrees.
  Qed.
  (** Meeting cuts the normalized raw intersection. *)
  Lemma F_meet : forall a b,
    cut_raw (meet a b) = cut_interval C.bits (R.meet (cut_raw a) (cut_raw b)).
  Proof.
    intros a b. apply cut_agrees.
  Qed.
  (** Every threshold parameter is accepted and its result is cut outward. *)
  Lemma F_widen : forall q a b,
    cut_raw (widen q a b) = cut_interval C.bits (R.widen q (cut_raw a) (cut_raw b)).
  Proof.
    intros q a b. apply cut_agrees.
  Qed.
  (** Narrowing cuts the raw narrowed result. *)
  Lemma F_narrow : forall a b,
    cut_raw (narrow a b) = cut_interval C.bits (R.narrow (cut_raw a) (cut_raw b)).
  Proof.
    intros a b. apply cut_agrees.
  Qed.
  (** Forward transfer cuts every raw result, including constants and shifts. *)
  Lemma F_forward : forall o xs,
    cut_raw (forward o xs) = cut_interval C.bits (R.forward o (map cut_raw xs)).
  Proof.
    intros o xs. apply cut_agrees.
  Qed.
  (** Backward transfer cuts each result in its original operand position. *)
  Lemma F_backward : forall o r xs,
    map cut_raw (backward o r xs) =
      map (fun yx => cut_within C.bits (snd yx) (fst yx))
        (combine (R.backward o (cut_raw r) (map cut_raw xs)) (map cut_raw xs)).
  Proof.
    intros o r xs. unfold backward.
    apply refinement_projections, R.backward_refines.
  Qed.
  (** Guard refinement cuts each returned operand. *)
  Lemma F_guard : forall g xs,
    map cut_raw (guard g xs) =
      map (fun yx => cut_within C.bits (snd yx) (fst yx))
        (combine (R.guard g (map cut_raw xs)) (map cut_raw xs)).
  Proof.
    intros g xs. unfold guard.
    apply refinement_projections, R.guard_refines.
  Qed.
  (** Widening rank counts thresholds beyond the retained finite endpoints. *)
  Lemma F_rank : forall q a, wrank q a = R.interval_wrank q (cut_raw a).
  Proof.
    intros q a. reflexivity.
  Qed.
  (** Normalization and outward cutoff cannot increase the raw threshold rank. *)
  Lemma F_cut_rank : forall q a,
    R.interval_wrank q (cut_interval C.bits a) <= R.interval_wrank q a.
  Proof.
    apply cut_rank_nonincreasing.
  Qed.
  (** The total raw helper clock includes all endpoint inspections. *)
  Lemma T_cut_helper : forall a,
    (T_cut_interval C.bits a <= k_cut * N.of_nat (interval_bits a + 1))%N.
  Proof.
    intro a. pose proof (cut_interval_scan_upper C.bits a) as Hscan.
    unfold k_cut. rewrite Nat2N.inj_add. lia.
  Qed.
  (** Inward cutting reads both intervals. *)
  Lemma T_cut_within_helper : forall old a,
    (T_cut_within C.bits old a <= k_cut * N.of_nat (interval_bits old + interval_bits a + 1))%N.
  Proof.
    intros old a. pose proof (cut_within_scan_upper C.bits old a) as Hscan.
    unfold k_cut. rewrite !Nat2N.inj_add. lia.
  Qed.
  (** Packing the Boolean subtype adds constant overhead to the raw cutoff helper. *)
  Lemma T_cut_pack : forall a,
    (T_cut a <= k_cut * (T_cut_interval C.bits a + 1))%N.
  Proof.
    intro a. pose proof (cut_pack_interval_scan C.bits a) as Hpack.
    unfold T_cut, k_cut. cbn beta iota zeta. lia.
  Qed.
  (** Mapping adds one list step to each bounded callback and one terminal step. *)
  Lemma map_scan_bound : forall (A B : Type) (f : A -> B) (clock cost : A -> N)
      (factor : N) (xs : list A),
    (forall x, In x xs -> (clock x + 1 <= factor * cost x)%N) ->
    (Std.ListDef.T_map f clock xs <=
      factor * fold_right N.add 0%N (map cost xs) + 1)%N.
  Proof.
    intros A B f clock cost factor xs.
    induction xs as [|x xs IH]; intro Hcost.
    - change (1 <= factor * 0 + 1)%N. lia.
    - assert (Hhead : (clock x + 1 <= factor * cost x)%N).
      { apply Hcost. now left. }
      assert (Htail : forall y, In y xs -> (clock y + 1 <= factor * cost y)%N).
      { intros y Hy. apply Hcost. now right. }
      specialize (IH Htail).
      change (1 + (clock x + Std.ListDef.T_map f clock xs) <=
        factor * (cost x + fold_right N.add 0%N (map cost xs)) + 1)%N.
      rewrite N.mul_add_distr_l. lia.
  Qed.

  (** The paired packing traversal is paid by the inward-cut clocks in its positions. *)
  Lemma refinement_list_scan : forall (xs : list t) (ys : list itv),
    (Std.ListDef.T_map
      (fun yx => pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))
      (fun yx => (1 + (((Std.Datatypes.T_snd yx + Std.Datatypes.T_fst yx) +
        T_cut_within C.bits (snd yx) (fst yx)) +
        T_pack_cut C.bits (cut_within C.bits (snd yx) (fst yx))))%N)
      (combine ys (map cut_raw xs)) <=
      64 * fold_right N.add 0%N
        (map (fun yx => (T_cut_within C.bits (snd yx) (fst yx) + 1)%N)
          (combine ys (map cut_raw xs))) + 1)%N.
  Proof.
    intros xs ys. apply map_scan_bound.
    intros [y old] Hposition.
    apply in_combine_r in Hposition.
    apply in_map_iff in Hposition as [x [Hraw _]].
    subst old.
    pose proof (cut_pack_within_scan C.bits (cut_raw x) y (cut_raw_valid C.bits x)) as Hpack.
    unfold Std.Datatypes.T_snd, Std.Datatypes.T_fst.
    cbn beta iota zeta. cbn [fst snd]. lia.
  Qed.

  (** Raw backward refinement preserves the operand list length. *)
  Lemma raw_backward_length : forall o (r : t) (xs : list t),
    length (R.backward o (cut_raw r) (map cut_raw xs)) = length xs.
  Proof.
    intros o r xs.
    pose proof (Forall2_length (R.backward_refines o (cut_raw r) (map cut_raw xs))) as Hlength.
    now rewrite length_map in Hlength.
  Qed.

  (** Raw guard refinement preserves the operand list length. *)
  Lemma raw_guard_length : forall g (xs : list t),
    length (R.guard g (map cut_raw xs)) = length xs.
  Proof.
    intros g xs.
    pose proof (Forall2_length (R.guard_refines g (map cut_raw xs))) as Hlength.
    now rewrite length_map in Hlength.
  Qed.

  (** Forward timing includes projection traversal and cutting the actual raw result. *)
  Lemma T_forward_source : forall o xs,
    (T_forward o xs <= k_cut *
      (R.T_forward o (map cut_raw xs) +
       T_cut_interval C.bits (R.forward o (map cut_raw xs)) +
       N.of_nat (length xs) + 1))%N.
  Proof.
    intros o xs.
    pose proof (cut_projection_scan C.bits xs) as Hprojection.
    pose proof (cut_pack_interval_scan C.bits (R.forward o (map cut_raw xs))) as Hpack.
    unfold T_forward, T_cut, T_cut_raw, k_cut in *.
    unfold t, R.t in *.
    cbn beta iota zeta in *.
    lia.
  Qed.

  (** Backward timing includes every returned cutoff and both list traversals. *)
  Lemma T_backward_source : forall o r xs,
    (T_backward o r xs <= k_cut *
      (R.T_backward o (cut_raw r) (map cut_raw xs) +
       fold_right N.add 0%N
         (map (fun yx => (T_cut_within C.bits (snd yx) (fst yx) + 1)%N)
           (combine (R.backward o (cut_raw r) (map cut_raw xs)) (map cut_raw xs))) +
       N.of_nat (length xs) + 1))%N.
  Proof.
    intros o r xs.
    pose proof (cut_projection_scan C.bits xs) as Hprojection.
    pose proof (refinement_list_scan xs (R.backward o (cut_raw r) (map cut_raw xs))) as Hpack.
    pose proof (Std.List.T_combine_le
      (R.backward o (cut_raw r) (map cut_raw xs)) (map cut_raw xs)) as Hcombine.
    rewrite raw_backward_length in Hcombine.
    unfold T_backward, T_cut_raw, k_cut in *.
    unfold t, R.t in *.
    cbn beta iota zeta in *.
    lia.
  Qed.

  (** Guard timing includes every returned cutoff and both list traversals. *)
  Lemma T_guard_source : forall g xs,
    (T_guard g xs <= k_cut *
      (R.T_guard g (map cut_raw xs) +
       fold_right N.add 0%N
         (map (fun yx => (T_cut_within C.bits (snd yx) (fst yx) + 1)%N)
           (combine (R.guard g (map cut_raw xs)) (map cut_raw xs))) + N.of_nat (length xs) + 1))%N.
  Proof.
    intros g xs.
    pose proof (cut_projection_scan C.bits xs) as Hprojection.
    pose proof (refinement_list_scan xs (R.guard g (map cut_raw xs))) as Hpack.
    pose proof (Std.List.T_combine_le (R.guard g (map cut_raw xs)) (map cut_raw xs)) as Hcombine.
    rewrite raw_guard_length in Hcombine.
    unfold T_guard, T_cut_raw, k_cut in *.
    unfold t, R.t in *.
    cbn beta iota zeta in *.
    lia.
  Qed.

  (** Widening timing includes cutting the threshold-selected endpoints. *)
  Lemma T_widen_source : forall q a b,
    (T_widen q a b <= k_cut *
      (R.T_widen q (cut_raw a) (cut_raw b) +
       T_cut_interval C.bits (R.widen q (cut_raw a) (cut_raw b)) + 1))%N.
  Proof.
    intros q a b.
    pose proof (cut_pack_interval_scan C.bits (R.widen q (cut_raw a) (cut_raw b))) as Hpack.
    unfold T_widen, T_cut, T_cut_raw, k_cut. cbn beta iota zeta. lia.
  Qed.

  (** The wrapper constant covers the raw constant and its fixed call overhead. *)
  Lemma c_val_dominates : (R.c_val + 4 <= c_val)%N.
  Proof.
    unfold c_val.
    nia.
  Qed.

  (** Rejecting an invalid packed value can only reduce its endpoint storage. *)
  Lemma pack_cut_bits_le : forall a,
    interval_bits (cut_raw (pack_cut C.bits a)) <= interval_bits a.
  Proof.
    intro a.
    rewrite pack_cut_choice.
    destruct (cut_interval_ok C.bits a); cbn [interval_bits]; lia.
  Qed.

  (** Outward cutoff replaces finite endpoints by zero-storage infinities. *)
  Lemma cut_interval_bits_le : forall a,
    interval_bits (cut_interval C.bits a) <= interval_bits a.
  Proof.
    intro a.
    unfold cut_interval.
    destruct (cut_shape_ok a); [|cbn [interval_bits]; lia].
    destruct a as [|lo hi]; [cbn [interval_bits]; lia|].
    unfold cut_lower, cut_upper.
    destruct (cut_endpoint_ok C.bits lo), (cut_endpoint_ok C.bits hi);
      cbn [interval_bits]; lia.
  Qed.

  (** The bounded carrier stores no more endpoint bits than its raw source. *)
  Lemma cut_bits_le : forall a, size (cut a) <= interval_bits a.
  Proof.
    intro a.
    unfold size.
    rewrite cut_agrees.
    apply cut_interval_bits_le.
  Qed.

  (** An inward cutoff chooses every endpoint from one of its two operands. *)
  Lemma cut_within_bits_le : forall old a,
    interval_bits (cut_within C.bits old a) <= interval_bits old + interval_bits a.
  Proof.
    intros old a.
    unfold cut_within.
    destruct (cut_shape_ok a); [|cbn [interval_bits]; lia].
    destruct old as [|olo ohi], a as [|lo hi]; cbn [interval_bits]; try lia.
    destruct (cut_endpoint_ok C.bits lo), (cut_endpoint_ok C.bits hi);
      cbn [interval_bits]; lia.
  Qed.

  (** The combined exchange list uses at most the storage of both input lists. *)
  Lemma within_list_bits_le : forall ys olds,
    fold_right Nat.add 0
      (map (fun yx => interval_bits
        (cut_raw (pack_cut C.bits (cut_within C.bits (snd yx) (fst yx)))))
        (combine ys olds)) <=
      fold_right Nat.add 0 (map interval_bits ys) +
      fold_right Nat.add 0 (map interval_bits olds).
  Proof.
    induction ys as [|y ys IH]; intros [|old olds]; cbn [combine map fold_right]; try lia.
    pose proof (pack_cut_bits_le (cut_within C.bits old y)) as Hpack.
    pose proof (cut_within_bits_le old y) as Hwithin.
    specialize (IH olds).
    cbn [fst snd].
    lia.
  Qed.

  (** The raw domain's public storage pin agrees with endpoint bit length. *)
  Lemma raw_size_agrees : forall a, R.size a = interval_bits a.
  Proof.
    intro a.
    rewrite R.size_bits.
    reflexivity.
  Qed.

  (** Summing raw sizes preserves the endpoint-storage view. *)
  Lemma raw_sizes_agree : forall xs,
    fold_right Nat.add 0 (map R.size xs) =
    fold_right Nat.add 0 (map interval_bits xs).
  Proof.
    induction xs as [|a xs IH]; cbn [map fold_right].
    - reflexivity.
    - rewrite raw_size_agrees, IH. reflexivity.
  Qed.

  (** Projecting carrier operands preserves their total endpoint storage. *)
  Lemma projected_bits_agree : forall xs,
    fold_right Nat.add 0 (map interval_bits (map cut_raw xs)) = operand_bits xs.
  Proof.
    intro xs.
    unfold operand_bits.
    rewrite map_map.
    reflexivity.
  Qed.

  (** The bounded work budget adds only its fixed cutoff to the raw work budget. *)
  Lemma raw_work_agrees : forall o xs,
    R.work o (map cut_raw xs) + C.bits = work o xs.
  Proof.
    intros o xs.
    unfold work, transfer_work, operand_bits.
    rewrite RL.raw_work, length_map, map_map.
    unfold t in *.
    lia.
  Qed.

  (** The guard budget extends raw guard work by the fixed cutoff. *)
  Lemma raw_gwork_agrees : forall g xs,
    R.gwork g (map cut_raw xs) + C.bits = gwork g xs.
  Proof.
    intros g xs.
    unfold gwork, guard_work, operand_bits.
    rewrite RL.raw_gwork, length_map, map_map.
    reflexivity.
  Qed.

  (** The bounded widening budget adds its cutoff to the raw threshold budget. *)
  Lemma raw_wsize_agrees : forall q, R.wsize q + C.bits = wsize q.
  Proof.
    intro q.
    rewrite R.F_wsize.
    reflexivity.
  Qed.

  (** Operator work pays for traversing the operand list. *)
  Lemma work_length : forall o xs, length xs <= work o xs.
  Proof.
    intros o xs.
    unfold work, transfer_work, t in *.
    lia.
  Qed.

  (** Guard work pays for traversing the operand list. *)
  Lemma gwork_length : forall g xs, length xs <= gwork g xs.
  Proof.
    intros g xs.
    unfold gwork, guard_work, t in *.
    lia.
  Qed.

  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    pose proof c_val_dominates.
    unfold c_lat.
    lia.
  Qed.

  (** The representation measure counts the largest finite endpoint. *)
  Lemma size_raw : forall a, size a = interval_bits (cut_raw a).
  Proof.
    reflexivity.
  Qed.

  (** The fixed cutoff bounds every value independently of operations and thresholds. *)
  Lemma size_bound : forall a, size a <= C.bits.
  Proof.
    intro a.
    exact (proj2 (carrier_invariant a)).
  Qed.

  (** Forward and backward work includes literals, list traversal and cutoff scans. *)
  Lemma work_agrees : forall o xs, work o xs = transfer_work o xs.
  Proof.
    reflexivity.
  Qed.

  (** Guard work includes operand traversal and cutoff scans. *)
  Lemma gwork_agrees : forall g xs, gwork g xs = guard_work g xs.
  Proof.
    reflexivity.
  Qed.

  (** Widening pays for unrestricted threshold values and their search paths. *)
  Lemma wsize_agrees : forall q,
    wsize q = (T.depth q + 1) * (T.tree_bits q + 1) + C.bits.
  Proof.
    reflexivity.
  Qed.

  (** Each finite side contributes at most one plus the threshold count. *)
  Lemma rank_bound : forall q a, wrank q a <= 2 * (length (T.vals q) + 1).
  Proof.
    intros q a.
    unfold wrank.
    rewrite <- RL.raw_wrank.
    apply R.F3_wrank_le.
  Qed.

  (** Operator work accounts for every operand size. *)
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof.
    intros o xs.
    unfold work, transfer_work, operand_bits, size, t in *.
    lia.
  Qed.

  (** Guard work accounts for every operand size. *)
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    intros g xs.
    unfold gwork, guard_work, operand_bits, size, t in *.
    lia.
  Qed.

  (** Forward results fit within the charged operator work. *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs.
    pose proof (size_bound (forward o xs)) as Hbits.
    assert (Hcutoff : C.bits <= work o xs) by (unfold work, transfer_work; lia).
    pose proof c_val_dominates.
    nia.
  Qed.

  (** Meet results fit within the combined operand sizes. *)
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b.
    pose proof (R.meet_size (cut_raw a) (cut_raw b)) as Hraw.
    rewrite !raw_size_agrees in Hraw.
    pose proof (cut_bits_le (R.meet (cut_raw a) (cut_raw b))) as Hcut.
    change (size (meet a b) <= interval_bits (R.meet (cut_raw a) (cut_raw b))) in Hcut.
    change (N.of_nat (interval_bits (R.meet (cut_raw a) (cut_raw b))) <=
      R.c_val * N.of_nat (size a + size b + 1))%N in Hraw.
    pose proof c_val_dominates.
    nia.
  Qed.

  (** Join results fit within the combined operand sizes. *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b.
    pose proof (R.join_size (cut_raw a) (cut_raw b)) as Hraw.
    rewrite !raw_size_agrees in Hraw.
    pose proof (cut_bits_le (R.join (cut_raw a) (cut_raw b))) as Hcut.
    change (size (join a b) <= interval_bits (R.join (cut_raw a) (cut_raw b))) in Hcut.
    change (N.of_nat (interval_bits (R.join (cut_raw a) (cut_raw b))) <=
      R.c_val * N.of_nat (size a + size b + 1))%N in Hraw.
    pose proof c_val_dominates.
    nia.
  Qed.

  (** Widening results fit within operand and parameter sizes. *)
  Lemma widen_size : forall q a b,
    (N.of_nat (size (widen q a b)) <=
      c_val * N.of_nat (size a + size b + wsize q + 1))%N.
  Proof.
    intros q a b.
    pose proof (size_bound (widen q a b)) as Hbits.
    assert (Hcutoff : C.bits <= wsize q) by (unfold wsize; lia).
    pose proof c_val_dominates.
    nia.
  Qed.

  (** Backward results fit within charged work and request size. *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs.
    assert (Hbits : fold_right Nat.add 0 (map size (backward o r xs)) <=
      fold_right Nat.add 0
        (map interval_bits (R.backward o (cut_raw r) (map cut_raw xs))) +
      fold_right Nat.add 0 (map interval_bits (map cut_raw xs))).
    { unfold backward. rewrite map_map. apply within_list_bits_le. }
    rewrite projected_bits_agree in Hbits.
    pose proof (R.backward_size o (cut_raw r) (map cut_raw xs)) as Hraw.
    rewrite raw_sizes_agree, raw_size_agrees in Hraw.
    pose proof (raw_work_agrees o xs) as Hwork.
    assert (Hinput : operand_bits xs <= work o xs) by (unfold work, transfer_work; lia).
    pose proof c_val_dominates.
    unfold size, t in *.
    nia.
  Qed.

  (** Guard results fit within the charged guard work. *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs.
    assert (Hbits : fold_right Nat.add 0 (map size (guard g xs)) <=
      fold_right Nat.add 0 (map interval_bits (R.guard g (map cut_raw xs))) +
      fold_right Nat.add 0 (map interval_bits (map cut_raw xs))).
    { unfold guard. rewrite map_map. apply within_list_bits_le. }
    rewrite projected_bits_agree in Hbits.
    pose proof (R.guard_size g (map cut_raw xs)) as Hraw.
    rewrite raw_sizes_agree in Hraw.
    pose proof (raw_gwork_agrees g xs) as Hwork.
    assert (Hinput : operand_bits xs <= gwork g xs) by (unfold gwork, guard_work; lia).
    pose proof c_val_dominates.
    unfold t in *.
    nia.
  Qed.

  (** The cutoff pays for shape comparisons and endpoint bit scans. *)
  Lemma T_cut_le : forall a,
    (T_cut a <= c_cut * N.of_nat (interval_bits a + 1))%N.
  Proof.
    intro a.
    pose proof (T_cut_pack a) as Hpack.
    pose proof (T_cut_helper a) as Hcut.
    assert (Hpositive : (1 <= N.of_nat (interval_bits a + 1))%N) by lia.
    unfold c_cut.
    nia.
  Qed.

  (** The value constant covers a raw operation, its cutoff and call overhead. *)
  Lemma c_val_cut_coefficient :
    (R.c_val + c_cut * (R.c_val + 1) + 3 <= c_val)%N.
  Proof.
    unfold c_cut, c_val.
    nia.
  Qed.

  (** The value constant covers one projected raw operation and output scan. *)
  Lemma c_val_source_coefficient :
    (k_cut * (R.c_val + k_cut * (R.c_val + 1) + 2) <= c_val)%N.
  Proof.
    unfold c_val.
    nia.
  Qed.

  (** The value constant covers raw transfer work and every returned cutoff. *)
  Lemma c_val_list_coefficient :
    (k_cut * (R.c_val + (k_cut + 1) * (R.c_val + 2) + 2) <= c_val)%N.
  Proof.
    unfold c_val.
    nia.
  Qed.

  (** A raw operation and its resulting cutoff fit the wrapper constant. *)
  Lemma cut_clock_budget : forall raw_time a budget,
    (1 <= budget)%N ->
    (raw_time <= R.c_val * budget)%N ->
    (N.of_nat (interval_bits a) <= R.c_val * budget)%N ->
    (raw_time + T_cut a + 3 <= c_val * budget)%N.
  Proof.
    intros raw_time a budget Hpositive Htime Hsize.
    pose proof (T_cut_le a) as Hcut.
    assert (Hscan : (T_cut a <= c_cut * ((R.c_val + 1) * budget))%N).
    { eapply N.le_trans; [exact Hcut|]. apply N.mul_le_mono_l. nia. }
    eapply N.le_trans with ((R.c_val + c_cut * (R.c_val + 1) + 3) * budget)%N.
    - nia.
    - apply N.mul_le_mono_r. exact c_val_cut_coefficient.
  Qed.

  (** The source clock's projection traversal and output scan share one work budget. *)
  Lemma source_clock_budget : forall budget raw_time raw_bits cut_time traversal,
    (1 <= budget)%N ->
    (raw_time <= R.c_val * budget)%N ->
    (raw_bits <= R.c_val * budget)%N ->
    (cut_time <= k_cut * (raw_bits + 1))%N ->
    (traversal <= budget)%N ->
    (k_cut * (raw_time + cut_time + traversal + 1) <= c_val * budget)%N.
  Proof.
    intros budget raw_time raw_bits cut_time traversal Hpositive Htime Hsize Hcut Htraversal.
    assert (Hscan : (cut_time <= k_cut * ((R.c_val + 1) * budget))%N).
    { eapply N.le_trans; [exact Hcut|]. apply N.mul_le_mono_l. nia. }
    assert (Hinside :
      (raw_time + cut_time + traversal + 1 <=
        (R.c_val + k_cut * (R.c_val + 1) + 2) * budget)%N) by nia.
    eapply N.le_trans with
      (k_cut * ((R.c_val + k_cut * (R.c_val + 1) + 2) * budget))%N.
    - apply N.mul_le_mono_l. exact Hinside.
    - rewrite N.mul_assoc. apply N.mul_le_mono_r. exact c_val_source_coefficient.
  Qed.

  (** Summing inward scans charges both lists and the traversal of the old operands. *)
  Lemma within_list_clock_le : forall ys olds,
    (fold_right N.add 0%N
      (map (fun yx => (T_cut_within C.bits (snd yx) (fst yx) + 1)%N)
        (combine ys olds)) <=
      (k_cut + 1) * N.of_nat
        (fold_right Nat.add 0%nat (map interval_bits ys) +
          fold_right Nat.add 0%nat (map interval_bits olds) + length olds))%N.
  Proof.
    induction ys as [|y ys IH]; intros [|old olds];
      cbn [combine map fold_right length fst snd]; try lia.
    pose proof (T_cut_within_helper old y) as Hhead.
    specialize (IH olds).
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
    nia.
  Qed.

  (** Returned storage, original storage and list traversal fit one transfer budget. *)
  Lemma source_list_clock_budget : forall budget raw_time raw_bits input_bits traversal scans,
    (1 <= budget)%N ->
    (raw_time <= R.c_val * budget)%N ->
    (raw_bits <= R.c_val * budget)%N ->
    (input_bits <= budget)%N ->
    (traversal <= budget)%N ->
    (scans <= (k_cut + 1) * (raw_bits + input_bits + traversal))%N ->
    (k_cut * (raw_time + scans + traversal + 1) <= c_val * budget)%N.
  Proof.
    intros budget raw_time raw_bits input_bits traversal scans
      Hpositive Htime Hsize Hinput Htraversal Hscans.
    assert (Hstorage :
      (raw_bits + input_bits + traversal <= (R.c_val + 2) * budget)%N) by nia.
    assert (Hscan : (scans <= (k_cut + 1) * ((R.c_val + 2) * budget))%N).
    { eapply N.le_trans; [exact Hscans|]. apply N.mul_le_mono_l. exact Hstorage. }
    assert (Hinside :
      (raw_time + scans + traversal + 1 <=
        (R.c_val + (k_cut + 1) * (R.c_val + 2) + 2) * budget)%N) by nia.
    eapply N.le_trans with
      (k_cut * ((R.c_val + (k_cut + 1) * (R.c_val + 2) + 2) * budget))%N.
    - apply N.mul_le_mono_l. exact Hinside.
    - rewrite N.mul_assoc. apply N.mul_le_mono_r. exact c_val_list_coefficient.
  Qed.

  (** Inclusion testing costs at most the combined abstract sizes. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b.
    pose proof (R.T_leb_le (cut_raw a) (cut_raw b)) as Hraw.
    rewrite !raw_size_agrees in Hraw.
    change (R.T_leb (cut_raw a) (cut_raw b) <=
      R.c_val * N.of_nat (size a + size b + 1))%N in Hraw.
    pose proof c_val_dominates.
    assert (Hpositive : (1 <= N.of_nat (size a + size b + 1))%N) by lia.
    unfold T_leb, T_cut_raw.
    cbn beta iota zeta.
    nia.
  Qed.

  (** Joining costs at most the combined abstract sizes. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b.
    pose proof (R.T_join_le (cut_raw a) (cut_raw b)) as Htime.
    pose proof (R.join_size (cut_raw a) (cut_raw b)) as Hsize.
    rewrite !raw_size_agrees in Htime.
    rewrite !raw_size_agrees in Hsize.
    assert (Hpositive : (1 <= N.of_nat (size a + size b + 1))%N) by lia.
    pose proof (cut_clock_budget (R.T_join (cut_raw a) (cut_raw b))
      (R.join (cut_raw a) (cut_raw b)) (N.of_nat (size a + size b + 1))
      Hpositive Htime Hsize) as Hbudget.
    unfold T_join, T_cut_raw.
    cbn beta iota zeta.
    lia.
  Qed.

  (** Meeting costs at most the combined abstract sizes. *)
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b.
    pose proof (R.T_meet_le (cut_raw a) (cut_raw b)) as Htime.
    pose proof (R.meet_size (cut_raw a) (cut_raw b)) as Hsize.
    rewrite !raw_size_agrees in Htime.
    rewrite !raw_size_agrees in Hsize.
    assert (Hpositive : (1 <= N.of_nat (size a + size b + 1))%N) by lia.
    pose proof (cut_clock_budget (R.T_meet (cut_raw a) (cut_raw b))
      (R.meet (cut_raw a) (cut_raw b)) (N.of_nat (size a + size b + 1))
      Hpositive Htime Hsize) as Hbudget.
    unfold T_meet, T_cut_raw.
    cbn beta iota zeta.
    lia.
  Qed.

  (** Bottom testing costs at most the abstract size. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intro a.
    pose proof (R.T_is_bot_le (cut_raw a)) as Hraw.
    rewrite raw_size_agrees in Hraw.
    change (R.T_is_bot (cut_raw a) <= R.c_val * N.of_nat (size a + 1))%N in Hraw.
    pose proof c_val_dominates.
    assert (Hpositive : (1 <= N.of_nat (size a + 1))%N) by lia.
    unfold T_is_bot, T_cut_raw.
    cbn beta iota zeta.
    nia.
  Qed.

  (** Widening charges both values and the widening parameters. *)
  Lemma T_widen_le : forall q a b,
    (T_widen q a b <= c_val * N.of_nat (size a + size b + wsize q + 1))%N.
  Proof.
    intros q a b.
    pose proof (R.T_widen_le q (cut_raw a) (cut_raw b)) as Htime.
    pose proof (R.widen_size q (cut_raw a) (cut_raw b)) as Hsize.
    rewrite !raw_size_agrees in Htime.
    rewrite !raw_size_agrees in Hsize.
    pose proof (raw_wsize_agrees q) as Hparameter.
    assert (Htime' : (R.T_widen q (cut_raw a) (cut_raw b) <=
      R.c_val * N.of_nat (size a + size b + wsize q + 1))%N).
    { unfold size. nia. }
    assert (Hsize' : (N.of_nat (interval_bits (R.widen q (cut_raw a) (cut_raw b))) <=
      R.c_val * N.of_nat (size a + size b + wsize q + 1))%N).
    { unfold size. nia. }
    assert (Hpositive : (1 <= N.of_nat (size a + size b + wsize q + 1))%N) by lia.
    pose proof (cut_clock_budget (R.T_widen q (cut_raw a) (cut_raw b))
      (R.widen q (cut_raw a) (cut_raw b)) (N.of_nat (size a + size b + wsize q + 1))
      Hpositive Htime' Hsize') as Hbudget.
    unfold T_widen, T_cut_raw.
    cbn beta iota zeta.
    lia.
  Qed.

  (** Narrowing charges both abstract values. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b.
    pose proof (R.T_narrow_le (cut_raw a) (cut_raw b)) as Htime.
    rewrite !raw_size_agrees in Htime.
    pose proof (RL.raw_narrow_bits (cut_raw a) (cut_raw b)) as Hbits.
    pose proof R.c_lat_pos as Hrawpositive.
    change (1 <= R.c_val)%N in Hrawpositive.
    assert (Hsize : (N.of_nat (interval_bits (R.narrow (cut_raw a) (cut_raw b))) <=
      R.c_val * N.of_nat (size a + size b + 1))%N).
    { unfold size. nia. }
    assert (Hpositive : (1 <= N.of_nat (size a + size b + 1))%N) by lia.
    pose proof (cut_clock_budget (R.T_narrow (cut_raw a) (cut_raw b))
      (R.narrow (cut_raw a) (cut_raw b)) (N.of_nat (size a + size b + 1))
      Hpositive Htime Hsize) as Hbudget.
    unfold T_narrow, T_cut_raw.
    cbn beta iota zeta.
    lia.
  Qed.

  (** Forward transfer is bounded by operator work. *)
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs.
    pose proof (R.T_forward_le o (map cut_raw xs)) as Htime.
    pose proof (R.forward_size o (map cut_raw xs)) as Hsize.
    rewrite raw_size_agrees in Hsize.
    pose proof (raw_work_agrees o xs) as Hwork.
    pose proof (work_length o xs) as Hlength.
    pose proof (T_cut_helper (R.forward o (map cut_raw xs))) as Hcut.
    rewrite Nat2N.inj_add in Hcut.
    eapply N.le_trans; [apply T_forward_source|].
    unfold t in *.
    eapply source_clock_budget.
    - lia.
    - eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l. lia.
    - eapply N.le_trans; [exact Hsize|]. apply N.mul_le_mono_l. lia.
    - exact Hcut.
    - lia.
  Qed.

  (** Backward transfer charges operator work and the requested result. *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs.
    pose proof (R.T_backward_le o (cut_raw r) (map cut_raw xs)) as Htime.
    pose proof (R.backward_size o (cut_raw r) (map cut_raw xs)) as Hsize.
    rewrite raw_size_agrees in Htime.
    rewrite raw_sizes_agree, raw_size_agrees in Hsize.
    pose proof (raw_work_agrees o xs) as Hwork.
    pose proof (work_length o xs) as Hlength.
    assert (Hinput : operand_bits xs <= work o xs) by (unfold work, transfer_work; lia).
    pose proof (within_list_clock_le
      (R.backward o (cut_raw r) (map cut_raw xs)) (map cut_raw xs)) as Hscans.
    rewrite projected_bits_agree, length_map, !Nat2N.inj_add in Hscans.
    eapply N.le_trans; [apply T_backward_source|].
    unfold t in *.
    eapply source_list_clock_budget with (input_bits := N.of_nat (operand_bits xs)).
    - lia.
    - eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l. unfold size. lia.
    - eapply N.le_trans; [exact Hsize|]. apply N.mul_le_mono_l. unfold size. lia.
    - lia.
    - lia.
    - exact Hscans.
  Qed.

  (** Guard transfer is bounded by guard work. *)
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs.
    pose proof (R.T_guard_le g (map cut_raw xs)) as Htime.
    pose proof (R.guard_size g (map cut_raw xs)) as Hsize.
    rewrite raw_sizes_agree in Hsize.
    pose proof (raw_gwork_agrees g xs) as Hwork.
    pose proof (gwork_length g xs) as Hlength.
    assert (Hinput : operand_bits xs <= gwork g xs) by (unfold gwork, guard_work; lia).
    pose proof (within_list_clock_le (R.guard g (map cut_raw xs)) (map cut_raw xs)) as Hscans.
    rewrite projected_bits_agree, length_map, !Nat2N.inj_add in Hscans.
    eapply N.le_trans; [apply T_guard_source|].
    unfold t in *.
    eapply source_list_clock_budget with (input_bits := N.of_nat (operand_bits xs)).
    - lia.
    - eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l. lia.
    - eapply N.le_trans; [exact Hsize|]. apply N.mul_le_mono_l. lia.
    - lia.
    - lia.
    - exact Hscans.
  Qed.

End CutIntervalT.
