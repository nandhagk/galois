(** * Tagged word payloads

    Tags attach widths to payloads and represent bottom and top.
    For example, joining values of different widths produces top.
    Builds on: WordSig and BitsLang. *)

From Stdlib Require Import List ZArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Bits Require Import Word.
From Galois.Domains Require Import LangSig WordSig HarnessSig Harness BitsLang.

Module TaggedCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    <: HARNESS_BASE_OPS BitsLangCode.
  Definition t := tagged W.p.
  Definition bot : t := TBot.
  Definition top : t := TAny.
  Definition is_bot (a : t) : bool :=
    match a with
    | TBot => true
    | TVal w p => W.pis_bot w p
    | TAny => false
    end.
  Definition leb (a b : t) : bool :=
    match a, b with
    | TBot, _ => true
    | _, TAny => true
    | TVal w p, TVal v q =>
      if Pos.eqb w v then W.pleb w p q else W.pis_bot w p
    | TVal w p, TBot => W.pis_bot w p
    | _, _ => false
    end.
  Definition join (a b : t) : t :=
    if is_bot a then b else if is_bot b then a else
    match a, b with
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pjoin w p q) else TAny
    | _, _ => TAny
    end.
  Definition meet (a b : t) : t :=
    match a, b with
    | TBot, _ | _, TBot => TBot
    | TAny, _ => b
    | _, TAny => a
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pmeet w p q) else TBot
    end.
  Definition wparam := W.pwparam.
  Definition widen (q : wparam) (a b : t) : t :=
    if leb b a then a else
    match a, b with
    | TBot, _ => b
    | TVal w p, TVal v r =>
      if W.pis_bot w p then b else
      if Pos.eqb w v then TVal w (W.pwiden q w p r) else TAny
    | _, _ => TAny
    end.
  Definition narrow (a b : t) : t :=
    match a, b with
    | TAny, _ => b
    | _, TAny => a
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pnarrow w p q) else TBot
    | _, _ => TBot
    end.
  Definition point (a : t) : option BitsLangCode.val :=
    match a with
    | TVal w p => match W.ppoint w p with Some z => Some (w, z) | None => None end
    | _ => None
    end.
  Definition abst (v : BitsLangCode.val) : t :=
    if Z.eqb (Word.wrap (fst v) (snd v)) (snd v)
    then TVal (fst v) (W.pconst (fst v) (snd v)) else TAny.
End TaggedCode.

Module TaggedTableCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    (T : WORD_TABLE_OPS L W).
  Fixpoint untag (xs : list (tagged W.p)) : option (list (positive * W.p)) :=
    match xs with
    | nil => Some nil
    | TVal w p :: rest =>
      match untag rest with
      | Some ws => Some ((w, p) :: ws)
      | None => None
      end
    | _ => None
    end.

  Fixpoint retag (ws : list positive) (ps : list W.p) : list (tagged W.p) :=
    match ws, ps with
    | w :: rest, p :: tail => TVal w p :: retag rest tail
    | _, _ => nil
    end.

  Definition fwd (o : BitsLangCode.op) (xs : list (tagged W.p)) : option (tagged W.p) :=
    match o with
    | BConst w z =>
      match xs with nil => Some (TVal w (W.pconst w z)) | _ => None end
    | BOp o =>
      match untag xs with
      | Some ws =>
        match Op.result_width o (map fst ws) with
        | Some w => match T.wfwd o w ws with Some p => Some (TVal w p) | None => None end
        | None => None
        end
      | None => None
      end
    end.

  Definition bwd (o : BitsLangCode.op) (r : tagged W.p) (xs : list (tagged W.p))
      : option (list (tagged W.p)) :=
    match o, r, untag xs with
    | BOp o, TVal w p, Some ws =>
      match Op.result_width o (map fst ws) with
      | Some rw =>
        if Pos.eqb w rw then
          match T.wbwd o w p ws with
          | Some ps => Some (retag (map fst ws) ps)
          | None => None
          end
        else None
      | None => None
      end
    | _, _, _ => None
    end.

  Definition grd (_ : BitsLangCode.guard) (_ : list (tagged W.p))
      : option (list (tagged W.p)) := None.
End TaggedTableCode.

Definition tagged_gamma {P : Type} (is_word : positive -> Z -> Prop)
    (pgamma : positive -> P -> Z -> Prop) (a : tagged P) (c : BitsLang.val) : Prop :=
  match a with
  | TBot => False
  | TAny => True
  | TVal w p => fst c = w /\ is_word w (snd c) /\ pgamma w p (snd c)
  end.

Definition tagged_point {P : Type} (ppoint : positive -> P -> option Z) (a : tagged P)
    : option (positive * Z) :=
  match a with
  | TVal w p => match ppoint w p with Some z => Some (w, z) | None => None end
  | _ => None
  end.

Module Type TAGGED_BASE (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) :=
  HARNESS_BASE BitsLang with Definition t := tagged W.p
    with Definition gamma := tagged_gamma L.is_word W.pgamma.

Definition tagged_size {P : Type} (psize : positive -> P -> nat) (a : tagged P) : nat :=
  match a with
  | TVal w p => Pos.to_nat w + psize w p + 1
  | _ => 1
  end.

Definition tagged_abst_work (v : positive * Z) : nat :=
  (Pos.to_nat (fst v) + Z.size_nat (snd v) + 1) ^ 2.

Module Type TAGGED_BASE_T (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L) :=
  HARNESS_BASE_T BitsLangT with Definition t := tagged W.p
    with Definition wparam := W.pwparam
    with Definition gamma := tagged_gamma L.is_word W.pgamma
    with Definition point := tagged_point W.ppoint
    with Definition bsize := tagged_size W.psize
    with Definition wsize := W.pwsize
    with Definition abst_work := tagged_abst_work.

Module Tagged (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) <: HARNESS_BASE BitsLang.
  Include TaggedCode L W.
  Definition gamma := tagged_gamma L.is_word W.pgamma.
  Definition wrank (q : wparam) (a : t) : nat :=
    match a with
    | TBot | TAny => 0
    | TVal w p => S (W.pwrank q w p)
    end.
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros [|w p|]; cbn [leb]; try reflexivity.
    rewrite Pos.eqb_refl. apply W.pleb_refl.
  Qed.

  (** A recognized empty payload is below every tag, including a different width. *)
  Local Lemma bottom_below : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [|w p|] [|v q|] Hbot; cbn [is_bot leb] in *;
      try discriminate; try reflexivity; try exact Hbot.
    destruct (Pos.eqb w v); [now apply W.pis_bot_least|exact Hbot].
  Qed.

  (** Payload bottom recognition descends through the tagged order. *)
  Local Lemma bottom_downward : forall a b,
    leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    intros [|w p|] [|v q|] Hle Hbot; cbn [leb is_bot] in *;
      try discriminate; try reflexivity; try exact Hle.
    destruct (Pos.eqb w v) eqn:Hwidth; [|exact Hle].
    apply Pos.eqb_eq in Hwidth. subst v.
    exact (W.pis_bot_below w p q Hle Hbot).
  Qed.

  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc.
    destruct (is_bot a) eqn:Ha; [now apply bottom_below|].
    destruct (is_bot b) eqn:Hb.
    { pose proof (bottom_downward a b Hab Hb). congruence. }
    destruct a as [|w p|], b as [|v q|], c as [|u r|];
      cbn [is_bot leb] in *; try discriminate; try reflexivity; try congruence.
    destruct (Pos.eqb w v) eqn:Hwv; [|congruence].
    destruct (Pos.eqb v u) eqn:Hvu; [|congruence].
    apply Pos.eqb_eq in Hwv. apply Pos.eqb_eq in Hvu. subst v u.
    rewrite Pos.eqb_refl. exact (W.pleb_trans w p q r Hab Hbc).
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros []; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    exact bottom_below.
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b. unfold join.
    destruct (is_bot a) eqn:Ha; [now apply is_bot_least|].
    destruct (is_bot b) eqn:Hb; [apply leb_refl|].
    destruct a as [|w p|], b as [|v q|];
      cbn [is_bot leb] in *; try discriminate; try reflexivity.
    destruct (Pos.eqb w v); cbn [leb]; [|reflexivity].
    rewrite Pos.eqb_refl. apply W.pjoin_ub_l.
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b. unfold join.
    destruct (is_bot a) eqn:Ha; [apply leb_refl|].
    destruct (is_bot b) eqn:Hb; [now apply is_bot_least|].
    destruct a as [|w p|], b as [|v q|];
      cbn [is_bot leb] in *; try discriminate; try reflexivity.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [leb]; [|reflexivity].
    apply Pos.eqb_eq in Hwidth. subst v.
    rewrite Pos.eqb_refl. apply W.pjoin_ub_r.
  Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros []; reflexivity.
  Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros [|w p|] [|v q|]; cbn [meet leb]; try reflexivity.
    - destruct (Pos.eqb w v); cbn [leb]; [|reflexivity].
      rewrite Pos.eqb_refl. apply W.pmeet_lb_l.
    - rewrite Pos.eqb_refl. apply W.pleb_refl.
  Qed.
  Lemma widen_ub_l : forall q a b, leb a (widen q a b) = true.
  Proof.
    intros q a b. unfold widen.
    destruct (leb b a) eqn:Hba; [apply leb_refl|].
    destruct a as [|w p|], b as [|v r|];
      try apply bot_least; try apply top_greatest; try apply leb_refl.
    destruct (W.pis_bot w p) eqn:Hbot.
    - apply bottom_below. exact Hbot.
    - destruct (Pos.eqb w v); cbn [leb]; [|reflexivity].
      rewrite Pos.eqb_refl. apply W.pwiden_ub_l.
  Qed.
  Lemma widen_ub_r : forall q a b, leb b (widen q a b) = true.
  Proof.
    intros q a b. unfold widen.
    destruct (leb b a) eqn:Hba; [exact Hba|].
    destruct a as [|w p|], b as [|v r|];
      try apply leb_refl; try apply top_greatest.
    destruct (W.pis_bot w p) eqn:Hbot.
    - apply leb_refl.
    - destruct (Pos.eqb w v) eqn:Hwidth; cbn [leb]; [|reflexivity].
      apply Pos.eqb_eq in Hwidth. subst v.
      rewrite Pos.eqb_refl. apply W.pwiden_ub_r.
  Qed.
  Lemma widen_stable : forall q a b, leb b a = true -> widen q a b = a.
  Proof.
    intros q a b Hle. unfold widen. now rewrite Hle.
  Qed.
  Lemma wrank_widen : forall q a b, is_bot a = false -> leb b a = false ->
    (wrank q (widen q a b) < wrank q a)%nat.
  Proof.
    intros q a b Hbot Hle. unfold widen. rewrite Hle.
    destruct a as [|w p|], b as [|v r|];
      cbn [is_bot leb wrank] in Hbot, Hle |- *; try discriminate; try lia.
    rewrite Hbot. destruct (Pos.eqb w v) eqn:Hwidth; cbn [wrank]; [|lia].
    apply Pos.eqb_eq in Hwidth. subst v. rewrite Pos.eqb_refl in Hle.
    pose proof (W.pwrank_widen q w p r Hbot Hle). lia.
  Qed.
  Lemma wrank_widen_le : forall q a b, is_bot a = false -> (wrank q (widen q a b) <= wrank q a)%nat.
  Proof.
    intros q a b Hbot. destruct (leb b a) eqn:Hle.
    - rewrite (widen_stable q a b Hle). lia.
    - pose proof (wrank_widen q a b Hbot Hle). lia.
  Qed.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros [|w p|] [|v r|] Hle; cbn [leb narrow] in Hle |- *;
      try discriminate; try (split; reflexivity).
    - split; [exact Hle|reflexivity].
    - destruct (Pos.eqb v w) eqn:Hwidth.
      + apply Pos.eqb_eq in Hwidth. subst v. rewrite Pos.eqb_refl.
        cbn [leb]. rewrite Pos.eqb_refl. apply W.pnarrow_between. exact Hle.
      + rewrite Pos.eqb_sym, Hwidth. cbn [leb]. split; [exact Hle|reflexivity].
    - split; [rewrite Pos.eqb_refl; apply W.pleb_refl|reflexivity].
  Qed.
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    intros [|w p|] [|v q|] [u z] Hle Hg;
      cbn [leb gamma tagged_gamma] in *; try contradiction; try discriminate; try exact I.
    - destruct Hg as [Hwidth [Hword Hpayload]].
      exact (W.pis_bot_sound w p z Hle Hpayload).
    - destruct Hg as [Huw [Hword Hpayload]].
      destruct (Pos.eqb w v) eqn:Hwv.
      + apply Pos.eqb_eq in Hwv. subst v.
        split; [exact Huw|]. split; [exact Hword|].
        exact (W.pgamma_mono w p q z Hle Hpayload).
      + exfalso. exact (W.pis_bot_sound w p z Hle Hpayload).
  Qed.
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof. intros c Hg. exact Hg. Qed.
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intros c. exact I.
  Qed.
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    intros [|w p|] [|v q|] [u z] Ha Hb;
      cbn [gamma tagged_gamma meet] in *; try contradiction; try assumption.
    destruct Ha as [Huw [Hword Hp]], Hb as [Huv [_ Hq]].
    cbn in Huw, Huv. subst u v.
    rewrite Pos.eqb_refl. cbn [tagged_gamma].
    split; [reflexivity|]. split; [exact Hword|].
    exact (W.pgamma_meet w p q z Hp Hq).
  Qed.
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros [|w p|] [v z] Hbot Hg; cbn [is_bot gamma tagged_gamma] in *;
      try discriminate; try contradiction.
    destruct Hg as [Hwidth [Hword Hpayload]].
    exact (W.pis_bot_sound w p z Hbot Hpayload).
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    exact bottom_downward.
  Qed.
  Lemma point_sound : forall a v c, point a = Some v -> gamma a c -> c = v.
  Proof.
    intros [|w p|] [v x] [u z] Hpoint Hgamma; cbn in Hpoint; try discriminate.
    destruct (W.ppoint w p) as [value|] eqn:Hpayload; [|discriminate].
    inversion Hpoint; subst v x.
    destruct Hgamma as [Hwidth [Hword Hpayload_gamma]]. cbn in Hwidth. subst u.
    f_equal. exact (W.ppoint_sound w p z value Hpayload Hword Hpayload_gamma).
  Qed.
  Lemma abst_sound : forall v, gamma (abst v) v.
  Proof.
    intros [w z]. unfold abst. cbn [fst snd].
    destruct (Z.eqb (Word.wrap w z) z) eqn:Hwrap; [|exact I].
    apply Z.eqb_eq in Hwrap. cbn [gamma tagged_gamma].
    split; [reflexivity|]. split.
    - rewrite <- Hwrap. apply L.wrap_is_word.
    - rewrite <- Hwrap at 2. apply W.pconst_sound.
  Qed.
End Tagged.

Module TaggedTimingHelpers (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L).
  Include Tagged L W.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun point.
  TimeFun abst.

End TaggedTimingHelpers.

Module TaggedT (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    <: TAGGED_BASE_T L W.
  Include TaggedTimingHelpers L W.
  Definition bsize := tagged_size W.psize.
  Definition wsize := W.pwsize.
  Definition abst_work := tagged_abst_work.
  Definition c_base : N := (256 * (W.c_payload + 1))%N.

  (** Width comparison reads at most the numeric value of its left width. *)
  Local Lemma width_compare_time : forall w v,
    (Pos.T_eqb w v <= N.of_nat (Pos.to_nat w))%N.
  Proof.
    intros w v. eapply N.le_trans; [apply Pos.T_eqb_le|].
    apply time_of_nat_le. apply WordTime.positive_size_value.
  Qed.

  (** Tag bottom recognition adds one call to payload bottom recognition. *)
  Local Lemma is_bot_time_bound : forall a,
    (T_is_bot a <= (W.c_payload + 1) * N.of_nat (bsize a + 1))%N.
  Proof.
    intros [|w p|]; time_unfold T_is_bot; time_cbn;
      unfold bsize, tagged_size; rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (W.T_pis_bot_le w p).
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Tag inclusion pays for width comparison and the selected payload test. *)
  Local Lemma leb_time_bound : forall a b,
    (T_leb a b <= 4 * (W.c_payload + 1) * N.of_nat (bsize a + bsize b + 1))%N.
  Proof.
    intros [|w p|] [|v q|]; time_unfold T_leb; time_cbn;
      unfold bsize, tagged_size; rewrite ?Nat2N.inj_add; time_cbn; try nia.
    - pose proof (W.T_pis_bot_le w p).
      rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
    - pose proof (width_compare_time w v) as Hwidth.
      destruct (Pos.eqb w v) eqn:Hsame.
      + apply Pos.eqb_eq in Hsame. subst v.
        pose proof (W.T_pleb_le w p q).
        rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
      + pose proof (W.T_pis_bot_le w p).
        rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_leb_le : forall a b, (T_leb a b <= c_base * N.of_nat ((bsize a + bsize b + 1)%nat))%N.
  Proof.
    intros a b. pose proof (leb_time_bound a b). unfold c_base. nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_join_le : forall a b, (T_join a b <= c_base * N.of_nat ((bsize a + bsize b +
    1)%nat))%N.
  Proof.
    intros a b. pose proof (is_bot_time_bound a) as Ha.
    pose proof (is_bot_time_bound b) as Hb. time_unfold T_join.
    destruct (is_bot a).
    { unfold c_base. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia. }
    destruct (is_bot b).
    { unfold c_base. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia. }
    destruct a as [|w p|], b as [|v q|];
      unfold bsize, tagged_size, c_base in *; time_cbn_all;
      rewrite ?Nat2N.inj_add in *; time_cbn_all; try nia.
    pose proof (width_compare_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame. subst v. pose proof (W.T_pjoin_le w p q).
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_meet_le : forall a b, (T_meet a b <= c_base * N.of_nat ((bsize a + bsize b +
    1)%nat))%N.
  Proof.
    intros [|w p|] [|v q|]; time_unfold T_meet; time_cbn;
      unfold bsize, tagged_size, c_base;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (width_compare_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame. subst v. pose proof (W.T_pmeet_le w p q).
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_narrow_le : forall a b, (T_narrow a b <= c_base * N.of_nat ((bsize a + bsize b +
    1)%nat))%N.
  Proof.
    intros [|w p|] [|v q|]; time_unfold T_narrow; time_cbn;
      unfold bsize, tagged_size, c_base;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (width_compare_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame. subst v. pose proof (W.T_pnarrow_le w p q).
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_base * N.of_nat ((bsize a + 1)%nat))%N.
  Proof.
    intro a. pose proof (is_bot_time_bound a). unfold c_base. nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_point_le : forall a, (T_point a <= c_base * N.of_nat ((bsize a + 1)%nat))%N.
  Proof.
    intros [|w p|]; time_unfold T_point; time_cbn;
      unfold bsize, tagged_size, c_base;
      rewrite ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (W.T_ppoint_le w p).
    rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_base * N.of_nat ((bsize a + bsize b + wsize p + 1)%nat))%N.
  Proof.
    intros param a b. pose proof (leb_time_bound b a) as Hleb.
    time_unfold T_widen. destruct (leb b a).
    { unfold c_base. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia. }
    destruct a as [|w p|], b as [|v q|];
      unfold bsize, tagged_size, wsize, c_base in *; time_cbn_all;
      rewrite ?Nat2N.inj_add in *; time_cbn_all; try nia.
    pose proof (W.T_pis_bot_le w p) as Hbot.
    destruct (W.pis_bot w p).
    { rewrite ?Nat2N.inj_add in *; time_cbn_all; nia. }
    pose proof (width_compare_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame.
    - apply Pos.eqb_eq in Hsame. subst v. pose proof (W.T_pwiden_le param w p q).
      rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
    - rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma meet_size_le : forall a b,
    (N.of_nat (bsize (meet a b)) <= c_base * N.of_nat (bsize a + bsize b + 1))%N.
  Proof.
    intros [|w p|] [|v q|]; unfold meet, bsize, tagged_size, c_base;
      time_cbn; rewrite ?Nat2N.inj_add; time_cbn; try nia.
    destruct (Pos.eqb w v) eqn:Hsame; [|time_cbn; nia].
    apply Pos.eqb_eq in Hsame. subst v. pose proof (W.pmeet_size w p q).
    time_cbn. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma join_size_le : forall a b,
    (N.of_nat (bsize (join a b)) <= c_base * N.of_nat (bsize a + bsize b + 1))%N.
  Proof.
    intros a b. unfold join. destruct (is_bot a).
    { unfold c_base. rewrite ?Nat2N.inj_add. time_cbn. nia. }
    destruct (is_bot b).
    { unfold c_base. rewrite ?Nat2N.inj_add. time_cbn. nia. }
    destruct a as [|w p|], b as [|v q|]; unfold bsize, tagged_size, c_base;
      time_cbn; rewrite ?Nat2N.inj_add; time_cbn; try nia.
    destruct (Pos.eqb w v) eqn:Hsame; [|time_cbn; nia].
    apply Pos.eqb_eq in Hsame. subst v. pose proof (W.pjoin_size w p q).
    time_cbn. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma widen_size_le : forall p a b,
    (N.of_nat (bsize (widen p a b)) <= c_base * N.of_nat (bsize a + bsize b + wsize p + 1))%N.
  Proof.
    intros param a b. unfold widen. destruct (leb b a).
    { unfold c_base. rewrite ?Nat2N.inj_add. time_cbn. nia. }
    destruct a as [|w p|], b as [|v q|]; unfold bsize, tagged_size, wsize, c_base;
      time_cbn; rewrite ?Nat2N.inj_add; time_cbn; try nia.
    destruct (W.pis_bot w p); [time_cbn; nia|].
    destruct (Pos.eqb w v) eqn:Hsame; [|time_cbn; nia].
    apply Pos.eqb_eq in Hsame. subst v. pose proof (W.pwiden_size param w p q).
    time_cbn. rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma T_abst_le : forall v,
    (T_abst v <= c_base * N.of_nat (abst_work v + 1))%N.
  Proof.
    intros [w z]. pose proof (WordTime.word_wrap_time_bound w z) as Hwrap.
    pose proof (W.T_pconst_le w z) as Hconst.
    pose proof (Z.T_eqb_le (Word.wrap w z) z) as Hcompare.
    assert (Hsize : (N.of_nat (Z.size_nat (Word.wrap w z)) <=
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N).
    { apply WordTime.time_square_floor; [|lia].
      pose proof (WordTime.word_wrap_size_bound w z). lia. }
    set (budget := N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2)) in *.
    change (T_abst (w, z) <= 256 * (W.c_payload + 1) *
      N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2) + 1))%N.
    rewrite Nat2N.inj_add.
    change (T_abst (w, z) <= 256 * (W.c_payload + 1) * (budget + 1))%N.
    time_unfold T_abst. unfold Datatypes.T_fst, Datatypes.T_snd.
    time_cbn. destruct (Z.eqb (Word.wrap w z) z); nia.
  Qed.
  (** The operation stays within the declared work budget. *)
  Lemma abst_size_le : forall v,
    (N.of_nat (bsize (abst v)) <= c_base * N.of_nat (abst_work v + 1))%N.
  Proof.
    intros [w z]. pose proof (W.pconst_size w z) as Hconst.
    assert (Hwidth : (N.of_nat (Pos.to_nat w) <=
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N).
    { apply WordTime.time_square_floor; lia. }
    set (budget := N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2)) in *.
    change (N.of_nat (bsize (abst (w, z))) <= 256 * (W.c_payload + 1) *
      N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2) + 1))%N.
    rewrite Nat2N.inj_add.
    change (N.of_nat (bsize (abst (w, z))) <=
      256 * (W.c_payload + 1) * (budget + 1))%N.
    unfold abst, bsize, tagged_size.
    time_cbn. destruct (Z.eqb (Word.wrap w z) z);
      time_cbn; rewrite ?Nat2N.inj_add; time_cbn; nia.
  Qed.
End TaggedT.

Module TaggedTable (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) (T : WORD_TABLE L W)
    (B : TAGGED_BASE L W) <: TABLE BitsLang B.
  Include TaggedTableCode L W T.

  (** Removing tags retains each concrete operand's width and payload meaning. *)
  Local Lemma untag_sound : forall xs cs wps,
    Forall2 B.gamma xs cs -> untag xs = Some wps ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs.
  Proof.
    intros xs cs wps Hfacts. revert wps.
    induction Hfacts as [|x [v z] xs cs Hhead Htail IH]; intros wps Htags.
    - inversion Htags. constructor.
    - destruct x as [|w p|]; cbn [untag] in Htags; try discriminate.
      destruct (untag xs) as [tail|] eqn:Huntag; [|discriminate].
      inversion Htags; subst wps. constructor.
      + change (v = w /\ L.is_word w z /\ W.pgamma w p z) in Hhead.
        destruct Hhead as [Hwidth [Hword Hpayload]]. subst v.
        split; [reflexivity|]. split; assumption.
      + apply IH. reflexivity.
  Qed.

  (** Related payload lists carry the concrete operand widths in order. *)
  Local Lemma payload_widths : forall wps cs,
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs -> map fst wps = map fst cs.
  Proof.
    intros wps cs Hfacts.
    induction Hfacts as [|wp c wps cs [Hwidth Hpayload] Htail IH]; cbn; congruence.
  Qed.

  (** Retagging restores the checked width around every refined payload. *)
  Local Lemma retag_sound : forall ws ps cs,
    Forall2 (fun w c => fst c = w /\ L.is_word w (snd c)) ws cs ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c)) (combine ws ps) cs ->
    (length ws <= length ps)%nat -> Forall2 B.gamma (retag ws ps) cs.
  Proof.
    intros ws ps cs Hwidths. revert ps.
    induction Hwidths as [|w c ws cs Hhead Htail IH]; intros ps Hpayloads Hlength.
    - destruct ps; constructor.
    - destruct ps as [|p ps]; cbn in Hlength; [lia|].
      inversion Hpayloads as [|wp c' pairs cs' Hp Hps]; subst.
      cbn [retag]. constructor.
      + change (fst c = w /\ L.is_word w (snd c) /\ W.pgamma w p (snd c)).
        destruct Hhead as [Hwidth Hword]. split; [exact Hwidth|].
        split; [exact Hword|exact Hp].
      + apply IH; [exact Hps|lia].
  Qed.

  Lemma fwd_sound : forall o xs cs c r, fwd o xs = Some r ->
    Forall2 B.gamma xs cs -> BitsLang.eval o cs = Some c -> B.gamma r c.
  Proof.
    intros [w z|o] xs cs c r Hentry Hfacts Heval.
    - destruct xs as [|x xs]; cbn [fwd] in Hentry; [|discriminate].
      inversion Hentry; subst r. inversion Hfacts; subst cs.
      inversion Heval; subst c.
      change (w = w /\ L.is_word w (L.wrap w z) /\
        W.pgamma w (W.pconst w z) (L.wrap w z)).
      split; [reflexivity|]. split; [apply L.wrap_is_word|apply W.pconst_sound].
    - cbn [fwd] in Hentry.
      destruct (untag xs) as [wps|] eqn:Htags; [|discriminate].
      destruct (Op.result_width o (map fst wps)) as [rw|] eqn:Hwidth; [|discriminate].
      destruct (T.wfwd o rw wps) as [p|] eqn:Hpayload; [|discriminate].
      inversion Hentry; subst r. destruct c as [cw z].
      change (L.eval_op o cs = Some (cw, z)) in Heval.
      pose proof (untag_sound xs cs wps Hfacts Htags) as Hoperands.
      pose proof (L.eval_op_is_word o cs cw z Heval) as [Hword Hresult].
      rewrite <- (payload_widths wps cs Hoperands) in Hresult.
      change (Op.result_width o (map fst wps) = Some cw) in Hresult.
      rewrite Hwidth in Hresult. inversion Hresult; subst cw.
      change (rw = rw /\ L.is_word rw z /\ W.pgamma rw p z).
      split; [reflexivity|]. split; [exact Hword|].
      exact (T.wfwd_sound o rw wps cs z p Hpayload Hoperands Heval).
  Qed.

  Lemma bwd_sound : forall o r xs ys cs c, bwd o r xs = Some ys ->
    Forall2 B.gamma xs cs -> BitsLang.eval o cs = Some c -> B.gamma r c ->
    Forall2 B.gamma ys cs.
  Proof.
    intros [w z|o] r xs ys cs c Hentry Hfacts Heval Hr;
      [discriminate Hentry|].
    destruct r as [|w p|]; cbn [bwd] in Hentry; try discriminate.
    destruct (untag xs) as [wps|] eqn:Htags; [|discriminate].
    destruct (Op.result_width o (map fst wps)) as [rw|] eqn:Hwidth; [|discriminate].
    destruct (Pos.eqb w rw) eqn:Hwr; [|discriminate].
    apply Pos.eqb_eq in Hwr. subst rw.
    destruct (T.wbwd o w p wps) as [ps|] eqn:Hpayload; [|discriminate].
    inversion Hentry; subst ys. destruct c as [cw z].
    change (L.eval_op o cs = Some (cw, z)) in Heval.
    change (cw = w /\ L.is_word w z /\ W.pgamma w p z) in Hr.
    destruct Hr as [Hcw [Hword Hr]]. subst cw.
    pose proof (untag_sound xs cs wps Hfacts Htags) as Hoperands.
    pose proof (T.wbwd_sound o w p wps ps cs z Hpayload Hoperands Heval Hr) as Hresult.
    apply retag_sound.
    - clear - Hoperands.
      induction Hoperands as [|[v q] c wps cs [Hwc [Hnormal Hq]] Htail IH];
        cbn; constructor.
      + cbn in Hwc, Hnormal. split; [symmetry; exact Hwc|].
        now rewrite Hwc.
      + exact IH.
    - exact Hresult.
    - rewrite length_map.
      pose proof (Forall2_length Hoperands) as Hop_length.
      pose proof (Forall2_length Hresult) as Hr_length.
      rewrite length_combine, length_map in Hr_length.
      change (length wps <= length ps)%nat.
      change (length wps = length cs) in Hop_length.
      change (Nat.min (length wps) (length ps) = length cs) in Hr_length.
      rewrite Hop_length, <- Hr_length. apply Nat.le_min_r.
  Qed.

  Lemma grd_sound : forall g xs ys cs, grd g xs = Some ys ->
    Forall2 B.gamma xs cs -> BitsLang.holds g cs -> Forall2 B.gamma ys cs.
  Proof.
    intros g xs ys cs Hentry. discriminate Hentry.
  Qed.
End TaggedTable.

Module TaggedTableTimingHelpers (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W).
  Include TaggedTableCode L W T.
  TimeFun untag.
  TimeFun retag.
  TimeFun fwd.
  TimeFun bwd.
  TimeFun grd.
End TaggedTableTimingHelpers.

Module TaggedWordPlan (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W) <: WORD_PLAN L W T.
  Include TaggedTableCode L W T.
  TimeFun untag.
  TimeFun retag.

  Definition tagged_wrank (q : W.pwparam) (a : tagged W.p) : nat :=
    match a with
    | TBot | TAny => 0
    | TVal w p => 1 + W.pwrank q w p
    end.
  Definition k_untag : N := 1%N.
  Definition k_retag : N := 1%N.
  Definition tagged_gamma (a : tagged W.p) (c : positive * Z) : Prop :=
    match a with
    | TBot => False
    | TAny => True
    | TVal w p => fst c = w /\ L.is_word w (snd c) /\ W.pgamma w p (snd c)
    end.
  Lemma F1_untag_sound : forall xs cs wps,
    Forall2 tagged_gamma xs cs -> untag xs = Some wps ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs.
  Proof.
    intros xs cs wps Hfacts. revert wps.
    induction Hfacts as [|x [v z] xs cs Hhead Htail IH]; intros wps Htags.
    - inversion Htags. constructor.
    - destruct x as [|w p|]; cbn [untag] in Htags; try discriminate.
      destruct (untag xs) as [tail|] eqn:Huntag; [|discriminate].
      inversion Htags; subst wps. constructor.
      + cbn [tagged_gamma] in Hhead.
        destruct Hhead as [Hwidth [Hword Hpayload]]. cbn in Hwidth. subst v.
        split; [reflexivity|]. split; assumption.
      + apply IH. reflexivity.
  Qed.
  Lemma F2_retag_sound : forall ws ps cs,
    Forall2 (fun w c => fst c = w /\ L.is_word w (snd c)) ws cs ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c)) (combine ws ps) cs ->
    (length ws <= length ps)%nat -> Forall2 tagged_gamma (retag ws ps) cs.
  Proof.
    intros ws ps cs Hwidths. revert ps.
    induction Hwidths as [|w c ws cs Hhead Htail IH]; intros ps Hpayloads Hlength.
    - destruct ps; constructor.
    - destruct ps as [|p ps]; cbn in Hlength; [lia|].
      inversion Hpayloads as [|wp c' pairs cs' Hp Hps]; subst.
      cbn [retag]. constructor.
      + cbn [tagged_gamma]. destruct Hhead as [Hwidth Hword].
        split; [exact Hwidth|]. split; [exact Hword|exact Hp].
      + apply IH; [exact Hps|lia].
  Qed.
  (** Untagging charges at most one call per operand and one final call. *)
  Lemma T1_untag : forall xs,
    (T_untag xs <= k_untag * N.of_nat ((length xs + 1)%nat))%N.
  Proof.
    unfold k_untag. induction xs as [|x xs IH].
    - time_step.
    - destruct x as [|w p|]; time_unfold T_untag; cbn [length];
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all; lia.
  Qed.

  (** Retagging charges one call per paired position and one final call. *)
  Lemma T2_retag : forall ws ps,
    (T_retag ws ps <= k_retag * N.of_nat ((length ws + length ps + 1)%nat))%N.
  Proof.
    unfold k_retag. induction ws as [|w ws IH]; intros [|p ps];
      time_unfold T_retag; cbn [length];
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ; time_cbn; try lia.
    specialize (IH ps). rewrite ?Nat2N.inj_add in IH. time_cbn_all. lia.
  Qed.
End TaggedWordPlan.

Module WordDomain (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) (T : WORD_TABLE L W).
  Module B := Tagged L W.
  Module Table := TaggedTable L W T B.
  Module Domain := Harness BitsLang B Table.
End WordDomain.

Module TaggedTableT (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W) (B : TAGGED_BASE_T L W) <: TABLE_T BitsLangT B.
  Include TaggedTable L W T B.
  TimeFun untag.
  TimeFun retag.
  TimeFun fwd.
  TimeFun bwd.
  TimeFun grd.

  Definition operand_sizes (xs : list B.t) : nat :=
    fold_right Nat.add 0%nat (map B.bsize xs).
  Definition operand_widths (xs : list B.t) : nat :=
    fold_right Nat.add 0%nat
      (map (fun x => match x with TVal w _ => Pos.to_nat w | _ => 0%nat end) xs).
  Definition twork (o : BitsLangT.op) (xs : list B.t) : nat :=
    operand_sizes xs + length xs +
    match o with
    | BConst w z => (Pos.to_nat w + Z.size_nat z + 1%nat) ^ 2
    | BOp o => (Op.op_widths o + operand_widths xs + 1%nat) ^ 2
    end.
  Definition tgwork (_ : BitsLangT.guard) (xs : list B.t) : nat :=
    operand_sizes xs + length xs + 1%nat.
  Definition c_tab : N := (1000000 * (T.c_word_table + W.c_payload + 1))%N.

  (** Successful untagging exposes the widths and payload sizes charged by the operands. *)
  Local Lemma untag_sizes xs ws : untag xs = Some ws ->
    operand_widths xs = fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) ws) /\
    operand_sizes xs =
      fold_right Nat.add 0%nat (map (fun x =>
        (Pos.to_nat (fst x) + W.psize (fst x) (snd x) + 1)%nat) ws) /\
    length xs = length ws.
  Proof.
    revert ws.
    induction xs as [|x xs IH]; intros ws Htag.
    - inversion Htag; subst. repeat split; reflexivity.
    - destruct x as [|w p|]; cbn [untag] in Htag; try discriminate.
      destruct (untag xs) as [tail|] eqn:Htail; [|discriminate].
      inversion Htag; subst ws.
      specialize (IH tail eq_refl) as [Hwidth [Hsize Hlength]].
      unfold operand_widths, operand_sizes in *.
      cbn [map fold_right length]. rewrite Hwidth, Hsize, Hlength.
      repeat split; reflexivity.
  Qed.

  (** Each tagged operand pays for one list position. *)
  Local Lemma operand_length xs : (length xs <= operand_sizes xs)%nat.
  Proof.
    induction xs as [|x xs IH]; [reflexivity|].
    assert (Hunit : (1 <= B.bsize x)%nat).
    { destruct x as [|w p|].
      - change (B.bsize TBot) with 1%nat. lia.
      - change (B.bsize (TVal w p)) with
          (Pos.to_nat w + W.psize w p + 1)%nat.
        pose proof (Pos2Nat.is_pos w). lia.
      - change (B.bsize TAny) with 1%nat. lia. }
    change (operand_sizes (x :: xs)) with (B.bsize x + operand_sizes xs)%nat.
    cbn [length]. lia.
  Qed.

  (** The derived untag clock makes one visit per tagged operand. *)
  Local Lemma untag_time xs :
    (T_untag xs <= N.of_nat (length xs + 1))%N.
  Proof.
    induction xs as [|x xs IH].
    - time_step.
    - destruct x as [|w p|]; time_unfold T_untag; cbn [length];
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all; lia.
  Qed.

  (** Retagging visits at most the paired positions and one final list cell. *)
  Local Lemma retag_time ws ps :
    (T_retag ws ps <= N.of_nat (length ws + length ps + 1))%N.
  Proof.
    revert ps.
    induction ws as [|w ws IH]; intros [|p ps];
      time_unfold T_retag; cbn [length];
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ; time_cbn; try lia.
    specialize (IH ps). rewrite ?Nat2N.inj_add in IH. time_cbn_all. lia.
  Qed.

  (** Payload sizes are part of the size of each tagged operand. *)
  Local Lemma payload_sum_le ws :
    (fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) ws) <=
      fold_right Nat.add 0%nat (map (fun x =>
        (Pos.to_nat (fst x) + W.psize (fst x) (snd x) + 1)%nat) ws))%nat.
  Proof.
    induction ws as [|[w p] ws IH]; cbn [map fold_right]; lia.
  Qed.

  (** A checked result width and the payloads fit within four table work units. *)
  Local Lemma table_budget o xs ws rw :
    untag xs = Some ws -> Op.result_width o (map fst ws) = Some rw ->
    (((Pos.to_nat rw +
      fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) ws) + 1) ^ 2 +
      fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) ws))%nat <=
      4 * (twork (BOp o) xs + 1))%nat.
  Proof.
    intros Htag Hwidth.
    pose proof (untag_sizes xs ws Htag) as [Hws [Hsize Hlength]].
    pose proof (WordTime.result_width_size_bound o (map fst ws) rw Hwidth) as Hr.
    rewrite map_map in Hr.
    pose proof (payload_sum_le ws) as Hpayload.
    rewrite <- Hsize in Hpayload.
    cbn [twork].
    rewrite <- Hws in Hr.
    rewrite <- Hws.
    set (base := (Op.op_widths o + operand_widths xs + 1)%nat) in *.
    set (target := (Pos.to_nat rw + operand_widths xs + 1)%nat) in *.
    assert (Hscaled : (target <= 2 * base)%nat).
    { unfold target, base. lia. }
    assert (Hsquare : (target ^ 2 <= 4 * base ^ 2)%nat).
    { assert (Hmono : (target ^ 2 <= (2 * base) ^ 2)%nat).
      { apply Nat.pow_le_mono_l. exact Hscaled. }
      rewrite !Nat.pow_2_r in Hmono.
      rewrite !Nat.pow_2_r. nia. }
    change ((target ^ 2 +
      fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) ws))%nat <=
      4 * (operand_sizes xs + length xs + base ^ 2 + 1))%nat.
    lia.
  Qed.

  (** A requested payload adds its size to the checked word-table budget. *)
  Local Lemma backward_table_budget o xs ws w p :
    untag xs = Some ws -> Op.result_width o (map fst ws) = Some w ->
    (((Pos.to_nat w +
      fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) ws) + 1) ^ 2 +
      W.psize w p +
      fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) ws))%nat <=
      4 * (twork (BOp o) xs + B.bsize (TVal w p) + 1))%nat.
  Proof.
    intros Htag Hwidth.
    pose proof (table_budget o xs ws w Htag Hwidth) as Hbase.
    change (B.bsize (TVal w p)) with (Pos.to_nat w + W.psize w p + 1)%nat.
    lia.
  Qed.

  (** Comparing a requested result width costs at most that width. *)
  Local Lemma width_compare_time w v :
    (Pos.T_eqb w v <= N.of_nat (Pos.to_nat w))%N.
  Proof.
    eapply N.le_trans; [apply Pos.T_eqb_le|].
    apply time_of_nat_le. apply WordTime.positive_size_value.
  Qed.

  (** Reading the width of each untagged operand has linear clock. *)
  Local Lemma width_map_time ws :
    (ListDef.T_map (@fst positive W.p)
      (fun x => @Datatypes.T_fst positive W.p x) ws <=
      2 * N.of_nat (length ws) + 1)%N.
  Proof.
    pose proof (ListDef.T_map_le (@fst positive W.p)
      (fun x => @Datatypes.T_fst positive W.p x) 1 ws
      ltac:(intros [w p]; time_step)) as Hmap.
    nia.
  Qed.
  (** The entry stays within its declared work budget. *)
  Lemma T_fwd_le : forall o xs, (T_fwd o xs <= c_tab * N.of_nat ((twork o xs + 1)%nat))%N.
  Proof.
    intros [w z|o] xs.
    - destruct xs as [|x xs]; time_unfold T_fwd; unfold c_tab, twork;
        time_cbn; pose proof (W.T_pconst_le w z) as Hconst;
        rewrite ?Nat2N.inj_add in *; time_cbn_all; nia.
    - pose proof (untag_time xs) as Huntag.
      pose proof (operand_length xs) as Hlength.
      time_unfold T_fwd.
      destruct (untag xs) as [ws|] eqn:Htag.
      + pose proof (untag_sizes xs ws Htag) as [Hwidth [Hsize Hlen]].
        pose proof (width_map_time ws) as Hmap.
        pose proof (WordTime.result_width_time_bound o (map fst ws)) as Hrwtime.
        rewrite map_map in Hrwtime. rewrite <- Hwidth in Hrwtime.
        destruct (Op.result_width o (map fst ws)) as [rw|] eqn:Hrw.
        * pose proof (table_budget o xs ws rw Htag Hrw) as Hbudget.
          pose proof (T.T_wfwd_le o rw ws) as Htable.
          apply time_of_nat_le in Hbudget.
          rewrite Nat2N.inj_mul in Hbudget.
          time_cbn_all.
          set (budget := N.of_nat (twork (BOp o) xs + 1)).
          assert (Hlinear : (N.of_nat (length xs + 1) <= budget)%N).
          { unfold budget.
            change (N.of_nat (length xs + 1) <= N.of_nat
              (operand_sizes xs + length xs +
                (Op.op_widths o + operand_widths xs + 1) ^ 2 + 1))%N.
            apply time_of_nat_le. lia. }
          rewrite Nat2N.inj_add in Hlinear.
          assert (Hpositive : (1 <= budget)%N) by nia.
          assert (Hsquare :
            (N.of_nat ((Op.op_widths o + operand_widths xs + 1) ^ 2) <= budget)%N).
          { unfold budget.
            change (N.of_nat ((Op.op_widths o + operand_widths xs + 1) ^ 2) <= N.of_nat
              (operand_sizes xs + length xs +
                (Op.op_widths o + operand_widths xs + 1) ^ 2 + 1))%N.
            apply time_of_nat_le. lia. }
          assert (Htable_budget :
            (T.T_wfwd o rw ws <= 4 * T.c_word_table * budget)%N).
          { eapply N.le_trans; [exact Htable|].
            replace (4 * T.c_word_table * budget)%N with
              (T.c_word_table * (4 * budget))%N by nia.
            apply N.mul_le_mono_l.
            unfold budget. exact Hbudget. }
          assert (Hmap_budget :
            (ListDef.T_map (@fst positive W.p)
              (fun x => @Datatypes.T_fst positive W.p x) ws <= 3 * budget)%N).
          { rewrite <- Hlen in Hmap. nia. }
          assert (Hrw_budget :
            (Op.T_result_width o (map fst ws) <= 128 * budget)%N).
          { eapply N.le_trans; [exact Hrwtime|].
            apply N.mul_le_mono_l. exact Hsquare. }
          change (1 + (T_untag xs +
            (ListDef.T_map (@fst positive W.p)
              (fun x => @Datatypes.T_fst positive W.p x) ws +
              Op.T_result_width o (map fst ws) + T.T_wfwd o rw ws)) <=
            c_tab * budget)%N.
          rewrite Nat2N.inj_add in Huntag.
          clear - Huntag Hlinear Hpositive Hmap_budget Hrw_budget Htable_budget.
          eapply N.le_trans with (m := ((4 * T.c_word_table + 133) * budget)%N).
          -- rewrite N.mul_add_distr_r. lia.
          -- apply N.mul_le_mono_r. unfold c_tab. nia.
        * time_cbn_all.
          set (budget := N.of_nat (twork (BOp o) xs + 1)).
          assert (Hlinear : (N.of_nat (length xs + 1) <= budget)%N).
          { unfold budget.
            change (N.of_nat (length xs + 1) <= N.of_nat
              (operand_sizes xs + length xs +
                (Op.op_widths o + operand_widths xs + 1) ^ 2 + 1))%N.
            apply time_of_nat_le. lia. }
          assert (Hsquare :
            (N.of_nat ((Op.op_widths o + operand_widths xs + 1) ^ 2) <= budget)%N).
          { unfold budget.
            change (N.of_nat ((Op.op_widths o + operand_widths xs + 1) ^ 2) <= N.of_nat
              (operand_sizes xs + length xs +
                (Op.op_widths o + operand_widths xs + 1) ^ 2 + 1))%N.
            apply time_of_nat_le. lia. }
          rewrite Nat2N.inj_add in Hlinear.
          assert (Hmap_budget :
            (ListDef.T_map (@fst positive W.p)
              (fun x => @Datatypes.T_fst positive W.p x) ws <= 3 * budget)%N).
          { rewrite <- Hlen in Hmap. nia. }
          assert (Hrw_budget :
            (Op.T_result_width o (map fst ws) <= 128 * budget)%N).
          { eapply N.le_trans; [exact Hrwtime|].
            apply N.mul_le_mono_l. exact Hsquare. }
          eapply N.le_trans with (m := (3 + T_untag xs +
            ListDef.T_map (@fst positive W.p)
              (fun x => @Datatypes.T_fst positive W.p x) ws +
            Op.T_result_width o (map fst ws))%N); [lia|].
          rewrite Nat2N.inj_add in Huntag.
          assert (Hpositive : (1 <= budget)%N) by lia.
          clear - Huntag Hlinear Hpositive Hmap_budget Hrw_budget.
          eapply N.le_trans with (m := (135 * budget)%N).
          -- lia.
          -- apply N.mul_le_mono_r. unfold c_tab. nia.
      + time_cbn_all.
        set (budget := N.of_nat (twork (BOp o) xs + 1)).
        assert (Hlinear : (N.of_nat (length xs + 1) <= budget)%N).
        { unfold budget.
          change (N.of_nat (length xs + 1) <= N.of_nat
            (operand_sizes xs + length xs +
              (Op.op_widths o + operand_widths xs + 1) ^ 2 + 1))%N.
          apply time_of_nat_le. lia. }
        rewrite Nat2N.inj_add in Hlinear.
        rewrite Nat2N.inj_add in Huntag.
        eapply N.le_trans with (m := (3 + T_untag xs)%N); [lia|].
        assert (Hpositive : (1 <= budget)%N) by lia.
        clear - Huntag Hlinear Hpositive.
        eapply N.le_trans with (m := (4 * budget)%N).
        * lia.
        * apply N.mul_le_mono_r. unfold c_tab. nia.
  Qed.

  (** Untagging and width checking fit within the requested backward work. *)
  Local Lemma backward_prefix_time o w p xs ws : untag xs = Some ws ->
    (T_untag xs +
      ListDef.T_map (@fst positive W.p)
        (fun x => @Datatypes.T_fst positive W.p x) ws +
      Op.T_result_width o (map fst ws) <=
      132 * N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N.
  Proof.
    intro Htag.
    pose proof (untag_sizes xs ws Htag) as [Hwidth [_ Hlen]].
    pose proof (untag_time xs) as Huntag.
    pose proof (width_map_time ws) as Hmap.
    pose proof (WordTime.result_width_time_bound o (map fst ws)) as Hrwtime.
    rewrite map_map in Hrwtime. rewrite <- Hwidth in Hrwtime.
    rewrite <- Hlen in Hmap.
    set (budget := N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1)).
    assert (Hlinear : (N.of_nat (length xs + 1) <= budget)%N).
    { unfold budget.
      change (N.of_nat (length xs + 1) <= N.of_nat
        (operand_sizes xs + length xs +
          (Op.op_widths o + operand_widths xs + 1) ^ 2 +
          (Pos.to_nat w + W.psize w p + 1) + 1))%N.
      apply time_of_nat_le. lia. }
    assert (Hsquare :
      (N.of_nat ((Op.op_widths o + operand_widths xs + 1) ^ 2) <= budget)%N).
    { unfold budget.
      change (N.of_nat ((Op.op_widths o + operand_widths xs + 1) ^ 2) <= N.of_nat
        (operand_sizes xs + length xs +
          (Op.op_widths o + operand_widths xs + 1) ^ 2 +
          (Pos.to_nat w + W.psize w p + 1) + 1))%N.
      apply time_of_nat_le. lia. }
    rewrite Nat2N.inj_add in Hlinear, Huntag.
    clear - Huntag Hmap Hrwtime Hlinear Hsquare.
    lia.
  Qed.

  (** A backward table call fits four times its declared coefficient and work. *)
  Local Lemma backward_payload_time o w p xs ws :
    untag xs = Some ws -> Op.result_width o (map fst ws) = Some w ->
    (T.T_wbwd o w p ws <= 4 * T.c_word_table *
      N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N.
  Proof.
    intros Htag Hwidth.
    pose proof (T.T_wbwd_le o w p ws) as Htime.
    pose proof (backward_table_budget o xs ws w p Htag Hwidth) as Hbudget.
    apply time_of_nat_le in Hbudget. rewrite Nat2N.inj_mul in Hbudget.
    eapply N.le_trans; [exact Htime|].
    replace (4 * T.c_word_table *
      N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N with
      (T.c_word_table *
        (4 * N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1)))%N by nia.
    apply N.mul_le_mono_l. exact Hbudget.
  Qed.

  (** A returned backward payload list has bounded length. *)
  Local Lemma backward_payload_length o w p xs ws ps :
    untag xs = Some ws -> Op.result_width o (map fst ws) = Some w ->
    T.wbwd o w p ws = Some ps ->
    (N.of_nat (length ps) <= 4 * T.c_word_table *
      N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N.
  Proof.
    intros Htag Hwidth Hresult.
    pose proof (T.wbwd_size_le o w p ws ps Hresult) as Hsize.
    pose proof (backward_table_budget o xs ws w p Htag Hwidth) as Hbudget.
    apply time_of_nat_le in Hbudget. rewrite Nat2N.inj_mul in Hbudget.
    eapply N.le_trans; [|eapply N.le_trans; [exact Hsize|]].
    - apply time_of_nat_le. lia.
    - replace (4 * T.c_word_table *
        N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N with
        (T.c_word_table *
          (4 * N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1)))%N by nia.
      apply N.mul_le_mono_l. exact Hbudget.
  Qed.

  (** Backward work pays for every operand and the requested result width. *)
  Local Lemma backward_work_linear o w p xs :
    (N.of_nat (length xs + 1) <=
      N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N /\
    (N.of_nat (Pos.to_nat w) <=
      N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1))%N.
  Proof.
    change (B.bsize (TVal w p)) with (Pos.to_nat w + W.psize w p + 1)%nat.
    split; apply time_of_nat_le; unfold twork; cbn; lia.
  Qed.

  (** Every table budget pays for one clock unit. *)
  Local Lemma table_budget_positive o r xs :
    (1 <= c_tab * N.of_nat (twork o xs + B.bsize r + 1))%N.
  Proof.
    assert (Hcoefficient : (1 <= c_tab)%N) by (unfold c_tab; nia).
    assert (Hwork : (1 <= N.of_nat (twork o xs + B.bsize r + 1))%N).
    { change (N.of_nat 1 <= N.of_nat (twork o xs + B.bsize r + 1))%N.
      apply time_of_nat_le. lia. }
    nia.
  Qed.
  (** The initial untag pass fits every backward work budget. *)
  Local Lemma backward_untag_budget op r xs :
    (N.of_nat (length xs + 1) <=
      N.of_nat (twork op xs + B.bsize r + 1))%N.
  Proof.
    apply time_of_nat_le.
    destruct op, r; unfold twork; cbn [B.bsize]; lia.
  Qed.
  (** The entry stays within its declared work budget. *)
  Lemma T_bwd_le : forall o r xs,
    (T_bwd o r xs <= c_tab * N.of_nat ((twork o xs + B.bsize r + 1)%nat))%N.
  Proof.
    intros op result xs.
    pose proof (table_budget_positive op result xs) as Hunit.
    pose proof (backward_untag_budget op result xs) as Hinitial.
    pose proof (untag_time xs) as Hinitial_time.
    assert (Hinitial_positive :
      (1 <= N.of_nat (twork op xs + B.bsize result + 1))%N).
    { change (N.of_nat 1 <= N.of_nat
        (twork op xs + B.bsize result + 1))%N.
      apply time_of_nat_le. lia. }
    assert (Hshort :
      (3 + T_untag xs <=
        c_tab * N.of_nat (twork op xs + B.bsize result + 1))%N).
    { eapply N.le_trans with
        (m := (4 * N.of_nat (twork op xs + B.bsize result + 1))%N).
      - assert (Hvisit :
          (T_untag xs <=
            N.of_nat (twork op xs + B.bsize result + 1))%N).
        { eapply N.le_trans; [exact Hinitial_time|exact Hinitial]. }
        lia.
      - apply N.mul_le_mono_r. unfold c_tab. nia. }
    destruct op as [cw cz|o], result as [|w p|];
      time_unfold T_bwd; time_cbn;
      try solve [cbn in Hunit |- *; lia].
    pose proof (untag_time xs) as Huntag.
    pose proof (backward_work_linear o w p xs) as [Hlinear Hwidth].
    set (budget := N.of_nat (twork (BOp o) xs + B.bsize (TVal w p) + 1)).
    change (N.of_nat (length xs + 1) <= budget)%N in Hlinear.
    change (N.of_nat (Pos.to_nat w) <= budget)%N in Hwidth.
    rewrite Nat2N.inj_add in Hlinear at 1.
    rewrite Nat2N.inj_add in Huntag.
    assert (Hpositive : (1 <= budget)%N) by lia.
    destruct (untag xs) as [ws|] eqn:Htag; time_cbn_all.
    - pose proof (backward_prefix_time o w p xs ws Htag) as Hprefix.
      change (T_untag xs +
        ListDef.T_map (@fst positive W.p)
          (fun x => @Datatypes.T_fst positive W.p x) ws +
        Op.T_result_width o (map fst ws) <= 132 * budget)%N in Hprefix.
      destruct (Op.result_width o (map fst ws)) as [rw|] eqn:Hrw; time_cbn_all.
      + pose proof (width_compare_time w rw) as Hcompare.
        assert (Hcompare_budget : (Pos.T_eqb w rw <= budget)%N).
        { eapply N.le_trans; [exact Hcompare|exact Hwidth]. }
        clear Hcompare. rename Hcompare_budget into Hcompare.
        destruct (Pos.eqb w rw) eqn:Hsame; time_cbn_all.
        * apply Pos.eqb_eq in Hsame. subst rw.
          pose proof (backward_payload_time o w p xs ws Htag Hrw) as Htable.
          change (T.T_wbwd o w p ws <=
            4 * T.c_word_table * budget)%N in Htable.
          destruct (T.wbwd o w p ws) as [ps|] eqn:Hback; time_cbn_all.
          -- pose proof (backward_payload_length o w p xs ws ps Htag Hrw Hback)
               as Hpayload_length.
             pose proof (retag_time (map fst ws) ps) as Hretag.
             pose proof (width_map_time ws) as Hmap.
             pose proof (untag_sizes xs ws Htag) as [_ [_ Hlen]].
             pose proof (backward_work_linear o w p xs) as [Hxs _].
             rewrite Nat2N.inj_add in Hxs at 1.
             change (N.of_nat (length xs) + N.of_nat 1 <= budget)%N in Hxs.
             change (N.of_nat (length ps) <=
               4 * T.c_word_table * budget)%N in Hpayload_length.
             rewrite length_map in Hretag.
             rewrite <- Hlen in Hretag, Hmap.
             rewrite !Nat2N.inj_add in Hretag.
             assert (Hretag_budget :
               (T_retag (map fst ws) ps <=
                 (1 + 4 * T.c_word_table) * budget)%N).
             { eapply N.le_trans; [exact Hretag|].
               eapply N.le_trans with
                 (m := (budget + 4 * T.c_word_table * budget)%N).
               - lia.
               - nia. }
             assert (Hmap_budget :
               (ListDef.T_map (@fst positive W.p)
                 (fun x => @Datatypes.T_fst positive W.p x) ws <= 3 * budget)%N)
               by lia.
             eapply N.le_trans with (m := (5 +
               (T_untag xs +
                ListDef.T_map (@fst positive W.p)
                  (fun x => @Datatypes.T_fst positive W.p x) ws +
                Op.T_result_width o (map fst ws)) +
               Pos.T_eqb w w + T.T_wbwd o w p ws +
               ListDef.T_map (@fst positive W.p)
                 (fun x => @Datatypes.T_fst positive W.p x) ws +
               T_retag (map fst ws) ps)%N); [lia|].
             clear - Hprefix Hcompare Htable Hretag_budget Hmap_budget Hpositive.
             eapply N.le_trans with
               (m := ((142 + 8 * T.c_word_table) * budget)%N).
             ++ rewrite N.mul_add_distr_r. lia.
             ++ apply N.mul_le_mono_r. unfold c_tab. nia.
          -- eapply N.le_trans with (m := (3 +
               (T_untag xs +
                ListDef.T_map (@fst positive W.p)
                  (fun x => @Datatypes.T_fst positive W.p x) ws +
                Op.T_result_width o (map fst ws)) +
               Pos.T_eqb w w + T.T_wbwd o w p ws)%N); [lia|].
             clear - Hprefix Hcompare Htable Hpositive.
             eapply N.le_trans with
               (m := ((137 + 4 * T.c_word_table) * budget)%N).
             ++ rewrite N.mul_add_distr_r. lia.
             ++ apply N.mul_le_mono_r. unfold c_tab. nia.
        * eapply N.le_trans with (m := (3 +
            (T_untag xs +
             ListDef.T_map (@fst positive W.p)
               (fun x => @Datatypes.T_fst positive W.p x) ws +
             Op.T_result_width o (map fst ws)) +
            Pos.T_eqb w rw)%N); [lia|].
          clear - Hprefix Hcompare Hpositive.
          eapply N.le_trans with (m := (136 * budget)%N).
          -- lia.
          -- apply N.mul_le_mono_r. unfold c_tab. nia.
      + eapply N.le_trans with (m := (3 +
          T_untag xs +
          ListDef.T_map (@fst positive W.p)
            (fun x => @Datatypes.T_fst positive W.p x) ws +
          Op.T_result_width o (map fst ws))%N); [lia|].
        clear - Hprefix Hpositive.
        eapply N.le_trans with (m := (135 * budget)%N).
        * lia.
        * apply N.mul_le_mono_r. unfold c_tab. nia.
    - eapply N.le_trans with (m := (3 + T_untag xs)%N); [lia|].
      clear - Huntag Hlinear Hpositive.
      eapply N.le_trans with (m := (4 * budget)%N).
      + lia.
      + apply N.mul_le_mono_r. unfold c_tab. nia.
  Qed.
  (** The entry stays within its declared work budget. *)
  Lemma T_grd_le : forall g xs, (T_grd g xs <= c_tab * N.of_nat ((tgwork g xs + 1)%nat))%N.
  Proof.
    intros g xs.
    assert (Hwork : (1 <= N.of_nat (tgwork g xs + 1))%N).
    { change (N.of_nat 1 <= N.of_nat (tgwork g xs + 1))%N.
      apply time_of_nat_le. lia. }
    time_unfold T_grd. time_cbn.
    unfold c_tab. nia.
  Qed.
  (** A pointed tagged operand exposes exactly its stored width. *)
  Local Lemma pointed_widths xs cs :
    Forall2 (fun x c => B.point x = Some c) xs cs ->
    operand_widths xs =
      fold_right Nat.add 0%nat (map (fun c => Pos.to_nat (fst c)) cs).
  Proof.
    intro Hpoints.
    induction Hpoints as [|x c xs cs Hpoint Htail IH]; [reflexivity|].
    change (tagged_point W.ppoint x = Some c) in Hpoint.
    destruct x as [|w p|]; cbn [tagged_point] in Hpoint; try discriminate.
    destruct (W.ppoint w p) as [z|] eqn:Hp; [|discriminate].
    inversion Hpoint; subst c.
    cbn [operand_widths map fold_right fst].
    unfold operand_widths in IH. rewrite IH. reflexivity.
  Qed.
  (** The entry stays within its declared work budget. *)
  Lemma T_abst_le : forall v xs o cs, BitsLangT.eval o cs = Some v ->
    Forall2 (fun x c => B.point x = Some c) xs cs ->
    (N.of_nat (B.abst_work v) <= c_tab * N.of_nat ((twork o xs + 1)%nat))%N.
  Proof.
    intros [w z] xs [cw cz|o] cs Heval Hpoints.
    - destruct cs as [|c cs]; cbn [BitsLangT.eval BitsLangCode.eval] in Heval;
        [|discriminate].
      inversion Hpoints; subst xs.
      inversion Heval; subst w z.
      change (B.abst_work (cw, Word.wrap cw cz)) with
        ((Pos.to_nat cw + Z.size_nat (Word.wrap cw cz) + 1) ^ 2)%nat.
      pose proof (WordTime.word_wrap_size_bound cw cz) as Hsize.
      set (base := (Pos.to_nat cw + Z.size_nat cz + 1)%nat).
      assert (Hscaled :
        (Pos.to_nat cw + Z.size_nat (Word.wrap cw cz) + 1 <=
          2 * base)%nat) by (unfold base; lia).
      assert (Hsquare :
        ((Pos.to_nat cw + Z.size_nat (Word.wrap cw cz) + 1) ^ 2 <=
          4 * base ^ 2)%nat).
      { pose proof (Nat.pow_le_mono_l _ _ 2 Hscaled) as Hmono.
        rewrite !Nat.pow_2_r in Hmono |- *. nia. }
      apply time_of_nat_le in Hsquare.
      rewrite Nat2N.inj_mul in Hsquare.
      eapply N.le_trans; [exact Hsquare|].
      change (4 * N.of_nat (base ^ 2) <=
        c_tab * N.of_nat (twork (BConst cw cz) nil + 1))%N.
      unfold twork, c_tab, base. cbn [operand_sizes length].
      rewrite Nat2N.inj_add. nia.
    - change (L.eval_op o cs = Some (w, z)) in Heval.
      pose proof (L.eval_op_is_word o cs w z Heval) as [Hword Hresult].
      pose proof (pointed_widths xs cs Hpoints) as Hwidths.
      pose proof (WordTime.word_size_bound w z Hword) as Hsize.
      pose proof (WordTime.result_width_size_bound o (map fst cs) w Hresult)
        as Hresult_width.
      rewrite map_map in Hresult_width.
      change (Pos.to_nat w <= Op.op_widths o +
        fold_right Nat.add 0%nat
          (map (fun c : positive * Z => Pos.to_nat (fst c)) cs) + 1)%nat
        in Hresult_width.
      rewrite <- Hwidths in Hresult_width.
      set (base := (Op.op_widths o + operand_widths xs + 1)%nat).
      assert (Hscaled :
        (Pos.to_nat w + Z.size_nat z + 1 <= 3 * base)%nat)
        by (unfold base; lia).
      assert (Hsquare :
        ((Pos.to_nat w + Z.size_nat z + 1) ^ 2 <= 9 * base ^ 2)%nat).
      { pose proof (Nat.pow_le_mono_l _ _ 2 Hscaled) as Hmono.
        rewrite !Nat.pow_2_r in Hmono |- *. nia. }
      apply time_of_nat_le in Hsquare.
      rewrite Nat2N.inj_mul in Hsquare.
      change (B.abst_work (w, z)) with
        ((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat.
      eapply N.le_trans; [exact Hsquare|].
      change (9 * N.of_nat (base ^ 2) <=
        c_tab * N.of_nat (twork (BOp o) xs + 1))%N.
      unfold twork, c_tab, base.
      rewrite Nat2N.inj_add. nia.
  Qed.
  (** A successful forward payload fits four table coefficients of caller work. *)
  Local Lemma forward_payload_size o xs ws w p :
    untag xs = Some ws -> Op.result_width o (map fst ws) = Some w ->
    T.wfwd o w ws = Some p ->
    (N.of_nat (W.psize w p) <=
      4 * T.c_word_table * N.of_nat (twork (BOp o) xs + 1))%N.
  Proof.
    intros Htag Hwidth Hresult.
    pose proof (T.wfwd_size_le o w ws p Hresult) as Hsize.
    pose proof (table_budget o xs ws w Htag Hwidth) as Hbudget.
    apply time_of_nat_le in Hbudget. rewrite Nat2N.inj_mul in Hbudget.
    eapply N.le_trans; [exact Hsize|].
    replace (4 * T.c_word_table * N.of_nat (twork (BOp o) xs + 1))%N with
      (T.c_word_table *
        (4 * N.of_nat (twork (BOp o) xs + 1)))%N by nia.
    apply N.mul_le_mono_l. exact Hbudget.
  Qed.

  (** A checked forward result width is charged by the caller work. *)
  Local Lemma forward_width_size o xs ws w :
    untag xs = Some ws -> Op.result_width o (map fst ws) = Some w ->
    (N.of_nat (Pos.to_nat w + 1) <=
      N.of_nat (twork (BOp o) xs + 1))%N.
  Proof.
    intros Htag Hwidth.
    pose proof (untag_sizes xs ws Htag) as [Hws _].
    pose proof (WordTime.result_width_size_bound o (map fst ws) w Hwidth) as Hr.
    rewrite map_map in Hr. rewrite <- Hws in Hr.
    set (base := (Op.op_widths o + operand_widths xs + 1)%nat).
    assert (Hbase : (1 <= base)%nat) by (unfold base; lia).
    assert (Hbound : (Pos.to_nat w + 1 <= base ^ 2 + 1)%nat).
    { rewrite Nat.pow_2_r. unfold base in Hr. nia. }
    apply time_of_nat_le.
    change (Pos.to_nat w + 1 <=
      operand_sizes xs + length xs + base ^ 2 + 1)%nat.
    lia.
  Qed.
  (** The entry stays within its declared work budget. *)
  Lemma fwd_size_le : forall o xs r, fwd o xs = Some r ->
    (N.of_nat (B.bsize r) <= c_tab * N.of_nat (twork o xs + 1))%N.
  Proof.
    intros [w z|o] xs r Hresult.
    - destruct xs as [|x xs]; cbn [fwd] in Hresult; [|discriminate].
      inversion Hresult; subst r.
      pose proof (W.pconst_size w z) as Hpayload.
      set (base := (Pos.to_nat w + Z.size_nat z + 1)%nat).
      assert (Hwidth :
        (N.of_nat (Pos.to_nat w + 1) <= N.of_nat (base ^ 2))%N).
      { apply time_of_nat_le. rewrite Nat.pow_2_r. unfold base. nia. }
      rewrite Nat2N.inj_add in Hwidth at 1.
      change (N.of_nat (W.psize w (W.pconst w z)) <=
        W.c_payload * N.of_nat (base ^ 2))%N in Hpayload.
      change (N.of_nat (Pos.to_nat w + W.psize w (W.pconst w z) + 1) <=
        c_tab * N.of_nat (twork (BConst w z) nil + 1))%N.
      rewrite Nat2N.inj_add at 1.
      rewrite Nat2N.inj_add at 1.
      assert (Hbase :
        (N.of_nat (base ^ 2) <=
          N.of_nat (twork (BConst w z) nil + 1))%N).
      { apply time_of_nat_le. unfold twork, base.
        cbn [operand_sizes length]. lia. }
      eapply N.le_trans with
        (m := ((W.c_payload + 1) * N.of_nat (base ^ 2))%N).
      + eapply N.le_trans with
          (m := (N.of_nat (base ^ 2) +
            W.c_payload * N.of_nat (base ^ 2))%N).
        * lia.
        * nia.
      + eapply N.le_trans with
          (m := ((W.c_payload + 1) *
            N.of_nat (twork (BConst w z) nil + 1))%N).
        * apply N.mul_le_mono_l. exact Hbase.
        * apply N.mul_le_mono_r. unfold c_tab. nia.
    - cbn [fwd] in Hresult.
      destruct (untag xs) as [ws|] eqn:Htag; [|discriminate].
      destruct (Op.result_width o (map fst ws)) as [w|] eqn:Hwidth;
        [|discriminate].
      destruct (T.wfwd o w ws) as [p|] eqn:Hpayload; [|discriminate].
      inversion Hresult; subst r.
      pose proof (forward_payload_size o xs ws w p Htag Hwidth Hpayload)
        as Hpayload_size.
      pose proof (forward_width_size o xs ws w Htag Hwidth) as Hwidth_size.
      set (budget := N.of_nat (twork (BOp o) xs + 1)).
      change (N.of_nat (W.psize w p) <=
        4 * T.c_word_table * budget)%N in Hpayload_size.
      change (N.of_nat (Pos.to_nat w + 1) <= budget)%N in Hwidth_size.
      rewrite Nat2N.inj_add in Hwidth_size at 1.
      change (N.of_nat (Pos.to_nat w + W.psize w p + 1) <=
        c_tab * budget)%N.
      rewrite Nat2N.inj_add at 1.
      rewrite Nat2N.inj_add at 1.
      eapply N.le_trans with
        (m := ((1 + 4 * T.c_word_table) * budget)%N).
      + eapply N.le_trans with
          (m := (budget + 4 * T.c_word_table * budget)%N).
        * lia.
        * nia.
      + apply N.mul_le_mono_r. unfold c_tab. nia.
  Qed.
  (** The entry stays within its declared work budget. *)
  Lemma bwd_size_le : forall o r xs ys, bwd o r xs = Some ys ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <=
      c_tab * N.of_nat (twork o xs + B.bsize r + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The entry stays within its declared work budget. *)
  Lemma grd_size_le : forall g xs ys, grd g xs = Some ys ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <=
      c_tab * N.of_nat (tgwork g xs + 1))%N.
  Proof.
    intros g xs ys Hresult. cbn [grd] in Hresult. discriminate.
  Qed.
End TaggedTableT.

Module WordDomainT (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L) (T : WORD_TABLE_T L W).
  Module B := TaggedT L W.
  Module Table := TaggedTableT L W T B.
  Module Domain := HarnessT BitsLangT B Table.
End WordDomainT.
