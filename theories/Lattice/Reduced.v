(** * Reduced products

    A descending reducer normalises comparisons and joins while widening stays unreduced.
    For example, a boolean reducer can clear the second slot when the first is false.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Lattice Require Import LatticeSig Product.

Module ReducedCode (A B : BLATTICE_OPS) (R : REDUCER_OPS A B) <: BLATTICE_OPS.
  Definition t := (A.t * B.t)%type.
  Definition leb (x y : t) :=
    let r := R.reduce x in andb (A.leb (fst r) (fst y)) (B.leb (snd r) (snd y)).
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot (x : t) := andb (A.is_bot (fst x)) (B.is_bot (snd x)).
  Definition join (x y : t) := R.reduce (A.join (fst x) (fst y), B.join (snd x) (snd y)).
  Definition top : t := (A.top, B.top).
  Definition meet (x y : t) : t := (A.meet (fst x) (fst y), B.meet (snd x) (snd y)).
End ReducedCode.

Module Reduced (A B : BLATTICE) (R : REDUCER A B) <: BLATTICE.
  Include ReducedCode A B R.
  Module P := Product A B.

  Local Lemma reduce_lower_pair x : P.leb (R.reduce x) x = true.
  Proof. destruct x as [a b]; unfold P.leb; apply andb_true_iff; apply R.reduce_lower. Qed.

  Local Lemma reduce_mono_pair x y : P.leb x y = true -> P.leb (R.reduce x) (R.reduce y) = true.
  Proof.
    destruct x as [a b], y as [c d]; unfold P.leb; cbn.
    rewrite !andb_true_iff. intros [Ha Hb]. apply R.reduce_mono; assumption.
  Qed.

  Local Lemma reduce_idem_pair x : P.leb (R.reduce x) (R.reduce (R.reduce x)) = true.
  Proof. destruct x as [a b]; unfold P.leb; apply andb_true_iff; apply R.reduce_idem. Qed.

  Local Lemma leb_pair x y : leb x y = P.leb (R.reduce x) y.
  Proof. reflexivity. Qed.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; rewrite leb_pair; apply reduce_lower_pair. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc. rewrite !leb_pair in *.
    eapply P.leb_trans; [apply reduce_idem_pair|].
    eapply P.leb_trans; [apply reduce_mono_pair; exact Hab|exact Hbc].
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intro a; rewrite leb_pair; eapply P.leb_trans; [apply reduce_lower_pair|apply P.bot_least]. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. apply P.is_bot_bot. Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Ha. rewrite leb_pair. eapply P.leb_trans; [apply reduce_lower_pair|].
    apply P.is_bot_least; exact Ha.
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros a b; rewrite leb_pair; apply reduce_mono_pair, P.join_ub_l. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros a b; rewrite leb_pair; apply reduce_mono_pair, P.join_ub_r. Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intros a; rewrite leb_pair; unfold P.leb, top; cbn; rewrite A.top_greatest, B.top_greatest; reflexivity. Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros a b; rewrite leb_pair; eapply P.leb_trans; [apply reduce_lower_pair|].
    unfold P.leb, meet; cbn; rewrite A.meet_lb_l, B.meet_lb_l; reflexivity.
  Qed.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof.
    intros a b; rewrite leb_pair; eapply P.leb_trans; [apply reduce_lower_pair|].
    unfold P.leb, meet; cbn; rewrite A.meet_lb_r, B.meet_lb_r; reflexivity.
  Qed.
End Reduced.

Module ReducedT (A B : BLATTICE_T) (SA : JOIN_SIZE A) (SB : JOIN_SIZE B)
    (R : REDUCER_T A B) <: BLATTICE_T.
  Include Reduced A B R.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.

  Definition size (x : t) : nat := A.size (fst x) + B.size (snd x) + 1.
  Definition c_lat : N := (8 * (A.c_lat + B.c_lat + 1) * (R.c_reduce + 1))%N.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. unfold c_lat; nia. Qed.

  Local Lemma c_lat_base : (A.c_lat + B.c_lat + 8 <= c_lat)%N.
  Proof. unfold c_lat; nia. Qed.

  Local Lemma c_lat_scale n : ((A.c_lat + B.c_lat + 8) * n <= c_lat * n)%N.
  Proof. apply N.mul_le_mono_r. exact c_lat_base. Qed.

  Lemma T_leb_le : forall a b, (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d].
    time_unfold @T_leb. destruct (R.reduce (a, b)) as [ra rb] eqn:Hreduced.
    cbn [fst snd]. time_simpl; time_cbn.
    remember (N.of_nat (size (a, b) + size (c, d) + 1)) as u eqn:Hu.
    assert (Hu1 : (1 <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (Hinput : (N.of_nat (A.size a + B.size b + 1) <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (HrightA : (N.of_nat (A.size c + 1) <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (HrightB : (N.of_nat (B.size d + 1) <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (Hsize : (N.of_nat (A.size ra + B.size rb) <= R.c_reduce * u)%N).
    { pose proof (R.reduce_size_le a b) as Hsize0. rewrite Hreduced in Hsize0.
      cbn [fst snd] in Hsize0. eapply N.le_trans; [exact Hsize0 |].
      apply N.mul_le_mono_l. exact Hinput. }
    remember ((R.c_reduce + 1) * u)%N as budget eqn:Hbudget.
    assert (Hbudget1 : (1 <= budget)%N) by (rewrite Hbudget; nia).
    assert (HAsize : (N.of_nat (A.size ra + A.size c + 1) <= budget)%N).
    { rewrite Hbudget, N.mul_add_distr_r, N.mul_1_l.
      rewrite !Nat2N.inj_add in Hsize, HrightA |- *. lia. }
    assert (HBsize : (N.of_nat (B.size rb + B.size d + 1) <= budget)%N).
    { rewrite Hbudget, N.mul_add_distr_r, N.mul_1_l.
      rewrite !Nat2N.inj_add in Hsize, HrightB |- *. lia. }
    assert (HA : (A.T_leb ra c <= A.c_lat * budget)%N).
    { eapply N.le_trans; [apply A.T_leb_le |]. apply N.mul_le_mono_l. exact HAsize. }
    assert (HB : (B.T_leb rb d <= B.c_lat * budget)%N).
    { eapply N.le_trans; [apply B.T_leb_le |]. apply N.mul_le_mono_l. exact HBsize. }
    assert (HR : (R.T_reduce (a, b) <= budget)%N).
    { eapply N.le_trans; [apply R.T_reduce_le |].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinput |].
      rewrite Hbudget. nia. }
    replace (c_lat * u)%N with (8 * (A.c_lat + B.c_lat + 1) * budget)%N
      by (rewrite Hbudget; unfold c_lat; nia).
    nia.
  Qed.
  Lemma T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d].
    time_unfold @T_join. cbn [fst snd]. time_simpl; time_cbn.
    remember (N.of_nat (size (a, b) + size (c, d) + 1)) as u eqn:Hu.
    assert (Hu1 : (1 <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (HinputA : (N.of_nat (A.size a + A.size c + 1) <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (HinputB : (N.of_nat (B.size b + B.size d + 1) <= u)%N).
    { rewrite Hu. unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (HA : (A.T_join a c <= A.c_lat * u)%N).
    { eapply N.le_trans; [apply A.T_join_le |]. apply N.mul_le_mono_l. exact HinputA. }
    assert (HB : (B.T_join b d <= B.c_lat * u)%N).
    { eapply N.le_trans; [apply B.T_join_le |]. apply N.mul_le_mono_l. exact HinputB. }
    assert (HAsize : (N.of_nat (A.size (A.join a c)) <= A.c_lat * u)%N).
    { eapply N.le_trans; [apply SA.join_size |]. apply N.mul_le_mono_l. exact HinputA. }
    assert (HBsize : (N.of_nat (B.size (B.join b d)) <= B.c_lat * u)%N).
    { eapply N.le_trans; [apply SB.join_size |]. apply N.mul_le_mono_l. exact HinputB. }
    remember ((A.c_lat + B.c_lat + 1) * u)%N as budget eqn:Hbudget.
    assert (Hbudget1 : (1 <= budget)%N) by (rewrite Hbudget; nia).
    assert (Hjoin : (A.T_join a c + B.T_join b d <= budget)%N)
      by (rewrite Hbudget; nia).
    assert (Hsize : (N.of_nat (A.size (A.join a c) + B.size (B.join b d) + 1) <= budget)%N).
    { rewrite Hbudget. rewrite !Nat2N.inj_add. nia. }
    assert (HR : (R.T_reduce (A.join a c, B.join b d) <= R.c_reduce * budget)%N).
    { eapply N.le_trans; [apply R.T_reduce_le |]. apply N.mul_le_mono_l. exact Hsize. }
    replace (c_lat * u)%N with (8 * (R.c_reduce + 1) * budget)%N
      by (rewrite Hbudget; unfold c_lat; nia).
    nia.
  Qed.
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros [a b]. pose proof (A.T_is_bot_le a) as HA. pose proof (B.T_is_bot_le b) as HB.
    pose proof (c_lat_scale (N.of_nat (size (a, b) + 1))) as Hscale.
    time_unfold @T_is_bot. unfold size in *. cbn [fst snd] in *. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
  Lemma T_meet_le : forall a b, (T_meet a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d]. pose proof (A.T_meet_le a c) as HA. pose proof (B.T_meet_le b d) as HB.
    pose proof (c_lat_scale (N.of_nat (size (a, b) + size (c, d) + 1))) as Hscale.
    time_unfold @T_meet. unfold size in *. cbn [fst snd] in *. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
End ReducedT.

Module ReducedHeight (A B : BLATTICE) (R : REDUCER A B)
    (P : LATTICE with Definition t := (A.t * B.t)%type
                  with Definition leb :=
                    (fun x y => andb (A.leb (fst x) (fst y)) (B.leb (snd x) (snd y))))
    (H : HEIGHT P)
    (Lat : BLATTICE with Definition t := (A.t * B.t)%type
                     with Definition leb :=
                       (fun x y => let r := R.reduce x in
                         andb (A.leb (fst r) (fst y)) (B.leb (snd r) (snd y))))
    <: HEIGHT Lat.
  Definition rank (x : Lat.t) := H.rank (R.reduce x).
  Definition height := H.height.

  Lemma rank_le : forall a, rank a <= height.
  Proof. intro a; apply H.rank_le. Qed.

  (** Reduction preserves the rank order of comparable pairs. *)
  Lemma rank_mono : forall a b, Lat.leb a b = true -> rank a <= rank b.
  Proof. Admitted. (* STUB *)

  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof. Admitted. (* CONVERT: reduced_height: the dictionary carrier changed *)
End ReducedHeight.
