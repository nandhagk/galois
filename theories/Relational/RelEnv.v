(** * Relational and value-state composition

    Relational environments combine a numeric state with a value state.
    For example, a numeric range query can refine an interval value.

    Main results
    - [eval_complexity] Evaluation is linear in the work of both components.
    - [assign_complexity] Assignment is linear in the work of both components.
    - [havoc_complexity] Havoc is linear in the work of both components.
    - [assume_complexity] Assumption is linear in the work of both components.

    Builds on: RelEnvSig, NumStateSig, StateSig and ValueSig. *)

From Stdlib Require Import NArith List Bool Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig Product.
From Galois.States Require Import StateSig.
From Galois.Relational Require Import LinearizeSig NumStateSig RelEnvSig.
Import ComplexityNotations.

Module RelEnvCode (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (F : LINEARIZE_OPS X L) (R : NUM_STATE_OPS X L F) (E : STATE_DOMAIN_OPS X L V)
    (RR : REL_RANGE_REFINE_OPS L V)
    (P : LATTICE_OPS with Definition t := (R.t * E.t)%type)
    <: REL_ENV_OPS X L V F R E RR P.
  Definition t := (R.t * E.t)%type.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top : t := (R.top, E.top).
  Definition meet (a b : t) : t := (R.meet (fst a) (fst b), E.meet (snd a) (snd b)).
  Definition wparam := (R.wparam * E.wparam)%type.
  Definition widen (p : wparam) (a b : t) : t :=
    if is_bot b then a
    else (R.widen (fst p) (fst a) (fst b), E.widen (snd p) (snd a) (snd b)).
  Definition narrow := product_narrow R.is_bot E.is_bot R.narrow E.narrow.
  Definition assign x e (s : t) : t := (R.assign x e (fst s), E.assign x e (snd s)).
  Definition havoc x (s : t) : t := (R.havoc x (fst s), E.havoc x (snd s)).
  Definition assume g es (s : t) : t := (R.assume g es (fst s), E.assume g es (snd s)).
  Definition eval e (s : t) : V.t :=
    let bounds := R.range e (fst s) in
    RR.refine_range (fst bounds) (snd bounds) (E.eval e (snd s)).
End RelEnvCode.

Module RelEnv (X : KEY) (L : LANG) (N : NUM_VIEW L) (V : VALUE_DOMAIN L)
    (F : LINEARIZE X L N) (R : NUM_STATE X L N F) (E : STATE_DOMAIN X L V)
    (RR : RANGE_REFINE L N V)
    (P : LATTICE with Definition t := (R.t * E.t)%type)
    (PL : REL_PAIR_LINK X L N V F R E P) <: REL_ENV X L N V F R E RR P PL.
  Include RelEnvCode X L V F R E RR P.
  Definition wrank (p : wparam) (s : t) : nat :=
    R.wrank (fst p) (fst s) + E.wrank (snd p) (snd s).
  Definition gamma (s : t) (st : X.t -> L.val) : Prop :=
    R.ngamma (fst s) (fun x => N.num (st x)) /\ E.gamma (snd s) st.

  (** Componentwise inclusion implies inclusion of the paired states. *)
  Lemma components_below : forall a b,
    R.leb (fst a) (fst b) = true -> E.leb (snd a) (snd b) = true -> leb a b = true.
  Proof.
    intros a b Hr He. unfold leb. rewrite PL.leb_pair, Hr, He.
    now rewrite orb_true_r.
  Qed.

  (** Inclusion from a nonbottom pair holds in both components. *)
  Lemma nonbottom_components : forall a b, is_bot a = false -> leb a b = true ->
    R.leb (fst a) (fst b) = true /\ E.leb (snd a) (snd b) = true.
  Proof.
    intros a b Hbot Hle. unfold leb in Hle. rewrite PL.leb_pair in Hle.
    change (P.is_bot a = false) in Hbot. rewrite Hbot in Hle.
    now apply andb_true_iff in Hle.
  Qed.

  (** A recognized bottom component makes the intersection empty. *)
  Lemma bottom_empty : forall a st, is_bot a = true -> ~ gamma a st.
  Proof.
    intros a st Hbot [Hr He]. unfold is_bot in Hbot.
    rewrite PL.is_bot_pair in Hbot. apply orb_true_iff in Hbot as [Hbot|Hbot].
    - apply (R.ngamma_bot (fun x => N.num (st x))).
      eapply R.ngamma_mono; [apply R.is_bot_least; exact Hbot|exact Hr].
    - apply (E.gamma_bot st).
      eapply E.gamma_mono; [apply E.is_bot_least; exact Hbot|exact He].
  Qed.

  (** Every paired state is below itself. *)
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

  (** The pair of component tops describes every paired state. *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intro a. apply components_below; [apply R.top_greatest|apply E.top_greatest].
  Qed.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (is_bot b); [apply leb_refl|].
    apply components_below; [apply R.widen_ub_l|apply E.widen_ub_l].
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (is_bot b) eqn:Hbot.
    - apply is_bot_least. exact Hbot.
    - apply components_below; [apply R.widen_ub_r|apply E.widen_ub_r].
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros [pr pe] [ar ae] [br be] Hle. unfold widen.
    destruct (is_bot (br, be)) eqn:Hbot; [reflexivity|].
    destruct (nonbottom_components (br, be) (ar, ae) Hbot Hle) as [Hr He].
    cbn [fst snd] in Hr, He |- *.
    rewrite (R.widen_stable pr ar br Hr), (E.widen_stable pe ae be He).
    reflexivity.
  Qed.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros [pr pe] [ar ae] [br be] Hbot Hle.
    unfold is_bot in Hbot. rewrite PL.is_bot_pair in Hbot.
    apply orb_false_iff in Hbot as [Hr He]. cbn [fst snd] in Hr, He.
    unfold leb in Hle. rewrite PL.leb_pair in Hle.
    apply orb_false_iff in Hle as [Hcandidate Hle].
    unfold widen, is_bot. rewrite Hcandidate. unfold wrank. cbn [fst snd] in Hle |- *.
    pose proof (R.wrank_widen_le pr ar br Hr) as Hleft.
    pose proof (E.wrank_widen_le pe ae be He) as Hright.
    apply andb_false_iff in Hle as [Hle|Hle].
    - pose proof (R.wrank_widen pr ar br Hr Hle). lia.
    - pose proof (E.wrank_widen pe ae be He Hle). lia.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hle.
    - rewrite (widen_stable p a b Hle). lia.
    - pose proof (wrank_widen p a b Hbot Hle). lia.
  Qed.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle. unfold narrow, product_narrow, product_is_bot.
    rewrite <- PL.is_bot_pair. destruct (P.is_bot b) eqn:Hbot.
    - split; [apply leb_refl|exact Hle].
    - destruct (nonbottom_components b a Hbot Hle) as [Hr He].
      destruct (R.narrow_between (fst a) (fst b) Hr) as [Hr1 Hr2].
      destruct (E.narrow_between (snd a) (snd b) He) as [He1 He2].
      split; apply components_below; assumption.
  Qed.

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof.
    intros a b st Hle Hgamma. destruct (is_bot a) eqn:Hbot.
    - exfalso. exact (bottom_empty a st Hbot Hgamma).
    - destruct (nonbottom_components a b Hbot Hle) as [Hr He].
      destruct Hgamma as [Hnum Hstate]. split.
      + eapply R.ngamma_mono; eassumption.
      + eapply E.gamma_mono; eassumption.
  Qed.
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intro st. apply bottom_empty. apply is_bot_bot.
  Qed.
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof.
    intro st. split; [apply R.ngamma_top|apply E.gamma_top].
  Qed.
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof.
    intros x e s st c [Hr He] Heval. split.
    - eapply R.assign_sound; eassumption.
    - eapply E.assign_sound; eassumption.
  Qed.
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof.
    intros x s st c [Hr He]. split.
    - apply R.havoc_sound. exact Hr.
    - apply E.havoc_sound. exact He.
  Qed.
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof.
    intros g es s st cs [Hr He] Heval Hholds. split.
    - eapply R.assume_sound; eassumption.
    - eapply E.assume_sound; eassumption.
  Qed.
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof.
    intros e s st c [Hr He] Heval. apply RR.refine_range_sound.
    - eapply E.eval_sound; eassumption.
    - eapply R.range_sound; eassumption.
  Qed.

End RelEnv.

Module RelEnvT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type
      with Definition size := fun a => R.size (fst a) + E.size (snd a))
    (PL : REL_PAIR_LINK X L N V F R E P)
    <: REL_ENV_ALL X L N V F R E RR P PL.
  Include RelEnv X L N V F R E RR P PL.
  Definition size (a : t) : nat := R.size (fst a) + E.size (snd a).
  Definition wsize (p : wparam) : nat := R.wsize (fst p) + E.wsize (snd p).
  Definition wunits (a : t) : nat := R.wunits (fst a) + E.wunits (snd a).
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    R.assign_work x e (fst s) + E.assign_work x e (snd s).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    R.havoc_work x (fst s) + E.havoc_work x (snd s).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    R.assume_work g es (fst s) + E.assume_work g es (snd s).
  Definition eval_work (e : term L.op X.t) (s : t) : nat :=
    R.range_work e (fst s) + R.range_bits e (fst s) + E.eval_work e (snd s) +
      V.size (E.eval e (snd s)) + 1.
  TimeFun leb.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun widen.
  TimeFun narrow.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.
  Definition k_lattice : N := (P.c_lat + R.c_lat + E.c_lat + 16)%N.
  Definition k_transfer : N :=
    (R.c_num + E.c_state + RR.c_refine * (R.c_num + 1) + 16)%N.
  Definition c_rel_env : N := 16%N.
  Definition c_lat : N := (64 * k_lattice)%N.
  Definition c_state : N := (64 * k_transfer)%N.

  (** Enlarging a callback coefficient and its work budget preserves its bound. *)
  Local Lemma scale_cost : forall ticks coefficient own budget ceiling,
    (ticks <= coefficient * N.of_nat own)%N -> (coefficient <= ceiling)%N ->
    (own <= budget)%nat -> (ticks <= ceiling * N.of_nat budget)%N.
  Proof.
    intros ticks coefficient own budget ceiling Htime Hcoefficient Hsize.
    eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono; [exact Hcoefficient|lia].
  Qed.

  (** The lattice coefficient pays for four callbacks and their fixed bookkeeping. *)
  Local Lemma lattice_budget : forall budget,
    (4 * (k_lattice * budget) + 32 * budget <= c_lat * budget)%N.
  Proof.
    intro budget. unfold c_lat.
    replace (4 * (k_lattice * budget) + 32 * budget)%N with
      ((4 * k_lattice + 32) * budget)%N by ring.
    apply N.mul_le_mono_r. unfold k_lattice. lia.
  Qed.

  (** The state coefficient pays for its three callbacks and fixed bookkeeping. *)
  Local Lemma transfer_budget : forall budget,
    (3 * (k_transfer * budget) + 32 * budget <= c_state * budget)%N.
  Proof.
    intro budget. unfold c_state.
    replace (3 * (k_transfer * budget) + 32 * budget)%N with
      ((3 * k_transfer + 32) * budget)%N by ring.
    apply N.mul_le_mono_r. unfold k_transfer. nia.
  Qed.

  (** The shared lattice coefficient is positive. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, k_lattice. lia.
  Qed.

  (** Paired order testing inherits the shared lattice's size bound. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. set (budget := N.of_nat (size a + size b + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hcallback : (P.T_leb a b <= k_lattice * budget)%N).
    { eapply scale_cost; [apply P.T_leb_le|unfold k_lattice; lia|reflexivity]. }
    pose proof (lattice_budget budget) as Htotal.
    time_unfold T_leb. time_cbn. time_pose. lia.
  Qed.

  (** Paired joining inherits the shared lattice's size bound. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. set (budget := N.of_nat (size a + size b + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hcallback : (P.T_join a b <= k_lattice * budget)%N).
    { eapply scale_cost; [apply P.T_join_le|unfold k_lattice; lia|reflexivity]. }
    pose proof (lattice_budget budget) as Htotal.
    time_unfold T_join. time_cbn. time_pose. lia.
  Qed.

  (** Paired bottom testing inherits the shared lattice's size bound. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intro a. set (budget := N.of_nat (size a + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hcallback : (P.T_is_bot a <= k_lattice * budget)%N).
    { eapply scale_cost; [apply P.T_is_bot_le|unfold k_lattice; lia|reflexivity]. }
    pose proof (lattice_budget budget) as Htotal.
    time_unfold T_is_bot. time_cbn. time_pose. lia.
  Qed.
  (** Widening charges both component updates and the shared bottom test. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b.
    set (budget := N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1))).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite !Nat2N.inj_add. lia. }
    assert (Hbot : (P.T_is_bot b <= k_lattice * budget)%N).
    { eapply scale_cost; [apply P.T_is_bot_le|unfold k_lattice; lia|].
      change (size b + 1 <=
        (wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1))%nat. nia. }
    assert (Hr : (R.T_widen (fst p) (fst a) (fst b) <= k_lattice * budget)%N).
    { eapply scale_cost; [apply R.T_widen_le|unfold k_lattice; lia|].
      unfold size, wsize, wunits. nia. }
    assert (He : (E.T_widen (snd p) (snd a) (snd b) <= k_lattice * budget)%N).
    { eapply scale_cost; [apply E.T_widen_le|unfold k_lattice; lia|].
      unfold size, wsize, wunits. nia. }
    pose proof (lattice_budget budget) as Htotal.
    time_unfold T_widen. time_unfold T_is_bot. time_cbn. time_pose.
    destruct (is_bot b); lia.
  Qed.
  (** Narrowing charges the two bottom tests and the two component narrowings. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. set (budget := N.of_nat (size a + size b + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hr0 : (R.T_is_bot (fst b) <= k_lattice * budget)%N).
    { eapply scale_cost; [apply R.T_is_bot_le|unfold k_lattice; lia|]. unfold size. lia. }
    assert (He0 : (E.T_is_bot (snd b) <= k_lattice * budget)%N).
    { eapply scale_cost; [apply E.T_is_bot_le|unfold k_lattice; lia|]. unfold size. lia. }
    assert (Hr1 : (R.T_narrow (fst a) (fst b) <= k_lattice * budget)%N).
    { eapply scale_cost; [apply R.T_narrow_le|unfold k_lattice; lia|]. unfold size. lia. }
    assert (He1 : (E.T_narrow (snd a) (snd b) <= k_lattice * budget)%N).
    { eapply scale_cost; [apply E.T_narrow_le|unfold k_lattice; lia|]. unfold size. lia. }
    pose proof (lattice_budget budget) as Htotal.
    time_unfold T_narrow. time_unfold @T_product_narrow.
    time_unfold @T_product_is_bot. time_unfold @T_product_pair. time_cbn. time_pose.
    destruct (product_is_bot R.is_bot E.is_bot b); lia.
  Qed.
  (** Assignment is bounded by the sum of component work. *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof.
    intros x e s. set (budget := N.of_nat (assign_work x e s + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hr : (R.T_assign x e (fst s) <= k_transfer * budget)%N).
    { eapply scale_cost; [apply R.T_assign_le|unfold k_transfer; nia|].
      unfold assign_work. lia. }
    assert (He : (E.T_assign x e (snd s) <= k_transfer * budget)%N).
    { eapply scale_cost; [apply E.T_assign_le|unfold k_transfer; nia|].
      unfold assign_work. lia. }
    pose proof (transfer_budget budget) as Htotal.
    time_unfold T_assign. time_cbn. time_pose. lia.
  Qed.
  (** Havoc is bounded by the sum of component work. *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x s. set (budget := N.of_nat (havoc_work x s + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hr : (R.T_havoc x (fst s) <= k_transfer * budget)%N).
    { eapply scale_cost; [apply R.T_havoc_le|unfold k_transfer; nia|].
      unfold havoc_work. lia. }
    assert (He : (E.T_havoc x (snd s) <= k_transfer * budget)%N).
    { eapply scale_cost; [apply E.T_havoc_le|unfold k_transfer; nia|].
      unfold havoc_work. lia. }
    pose proof (transfer_budget budget) as Htotal.
    time_unfold T_havoc. time_cbn. time_pose. lia.
  Qed.
  (** Assumption is bounded by the sum of component work without an invariant premise. *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es s. set (budget := N.of_nat (assume_work g es s + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hr : (R.T_assume g es (fst s) <= k_transfer * budget)%N).
    { eapply scale_cost; [apply R.T_assume_le|unfold k_transfer; nia|].
      unfold assume_work. lia. }
    assert (He : (E.T_assume g es (snd s) <= k_transfer * budget)%N).
    { eapply scale_cost; [apply E.T_assume_le|unfold k_transfer; nia|].
      unfold assume_work. lia. }
    pose proof (transfer_budget budget) as Htotal.
    time_unfold T_assume. time_cbn. time_pose. lia.
  Qed.

  (** The numeric endpoint budget pays for refinement of the evaluated value. *)
  Local Lemma refinement_cost : forall e r s budget,
    (R.range_bits e r + 1 <= budget)%nat -> (V.size (E.eval e s) + 1 <= budget)%nat ->
    (RR.T_refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s) <=
      k_transfer * N.of_nat budget)%N.
  Proof.
    intros e r s budget Hbits Hvalue.
    assert (Hendpoints : (N.of_nat
      ((match fst (R.range e r) with Fin z => Z.size_nat z | _ => 0 end) +
       (match snd (R.range e r) with Fin z => Z.size_nat z | _ => 0 end)) <=
      R.c_num * N.of_nat budget)%N).
    { eapply N.le_trans; [apply R.range_size|]. apply N.mul_le_mono_l. lia. }
    eapply N.le_trans; [apply RR.T_refine_range_le|].
    eapply N.le_trans with (m :=
      (RR.c_refine * ((R.c_num + 1) * N.of_nat budget))%N).
    - apply N.mul_le_mono_l. rewrite !Nat2N.inj_add in Hendpoints |- *.
      assert (HvalueN : (N.of_nat (V.size (E.eval e s)) + 1 <= N.of_nat budget)%N) by lia.
      rewrite N.mul_add_distr_r. lia.
    - rewrite N.mul_assoc. apply N.mul_le_mono_r. unfold k_transfer. nia.
  Qed.

  (** Evaluation pays for both component queries and the actual refinement. *)
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof.
    intros e [r s]. set (budget := N.of_nat (eval_work e (r, s) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hr : (R.T_range e r <= k_transfer * budget)%N).
    { eapply scale_cost; [apply R.T_range_le|unfold k_transfer; nia|].
      unfold eval_work. cbn [fst snd]. lia. }
    assert (He : (E.T_eval e s <= k_transfer * budget)%N).
    { eapply scale_cost; [apply E.T_eval_le|unfold k_transfer; nia|].
      unfold eval_work. cbn [fst snd]. lia. }
    assert (Hrefine : (RR.T_refine_range (fst (R.range e r)) (snd (R.range e r))
      (E.eval e s) <= k_transfer * budget)%N).
    { apply refinement_cost; unfold eval_work; cbn [fst snd]; lia. }
    pose proof (transfer_budget budget) as Htotal.
    time_unfold T_eval. time_cbn. time_pose. lia.
  Qed.
  (** Evaluation charges its two queries and the refinement it actually performs. *)
  Lemma T_eval_components : forall e r s, (T_eval e (r, s) <= c_rel_env *
    (R.T_range e r + E.T_eval e s +
      RR.T_refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s) + 1))%N.
  Proof.
    intros e r s. unfold c_rel_env. time_unfold T_eval. time_cbn. time_pose. lia.
  Qed.
  (** Assignment adds only fixed bookkeeping to the component clocks. *)
  Lemma T_assign_components : forall x e r s, (T_assign x e (r, s) <=
    c_rel_env * (R.T_assign x e r + E.T_assign x e s + 1))%N.
  Proof.
    intros x e r s. unfold c_rel_env. time_unfold T_assign. time_cbn. time_pose. lia.
  Qed.
  (** Havoc adds only fixed bookkeeping to the component clocks. *)
  Lemma T_havoc_components : forall x r s, (T_havoc x (r, s) <=
    c_rel_env * (R.T_havoc x r + E.T_havoc x s + 1))%N.
  Proof.
    intros x r s. unfold c_rel_env. time_unfold T_havoc. time_cbn. time_pose. lia.
  Qed.
  (** Assumption adds only fixed bookkeeping to the component clocks. *)
  Lemma T_assume_components : forall g es r s, (T_assume g es (r, s) <=
    c_rel_env * (R.T_assume g es r + E.T_assume g es s + 1))%N.
  Proof.
    intros g es r s. unfold c_rel_env. time_unfold T_assume. time_cbn. time_pose. lia.
  Qed.
  (** Evaluation work includes endpoint and result sizes needed by refinement. *)
  Lemma eval_work_components : forall e r s, eval_work e (r, s) =
    R.range_work e r + R.range_bits e r + E.eval_work e s + V.size (E.eval e s) + 1.
  Proof. reflexivity. Qed.
  (** Assignment work adds the work of both components. *)
  Lemma assign_work_components : forall x e r s,
    assign_work x e (r, s) = R.assign_work x e r + E.assign_work x e s.
  Proof.
    reflexivity.
  Qed.
  (** Havoc work adds the work of both components. *)
  Lemma havoc_work_components : forall x r s,
    havoc_work x (r, s) = R.havoc_work x r + E.havoc_work x s.
  Proof.
    reflexivity.
  Qed.
  (** Assumption work adds the work of both components. *)
  Lemma assume_work_components : forall g es r s,
    assume_work g es (r, s) = R.assume_work g es r + E.assume_work g es s.
  Proof.
    reflexivity.
  Qed.
  (** Widening visits the units of both components. *)
  Lemma wunits_components : forall r s, wunits (r, s) = R.wunits r + E.wunits s.
  Proof.
    reflexivity.
  Qed.
  (** The widening parameter is measured by its two component parameters. *)
  Lemma wsize_components : forall p, wsize p = R.wsize (fst p) + E.wsize (snd p).
  Proof.
    reflexivity.
  Qed.
  (** The inherited pair coefficient is covered by the composed lattice coefficient. *)
  Lemma c_lat_pair : (P.c_lat <= c_lat)%N.
  Proof.
    unfold c_lat, k_lattice. lia.
  Qed.
  (** The pair's public size agrees with the sum of component sizes. *)
  Lemma size_pair : forall a, P.size a = R.size (fst a) + E.size (snd a).
  Proof. reflexivity. Qed.
  (** Evaluation is linear in the work of both components. *)
  Lemma eval_complexity :
    T_eval e s ∈ 𝑂(N.of_nat (eval_work e s)) for (e, s).
  Proof.
    apply bigO_intro with (c := c_state).
    intros [e s] _. cbn [fst snd].
    pose proof (T_eval_le e s) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Assignment is linear in the work of both components. *)
  Lemma assign_complexity :
    T_assign x e s ∈ 𝑂(N.of_nat (assign_work x e s)) for (x, e, s).
  Proof.
    apply bigO_intro with (c := c_state).
    intros [[x e] s] _. cbn [fst snd].
    pose proof (T_assign_le x e s) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Havoc is linear in the work of both components. *)
  Lemma havoc_complexity :
    T_havoc x s ∈ 𝑂(N.of_nat (havoc_work x s)) for (x, s).
  Proof.
    apply bigO_intro with (c := c_state).
    intros [x s] _. cbn [fst snd].
    pose proof (T_havoc_le x s) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Assumption is linear in the work of both components. *)
  Lemma assume_complexity :
    T_assume g es s ∈ 𝑂(N.of_nat (assume_work g es s)) for (g, es, s).
  Proof.
    apply bigO_intro with (c := c_state).
    intros [[g es] s] _. cbn [fst snd].
    pose proof (T_assume_le g es s) as Htime.
    rewrite Nat2N.inj_add in Htime. nia.
  Qed.
  (** Relational environments denote the intersection of their two meanings. *)
  Lemma gamma_def : forall r s st,
    gamma (r, s) st <-> R.ngamma r (fun x => N.num (st x)) /\ E.gamma s st.
  Proof.
    reflexivity.
  Qed.
  (** Evaluation refines the value result using the numeric range of the same expression. *)
  Lemma eval_def : forall e r s, eval e (r, s) =
    RR.refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s).
  Proof.
    reflexivity.
  Qed.
  (** Assignment updates both components. *)
  Lemma assign_def : forall x e r s, assign x e (r, s) =
    (R.assign x e r, E.assign x e s).
  Proof.
    reflexivity.
  Qed.
  (** Havoc updates both components. *)
  Lemma havoc_def : forall x r s, havoc x (r, s) = (R.havoc x r, E.havoc x s).
  Proof.
    reflexivity.
  Qed.
  (** Assumption updates both components. *)
  Lemma assume_def : forall g es r s,
    assume g es (r, s) = (R.assume g es r, E.assume g es s).
  Proof.
    reflexivity.
  Qed.
  (** Widening ignores a bottom candidate and otherwise widens componentwise. *)
  Lemma widen_def : forall p r s r' s', widen p (r, s) (r', s') =
    if is_bot (r', s') then (r, s)
    else (R.widen (fst p) r r', E.widen (snd p) s s').
  Proof.
    reflexivity.
  Qed.
  (** Narrowing keeps a bottom candidate and otherwise narrows componentwise. *)
  Lemma narrow_def : forall a b, narrow a b =
    if is_bot b then b else (R.narrow (fst a) (fst b), E.narrow (snd a) (snd b)).
  Proof.
    intros a b. unfold narrow, product_narrow, product_is_bot, is_bot.
    rewrite PL.is_bot_pair. reflexivity.
  Qed.
  (** The widening rank is the sum of the ranks of the actual component states. *)
  Lemma wrank_def : forall p r s,
    wrank p (r, s) = R.wrank (fst p) r + E.wrank (snd p) s.
  Proof.
    reflexivity.
  Qed.
  (** Stored state size is the sum of component sizes. *)
  Lemma size_def : forall r s, size (r, s) = R.size r + E.size s.
  Proof. reflexivity. Qed.
End RelEnvT.
