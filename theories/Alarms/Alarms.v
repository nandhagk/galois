(** * Alarm reporting implementation

    Alarm reporting checks abstract operands at each program point.
    For example, a missing invariant uses the bottom state.
    Builds on: AlarmsSig. *)

From Stdlib Require Import List NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Program Require Import SemanticsSig CfgSig.
From Galois.Framework Require Import InterpSig.
From Galois.Alarms Require Import ChecksSig AlarmsSig.

Module AlarmsCode (N X : KEY_OPS) (MN : MAP_OPS N) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) (S : STATE_DOMAIN_OPS X L V) (C : CHECKS_OPS L V)
    <: ALARMS_OPS N X MN L V S C.
  Definition inv_at (inv : MN.t S.t) (n : N.t) : S.t :=
    match MN.get n inv with Some s => s | None => S.bot end.

  Definition alarm (inv : MN.t S.t) (k : check N.t L.op X.t C.kd) : bool :=
    let s := inv_at inv (site k) in
    C.may_fail (ckind k) (map (fun e => S.eval e s) (args k)).

  Definition alarms (inv : MN.t S.t) (ks : list (check N.t L.op X.t C.kd)) :=
    filter (alarm inv) ks.
End AlarmsCode.

Module Alarms (N X : KEY) (MN : MAP N) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V) (C : CHECKS L V)
    <: ALARMS N X MN L V S C.
  Include AlarmsCode N X MN L V S C.

  Lemma inv_at_spec : forall inv n,
    inv_at inv n = match MN.get n inv with Some s => s | None => S.bot end.
  Proof. reflexivity. Qed.

  Lemma alarm_spec : forall inv k, alarm inv k = C.may_fail (ckind k)
    (map (fun e => S.eval e (inv_at inv (site k))) (args k)).
  Proof. reflexivity. Qed.

  Lemma alarms_spec : forall inv ks, alarms inv ks = filter (alarm inv) ks.
  Proof. reflexivity. Qed.

  (** Successful operand evaluation is covered pointwise by the abstract state. *)
  Lemma eval_operands_sound : forall es s st cs,
    S.gamma s st -> eval_terms L.eval st es = Some cs ->
    Forall2 V.gamma (map (fun e => S.eval e s) es) cs.
  Proof.
    unfold eval_terms. intros es s st cs Hgamma. revert cs.
    induction es as [|e es IH]; intros cs Heval; cbn in Heval.
    - inversion Heval. constructor.
    - destruct (eval_term L.eval st e) as [c|] eqn:He; [|discriminate].
      destruct (sequence (map (eval_term L.eval st) es)) as [vs|] eqn:Hes;
        [|discriminate].
      inversion Heval; subst cs. constructor.
      + eapply S.eval_sound; eassumption.
      + now apply IH.
  Qed.

  Lemma no_alarm_safe : forall (reach : N.t -> (X.t -> L.val) -> Prop) inv,
    (forall n st, reach n st -> S.gamma (inv_at inv n) st) ->
    forall k, alarm inv k = false -> forall st cs,
    reach (site k) st -> eval_terms L.eval st (args k) = Some cs -> C.safe (ckind k) cs.
  Proof.
    intros reach inv Hcovers k Hquiet st cs Hreach Heval.
    eapply C.may_fail_sound; [exact Hquiet|].
    eapply eval_operands_sound; [apply Hcovers; exact Hreach|exact Heval].
  Qed.

  (** Top-valued operands have the exact arity required by the checks contract. *)
  Lemma top_operands : forall es,
    (forall e, In e es -> S.eval e S.top = V.top) ->
    map (fun e => S.eval e S.top) es = repeat V.top (length es).
  Proof.
    intros es. induction es as [|e es IH]; intros Htop; cbn; [reflexivity|].
    rewrite Htop; [|now left]. rewrite IH; [reflexivity|].
    intros e1 He1. apply Htop. now right.
  Qed.

  Lemma alarm_at_top : forall inv k, inv_at inv (site k) = S.top ->
    (forall e, In e (args k) -> S.eval e S.top = V.top) ->
    (exists cs, length cs = length (args k) /\ ~ C.safe (ckind k) cs) -> alarm inv k = true.
  Proof.
    intros inv k Hinv Htop Hunsafe. unfold alarm. rewrite Hinv.
    rewrite top_operands; [now apply C.may_fail_top|exact Htop].
  Qed.
End Alarms.

Module AlarmsT (N X : KEY_T) (MN : MAP_T N) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V) (C : CHECKS_T L V)
    <: ALARMS_T N X MN L V S C.
  Include Alarms N X MN L V S C.
  TimeFun inv_at.
  TimeFun alarm.
  TimeFun alarms.
  (** One check pays for lookup, operand evaluation and its safety test. *)
  Definition k_alarm : N := (MN.c_map + S.c_state + C.c_checks + 16)%N.
  Definition c_alarms : N := (2 * k_alarm)%N.
  Definition check_work inv (k : check N.t L.op X.t C.kd) : nat :=
    let s := inv_at inv (site k) in
    fold_right Nat.add 0 (map (fun e => S.eval_work e s + 1) (args k)) +
    C.work (ckind k) (map (fun e => S.eval e s) (args k)) + N.bits (site k) + 1.
  Lemma T_inv_at_le : forall inv n, (T_inv_at inv n <= c_alarms * N.of_nat ((N.bits n + 1)%nat))%N.
  Proof.
    intros inv n. pose proof (MN.T_get_le S.t n inv).
    unfold T_inv_at, c_alarms, k_alarm. rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.

  (** Operand mapping charges each evaluation and its list cell. *)
  Lemma eval_map_time : forall s es,
    (ListDef.T_map (fun e => S.eval e s) (fun e => 1 + S.T_eval e s) es <=
      (S.c_state + 2) * N.of_nat
        ((fold_right Nat.add 0 (map (fun e => S.eval_work e s + 1) es))%nat) + 1)%N.
  Proof.
    intros s es. induction es as [|e es IH].
    - time_step.
    - pose proof (S.T_eval_le e s). time_step.
  Qed.

  (** The single-check bound reserves part of the reporting constant for filtering. *)
  Lemma T_alarm_core : forall inv k,
    (T_alarm inv k <= k_alarm * N.of_nat (check_work inv k))%N.
  Proof.
    intros inv k.
    pose proof (eval_map_time (inv_at inv (site k)) (args k)) as Hmap.
    pose proof (MN.T_get_le S.t (site k) inv) as Hget.
    pose proof (C.T_may_fail_le (ckind k)
      (map (fun e => S.eval e (inv_at inv (site k))) (args k))) as Hcheck.
    unfold T_alarm, T_inv_at, T_site, T_ckind, T_args.
    unfold check_work, k_alarm. time_cbn.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  Lemma T_alarm_le : forall inv k, (T_alarm inv k <= c_alarms * N.of_nat (check_work inv k))%N.
  Proof.
    intros inv k. pose proof (T_alarm_core inv k). unfold c_alarms. nia.
  Qed.

  (** Every check contributes one unit even when its operands and key have zero work. *)
  Lemma check_work_positive : forall inv k, 1 <= check_work inv k.
  Proof.
    intros. unfold check_work. lia.
  Qed.

  (** Filtering charges each check's work and a bounded list-cell overhead. *)
  Lemma filter_checks_time : forall inv ks,
    (List.T_filter (alarm inv) (T_alarm inv) ks <=
      (k_alarm + 1) * N.of_nat
        ((fold_right Nat.add 0 (map (check_work inv) ks))%nat) + 1)%N.
  Proof.
    intros inv ks. induction ks as [|k ks IH].
    - time_step.
    - pose proof (T_alarm_core inv k).
      pose proof (check_work_positive inv k). time_step.
  Qed.

  Lemma T_alarms_le : forall inv ks, (T_alarms inv ks <=
    c_alarms * N.of_nat ((fold_right Nat.add 0 (map (check_work inv) ks) + 1)%nat))%N.
  Proof.
    intros inv ks. pose proof (filter_checks_time inv ks).
    unfold T_alarms, c_alarms. rewrite Nat2N.inj_add. time_cbn.
    change (1 + List.T_filter (alarm inv) (T_alarm inv) ks <=
      2 * k_alarm *
        (N.of_nat ((fold_right Nat.add 0 (map (check_work inv) ks))%nat) + 1))%N.
    assert (Hk : (1 <= k_alarm)%N) by (unfold k_alarm; lia). nia.
  Qed.
End AlarmsT.

Module AlarmsPoint (N X : KEY) (MN : MAP N) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V) (C : CHECKS L V)
    (CP : CHECKS_POINT L V C).
  Include Alarms N X MN L V S C.

  Lemma alarm_on_exact_error : forall inv k cs,
    Forall2 (fun e c => CP.point (S.eval e (inv_at inv (site k))) = Some c) (args k) cs ->
    ~ C.safe (ckind k) cs -> alarm inv k = true.
  Proof.
    intros inv k cs Hpoints Hunsafe. unfold alarm.
    eapply CP.may_fail_point; [|exact Hunsafe].
    clear Hunsafe. induction Hpoints; cbn; constructor; assumption.
  Qed.
End AlarmsPoint.

Module AlarmsAnalysis (P : TYPE) (N : KEY) (E : TYPE) (G : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (ACT : ACTIONS_OPS P E X L)
    (D : STATE_DOMAIN X L V) (SYS : INTERP_SYSTEM P N E G X L V ACT D)
    (M : SEMANTICS P) (K : INTERP_LINK P N E G X L ACT M)
    (SOUND : INTERP_SOUND P N E G X L V ACT D SYS M K)
    (MN : MAP N) (C : CHECKS L V) (A : ALARMS N X MN L V D C)
    <: ALARMS_ANALYSIS P N E G X L V ACT D SYS M K SOUND MN C A.
  Include Alarms N X MN L V D C.

  (** Certified interpreter invariants make every silent reachable check safe. *)
  Lemma analysis_no_alarm_safe : forall p inv,
    SYS.post_solution p (A.inv_at inv) -> forall k,
    A.alarm inv k = false -> forall s cs,
    reachable (M.initial p) (M.step p) s -> K.point s = site k ->
    eval_terms L.eval (K.store s) (args k) = Some cs -> C.safe (ckind k) cs.
  Proof.
    intros p inv Hpost k Hquiet s cs Hreach Hpoint Heval.
    eapply A.no_alarm_safe with
      (reach := fun n st => exists s,
        reachable (M.initial p) (M.step p) s /\ K.point s = n /\ K.store s = st).
    - intros n st [s1 [Hs1 [Hn Hst]]]. subst n st.
      eapply SOUND.covers; eassumption.
    - exact Hquiet.
    - exists s. auto.
    - exact Heval.
  Qed.
End AlarmsAnalysis.
