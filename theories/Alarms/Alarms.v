(** * Alarm reporting implementation

    Alarm reporting checks abstract operands at each program point.
    For example, a missing invariant uses the bottom state.
    Builds on: AlarmsSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Alarms Require Import ChecksSig AlarmsSig.

Module AlarmsCode (N X : KEY_OPS) (MN : MAP_OPS N) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) (S : STATE_DOMAIN_OPS X L V) (C : CHECKS_OPS L V)
    <: ALARMS_OPS N X MN L V S C.
  Definition inv_at (inv : MN.t S.t) (n : N.t) : S.t :=
    match MN.get n inv with Some s => s | None => S.bot end.

  Definition alarm (inv : MN.t S.t) (k : check N.t L.op X.t C.kd) : bool :=
    C.may_fail (ckind k) (map (fun e => S.eval e (inv_at inv (site k))) (args k)).

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

  Lemma no_alarm_safe : forall (reach : N.t -> (X.t -> L.val) -> Prop) inv,
    (forall n st, reach n st -> S.gamma (inv_at inv n) st) ->
    forall k, alarm inv k = false -> forall st cs,
    reach (site k) st -> eval_terms L.eval st (args k) = Some cs -> C.safe (ckind k) cs.
  Proof. Admitted.

  Lemma alarm_at_top : forall inv k, inv_at inv (site k) = S.top ->
    (forall e, In e (args k) -> S.eval e S.top = V.top) ->
    (exists cs, length cs = length (args k) /\ ~ C.safe (ckind k) cs) -> alarm inv k = true.
  Proof. Admitted.
End Alarms.

Module AlarmsT (N X : KEY_T) (MN : MAP_T N) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V) (C : CHECKS_T L V)
    <: ALARMS_T N X MN L V S C.
  Include Alarms N X MN L V S C.
  TimeFun inv_at.
  TimeFun alarm.
  TimeFun alarms.
  Definition c_alarms : N := 1%N. (* STUB *)
  Definition check_work inv (k : check N.t L.op X.t C.kd) : nat :=
    let s := inv_at inv (site k) in
    fold_right Nat.add 0 (map (fun e => S.eval_work e s + 1) (args k)) +
    C.work (ckind k) (map (fun e => S.eval e s) (args k)) + N.bits (site k) + 1.
  Lemma T_inv_at_le : forall inv n, (T_inv_at inv n <= c_alarms * N.of_nat ((N.bits n + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_alarm_le : forall inv k, (T_alarm inv k <= c_alarms * N.of_nat (check_work inv k))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_alarms_le : forall inv ks, (T_alarms inv ks <=
    c_alarms * N.of_nat ((fold_right Nat.add 0 (map (check_work inv) ks) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
End AlarmsT.

Module AlarmsPoint (N X : KEY) (MN : MAP N) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V) (C : CHECKS L V)
    (CP : CHECKS_POINT L V C).
  Include Alarms N X MN L V S C.

  Lemma alarm_on_exact_error : forall inv k cs,
    Forall2 (fun e c => CP.point (S.eval e (inv_at inv (site k))) = Some c) (args k) cs ->
    ~ C.safe (ckind k) cs -> alarm inv k = true.
  Proof. Admitted.
End AlarmsPoint.
