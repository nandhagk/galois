(** * Alarm reporting

    Alarm reporting evaluates checks in the invariant stored at each program point.
    For example, a missing invariant is read as the unreachable state.
    Builds on: MapSig, ChecksSig, StateSig and InterpSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Program Require Import SemanticsSig CfgSig.
From Galois.Framework Require Import InterpSig.
From Galois.Alarms Require Import ChecksSig.

Module Type ALARMS_OPS (N X : KEY_OPS) (MN : MAP_OPS N) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) (S : STATE_DOMAIN_OPS X L V) (C : CHECKS_OPS L V).
  Parameter inv_at : MN.t S.t -> N.t -> S.t.
  Parameter alarm : MN.t S.t -> check N.t L.op X.t C.kd -> bool.
  Parameter alarms : MN.t S.t -> list (check N.t L.op X.t C.kd) ->
    list (check N.t L.op X.t C.kd).
End ALARMS_OPS.

Module Type ALARMS_LAWS (N X : KEY) (MN : MAP N) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V) (C : CHECKS L V)
    (Import A : ALARMS_OPS N X MN L V S C).
  (** Invariant lookup defaults to bottom. *)
  Parameter inv_at_spec : forall inv n,
    inv_at inv n = match MN.get n inv with Some s => s | None => S.bot end.
  (** An alarm checks the abstract results of all operands at its site. *)
  Parameter alarm_spec : forall inv k, alarm inv k = C.may_fail (ckind k)
    (map (fun e => S.eval e (inv_at inv (site k))) (args k)).
  (** Reporting retains precisely the checks that raise an alarm, in input order. *)
  Parameter alarms_spec : forall inv ks, alarms inv ks = filter (alarm inv) ks.
  (** A silent check is safe at every concrete store covered by the invariant. *)
  Parameter no_alarm_safe : forall (reach : N.t -> (X.t -> L.val) -> Prop) inv,
    (forall n st, reach n st -> S.gamma (inv_at inv n) st) ->
    forall k, alarm inv k = false -> forall st cs,
    reach (site k) st -> eval_terms L.eval st (args k) = Some cs -> C.safe (ckind k) cs.
  (** An unsafe possibility is reported when all operands are top. *)
  Parameter alarm_at_top : forall inv k, inv_at inv (site k) = S.top ->
    (forall e, In e (args k) -> S.eval e S.top = V.top) ->
    (exists cs, length cs = length (args k) /\ ~ C.safe (ckind k) cs) -> alarm inv k = true.
End ALARMS_LAWS.

Module Type ALARMS (N X : KEY) (MN : MAP N) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V) (C : CHECKS L V) :=
  ALARMS_OPS N X MN L V S C <+ ALARMS_LAWS N X MN L V S C.

Module Type ALARMS_TIME (N X : KEY_T) (MN : MAP_T N) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V) (C : CHECKS_T L V)
    (Import A : ALARMS N X MN L V S C).
  Parameter T_inv_at : MN.t S.t -> N.t -> N.
  Parameter T_alarm : MN.t S.t -> check N.t L.op X.t C.kd -> N.
  Parameter T_alarms : MN.t S.t -> list (check N.t L.op X.t C.kd) -> N.
  Parameter c_alarms : N.
  Definition check_work inv (k : check N.t L.op X.t C.kd) : nat :=
    let s := inv_at inv (site k) in
    fold_right Nat.add 0 (map (fun e => S.eval_work e s + 1) (args k)) +
    C.work (ckind k) (map (fun e => S.eval e s) (args k)) + N.bits (site k) + 1.
  (** Invariant lookup charges the site key. *)
  Parameter T_inv_at_le : forall inv n, (T_inv_at inv n <= c_alarms * N.of_nat ((N.bits n +
    1)%nat))%N.
  (** One alarm charges operand evaluation, checking and site lookup. *)
  Parameter T_alarm_le : forall inv k, (T_alarm inv k <= c_alarms * N.of_nat ((check_work inv
    k)%nat))%N.
  (** Reporting charges the sum of its checks' work. *)
  Parameter T_alarms_le : forall inv ks, (T_alarms inv ks <=
    c_alarms * N.of_nat ((fold_right Nat.add 0 (map (check_work inv) ks) + 1)%nat))%N.
End ALARMS_TIME.

Module Type ALARMS_T (N X : KEY_T) (MN : MAP_T N) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V) (C : CHECKS_T L V) :=
  ALARMS N X MN L V S C <+ ALARMS_TIME N X MN L V S C.

Module Type ALARMS_POINT (N X : KEY) (MN : MAP N) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V) (C : CHECKS L V)
    (CP : CHECKS_POINT L V C) (Import A : ALARMS N X MN L V S C).
  (** Exact erroneous operands raise an alarm. *)
  Parameter alarm_on_exact_error : forall inv k cs,
    Forall2 (fun e c => CP.point (S.eval e (inv_at inv (site k))) = Some c) (args k) cs ->
    ~ C.safe (ckind k) cs -> alarm inv k = true.
End ALARMS_POINT.

Module Type ALARMS_ANALYSIS (P : TYPE) (N : KEY) (E : TYPE) (G : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (ACT : ACTIONS_OPS P E X L)
    (D : STATE_DOMAIN X L V) (SYS : INTERP_SYSTEM P N E G X L V ACT D)
    (M : SEMANTICS P) (K : INTERP_LINK P N E G X L ACT M)
    (SOUND : INTERP_SOUND P N E G X L V ACT D SYS M K)
    (MN : MAP N) (C : CHECKS L V) (A : ALARMS N X MN L V D C).
  (** Certified interpreter invariants make every silent reachable check safe. *)
  Parameter analysis_no_alarm_safe : forall p inv,
    SYS.post_solution p (A.inv_at inv) -> forall k,
    A.alarm inv k = false -> forall s cs,
    reachable (M.initial p) (M.step p) s -> K.point s = site k ->
    eval_terms L.eval (K.store s) (args k) = Some cs -> C.safe (ckind k) cs.
End ALARMS_ANALYSIS.
