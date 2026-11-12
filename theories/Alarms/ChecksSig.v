(** * Alarm checks

    Checks describe safety tests on abstract operands.
    For example, a division check can reject a possible zero divisor.
    Builds on: LangSig and ValueSig. *)

From Stdlib Require Import List.
From Argent Require Import Time Std.
From Galois.Domains Require Import LangSig ValueSig.

Record check (N K X Kd : Type) := MkCheck {
  site : N;
  ckind : Kd;
  args : list (term K X)
}.

Arguments site {N K X Kd} _.
Arguments ckind {N K X Kd} _.
Arguments args {N K X Kd} _.
TimeFun site.
TimeFun ckind.
TimeFun args.

Module Type CHECKS_OPS (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L).
  Parameter kd : Type.
  Parameter may_fail : kd -> list V.t -> bool.
End CHECKS_OPS.

Module Type CHECKS_LAWS (L : LANG) (V : VALUE_DOMAIN L)
    (Import C : CHECKS_OPS L V).
  (* spec: safe *)
  Parameter safe : kd -> list L.val -> Prop.
  (** A successful check excludes concrete errors. *)
  Parameter may_fail_sound : forall k xs cs, may_fail k xs = false ->
    Forall2 V.gamma xs cs -> safe k cs.
  (** Top operands report every possible error of their arity. *)
  Parameter may_fail_top : forall k n,
    (exists cs, length cs = n /\ ~ safe k cs) -> may_fail k (repeat V.top n) = true.
End CHECKS_LAWS.

Module Type CHECKS (L : LANG) (V : VALUE_DOMAIN L) :=
  CHECKS_OPS L V <+ CHECKS_LAWS L V.

Module Type CHECKS_TIME (L : LANG_T) (V : VALUE_DOMAIN_T L) (Import C : CHECKS L V).
  (* spec: work *)
  Parameter work : kd -> list V.t -> nat.
  Parameter T_may_fail : kd -> list V.t -> nat.
  Parameter c_checks : nat.
  (** Checks charge their domain-specific operand work. *)
  Parameter T_may_fail_le : forall k xs, T_may_fail k xs <= c_checks * (work k xs + 1).
End CHECKS_TIME.

Module Type CHECKS_T (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  CHECKS L V <+ CHECKS_TIME L V.

Module Type CHECKS_POINT (L : LANG) (V : VALUE_DOMAIN L) (C : CHECKS L V).
  Parameter point : V.t -> option L.val.
  (** Exact erroneous operands always raise an alarm. *)
  Parameter may_fail_point : forall k xs cs,
    Forall2 (fun x c => point x = Some c) xs cs ->
    ~ C.safe k cs -> C.may_fail k xs = true.
End CHECKS_POINT.
