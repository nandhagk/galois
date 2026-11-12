(** * Alarm reporting observations

    Checks inspect abstract operands at their recorded program points.
    For example, a zero interval triggers the sample check at a reached point.
    Builds on: Alarms, Env and Interval. *)

From Stdlib Require Import List ZArith Bool.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval Thresholds ZLang.
From Galois.States Require Import Env.
From Galois.Alarms Require Import ChecksSig Alarms.
Import List.ListNotations.
Local Open Scope Z_scope.

Module NatMap := TrieMapCode NatKeyCode.
Module Values := IntervalCode ZLangCode ThresholdsCode.
Module State := EnvCode NatKeyCode NatMap ZLangCode Values.
Module Checks.
  Definition kd := unit.
  Definition may_fail (_ : kd) (xs : list Values.t) :=
    match xs with
    | [I (Fin z) (Fin w)] => Z.eqb z 0 && Z.eqb w 0
    | _ => false
    end.
End Checks.
Module Report := AlarmsCode NatKeyCode NatKeyCode NatMap ZLangCode Values State Checks.

Definition zero_check := MkCheck nat zview nat unit 1%nat tt [Node (ZConst 0) []].
Definition nonzero_check := MkCheck nat zview nat unit 1%nat tt [Node (ZConst 2) []].
Definition absent_check := MkCheck nat zview nat unit 2%nat tt [Node (ZConst 0) []].
Definition invariants := NatMap.set 1%nat State.top NatMap.empty.

Example missing_invariant_is_bottom : Report.inv_at invariants 2%nat = State.bot.
Proof. vm_compute. reflexivity. Qed.
Example reached_zero_triggers : Report.alarm invariants zero_check = true.
Proof. vm_compute. reflexivity. Qed.
Example reached_nonzero_is_safe : Report.alarm invariants nonzero_check = false.
Proof. vm_compute. reflexivity. Qed.
Example absent_site_uses_bottom : Report.alarm invariants absent_check = false.
Proof. vm_compute. reflexivity. Qed.
Example alarm_filter_preserves_order :
  Report.alarms invariants [nonzero_check; zero_check; absent_check; zero_check] =
    [zero_check; zero_check].
Proof. vm_compute. reflexivity. Qed.
