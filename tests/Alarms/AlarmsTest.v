(** * Alarm reporting observations

    Checks inspect abstract operands at their recorded program points.
    For example, a zero interval triggers the sample check at a reached point.
    Builds on: Alarms, Env and Interval.

    Groups:
    - InvAtTests: the invariant recorded at a program point.
    - AlarmTests: whether one check raises an alarm.
    - AlarmsTests: which checks raise alarms, and in what order. *)

From Stdlib Require Import List ZArith Bool.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval Thresholds ZLang.
From Galois.States Require Import Env.
From Galois.Alarms Require Import ChecksSig Alarms.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module NatMap := TrieMapCode NatKeyCode.
Module Values := IntervalCode ZLangCode ThresholdsCode.
Module State := EnvCode NatKeyCode NatMap ZLangCode Values.

(** A check that fails when its operand is the interval [0, 0]. *)
Module Checks.
  Definition kd := unit.
  Definition may_fail (_ : kd) (xs : list Values.t) :=
    match xs with
    | [I (Fin z) (Fin w)] => Z.eqb z 0 && Z.eqb w 0
    | _ => false
    end.
End Checks.
Module Report := AlarmsCode NatKeyCode NatKeyCode NatMap ZLangCode Values State Checks.

(** A check at program point 1 whose operand is the constant 0. *)
Definition zero_check := MkCheck nat zview nat unit 1%nat tt [Node (ZConst 0) []].

(** A check at program point 1 whose operand is the constant 2. *)
Definition nonzero_check := MkCheck nat zview nat unit 1%nat tt [Node (ZConst 2) []].

(** A check at program point 2, which has no recorded invariant. *)
Definition absent_check := MkCheck nat zview nat unit 2%nat tt [Node (ZConst 0) []].

(** The invariants record only program point 1, with the top state. *)
Definition invariants := NatMap.set 1%nat State.top NatMap.empty.

Module InvAtTests.

  (** A program point without a recorded invariant reads as the bottom state. *)
  Example site_without_invariant_is_bottom : Report.inv_at invariants 2%nat = State.bot.
  Proof. vm_compute. reflexivity. Qed.

End InvAtTests.

Module AlarmTests.

  (** A check whose operand is zero at a reached point raises an alarm. *)
  Example reached_zero_raises_alarm : Report.alarm invariants zero_check = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A check whose operand is nonzero at a reached point raises no alarm. *)
  Example reached_nonzero_raises_no_alarm : Report.alarm invariants nonzero_check = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A check at a point without an invariant raises no alarm. *)
  Example absent_site_raises_no_alarm : Report.alarm invariants absent_check = false.
  Proof. vm_compute. reflexivity. Qed.

End AlarmTests.

Module AlarmsTests.

  (** The alarm list keeps the alarming checks in their original order. *)
  Example keeps_order_of_alarming_checks :
    Report.alarms invariants [nonzero_check; zero_check; absent_check; zero_check] =
      [zero_check; zero_check].
  Proof. vm_compute. reflexivity. Qed.

End AlarmsTests.
