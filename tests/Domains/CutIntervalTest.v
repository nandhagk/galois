(** * Fixed-budget interval computations

    The executable interval tower cuts every raw result to the endpoint budget.
    For example, an eight-bit upper endpoint of 256 becomes positive infinity.
    Builds on: CutInterval, Interval, Thresholds and ZLang. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig CutIntervalSig CutInterval Interval
  Thresholds ZLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Budget8 <: INTERVAL_CUTOFF.
  Definition bits := 8%nat.
End Budget8.
Module Raw := IntervalCode ZLangCode ThresholdsCode.
Module Cut := CutIntervalCode Budget8 ZLangCode ThresholdsCode Raw.

Example bounded_and_malformed :
  cut_raw (Cut.cut (I (Fin (-12)) (Fin 24))) = I (Fin (-12)) (Fin 24) /\
  cut_interval_ok 8 (cut_raw (Cut.cut (I (Fin (-12)) (Fin 24)))) = true /\
  cut_raw (Cut.cut (I (Fin 2) (Fin 1))) = IBot /\
  cut_raw (Cut.cut (I PosInf PosInf)) = IBot.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example outward_endpoints :
  cut_raw (Cut.cut (I (Fin 256) (Fin 300))) = I NegInf PosInf /\
  cut_raw (Cut.cut (I (Fin (-300)) (Fin (-256)))) = I NegInf PosInf /\
  cut_raw (Cut.cut (I (Fin (-256)) (Fin 10))) = I NegInf (Fin 10) /\
  cut_raw (Cut.cut (I (Fin 10) (Fin 256))) = I (Fin 10) PosInf.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example literal_and_add_overflow :
  cut_raw (Cut.forward (ZConst 256) []) = I NegInf PosInf /\
  cut_raw (Cut.forward ZAdd [Cut.cut (I (Fin 200) (Fin 200));
                             Cut.cut (I (Fin 100) (Fin 100))]) = I NegInf PosInf.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example unrestricted_threshold_is_cut :
  cut_raw (Cut.widen (ThresholdsCode.make [1000])
    (Cut.cut (I (Fin 0) (Fin 0))) (Cut.cut (I (Fin 0) (Fin 1)))) =
    I (Fin 0) PosInf.
Proof. vm_compute. reflexivity. Qed.
