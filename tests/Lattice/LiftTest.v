(** * Top-lift fixtures

    Unknown absorbs joins and lies above every known element.
    For example, joining Unknown with Elem false gives Unknown.
    Builds on: WithTop and Simple. *)

From Stdlib Require Import NArith.
From Galois.Lattice Require Import WithTop Simple JoinWidening.
Module TopBool := WithTopCode BoolLatCode.
Module TopBoolLat := WithTop BoolLat.
Module TopBoolHeight := WithTopHeight BoolLat BoolLatHeight TopBoolLat.
Module TopBoolRank := JoinWidening TopBoolLat TopBoolHeight.

Example lift_positive :
  TopBool.join (Elem false) (Elem true) = Elem true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_negative :
  TopBool.leb Unknown (Elem true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_unknown :
  TopBool.join (Elem false) Unknown = Unknown.
Proof.
  vm_compute; reflexivity.
Qed.

(* LatticeLiftTest.lift_narrow_unknown expects narrow Unknown (Elem false) = Elem false.
   The public JoinWideningCode adapter gives Unknown on these arguments. *)

Example lift_bottom :
  TopBool.bot = Elem false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_measure_client :
  (TopBoolHeight.height, TopBoolHeight.rank Unknown, TopBoolHeight.rank (Elem false),
   TopBoolHeight.height, TopBoolRank.wrank tt Unknown, TopBoolRank.wrank tt (Elem false)) =
  (2, 2, 0, 2, 0, 2).
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeLiftTest.lift_leb_ticks, lift_join_ticks and lift_unknown_ticks retire
   with Cost.ticks. lift_callback_charges replaces the widening dictionary at run
   time and expects (Elem true, 9%N). WithTop has no widening callback parameter,
   so that replacement observation retires with with_widen_c and Cost. *)
