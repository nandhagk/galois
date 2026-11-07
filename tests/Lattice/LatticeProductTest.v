(** * Product fixtures

    These clients exercise a flat boolean value paired with a boolean fact.
    For example, joining unequal known values produces a flat top coordinate.
    Builds on: LatticeProduct, LatticeFlat and LatticeSimple. *)

From Stdlib Require Import Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeProduct LatticeFlat
  LatticeSimple.
Import Cost.Notations.

Definition pair_fixture := product (flat_lattice Bool.eqb) bool_lattice.

Example product_positive :
  join pair_fixture (FVal false, false) (FVal true, true) = (FTop, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_negative :
  leb pair_fixture (FVal false, true) (FVal true, true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_bottom :
  join pair_fixture (FBot, false) (FVal true, false) = (FVal true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_top :
  leb pair_fixture (FTop, true) (FTop, true) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_leb_ticks :
  Cost.ticks (leb_c pair_fixture (FBot, false) (FTop, true)) = 4%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_join_ticks :
  Cost.ticks (join_c pair_fixture (FVal false, false) (FVal true, true)) = 4%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_measure_client :
  let H := product_height (flat_lattice Bool.eqb) bool_lattice
    (flat_laws Bool.eqb Bool.eqb_true_iff) bool_laws
    (flat_closed Bool.eqb) bool_closed
    (flat_height Bool.eqb Bool.eqb_true_iff) bool_height in
  let W := product_wrank (flat_lattice Bool.eqb) bool_lattice
    (flat_wrank Bool.eqb Bool.eqb_true_iff) bool_wrank in
  (bound H, rank H (FTop, true), wbound W, wrank W (FBot, false)) = (3, 3, 3, 3).
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_bool : lattice bool :=
  {| leb_c := fun a b => Cost.tick 5 ;; Cost.ret (implb a b);
     bot := false;
     join_c := fun a b => Cost.tick 7 ;; Cost.ret (orb a b);
     widen_c := fun _ _ => Cost.tick 11 ;; Cost.ret true;
     narrow_c := fun a b => Cost.tick 13 ;; Cost.ret (andb a b) |}.

Example product_callback_charges :
  let P := product charged_bool unit_lattice in
  (Cost.ticks (leb_c P (false, tt) (true, tt)),
   Cost.ticks (join_c P (false, tt) (true, tt)),
   Cost.ticks (widen_c P (false, tt) (false, tt)),
   Cost.ticks (narrow_c P (true, tt) (false, tt))) = (8%N, 10%N, 14%N, 16%N).
Proof.
  vm_compute; reflexivity.
Qed.
