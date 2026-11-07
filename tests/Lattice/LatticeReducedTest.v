(** * Reducer fixtures and law instances

    Boolean pairs exercise changed operations, unequal round counts and two-step stability.
    For example, clearing a false first slot also clears the second slot.
    Builds on: LatticeReduced, LatticeKit and LatticeSimple. *)

From Stdlib Require Import Bool NArith List Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeHeight LatticeKit
  LatticeSimple LatticeReduced.
Import Cost.Notations List.ListNotations.

Definition reduce_pair : lattice (bool * bool) :=
  simple (fun x y => implb (fst x) (fst y) && implb (snd x) (snd y))
    (false, false) (fun x y => (fst x || fst y, snd x || snd y)).

(** The local plain pair has exact slots independently of LAT-BASIC. *)
Theorem reduce_pair_slots : slots2 reduce_pair bool_lattice bool_lattice fst snd.
Proof.
  constructor.
  - intros [a b] [c d]; destruct a, b, c, d; vm_compute; tauto.
  - split; reflexivity.
  - intros; split; reflexivity.
  - intros; split; reflexivity.
  - intros; split; reflexivity.
Qed.

Definition clear_second n : reducer bool bool :=
  {| step_c := fun a b => Cost.step ;; Cost.ret (a, a && b);
     rounds := fun _ => n |}.

Definition clear_variable : reducer bool bool :=
  {| step_c := step_c (clear_second 1);
     rounds := fun x => if snd x then 1 else 2 |}.

Definition clear_twice : reducer bool bool :=
  {| step_c := fun a b => Cost.step ;; Cost.ret (a && b, false);
     rounds := fun _ => 2 |}.

Definition reduce_meaning : concretisation (bool * bool) unit :=
  {| gamma := fun x _ => fst x = true |}.

Definition reduce_twice_meaning : concretisation (bool * bool) unit :=
  {| gamma := fun _ _ => True |}.

(** The unequal-round fixture satisfies descending, monotone, sound and stable laws. *)
Theorem clear_variable_laws : reducer_laws reduce_pair reduce_meaning clear_variable.
Proof.
  constructor.
  - intros [a b]; destruct a, b; vm_compute; reflexivity.
  - intros [a b] [c d]; destruct a, b, c, d; vm_compute; intuition discriminate.
  - intros [a b] c Hc; exact Hc.
  - intros [a b]; destruct a, b; vm_compute; reflexivity.
Qed.

(** The two-step fixture also satisfies the reducer contract. *)
Theorem clear_twice_laws : reducer_laws reduce_pair reduce_twice_meaning clear_twice.
Proof.
  constructor.
  - intros [a b]; destruct a, b; vm_compute; reflexivity.
  - intros [a b] [c d]; destruct a, b, c, d; vm_compute; intuition discriminate.
  - intros [a b] c Hc; exact Hc.
  - intros [a b]; destruct a, b; vm_compute; reflexivity.
Qed.

Definition reduce_pair_laws := slots2_laws reduce_pair_slots bool_laws bool_laws.
Definition reduced_fixture := reduced reduce_pair reduce_pair_slots (clear_second 1).

(** A nonidentity reducer yields a total weak lattice from the plain pair laws. *)
Theorem reduced_variable_laws :
  lattice_laws (reduced reduce_pair reduce_pair_slots clear_variable).
Proof.
  exact (reduced_laws reduce_pair reduce_pair_slots reduce_meaning clear_variable
    reduce_pair_laws clear_variable_laws).
Qed.

(** The reducer meaning is monotone on the completed reduced order. *)
Theorem reduced_variable_gamma :
  concretisation_laws (reduced reduce_pair reduce_pair_slots clear_variable) reduce_meaning.
Proof.
  apply (reduced_gamma_laws reduce_pair reduce_pair_slots reduce_meaning clear_variable
    clear_variable_laws).
  constructor; intros [a b] [c d] concrete Hle Hc.
  destruct a, b, c, d; vm_compute in *; intuition discriminate.
Qed.

Definition reduced_variable_rank :=
  reduced_wrank reduce_pair reduce_pair_slots reduce_meaning clear_variable
    reduce_pair_laws clear_variable_laws
    (slots2_wrank reduce_pair_slots bool_wrank bool_wrank).

Definition reduced_identity_height :=
  reduced_height reduce_pair reduce_pair_slots reduce_meaning identity_reducer
    reduce_pair_laws (identity_reducer_laws _ _ reduce_pair_laws)
    (slots2_lub reduce_pair_slots bool_lub bool_lub)
    (slots2_closed reduce_pair_slots bool_closed bool_closed)
    (fun _ H => H)
    (slots2_height reduce_pair_slots bool_laws bool_laws
      bool_closed bool_closed bool_height bool_height).

Definition reduced_variable_height :=
  reduced_height reduce_pair reduce_pair_slots reduce_meaning clear_variable
    reduce_pair_laws clear_variable_laws
    (slots2_lub reduce_pair_slots bool_lub bool_lub)
    (slots2_closed reduce_pair_slots bool_closed bool_closed)
    (fun _ _ => conj I I)
    (slots2_height reduce_pair_slots bool_laws bool_laws
      bool_closed bool_closed bool_height bool_height).

(** Identity reduction supplies a useful least-join instance. *)
Theorem reduced_identity_lub :
  lub_laws (reduced reduce_pair reduce_pair_slots identity_reducer).
Proof.
  apply (reduced_lub reduce_pair reduce_pair_slots reduce_meaning identity_reducer
    reduce_pair_laws (identity_reducer_laws _ _ reduce_pair_laws)
    (slots2_lub reduce_pair_slots bool_lub bool_lub)).
  intros; apply (leb_refl reduce_pair_laws).
Qed.

(** The two-step constant normalisation supplies a nonidentity least-join instance. *)
Theorem reduced_twice_lub :
  lub_laws (reduced reduce_pair reduce_pair_slots clear_twice).
Proof.
  apply (reduced_lub reduce_pair reduce_pair_slots reduce_twice_meaning clear_twice
    reduce_pair_laws clear_twice_laws (slots2_lub reduce_pair_slots bool_lub bool_lub)).
  intros [a b] [c d]; destruct a, b, c, d; vm_compute; reflexivity.
Qed.

Definition reduced_variable_top :=
  reduced_top reduce_pair reduce_pair_slots clear_variable
    (slots2_top reduce_pair_slots bool_top bool_top (true, true) eq_refl eq_refl).

Definition clear_measure (x : bool * bool) : nat :=
  if negb (fst x) && snd x then 1 else 0.

(** A runtime measure proves stability without a fixed global round count. *)
Theorem clear_measure_stable :
  forall x, leb reduce_pair
    (reduce (rounds_of_measure clear_measure (step_c (clear_second 1))) x)
    (step (rounds_of_measure clear_measure (step_c (clear_second 1)))
      (reduce (rounds_of_measure clear_measure (step_c (clear_second 1))) x)) = true.
Proof.
  apply stable_of_measure.
  - intros [a b] [c d]; destruct a, b, c, d; vm_compute; intuition discriminate.
  - intros [a b]; destruct a, b; vm_compute; intros; try discriminate; lia.
Qed.

Example reduce_positive :
  (reduce (clear_second 1) (false, true), reduce clear_twice (true, true)) =
    ((false, false), (false, false)).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduce_negative :
  (leb reduced_fixture (false, true) (false, false),
    leb reduced_fixture (true, true) (false, false)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduce_zero_rounds : reduce (clear_second 0) (false, true) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduce_unequal_rounds :
  (rounds clear_variable (false, true), rounds clear_variable (true, false),
    reduce clear_variable (false, true), reduce clear_variable (true, false)) =
    (1, 2, (false, false), (true, false)).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_height_counts_normalised_slots :
  (rank reduced_variable_height (false, true), rank reduced_variable_height (true, true)) =
    (0, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_operations :
  (join reduced_fixture (false, true) (false, false),
    widen reduced_fixture (false, true) (false, false),
    narrow reduced_fixture (true, true) (false, true)) =
    ((false, false), (false, true), (true, true)).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_join_is_not_an_exact_slot :
  (snd (join reduced_fixture (false, true) (false, false)),
    join bool_lattice true false) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_join_needs_compatibility :
  (leb reduced_fixture (true, false) (true, false),
    leb reduced_fixture (false, true) (true, false),
    leb reduced_fixture (join reduced_fixture (true, false) (false, true))
      (true, false)) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example reducer_ticks :
  (Cost.ticks (reduce_c (clear_second 0) (false, true)),
    Cost.ticks (reduce_c (clear_second 1) (false, true)),
    Cost.ticks (reduce_c clear_twice (true, true)),
    Cost.ticks (leb_c reduced_fixture (false, true) (false, false)),
    Cost.ticks (join_c reduced_fixture (false, true) (false, false))) =
    (0%N, 3%N, 6%N, 6%N, 5%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** The concrete callback bound instantiates the honest two-tick overhead theorem. *)
Theorem reducer_fixture_cost x :
  (Cost.ticks (reduce_c clear_twice x) <= 6)%N.
Proof.
  exact (reducer_cost clear_twice 1%N (fun _ _ => N.le_refl _) x).
Qed.
