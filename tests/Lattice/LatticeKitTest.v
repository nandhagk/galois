(** * Slot-kit pilot

    A costed product derives its laws and termination measures from projection facts.
    For example, false paired with unit is below true paired with unit.
    Builds on: LatticeKit and LatticeSimple. *)

From Stdlib Require Import Bool Arith NArith List.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKit
  LatticeKitFamily LatticeSub LatticeSimple.
Import Cost.Notations List.ListNotations.

Definition pair_lattice {A B} (LA : lattice A) (LB : lattice B) : lattice (A * B) :=
  {| leb_c := fun x y => Cost.step ;;
       let* a := leb_c LA (fst x) (fst y) in
       if a then Cost.step ;; leb_c LB (snd x) (snd y) else Cost.ret false;
     join_c := fun x y => Cost.step ;;
       let* a := join_c LA (fst x) (fst y) in Cost.step ;;
       let* b := join_c LB (snd x) (snd y) in Cost.ret (a, b);
     widen_c := fun x y => Cost.step ;;
       let* a := widen_c LA (fst x) (fst y) in Cost.step ;;
       let* b := widen_c LB (snd x) (snd y) in Cost.ret (a, b);
     narrow_c := fun x y => Cost.step ;;
       let* a := narrow_c LA (fst x) (fst y) in Cost.step ;;
       let* b := narrow_c LB (snd x) (snd y) in Cost.ret (a, b);
     bot := (bot LA, bot LB) |}.

(** Pair observations commute with operations and reflect both component orders. *)
Theorem pair_slots {A B} (LA : lattice A) (LB : lattice B) :
  slots2 (pair_lattice LA LB) LA LB fst snd.
Proof.
  constructor; intros.
  - rewrite leb_equation at 1; cbn [pair_lattice leb_c]; cost_simpl.
    rewrite <- !leb_equation.
    destruct (leb LA (fst x) (fst y)); cost_simpl;
      rewrite <- ?leb_equation; intuition congruence.
  - auto.
  - split; reflexivity.
  - split; reflexivity.
  - split; reflexivity.
Qed.

Definition pilot := pair_lattice bool_lattice unit_lattice.

Example pilot_laws : lattice_laws pilot.
Proof.
  exact (slots2_laws (pair_slots _ _) bool_laws unit_laws).
Qed.

Example pilot_lub : lub_laws pilot.
Proof.
  exact (slots2_lub (pair_slots _ _) bool_lub unit_lub).
Qed.

Definition pilot_top : top pilot :=
  slots2_top (pair_slots _ _) bool_top unit_top (true, tt) eq_refl eq_refl.

Definition pilot_height :=
  slots2_height (pair_slots bool_lattice unit_lattice) bool_laws unit_laws
    bool_closed unit_closed bool_height unit_height.

Definition pilot_wrank :=
  slots2_wrank (pair_slots bool_lattice unit_lattice) bool_wrank unit_wrank.

Example pilot_closed :
  closed_on pilot (fun x => True /\ True).
Proof.
  exact (slots2_closed (pair_slots _ _) bool_closed unit_closed).
Qed.

Definition pilot_gamma : concretisation (bool * unit) nat :=
  slots2_gamma bool_gamma unit_gamma fst snd.

Example pilot_gamma_laws : concretisation_laws pilot pilot_gamma.
Proof.
  exact (slots2_gamma_laws (pair_slots _ _) _ _ bool_gamma_laws unit_gamma_laws).
Qed.

Example pilot_bot_empty : bottom_empty pilot pilot_gamma.
Proof.
  exact (slots2_bot_empty (pair_slots _ _) _ _ (or_introl bool_bot_empty)).
Qed.

Example pilot_top_full : top_full pilot_top pilot_gamma.
Proof.
  exact (slots2_top_full (pair_slots _ _) _ _ bool_top unit_top _ _ _
    bool_top_full unit_top_full).
Qed.

Definition pilot_agree : agreement (bool * unit) nat :=
  slots2_agree bool_agree unit_agree fst snd.

Example pilot_agree_laws : agreement_laws pilot pilot_agree.
Proof.
  exact (slots2_agree_laws (pair_slots _ _) _ _ bool_agree_laws unit_agree_laws).
Qed.

Example pilot_agree_join : agreement_join_law pilot pilot_agree.
Proof.
  exact (slots2_agree_join (pair_slots _ _) _ _ bool_agree_join unit_agree_join).
Qed.

Example pair_equal :
  (leb pilot (false, tt) (false, tt), join pilot (false, tt) (false, tt),
   Cost.ticks (leb_c pilot (false, tt) (false, tt))) = (true, (false, tt), 4%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example pair_ordered :
  (leb pilot (false, tt) (true, tt), join pilot (false, tt) (true, tt),
   Cost.ticks (join_c pilot (false, tt) (true, tt))) = (true, (true, tt), 4%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example pair_rejected :
  (leb pilot (true, tt) (false, tt), Cost.ticks (leb_c pilot (true, tt) (false, tt))) =
  (false, 2%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example pair_incomparable :
  let P := pair_lattice bool_lattice bool_lattice in
  (leb P (true, false) (false, true), leb P (false, true) (true, false),
   join P (true, false) (false, true),
   Cost.ticks (join_c P (true, false) (false, true))) = (false, false, (true, true), 4%N).
Proof.
  vm_compute; reflexivity.
Qed.

Definition bool_pair := pair_lattice bool_lattice bool_lattice.

Definition bool_slot (i : bool) (x : bool * bool) := if i then fst x else snd x.

(** Boolean indices observe both coordinates of the pair lattice. *)
Theorem bool_pair_family : family bool_pair bool_lattice bool_slot.
Proof.
  constructor.
  - intros x y; split.
    + intro Hxy; apply (slots_leb (pair_slots _ _)) in Hxy.
      intros []; [exact (proj1 Hxy) | exact (proj2 Hxy)].
    + intro Hslots; apply (slots_leb (pair_slots _ _)); split.
      * exact (Hslots true).
      * exact (Hslots false).
  - intros []; reflexivity.
  - intros [] x y; reflexivity.
  - intros [] x y; reflexivity.
  - intros [] x y; reflexivity.
Qed.

Example family_pilot_laws : lattice_laws bool_pair.
Proof.
  exact (family_laws bool_pair_family bool_laws).
Qed.

Definition family_pilot_height :=
  family_height bool_pair_family [true; false] false bool_laws bool_lub bool_closed bool_height.

Definition family_pilot_wrank :=
  family_wrank bool_pair_family [true; false] false bool_laws bool_wrank.

Example family_supported_closed :
  closed_on bool_pair
    (family_inv bool_lattice bool_slot [true; false] false (fun _ => True)).
Proof.
  apply (family_support_closed bool_pair_family); try exact bool_laws;
    try exact bool_lub; try exact bool_closed.
  - split; reflexivity.
  - intros [] [] _ _ [Ha _] [Hb _]; cbn in *; try discriminate; split; reflexivity.
  - intros [] [] _ _ Hle [Ha _] [Hb _]; cbn in *;
      try discriminate; split; reflexivity.
Qed.

Example family_meaning_laws :
  concretisation_laws bool_pair (family_gamma (@bool_gamma nat) bool_slot).
Proof.
  exact (family_gamma_laws bool_pair_family _ bool_gamma_laws).
Qed.

Example family_agreement_laws :
  agreement_laws bool_pair (family_agree (@bool_agree nat) bool_slot).
Proof.
  exact (family_agree_laws bool_pair_family _ bool_agree_laws).
Qed.

Example family_join_agreement :
  agreement_join_law bool_pair (family_agree (@bool_agree nat) bool_slot).
Proof.
  exact (family_agree_join bool_pair_family _ bool_agree_join).
Qed.

Example family_measures :
  (map (rank family_pilot_height) [(false, false); (true, false); (false, true); (true, true)],
   map (wrank family_pilot_wrank) [(false, false); (true, false); (false, true); (true, true)],
   bound family_pilot_height, wbound family_pilot_wrank) =
  ([0; 1; 1; 2], [2; 1; 1; 0], 2, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example family_full_universe x :
  family_inv bool_lattice bool_slot [true; false] false (fun _ => True) x.
Proof.
  split; [intros; exact I | intros [] Hout; exfalso; apply Hout; vm_compute; auto].
Qed.

Example family_rejects_outside_growth :
  ~ family_inv bool_lattice bool_slot [true] false (fun _ => True) (true, true).
Proof.
  vm_compute; intros [_ Hout]; specialize (Hout false); intuition congruence.
Qed.

Definition family_empty_height :=
  family_height bool_pair_family [] false bool_laws bool_lub bool_closed bool_height.

Example family_empty_boundary :
  family_inv bool_lattice bool_slot [] false (fun _ => True) (false, false) /\
  rank family_empty_height (false, false) = 0 /\ bound family_empty_height = 0.
Proof.
  split.
  - split; [intros; exact I | intros [] _; split; reflexivity].
  - vm_compute; auto.
Qed.

Definition family_duplicate_height :=
  family_height bool_pair_family [true; true; false] false
    bool_laws bool_lub bool_closed bool_height.

Example family_duplicate_boundary :
  (rank family_duplicate_height (true, false), bound family_duplicate_height) = (2, 3).
Proof.
  vm_compute; reflexivity.
Qed.

Definition guarded_narrow (a b : nat) := if Nat.leb b a then a else 3.

Definition bounded_nat := with_narrow (simple Nat.leb 0 Nat.max) guarded_narrow.

Definition within_two (n : nat) := n <= 2.

(** The interval up to two is closed even though unordered narrowing can escape it. *)
Theorem within_two_closed : closed_on bounded_nat within_two.
Proof.
  constructor.
  - exact (Nat.le_0_l 2).
  - intros a b Ha Hb; apply Nat.max_lub; assumption.
  - intros a b Ha Hb; apply Nat.max_lub; assumption.
  - intros a b Ha Hb Hle; change (Nat.leb b a = true) in Hle.
    change ((if Nat.leb b a then a else 3) <= 2); rewrite Hle; exact Ha.
Qed.

Definition subtype_nat := sub_lattice bounded_nat within_two within_two_closed.

Definition sub_zero : {a | within_two a} := exist _ 0 (Nat.le_0_l 2).

Definition sub_one : {a | within_two a} := exist _ 1 (Nat.le_succ_diag_r 1).

Example subtype_unordered_narrow :
  (narrow bounded_nat 0 1,
   proj1_sig (narrow subtype_nat sub_zero sub_one),
   Cost.ticks (narrow_c subtype_nat sub_zero sub_one)) = (3, 0, 2%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example subtype_ordered_narrow :
  (proj1_sig (narrow subtype_nat sub_one sub_zero),
   Cost.ticks (narrow_c subtype_nat sub_one sub_zero)) = (1, 4%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example subtype_join_boundary :
  (proj1_sig (join subtype_nat sub_zero sub_one),
   Cost.ticks (join_c subtype_nat sub_zero sub_one), leb subtype_nat sub_one sub_zero) =
  (1, 2%N, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition sub_bool := sub_lattice bool_lattice (fun _ => True) bool_closed.

Example subtype_bool_laws : lattice_laws sub_bool.
Proof.
  exact (sub_laws _ _ _ bool_laws).
Qed.

Example subtype_bool_lub : lub_laws sub_bool.
Proof.
  exact (sub_lub _ _ _ bool_lub).
Qed.

Definition subtype_bool_top := sub_top _ _ bool_closed bool_top I.

Definition subtype_bool_height := sub_height _ _ bool_closed bool_height.

Definition subtype_bool_wrank := sub_wrank _ _ bool_closed bool_wrank.

Example subtype_bool_gamma_laws :
  concretisation_laws sub_bool (sub_gamma (fun _ => True) (@bool_gamma nat)).
Proof.
  exact (sub_gamma_laws _ _ _ _ bool_gamma_laws).
Qed.

Example subtype_bool_measures :
  (rank subtype_bool_height (exist _ false I), wrank subtype_bool_wrank (exist _ false I),
   rank subtype_bool_height (exist _ true I), wrank subtype_bool_wrank (exist _ true I)) =
  (0, 1, 1, 0).
Proof.
  vm_compute; reflexivity.
Qed.
