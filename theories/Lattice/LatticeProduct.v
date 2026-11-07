(** * Product lattices

    Products apply lattice operations to each coordinate independently.
    For example, a pair of booleans joins by disjoining each coordinate.
    Builds on: CostMonad and the lattice combinator kit. *)

From Stdlib Require Import Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKit.
Import Cost.Notations.

(** Products charge each component callback and its invocation. *)
Definition product {A B} (LA : lattice A) (LB : lattice B) : lattice (A * B) :=
  {| leb_c := fun x y =>
       Cost.step ;; let* a := leb_c LA (fst x) (fst y) in
       Cost.step ;; let* b := leb_c LB (snd x) (snd y) in
       Cost.ret (andb a b);
     join_c := fun x y =>
       Cost.step ;; let* a := join_c LA (fst x) (fst y) in
       Cost.step ;; let* b := join_c LB (snd x) (snd y) in
       Cost.ret (a, b);
     widen_c := fun x y =>
       Cost.step ;; let* a := widen_c LA (fst x) (fst y) in
       Cost.step ;; let* b := widen_c LB (snd x) (snd y) in
       Cost.ret (a, b);
     narrow_c := fun x y =>
       Cost.step ;; let* a := narrow_c LA (fst x) (fst y) in
       Cost.step ;; let* b := narrow_c LB (snd x) (snd y) in
       Cost.ret (a, b);
     bot := (bot LA, bot LB) |}.

Section Product.
Context {A B : Type} (LA : lattice A) (LB : lattice B).

(** Product comparison requires both component comparisons. *)
Theorem leb_product x y :
  leb (product LA LB) x y = andb (leb LA (fst x) (fst y)) (leb LB (snd x) (snd y)).
Proof.
  cbn [leb product leb_c]; cost_simpl; reflexivity.
Qed.

(** Product join combines both coordinates. *)
Theorem join_product x y :
  join (product LA LB) x y = (join LA (fst x) (fst y), join LB (snd x) (snd y)).
Proof.
  cbn [join product join_c]; cost_simpl; reflexivity.
Qed.

(** Product widening combines both coordinates. *)
Theorem widen_product x y :
  widen (product LA LB) x y = (widen LA (fst x) (fst y), widen LB (snd x) (snd y)).
Proof.
  cbn [widen product widen_c]; cost_simpl; reflexivity.
Qed.

(** Product narrowing combines both coordinates. *)
Theorem narrow_product x y :
  narrow (product LA LB) x y = (narrow LA (fst x) (fst y), narrow LB (snd x) (snd y)).
Proof.
  cbn [narrow product narrow_c]; cost_simpl; reflexivity.
Qed.

(** The two product projections satisfy the slot equations. *)
Theorem product_slots : slots2 (product LA LB) LA LB fst snd.
Proof.
  constructor.
  - intros x y; rewrite leb_product, andb_true_iff; reflexivity.
  - split; reflexivity.
  - intros x y; rewrite join_product; split; reflexivity.
  - intros x y; rewrite widen_product; split; reflexivity.
  - intros x y; rewrite narrow_product; split; reflexivity.
Qed.

(** Component weak laws imply product weak laws. *)
Theorem product_laws : lattice_laws LA -> lattice_laws LB -> lattice_laws (product LA LB).
Proof.
  apply (slots2_laws product_slots).
Qed.

(** Component least joins imply product least joins. *)
Theorem product_lub : lub_laws LA -> lub_laws LB -> lub_laws (product LA LB).
Proof.
  apply (slots2_lub product_slots).
Qed.

(** The pair of component tops bounds the product. *)
Definition product_top (TA : top LA) (TB : top LB) : top (product LA LB) :=
  slots2_top product_slots TA TB (top_value TA, top_value TB) eq_refl eq_refl.

(** Component closure lifts to the conjunction of invariants. *)
Theorem product_closed {ia ib} :
  closed_on LA ia -> closed_on LB ib ->
  closed_on (product LA LB) (fun x => ia (fst x) /\ ib (snd x)).
Proof.
  apply (slots2_closed product_slots).
Qed.

(** Product height is the sum of the component heights. *)
Theorem product_height {ia ib} (HA : lattice_laws LA) (HB : lattice_laws LB)
    (CA : closed_on LA ia) (CB : closed_on LB ib)
    (RA : height_on LA ia) (RB : height_on LB ib) :
    height_on (product LA LB) (fun x => ia (fst x) /\ ib (snd x)).
Proof.
  exact (slots2_height product_slots HA HB CA CB RA RB).
Defined.

(** Product widening credits sum the component credits. *)
Theorem product_wrank {ia ib} (WA : widening_rank_on LA ia) (WB : widening_rank_on LB ib) :
    widening_rank_on (product LA LB) (fun x => ia (fst x) /\ ib (snd x)).
Proof.
  exact (slots2_wrank product_slots WA WB).
Defined.

(** Each product callback costs at most the component bounds and two invocation ticks. *)
Theorem product_cost ia ib ka kb :
  cost_bounded_on LA ia ka -> cost_bounded_on LB ib kb ->
  cost_bounded_on (product LA LB) (fun x => ia (fst x) /\ ib (snd x)) (ka + kb + 2)%N.
Proof.
  intros HA HB x y [Hxa Hxb] [Hya Hyb].
  destruct (HA _ _ Hxa Hya) as [Hla [Hja [Hwa Hna]]].
  destruct (HB _ _ Hxb Hyb) as [Hlb [Hjb [Hwb Hnb]]].
  cbn [product leb_c join_c widen_c narrow_c]; cost_simpl; repeat split; lia.
Qed.

(** Product meanings intersect component meanings. *)
Definition product_gamma {C} (GA : concretisation A C) (GB : concretisation B C) :=
  slots2_gamma GA GB fst snd.

(** Intersected meanings are monotone when both components are monotone. *)
Theorem product_gamma_laws {C} (GA : concretisation A C) (GB : concretisation B C) :
  concretisation_laws LA GA -> concretisation_laws LB GB ->
  concretisation_laws (product LA LB) (product_gamma GA GB).
Proof.
  apply (slots2_gamma_laws product_slots).
Qed.

(** An empty component bottom makes the product bottom empty. *)
Theorem product_bot_empty {C} (GA : concretisation A C) (GB : concretisation B C) :
  bottom_empty LA GA \/ bottom_empty LB GB ->
  bottom_empty (product LA LB) (product_gamma GA GB).
Proof.
  apply (slots2_bot_empty product_slots).
Qed.

(** Product agreement requires agreement in both components. *)
Definition product_agree {C} (RA : agreement A C) (RB : agreement B C) :=
  slots2_agree RA RB fst snd.

(** Product agreement inherits reflexivity and antitonicity. *)
Theorem product_agree_laws {C} (RA : agreement A C) (RB : agreement B C) :
  agreement_laws LA RA -> agreement_laws LB RB ->
  agreement_laws (product LA LB) (product_agree RA RB).
Proof.
  apply (slots2_agree_laws product_slots).
Qed.

(** Component join agreement implies product join agreement. *)
Theorem product_agree_join {C} (RA : agreement A C) (RB : agreement B C) :
  agreement_join_law LA RA -> agreement_join_law LB RB ->
  agreement_join_law (product LA LB) (product_agree RA RB).
Proof.
  apply (slots2_agree_join product_slots).
Qed.

(** The first projection preserves product order. *)
Theorem monotone_fst : monotone_fun (product LA LB) LA fst.
Proof.
  intros x y H; apply (slots_leb product_slots) in H; exact (proj1 H).
Qed.

(** The second projection preserves product order. *)
Theorem monotone_snd : monotone_fun (product LA LB) LB snd.
Proof.
  intros x y H; apply (slots_leb product_slots) in H; exact (proj2 H).
Qed.

(** Pairing monotone maps preserves order. *)
Theorem monotone_pair {D} (LD : lattice D) (f : D -> A) (g : D -> B) :
  monotone_fun LD LA f -> monotone_fun LD LB g ->
  monotone_fun LD (product LA LB) (fun d => (f d, g d)).
Proof.
  intros Hf Hg x y Hxy; apply (slots_leb product_slots); split; [apply Hf | apply Hg]; exact Hxy.
Qed.
End Product.

Arguments product {A B} LA LB : simpl never.
