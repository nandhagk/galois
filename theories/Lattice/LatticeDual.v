(** * Dual lattices

    A dual reverses an order and uses a supplied meet as its join.
    For example, boolean conjunction joins in reverse implication order.
    Builds on: CostMonad, LatticeCore and LatticeHeight. *)

From Stdlib Require Import Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
Import Cost.Notations.
Local Open Scope nat_scope.

(** Dual operations reverse comparison and charge the meet callback invocation. *)
Definition dual {A} (L : lattice A) (T : top L) (meet_c : A -> A -> Cost.t A) : lattice A :=
  {| leb_c := fun a b => Cost.step ;; leb_c L b a;
     join_c := fun a b => Cost.step ;; meet_c a b;
     widen_c := fun a b => Cost.step ;; meet_c a b;
     narrow_c := fun a _ => Cost.step ;; Cost.ret a;
     bot := top_value T |}.

(** Dual comparison reverses the component order. *)
Theorem leb_dual {A} (L : lattice A) (T : top L) meet_c a b :
  leb (dual L T meet_c) a b = leb L b a.
Proof.
  reflexivity.
Qed.

(** Dual join returns the value of the supplied meet callback. *)
Theorem join_dual {A} (L : lattice A) (T : top L) meet_c a b :
  join (dual L T meet_c) a b = Cost.value (meet_c a b).
Proof.
  reflexivity.
Qed.

(** A component greatest lower bound supplies dual weak laws. *)
Theorem dual_laws {A} (L : lattice A) (T : top L) meet_c :
  lattice_laws L -> meet_laws L (fun a b => Cost.value (meet_c a b)) ->
  lattice_laws (dual L T meet_c).
Proof.
  intros H M; constructor.
  - intro a; apply (leb_refl H).
  - intros a b c Hab Hbc; eapply (leb_trans H); eassumption.
  - apply (top_greatest T).
  - apply (meet_lower_l M).
  - apply (meet_lower_r M).
  - apply (meet_lower_l M).
  - apply (meet_lower_r M).
  - intros a b _; apply (leb_refl H).
  - intros a b Hab; exact Hab.
Qed.

(** Greatest lower bounds are least upper bounds in the dual. *)
Theorem dual_lub {A} (L : lattice A) (T : top L) meet_c :
  meet_laws L (fun a b => Cost.value (meet_c a b)) -> lub_laws (dual L T meet_c).
Proof.
  intro M; constructor; apply (meet_greatest M).
Qed.

(** The original bottom is the dual top. *)
Definition dual_top {A} (L : lattice A) (T : top L) meet_c (H : lattice_laws L) :
  top (dual L T meet_c).
Proof.
  refine {| top_value := bot L |}; intro a; apply (bot_least H).
Defined.

(** Complementing a component height bounds the dual and grows on strict meets. *)
Theorem dual_height {A} (L : lattice A) (T : top L) meet_c
    (H : lattice_laws L) (J : lub_laws L)
    (M : meet_laws L (fun a b => Cost.value (meet_c a b))) (R : height L) :
  height (dual L T meet_c).
Proof.
  refine {| rank := fun a => bound R - rank R a; bound := bound R |}.
  - intros a _; lia.
  - intros a b _ _ Hle.
    pose proof (rank_monotone R b a I I Hle); lia.
  - intros a b _ _ Hstrict.
    change (leb L a (Cost.value (meet_c a b)) = false) in Hstrict.
    set (m := Cost.value (meet_c a b)) in *.
    assert (Hma : leb L m a = true) by apply (meet_lower_l M).
    assert (Hstrict' : leb L (join L m a) m = false).
    { destruct (leb L (join L m a) m) eqn:Hback; [| reflexivity].
      pose proof (leb_trans H _ _ _ (join_upper_r H m a) Hback) as Hcontra.
      congruence. }
    assert (Hja : leb L (join L m a) a = true).
    { apply (join_least J); [exact Hma | apply (leb_refl H)]. }
    pose proof (join_rank_grows R m a I I Hstrict').
    pose proof (rank_monotone R (join L m a) a I I Hja).
    pose proof (rank_bounded R a I).
    change (bound R - rank R a < bound R - rank R m); lia.
Defined.

(** Dual cost includes the reversed comparison and each supplied meet callback. *)
Theorem dual_cost {A} (L : lattice A) (T : top L) meet_c inv k :
  cost_bounded_on L inv k ->
  (forall a b, inv a -> inv b -> (Cost.ticks (meet_c a b) <= k)%N) ->
  cost_bounded_on (dual L T meet_c) inv (k + 1)%N.
Proof.
  intros K Km a b Ha Hb; destruct (K b a Hb Ha) as [Hl _].
  specialize (Km a b Ha Hb); cbn [dual leb_c join_c widen_c narrow_c]; cost_simpl.
  repeat split; lia.
Qed.

Arguments dual {A} L T meet_c : simpl never.
