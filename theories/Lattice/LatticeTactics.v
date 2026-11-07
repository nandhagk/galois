(** * Order automation

    Bounded hint search derives order facts from explicit law records in the context.
    For example, bottom is below a join without unfolding any lattice.
    Builds on: LatticeCore. *)

From Galois.Lattice Require Import LatticeCore.

Create HintDb galois_order.

(** Reflexivity reads the law record for the goal's dictionary. *)
#[export] Hint Extern 1 (leb ?L ?a ?a = true) =>
  match goal with
  | H : lattice_laws L |- _ => exact (leb_refl H a)
  end : galois_order.

(** Bottom is below every value according to the matching law record. *)
#[export] Hint Extern 1 (leb ?L (bot ?L) ?a = true) =>
  match goal with
  | H : lattice_laws L |- _ => exact (bot_least H a)
  end : galois_order.

(** The left join bound uses the matching weak laws. *)
#[export] Hint Extern 1 (leb ?L ?a (join ?L ?a ?b) = true) =>
  match goal with
  | H : lattice_laws L |- _ => exact (join_upper_l H a b)
  end : galois_order.

(** The right join bound uses the matching weak laws. *)
#[export] Hint Extern 1 (leb ?L ?b (join ?L ?a ?b) = true) =>
  match goal with
  | H : lattice_laws L |- _ => exact (join_upper_r H a b)
  end : galois_order.

(** The left widening bound uses the matching weak laws. *)
#[export] Hint Extern 1 (leb ?L ?a (widen ?L ?a ?b) = true) =>
  match goal with
  | H : lattice_laws L |- _ => exact (widen_upper_l H a b)
  end : galois_order.

(** The right widening bound uses the matching weak laws. *)
#[export] Hint Extern 1 (leb ?L ?b (widen ?L ?a ?b) = true) =>
  match goal with
  | H : lattice_laws L |- _ => exact (widen_upper_r H a b)
  end : galois_order.

(** Conditional narrowing lower bounds leave the input-order premise to search. *)
#[export] Hint Extern 2 (leb ?L (narrow ?L ?a ?b) ?a = true) =>
  match goal with
  | H : lattice_laws L |- _ => apply (narrow_lower H a b)
  end : galois_order.

(** Conditional narrowing upper bounds leave the input-order premise to search. *)
#[export] Hint Extern 2 (leb ?L ?b (narrow ?L ?a ?b) = true) =>
  match goal with
  | H : lattice_laws L |- _ => apply (narrow_upper H a b)
  end : galois_order.

(** The left meet bound uses a separately supplied meet law record. *)
#[export] Hint Extern 1 (leb ?L (?meet ?a ?b) ?a = true) =>
  match goal with
  | H : meet_laws L meet |- _ => exact (meet_lower_l H a b)
  end : galois_order.

(** The right meet bound uses a separately supplied meet law record. *)
#[export] Hint Extern 1 (leb ?L (?meet ?a ?b) ?b = true) =>
  match goal with
  | H : meet_laws L meet |- _ => exact (meet_lower_r H a b)
  end : galois_order.

(** Least joins let search reduce join monotonicity to two input comparisons. *)
#[export] Hint Extern 3 (leb ?L (join ?L ?a ?b) (join ?L ?a' ?b') = true) =>
  match goal with
  | H : lattice_laws L, Hlub : lub_laws L |- _ =>
    apply (join_monotone L a a' b b' H Hlub)
  end : galois_order.

(** Transitivity extends a comparison already present in the context. *)
#[export] Hint Extern 5 (leb ?L ?a ?b = true) =>
  multimatch goal with
  | H : lattice_laws L, Ham : leb L a ?m = true |- _ =>
    eapply (leb_trans H a m b); [exact Ham |]
  end : galois_order.

(** Close order goals in six search layers or fail without leaving residual goals. *)
Ltac order_solver := solve [eauto 6 with galois_order].
