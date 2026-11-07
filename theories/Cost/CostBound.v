(** * Bounds on abstract costs

    A bound relates a size function to a cost with one global constant.
    For example, a linear cost is bounded by its input size.
    Builds on: Stdlib binary arithmetic and CostMonad. *)

From Stdlib Require Import NArith Lia List.
From Galois.Cost Require Import CostMonad.

Open Scope N_scope.

(** A global multiplicative constant bounds the cost at every input. *)
Definition bigO {X : Type} (f g : X -> N) : Prop :=
  exists c, forall x, g x <= c * (1 + f x).

(** Every size bounds itself. *)
Theorem bigO_refl {X} (f : X -> N) : bigO f f.
Proof.
  exists 1. intro x. nia.
Qed.

(** Bounds compose through an intermediate cost. *)
Theorem bigO_trans {X} (f g h : X -> N) :
  bigO f g -> bigO g h -> bigO f h.
Proof.
  intros [c Hc] [d Hd]. exists (d * (1 + c)).
  intro x. specialize (Hc x). specialize (Hd x). nia.
Qed.

(** Decreasing a cost preserves its bound. *)
Theorem bigO_le {X} (f g h : X -> N) :
  bigO f g -> (forall x, h x <= g x) -> bigO f h.
Proof.
  intros [c Hc] Hle. exists c. intro x.
  specialize (Hc x). specialize (Hle x). lia.
Qed.

(** Increasing a size preserves a cost bound. *)
Theorem bigO_mono {X} (f g h : X -> N) :
  bigO f h -> (forall x, f x <= g x) -> bigO g h.
Proof.
  intros [c Hc] Hle. exists c. intro x.
  specialize (Hc x). specialize (Hle x). nia.
Qed.

(** Adding two bounded costs adds their sizes. *)
Theorem bigO_add {X} (f g h k : X -> N) :
  bigO f g -> bigO h k -> bigO (fun x => f x + h x) (fun x => g x + k x).
Proof.
  intros [c Hc] [d Hd]. exists (c + d).
  intro x. specialize (Hc x). specialize (Hd x). nia.
Qed.

(** Multiplication by a fixed constant preserves a bound. *)
Theorem bigO_scale {X} (f g : X -> N) a :
  bigO f g -> bigO f (fun x => a * g x).
Proof.
  intros [c Hc]. exists (a * c). intro x. specialize (Hc x). nia.
Qed.

(** Products are bounded by the two sizes and their product, including zero sizes. *)
Theorem bigO_mul {X} (f g h k : X -> N) :
  bigO f g -> bigO h k ->
  bigO (fun x => f x + h x + f x * h x) (fun x => g x * k x).
Proof.
  intros [c Hc] [d Hd]. exists (c * d).
  intro x. specialize (Hc x). specialize (Hd x).
  eapply N.le_trans.
  - apply N.mul_le_mono; eassumption.
  - nia.
Qed.

(** Precomposition transports a bound along any size map. *)
Theorem bigO_comp {X Y} (f g : Y -> N) (h : X -> Y) :
  bigO f g -> bigO (fun x => f (h x)) (fun x => g (h x)).
Proof.
  intros [c Hc]. exists c. intro x. apply Hc.
Qed.

(** A monotone outer size transports a bound through a size overapproximation. *)
Theorem bigO_through {X Y} (size : Y -> N) (s : X -> N)
    (F : N -> N) (g : Y -> N) (h : X -> Y) :
  (forall a b, a <= b -> F a <= F b) ->
  (forall x, size (h x) <= s x) ->
  bigO (fun y => F (size y)) g -> bigO (fun x => F (s x)) (fun x => g (h x)).
Proof.
  intros Hmono Hsize Hbound.
  eapply bigO_mono.
  - exact (bigO_comp _ _ h Hbound).
  - intro x. apply Hmono, Hsize.
Qed.

(** Summing a uniformly bounded family pays one unit per summand. *)
Theorem bigO_sum {X Y} (items : X -> list Y) (f g : Y -> N) :
  bigO f g ->
  bigO (fun x => fold_right (fun y n => 1 + f y + n) 0 (items x))
    (fun x => fold_right (fun y n => g y + n) 0 (items x)).
Proof.
  intros [c Hc]. exists c. intro x.
  induction (items x) as [|y rest IH]; cbn [fold_right].
  - nia.
  - specialize (Hc y). nia.
Qed.

(** Sequencing adds the bounds of the first computation and the reached continuation. *)
Theorem bigO_bind {X A B} (f g : X -> N)
    (m : X -> Cost.t A) (k : X -> A -> Cost.t B) :
  bigO f (fun x => Cost.ticks (m x)) ->
  bigO g (fun x => Cost.ticks (k x (Cost.value (m x)))) ->
  bigO (fun x => f x + g x) (fun x => Cost.ticks (Cost.bind (m x) (k x))).
Proof.
  intros Hm Hk. unfold bigO in *.
  destruct Hm as [c Hc]. destruct Hk as [d Hd]. exists (c + d).
  intro x. rewrite Cost.ticks_bind. specialize (Hc x). specialize (Hd x). nia.
Qed.
