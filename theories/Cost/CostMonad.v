(** * The cost monad

    A costed computation stores its result and a binary count of abstract steps.
    The operations compose computations without inspecting their counts to choose results.

    For example, binding [tick 2] to [ret true] returns [true] and charges two ticks.
    Builds on: Stdlib binary arithmetic. *)

From Stdlib.NArith Require Import NArith.

Module Cost.

(** A costed result contains computational data alone, without semantic laws. *)
#[projections(primitive)]
Record t (A : Type) : Type := mk {
  value : A;
  ticks : N
}.

Arguments mk {A} value ticks.
Arguments value {A} _.
Arguments ticks {A} _.

(** A predicate on a costed child concerns its value, independently of its count. *)
Polymorphic Definition t_all@{s;u +} (A : Type) (P : A -> Type@{s;u}) (m : t A)
    : Type@{s;u} :=
  P (value m).

(** Evidence for every value supplies evidence for the child of every costed result. *)
Polymorphic Theorem t_all_forall@{s;u +} (A : Type) (P : A -> Type@{s;u})
    (H : forall a, P a) (m : t A) : t_all A P m.
Proof.
  exact (H (value m)).
Defined.

Register Scheme t_all as All for t.
Register Scheme t_all_forall as AllForall for t.

(** Returning a result charges no ticks. *)
Definition ret {A : Type} (a : A) : t A := mk a 0.

(** Sequencing passes the first result to the continuation and adds both counts. *)
Definition bind {A B : Type} (m : t A) (f : A -> t B) : t B :=
  let r := f (value m) in mk (value r) (ticks m + ticks r).

(** Charging a count returns the unit value. *)
Definition tick (k : N) : t unit := mk tt k.

(** A single abstract step charges one tick. *)
Definition step : t unit := tick 1.

(** Mapping changes the result without changing its count. *)
Definition map {A B : Type} (f : A -> B) (m : t A) : t B :=
  mk (f (value m)) (ticks m).

(** Lifting a pure function charges the supplied input weight. *)
Definition lift {A B : Type} (w : A -> N) (f : A -> B) (a : A) : t B :=
  mk (f a) (w a).

(** Traversing a positive number charges one tick for each binary digit. *)
Fixpoint tick_bits (p : positive) : t unit :=
  match p with
  | xI q => bind step (fun _ => tick_bits q)
  | xO q => bind step (fun _ => tick_bits q)
  | xH => step
  end.

(** Refinement attaches a proof to the result without changing the count. *)
Definition refine {A : Type} {P : A -> Prop} (m : t A) (Hvalue : P (value m))
    : t {a | P a} :=
  mk (exist P (value m) Hvalue) (ticks m).

Module Notations.
  Notation "'let*' x ':=' m 'in' k" := (bind m (fun x => k))
    (at level 10, x binder, m at level 100, k at level 200).
  Notation "m ;; k" := (bind m (fun _ => k))
    (at level 100, right associativity).
End Notations.

(** * Projection equations *)

(** A returned computation has the supplied result. *)
Theorem value_ret {A : Type} (a : A) : value (ret a) = a.
Proof.
  reflexivity.
Qed.

(** A returned computation has zero cost. *)
Theorem ticks_ret {A : Type} (a : A) : ticks (ret a) = 0%N.
Proof.
  reflexivity.
Qed.

(** Sequencing returns the continuation's result on the first result. *)
Theorem value_bind {A B : Type} (m : t A) (f : A -> t B) :
  value (bind m f) = value (f (value m)).
Proof.
  reflexivity.
Qed.

(** Sequencing charges the sum of the first computation and its continuation. *)
Theorem ticks_bind {A B : Type} (m : t A) (f : A -> t B) :
  ticks (bind m f) = (ticks m + ticks (f (value m)))%N.
Proof.
  reflexivity.
Qed.

(** Mapping applies the pure function to the result. *)
Theorem value_map {A B : Type} (f : A -> B) (m : t A) :
  value (map f m) = f (value m).
Proof.
  reflexivity.
Qed.

(** Mapping leaves the cost unchanged. *)
Theorem ticks_map {A B : Type} (f : A -> B) (m : t A) :
  ticks (map f m) = ticks m.
Proof.
  reflexivity.
Qed.

(** Charging ticks returns the unit value. *)
Theorem value_tick (k : N) : value (tick k) = tt.
Proof.
  reflexivity.
Qed.

(** Charging ticks records the supplied count. *)
Theorem ticks_tick (k : N) : ticks (tick k) = k.
Proof.
  reflexivity.
Qed.

(** A single step returns the unit value. *)
Theorem value_step : value step = tt.
Proof.
  reflexivity.
Qed.

(** A single step costs one tick. *)
Theorem ticks_step : ticks step = 1%N.
Proof.
  reflexivity.
Qed.

(** Lifting returns the pure function's result. *)
Theorem value_lift {A B : Type} (w : A -> N) (f : A -> B) (a : A) :
  value (lift w f a) = f a.
Proof.
  reflexivity.
Qed.

(** Lifting charges the supplied weight on the input. *)
Theorem ticks_lift {A B : Type} (w : A -> N) (f : A -> B) (a : A) :
  ticks (lift w f a) = w a.
Proof.
  reflexivity.
Qed.

(** Traversing binary digits returns the unit value. *)
Theorem value_tick_bits (p : positive) : value (tick_bits p) = tt.
Proof.
  induction p as [p IH | p IH |].
  - exact IH.
  - exact IH.
  - reflexivity.
Qed.

(** Traversing binary digits charges their count, including the leading digit. *)
Theorem ticks_tick_bits (p : positive) : ticks (tick_bits p) = N.pos (Pos.size p).
Proof.
  induction p as [p IH | p IH |].
  - change (1 + ticks (tick_bits p) = N.pos (Pos.succ (Pos.size p)))%N.
    rewrite IH, N.add_1_l.
    reflexivity.
  - change (1 + ticks (tick_bits p) = N.pos (Pos.succ (Pos.size p)))%N.
    rewrite IH, N.add_1_l.
    reflexivity.
  - reflexivity.
Qed.

(** Refinement returns the original result paired with the supplied proof. *)
Theorem value_refine {A : Type} {P : A -> Prop} (m : t A) (Hvalue : P (value m)) :
  value (refine m Hvalue) = exist P (value m) Hvalue.
Proof.
  reflexivity.
Qed.

(** Refinement leaves the cost unchanged. *)
Theorem ticks_refine {A : Type} {P : A -> Prop} (m : t A) (Hvalue : P (value m)) :
  ticks (refine m Hvalue) = ticks m.
Proof.
  reflexivity.
Qed.

(** * Monad laws *)

(** Returning before a continuation leaves the whole computation unchanged. *)
Theorem bind_ret_l {A B : Type} (a : A) (f : A -> t B) :
  bind (ret a) f = f a.
Proof.
  reflexivity.
Qed.

(** Returning the result of a computation leaves the whole computation unchanged. *)
Theorem bind_ret_r {A : Type} (m : t A) : bind m ret = m.
Proof.
  unfold bind, ret.
  rewrite N.add_0_r.
  reflexivity.
Qed.

(** Reassociating sequencing leaves both the result and the total count unchanged. *)
Theorem bind_assoc {A B C : Type} (m : t A) (f : A -> t B) (g : B -> t C) :
  bind (bind m f) g = bind m (fun a => bind (f a) g).
Proof.
  unfold bind.
  cbn.
  rewrite N.add_assoc.
  reflexivity.
Qed.

End Cost.

Create Rewrite HintDb galois_cost.
#[export] Hint Rewrite
  @Cost.value_ret @Cost.ticks_ret @Cost.value_bind @Cost.ticks_bind
  @Cost.value_map @Cost.ticks_map Cost.value_tick Cost.ticks_tick
  Cost.value_step Cost.ticks_step @Cost.value_lift @Cost.ticks_lift
  Cost.value_tick_bits Cost.ticks_tick_bits @Cost.value_refine @Cost.ticks_refine
  : galois_cost.
