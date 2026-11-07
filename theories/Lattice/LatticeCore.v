(** * Costed lattice dictionaries

    Operations compute independently of their weak order laws.
    For example, [simple implb false orb] orders booleans by implication.
    Builds on: CostMonad and Stdlib relations. *)

From Stdlib Require Import Bool Arith NArith Relation_Definitions.
From Galois.Cost Require Import CostMonad.
Import Cost.Notations.

(** A lattice dictionary holds costed callbacks and a bottom value. *)
Record lattice (A : Type) : Type := Lattice {
  leb_c : A -> A -> Cost.t bool;
  join_c : A -> A -> Cost.t A;
  widen_c : A -> A -> Cost.t A;
  narrow_c : A -> A -> Cost.t A;
  bot : A
}.

Arguments leb_c {A}.
Arguments join_c {A}.
Arguments widen_c {A}.
Arguments narrow_c {A}.
Arguments bot {A}.

(** Pure comparison observes the costed comparison's result. *)
Definition leb {A} (L : lattice A) a b := Cost.value (leb_c L a b).

(** Pure join observes the costed join's result. *)
Definition join {A} (L : lattice A) a b := Cost.value (join_c L a b).

(** Pure widening observes the costed widening's result. *)
Definition widen {A} (L : lattice A) a b := Cost.value (widen_c L a b).

(** Pure narrowing observes the costed narrowing's result. *)
Definition narrow {A} (L : lattice A) a b := Cost.value (narrow_c L a b).

(** Comparison is the value projection of the costed callback. *)
Theorem leb_equation {A} (L : lattice A) a b : leb L a b = Cost.value (leb_c L a b).
Proof.
  reflexivity.
Qed.

(** Join is the value projection of the costed callback. *)
Theorem join_equation {A} (L : lattice A) a b : join L a b = Cost.value (join_c L a b).
Proof.
  reflexivity.
Qed.

(** Widening is the value projection of the costed callback. *)
Theorem widen_equation {A} (L : lattice A) a b : widen L a b = Cost.value (widen_c L a b).
Proof.
  reflexivity.
Qed.

(** Narrowing is the value projection of the costed callback. *)
Theorem narrow_equation {A} (L : lattice A) a b : narrow L a b = Cost.value (narrow_c L a b).
Proof.
  reflexivity.
Qed.

(** Pure client callbacks charge one tick per operation. *)
Definition of_pure {A} (le : A -> A -> bool) (b : A)
    (j w n : A -> A -> A) : lattice A :=
  {| leb_c := fun x y => Cost.step ;; Cost.ret (le x y);
     join_c := fun x y => Cost.step ;; Cost.ret (j x y);
     widen_c := fun x y => Cost.step ;; Cost.ret (w x y);
     narrow_c := fun x y => Cost.step ;; Cost.ret (n x y);
     bot := b |}.

(** Finite-domain defaults widen by join and narrow by keeping the left input. *)
Definition simple {A} (le : A -> A -> bool) (b : A) (j : A -> A -> A) :=
  of_pure le b j j (fun x _ => x).

(** Replacing widening keeps comparison, bottom, join and narrowing unchanged. *)
Definition with_widen_c {A} (L : lattice A) (w : A -> A -> Cost.t A) : lattice A :=
  {| leb_c := leb_c L;
     join_c := join_c L;
     widen_c := w;
     narrow_c := narrow_c L;
     bot := bot L |}.

(** A pure replacement widening charges one tick. *)
Definition with_widen {A} (L : lattice A) (w : A -> A -> A) :=
  with_widen_c L (fun x y => Cost.step ;; Cost.ret (w x y)).

(** Replacing narrowing keeps comparison, bottom, join and widening unchanged. *)
Definition with_narrow_c {A} (L : lattice A) (n : A -> A -> Cost.t A) : lattice A :=
  {| leb_c := leb_c L;
     join_c := join_c L;
     widen_c := widen_c L;
     narrow_c := n;
     bot := bot L |}.

(** A pure replacement narrowing charges one tick. *)
Definition with_narrow {A} (L : lattice A) (n : A -> A -> A) :=
  with_narrow_c L (fun x y => Cost.step ;; Cost.ret (n x y)).

Section Pure.
Context {A : Type} (le : A -> A -> bool) (b : A) (j w n : A -> A -> A).

(** The pure constructor returns its supplied comparison. *)
Theorem leb_of_pure x y : leb (of_pure le b j w n) x y = le x y.
Proof.
  reflexivity.
Qed.

(** The pure constructor charges one tick for comparison. *)
Theorem ticks_leb_of_pure x y : Cost.ticks (leb_c (of_pure le b j w n) x y) = 1%N.
Proof.
  reflexivity.
Qed.

(** The pure constructor returns its supplied join. *)
Theorem join_of_pure x y : join (of_pure le b j w n) x y = j x y.
Proof.
  reflexivity.
Qed.

(** The pure constructor charges one tick for join. *)
Theorem ticks_join_of_pure x y : Cost.ticks (join_c (of_pure le b j w n) x y) = 1%N.
Proof.
  reflexivity.
Qed.

(** The pure constructor returns its supplied widening. *)
Theorem widen_of_pure x y : widen (of_pure le b j w n) x y = w x y.
Proof.
  reflexivity.
Qed.

(** The pure constructor charges one tick for widening. *)
Theorem ticks_widen_of_pure x y : Cost.ticks (widen_c (of_pure le b j w n) x y) = 1%N.
Proof.
  reflexivity.
Qed.

(** The pure constructor returns its supplied narrowing. *)
Theorem narrow_of_pure x y : narrow (of_pure le b j w n) x y = n x y.
Proof.
  reflexivity.
Qed.

(** The pure constructor charges one tick for narrowing. *)
Theorem ticks_narrow_of_pure x y : Cost.ticks (narrow_c (of_pure le b j w n) x y) = 1%N.
Proof.
  reflexivity.
Qed.
End Pure.

(** Weak laws require a preorder and bounds, without requiring least joins. *)
Record lattice_laws {A} (L : lattice A) : Prop := {
  leb_refl : forall a, leb L a a = true;
  leb_trans : forall a b c, leb L a b = true -> leb L b c = true -> leb L a c = true;
  bot_least : forall a, leb L (bot L) a = true;
  join_upper_l : forall a b, leb L a (join L a b) = true;
  join_upper_r : forall a b, leb L b (join L a b) = true;
  widen_upper_l : forall a b, leb L a (widen L a b) = true;
  widen_upper_r : forall a b, leb L b (widen L a b) = true;
  narrow_lower : forall a b, leb L b a = true -> leb L (narrow L a b) a = true;
  narrow_upper : forall a b, leb L b a = true -> leb L b (narrow L a b) = true
}.

(** Leastness of join is an optional law. *)
Record lub_laws {A} (L : lattice A) : Prop := {
  join_least : forall a b c, leb L a c = true -> leb L b c = true -> leb L (join L a b) c = true
}.

(** A supplied meet is a greatest lower bound. *)
Record meet_laws {A} (L : lattice A) (meet : A -> A -> A) : Prop := {
  meet_lower_l : forall a b, leb L (meet a b) a = true;
  meet_lower_r : forall a b, leb L (meet a b) b = true;
  meet_greatest : forall a b c, leb L c a = true -> leb L c b = true -> leb L c (meet a b) = true
}.

(** A top value bounds every element of the carrier. *)
Record top {A} (L : lattice A) : Type := Top {
  top_value : A;
  top_greatest : forall a, leb L a top_value = true
}.

Arguments leb_refl {A L}.
Arguments leb_trans {A L}.
Arguments bot_least {A L}.
Arguments join_upper_l {A L}.
Arguments join_upper_r {A L}.
Arguments widen_upper_l {A L}.
Arguments widen_upper_r {A L}.
Arguments narrow_lower {A L}.
Arguments narrow_upper {A L}.
Arguments join_least {A L}.
Arguments meet_lower_l {A L meet}.
Arguments meet_lower_r {A L meet}.
Arguments meet_greatest {A L meet}.
Arguments top_value {A L}.
Arguments top_greatest {A L}.

(** Equivalent values bound one another in the preorder. *)
Definition equivalent {A} (L : lattice A) a b :=
  leb L a b = true /\ leb L b a = true.

(** A boolean equality test recognizes carrier equality. *)
Definition eqb_spec {A} (eqb : A -> A -> bool) : Prop :=
  forall a b, eqb a b = true <-> a = b.

(** Closure holds for narrowing only when its second input is below its first input. *)
Record closed_on {A} (L : lattice A) (inv : A -> Prop) : Prop := {
  bot_inv : inv (bot L);
  join_inv : forall a b, inv a -> inv b -> inv (join L a b);
  widen_inv : forall a b, inv a -> inv b -> inv (widen L a b);
  narrow_inv : forall a b, inv a -> inv b -> leb L b a = true -> inv (narrow L a b)
}.

Arguments bot_inv {A L inv}.
Arguments join_inv {A L inv}.
Arguments widen_inv {A L inv}.
Arguments narrow_inv {A L inv}.

(** A uniform bound accounts for each callback on invariant inputs. *)
Definition cost_bounded_on {A} (L : lattice A) (inv : A -> Prop) (k : N) : Prop :=
  forall a b, inv a -> inv b ->
    (Cost.ticks (leb_c L a b) <= k)%N /\ (Cost.ticks (join_c L a b) <= k)%N /\
    (Cost.ticks (widen_c L a b) <= k)%N /\ (Cost.ticks (narrow_c L a b) <= k)%N.

(** Every pure callback has uniform cost one on any invariant. *)
Theorem of_pure_cost {A} le (b : A) j w n inv :
  cost_bounded_on (of_pure le b j w n) inv 1.
Proof.
  intros a a' Ha Ha'; repeat split; reflexivity.
Qed.

(** Five preorder and join facts suffice for the default widening and narrowing. *)
Theorem simple_laws {A} le (b : A) j :
  (forall a, le a a = true) ->
  (forall a b c, le a b = true -> le b c = true -> le a c = true) ->
  (forall a, le b a = true) ->
  (forall a b, le a (j a b) = true) ->
  (forall a b, le b (j a b) = true) ->
  lattice_laws (simple le b j).
Proof.
  intros Hrefl Htrans Hbot Hleft Hright; constructor;
    cbn [simple of_pure leb join widen narrow]; eauto.
Qed.

(** Replacing widening preserves weak laws when both new bounds hold. *)
Theorem with_widen_laws {A} (L : lattice A) w :
  lattice_laws L ->
  (forall a b, leb L a (w a b) = true) ->
  (forall a b, leb L b (w a b) = true) -> lattice_laws (with_widen L w).
Proof.
  intros H Hleft Hright; destruct H; constructor; assumption.
Qed.

(** Replacing widening leaves least joins unchanged. *)
Theorem with_widen_lub {A} (L : lattice A) w :
  lub_laws L -> lub_laws (with_widen L w).
Proof.
  intros [H]; constructor; exact H.
Qed.

(** A costed widening replacement obeys the same upper-bound contract on its value. *)
Theorem with_widen_c_laws {A} (L : lattice A) w :
  lattice_laws L ->
  (forall a b, leb L a (Cost.value (w a b)) = true) ->
  (forall a b, leb L b (Cost.value (w a b)) = true) ->
  lattice_laws (with_widen_c L w).
Proof.
  intros H Hleft Hright; destruct H; constructor; assumption.
Qed.

(** A costed widening replacement leaves least joins unchanged. *)
Theorem with_widen_c_lub {A} (L : lattice A) w :
  lub_laws L -> lub_laws (with_widen_c L w).
Proof.
  intros [H]; constructor; exact H.
Qed.

(** Replacing narrowing preserves weak laws under its two conditional bounds. *)
Theorem with_narrow_laws {A} (L : lattice A) n :
  lattice_laws L ->
  (forall a b, leb L b a = true -> leb L (n a b) a = true) ->
  (forall a b, leb L b a = true -> leb L b (n a b) = true) ->
  lattice_laws (with_narrow L n).
Proof.
  intros H Hlower Hupper; destruct H; constructor; assumption.
Qed.

(** Replacing narrowing leaves least joins unchanged. *)
Theorem with_narrow_lub {A} (L : lattice A) n :
  lub_laws L -> lub_laws (with_narrow L n).
Proof.
  intros [H]; constructor; exact H.
Qed.

(** A costed narrowing replacement obeys the conditional bounds on its value. *)
Theorem with_narrow_c_laws {A} (L : lattice A) n :
  lattice_laws L ->
  (forall a b, leb L b a = true -> leb L (Cost.value (n a b)) a = true) ->
  (forall a b, leb L b a = true -> leb L b (Cost.value (n a b)) = true) ->
  lattice_laws (with_narrow_c L n).
Proof.
  intros H Hlower Hupper; destruct H; constructor; assumption.
Qed.

(** A costed narrowing replacement leaves least joins unchanged. *)
Theorem with_narrow_c_lub {A} (L : lattice A) n :
  lub_laws L -> lub_laws (with_narrow_c L n).
Proof.
  intros [H]; constructor; exact H.
Qed.

(** Least joins preserve order in both arguments. *)
Theorem join_monotone {A} (L : lattice A) a a' b b' :
  lattice_laws L -> lub_laws L -> leb L a a' = true -> leb L b b' = true ->
  leb L (join L a b) (join L a' b') = true.
Proof.
  intros H Hlub Ha Hb; apply (join_least Hlub).
  - eapply (leb_trans H); [exact Ha | apply (join_upper_l H)].
  - eapply (leb_trans H); [exact Hb | apply (join_upper_r H)].
Qed.

(** Joining bottom changes a value only up to preorder equivalence. *)
Theorem join_bot_equivalent {A} (L : lattice A) a :
  lattice_laws L -> lub_laws L -> equivalent L (join L (bot L) a) a.
Proof.
  intros H Hlub; split.
  - apply (join_least Hlub); [apply (bot_least H) | apply (leb_refl H)].
  - apply (join_upper_r H).
Qed.

(** Assignments are ordered pointwise. *)
Definition fun_leb {X A} (L : lattice A) (s1 s2 : X -> A) : Prop :=
  forall x, leb L (s1 x) (s2 x) = true.

(** Unary monotonicity preserves boolean order. *)
Definition monotone_fun {A B} (L1 : lattice A) (L2 : lattice B) (f : A -> B) : Prop :=
  forall a b, leb L1 a b = true -> leb L2 (f a) (f b) = true.

(** Binary monotonicity preserves order in both inputs. *)
Definition monotone_fun2 {A B C} (L1 : lattice A) (L2 : lattice B) (L3 : lattice C)
    (f : A -> B -> C) : Prop :=
  forall a1 a2 b1 b2, leb L1 a1 a2 = true -> leb L2 b1 b2 = true ->
    leb L3 (f a1 b1) (f a2 b2) = true.

(** An assignment transfer preserves pointwise input order. *)
Definition monotone_on_assignments {X A B} (L1 : lattice A) (L2 : lattice B)
    (f : (X -> A) -> B) : Prop :=
  forall s1 s2, fun_leb L1 s1 s2 -> leb L2 (f s1) (f s2) = true.

Section Monotone.
Context {X A B C : Type} (L1 : lattice A) (L2 : lattice B) (L3 : lattice C).

(** Identity preserves order. *)
Theorem monotone_id : lattice_laws L1 -> monotone_fun L1 L1 (fun a => a).
Proof.
  intros _ a b Hab; exact Hab.
Qed.

(** Constants preserve order by reflexivity. *)
Theorem monotone_const b : lattice_laws L2 -> monotone_fun L1 L2 (fun _ => b).
Proof.
  intros H a a' _; apply (leb_refl H).
Qed.

(** Composition preserves unary monotonicity. *)
Theorem monotone_compose f g :
  monotone_fun L1 L2 f -> monotone_fun L2 L3 g -> monotone_fun L1 L3 (fun a => g (f a)).
Proof.
  intros Hf Hg a b Hab; apply Hg, Hf, Hab.
Qed.

(** A least join is a monotone binary operation. *)
Theorem monotone_join : lattice_laws L1 -> lub_laws L1 -> monotone_fun2 L1 L1 L1 (join L1).
Proof.
  intros H Hlub a a' b b' Ha Hb; exact (join_monotone L1 _ _ _ _ H Hlub Ha Hb).
Qed.

(** Constant transfers preserve assignment order. *)
Theorem monotone_on_const b : lattice_laws L2 ->
  @monotone_on_assignments X A B L1 L2 (fun _ => b).
Proof.
  intros H s1 s2 _; apply (leb_refl H).
Qed.

(** Reading an unknown preserves assignment order. *)
Theorem monotone_on_lookup x : @monotone_on_assignments X A A L1 L1 (fun s => s x).
Proof.
  intros s1 s2 H; apply H.
Qed.

(** Joining monotone transfers preserves monotonicity when joins are least. *)
Theorem monotone_on_join (f g : (X -> A) -> A) : lattice_laws L1 -> lub_laws L1 ->
  monotone_on_assignments L1 L1 f -> monotone_on_assignments L1 L1 g ->
  monotone_on_assignments L1 L1 (fun s => join L1 (f s) (g s)).
Proof.
  intros H Hlub Hf Hg s1 s2 Hs.
  apply (join_monotone L1 _ _ _ _ H Hlub); [apply Hf | apply Hg]; exact Hs.
Qed.

(** Composing an assignment transfer with a monotone function preserves order. *)
Theorem monotone_on_compose f g :
  @monotone_on_assignments X A B L1 L2 f -> monotone_fun L2 L3 g ->
  monotone_on_assignments L1 L3 (fun s => g (f s)).
Proof.
  intros Hf Hg s1 s2 Hs; apply Hg, Hf, Hs.
Qed.

(** Pointwise assignment order is a preorder whenever the value order is. *)
Theorem fun_leb_preorder : lattice_laws L1 ->
  preorder (X -> A) (fun s1 s2 => fun_leb L1 s1 s2).
Proof.
  intros H; constructor.
  - intros s x; apply (leb_refl H).
  - intros s1 s2 s3 H12 H23 x; eapply (leb_trans H); [apply H12 | apply H23].
Qed.
End Monotone.
