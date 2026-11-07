(** * Costed reduced products

    A descending reducer normalises comparisons and joins while widening stays unreduced.
    For example, a boolean reducer can clear the second slot when the first is false.
    Builds on: CostMonad, LatticeCore, LatticeConcrete, LatticeHeight and LatticeKit. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeHeight LatticeKit.
Import Cost.Notations.

(** A reducer supplies a runtime step and an input-dependent number of rounds. *)
Record reducer (A B : Type) : Type := Reducer {
  step_c : A -> B -> Cost.t (A * B);
  rounds : A * B -> nat
}.

Arguments step_c {A B}.
Arguments rounds {A B}.

(** The pure step observes the value of the costed callback. *)
Definition step {A B} (R : reducer A B) (x : A * B) :=
  Cost.value (step_c R (fst x) (snd x)).

(** Each round charges traversal and callback invocation separately. *)
Fixpoint reduce_steps_c {A B} (R : reducer A B) n (x : A * B) : Cost.t (A * B) :=
  match n with
  | O => Cost.ret x
  | S n' =>
    Cost.step ;;
    Cost.step ;;
    let* y := step_c R (fst x) (snd x) in
    reduce_steps_c R n' y
  end.

(** The pure runner performs exactly the requested rounds. *)
Definition reduce_steps {A B} (R : reducer A B) n x :=
  Cost.value (reduce_steps_c R n x).

(** Reduction evaluates the round count once on the original input. *)
Definition reduce_c {A B} (R : reducer A B) x :=
  reduce_steps_c R (rounds R x) x.

(** Reduction is the value projection of its costed runner. *)
Definition reduce {A B} (R : reducer A B) x := Cost.value (reduce_c R x).

(** The runner applies one step before processing the remaining rounds. *)
Theorem reduce_steps_equation {A B} (R : reducer A B) n x :
  reduce_steps R n x =
  match n with
  | O => x
  | S n' => reduce_steps R n' (step R x)
  end.
Proof.
  destruct n; reflexivity.
Qed.

(** Reducer laws separate semantic soundness and stability from runtime data. *)
Record reducer_laws {A B C} (P : lattice (A * B)) (G : concretisation (A * B) C)
    (R : reducer A B) : Prop := {
  step_lower : forall x, leb P (step R x) x = true;
  step_monotone : forall x y, leb P x y = true -> leb P (step R x) (step R y) = true;
  step_sound : forall x c, gamma G x c -> gamma G (step R x) c;
  step_stable : forall x, leb P (reduce R x) (step R (reduce R x)) = true
}.

Arguments step_lower {A B C P G R}.
Arguments step_monotone {A B C P G R}.
Arguments step_sound {A B C P G R}.
Arguments step_stable {A B C P G R}.

Section Reduction.
Context {A B C : Type} {P : lattice (A * B)} {G : concretisation (A * B) C}
  {R : reducer A B} (HP : lattice_laws P) (HR : reducer_laws P G R).

Local Lemma steps_lower n x : leb P (reduce_steps R n x) x = true.
Proof.
  revert x; induction n as [|n IH]; intro x; rewrite reduce_steps_equation.
  - apply (leb_refl HP).
  - eapply (leb_trans HP); [apply IH|apply (step_lower HR)].
Qed.

(** Completed reduction descends in the original preorder. *)
Theorem reduce_lower x : leb P (reduce R x) x = true.
Proof.
  apply steps_lower.
Qed.

Local Lemma fixed_below_steps n z y :
  leb P z (step R z) = true -> leb P z y = true ->
  leb P z (reduce_steps R n y) = true.
Proof.
  revert y; induction n as [|n IH]; intros y Hz Hzy; rewrite reduce_steps_equation.
  - exact Hzy.
  - apply IH; [exact Hz|].
    eapply (leb_trans HP); [exact Hz|apply (step_monotone HR); exact Hzy].
Qed.

(** Stability compares completed reductions even when their round counts differ. *)
Theorem reduce_monotone x y : leb P x y = true ->
  leb P (reduce R x) (reduce R y) = true.
Proof.
  intro Hxy; apply fixed_below_steps.
  - apply (step_stable HR).
  - eapply (leb_trans HP); [apply reduce_lower|exact Hxy].
Qed.

(** A completed reduction is idempotent up to the original preorder. *)
Theorem reduce_idempotent x : leb P (reduce R x) (reduce R (reduce R x)) = true.
Proof.
  apply fixed_below_steps; [apply (step_stable HR)|apply (leb_refl HP)].
Qed.

(** Every concrete value of the input survives all reduction rounds. *)
Theorem reduce_sound x c : gamma G x c -> gamma G (reduce R x) c.
Proof.
  unfold reduce, reduce_c; generalize (rounds R x) as n.
  intros n; revert x; induction n as [|n IH]; intros x Hx.
  - exact Hx.
  - apply IH, (step_sound HR); exact Hx.
Qed.
End Reduction.

(** Reduced operations use the plain product's slots only as input evidence. *)
Definition reduced {A B} (P : lattice (A * B)) {LA : lattice A} {LB : lattice B}
    (_S : slots2 P LA LB fst snd) (R : reducer A B) : lattice (A * B) :=
  {| leb_c := fun x y =>
       Cost.step ;; let* rx := reduce_c R x in Cost.step ;; leb_c P rx y;
     join_c := fun x y =>
       Cost.step ;; let* z := join_c P x y in reduce_c R z;
     widen_c := widen_c P;
     narrow_c := fun x y =>
       Cost.step ;; let* ry := reduce_c R y in Cost.step ;; narrow_c P x ry;
     bot := bot P |}.

Section Reduced.
Context {A B C : Type} (P : lattice (A * B)) {LA : lattice A} {LB : lattice B}
  (S : slots2 P LA LB fst snd) (G : concretisation (A * B) C) (R : reducer A B)
  (HP : lattice_laws P) (HR : reducer_laws P G R).

(** Reduced comparison normalises only its left operand. *)
Theorem reduced_leb x y : leb (reduced P S R) x y = leb P (reduce R x) y.
Proof.
  reflexivity.
Qed.

(** Reduced join normalises the result of the original join. *)
Theorem reduced_join x y : join (reduced P S R) x y = reduce R (join P x y).
Proof.
  reflexivity.
Qed.

(** Reducer-specific inequalities establish weak laws without exact reduced slots. *)
Theorem reduced_laws : lattice_laws (reduced P S R).
Proof.
  constructor.
  - apply (reduce_lower HP HR).
  - intros a b d Hab Hbd.
    eapply (leb_trans HP); [apply (reduce_idempotent HP HR)|].
    eapply (leb_trans HP); [apply (reduce_monotone HP HR _ _ Hab)|exact Hbd].
  - intro a; eapply (leb_trans HP); [apply (reduce_lower HP HR)|apply (bot_least HP)].
  - intros a b; apply (reduce_monotone HP HR), (join_upper_l HP).
  - intros a b; apply (reduce_monotone HP HR), (join_upper_r HP).
  - intros a b; eapply (leb_trans HP);
      [apply (reduce_lower HP HR)|apply (widen_upper_l HP)].
  - intros a b; eapply (leb_trans HP);
      [apply (reduce_lower HP HR)|apply (widen_upper_r HP)].
  - intros a b Hab; eapply (leb_trans HP);
      [apply (reduce_lower HP HR)|apply (narrow_lower HP _ _ Hab)].
  - intros a b Hab; apply (narrow_upper HP _ _ Hab).
Qed.

(** Least reduced joins require compatibility with joining normalised inputs. *)
Theorem reduced_lub (HL : lub_laws P)
    (Hjoin : forall x y, leb P (reduce R (join P x y))
      (join P (reduce R x) (reduce R y)) = true) :
  lub_laws (reduced P S R).
Proof.
  constructor; intros a b c Ha Hb.
  eapply (leb_trans HP); [apply (reduce_lower HP HR)|].
  eapply (leb_trans HP); [apply Hjoin|apply (join_least HL _ _ _ Ha Hb)].
Qed.

(** The original top bounds every normalised left operand. *)
Definition reduced_top (T : top P) : top (reduced P S R) :=
  @Top _ (reduced P S R) (top_value T) (fun x => top_greatest T (reduce R x)).

(** Reduced comparisons preserve meaning through sound normalisation of the left input. *)
Theorem reduced_gamma_laws : concretisation_laws P G ->
  concretisation_laws (reduced P S R) G.
Proof.
  intro HG; constructor; intros a b c Hab Hc.
  eapply (gamma_monotone HG); [exact Hab|apply (reduce_sound HR); exact Hc].
Qed.

(** Descending sound normalisation preserves the exact concrete meaning. *)
Theorem reduce_gamma_exact (HG : concretisation_laws P G) x c :
  gamma G (reduce R x) c <-> gamma G x c.
Proof.
  split.
  - apply (gamma_monotone HG _ _ _ (reduce_lower HP HR x)).
  - apply (reduce_sound HR).
Qed.

(** Unchanged widening inherits its rank even though reduced comparison is weaker. *)
Definition reduced_wrank {inv} (W : widening_rank_on P inv) :
  widening_rank_on (reduced P S R) inv.
Proof.
  refine {| wrank := wrank W; wbound := wbound W;
            wrank_bounded := wrank_bounded W |}.
  - intros a b Ha Hb _; apply (widening_rank_nonincreasing W a b Ha Hb).
  - intros a b Ha Hb Hstrict; apply (widen_rank_progress W a b Ha Hb).
    destruct (leb P b a) eqn:Hba; [|reflexivity].
    assert (Hred : leb P (reduce R b) a = true).
    { eapply (leb_trans HP); [apply (reduce_lower HP HR)|exact Hba]. }
    change (leb P (reduce R b) a = false) in Hstrict.
    rewrite Hred in Hstrict; discriminate.
Defined.

(** Height counts normalised states and needs closure under normalisation and plain joins. *)
Definition reduced_height (HL : lub_laws P) {inv} (HC : closed_on P inv)
    (Hinv : forall x, inv x -> inv (reduce R x)) (H : height_on P inv) :
  height_on (reduced P S R) inv.
Proof.
  refine {| rank := fun x => rank H (reduce R x); bound := bound H |}.
  - intros a Ha; apply (rank_bounded H), Hinv; exact Ha.
  - intros a b Ha Hb Hab; apply (rank_monotone H); try (apply Hinv; assumption).
    eapply (leb_trans HP); [apply (reduce_idempotent HP HR)|].
    apply (reduce_monotone HP HR); exact Hab.
  - intros a b Ha Hb Hstrict.
    pose (z := reduce R (join P a b)).
    assert (Hz : inv z) by (apply Hinv, (join_inv HC); assumption).
    assert (Hrz : inv (reduce R z)) by (apply Hinv; exact Hz).
    assert (Hra : inv (reduce R a)) by (apply Hinv; exact Ha).
    assert (Haz : leb P (reduce R a) (reduce R z) = true).
    { eapply (leb_trans HP).
      - apply (reduce_monotone HP HR), (join_upper_l HP).
      - apply (reduce_idempotent HP HR). }
    assert (Hnot : leb P (join P (reduce R a) (reduce R z)) (reduce R a) = false).
    { destruct (leb P (join P (reduce R a) (reduce R z)) (reduce R a)) eqn:Hle;
        [|reflexivity].
      assert (Hza : leb P (reduce R z) a = true).
      { eapply (leb_trans HP); [apply (join_upper_r HP)|].
        eapply (leb_trans HP); [exact Hle|apply (reduce_lower HP HR)]. }
      change (leb P (reduce R z) a = false) in Hstrict.
      rewrite Hza in Hstrict; discriminate. }
    pose proof (join_rank_grows H _ _ Hra Hrz Hnot) as Hgrow.
    assert (Hjoin : leb P (join P (reduce R a) (reduce R z)) (reduce R z) = true).
    { apply (join_least HL); [exact Haz|apply (leb_refl HP)]. }
    pose proof (rank_monotone H _ _ (join_inv HC _ _ Hra Hrz) Hrz Hjoin).
    change (rank H (reduce R a) < rank H (reduce R z)).
    lia.
Defined.
End Reduced.

(** Two ticks per round cover the loop cell and the callback invocation. *)
Definition reducer_k : N := 2.

(** A uniform callback bound gives a traversal-plus-callback bound for reduction. *)
Theorem reducer_cost {A B} (R : reducer A B) k :
  (forall a b, (Cost.ticks (step_c R a b) <= k)%N) ->
  forall x, (Cost.ticks (reduce_c R x) <= N.of_nat (rounds R x) * (k + reducer_k))%N.
Proof.
  intros Hk x; unfold reduce_c; generalize (rounds R x) as n.
  intros n; revert x; induction n as [|n IH]; intro x.
  - reflexivity.
  - cbn [reduce_steps_c]; autorewrite with galois_cost.
    specialize (IH (step R x)); specialize (Hk (fst x) (snd x)).
    rewrite Nat2N.inj_succ; unfold reducer_k in *; unfold step in IH; nia.
Qed.

(** A measure supplies runtime rounds without placing any law in the reducer data. *)
Definition rounds_of_measure {A B} (mu : A * B -> nat)
    (f : A -> B -> Cost.t (A * B)) : reducer A B :=
  {| step_c := f; rounds := mu |}.

(** Monotonicity preserves a stable state and strict measure decrease reaches one in time. *)
Theorem stable_of_measure {A B} (P : lattice (A * B)) mu f :
  let R := rounds_of_measure mu f in
  (forall x y, leb P x y = true -> leb P (step R x) (step R y) = true) ->
  (forall x, leb P x (step R x) = false -> mu (step R x) < mu x) ->
  forall x, leb P (reduce R x) (step R (reduce R x)) = true.
Proof.
  cbn zeta; intros Hmono Hmu.
  assert (Hstable : forall n x, leb P x (step (rounds_of_measure mu f) x) = true ->
    leb P (reduce_steps (rounds_of_measure mu f) n x)
      (step (rounds_of_measure mu f) (reduce_steps (rounds_of_measure mu f) n x)) = true).
  { induction n as [|n IH]; intros x Hx; rewrite reduce_steps_equation.
    - exact Hx.
    - apply IH, Hmono; exact Hx. }
  assert (Hbound : forall n x, mu x <= n ->
    leb P (reduce_steps (rounds_of_measure mu f) n x)
      (step (rounds_of_measure mu f) (reduce_steps (rounds_of_measure mu f) n x)) = true).
  { induction n as [|n IH]; intros x Hx.
    - rewrite reduce_steps_equation.
      destruct (leb P x (step (rounds_of_measure mu f) x)) eqn:Hstep; [reflexivity|].
      specialize (Hmu x Hstep); lia.
    - destruct (leb P x (step (rounds_of_measure mu f) x)) eqn:Hstep.
      + apply Hstable; exact Hstep.
      + rewrite reduce_steps_equation; apply IH.
        specialize (Hmu x Hstep); lia. }
  intro x; apply Hbound; reflexivity.
Qed.

(** Identity reduction performs no callbacks and keeps its argument exactly. *)
Definition identity_reducer {A B} : reducer A B :=
  {| step_c := fun a b => Cost.ret (a, b); rounds := fun _ => O |}.

(** The identity reducer has every reducer law for every lawful pair lattice and meaning. *)
Theorem identity_reducer_laws {A B C} (P : lattice (A * B))
    (G : concretisation (A * B) C) : lattice_laws P ->
  reducer_laws P G identity_reducer.
Proof.
  intro HP; constructor.
  - intros [a b]; apply (leb_refl HP).
  - intros [a b] [a' b'] Hle; exact Hle.
  - intros [a b] c Hc; exact Hc.
  - intros [a b]; apply (leb_refl HP).
Qed.

(** Identity reduction agrees with all original value operations and bottom. *)
Theorem reduced_identity {A B} (P : lattice (A * B)) {LA LB}
    (S : slots2 P LA LB fst snd) x y :
  leb (reduced P S identity_reducer) x y = leb P x y /\
  join (reduced P S identity_reducer) x y = join P x y /\
  widen (reduced P S identity_reducer) x y = widen P x y /\
  narrow (reduced P S identity_reducer) x y = narrow P x y /\
  bot (reduced P S identity_reducer) = bot P.
Proof.
  repeat split; reflexivity.
Qed.

(** Reduced operations retain every original callback and normalisation charge. *)
Theorem reduced_cost {A B} (P : lattice (A * B)) {LA LB}
    (S : slots2 P LA LB fst snd) R x y :
  Cost.ticks (leb_c (reduced P S R) x y) =
    (2 + Cost.ticks (reduce_c R x) + Cost.ticks (leb_c P (reduce R x) y))%N /\
  Cost.ticks (join_c (reduced P S R) x y) =
    (1 + Cost.ticks (join_c P x y) + Cost.ticks (reduce_c R (join P x y)))%N /\
  Cost.ticks (widen_c (reduced P S R) x y) = Cost.ticks (widen_c P x y) /\
  Cost.ticks (narrow_c (reduced P S R) x y) =
    (2 + Cost.ticks (reduce_c R y) + Cost.ticks (narrow_c P x (reduce R y)))%N.
Proof.
  unfold reduced; cbn [leb_c join_c widen_c narrow_c]; autorewrite with galois_cost.
  unfold reduce, join; repeat split; lia.
Qed.
