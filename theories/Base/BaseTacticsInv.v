(** * Fold and cost inversion tactics

    These helpers expose fold invariants and costed option branches.
    For example, [fold_invariant P] reduces a left-fold invariant to initialization and closure.
    Builds on: Stdlib lists, BaseTactics and CostTactics.

    [case_key]: BaseKeyTactics.
    [solve_roundtrip]: BaseKeyTactics.
    [simpl_map]: BaseTactics.
    [simpl_set]: BaseTactics.
    [set_solver]: BaseTactics.
    [inv_option]: BaseTactics.
    [fold_invariant]: BaseTacticsInv.
    [inv_bind]: BaseTacticsInv. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Base Require Import BaseTactics.

(** An invariant initially true and preserved at each member holds after a left fold. *)
Theorem fold_left_invariant {A B} (f : B -> A -> B) (l : list A) (init : B)
    (P : B -> Prop) :
  P init -> (forall acc x, In x l -> P acc -> P (f acc x)) ->
  P (fold_left f l init).
Proof.
  revert init.
  induction l as [|x xs IH]; intros init Hinit Hstep; simpl.
  - exact Hinit.
  - apply IH.
    + apply Hstep; simpl; auto.
    + intros acc y Hy HP. apply Hstep; simpl; auto.
Qed.

(** An invariant initially true and preserved at each member holds after a right fold. *)
Theorem fold_right_invariant {A B} (f : A -> B -> B) (l : list A) (init : B)
    (P : B -> Prop) :
  P init -> (forall x acc, In x l -> P acc -> P (f x acc)) ->
  P (fold_right f init l).
Proof.
  induction l as [|x xs IH]; intros Hinit Hstep; simpl.
  - exact Hinit.
  - apply Hstep.
    + simpl; auto.
    + apply IH; auto. intros y acc Hy HP. apply Hstep; simpl; auto.
Qed.

(** A pointwise list precondition can be used to establish each left-fold step. *)
Theorem fold_invariant_gen {A B} (f : B -> A -> B) (l : list A) (init : B)
    (P : B -> Prop) (Q : A -> Prop) :
  Forall Q l -> P init -> (forall acc x, Q x -> P acc -> P (f acc x)) ->
  P (fold_left f l init).
Proof.
  intros Hall Hinit Hstep.
  apply fold_left_invariant; auto.
  intros acc x Hin HP. apply Hstep; auto.
  apply Forall_forall with (x := x) in Hall; auto.
Qed.

(** [fold_invariant P] applies the left-fold rule to a goal [P (fold_left f l init)],
    leaving initialization and then member-wise closure; it uses no hint database. *)
Ltac fold_invariant P :=
  lazymatch goal with
  | |- context [fold_left ?f ?l ?init] =>
    change (P (fold_left f l init));
    apply (fold_left_invariant f l init P)
  | _ => fail "fold_invariant: expected P (fold_left f l init)"
  end.

(** [inv_bind] accepts a hypothesis observing the value of a bind. It normalizes
    projections with [galois_cost], then uses [inv_option] to expose option cases;
    callback ticks and surviving branch equalities remain available to the caller. *)
Ltac inv_bind :=
  first
    [ match goal with
      | H : context [Cost.value (Cost.bind _ _)] |- _ => idtac
      end
    | fail 1 "inv_bind: no Cost.value hypothesis" ];
  autorewrite with galois_cost in *;
  cbn beta iota zeta in *;
  inv_option;
  cost_simpl.
