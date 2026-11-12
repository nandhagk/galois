(** * Linear forms and constraints

    Linear forms evaluate weighted variables plus an integer constant.
    For example, coefficients [(x, 2)] and constant 1 describe twice x plus one.
    Builds on: Stdlib List, ZArith and QArith. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Time Std.

Record lin (X : Type) := Lin {
  coef : list (X * Z);
  cst : Z
}.

Inductive rel :=
  | REq
  | RLe.

Record lcons (X : Type) := LCons {
  lhs : list (X * Z);
  lrel : rel;
  rhs : Z
}.

Inductive wrapr :=
  | NoWrap
  | WrapTo (lo hi : Z).

Inductive cmp :=
  | CLe
  | CLt
  | CEq.

Record atom (X : Type) := Atom {
  al : lin X;
  alw : wrapr;
  acmp : cmp;
  ar : lin X;
  arw : wrapr
}.

Arguments coef {X} _.
Arguments cst {X} _.
Arguments lhs {X} _.
Arguments lrel {X} _.
Arguments rhs {X} _.
Arguments al {X} _.
Arguments alw {X} _.
Arguments acmp {X} _.
Arguments ar {X} _.
Arguments arw {X} _.
TimeFun coef.
TimeFun cst.
TimeFun lhs.
TimeFun lrel.
TimeFun rhs.
TimeFun al.
TimeFun alw.
TimeFun acmp.
TimeFun ar.
TimeFun arw.

(** Coefficient evaluation sums every stored occurrence of a variable. *)
Definition eval_coef {X} (v : X -> Z) (xs : list (X * Z)) : Z :=
  fold_right (fun p z => (snd p * v (fst p) + z)%Z) 0%Z xs.

TimeFun eval_coef.

(** Linear evaluation adds the constant to the weighted sum. *)
Definition eval_lin {X} (v : X -> Z) (f : lin X) : Z :=
  (eval_coef v (coef f) + cst f)%Z.

TimeFun eval_lin.

(** Wrapping uses the language's inclusive integer interval. *)
Definition wrap_into (r : wrapr) (z : Z) : Z :=
  match r with
  | NoWrap => z
  | WrapTo lo hi => (lo + (z - lo) mod (hi - lo + 1))%Z
  end.

TimeFun wrap_into.

(** Integer satisfaction interprets equality and non-strict inequality. *)
Definition sat {X} (v : X -> Z) (c : lcons X) : Prop :=
  match lrel c with
  | REq => eval_coef v (lhs c) = rhs c
  | RLe => (eval_coef v (lhs c) <= rhs c)%Z
  end.

(** Rational satisfaction embeds integer coefficients into rational arithmetic. *)
Definition satQ {X} (v : X -> Q) (c : lcons X) : Prop :=
  let z := fold_right (fun p q => (inject_Z (snd p) * v (fst p) + q)%Q) 0%Q (lhs c) in
  match lrel c with
  | REq => (z == inject_Z (rhs c))%Q
  | RLe => (z <= inject_Z (rhs c))%Q
  end.

(** Atoms compare the independently wrapped values of their two forms. *)
Definition atom_holds {X} (v : X -> Z) (a : atom X) : Prop :=
  let l := wrap_into (alw a) (eval_lin v (al a)) in
  let r := wrap_into (arw a) (eval_lin v (ar a)) in
  match acmp a with
  | CLe => (l <= r)%Z
  | CLt => (l < r)%Z
  | CEq => l = r
  end.
