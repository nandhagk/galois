(** * Flat equality-saturation syntax

    Patterns and expressions store nodes in post-order and name their roots by index.
    For example, a literal pattern has one [PLit] node and root zero.
    Builds on: Egglog syntax and Stdlib lists. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.

Inductive pnode (V : Type) : Type :=
  | PHole (h : positive)
  | PApp (f : positive) (args : list nat)
  | PLit (v : V).

Arguments PHole {V}.
Arguments PApp {V}.
Arguments PLit {V}.

Record fpat (V : Type) : Type := FPat {
  nodes : list (pnode V);
  root : nat
}.

(** A pattern whose root is a constructor node. *)
Definition app_rooted {V} (p : fpat V) : Prop :=
  exists f children, nth_error (nodes V p) (root V p) = Some (PApp f children).

Inductive enode (V : Type) : Type :=
  | EApp (f : positive) (args : list nat)
  | ELit (v : V).

Arguments EApp {V}.
Arguments ELit {V}.

Record fexpr (V : Type) : Type := FExpr {
  expr_nodes : list (enode V);
  expr_root : nat
}.

Record rewrite (V : Type) : Type := Rewrite {
  lhs : fpat V;
  rhs : fpat V;
  cond : list (atom V)
}.

(** An expression node unfolds when each child refers to an earlier node. *)
Inductive unfolds_expr {V : Type} (ns : list (enode V)) : nat -> @Model.expr V -> Prop :=
  | unfold_expr_lit i v :
      nth_error ns i = Some (ELit v) -> unfolds_expr ns i (Model.ELit v)
  | unfold_expr_app i f children args :
      nth_error ns i = Some (EApp f children) ->
      Forall (fun j => j < i) children ->
      Forall2 (unfolds_expr ns) children args ->
      unfolds_expr ns i (Model.EApp f args).

(** A pattern hole unfolds to the expression supplied by its substitution. *)
Inductive unfolds_pat {V : Type} (tau : positive -> option (@Model.expr V))
    (ns : list (pnode V)) : nat -> @Model.expr V -> Prop :=
  | unfold_pat_hole i h e :
      nth_error ns i = Some (PHole h) -> tau h = Some e -> unfolds_pat tau ns i e
  | unfold_pat_lit i v :
      nth_error ns i = Some (PLit v) -> unfolds_pat tau ns i (Model.ELit v)
  | unfold_pat_app i f children args :
      nth_error ns i = Some (PApp f children) ->
      Forall (fun j => j < i) children ->
      Forall2 (unfolds_pat tau ns) children args ->
      unfolds_pat tau ns i (Model.EApp f args).

(** A flat expression denotes the value of any expression that it unfolds to. *)
Definition denotes_expr {V} (merge : positive -> V -> V -> V)
    (M : model (V := V)) (e : fexpr V) (value : carrier M + V) : Prop :=
  exists t, unfolds_expr (expr_nodes V e) (expr_root V e) t /\
    denote M t = value.

(** A flat pattern denotes the value of any expression obtained from its holes. *)
Definition denotes_pat {V} (merge : positive -> V -> V -> V)
    (M : model (V := V)) (tau : positive -> option (@Model.expr V))
    (p : fpat V) (value : carrier M + V) : Prop :=
  exists t, unfolds_pat tau (nodes V p) (root V p) t /\
    denote M t = value.

(** A flat pattern takes a value when its holes take carrier values. *)
Inductive pat_value {V : Type} (M : model (V := V)) (s : positive -> option (carrier M + V))
    (ns : list (pnode V)) : nat -> carrier M + V -> Prop :=
  | pat_value_hole i h c :
      nth_error ns i = Some (PHole h) -> s h = Some c -> pat_value M s ns i c
  | pat_value_lit i v :
      nth_error ns i = Some (PLit v) -> pat_value M s ns i (inr v)
  | pat_value_app i f children cs :
      nth_error ns i = Some (PApp f children) ->
      Forall (fun j => j < i) children ->
      Forall2 (pat_value M s ns) children cs ->
      pat_value M s ns i (inl (con M f cs)).

(** A rewrite equates the classes of its two sides under every assignment that meets its conditions. *)
Definition valid_rw {V} (prim : positive -> list V -> option V)
    (merge : positive -> V -> V -> V) (M : model (V := V))
    (kinds : positive -> option output) (rw : rewrite V) : Prop :=
  forall s x y,
    Forall (model_atom prim M kinds s) (cond V rw) ->
    pat_value M s (nodes V (lhs V rw)) (root V (lhs V rw)) (inl x) ->
    pat_value M s (nodes V (rhs V rw)) (root V (rhs V rw)) (inl y) -> x = y.
