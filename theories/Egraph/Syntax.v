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
