(** * Top lifts

    A top lift adds a fresh value above an existing lattice.
    For example, joining Unknown with any element gives Unknown.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
Inductive lift_top (A : Type) : Type :=
  | Elem (a : A)
  | Unknown.

Arguments Elem {A}.
Arguments Unknown {A}.

Module Type TOP_LATTICE_OPS := LATTICE_OPS <+ HAS_TOP_OPS.

Module WithTopCode (L : LATTICE_OPS) <: TOP_LATTICE_OPS.
  Definition t := lift_top L.t.
  Definition leb (x y : t) : bool :=
    match x, y with
    | _, Unknown => true
    | Elem a, Elem b => L.leb a b
    | Unknown, Elem _ => false
    end.
  Definition bot : t := Elem L.bot.
  Definition is_bot (x : t) : bool :=
    match x with
    | Elem a => L.is_bot a
    | Unknown => false
    end.
  Definition join (x y : t) : t :=
    match x, y with
    | Elem a, Elem b => Elem (L.join a b)
    | _, _ => Unknown
    end.
  Definition top : t := Unknown.
End WithTopCode.
