(** * Flat lattices

    Flat values distinguish bottom, a known value and top.
    For example, joining distinct known values gives top.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
From Galois.Base Require Import KeySig.

Inductive flat (A : Type) : Type :=
  | FBot
  | FVal (a : A)
  | FTop.

Arguments FBot {A}.
Arguments FVal {A}.
Arguments FTop {A}.

(** Flat comparison uses the supplied test for known values. *)
Definition flat_leb {A} (eqb : A -> A -> bool) (x y : flat A) : bool :=
  match x, y with
  | FBot, _ => true
  | _, FTop => true
  | FVal a, FVal b => eqb a b
  | _, _ => false
  end.

(** Flat join preserves equal known values and otherwise returns top. *)
Definition flat_join {A} (eqb : A -> A -> bool) (x y : flat A) : flat A :=
  match x, y with
  | FBot, _ => y
  | _, FBot => x
  | FVal a, FVal b => if eqb a b then FVal a else FTop
  | _, _ => FTop
  end.

(** Flat widening is join and narrowing keeps its left input. *)
Module FlatCode (K : KEY_OPS) <: BLATTICE_OPS.
  Definition t := flat K.t.
  Definition leb := flat_leb K.eqb.
  Definition bot : t := FBot.
  Definition is_bot (x : t) := match x with FBot => true | _ => false end.
  Definition join := flat_join K.eqb.
  Definition top : t := FTop.
  Definition meet (x y : t) : t :=
    match x, y with
    | FTop, _ => y
    | _, FTop => x
    | FVal a, FVal b => if K.eqb a b then FVal a else FBot
    | _, _ => FBot
    end.
End FlatCode.
