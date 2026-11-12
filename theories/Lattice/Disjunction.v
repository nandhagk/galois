(** * Capped disjunction lattices

    Lists denote unions and compare by coverage of every alternative.
    For example, cap one collapses two incomparable flat values to their top.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
Import List.ListNotations.

Module DisjunctionCode (L : WLATTICE_OPS) (C : CAP) <: WLATTICE_OPS.
  Definition t := list L.t.
  Definition leb (xs ys : t) := forallb (fun x => existsb (L.leb x) ys) xs.
  Definition bot : t := [].
  Definition is_bot (xs : t) := match xs with [] => true | _ => false end.
  Definition join_all (xs : t) : L.t :=
    match xs with
    | [] => L.bot
    | x :: rest => fold_left L.join rest x
    end.
  Fixpoint compact_tail (n : nat) (xs : t) : t :=
    match n, xs with
    | S m, x :: rest => x :: compact_tail m rest
    | _, _ => [join_all xs]
    end.
  Definition compact (xs : t) :=
    if Nat.leb (length xs) C.k then xs else compact_tail (C.k - 1) xs.
  Definition join (xs ys : t) := compact (xs ++ ys).
  Definition wparam := L.wparam.
  Definition widen (p : wparam) (xs ys : t) :=
    if leb ys xs then xs else [L.widen p (join_all xs) (join_all (xs ++ ys))].
  Definition narrow (xs _ : t) := xs.
End DisjunctionCode.
