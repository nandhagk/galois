(** * Bottom lifts

    Option adds a fresh bottom while retaining reached values.
    For example, joining None and Some a returns Some a.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.

Module WithBotCode (L : LATTICE_OPS) <: LATTICE_OPS.
  Definition t := option L.t.
  Definition leb (x y : t) : bool :=
    match x, y with
    | None, _ => true
    | Some a, Some b => L.leb a b
    | Some _, None => false
    end.
  Definition bot : t := None.
  Definition is_bot (x : t) : bool :=
    match x with
    | None => true
    | Some _ => false
    end.
  Definition join (x y : t) : t :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some a, Some b => Some (L.join a b)
    end.
End WithBotCode.
