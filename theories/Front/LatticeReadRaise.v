(** * Raising the values that a clause reads

    A clause that reads lattice values in a monotone frame ([clause_reads_ok]) reads each value
    into a variable that occurs once in its body and in no key of its head. When its body holds
    with read values below the values that a view stores, it holds again with the stored values,
    under an environment that differs only at the read variables ([body_reads_raise]), and the
    keys of its head keep their values ([head_keys_raise]). A clause that derives a row of a
    well-sorted specification derives it into a relation table ([derive_head_rel]).

    For example, the shortest-path clause that reads the distance [d] at [[a; b]] also holds
    with [d] replaced by the shortest distance that a view stores there, and its key [[a; c]]
    does not change.

    Builds on: the lattice-read signature, the meaning of lattice reads and the lowering. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import Syntax Model Sorts RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig LatticeReadSig.

Import List.ListNotations.

Module LatticeReadRaise <: LATTICE_READ_RAISE_PLAN.
  (* STUB: induction on the premises. A read [Equals f args (PVar x)] gives a stored value
     [u'] above the read value, and [e'] maps [x] to [u']. Every other premise has no read
     variable, because a read variable occurs once in the body, so it keeps its values. *)
  Lemma body_reads_raise : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) (w : @view V) c e,
    clause_reads_ok c = true ->
    Forall (premise_lat_in prim (view_rows w) (stored_above merge s w) e) (body c) ->
    exists e', env_below merge s c e e' /\
      Forall (premise_lat_in prim (view_rows w) (stored_at w) e') (body c).
  Proof.
  Admitted. (* STUB *)

  (* STUB: the value of a pattern depends only on its variables, and no variable of a key of
     the head is a read variable. *)
  Lemma head_keys_raise : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) c e e',
    clause_reads_ok c = true -> env_below merge s c e e' ->
    pat_values prim e' (head_keys (head c)) = pat_values prim e (head_keys (head c)).
  Proof.
  Admitted. (* STUB *)

  (* STUB: [check_program_spec] gives the sorts of the rule of [c], whose last action is
     [Put r ts None]. A put without output needs a table whose output sort is none, so [ORel]. *)
  Lemma derive_head_rel : forall {V} (s : spec V) c r args,
    spec_ok s = true -> In c (clauses s) -> head c = Derive r args ->
    lookup_kind (tables s) r = Some ORel.
  Proof.
  Admitted. (* STUB *)
End LatticeReadRaise.
