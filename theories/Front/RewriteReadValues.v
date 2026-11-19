(** * Premises over terms read as premises over values

    A premise of an equational clause reads its arguments under an environment of terms, and
    each argument of a premise that holds is a literal term. The query of a body reads the same
    premise under an environment of values. This file proves that a premise that holds under an
    environment of terms holds under [literal_env], which keeps the values of the literal terms,
    so the plans of the queries of bodies apply to the premises of a rewrite.

    For example, the premise [known x c] under the environment that maps [x] to [ELit 1] and [c]
    to [ELit 5] reads the row [known 1 5], and so does the same premise under the environment
    that maps [x] to [1] and [c] to [5].

    Builds on: the signature of rewrites that read rows, the meaning of equations that read
    rows, the meaning of lattice reads and the specifications. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec SpecLattice SpecReads RewriteReadSig.

Import List.ListNotations.

Module RewriteReadValues <: REWRITE_READ_VALUES_PLAN.
  (* STUB: prove by recursion on patterns, together for one pattern and a list of patterns, as
     [Fixpoint ... with ...], that [pat_term prim e p = Some (ELit v)] gives
     [pat_value prim (literal_env e) p = Some v], and that [pat_literals prim e ps = Some vs]
     gives [pat_values prim (literal_env e) ps = Some vs]. A constructor pattern has no literal
     term, a variable reads [literal_env] and a primitive applies to the values of its
     arguments. Each case of [read_premise] then gives the case of [premise_lat_in]. *)
  Lemma read_premise_values : forall {V} (prim : positive -> list V -> option V)
      (P : positive -> list V -> Prop) (Q : positive -> list V -> V -> Prop)
      (e : positive -> option (@expr V)) p,
    read_premise prim P Q e p -> premise_lat_in prim P Q (literal_env e) p.
  Proof.
  Admitted. (* STUB *)
End RewriteReadValues.
