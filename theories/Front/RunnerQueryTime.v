(** * Time of lookups and comparisons of cells

    The second part of the timed runner. A lookup of a row of values pays for its key at the
    unit of the database and for the bits of its values. A comparison of two classes pays for
    two finds and for the bits of the representative of the first class, and a comparison of
    two values pays for the bits of the first value.
    For example, [T_holds_le] bounds the points-to query of Andersen's analysis by one lookup of
    a key of two values.

    Builds on: the runner signature, the first part of the timed runner, and the time contracts
    of the values and the database. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig RunnerSeedTime.

Import List.ListNotations.
Import ComplexityNotations.

Module RunnerQueryT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D).
  Include RunnerSeedT V I J D R.
  Definition c_query : N := 1. (* STUB *)

  (* STUB: [D.T_lookup_le] on the key [map Val vs], whose unit is at least one. [c_query] must
     be at least [D.c_db] plus the overheads of the derived time functions. *)
  Lemma T_holds_le : forall r vs db, D.wf db ->
    (T_holds r vs db <= c_query * N.of_nat ((length vs + 1) * D.unit db +
      fold_right (fun v n => (cell_bits V.encode (Val v) + n)%nat) 0%nat vs + 1))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma holds_complexity :
    T_holds r vs db ∈
      𝑂(N.of_nat ((length vs + 1) * D.unit db +
        fold_right (fun v n => (cell_bits V.encode (Val v) + n)%nat) 0%nat vs))
      for (r, vs, db) | D.wf db.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [D.T_find_le] for both identifiers, [D.find_spec] and [Std.Pos.T_eqb_le] for the
     representatives, and [V.T_eqb_le] for values. [c_query] must also be at least [V.c_key]
     plus the overheads. *)
  Lemma T_same_cell_le : forall a b db, D.wf db ->
    (forall i, In (Id i) [a; b] -> D.allocated db i) ->
    (T_same_cell a b db <=
      c_query * N.of_nat (2 * D.unit db + cell_bits V.encode (D.canon db a) + 1))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma same_cell_complexity :
    T_same_cell a b db ∈ 𝑂(N.of_nat (D.unit db + cell_bits V.encode (D.canon db a)))
      for (a, b, db) | D.wf db /\ (forall i, In (Id i) [a; b] -> D.allocated db i).
  Proof.
  Admitted. (* STUB *)
End RunnerQueryT.
