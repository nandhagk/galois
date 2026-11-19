(** * Lawful merges of lattice tables

    The theorems of lattice tables take a value module whose merge is commutative, associative
    and idempotent at every code and every value. A derived program merges with
    [prim_merge P.prim], which computes the primitive of its set and returns its first argument
    where the primitive has no result. On a value type whose decoder rejects some positives,
    such as [N], that merge is not commutative. The signatures of this file describe a merge
    that has the laws at every code and every positive and agrees with [prim_merge P.prim] on
    encodings. A join of decoded values ([DECODED]) belongs to the code of a primitive, and a
    merge at every code ([MERGE]) lifts such joins to positives. [LatticeMerge.v] builds the
    merges.

    For example, the join [N.lor] at the code [SetOps.lor_code] gives a merge that takes the
    union of two encoded sets of bits, and that agrees with [prim_merge SetOps.prim] on the
    encodings of [N].

    Main results
    - [join_comm], [join_assoc], [join_idem] A join has the laws of a semilattice.
    - [prim_join] The primitive at the code of a join computes the join on encodings.
    - [merge_comm], [merge_assoc], [merge_idem] A merge has the laws of the engine at every
      code.
    - [merge_agrees] At its codes, a merge agrees with the merge of the primitives on encodings.
    - [prim_merge_encoded] At those codes, the merge of the primitives keeps encodings.

    Builds on: the encoders of values and the merge of primitives. *)

From Stdlib Require Import List PArith.
From Galois.Front Require Import EncodeSig DeriveLattice.

Import List.ListNotations.

(** * Primitive sets *)

(** A primitive set, as the command [Egglog Primitives] defines it. *)
Module Type PRIMITIVES.
  (** The result of the primitive with a code on a list of engine values. *)
  Parameter prim : positive -> list positive -> option positive.
End PRIMITIVES.

(** * Joins of decoded values *)

(** A join of the values of an encoder, at the code of the primitive that merges a lattice
    table. *)
Module Type DECODED_OPS (E : ENCODE).
  (** The code of the primitive. *)
  Parameter code : positive.
  (** The join of two values. *)
  Parameter join : E.t -> E.t -> E.t.
End DECODED_OPS.

Module Type DECODED_LAWS (P : PRIMITIVES) (E : ENCODE) (Import D : DECODED_OPS E).
  (** Join order does not affect the value. *)
  Parameter join_comm : forall a b, join a b = join b a.
  (** Grouping joins does not affect the value. *)
  Parameter join_assoc : forall a b c, join a (join b c) = join (join a b) c.
  (** Joining a value with itself leaves it unchanged. *)
  Parameter join_idem : forall a, join a a = a.
  (** The primitive at the code computes the join on encodings. *)
  Parameter prim_join : forall x y,
    P.prim code [E.encode x; E.encode y] = Some (E.encode (join x y)).
End DECODED_LAWS.

Module Type DECODED (P : PRIMITIVES) (E : ENCODE) := DECODED_OPS E <+ DECODED_LAWS P E.

(** * Merges at every code *)

(** A merge of engine values at every code. *)
Module Type MERGE_OPS.
  (** The merge at a code of two engine values. *)
  Parameter merge : positive -> positive -> positive -> positive.
End MERGE_OPS.

Module Type MERGE_LAWS (P : PRIMITIVES) (Import M : MERGE_OPS).
  (* spec: codes encoded *)
  (** The codes at which the merge joins decoded values. *)
  Parameter codes : list positive.
  (** The engine values that encode a value of the type of the join at a code. *)
  Parameter encoded : positive -> positive -> Prop.
  (** Merge order does not affect the value. *)
  Parameter merge_comm : forall m a b, merge m a b = merge m b a.
  (** Grouping merges does not affect the value. *)
  Parameter merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  (** Merging a value with itself leaves it unchanged. *)
  Parameter merge_idem : forall m a, merge m a a = a.
  (** At its codes, the merge agrees with the merge of the primitives on encodings. *)
  Parameter merge_agrees : forall m a b, In m codes -> encoded m a -> encoded m b ->
    merge m a b = prim_merge P.prim m a b.
  (** At its codes, the merge of the primitives keeps encodings. *)
  Parameter prim_merge_encoded : forall m a b, In m codes -> encoded m a -> encoded m b ->
    encoded m (prim_merge P.prim m a b).
End MERGE_LAWS.

Module Type MERGE (P : PRIMITIVES) := MERGE_OPS <+ MERGE_LAWS P.
