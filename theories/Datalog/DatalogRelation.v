(** * Valid finite relations

    Relations use valid finite sets of tuples and inherit the may lattice.
    For example, the join of two relations contains each tuple in either input.
    Builds on: BaseCode, LatticeSet and DatalogSyntax. *)

From Stdlib Require Import List.
From Galois.Base Require Import BaseEncoding BaseCode.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet.
From Galois.Datalog Require Import DatalogSyntax.

(** * Relation carrier and order *)

Definition tuple_encoding : encoding tuple := codec_enc (list_codec positive_codec).

(** List decoding establishes injectivity of tuple keys. *)
Theorem tuple_encoding_laws : encoding_laws tuple_encoding.
Proof.
  apply codec_laws_injective, list_codec_laws, positive_codec_laws.
Qed.

Definition relation : Type := set_t tuple_encoding.

Definition relation_lattice : lattice relation := may tuple_encoding.

(** Relation inclusion and union satisfy the weak lattice laws. *)
Theorem relation_laws : lattice_laws relation_lattice.
Proof.
  apply may_laws, tuple_encoding_laws.
Qed.

(** Relation union is a least upper bound. *)
Theorem relation_lub_laws : lub_laws relation_lattice.
Proof.
  apply may_lub, tuple_encoding_laws.
Qed.

(** Cardinality gives finite height for relations supported by a universe list. *)
Theorem relation_height_on (universe : list tuple) :
  height_on relation_lattice (within_set tuple_encoding universe).
Proof.
  apply may_height, tuple_encoding_laws.
Defined.
