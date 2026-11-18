(** * The reference congruence closure

    The reference closure of [ClosureSig.v] on the encodings of a small datatype. The terms are
    atoms, a unary wrapper and pairs, and an equation relates the encodings of two terms. Two
    terms are joined when they have one normal form.
    For example, with the equation [Wrap (Atom 1) = Atom 2], the pairs
    [Pair (Wrap (Atom 1)) (Atom 3)] and [Pair (Atom 2) (Atom 3)] are joined, because their first
    arguments are.

    Groups:
    - [ClassTests] The classes contain the equations and grow by congruence.
    - [FormTests] Normal forms extend the classes to every expression.

    Builds on: the reference closure and the derive command. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec Derive ClosureSig.
Import List.ListNotations.

(** * Fixtures *)

(** Terms built from atoms with a unary wrapper and pairs. *)
Inductive term : Type :=
  | Atom (n : positive)
  | Wrap (a : term)
  | Pair (a b : term).

(** Equality of terms, with the closure laws and one union for each listed pair of atoms. *)
Inductive same (merges : list (positive * positive)) : term -> term -> Prop :=
  | same_refl a : same merges a a
  | same_sym a b : same merges a b -> same merges b a
  | same_trans a b c : same merges a b -> same merges b c -> same merges a c
  | same_wrap a a' : same merges a a' -> same merges (Wrap a) (Wrap a')
  | same_pair a a' b b' : same merges a a' -> same merges b b' ->
      same merges (Pair a b) (Pair a' b')
  | same_merge x y : In (x, y) merges -> same merges (Atom x) (Atom y).

Egglog Terms from same.

(** The equations between the encodings of pairs of terms. *)
Definition encoded (eqs : list (term * term)) : list (@expr positive * @expr positive) :=
  map (fun tu => (Terms.encode_term (fst tu), Terms.encode_term (snd tu))) eqs.

(** The normal form of the encoding of a term in the closure of equations between terms. *)
Definition nf_of (eqs : list (term * term)) (t : term) : @expr positive :=
  nf Pos.eqb (encoded eqs) (Terms.encode_term t).

(** Whether two terms have one normal form. *)
Definition joined (eqs : list (term * term)) (t u : term) : bool :=
  expr_eqb Pos.eqb (nf_of eqs t) (nf_of eqs u).

(** * Classes *)

Module ClassTests.

  Local Open Scope positive_scope.

  (** One wrapped atom equals another atom. *)
  Definition wrapped_two : list (term * term) := [(Wrap (Atom 1), Atom 2)].

  (** The two sides of an equation are joined. *)
  Example equation_sides_are_joined :
    joined wrapped_two (Wrap (Atom 1)) (Atom 2) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The atom inside the wrapper is not joined with the other atom. *)
  Example inner_atom_stays_apart :
    joined wrapped_two (Atom 1) (Atom 2) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two equations that share a side chain. *)
  Definition chain : list (term * term) := [(Atom 1, Atom 2); (Atom 2, Atom 3)].

  (** The ends of a chain of equations are joined. *)
  Example chained_ends_are_joined :
    joined chain (Atom 1) (Atom 3) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Atoms 1 and 2 are equal, and their wrappers equal atoms 5 and 6. *)
  Definition wrapped_pair : list (term * term) :=
    [(Atom 1, Atom 2); (Wrap (Atom 1), Atom 5); (Wrap (Atom 2), Atom 6)].

  (** A pass joins the two wrappers by congruence, and with them atoms 5 and 6. *)
  Example congruence_joins_universe_terms :
    joined wrapped_pair (Atom 5) (Atom 6) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without the first equation the wrappers stay apart, and so do atoms 5 and 6. *)
  Example unequal_arguments_keep_classes_apart :
    joined (tl wrapped_pair) (Atom 5) (Atom 6) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClassTests.

(** * Normal forms *)

Module FormTests.

  Local Open Scope positive_scope.

  (** One wrapped atom equals another atom. *)
  Definition wrapped_two : list (term * term) := [(Wrap (Atom 1), Atom 2)].

  (** A pair outside the universe is joined with the pair of the equal arguments. *)
  Example pairs_of_equal_arguments_are_joined :
    joined wrapped_two (Pair (Wrap (Atom 1)) (Atom 3)) (Pair (Atom 2) (Atom 3)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A wrapper outside the universe follows its argument into a class. *)
  Example wrapper_follows_its_argument :
    joined wrapped_two (Wrap (Wrap (Atom 1))) (Wrap (Atom 2)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Wrappers of unequal atoms are not joined. *)
  Example wrappers_of_unequal_atoms_stay_apart :
    joined wrapped_two (Wrap (Atom 1)) (Wrap (Atom 3)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A term outside the universe that no equation reaches is its own normal form. *)
  Example unreached_term_is_its_own_form :
    nf_of wrapped_two (Pair (Atom 7) (Atom 8)) = Terms.encode_term (Pair (Atom 7) (Atom 8)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A literal of the universe stays its own normal form, because the equations relate only
      applications. *)
  Example literal_keeps_its_form :
    nf Pos.eqb (encoded wrapped_two) (ELit 1) = ELit 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FormTests.
