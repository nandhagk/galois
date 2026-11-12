(** * Bounded collections

    Supported collection values carry total heights through invariant restriction.
    For example, a bounded may set adds at most the number of universe keys.
    Builds on: LatticeSig, Sets and MapLattice. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time.
From Galois.Base Require Import KeySig MapSig SetSig.
From Galois.Lattice Require Import LatticeSig Sets MapLattice.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module BoundedCode (K : KEY_OPS) (S : SET_OPS K).
  Definition rank (s : S.t) : nat := length (S.elements s).
  Definition height (universe : S.t) : nat := length (S.elements universe).
End BoundedCode.

(** * Sets restricted to a universe *)

Module BoundedSetCode (K : KEY) (S : SET K) (U : UNIVERSE K S) <: LATTICE_OPS.
  Definition t := {s : S.t | S.subset s U.u = true}.

  (** Empty support lies inside the universe. *)
  Lemma bot_inside : S.subset S.empty U.u = true.
  Proof. Admitted.

  (** Union preserves the restriction to the universe. *)
  Lemma union_inside (a b : t) :
    S.subset (S.union (proj1_sig a) (proj1_sig b)) U.u = true.
  Proof. Admitted.

  (** Intersection clips any raw set to the universe. *)
  Lemma inter_inside (s : S.t) : S.subset (S.inter s U.u) U.u = true.
  Proof. Admitted.

  Definition leb (a b : t) : bool := S.subset (proj1_sig a) (proj1_sig b).
  Definition bot : t := exist _ S.empty bot_inside.
  Definition is_bot (a : t) : bool := S.subset (proj1_sig a) S.empty.
  Definition join (a b : t) : t :=
    exist _ (S.union (proj1_sig a) (proj1_sig b)) (union_inside a b).
  Definition clip (s : S.t) : t := exist _ (S.inter s U.u) (inter_inside s).
End BoundedSetCode.

Module BoundedSet (K : KEY) (S : SET K) (U : UNIVERSE K S) <: LATTICE.
  Include BoundedSetCode K S U.

  (** Restricted inclusion is reflexive. *)
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted.
  (** Restricted inclusion composes. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  (** The empty restricted set is least. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  (** The bottom test recognizes the empty restricted set. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized empty support is least. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Union contains its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  (** Union contains its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.
End BoundedSet.

Module BoundedSetT (K : KEY_T) (S : SET_T K) (U : UNIVERSE K S) <: LATTICE_T.
  Include BoundedSet K S U.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun clip.

  Definition size (a : t) : nat := S.weight (proj1_sig a).
  Definition c_lat : N := 1. (* STUB *)

  (** Restricted inclusion has the time bound of the underlying set operation. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Restricted union has the time bound of the underlying set operation. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Bottom testing charges the restricted support. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End BoundedSetT.

Module BoundedHeight (K : KEY) (S : SET K) (U : UNIVERSE K S)
    (Lat : LATTICE with Definition t := {s : S.t | S.subset s U.u = true}
                  with Definition leb :=
                    (fun (a b : {s : S.t | S.subset s U.u = true}) =>
                      S.subset (proj1_sig a) (proj1_sig b))) <: HEIGHT Lat.
  Definition rank (a : Lat.t) : nat :=
    length (filter (fun k => S.mem k (proj1_sig a)) (S.elements U.u)).
  Definition height : nat := length (S.elements U.u).

  (** The restricted support contains at most all universe keys. *)
  Lemma rank_le : forall a, rank a <= height.
  Proof. Admitted.
  (** Inclusion never removes a universe key. *)
  Lemma rank_mono : forall a b, Lat.leb a b = true -> rank a <= rank b.
  Proof. Admitted.
  (** Strict inclusion adds a universe key. *)
  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof. Admitted.
End BoundedHeight.
