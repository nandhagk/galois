(** * Bounded collection fixtures

    Finite support supplies collection ranks.
    For example, the three-key chain reaches the universe size.
    Builds on: Bounded, TrieSet and Key.

    Groups:
    - [RankTests] Ranks and heights of clipped sets under a bounded universe.
    - [JoinTests] The order and join of clipped sets.
    - [ClipTests] Clipping removes keys outside the universe. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet.
From Galois.Lattice Require Import Bounded.
Import List.ListNotations.

(** * Fixtures *)

Module PosSet := TrieSet PosKey.

(** The empty set, then the sets that add 1, 2 and 3 in turn. *)
Definition s0 := PosSet.empty.
Definition s1 := PosSet.add 1%positive s0.
Definition s12 := PosSet.add 2%positive s1.
Definition s123 := PosSet.add 3%positive s12.

(** The universe of the keys 1, 2 and 3. *)
Module Universe.
  Definition u := s123.
  (** The universe is built by three lawful set insertions. *)
  Lemma u_wf : PosSet.wf u.
  Proof.
    apply PosSet.wf_add, PosSet.wf_add, PosSet.wf_add, PosSet.wf_empty.
  Qed.
End Universe.

(** The empty universe. *)
Module EmptyUniverse.
  Definition u := s0.
  (** The empty set is a lawful universe. *)
  Lemma u_wf : PosSet.wf u.
  Proof.
    apply PosSet.wf_empty.
  Qed.
End EmptyUniverse.

Module Bound := BoundedSet PosKey PosSet Universe.
Module Measure := BoundedHeight PosKey PosSet Universe Bound.
Module EmptyBound := BoundedSet PosKey PosSet EmptyUniverse.
Module EmptyMeasure := BoundedHeight PosKey PosSet EmptyUniverse EmptyBound.

(** The sets of the chain, clipped to the universe. *)
Definition b0 := Bound.clip s0.
Definition b1 := Bound.clip s1.
Definition b12 := Bound.clip s12.
Definition b123 := Bound.clip s123.

(** * Rank *)

Module RankTests.

  (** The clipped chain has ranks 0, 1, 2 and 3, one for each set in the chain. *)
  Example chain_ranks_run_from_0_to_3 :
    List.map Measure.rank [b0; b1; b12; b123] = [0; 1; 2; 3].
  Proof. vm_compute. reflexivity. Qed.

  (** The height of the bounded chain is three. *)
  Example chain_height_is_3 : Measure.height = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** An empty universe has height zero. *)
  Example bounded_empty_universe_height : EmptyMeasure.height = 0.
  Proof. vm_compute. reflexivity. Qed.

End RankTests.

(** * Join *)

Module JoinTests.

  (** The clipped set of one key is below the clipped set of two keys. *)
  Example clipped_subset_is_below : Bound.leb b1 b12 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The join of the two clipped sets lists its keys in trie order. *)
  Example join_lists_keys :
    PosSet.elements (proj1_sig (Bound.join b1 b12)) = [2%positive; 1%positive].

  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinTests.

(** * Clip *)

Module ClipTests.

  (** A key added to a set is a member of that set. *)
  Example added_outside_key_is_member : PosSet.mem 4%positive (PosSet.add 4%positive s0) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key outside the universe is not a member of the universe. *)
  Example universe_excludes_outside_key : PosSet.mem 4%positive Universe.u = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClipTests.

(* LatticeBoundedTest.outside_value_has_no_bounded_representative is a symbolic
   proof of the old within_set predicate. The new carrier carries S.subset = true.
   Bound.clip removes outside keys before constructing that carrier.
   bounded_environment_height_and_cost expects value coordinates (0, 1, 2).
   bounded_top_does_not_claim_an_unbounded_top expects (true, false). Both use
   bounded_env, env_height and bounded_env_top. Those constructors do not occur in
   the public Bounded API, which restricts sets. States.Env is a value-domain state
   functor and supplies neither an invariant-restricted map carrier nor map height.
   Their Cost.ticks coordinates retire with Cost. *)
