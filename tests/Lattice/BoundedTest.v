(** * Bounded collection fixtures

    Finite support supplies collection ranks.
    For example, the three-key chain reaches the universe size.
    Builds on: Bounded, TrieSet and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet.
From Galois.Lattice Require Import Bounded.
Import List.ListNotations.

Module PosSet := TrieSet PosKey.
Definition s0 := PosSet.empty.
Definition s1 := PosSet.add 1%positive s0.
Definition s12 := PosSet.add 2%positive s1.
Definition s123 := PosSet.add 3%positive s12.
Module Universe.
  Definition u := s123.
  (** The universe is built by three lawful set insertions. *)
  Lemma u_wf : PosSet.wf u.
  Proof.
    apply PosSet.wf_add, PosSet.wf_add, PosSet.wf_add, PosSet.wf_empty.
  Qed.
End Universe.
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
Definition b0 := Bound.clip s0.
Definition b1 := Bound.clip s1.
Definition b12 := Bound.clip s12.
Definition b123 := Bound.clip s123.

Example bounded_chain_reaches_bound :
  (List.map Measure.rank [b0; b1; b12; b123], Measure.height) = ([0; 1; 2; 3], 3).
Proof. vm_compute. reflexivity. Qed.
Example bounded_empty_universe_height : EmptyMeasure.height = 0.
Proof. vm_compute. reflexivity. Qed.

Example bounded_projection_and_join :
  (Bound.leb b1 b12, PosSet.elements (proj1_sig (Bound.join b1 b12))) =
  (true, [2%positive; 1%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Example bounded_outside_rejected :
  (PosSet.mem 4%positive (PosSet.add 4%positive s0), PosSet.mem 4%positive Universe.u) =
  (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeBoundedTest.outside_value_has_no_bounded_representative is a symbolic
   proof of the old within_set predicate. The new carrier carries S.subset = true.
   Bound.clip removes outside keys before constructing that carrier.
   bounded_environment_height_and_cost expects value coordinates (0, 1, 2).
   bounded_top_does_not_claim_an_unbounded_top expects (true, false). Both use
   bounded_env, env_height and bounded_env_top. Those constructors do not occur in
   the public Bounded API, which restricts sets. States.Env is a value-domain state
   functor and supplies neither an invariant-restricted map carrier nor map height.
   Their Cost.ticks coordinates retire with Cost. *)
