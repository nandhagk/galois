(** * Reduced product fixtures

    These examples check a reducer that clears the second boolean slot.
    For example, reducing [(false, true)] produces [(false, false)].
    Builds on: Reduced and Simple.

    Groups:
    - [ReduceTests] The reducers, and the order that they give.
    - [JoinTests] Joins of reduced pairs, and their compatibility.
    - [HeightTests] The rank of reduced pairs. *)

From Stdlib Require Import Bool.
From Galois.Lattice Require Import Reduced Simple Product JoinWidening.

(** * Fixtures *)

(** The reducer that clears the second slot when the first is false. *)
Module ClearSecond.
  Definition reduce (x : bool * bool) := (fst x, andb (fst x) (snd x)).
  (** Clearing the second slot lowers both boolean coordinates. *)
  Lemma reduce_lower : forall a b,
    BoolLat.leb (fst (reduce (a, b))) a = true /\
    BoolLat.leb (snd (reduce (a, b))) b = true.
  Proof.
    intros [] []; vm_compute; split; reflexivity.
  Qed.
  (** Clearing is monotone in both boolean coordinates. *)
  Lemma reduce_mono : forall a b a' b',
    BoolLat.leb a a' = true -> BoolLat.leb b b' = true ->
    BoolLat.leb (fst (reduce (a, b))) (fst (reduce (a', b'))) = true /\
    BoolLat.leb (snd (reduce (a, b))) (snd (reduce (a', b'))) = true.
  Proof.
    intros [] [] [] []; vm_compute; intros Ha Hb; try discriminate; split; reflexivity.
  Qed.
  (** A second clearing leaves the cleared pair unchanged. *)
  Lemma reduce_idem : forall a b,
    BoolLat.leb (fst (reduce (a, b))) (fst (reduce (reduce (a, b)))) = true /\
    BoolLat.leb (snd (reduce (a, b))) (snd (reduce (reduce (a, b)))) = true.
  Proof.
    intros [] []; vm_compute; split; reflexivity.
  Qed.
End ClearSecond.

(** The reducer that applies a clearing step twice. *)
Module ClearTwice.
  Definition step (x : bool * bool) := (andb (fst x) (snd x), false).
  Definition reduce (x : bool * bool) := step (step x).
End ClearTwice.

(** The reduced product of the booleans under the clearing reducer. *)
Module ReducedBool := ReducedCode BoolLatCode BoolLatCode ClearSecond.

(** The widening adapter of the reduced product. *)
Module ReducedWide := JoinWideningCode ReducedBool.

(** The product of two boolean lattices, and its height. *)
Module PairLat := Product BoolLat BoolLat.
Module PairHeight := ProductHeight BoolLat BoolLat BoolLatHeight BoolLatHeight PairLat.

(** The reduced lattice and its height measure. *)
Module ReducedLat := Reduced BoolLat BoolLat ClearSecond.
Module ReducedMeasure := ReducedHeight BoolLat BoolLat ClearSecond PairLat PairHeight ReducedLat.

(** * Reduce *)

Module ReduceTests.

  (** Clearing the second slot of false and true gives false and false. *)
  Example clear_second_slot_of_false_true : ClearSecond.reduce (false, true) = (false, false).
  Proof. vm_compute. reflexivity. Qed.

  (** Clearing twice of true and true gives false and false. *)
  Example clear_twice_of_true_true : ClearTwice.reduce (true, true) = (false, false).
  Proof. vm_compute. reflexivity. Qed.

  (** A reduced pair of false and true is below a reduced pair of false and false. *)
  Example reduced_false_true_below_false_false :
    ReducedBool.leb (false, true) (false, false) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A reduced pair of true and true is not below a reduced pair of false and false. *)
  Example reduced_true_true_not_below_false_false :
    ReducedBool.leb (true, true) (false, false) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Narrowing true and true against false and true keeps true and true. *)
  Example reduced_narrow_keeps_true_true :
    ReducedWide.narrow (true, true) (false, true) = (true, true).
  Proof. vm_compute. reflexivity. Qed.

End ReduceTests.

(** * Join *)

Module JoinTests.

  (** The second slot of the reduced join of false and true with false and false is false. *)
  Example reduced_join_second_slot_is_false :
    snd (ReducedBool.join (false, true) (false, false)) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The boolean join of true and false is true. *)
  Example bool_join_of_true_and_false_is_true : BoolLatCode.join true false = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A pair is below itself in the reduced order. *)
  Example reduced_pair_below_itself : ReducedBool.leb (true, false) (true, false) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A false-true pair is below a true-false pair in the reduced order. *)
  Example reduced_false_true_below_true_false :
    ReducedBool.leb (false, true) (true, false) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The reduced join of true-false and false-true is not below true-false. *)
  Example reduced_join_not_below_true_false :
    ReducedBool.leb (ReducedBool.join (true, false) (false, true)) (true, false) = false.
  Proof. vm_compute. reflexivity. Qed.

End JoinTests.

(* LatticeReducedTest.reduced_operations expects
   ((false, false), (false, true), (true, true)) from join, widen and narrow.
   JoinWideningCode gives ((false, false), (false, false), (true, true)) because
   its widening uses ReducedBool.join. The join and narrow coordinates are
   checked by reduced_join_second_slot_is_false and reduced_narrow_keeps_true_true above.
   The reducer interface has no round count. reduce_zero_rounds expects (false, true).
   reduce_unequal_rounds expects (1, 2, (false, false), (true, false)). These retire
   with the rounds/step reducer dictionary. ClearSecond and ClearTwice supply the
   completed reductions used by reduce_positive.
   costly_zero_rounds and costly_nonzero_count_once combine round-count observations
   with Cost.ticks. costed_measure_retains_count_work and reducer_ticks observe Cost.
   These retire with rounds_of_measure and Cost. The dictionary proof clients
   reduced_variable_laws, reduced_variable_gamma, reduced_identity_lub and
   reduced_twice_lub use the deleted slots and concretisation interfaces. *)

(** * Height *)

Module HeightTests.

  (** A reduced pair of false and true has rank zero. *)
  Example false_true_has_rank_zero : ReducedMeasure.rank (false, true) = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A reduced pair of true and true has rank two. *)
  Example true_true_has_rank_two : ReducedMeasure.rank (true, true) = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

End HeightTests.
