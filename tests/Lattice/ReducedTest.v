(** * Reduced product fixtures

    These examples check a reducer that clears the second boolean slot.
    For example, reducing [(false, true)] produces [(false, false)].
    Builds on: Reduced and Simple. *)

From Stdlib Require Import Bool.
From Galois.Lattice Require Import Reduced Simple Product JoinWidening.

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
Module ClearTwice.
  Definition step (x : bool * bool) := (andb (fst x) (snd x), false).
  Definition reduce (x : bool * bool) := step (step x).
End ClearTwice.
Module ReducedBool := ReducedCode BoolLatCode BoolLatCode ClearSecond.
Module ReducedWide := JoinWideningCode ReducedBool.
Module PairLat := Product BoolLat BoolLat.
Module PairHeight := ProductHeight BoolLat BoolLat BoolLatHeight BoolLatHeight PairLat.
Module ReducedLat := Reduced BoolLat BoolLat ClearSecond.
Module ReducedMeasure := ReducedHeight BoolLat BoolLat ClearSecond PairLat PairHeight ReducedLat.

Example reduce_positive :
  (ClearSecond.reduce (false, true), ClearTwice.reduce (true, true)) =
    ((false, false), (false, false)).
Proof. vm_compute. reflexivity. Qed.
Example reduce_negative :
  (ReducedBool.leb (false, true) (false, false),
    ReducedBool.leb (true, true) (false, false)) = (true, false).
Proof. vm_compute. reflexivity. Qed.
Example reduced_narrow :
  ReducedWide.narrow (true, true) (false, true) = (true, true).
Proof. vm_compute. reflexivity. Qed.
Example reduced_join_is_not_an_exact_slot :
  (snd (ReducedBool.join (false, true) (false, false)), BoolLatCode.join true false) =
    (false, true).
Proof. vm_compute. reflexivity. Qed.
Example reduced_join_needs_compatibility :
  (ReducedBool.leb (true, false) (true, false),
    ReducedBool.leb (false, true) (true, false),
    ReducedBool.leb (ReducedBool.join (true, false) (false, true)) (true, false)) =
    (true, true, false).
Proof. vm_compute. reflexivity. Qed.

(* LatticeReducedTest.reduced_operations expects
   ((false, false), (false, true), (true, true)) from join, widen and narrow.
   JoinWideningCode gives ((false, false), (false, false), (true, true)) because
   its widening uses ReducedBool.join. The join and narrow coordinates are
   checked by reduced_join_is_not_an_exact_slot and reduced_narrow above.
   The reducer interface has no round count. reduce_zero_rounds expects (false, true).
   reduce_unequal_rounds expects (1, 2, (false, false), (true, false)). These retire
   with the rounds/step reducer dictionary. ClearSecond and ClearTwice supply the
   completed reductions used by reduce_positive.
   costly_zero_rounds and costly_nonzero_count_once combine round-count observations
   with Cost.ticks. costed_measure_retains_count_work and reducer_ticks observe Cost.
   These retire with rounds_of_measure and Cost. The dictionary proof clients
   reduced_variable_laws, reduced_variable_gamma, reduced_identity_lub and
   reduced_twice_lub use the deleted slots and concretisation interfaces. *)

Example reduced_height_counts_normalised_slots :
  (ReducedMeasure.rank (false, true), ReducedMeasure.rank (true, true)) = (0, 2).
Proof.
  vm_compute. reflexivity.
Qed.
