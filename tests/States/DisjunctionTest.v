(** * Bounded state disjunction observations

    The shared bounded carrier holds alternatives and state transfers map over them.
    For example, a cap of one collapses two alternatives into one state.
    Builds on: State Disjunction, Env and the shared disjunction lattice.

    Groups:
    - [BottomTests] The empty disjunction.
    - [JoinTests] Joins of capped alternatives.
    - [WideningTests] Widening of alternatives, including the empty case.
    - [HavocTests] Havoc of a capped disjunction.
    - [MeetTests] Meets of capped disjunctions.
    - [PartitionTests] The labelled partition that the disjunction is built on. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import Disjunction.
From Galois.Domains Require Import ValueSig IntervalSig Interval ThresholdsSig Thresholds ZLang.
From Galois.States Require Import EnvSig Env Disjunction Partition.
Import List.ListNotations.

(** * Fixtures *)

Module NatMap := TrieMapCode NatKeyCode.
Module Values := IntervalCode ZLangCode ThresholdsCode.
Module State := EnvCode NatKeyCode NatMap ZLangCode Values.

(** A cap of one alternative. *)
Module Cap.
  Definition k := 1%nat.
End Cap.
Module Shared := DisjunctionCode State Cap.
Module D := StateDisjunctionCode NatKeyCode ZLangCode Values State Cap Shared.

(** A cap of two alternatives. *)
Module Cap2.
  Definition k := 2%nat.
End Cap2.
Module Shared2 := DisjunctionCode State Cap2.
Module D2 := StateDisjunctionCode NatKeyCode ZLangCode Values State Cap2 Shared2.

(** The reached state that binds variable 1 to the interval [lo, hi]. *)
Definition interval_state (lo hi : Z) : State.t :=
  Reached (NatMap.set 1%nat (I (Fin lo) (Fin hi)) NatMap.empty).

(** Two alternatives, [0, 10] and [20, 30], clipped to the cap of two. *)
Definition meet_left := Shared2.clip [interval_state 0 10; interval_state 20 30].

(** Two alternatives, [5, 25] and [27, 28], clipped to the cap of two. *)
Definition meet_right := Shared2.clip [interval_state 5 25; interval_state 27 28].

Module BottomTests.

  (** The empty disjunction is bottom. *)
  Example empty_is_bottom : D.is_bot D.bot = true.
  Proof. vm_compute. reflexivity. Qed.

End BottomTests.

Module JoinTests.

  (** Joining two clipped alternatives under a cap of one leaves one alternative. *)
  Example join_keeps_one_alternative_at_cap_one :
    length (proj1_sig (D.join (Shared.clip [State.top]) (Shared.clip [State.top]))) = 1%nat.
  Proof. vm_compute. reflexivity. Qed.

End JoinTests.

Module WideningTests.

  (** Widening a stable disjunction keeps its alternatives. *)
  Example stable_widening_keeps_alternatives :
    D.widen TLeaf (Shared.clip [State.top]) (Shared.clip [State.top]) =
      Shared.clip [State.top].
  Proof. vm_compute. reflexivity. Qed.

  (** Widening an empty disjunction returns the candidate alternatives. *)
  Example empty_widening_returns_candidate :
    proj1_sig (D2.widen TLeaf D2.bot (Shared2.clip [interval_state 0 0])) =
      [interval_state 0 0].
  Proof. vm_compute. reflexivity. Qed.

End WideningTests.

Module HavocTests.

  (** Havoc of a capped disjunction keeps the number of its alternatives. *)
  Example havoc_keeps_alternative_count :
    length (proj1_sig (D.havoc 1%nat (Shared.clip [State.top]))) = 1%nat.
  Proof. vm_compute. reflexivity. Qed.

End HavocTests.

Module MeetTests.

  (** The meet under a cap of two keeps the intersections of the alternatives. *)
  Example capped_meet_keeps_intersections :
    proj1_sig (D2.meet meet_left meet_right) = [interval_state 5 10; interval_state 20 28].
  Proof. vm_compute. reflexivity. Qed.

  (** The capped meet does not refine the right operand, so the order fails. *)
  Example capped_meet_does_not_refine_right :
    D2.leb (D2.meet meet_left meet_right) meet_right = false.
  Proof. vm_compute. reflexivity. Qed.

End MeetTests.

Module PartitionTests.

  (** The labelled partition that the disjunction is built on. *)
  Module Parts := PartitionCode NatKeyCode NatKeyCode ZLangCode Values State Cap2.

  (** A null part is below the empty partition. *)
  Example null_parts_are_ignored :
    Parts.leb (Parts.inject 1%nat State.bot) Parts.bot = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Parts under equal labels merge into one part with that label. *)
  Example equal_labels_merge :
    map fst (proj1_sig (Parts.join (Parts.inject 1%nat State.top)
      (Parts.inject 1%nat State.bot))) = [Some 1%nat].
  Proof. vm_compute. reflexivity. Qed.

  (** When parts overflow the cap, the first label stays and the rest go under no label. *)
  Example overflow_keeps_first_label :
    map fst (proj1_sig (Parts.join (Parts.join (Parts.inject 1%nat State.top)
      (Parts.inject 2%nat State.top)) (Parts.inject 3%nat State.top))) =
      [Some 1%nat; None].
  Proof. vm_compute. reflexivity. Qed.

  (** A stray part widens the first part that is not null. *)
  Example stray_widens_first_nonnull_part :
    Parts.leb (Parts.inject 3%nat (interval_state 5 5))
      (Parts.widen TLeaf (Parts.join (Parts.inject 1%nat (interval_state 0 0))
        (Parts.inject 2%nat State.bot)) (Parts.inject 3%nat (interval_state 5 5))) = true.
  Proof. vm_compute. reflexivity. Qed.

End PartitionTests.
