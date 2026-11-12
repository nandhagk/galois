(** * Bounded state disjunction observations

    The shared bounded carrier holds alternatives and state transfers map over them.
    For example, a cap of one collapses two alternatives into one state.
    Builds on: State Disjunction, Env and the shared disjunction lattice. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import Disjunction.
From Galois.Domains Require Import Interval ThresholdsSig Thresholds ZLang.
From Galois.States Require Import Env Disjunction.
Import List.ListNotations.

Module NatMap := TrieMapCode NatKeyCode.
Module Values := IntervalCode ZLangCode ThresholdsCode.
Module State := EnvCode NatKeyCode NatMap ZLangCode Values.
Module Cap.
  Definition k := 1%nat.
End Cap.
Module Shared := DisjunctionCode State Cap.
Module D := StateDisjunctionCode NatKeyCode ZLangCode Values State Cap Shared.

Example empty_is_bottom : D.is_bot D.bot = true.
Proof. vm_compute. reflexivity. Qed.
Example shared_clip_limits_join :
  length (proj1_sig (D.join (Shared.clip [State.top]) (Shared.clip [State.top]))) = 1%nat.
Proof. vm_compute. reflexivity. Qed.
Example stable_widen_keeps_value :
  D.widen TLeaf (Shared.clip [State.top]) (Shared.clip [State.top]) =
    Shared.clip [State.top].
Proof. vm_compute. reflexivity. Qed.
Example havoc_preserves_alternative_count :
  length (proj1_sig (D.havoc 1%nat (Shared.clip [State.top]))) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* The old shared lattice rank client expected (3, 3, 0) on [false; false] and its
   widening by [true]. It used a Boolean lattice as the component, while this
   state component requires a STATE_DOMAIN with assignment, havoc, assume and eval.
   No corresponding Boolean state instance is provided here, and the two-element input
   does not fit the cap-one bounded carrier. The old cap-zero
   empty widening is also outside the positive-cap functional interface. *)

(* The exact landed client used the raw-list carrier, which allowed two entries
   at cap one. The bounded carrier rejects that input.
Example disjunction_measure_client :
  let W := disjunction_wrank bool_lattice (fun _ => True) bool_closed
    bool_laws bool_wrank 1 in
  (wbound W, wrank W [false; false],
   wrank W (widen (disjunction 1 bool_lattice) [false; false] [true])) = (3, 3, 0).
Proof. vm_compute; reflexivity. Qed.
*)
