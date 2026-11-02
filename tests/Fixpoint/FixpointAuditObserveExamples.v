(** * Counted observation execution examples

    The counted execution records outputs before optional component-boundary eviction.
    For example, a predecessor remains in the reference but is absent after its last reader.
    Builds on: FixpointFIX6 and numbered observation execution adequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointObserve
  FixpointAuditObserveNumberExecute FixpointAuditObserveNumberExecuteAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX6.
Import List.ListNotations.

(** * Nonempty reference, eviction and fuel boundaries *)

Definition fx_observe_fix6_execution evict fuel :=
  fx_number_execute nat_encoding observation_test_lattice Joining observation_test_system 0
    (observation_number 0 (System.constraints observation_test_system))
    observation_test_schedule evict fuel.

(** Insufficient fuel returns no result in both modes while retaining the actual trace. *)
Example fx_observe_fix6_exhaustion :
  fst (fx_observe_fix6_execution true 1) = None /\
  fst (fx_observe_fix6_execution false 1) = None /\
  snd (fx_observe_fix6_execution true 1) <> [].
Proof.
  vm_compute; repeat split; try reflexivity; discriminate.
Qed.

(** Reference retains the predecessor while eviction removes it after recording the observation. *)
Example fx_observe_fix6_reference_and_eviction :
  let project := fun result => option_map (fun maps =>
    (Map.get nat_encoding 0 (fst maps), Map.get nat_encoding 3 (snd maps),
      Map.get nat_encoding 5 (snd maps), Map.get nat_encoding 6 (snd maps))) result in
  project (fst (fx_observe_fix6_execution false 64)) =
    Some (Some ObservationMiddle, Some ObservationMiddle, Some ObservationMiddle, Some
      ObservationBottom) /\
  project (fst (fx_observe_fix6_execution true 64)) =
    Some (None, Some ObservationMiddle, Some ObservationMiddle, Some ObservationBottom).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Both counted modes agree with the original fixed-schedule execution at the fuel boundary. *)
Example fx_observe_fix6_same_execution :
  fst (fx_observe_fix6_execution true 63) = None /\
  fst (fx_observe_fix6_execution true 64) =
    observation_execute nat_encoding observation_test_lattice Joining
      (observation_system observation_test_system 0) observation_test_schedule true 64 /\
  fst (fx_observe_fix6_execution false 64) =
    observation_execute nat_encoding observation_test_lattice Joining
      (observation_system observation_test_system 0) observation_test_schedule false 64.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
