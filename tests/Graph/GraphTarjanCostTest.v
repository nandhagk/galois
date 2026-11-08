(** * Tarjan visitor cost observations

    Computations retain visitor charges and instantiate the finite-domain potential law.
    For example, a component emission spends stack credit on each owner insertion.
    Builds on: GraphTarjanCost and the local GraphTarjanTest fixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchCost GraphTarjan GraphCondense
  GraphTarjanCost.
From Galois.Tests.Graph Require Import GraphTarjanTest.
Import List.ListNotations.

Module TarjanCostFixtures.

Definition line_ticks :=
  Cost.ticks (Tarjan.compute_c TarjanFixtures.line TarjanFixtures.unrestricted [1]%positive).
Definition nested_ticks :=
  Cost.ticks (Tarjan.compute_c TarjanFixtures.nested TarjanFixtures.unrestricted [1]%positive).

Example line_tick_observation : line_ticks = 348%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_tick_observation : nested_ticks = 437%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_below_scc_cost :
  (line_ticks <= TarjanCost.scc_k *
    TarjanCost.scc_size TarjanFixtures.line [1]%positive 3)%N.
Proof.
  vm_compute. discriminate.
Qed.

Example nested_below_scc_cost :
  (nested_ticks <= TarjanCost.scc_k *
    TarjanCost.scc_size TarjanFixtures.nested [1]%positive 3)%N.
Proof.
  vm_compute. discriminate.
Qed.

(** Local preparation supplies the finite global-ID and supplied-root width budget. *)
Example line_width : SearchCost.width_bound TarjanFixtures.line [1]%positive 3.
Proof.
  intros v [[name [Hin Hi]]|Hv].
  - change (In name [1; 2; 3; 4]%nat) in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|Hfalse]]]]; [| | | |contradiction].
    all: vm_compute in Hi; inversion Hi; subst v; vm_compute; discriminate.
  - destruct Hv as [<-|Hfalse]; [vm_compute; discriminate|contradiction].
Qed.

(** The numeric cost theorem applies to the actual prepared line and its actual visitor computation. *)
Example line_cost_client :
  (Cost.ticks (Tarjan.compute_c TarjanFixtures.line TarjanFixtures.unrestricted [1]%positive) <=
    TarjanCost.scc_k * TarjanCost.scc_size TarjanFixtures.line [1]%positive 3)%N.
Proof.
  apply TarjanCost.scc_cost; [exact (proj1 TarjanFixtures.fixtures_ready)|exact line_width].
Qed.

Definition condense_ticks {V E} (p : Prepared.t V E) :=
  Cost.ticks (Condense.of_scc_c p TarjanFixtures.unrestricted
    (Tarjan.compute p TarjanFixtures.unrestricted (Prepared.entry_ids p))).

Example line_condense_tick_observation : condense_ticks TarjanFixtures.line = 175%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_condense_tick_observation : condense_ticks TarjanFixtures.nested = 75%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_condense_below_numeric_bound :
  (condense_ticks TarjanFixtures.line <=
    TarjanCost.condense_k * TarjanCost.condense_size TarjanFixtures.line
      (Tarjan.compute TarjanFixtures.line TarjanFixtures.unrestricted [1]%positive) 3)%N.
Proof.
  vm_compute. discriminate.
Qed.

Example nested_condense_below_numeric_bound :
  (condense_ticks TarjanFixtures.nested <=
    TarjanCost.condense_k * TarjanCost.condense_size TarjanFixtures.nested
      (Tarjan.compute TarjanFixtures.nested TarjanFixtures.unrestricted [1]%positive) 3)%N.
Proof.
  vm_compute. discriminate.
Qed.

Example supplied_unknown_root_occurrences_still_cost :
  (Cost.ticks (Tarjan.compute_c TarjanFixtures.empty TarjanFixtures.unrestricted []) <
    Cost.ticks (Tarjan.compute_c TarjanFixtures.empty TarjanFixtures.unrestricted
      [99; 99]%positive))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_and_unknown_roots_still_cost :
  (Cost.ticks (Tarjan.compute_c TarjanFixtures.line TarjanFixtures.unrestricted [1]%positive) <
    Cost.ticks (Tarjan.compute_c TarjanFixtures.line TarjanFixtures.unrestricted
      [99; 1; 1; 99]%positive))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example initial_potential : TarjanCost.potential 3 Tarjan.initial = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example entry_local_amortisation :
  (Cost.ticks (Visitor.apply_c Tarjan.visitor (Search.Enter 1%positive (@None (nat * positive)))
      Tarjan.initial) +
    TarjanCost.potential 3 (Visitor.apply Tarjan.visitor
      (Search.Enter 1%positive (@None (nat * positive))) Tarjan.initial) <=
    TarjanCost.visitor_k * (1 + 3) + TarjanCost.potential 3 Tarjan.initial)%N.
Proof.
  apply TarjanCost.amortised.
  - vm_compute. discriminate.
  - constructor.
Qed.

End TarjanCostFixtures.
