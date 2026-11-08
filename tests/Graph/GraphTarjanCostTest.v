(** * Tarjan visitor cost observations

    Computations retain visitor charges and instantiate the finite-domain potential law.
    For example, a component emission spends stack credit on each owner insertion.
    Builds on: GraphTarjanCost and the local GraphTarjanTest fixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphTarjan GraphTarjanCost.
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

Example initial_potential : TarjanCost.potential 3 Tarjan.initial = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example entry_local_amortisation :
  (Cost.ticks (Visitor.apply_c Tarjan.visitor (Search.Enter 1%positive (@None (nat * positive)))
      Tarjan.initial) +
    TarjanCost.potential 3 (Visitor.apply Tarjan.visitor
      (Search.Enter 1%positive (@None (nat * positive))) Tarjan.initial) <=
    TarjanCost.scc_k * (1 + 3) + TarjanCost.potential 3 Tarjan.initial)%N.
Proof.
  apply TarjanCost.amortised.
  - vm_compute. discriminate.
  - constructor.
Qed.

End TarjanCostFixtures.
