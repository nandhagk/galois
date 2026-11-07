(** * Preparation values and callback charges

    Preparation retains callback costs and the original behavior on raw malformed graphs.
    For example, repeated source nodes repeat incoming occurrences and contribute to fuel.
    Builds on: GraphPreparedCost and GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphFixtures.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Definition raw_repeated := Fixtures.prepare [7; 99; 7] [7; 2; 7] [(7, 2)].

Example repeated_raw_preparation :
  (Prepared.entry_ids raw_repeated,
    Prepared.succ_edges raw_repeated 1%positive,
    Prepared.pred_edges raw_repeated 2%positive,
    Pos.to_nat (Prepared.fuel raw_repeated)) =
  ([1; 1]%positive, [((7, 2), 2%positive)],
    [((7, 2), 1%positive); ((7, 2), 1%positive)], 10).
Proof.
  vm_compute. reflexivity.
Qed.

Definition dangling := Fixtures.prepare [1; 99] [1] [(1, 99)].

Example dangling_target_filtered_but_counted :
  (Prepared.entry_ids dangling, Prepared.succ_edges dangling 1%positive,
    Pos.to_nat (Prepared.fuel dangling)) = ([1]%positive, [], 5).
Proof.
  vm_compute. reflexivity.
Qed.

Definition expensive_graph : Graph.t nat (nat * nat) :=
  Graph.Make [1] [1; 2]
    (fun v => Cost.tick 100%N ;; Cost.ret (if Nat.eqb v 1 then [(1, 2)] else []))
    (fun e => Cost.tick 200%N ;; Cost.ret (fst e))
    (fun e => Cost.tick 300%N ;; Cost.ret (snd e)).
Definition cheap_graph := Fixtures.graph [1] [1; 2] [(1, 2)].

Definition prepared_observation {V E} (p : Prepared.t V E) :=
  (Prepared.entry_ids p, Prepared.succ_edges p 1%positive,
    Prepared.pred_edges p 2%positive, Prepared.fuel p).

Example callee_costs_preserve_observations :
  prepared_observation (Prepared.prepare nat_encoding expensive_graph) =
    prepared_observation (Prepared.prepare nat_encoding cheap_graph).
Proof.
  vm_compute. reflexivity.
Qed.

Example preparation_retains_callee_charges :
  (Cost.ticks (Prepared.prepare_c nat_encoding cheap_graph) <
    Cost.ticks (Prepared.prepare_c nat_encoding expensive_graph))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_preparation_fuel :
  Pos.to_nat (Prepared.fuel (Fixtures.prepare [] [] [])) = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example preparation_value_bridge :
  Cost.value (Prepared.prepare_c nat_encoding expensive_graph) =
    Prepared.prepare nat_encoding expensive_graph.
Proof.
  vm_compute. reflexivity.
Qed.
