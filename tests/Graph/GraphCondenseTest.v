(** * Condensation successor observations

    These computations check distinct successors, sink rows and the empty component count.
    For example, the two diamond branches share one sink without adding a self edge.
    Builds on: GraphCondense and the local GraphTarjanTest fixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphPrepared GraphSccSpec GraphTarjan GraphCondense.
From Galois.Tests.Graph Require Import GraphTarjanTest.
Import List.ListNotations.

Module CondenseFixtures.

Definition condense {V E} (p : Prepared.t V E) :=
  Condense.of_scc p TarjanFixtures.unrestricted
    (Tarjan.compute p TarjanFixtures.unrestricted (Prepared.entry_ids p)).

Definition successors (c : Condensation.t) indices :=
  map (fun i => Map.get positive_encoding i (Condensation.succs c)) indices.

Example line_successors :
  successors (condense TarjanFixtures.line) [1; 2; 3; 4; 5]%positive =
    [Some []; Some [1]; Some [2]; Some [3]; None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_successors :
  successors (condense TarjanFixtures.diamond) [1; 2; 3; 4]%positive =
    [Some []; Some [1]; Some [1]; Some [2; 3]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_has_no_self_edge :
  successors (condense TarjanFixtures.self_loop) [1]%positive = [Some []].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_cycle_has_no_self_edge :
  (Condensation.count (condense TarjanFixtures.nested),
    successors (condense TarjanFixtures.nested) [1]%positive) = (1%nat, [Some []]).
Proof.
  vm_compute. reflexivity.
Qed.

Example distinct_scc_edge :
  successors (condense TarjanFixtures.distinct) [1; 2]%positive = [Some []; Some [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_count : condense TarjanFixtures.empty = Condensation.Make 0 Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Definition repeated_cross_edges :=
  TarjanFixtures.prepare [1] [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].

Example duplicate_targets_are_deduplicated :
  successors (condense repeated_cross_edges) [1; 2]%positive = [Some []; Some [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example scoped_unowned_endpoints_do_not_create_edges :
  let r := Tarjan.compute TarjanFixtures.nested TarjanFixtures.inner_scope [2]%positive in
  successors (Condense.of_scc TarjanFixtures.nested TarjanFixtures.inner_scope r)
    [1; 2]%positive = [Some []; None].
Proof.
  vm_compute. reflexivity.
Qed.

End CondenseFixtures.
