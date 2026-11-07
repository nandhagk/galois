(** * Named fixture observations

    These examples check the client names, graph arcs and supplied candidate data.
    For example, the two-entry join has no parent binding.
    Builds on: GraphFixtures and GraphReach. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphHierSpec GraphCheckWto
  GraphReach GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition parent_values (parents : Map.t positive positive) vs :=
  map (fun v => Map.get positive_encoding v parents) vs.

Example line_parents :
  parent_values Fixtures.Line.parents [1; 2; 3; 4] = [None; Some 1; Some 2; Some 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_parents :
  parent_values Fixtures.Diamond.parents [1; 2; 3; 4] = [None; Some 1; Some 1; Some 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example join_loop_parents :
  parent_values Fixtures.JoinLoop.parents [1; 2; 3; 4] = [None; Some 1; Some 1; Some 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_loop_parents :
  parent_values Fixtures.NestedLoop.parents [1; 2; 3; 4] = [None; Some 1; Some 2; Some 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_parents :
  parent_values Fixtures.TwoEntry.parents [1; 2; 3; 4] = [None; None; None; Some 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_parents : parent_values Fixtures.SelfLoop.parents [1] = [None].
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_parents :
  parent_values Fixtures.Irreducible.parents [1; 2; 3] = [None; Some 1; Some 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_parents : Map.elements Fixtures.Empty.parents = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_parents : parent_values Fixtures.Singleton.parents [1] = [None].
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_is_listed :
  (Prepared.id_of Fixtures.Unreachable.prepared 5%nat,
    FinSet.mem positive_encoding 5
      (Reach.set Fixtures.Unreachable.prepared Reach.unrestricted [1])) = (Some 5, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example natural_names_are_interned :
  (Prepared.name_of Fixtures.Line.prepared 1, Prepared.name_of Fixtures.Line.prepared 4) =
    (Some 1%nat, Some 4%nat).
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_loop_arcs :
  (Prepared.succ_edges Fixtures.NestedLoop.prepared 3,
    Prepared.succ_edges Fixtures.NestedLoop.prepared 4) =
    ([((3%nat, 2%nat), 2); ((3%nat, 4%nat), 4)], [((4%nat, 1%nat), 1)]).
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_roots : Prepared.entry_ids Fixtures.TwoEntry.prepared = [1; 2].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_order :
  Wto.order Fixtures.NestedLoop.wto = [1; 2; 3; 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_parent_absent : Map.get positive_encoding 5 Fixtures.Unreachable.parents = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_blocked_dominance :
  map (fun d => map (fun n => negb (FinSet.mem positive_encoding n
    (Reach.set Fixtures.Irreducible.prepared (Reach.blocked d) [1]))) [1; 2; 3]) [1; 2; 3] =
  [[true; true; true]; [false; true; false]; [false; false; true]].
Proof.
  vm_compute. reflexivity.
Qed.
