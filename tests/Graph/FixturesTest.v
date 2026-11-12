(** * Fixture observations

    These examples check the supplied parent bindings and candidate order.
    For example, the two-entry join has no parent binding.
    Builds on: the first-order graph fixtures. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import WtoSig.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition parent_values (parents : list (positive * positive)) (vs : list positive) :=
  map (fun v => option_map snd (find (fun binding => Pos.eqb (fst binding) v) parents)) vs.

Example line_parents :
  parent_values Line.parents [1; 2; 3; 4] = [None; Some 1; Some 2; Some 3].
Proof. vm_compute. reflexivity. Qed.

Example diamond_parents :
  parent_values Diamond.parents [1; 2; 3; 4] = [None; Some 1; Some 1; Some 1].
Proof. vm_compute. reflexivity. Qed.

Example two_entry_parents :
  parent_values TwoEntry.parents [1; 2; 3; 4] = [None; None; None; Some 3].
Proof. vm_compute. reflexivity. Qed.

Example nested_order : wto_order NestedLoop.order = [1; 2; 3; 4].
Proof. vm_compute. reflexivity. Qed.
