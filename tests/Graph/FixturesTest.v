(** * Fixture observations

    These examples check the supplied parent bindings and candidate order.
    For example, the two-entry join has no parent binding.

    Groups:
    - [ParentBindingTests] The parent of each vertex in the fixtures.
    - [OrderTests] The candidate order of the nested-loop fixture.

    Builds on: the first-order graph fixtures. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import WtoSig.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Parent bindings *)

Module ParentBindingTests.

  Local Open Scope positive_scope.

  (** The parent of each listed vertex in a binding list, or none when it has no binding. *)
  Definition parent_values (parents : list (positive * positive)) (vs : list positive) :=
    map (fun v => option_map snd (find (fun binding => Pos.eqb (fst binding) v) parents)) vs.

  (** In a path, each vertex after the root has the vertex before it as parent. *)
  Example line_chain_parents :
    parent_values Line.parents [1; 2; 3; 4] = [None; Some 1; Some 2; Some 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Both branches of a diamond have the root as parent. *)
  Example diamond_branches_share_root :
    parent_values Diamond.parents [1; 2; 3; 4] = [None; Some 1; Some 1; Some 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A two-entry join has no parent binding for its entry vertices. *)
  Example two_entry_join_has_one_binding :
    parent_values TwoEntry.parents [1; 2; 3; 4] = [None; None; None; Some 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ParentBindingTests.

(** * Candidate order *)

Module OrderTests.

  Local Open Scope positive_scope.

  (** The nested-loop fixture lists its vertices in the order 1, 2, 3, 4. *)
  Example nested_loop_order_lists_vertices : wto_order NestedLoop.order = [1; 2; 3; 4].
  Proof.
    vm_compute. reflexivity.
  Qed.

End OrderTests.
