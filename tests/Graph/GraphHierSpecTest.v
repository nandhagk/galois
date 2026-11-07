(** * Hierarchy flattening fixtures

    Nested components flatten in order and include each header once.
    For example, an empty-body component emits an opening and a closing token.
    Builds on: GraphHierSpec. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import GraphHierSpec.
Import List.ListNotations.
Open Scope positive_scope.

Definition nested :=
  Hier.Cons (Hier.Vertex 1)
    (Hier.Cons (Hier.Component 2
      (Hier.Cons (Hier.Vertex 3)
        (Hier.Cons (Hier.Component 4 Hier.Nil) Hier.Nil))) Hier.Nil).

Example nested_tokens :
  Wto.of_forest nested =
    [Wto.WVertex 1; Wto.WOpen 2; Wto.WVertex 3; Wto.WOpen 4; Wto.WClose; Wto.WClose].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_order : Wto.order (Wto.of_forest nested) = [1; 2; 3; 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_annotation :
  Wto.annotate [] (Wto.of_forest nested) = [(1, []); (2, [2]); (3, [2]); (4, [4; 2])].
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_tokens :
  Wto.of_forest (Hier.Cons (Hier.Component 1 Hier.Nil) Hier.Nil) =
    [Wto.WOpen 1; Wto.WClose].
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_order :
  Wto.order (Wto.of_forest (Hier.Cons (Hier.Component 1 Hier.Nil) Hier.Nil)) = [1].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_order : Wto.order (Wto.of_forest Hier.Nil) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example rejected_close : Wto.balanced_from 0 [Wto.WClose] = false.
Proof.
  vm_compute. reflexivity.
Qed.
