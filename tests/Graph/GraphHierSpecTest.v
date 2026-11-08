(** * Hierarchy flattening fixtures

    Nested components flatten in order and include each header once.
    For example, an empty-body component emits an opening and a closing token.
    Builds on: GraphHierSpec. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
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

Example emit_vertex_client v tail :
  Cost.value (Wto.emit_tree_c (Hier.Vertex v) tail) = Wto.WVertex v :: tail.
Proof.
  apply Wto.emit_tree_equation.
Qed.

Example emit_component_client h body tail :
  Cost.value (Wto.emit_tree_c (Hier.Component h body) tail) =
    Wto.WOpen h :: Cost.value (Wto.emit_forest_c body (Wto.WClose :: tail)).
Proof.
  apply Wto.emit_tree_equation.
Qed.

Example emit_cons_client t rest tail :
  Cost.value (Wto.emit_forest_c (Hier.Cons t rest) tail) =
    Cost.value (Wto.emit_tree_c t (Cost.value (Wto.emit_forest_c rest tail))).
Proof.
  apply Wto.emit_forest_equation.
Qed.

Example emit_empty_client tail :
  Cost.value (Wto.emit_forest_c Hier.Nil tail) = tail.
Proof.
  apply Wto.emit_forest_equation.
Qed.

Example flatten_client f :
  Wto.of_forest f = Cost.value (Wto.emit_forest_c f []).
Proof.
  apply Wto.of_forest_equation.
Qed.

Example annotate_open_client h stack rest :
  Wto.annotate stack (Wto.WOpen h :: rest) =
    (h, h :: stack) :: Wto.annotate (h :: stack) rest.
Proof.
  apply Wto.annotate_equation.
Qed.

Example annotate_close_client stack rest :
  Wto.annotate stack (Wto.WClose :: rest) = Wto.annotate (tl stack) rest.
Proof.
  apply Wto.annotate_equation.
Qed.

Example order_close_client rest : Wto.order (Wto.WClose :: rest) = Wto.order rest.
Proof.
  apply Wto.order_equation.
Qed.
