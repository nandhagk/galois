(** * Relational egglog programs on the engine

    Two relational programs of the egglog web demo, written as inductives, derived by the
    [Egglog] command, and solved by the engine. [path] is graph reachability, and [points] is a
    points-to analysis in the style of [points-to.egg]. A solved database holds exactly the
    rows that the program derives, and the generated [<R>_spec] lemmas connect the rows to the
    inductives.
    For example, the edges 1 to 2, 2 to 3 and 3 to 4 give the row [path 1 4] and not [path 4 1].

    Groups:
    - [PathTests] Reachability over a chain of edges.
    - [PointsToTests] A points-to analysis with allocations, copies, stores and loads.
    - [GlueTests] The generated lemmas turn rows into the inductive and back.

    Builds on: the derive command, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Index Join Database Run.
From Galois.Front Require Import Spec Runner Derive.
Import List.ListNotations.

(** * Fixtures *)

Module ExampleValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End ExampleValue.

Module ExampleIndex := IndexCode ExampleValue.
Module ExampleJoin := JoinCode ExampleValue ExampleIndex.
Module ExampleDatabase := DatabaseCode ExampleValue ExampleIndex.
Module ExampleRun := RunCode ExampleValue ExampleIndex ExampleJoin ExampleDatabase.
Module ExampleRunner :=
  RunnerCode ExampleValue ExampleIndex ExampleJoin ExampleDatabase ExampleRun.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.

(** The primitives of the examples: there are none. *)
Definition no_prim (_ : positive) (_ : list positive) : option positive := None.

(** Reachability over the edges that a list gives. *)
Inductive path (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | path_edge x y : In (x, y) edges -> path edges x y
  | path_step x y z : path edges x y -> In (y, z) edges -> path edges x z.

Egglog Path from path.

(** One constraint of a pointer program: an allocation, a copy, a load or a store. *)
Inductive constraint : Type :=
  | Addr (p a : positive)
  | Copy (p q : positive)
  | Load (p q : positive)
  | Store (p q : positive).

(** A pointer program is a list of constraints. *)
Record pointer_input : Type := PointerInput { constraints : list constraint }.

(** [points q x a] says that pointer [x] may point to object [a]. *)
Inductive points (q : pointer_input) : positive -> positive -> Prop :=
  | points_addr x a : In (Addr x a) (constraints q) -> points q x a
  | points_copy x y a : In (Copy x y) (constraints q) -> points q y a -> points q x a
  | points_load x y a b : In (Load x y) (constraints q) -> points q y a -> points q a b ->
      points q x b
  | points_store x y a b : In (Store x y) (constraints q) -> points q x a -> points q y b ->
      points q a b.

Egglog PointsTo from points.

(** * Path *)

Module PathTests.

  Local Open Scope positive_scope.

  (** The edges 1 to 2, 2 to 3 and 3 to 4. *)
  Definition chain : list (positive * positive) := [(1, 2); (2, 3); (3, 4)].

  (** The database that solves the chain. *)
  Definition chain_result : ExampleDatabase.t :=
    snd (ExampleRunner.solve Path.program (Path.facts chain) example_limits).

  (** Saturation reaches a fixpoint on the chain. *)
  Example chain_saturates :
    fst (ExampleRunner.solve Path.program (Path.facts chain) example_limits) = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An edge is a path. *)
  Example edge_is_a_path :
    ExampleRunner.holds Path.path_code [1; 2] chain_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The path from 1 to 4 follows three edges. *)
  Example path_follows_three_edges :
    ExampleRunner.holds Path.path_code [1; 4] chain_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The edges are directed, so there is no path from 4 back to 1. *)
  Example edges_are_directed :
    ExampleRunner.holds Path.path_code [4; 1] chain_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A node has no path to itself without a cycle. *)
  Example no_path_without_a_cycle :
    ExampleRunner.holds Path.path_code [2; 2] chain_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A cycle gives a path from a node to itself. *)
  Example cycle_gives_a_path_to_itself :
    ExampleRunner.holds Path.path_code [1; 1]
      (snd (ExampleRunner.solve Path.program (Path.facts [(1, 2); (2, 1)]) example_limits))
      = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PathTests.

(** * Points-to *)

Module PointsToTests.

  Local Open Scope positive_scope.

  (** The pointers [x], [y], [p], [q] and [z]. *)
  Definition ptr_x : positive := 1.
  Definition ptr_y : positive := 2.
  Definition ptr_p : positive := 3.
  Definition ptr_q : positive := 4.
  Definition ptr_z : positive := 5.

  (** The heap objects [a] and [b]. The address of the variable [x] is [x] itself. *)
  Definition heap_a : positive := 10.
  Definition heap_b : positive := 11.

  (** The program [x = &a; y = &b; p = &x; q = p; *p = y; z = *q]. *)
  Definition demo_program : pointer_input :=
    PointerInput
      [Addr ptr_x heap_a; Addr ptr_y heap_b; Addr ptr_p ptr_x; Copy ptr_q ptr_p;
       Store ptr_p ptr_y; Load ptr_z ptr_q].

  (** The database that solves the program. *)
  Definition demo_result : ExampleDatabase.t :=
    snd (ExampleRunner.solve PointsTo.program (PointsTo.facts demo_program) example_limits).

  (** Saturation reaches a fixpoint on the program. *)
  Example demo_saturates :
    fst (ExampleRunner.solve PointsTo.program (PointsTo.facts demo_program) example_limits)
      = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An allocation gives its pointer the object. *)
  Example allocation_points_to_object :
    ExampleRunner.holds PointsTo.points_code [ptr_x; heap_a] demo_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A copy gives the target the objects of the source. *)
  Example copy_shares_the_target :
    ExampleRunner.holds PointsTo.points_code [ptr_q; ptr_x] demo_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A store through [p] gives [x] the objects of [y]. *)
  Example store_writes_through_the_pointer :
    ExampleRunner.holds PointsTo.points_code [ptr_x; heap_b] demo_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A load through [q] gives [z] what [x] holds after the store. *)
  Example load_reads_the_stored_object :
    ExampleRunner.holds PointsTo.points_code [ptr_z; heap_b] demo_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The load does not give [z] the object that [x] was allocated, because [z] reads the
      cell that [x] points to. *)
  Example load_does_not_read_the_pointer_itself :
    ExampleRunner.holds PointsTo.points_code [ptr_z; ptr_x] demo_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The store does not give [y] the object of [x]. *)
  Example store_does_not_flow_backwards :
    ExampleRunner.holds PointsTo.points_code [ptr_y; heap_a] demo_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PointsToTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** The edges 1 to 2 and 2 to 3. *)
  Definition two_edges : list (positive * positive) := [(1, 2); (2, 3)].

  (** The program that copies pointer one into pointer two, where pointer one holds address ten. *)
  Definition copy_program : pointer_input := PointerInput [Addr 1 10; Copy 2 1].

  (** The inductive path from 1 to 3 gives the derived row, through [path_spec]. *)
  Example path_gives_derived_row :
    derived no_prim Path.spec (Path.inputs two_edges) Path.path_code [1; 3].
  Proof.
    apply (proj1 (Path.path_spec no_prim two_edges 1 3)).
    apply (path_step two_edges 1 2 3).
    - apply path_edge. simpl. auto.
    - simpl. auto.
  Qed.

  (** A derived points-to row gives the inductive, through [points_spec]. *)
  Example derived_row_gives_points :
    derived no_prim PointsTo.spec (PointsTo.inputs copy_program) PointsTo.points_code [2; 10] ->
    points copy_program 2 10.
  Proof.
    intros Hrow.
    exact (proj2 (PointsTo.points_spec no_prim copy_program 2 10) Hrow).
  Qed.

  (** The inductive points-to fact gives the derived row of the copy. *)
  Example points_gives_derived_row :
    derived no_prim PointsTo.spec (PointsTo.inputs copy_program) PointsTo.points_code [2; 10].
  Proof.
    apply (proj1 (PointsTo.points_spec no_prim copy_program 2 10)).
    apply (points_copy copy_program 2 1 10).
    - simpl. auto.
    - apply points_addr. simpl. auto.
  Qed.

End GlueTests.
