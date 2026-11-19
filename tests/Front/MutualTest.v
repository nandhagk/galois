(** * Relations that read each other

    The command [Egglog P from R1 .. Rn] accepts the relations in any order, and relations
    whose premises read each other, as the relations of a mutual inductive do. The tests derive
    programs from mutual inductives and from relations named before the relations that they
    read, run them on the engine, and use their glue lemmas in both directions.
    For example, [odd_walk] and [even_walk] read each other, and on a cycle of three nodes a
    walk of odd length leads from node 1 back to node 1.

    Groups:
    - [WalkTests] Two relations over a list of edges read each other.
    - [OrderTests] Relations named before the relations that their premises read.
    - [CycleTests] Three relations read each other in a cycle.
    - [StepTests] The relations [left] and [right] of egglog's [schedule-demo.egg].
    - [LatticeTests] Two lattice tables read each other, and a relation named before them
      reads one of them.
    - [GlueTests] The generated lemmas turn instances of relations that read each other into
      derived rows and back.

    Builds on: the derive command, the meaning of lattice reads, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Index Join Database Run.
From Galois.Front Require Import Spec SpecLattice Runner Derive.
Import List.ListNotations.

(** * Fixtures *)

(** The values are positives, and the programs of the fixtures call no primitive. *)
Module PlainValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End PlainValue.

Module PlainIndex := IndexCode PlainValue.
Module PlainJoin := JoinCode PlainValue PlainIndex.
Module PlainDatabase := DatabaseCode PlainValue PlainIndex.
Module PlainRun := RunCode PlainValue PlainIndex PlainJoin PlainDatabase.
Module PlainRunner := RunnerCode PlainValue PlainIndex PlainJoin PlainDatabase PlainRun.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition test_limits : limits := Limits 50%N 1000%N.

(** [odd_walk edges x y] says that a walk of odd length leads from [x] to [y], and
    [even_walk edges x y] says that a walk of even positive length does. *)
Inductive odd_walk (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | odd_edge x y : In (x, y) edges -> odd_walk edges x y
  | odd_step x y z : even_walk edges x y -> In (y, z) edges -> odd_walk edges x z
with even_walk (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | even_step x y z : odd_walk edges x y -> In (y, z) edges -> even_walk edges x z.

Egglog Walks from odd_walk even_walk.

(** [mod_zero edges x y], [mod_one edges x y] and [mod_two edges x y] say that a walk from [x]
    to [y] has a length that leaves the remainder 0, 1 or 2 when divided by 3. Each relation
    reads the one before it, and [mod_zero] reads [mod_two]. *)
Inductive mod_zero (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | zero_step x y z : mod_two edges x y -> In (y, z) edges -> mod_zero edges x z
with mod_one (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | one_edge x y : In (x, y) edges -> mod_one edges x y
  | one_step x y z : mod_zero edges x y -> In (y, z) edges -> mod_one edges x z
with mod_two (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | two_step x y z : mod_one edges x y -> In (y, z) edges -> mod_two edges x z.

Egglog Remainders from mod_zero mod_one mod_two.

Local Open Scope positive_scope.

(** The edges of a cycle of three nodes. *)
Definition triangle : list (positive * positive) := [(1, 2); (2, 3); (3, 1)].

(** The edges of a cycle of four nodes. *)
Definition square : list (positive * positive) := [(1, 2); (2, 3); (3, 4); (4, 1)].

(** * Walks *)

Module WalkTests.

  (** The run of the walks on the cycle of three nodes. *)
  Definition triangle_run : stop * PlainDatabase.t :=
    PlainRunner.solve Walks.program (Walks.facts triangle) test_limits.

  (** The run of the walks on the cycle of four nodes. *)
  Definition square_run : stop * PlainDatabase.t :=
    PlainRunner.solve Walks.program (Walks.facts square) test_limits.

  (** The walks between four nodes give finitely many rows, so the run saturates. *)
  Example square_run_saturates :
    fst square_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Once around the cycle of three nodes is a walk of odd length back to node 1. *)
  Example triangle_has_odd_walk_back :
    PlainRunner.holds Walks.odd_walk_code [1; 1] (snd triangle_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every walk from node 1 back to node 1 on the cycle of four nodes has a length that four
      divides, so none is odd. *)
  Example square_has_no_odd_walk_back :
    PlainRunner.holds Walks.odd_walk_code [1; 1] (snd square_run) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Once around the cycle of four nodes is a walk of even length back to node 1. *)
  Example square_has_even_walk_back :
    PlainRunner.holds Walks.even_walk_code [1; 1] (snd square_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WalkTests.

(** * Order of the relations *)

Module OrderTests.

  (** [reach edges x y] says that a path of edges leads from [x] to [y]. *)
  Inductive reach (edges : list (positive * positive)) : positive -> positive -> Prop :=
    | reach_edge x y : In (x, y) edges -> reach edges x y
    | reach_step x y z : reach edges x y -> In (y, z) edges -> reach edges x z.

  (** [loop edges x] says that a path leads from [x] back to [x]. *)
  Inductive loop (edges : list (positive * positive)) : positive -> Prop :=
    | loop_back x : reach edges x x -> loop edges x.

  (** The relation [loop] reads [reach], and the command names [loop] first. *)
  Egglog Loops from loop reach.

  (** The relations of a mutual inductive, named in the other order. *)
  Egglog WalksBack from even_walk odd_walk.

  (** The edges of a cycle through 1 and 2, and an edge from 2 out of the cycle to 3. *)
  Definition exit : list (positive * positive) := [(1, 2); (2, 1); (2, 3)].

  (** The run of the loops on the cycle with an exit. *)
  Definition exit_run : stop * PlainDatabase.t :=
    PlainRunner.solve Loops.program (Loops.facts exit) test_limits.

  (** The tables keep the order of the command, the relations first and the input list last. *)
  Example tables_keep_the_order_of_the_command :
    map name (tables Loops.spec) = [Loops.loop_code; Loops.reach_code; Loops.edges_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A path leads from node 1 around the cycle back to node 1. *)
  Example cycle_node_has_a_loop :
    PlainRunner.holds Loops.loop_code [1] (snd exit_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** No edge leaves node 3, so no path leads from node 3 back to node 3. *)
  Example exit_node_has_no_loop :
    PlainRunner.holds Loops.loop_code [3] (snd exit_run) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The mutual relations named in the other order find the odd walk around the cycle of
      three nodes. *)
  Example other_order_finds_the_odd_walk :
    PlainRunner.holds WalksBack.odd_walk_code [1; 1]
      (snd (PlainRunner.solve WalksBack.program (WalksBack.facts triangle) test_limits)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End OrderTests.

(** * A cycle of three relations *)

Module CycleTests.

  (** The run of the remainders on the cycle of three nodes. *)
  Definition triangle_run : stop * PlainDatabase.t :=
    PlainRunner.solve Remainders.program (Remainders.facts triangle) test_limits.

  (** The run reaches every remainder between the three nodes and saturates. *)
  Example triangle_run_saturates :
    fst triangle_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Once around the cycle of three nodes is a walk of length 3 back to node 1. *)
  Example cycle_leaves_remainder_zero :
    PlainRunner.holds Remainders.mod_zero_code [1; 1] (snd triangle_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The walks from node 1 to node 3 have the lengths 2, 5, 8 and so on. *)
  Example two_edges_leave_remainder_two :
    PlainRunner.holds Remainders.mod_two_code [1; 3] (snd triangle_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every walk from node 1 back to node 1 has a length that 3 divides. *)
  Example cycle_never_leaves_remainder_one :
    PlainRunner.holds Remainders.mod_one_code [1; 1] (snd triangle_run) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CycleTests.

(** * The feet of schedule-demo.egg *)

Module StepTests.

  (** Addition of positives. *)
  Egglog Primitives StepOps Pos.add.

  (** [left n] says that the left foot reaches position [n], and [right n] says that the right
      foot does. The left foot steps on from [x] when both feet stand at [x], and the right foot
      steps to the position of the left foot when that is one step ahead. The feet start at 1,
      where the demo starts at 0, because the values are positives. *)
  Inductive left : positive -> Prop :=
    | left_start : left 1
    | left_step x y : left x -> right x -> Pos.add x 1 = y -> left y
  with right : positive -> Prop :=
    | right_start : right 1
    | right_step x y : left x -> right y -> Pos.add y 1 = x -> right x.

  (** The rulesets of the demo. The engine runs all rules together, so a run reads neither. *)
  Egglog Steps from left right with StepOps
    ruleset step_left left_step
    ruleset step_right right_step.

  (** The values are positives, and the primitives are those of [StepOps]. *)
  Module StepValue <: VALUE_OPS.
    Include PosKeyCode.
    Definition prim := StepOps.prim.
    Definition merge (_ : positive) := Pos.max.
  End StepValue.

  Module StepIndex := IndexCode StepValue.
  Module StepJoin := JoinCode StepValue StepIndex.
  Module StepDatabase := DatabaseCode StepValue StepIndex.
  Module StepRun := RunCode StepValue StepIndex StepJoin StepDatabase.
  Module StepRunner := RunnerCode StepValue StepIndex StepJoin StepDatabase StepRun.

  (** The run of the feet from the facts [left 1] and [right 1]. *)
  Definition walk_run : stop * StepDatabase.t :=
    StepRunner.solve Steps.program Steps.facts test_limits.

  (** The feet step on forever, and the demo bounds them with its schedule. The engine has no
      schedule, so the run stops at its iteration limit. *)
  Example walk_run_stops_at_the_limit :
    fst walk_run = IterLimit.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Ten steps of the left foot reach position 11, as the demo checks [(left 10)]. *)
  Example left_foot_takes_ten_steps :
    StepRunner.holds Steps.left_code [11] (snd walk_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Nine steps of the right foot reach position 10, as the demo checks [(right 9)]. *)
  Example right_foot_takes_nine_steps :
    StepRunner.holds Steps.right_code [10] (snd walk_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End StepTests.

(** * Lattice tables *)

Module LatticeTests.

  (** Addition and the minimum of positives. *)
  Egglog Primitives PathOps Pos.add Pos.min.

  (** An edge of one of two colors, from a source node to a target node, with a weight. *)
  Inductive colored_edge : Type :=
    | Red (source target weight : positive)
    | Blue (source target weight : positive).

  (** [red_dist edges a b d] says that some path from [a] to [b] whose edges alternate in
      color ends with a red edge and has the length [d], and [blue_dist edges a b d] says that
      some such path ends with a blue edge. *)
  Inductive red_dist (edges : list colored_edge) : positive -> positive -> positive -> Prop :=
    | red_edge a b w : In (Red a b w) edges -> red_dist edges a b w
    | red_step a b c d w : blue_dist edges a b d -> In (Red b c w) edges ->
        red_dist edges a c (Pos.add d w)
  with blue_dist (edges : list colored_edge) : positive -> positive -> positive -> Prop :=
    | blue_edge a b w : In (Blue a b w) edges -> blue_dist edges a b w
    | blue_step a b c d w : red_dist edges a b d -> In (Blue b c w) edges ->
        blue_dist edges a c (Pos.add d w).

  Egglog Alternating from red_dist blue_dist with PathOps
    merge red_dist Pos.min merge blue_dist Pos.min.

  (** [red_reach edges a b] says that some alternating path from [a] to [b] ends with a red
      edge. It reads the lattice table [red_dist]. *)
  Inductive red_reach (edges : list colored_edge) : positive -> positive -> Prop :=
    | red_reach_dist a b d : red_dist edges a b d -> red_reach edges a b.

  (** The command names [red_reach] before the lattice tables that it reads. *)
  Egglog Reaching from red_reach red_dist blue_dist with PathOps
    merge red_dist Pos.min merge blue_dist Pos.min.

  (** The values are positives, and the merge of a lattice table is its primitive. *)
  Module PathValue <: VALUE_OPS.
    Include PosKeyCode.
    Definition prim := PathOps.prim.
    Definition merge := prim_merge PathOps.prim.
  End PathValue.

  Module PathIndex := IndexCode PathValue.
  Module PathJoin := JoinCode PathValue PathIndex.
  Module PathDatabase := DatabaseCode PathValue PathIndex.
  Module PathRun := RunCode PathValue PathIndex PathJoin PathDatabase.
  Module PathRunner := RunnerCode PathValue PathIndex PathJoin PathDatabase PathRun.

  (** The value that a database stores at a key of a lattice table, if it stores one. *)
  Definition stored (f : positive) (ks : list positive) (db : PathDatabase.t) :
      option positive :=
    match fst (PathDatabase.lookup f (map Val ks) db) with
    | Some (Some (Val v)) => Some v
    | _ => None
    end.

  (** A red edge from 1 to 4 of weight 5, and the path from 1 to 4 through a red, a blue and a
      red edge of weight 1. *)
  Definition alternating_edges : list colored_edge :=
    [Red 1 2 1; Blue 2 3 1; Red 3 4 1; Red 1 4 5].

  (** The run of the alternating distances. *)
  Definition alternating_run : stop * PathDatabase.t :=
    PathRunner.solve Alternating.program (Alternating.facts alternating_edges) test_limits.

  (** The run of the relation that reads the alternating distances. *)
  Definition reaching_run : stop * PathDatabase.t :=
    PathRunner.solve Reaching.program (Reaching.facts alternating_edges) test_limits.

  (** The edges form no cycle, so the run saturates. *)
  Example alternating_run_saturates :
    fst alternating_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The alternating path of length 3 is shorter than the red edge of weight 5. *)
  Example alternating_path_is_stored :
    stored Alternating.red_dist_code [1; 4] (snd alternating_run) = Some 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The alternating path from 1 to 3 ends with the blue edge and has length 2. *)
  Example blue_distance_reads_the_red_one :
    stored Alternating.blue_dist_code [1; 3] (snd alternating_run) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A relation named before the lattice tables reads the stored distance from 1 to 4. *)
  Example relation_named_first_reads_the_table :
    PathRunner.holds Reaching.red_reach_code [1; 4] (snd reaching_run) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The alternating path of length 3 gives an assigned value, through [red_dist_spec]. *)
  Example alternating_path_gives_assigned_value :
    lat_assigned PathOps.prim (prim_merge PathOps.prim) Alternating.spec
      (Alternating.inputs alternating_edges) Alternating.red_dist_code [1; 4] 3.
  Proof.
    apply (proj1 (Alternating.red_dist_spec alternating_edges 1 4 3)).
    apply (red_step alternating_edges 1 3 4 2 1).
    - apply (blue_step alternating_edges 1 2 3 1 1).
      + apply red_edge. simpl. auto.
      + simpl. auto.
    - simpl. auto.
  Qed.

End LatticeTests.

(** * Glue *)

Module GlueTests.

  (** The walk around the cycle of three nodes gives the derived row of [odd_walk]. *)
  Example odd_walk_gives_derived_row :
    derived (fun _ _ => None) Walks.spec (Walks.inputs triangle) Walks.odd_walk_code [1; 1].
  Proof.
    apply (proj1 (Walks.odd_walk_spec (fun _ _ => None) triangle 1 1)).
    apply (odd_step triangle 1 3 1).
    - apply (even_step triangle 1 2 3).
      + apply odd_edge. simpl. auto.
      + simpl. auto.
    - simpl. auto.
  Qed.

  (** A derived row of [even_walk] gives the instance of [even_walk]. *)
  Example derived_row_gives_even_walk :
    derived (fun _ _ => None) Walks.spec (Walks.inputs triangle) Walks.even_walk_code [1; 3] ->
    even_walk triangle 1 3.
  Proof.
    intros Hrow.
    exact (proj2 (Walks.even_walk_spec (fun _ _ => None) triangle 1 3) Hrow).
  Qed.

  (** For any edges, a derived row of [even_walk] and one more edge give a derived row of
      [odd_walk]. The proof reads the row as a walk, extends it, and reads it back. *)
  Example even_row_and_edge_give_odd_row :
    forall prim edges x y z,
      derived prim Walks.spec (Walks.inputs edges) Walks.even_walk_code [x; y] ->
      In (y, z) edges ->
      derived prim Walks.spec (Walks.inputs edges) Walks.odd_walk_code [x; z].
  Proof.
    intros prim edges x y z Heven Hedge.
    apply (proj1 (Walks.odd_walk_spec prim edges x z)).
    apply (odd_step edges x y z); [| exact Hedge].
    exact (proj2 (Walks.even_walk_spec prim edges x y) Heven).
  Qed.

  (** For any edges, a derived row of [mod_two] and one more edge give a derived row of
      [mod_zero], which closes the cycle of the three relations. *)
  Example two_row_and_edge_give_zero_row :
    forall prim edges x y z,
      derived prim Remainders.spec (Remainders.inputs edges) Remainders.mod_two_code [x; y] ->
      In (y, z) edges ->
      derived prim Remainders.spec (Remainders.inputs edges) Remainders.mod_zero_code [x; z].
  Proof.
    intros prim edges x y z Htwo Hedge.
    apply (proj1 (Remainders.mod_zero_spec prim edges x z)).
    apply (zero_step edges x y z); [| exact Hedge].
    exact (proj2 (Remainders.mod_two_spec prim edges x y) Htwo).
  Qed.

End GlueTests.
