(** * The Egglog derive command

    The command [Egglog P from R ..] reads inductive relations into a module [P]. Each input
    list gives its tables, each constructor gives a clause, and the facts of a parameter list one
    row per element. The tests read the generated specification through its table codes
    ([P.<relation>_code], [P.<Constructor>_code]) and never through raw numbers.
    For example, a list of pairs read by [In (x, y) edges] is one table, and a record field of
    constructors read by [In (Addr x a) (constraints q)] is one table per constructor.

    Groups:
    - [PairInputTests] A list of pairs and a relation premise read tables and clauses.
    - [ConstructorInputTests] A record field of constructors reads one table per constructor.
    - [EquationTests] The clauses of an equational relation over a datatype.
    - [FactTests] The facts list one row per input element, and the conditions accept them.

    Builds on: the derive command, the specifications and the runner conditions. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax.
From Galois.Front Require Import Spec RunnerSig Derive.
Import List.ListNotations.

(** * Fixtures *)

(** The head of a clause, as the kind of consequence it is. *)
Variant head_kind : Type :=
  | KindDerive
  | KindAssign
  | KindUnify
  | KindRewrites.

Definition kind_of (c : clause positive) : head_kind :=
  match head c with
  | Derive _ _ => KindDerive
  | Assign _ _ _ => KindAssign
  | Unify _ _ => KindUnify
  | Rewrites _ _ => KindRewrites
  end.

(** The table that a clause derives into, when its head derives a row. *)
Definition head_table (c : clause positive) : option positive :=
  match head c with
  | Derive r _ => Some r
  | _ => None
  end.

(** The tables that the premises of a clause read, in order. *)
Definition body_tables (c : clause positive) : list positive :=
  flat_map (fun p => match p with Holds r _ => [r] | _ => [] end) (body c).

(** Reachability over a list of edges, with the edges as a parameter. *)
Inductive path (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | path_edge x y : In (x, y) edges -> path edges x y
  | path_step x y z : path edges x y -> In (y, z) edges -> path edges x z.

Egglog Path from path.

(** One constraint of a pointer program. *)
Inductive constraint : Type :=
  | Addr (p a : positive)
  | Copy (p q : positive)
  | Load (p q : positive)
  | Store (p q : positive).

(** A pointer program is a list of constraints. *)
Record pointer_input : Type := PointerInput { constraints : list constraint }.

(** Points-to analysis over the constraints of a pointer program. *)
Inductive points (q : pointer_input) : positive -> positive -> Prop :=
  | points_addr x a : In (Addr x a) (constraints q) -> points q x a
  | points_copy x y a : In (Copy x y) (constraints q) -> points q y a -> points q x a
  | points_load x y a b : In (Load x y) (constraints q) -> points q y a -> points q a b ->
      points q x b
  | points_store x y a b : In (Store x y) (constraints q) -> points q x a -> points q y b ->
      points q a b.

Egglog PointsTo from points.

(** Arithmetic terms over numbers. *)
Inductive term : Type :=
  | Num (n : positive)
  | Add (a b : term).

(** Equality of terms: the closure laws, a union from the input, and two rewrites. *)
Inductive equiv (merges : list (positive * positive)) : term -> term -> Prop :=
  | equiv_refl a : equiv merges a a
  | equiv_sym a b : equiv merges a b -> equiv merges b a
  | equiv_trans a b c : equiv merges a b -> equiv merges b c -> equiv merges a c
  | equiv_add a a' b b' : equiv merges a a' -> equiv merges b b' ->
      equiv merges (Add a b) (Add a' b')
  | equiv_merge x y : In (x, y) merges -> equiv merges (Num x) (Num y)
  | equiv_comm a b : equiv merges (Add a b) (Add b a)
  | equiv_fold x y b : In (x, y) merges -> equiv merges (Add (Num x) b) (Num y).

Egglog Terms from equiv.

(** * Pair inputs *)

Module PairInputTests.

  (** A list of pairs is one input table, so the program declares the relation and that table. *)
  Example pair_list_is_one_table :
    map name (tables Path.spec) = [Path.path_code; Path.input1_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Only the table of the pair list takes rows from the input. *)
  Example pair_table_is_the_only_input :
    inputs Path.spec = [Path.input1_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each constructor of the relation is one clause. *)
  Example one_clause_per_constructor :
    length (clauses Path.spec) = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Both clauses derive a row of the relation. *)
  Example clauses_derive_into_the_relation :
    map head_table (clauses Path.spec) = [Some Path.path_code; Some Path.path_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The edge clause reads the input table, and the step clause reads the relation and then
      the input table. *)
  Example premises_read_their_tables :
    map body_tables (clauses Path.spec) =
      [[Path.input1_code]; [Path.path_code; Path.input1_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The relation and the input list are tables without an identifier output. *)
  Example relation_is_declared_without_output :
    map out (tables Path.spec) = [ORel; ORel].
  Proof.
    vm_compute. reflexivity.
  Qed.

End PairInputTests.

(** * Constructor inputs *)

Module ConstructorInputTests.

  (** The relation comes first, then one table for each constructor that a premise reads. *)
  Example constructors_are_tables :
    map name (tables PointsTo.spec) =
      [PointsTo.points_code; PointsTo.Addr_code; PointsTo.Copy_code; PointsTo.Load_code;
       PointsTo.Store_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every constructor table is an input table. *)
  Example constructor_tables_are_inputs :
    inputs PointsTo.spec =
      [PointsTo.Addr_code; PointsTo.Copy_code; PointsTo.Load_code; PointsTo.Store_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each constructor of the relation is one clause that derives a points-to row. *)
  Example clauses_derive_points_rows :
    map head_table (clauses PointsTo.spec) = repeat (Some PointsTo.points_code) 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The premises read the constructor tables in the order of the hypotheses, and the
      relation premises read the relation table. *)
  Example premises_read_constructor_tables :
    map body_tables (clauses PointsTo.spec) =
      [[PointsTo.Addr_code];
       [PointsTo.Copy_code; PointsTo.points_code];
       [PointsTo.Load_code; PointsTo.points_code; PointsTo.points_code];
       [PointsTo.Store_code; PointsTo.points_code; PointsTo.points_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constructor that takes two values is a table of two value arguments. *)
  Example constructor_table_has_value_arguments :
    map arg_sorts (tables PointsTo.spec) =
      [[SVal; SVal]; [SVal; SVal]; [SVal; SVal]; [SVal; SVal]; [SVal; SVal]].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ConstructorInputTests.

(** * Equations *)

Module EquationTests.

  (** Reflexivity, symmetry, transitivity and congruence give no clause, so the three other
      constructors are the clauses. *)
  Example closure_laws_give_no_clause :
    length (clauses Terms.spec) = 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A clause whose premises bind every variable is a union, and a clause with a variable that
      no premise binds is a rewrite. *)
  Example unify_when_premises_bind_all_variables :
    map kind_of (clauses Terms.spec) = [KindUnify; KindRewrites; KindRewrites].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Only the rewrite clauses become rewrites of the program. *)
  Example rewrite_clauses_become_rewrites :
    length Terms.rewrites = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equational relation has no table of its own. The input list and the constructors of
      the datatype are the tables. *)
  Example datatype_constructors_are_tables :
    map name (tables Terms.spec) = [Terms.input1_code; Terms.Num_code; Terms.Add_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The constructors of a datatype build class identifiers, and the input list is a relation. *)
  Example constructors_output_identifiers :
    map out (tables Terms.spec) = [ORel; OId; OId].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constructor of a datatype has an argument of the sort of its type. *)
  Example datatype_arguments_have_their_sorts :
    map arg_sorts (tables Terms.spec) = [[SVal; SVal]; [SVal]; [SId; SId]].
  Proof.
    vm_compute. reflexivity.
  Qed.

End EquationTests.

(** * Facts *)

Module FactTests.

  Local Open Scope positive_scope.

  (** Two edges of a path input. *)
  Definition two_edges : list (positive * positive) := [(1, 2); (2, 3)].

  (** A copy of pointer one into pointer two, and the address ten of pointer one. *)
  Definition copy_program : pointer_input := PointerInput [Addr 1 10; Copy 2 1].

  (** Two unions of numbers. *)
  Definition two_merges : list (positive * positive) := [(1, 2); (3, 4)].

  (** A pair list gives one row for each pair, in its table. *)
  Example pairs_give_one_row_each :
    Path.facts two_edges = [(Path.input1_code, [1; 2]); (Path.input1_code, [2; 3])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constructor gives its row in its own table, with its arguments in order. *)
  Example constructors_give_rows_in_their_tables :
    PointsTo.facts copy_program = [(PointsTo.Addr_code, [1; 10]); (PointsTo.Copy_code, [2; 1])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The address row is in the facts of the program. *)
  Example address_row_is_a_fact :
    In (PointsTo.Addr_code, [1; 10]) (PointsTo.facts copy_program).
  Proof.
    vm_compute. auto.
  Qed.

  (** No row is invented for a constructor that the program does not use. *)
  Example unused_constructor_gives_no_row :
    In (PointsTo.Load_code, [2; 1]) (PointsTo.facts copy_program) -> False.
  Proof.
    vm_compute. intros [Hrow | [Hrow | []]]; discriminate Hrow.
  Qed.

  (** An equational relation takes the rows of its input list too. *)
  Example equation_inputs_give_rows :
    Terms.facts two_merges = [(Terms.input1_code, [1; 2]); (Terms.input1_code, [3; 4])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lowered program of the path relation is well sorted. *)
  Example path_program_is_well_sorted :
    spec_ok Path.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lowered program of the points-to relation is well sorted. *)
  Example points_program_is_well_sorted :
    spec_ok PointsTo.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The path program uses no rewrites, so it is relational. *)
  Example path_program_is_relational :
    relational Path.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The points-to program uses no rewrites, so it is relational. *)
  Example points_program_is_relational :
    relational PointsTo.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rows of the path facts are input rows of the right arity. *)
  Example path_facts_are_input_rows :
    rows_ok Path.spec (Path.facts two_edges) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rows of the points-to facts are input rows of the right arity. *)
  Example points_facts_are_input_rows :
    rows_ok PointsTo.spec (PointsTo.facts copy_program) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A row of the relation table is not an input row. *)
  Example derived_row_is_not_an_input_row :
    rows_ok Path.spec [(Path.path_code, [1; 2])] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An input row of the wrong arity is rejected. *)
  Example wrong_arity_row_is_rejected :
    rows_ok Path.spec [(Path.input1_code, [1])] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FactTests.
