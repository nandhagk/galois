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
    - [PrimitiveSetTests] A primitive set dispatches each generated code to its function.
    - [PrimitiveReadingTests] Applications of primitives become primitive patterns.
    - [PrimitiveGlueTests] A glue lemma is stated for the set, or for any primitive function.

    Builds on: the derive command, the specifications and the runner conditions. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax.
From Galois.Front Require Import Spec LowerSig RunnerSig Derive.
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

(** The primitives of the examples: addition, multiplication and successor on positives. *)
Egglog Primitives Arith Pos.add Pos.mul Pos.succ.

(** Fibonacci with the successor of an index and the sum of two numbers inside the clauses. *)
Open Scope positive_scope.
Inductive fib : positive -> positive -> Prop :=
  | fib_one : fib 1 1
  | fib_two : fib 2 1
  | fib_step x a b : fib x a -> fib (Pos.succ x) b ->
      fib (Pos.succ (Pos.succ x)) (Pos.add a b).

Close Scope positive_scope.

Egglog Fib from fib with Arith.

(** The primitive codes in a pattern, in order. *)
Fixpoint pat_ops (p : pat positive) : list positive :=
  match p with
  | PVar _ => []
  | PVal _ => []
  | PNode _ args =>
      (fix go (ps : list (pat positive)) : list positive :=
         match ps with
         | [] => []
         | q :: rest => pat_ops q ++ go rest
         end) args
  | POp c args =>
      c :: (fix go (ps : list (pat positive)) : list positive :=
              match ps with
              | [] => []
              | q :: rest => pat_ops q ++ go rest
              end) args
  end.

(** The primitive codes in the arguments of a premise, in order. *)
Definition premise_ops (p : premise positive) : list positive :=
  match p with
  | Holds _ args => flat_map pat_ops args
  | Equals _ args v => flat_map pat_ops args ++ pat_ops v
  | Computes _ args v => flat_map pat_ops args ++ pat_ops v
  end.

(** The primitive codes in the arguments of the head of a clause, in order. *)
Definition head_ops (c : clause positive) : list positive :=
  match head c with
  | Derive _ args => flat_map pat_ops args
  | _ => []
  end.

(** * Pair inputs *)

Module PairInputTests.

  (** A list of pairs is one input table, so the program declares the relation and that table. *)
  Example pair_list_is_one_table :
    map name (tables Path.spec) = [Path.path_code; Path.edges_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Only the table of the pair list takes rows from the input. *)
  Example pair_table_is_the_only_input :
    inputs Path.spec = [Path.edges_code].
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
      [[Path.edges_code]; [Path.path_code; Path.edges_code]].
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

  (** The tables that the query of a rule reads, in order. *)
  Definition rule_tables (r : rule positive) : list positive :=
    map (fun a => match a with Fun _ f _ _ => f | Prim _ p _ _ => p end) (query positive r).

  (** Each clause is one rule. The union reads its input row, and a rewrite reads the tables of
      the constructors of its left side after its premises. *)
  Example rewrites_match_their_left_sides :
    map rule_tables (spec_rules Terms.spec) =
      [[Terms.merges_code]; [Terms.Add_code];
       [Terms.merges_code; Terms.Num_code; Terms.Add_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equational relation has no table of its own. The input list and the constructors of
      the datatype are the tables. *)
  Example datatype_constructors_are_tables :
    map name (tables Terms.spec) = [Terms.merges_code; Terms.Num_code; Terms.Add_code].
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
    Path.facts two_edges = [(Path.edges_code, [1; 2]); (Path.edges_code, [2; 3])].
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
    Terms.facts two_merges = [(Terms.merges_code, [1; 2]); (Terms.merges_code, [3; 4])].
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
    rows_ok Path.spec [(Path.edges_code, [1])] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FactTests.

(** * Primitive sets *)

Module PrimitiveSetTests.

  Local Open Scope positive_scope.

  (** Every registered function has its own code. *)
  Example codes_are_distinct :
    Arith.add_code <> Arith.mul_code /\ Arith.add_code <> Arith.succ_code /\
    Arith.mul_code <> Arith.succ_code.
  Proof.
    vm_compute. repeat split; discriminate.
  Qed.

  (** The primitive of the addition code adds its two arguments. *)
  Example add_code_adds :
    Arith.prim Arith.add_code [2; 3] = Some 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The primitive of the multiplication code multiplies its two arguments. *)
  Example mul_code_multiplies :
    Arith.prim Arith.mul_code [2; 3] = Some 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The primitive of the successor code takes one argument. *)
  Example succ_code_takes_one_argument :
    Arith.prim Arith.succ_code [4] = Some 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A call with the wrong number of arguments has no result. *)
  Example wrong_arity_has_no_result :
    Arith.prim Arith.add_code [2] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A code that is not registered has no result. *)
  Example unregistered_code_has_no_result :
    Arith.prim (Pos.succ (Arith.add_code + Arith.mul_code + Arith.succ_code)) [2; 3] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PrimitiveSetTests.

(** * Reading primitives *)

Module PrimitiveReadingTests.

  (** The clause of the step constructor, the third of Fibonacci. *)
  Definition fib_step_clause : option (clause positive) := nth_error (clauses Fib.spec) 2.

  (** An application in a premise argument is a primitive pattern with the generated code, and
      the premise that reads the first index has none. *)
  Example application_in_premise_becomes_op :
    option_map (fun c => map premise_ops (body c)) fib_step_clause =
      Some [[]; [Arith.succ_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An application in the head is a primitive pattern too, and a nested application keeps its
      order, outermost first. *)
  Example application_in_head_becomes_op :
    option_map head_ops fib_step_clause =
      Some [Arith.succ_code; Arith.succ_code; Arith.add_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The clauses without applications have no primitive pattern. *)
  Example base_clauses_use_no_primitive :
    map (fun c => (flat_map premise_ops (body c), head_ops c)) (firstn 2 (clauses Fib.spec)) =
      [([], []); ([], [])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (* An equation premise [Pos.add a b = c] should be read as a [Computes] premise with the code of
     [Pos.add], and the head should use [c]:
       expected: the command derives the program
       actual:   [Egglog R from r with Arith] fails without a message on an inductive with the
                 premise [Pos.succ x = y -> r y]
     Open problems: the command rejects equation premises over primitives. *)

End PrimitiveReadingTests.

(** * Glue lemmas *)

Module PrimitiveGlueTests.

  (** A program read with a primitive set states its lemma for the primitive function of the
      set, with no argument for it. *)
  Example set_fixes_the_primitive_function :
    forall x v, fib x v <-> derived Arith.prim Fib.spec Fib.inputs Fib.fib_code [x; v].
  Proof.
    exact Fib.fib_spec.
  Qed.

  (** A program read without a set keeps the primitive function as an argument, so its lemma
      holds for every function. *)
  Example no_set_keeps_the_generic_function :
    forall (prim : positive -> list positive -> option positive) edges x y,
      path edges x y <-> derived prim Path.spec (Path.inputs edges) Path.path_code [x; y].
  Proof.
    exact Path.path_spec.
  Qed.

End PrimitiveGlueTests.
