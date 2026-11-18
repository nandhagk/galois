(** * Primitives in programs on the engine

    Programs that compute with primitives, written as inductives and derived with
    [Egglog P from R with Arith]. Two of them come from the egglog web demo. [fib] is the
    Fibonacci relation. It never saturates, so the run stops at an iteration limit. [equiv] is
    the equality of arithmetic terms of [eqsat-basic.egg], solved by equality saturation.
    [shifted] and [sums_to] compute values in equation premises. The generated glue lemmas
    connect the rows and classes to the inductives.
    For example, after eight iterations the table of [fib] holds the row [7, 13], because the
    seventh Fibonacci number is 13.

    Groups:
    - [FibonacciTests] The relation [fib] under an iteration limit.
    - [TermTests] Saturating arithmetic terms with commutativity, distributivity and folding.
    - [EquationPremiseTests] Equation premises that compute values, in a relation and in
      an equation.
    - [GlueTests] The generated lemma turns a derived row into the inductive and back.

    Builds on: the derive command, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec LowerSig RunnerSig Runner Derive.
Import List.ListNotations.

(** * Fixtures *)

(** The primitives of the examples: addition, multiplication and successor on positives. *)
Egglog Primitives Arith Pos.add Pos.mul Pos.succ.

(** Values are positives, and the primitive function is the one that [Arith] generated. *)
Module ArithValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Arith.prim.
  Definition merge (_ : positive) := Pos.max.
End ArithValue.

Module ArithIndex := IndexCode ArithValue.
Module ArithJoin := JoinCode ArithValue ArithIndex.
Module ArithDatabase := DatabaseCode ArithValue ArithIndex.
Module ArithRun := RunCode ArithValue ArithIndex ArithJoin ArithDatabase.
Module ArithRunner :=
  RunnerCode ArithValue ArithIndex ArithJoin ArithDatabase ArithRun.

(** The Fibonacci relation. The index starts at one, where egglog starts at zero, so [fib n v]
    says that [v] is the [n]-th Fibonacci number with [fib 1 1] and [fib 2 1] as the base. *)
Open Scope positive_scope.
Inductive fib : positive -> positive -> Prop :=
  | fib_one : fib 1 1
  | fib_two : fib 2 1
  | fib_step x a b : fib x a -> fib (Pos.succ x) b ->
      fib (Pos.succ (Pos.succ x)) (Pos.add a b).
Close Scope positive_scope.

Egglog Fib from fib with Arith.

(** Arithmetic terms of [eqsat-basic.egg]. A number is a [Num], and [Var] stands for an unknown
    number. Strings wait for value encodings, so a variable carries a number that names it. *)
Inductive term : Type :=
  | Num (n : positive)
  | Var (x : positive)
  | Add (a b : term)
  | Mul (a b : term).

(** Equality of terms: the closure laws, commutativity of both operations, distributivity of
    multiplication over addition, and the folding of constants with the primitives. *)
Inductive equiv : term -> term -> Prop :=
  | equiv_refl a : equiv a a
  | equiv_sym a b : equiv a b -> equiv b a
  | equiv_trans a b c : equiv a b -> equiv b c -> equiv a c
  | equiv_add a a' b b' : equiv a a' -> equiv b b' -> equiv (Add a b) (Add a' b')
  | equiv_mul a a' b b' : equiv a a' -> equiv b b' -> equiv (Mul a b) (Mul a' b')
  | equiv_comm_add a b : equiv (Add a b) (Add b a)
  | equiv_comm_mul a b : equiv (Mul a b) (Mul b a)
  | equiv_distrib a b c : equiv (Mul a (Add b c)) (Add (Mul a b) (Mul a c))
  | equiv_fold_add x y : equiv (Add (Num x) (Num y)) (Num (Pos.add x y))
  | equiv_fold_mul x y : equiv (Mul (Num x) (Num y)) (Num (Pos.mul x y)).

Egglog Math from equiv with Arith.

(** Points moved by offsets: [y] is [x] moved by [k]. The equation premise computes [y]. *)
Inductive shifted (offsets : list (positive * positive)) : positive -> positive -> Prop :=
  | shift x k y : In (x, k) offsets -> Pos.add x k = y -> shifted offsets x y.

Egglog Shifts from shifted with Arith.

(** Sums of numbers. *)
Inductive sum_term : Type :=
  | Number (n : positive)
  | Plus (a b : sum_term).

(** Sums equal their value for each listed pair. The equation premise computes the value, so
    the clause is a union. *)
Inductive sums_to (pairs : list (positive * positive)) : sum_term -> sum_term -> Prop :=
  | sums_to_refl a : sums_to pairs a a
  | sums_to_sym a b : sums_to pairs a b -> sums_to pairs b a
  | sums_to_trans a b c : sums_to pairs a b -> sums_to pairs b c -> sums_to pairs a c
  | sums_to_plus a a' b b' : sums_to pairs a a' -> sums_to pairs b b' ->
      sums_to pairs (Plus a b) (Plus a' b')
  | sums_to_pair x y z : In (x, y) pairs -> Pos.add x y = z ->
      sums_to pairs (Plus (Number x) (Number y)) (Number z).

Egglog Sums from sums_to with Arith.

(** * Fibonacci *)

Module FibonacciTests.

  Local Open Scope positive_scope.

  (** Eight iterations reach the row for index eight. *)
  Definition fib_limits : limits := Limits 8%N 1000%N.

  (** The run of [fib] from its two base rows. *)
  Definition fib_run : stop * ArithDatabase.t :=
    ArithRunner.solve Fib.program Fib.facts fib_limits.

  (** The database after the run. *)
  Definition fib_result : ArithDatabase.t := snd fib_run.

  (** Every iteration derives a new row, so the run stops at its limit. *)
  Example fib_never_saturates :
    fst fib_run = IterLimit.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The seventh Fibonacci number is 13. Egglog numbers from zero, so this is its [fib 6]. *)
  Example seventh_number_is_thirteen :
    ArithRunner.holds Fib.fib_code [7; 13] fib_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The base rows are in the table. *)
  Example base_rows_hold :
    ArithRunner.holds Fib.fib_code [1; 1] fib_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A wrong value for an index is not derived. *)
  Example wrong_value_is_not_derived :
    ArithRunner.holds Fib.fib_code [7; 14] fib_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The index of a row is not its value, so the table has no row [13, 7]. *)
  Example index_and_value_do_not_swap :
    ArithRunner.holds Fib.fib_code [13; 7] fib_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An index past the iteration limit has no row yet, although its value is correct. *)
  Example rows_past_the_limit_are_not_derived :
    ArithRunner.holds Fib.fib_code [9; 34] fib_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The last index that the limit reaches has its row. *)
  Example last_row_in_the_limit_is_derived :
    ArithRunner.holds Fib.fib_code [8; 21] fib_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The engine accepts the sorts of the lowered program, so the theorems of the runner cover
      it. The successor in a premise argument is a check after the table atoms. *)
  Example fib_program_is_well_sorted :
    spec_ok Fib.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FibonacciTests.

(** * Terms *)

Module TermTests.

  Local Open Scope positive_scope.

  (** The unknown number [x]. *)
  Definition x_var : positive := 1.

  (** The tutorial's [2 * (x + 3)]. *)
  Definition two_times_sum : term := Mul (Num 2) (Add (Var x_var) (Num 3)).

  (** The product distributed over the sum, [2 * x + 2 * 3]. *)
  Definition distributed : term := Add (Mul (Num 2) (Var x_var)) (Mul (Num 2) (Num 3)).

  (** The sum written second and multiplied from the right, [(x + 3) * 2]. *)
  Definition flipped : term := Mul (Add (Num 3) (Var x_var)) (Num 2).

  (** A different sum of the same parts, [2 + 2 * x]. *)
  Definition other_sum : term := Add (Num 2) (Mul (Num 2) (Var x_var)).

  (** Twenty iterations and a thousand identifiers are far more than these terms need. *)
  Definition term_limits : limits := Limits 20%N 1000%N.

  (** Whether saturating the rules of [Math] with two terms puts them in one class. *)
  Definition joined (a b : term) : bool :=
    ArithRunner.equal Math.program [] term_limits (Math.encode_term a) (Math.encode_term b).

  (** The stop reason of saturating the rules of [Math] with two terms. *)
  Definition stopped (a b : term) : stop :=
    fst (fst (ArithRunner.saturate Math.program []
      [Math.encode_term a; Math.encode_term b] term_limits)).

  (** The engine accepts the sorts of the rules that [Math] derives. *)
  Example math_program_is_well_sorted :
    spec_ok Math.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Encoded terms are well sorted, so the theorems about saturation cover them. *)
  Example encoded_terms_are_well_sorted :
    term_ok Math.spec (Math.encode_term two_times_sum) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A number whose argument is a term instead of a value is not well sorted. *)
  Example misplaced_term_is_not_well_sorted :
    term_ok Math.spec (Model.EApp Math.Num_code [Math.encode_term (Num 1)]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rules stop adding terms, so saturation reaches a fixpoint. *)
  Example saturation_reaches_a_fixpoint :
    stopped two_times_sum distributed = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Distributivity puts a product of a sum in the class of the sum of products. *)
  Example distributivity_joins_the_classes :
    joined two_times_sum distributed = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Commutativity of both operations joins the product with its flipped form. *)
  Example commutativity_joins_the_classes :
    joined two_times_sum flipped = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A term that is not equal to the product stays in its own class. *)
  Example different_terms_stay_apart :
    joined two_times_sum other_sum = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A variable is not equal to a term that contains it. *)
  Example variable_stays_apart_from_its_context :
    joined (Var x_var) two_times_sum = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Distributing and folding [2 * 3] puts [2 * (x + 3)] in the class of [6 + 2 * x], as in
      the tutorial. *)
  Example folding_joins_the_tutorial_terms :
    joined two_times_sum (Add (Num 6) (Mul (Num 2) (Var x_var))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End TermTests.

(** * Equation premises *)

Module EquationPremiseTests.

  Local Open Scope positive_scope.

  (** The kind of an engine action. *)
  Variant action_kind : Type :=
    | KindMake
    | KindPut
    | KindUnion
    | KindLet.

  Definition action_kind_of (a : action positive) : action_kind :=
    match a with
    | Make _ _ _ => KindMake
    | Put _ _ _ => KindPut
    | Union _ _ => KindUnion
    | Let _ _ _ => KindLet
    end.

  (** The kinds of the actions of each rule of a program. *)
  Definition rule_action_kinds (p : program positive) : list (list action_kind) :=
    map (fun r => map action_kind_of (actions positive r)) (rules positive p).

  (** Two offsets, from 1 by 2 and from 5 by 10. *)
  Definition two_offsets : list (positive * positive) := [(1, 2); (5, 10)].

  (** The database after shifting the two offsets. *)
  Definition shifted_result : ArithDatabase.t :=
    snd (ArithRunner.solve Shifts.program (Shifts.facts two_offsets) (Limits 4%N 100%N)).

  (** The equation defines [y], so the rule computes it with [Let] before it puts the row. *)
  Example equation_defines_its_result :
    rule_action_kinds Shifts.program = [[KindLet; KindPut]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The program is relational, so the theorems about relations cover it. *)
  Example shifted_program_is_relational :
    spec_ok Shifts.spec = true /\ relational Shifts.spec = true.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

  (** Each offset gives its moved point. *)
  Example offsets_give_moved_points :
    ArithRunner.holds Shifts.shifted_code [1; 3] shifted_result = true /\
    ArithRunner.holds Shifts.shifted_code [5; 15] shifted_result = true.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

  (** A point is not moved by an offset of another point. *)
  Example offsets_stay_with_their_points :
    ArithRunner.holds Shifts.shifted_code [1; 11] shifted_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The glue lemma turns the inductive into a derived row. *)
  Example shift_gives_derived_row :
    derived Arith.prim Shifts.spec (Shifts.inputs two_offsets) Shifts.shifted_code [1; 3].
  Proof.
    apply (proj1 (Shifts.shifted_spec two_offsets 1 3)).
    apply (shift two_offsets 1 2 3); [left; reflexivity | reflexivity].
  Qed.

  (** The equation of [sums_to] computes its value from bound variables, so the clause is one
      rule that builds both sides and joins them. *)
  Example sum_clause_builds_and_joins :
    rule_action_kinds Sums.program =
      [[KindLet; KindMake; KindMake; KindMake; KindMake; KindUnion]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Whether saturation with the listed pairs puts two sums in one class. *)
  Definition joined (pairs : list (positive * positive)) (a b : sum_term) : bool :=
    ArithRunner.equal Sums.program (Sums.facts pairs) (Limits 4%N 100%N)
      (Sums.encode_sum_term a) (Sums.encode_sum_term b).

  (** A listed pair joins its sum with its value. *)
  Example listed_sum_joins_its_value :
    joined [(1, 2)] (Plus (Number 1) (Number 2)) (Number 3) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A sum of a pair that is not listed stays apart from its value. *)
  Example unlisted_sum_stays_apart :
    joined [] (Plus (Number 1) (Number 2)) (Number 3) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The glue lemma turns each instance of [sums_to] into a congruence of the encodings. *)
  Example sum_gives_congruence :
    congruent Arith.prim Sums.spec (Sums.inputs [(1, 2)])
      (Sums.encode_sum_term (Plus (Number 1) (Number 2))) (Sums.encode_sum_term (Number 3)).
  Proof.
    apply Sums.sums_to_congruent.
    apply (sums_to_pair [(1, 2)] 1 2 3); [left; reflexivity | reflexivity].
  Qed.

End EquationPremiseTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** The inductive number at index three gives the derived row, through [fib_spec]. *)
  Example fib_gives_derived_row :
    derived Arith.prim Fib.spec Fib.inputs Fib.fib_code [3; 2].
  Proof.
    apply (proj1 (Fib.fib_spec 3 2)).
    exact (fib_step 1 1 1 fib_one fib_two).
  Qed.

  (** A derived row gives the inductive number, through [fib_spec]. *)
  Example derived_row_gives_fib :
    derived Arith.prim Fib.spec Fib.inputs Fib.fib_code [7; 13] -> fib 7 13.
  Proof.
    intros Hrow.
    exact (proj2 (Fib.fib_spec 7 13) Hrow).
  Qed.

End GlueTests.
