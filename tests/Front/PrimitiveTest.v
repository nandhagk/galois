(** * Primitives in programs on the engine

    Two programs of the egglog web demo that compute with primitives, written as inductives and
    derived with [Egglog P from R with Arith]. [fib] is the Fibonacci relation. It never
    saturates, so the run stops at an iteration limit. [equiv] is the equality of arithmetic
    terms of [eqsat-basic.egg], solved by equality saturation. The generated glue lemma of [fib]
    connects its rows to the inductive.
    For example, after eight iterations the table of [fib] holds the row [7, 13], because the
    seventh Fibonacci number is 13.

    Groups:
    - [FibonacciTests] The relation [fib] under an iteration limit.
    - [TermTests] Saturating arithmetic terms with commutativity and distributivity.
    - [GlueTests] The generated lemma turns a derived row into the inductive and back.

    Builds on: the derive command, the runner, the saturation front end and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Egraph Require Import Syntax Compile Saturate.
From Galois.Front Require Import Spec LowerSig Runner Derive.
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
Module ArithCompile := CompileCode ArithValue.
Module ArithSaturate :=
  SaturateCode ArithValue ArithIndex ArithJoin ArithDatabase ArithRun ArithCompile.

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

(** Equality of terms: the closure laws, commutativity of both operations and distributivity
    of multiplication over addition. Constant folding is missing, see the end of [TermTests]. *)
Inductive equiv : term -> term -> Prop :=
  | equiv_refl a : equiv a a
  | equiv_sym a b : equiv a b -> equiv b a
  | equiv_trans a b c : equiv a b -> equiv b c -> equiv a c
  | equiv_add a a' b b' : equiv a a' -> equiv b b' -> equiv (Add a b) (Add a' b')
  | equiv_mul a a' b b' : equiv a a' -> equiv b b' -> equiv (Mul a b) (Mul a' b')
  | equiv_comm_add a b : equiv (Add a b) (Add b a)
  | equiv_comm_mul a b : equiv (Mul a b) (Mul b a)
  | equiv_distrib a b c : equiv (Mul a (Add b c)) (Add (Mul a b) (Mul a c)).

Egglog Math from equiv with Arith.

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

  (* The lowered program of [fib] is not accepted by the sort check, so the theorems of the
     runner do not cover it yet.
       expected: [spec_ok Fib.spec = true]
       actual:   [spec_ok Fib.spec = false]
     The check [query_prim] requires the result of a primitive atom to be bound before the
     atom, but a primitive inside a premise argument is lowered to an atom with a fresh
     result. Open problems: sort check of primitive atoms with fresh results. *)

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

  (** The flat nodes of an expression, in post-order, and the index of its root. *)
  Fixpoint flat (ns : list (enode positive)) (e : @Model.expr positive) :
      list (enode positive) * nat :=
    match e with
    | Model.ELit v => (ns ++ [ELit v], length ns)
    | Model.EApp f args =>
        let '(ns1, children) :=
          (fix go (ns : list (enode positive)) (args : list (@Model.expr positive)) :
              list (enode positive) * list nat :=
             match args with
             | [] => (ns, [])
             | a :: rest =>
                 let '(ns1, i) := flat ns a in
                 let '(ns2, others) := go ns1 rest in
                 (ns2, i :: others)
             end) ns args in
        (ns1 ++ [EApp f children], length ns1)
    end.

  (** The input of the engine that adds a term, through the generated encoder. *)
  Definition input_of (t : term) : fexpr positive :=
    let '(ns, root) := flat [] (Math.encode_term t) in FExpr positive ns root.

  (** Twenty iterations and a thousand identifiers are far more than these terms need. *)
  Definition term_limits : limits := Limits 20%N 1000%N.

  (** The saturation of two terms with the rewrites of [Math]. *)
  Definition saturate_pair (a b : term) :=
    ArithSaturate.saturate (tables Math.spec) Math.rewrites (spec_rules Math.spec) term_limits
      [input_of a; input_of b].

  (** Whether saturating two terms puts them in one class. *)
  Definition joined (a b : term) : bool :=
    match saturate_pair a b with
    | inr (_, db, [i; j]) => Pos.eqb (fst (ArithDatabase.find i db)) (fst (ArithDatabase.find j db))
    | _ => false
    end.

  (** The stop reason of saturating two terms. *)
  Definition stopped (a b : term) : option stop :=
    match saturate_pair a b with
    | inr (st, _, _) => Some st
    | inl _ => None
    end.

  (** The front end accepts the rewrites that [Math] derives and the encoded inputs. *)
  Example front_end_accepts_the_program :
    ArithSaturate.check_front (tables Math.spec) Math.rewrites (spec_rules Math.spec)
      [input_of two_times_sum; input_of distributed] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without folding the rewrites stop growing, so saturation reaches a fixpoint. *)
  Example saturation_reaches_a_fixpoint :
    stopped two_times_sum distributed = Some Saturated.
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

  (* The tutorial also folds constants, with the clauses
       [equiv_fold_add x y : equiv (Add (Num x) (Num y)) (Num (Pos.add x y))]
       [equiv_fold_mul x y : equiv (Mul (Num x) (Num y)) (Num (Pos.mul x y))]
     so that [6 + 2 * x] joins the class of [2 * (x + 3)]. The command derives both clauses as
     rewrites, but the front end rejects the first of them:
       expected: [joined two_times_sum (Add (Num 6) (Mul (Num 2) (Var x_var))) = true]
       actual:   [check_front .. = Some (BadRewrite 3)]
     The right side of a folding rewrite is a hole that a primitive atom of the condition
     binds. The check [query_prim] requires that atom's result to be bound already. Open
     problems: sort check of primitive atoms in rewrites that fold constants. *)

End TermTests.

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
