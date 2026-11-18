(** * Cheapest terms of classes

    The cheapest term of a class after saturating arithmetic terms with the rules of
    [eqsat-basic.egg]. A cost module charges one for every constructor and every literal, plus
    the cost of the children, so the cost of a term is its size.
    For example, saturating [Add (Num 1) (Num 2)] folds it to [Num 3], whose class has the
    cheapest term [Num 3] at cost two instead of five.

    Groups:
    - [FoldingTests] A class that folds to a literal returns the literal.
    - [PlainTests] A class without folding returns an equal term that is no bigger.
    - [MissingTests] A class that does not exist has no term.
    - [BoundTests] The extracted DAG passes the bound check, and a costlier DAG of the same
      class fails it.

    Builds on: the extraction functor, the derive command, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key Heap.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run ExtractSig Extract.
From Galois.Front Require Import Spec LowerSig RunnerSig Runner Derive ExtractionSig Extraction.
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

(** Each constructor costs one more than its children together, and each literal costs one. *)
Module SizeCost <: COST_OPS ArithValue.
  Definition fn_cost (_ : positive) (cs : list N) := N.succ (fold_right N.add 0%N cs).
  Definition val_cost (_ : positive) := 1%N.
End SizeCost.

Module ArithExtract := ExtractCode ArithValue ArithIndex ArithDatabase SizeCost HeapCode.
Module ArithExtraction :=
  ExtractionCode ArithValue ArithIndex ArithJoin ArithDatabase ArithRun SizeCost ArithExtract.

(** Arithmetic terms of [eqsat-basic.egg]. A number is a [Num], and [Var] stands for an unknown
    number that a positive names. *)
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

(** The unknown number [x]. *)
Definition x_var : positive := 1%positive.

(** Twenty iterations and a thousand identifiers are far more than these terms need. *)
Definition term_limits : limits := Limits 20%N 1000%N.

(** No iterations, so the rules never fire. *)
Definition no_rounds : limits := Limits 0%N 1000%N.

(** The database and the cell after saturating a program with one term. *)
Definition saturated_with (lim : limits) (t : term) : ArithDatabase.t * option (cell positive) :=
  match ArithRunner.saturate Math.program [] [Math.encode_term t] lim with
  | (_, db, c :: _) => (db, Some c)
  | (_, db, []) => (db, None)
  end.

(** The cheapest term of the class of a saturated term, with the database that it was read
    from. A literal cell has no class. *)
Definition cheapest_of (lim : limits) (t : term) : option (@expr positive) :=
  match saturated_with lim t with
  | (db, Some (Id i)) =>
      ArithExtraction.cheapest Math.program db (fst (ArithDatabase.find i db))
  | _ => None
  end.

(** The size of an expression, as the cost module charges it. *)
Definition size (e : @expr positive) : N :=
  expression_cost SizeCost.fn_cost SizeCost.val_cost e.

(** The size of the cheapest term, when there is one. *)
Definition cheapest_size (lim : limits) (t : term) : option N :=
  option_map size (cheapest_of lim t).

(** Whether saturating puts a term and the cheapest term of its class in one class. *)
Definition represented (t : term) : bool :=
  match cheapest_of term_limits t with
  | Some e => ArithRunner.equal Math.program [] term_limits (Math.encode_term t) e
  | None => false
  end.

(** * Folding *)

Module FoldingTests.

  Local Open Scope positive_scope.

  (** The sum of two numbers. *)
  Definition one_plus_two : term := Add (Num 1) (Num 2).

  (** The cost module charges each constructor and literal, so the sum costs five. *)
  Example sum_costs_five :
    size (Math.encode_term one_plus_two) = 5%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Folding puts the literal in the class of the sum, and the literal is the cheapest term. *)
  Example folded_class_returns_the_literal :
    cheapest_of term_limits one_plus_two = Some (Math.encode_term (Num 3)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The literal costs two, less than the sum. *)
  Example folded_term_is_smaller :
    cheapest_size term_limits one_plus_two = Some 2%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without iterations the rules never fire, so the class keeps the sum that it was given. *)
  Example class_without_folding_keeps_the_sum :
    cheapest_of no_rounds one_plus_two = Some (Math.encode_term one_plus_two).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Folding the product of two numbers returns the literal too. *)
  Example folded_product_returns_the_literal :
    cheapest_of term_limits (Mul (Num 2) (Num 3)) = Some (Math.encode_term (Num 6)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Folding inside a larger term returns the cheapest rewrite of the whole term. The sum of
      two folded literals is itself folded. *)
  Example nested_folding_returns_one_literal :
    cheapest_of term_limits (Add (Add (Num 1) (Num 2)) (Num 4)) = Some (Math.encode_term (Num 7)).
  Proof.
    vm_compute. reflexivity.
  Qed.

End FoldingTests.

(** * Plain classes *)

Module PlainTests.

  Local Open Scope positive_scope.

  (** A product that has no folding opportunity, [2 * x]. *)
  Definition two_times_x : term := Mul (Num 2) (Var x_var).

  (** The returned term is in the class of the input. *)
  Example plain_class_is_represented :
    represented two_times_x = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The returned term is no bigger than the input, which costs five. *)
  Example plain_class_is_no_bigger :
    cheapest_size term_limits two_times_x = Some 5%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Distributing and folding leaves a class with several forms. [2 * (x + 3)] has a form
      [6 + 2 * x] of the same size, and no form is smaller, so the cheapest term costs eight. *)
  Example distributed_class_keeps_the_least_size :
    cheapest_size term_limits (Mul (Num 2) (Add (Var x_var) (Num 3))) = Some 8%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The cheapest term of the distributed class is in the class of the input. *)
  Example distributed_class_is_represented :
    represented (Mul (Num 2) (Add (Var x_var) (Num 3))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A variable alone is its own cheapest term, at cost two. *)
  Example variable_is_its_own_cheapest_term :
    cheapest_of term_limits (Var x_var) = Some (Math.encode_term (Var x_var)).
  Proof.
    vm_compute. reflexivity.
  Qed.

End PlainTests.

(** * Missing classes *)

Module MissingTests.

  Local Open Scope positive_scope.

  (** The database of a saturated sum. *)
  Definition sum_database : ArithDatabase.t :=
    fst (saturated_with term_limits (Add (Num 1) (Num 2))).

  (** The first identifier past the allocated ones. *)
  Definition unallocated : positive := N.succ_pos (ArithDatabase.ids sum_database).

  (** A class that was never allocated has no term. *)
  Example unallocated_class_has_no_term :
    ArithExtraction.cheapest Math.program sum_database unallocated = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The class of the saturated sum itself, when its cell is a class. *)
  Definition sum_class : option positive :=
    match snd (saturated_with term_limits (Add (Num 1) (Num 2))) with
    | Some (Id i) => Some (fst (ArithDatabase.find i sum_database))
    | _ => None
    end.

  (** The same database has a term for the class that exists, so the missing result is the
      identifier and not the database. *)
  Example allocated_class_has_a_term :
    match sum_class with
    | Some c =>
        match ArithExtraction.cheapest Math.program sum_database c with
        | Some _ => true
        | None => false
        end
    | None => false
    end = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MissingTests.

(** * Bound check *)

Module BoundTests.

  Local Open Scope positive_scope.

  (** The inventory of the arithmetic program. *)
  Definition math_inventory : list (positive * (N * nat)) :=
    ArithExtract.inventory (decls positive Math.program)
      (planned_slots (ArithRun.plan Math.program)).

  (** Whether the extracted DAG of the class of a saturated term passes the bound check. *)
  Definition bound_checked (lim : limits) (t : term) : bool :=
    match saturated_with lim t with
    | (db, Some (Id i)) =>
        let c := fst (ArithDatabase.find i db) in
        match ArithExtract.extract math_inventory db c with
        | Some g => ArithExtraction.best_bounded Math.program db c g
        | None => false
        end
    | _ => false
    end.

  (** The extracted DAG of the folded sum passes the check. *)
  Example folded_sum_passes_the_check :
    bound_checked term_limits (Add (Num 1) (Num 2)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The extracted DAG of a sum that no rule has folded passes the check. *)
  Example unfolded_sum_passes_the_check :
    bound_checked no_rounds (Add (Num 1) (Num 2)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The extracted DAG of the distributed class passes the check. *)
  Example distributed_class_passes_the_check :
    bound_checked term_limits (Mul (Num 2) (Add (Var x_var) (Num 3))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The extracted DAG of a variable passes the check. *)
  Example variable_passes_the_check :
    bound_checked term_limits (Var x_var) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The identifier of the output of a constructor row, when the row exists. *)
  Definition row_id (db : ArithDatabase.t) (f : positive) (k : list (cell positive)) :
      option positive :=
    match fst (ArithDatabase.lookup f k db) with
    | Some (Some (Id i)) => Some i
    | _ => None
    end.

  (** The saturated database of the sum, its class, and the DAG of the sum itself in it. *)
  Definition sum_dag : option (ArithDatabase.t * positive * extraction_dag positive) :=
    let db := fst (saturated_with term_limits (Add (Num 1) (Num 2))) in
    match row_id db Math.Num_code [Val 1], row_id db Math.Num_code [Val 2] with
    | Some a, Some b =>
        match row_id db Math.Add_code [Id a; Id b] with
        | Some c =>
            Some (db, c,
              [(a, (Math.Num_code, [Val 1])); (b, (Math.Num_code, [Val 2]));
               (c, (Math.Add_code, [Id a; Id b]))])
        | None => None
        end
    | _, _ => None
    end.

  (** The DAG of the sum is a certificate of its class, and the checker accepts it. *)
  Example sum_dag_is_checked :
    match sum_dag with
    | Some (db, c, g) =>
        match ArithExtract.check_dag db c g with
        | Some n => n
        | None => 0%N
        end
    | None => 0%N
    end = 5%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The DAG of the sum costs five where the literal of its class costs two, so it fails the
      check. *)
  Example costly_dag_fails_the_check :
    match sum_dag with
    | Some (db, c, g) => ArithExtraction.best_bounded Math.program db c g
    | None => true
    end = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End BoundTests.
