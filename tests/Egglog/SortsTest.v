(** * Program sort checks

    The program checker rejects actions that misuse values and class identifiers.
    For example, union requires two bound class identifiers.
    Builds on: Egglog syntax and sorts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Sorts.

Import List.ListNotations.

Definition value_relation : decl := Decl 1 [SVal] ORel.
Definition class_relation : decl := Decl 2 [SId] ORel.

(** Values cannot be united as class identifiers. *)
Example reject_union_values :
  check_program (Program positive [value_relation]
    [Rule positive [Fun positive 1 [Var 1] None] [Union (Var 1) (Var 1)]]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** A relation application must use the declared arity. *)
Example reject_wrong_arity :
  check_program (Program positive [value_relation]
    [Rule positive [Fun positive 1 [] None] []]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** An action cannot refer to a variable absent from its query. *)
Example reject_unbound_variable :
  check_program (Program positive [value_relation]
    [Rule positive [] [Put 1 [Var 1] None]]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** A literal cannot occupy a class identifier position. *)
Example reject_literal_class :
  check_program (Program positive [class_relation]
    [Rule positive [Fun positive 2 [Lit 1%positive] None] []]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** A bound value can be copied into a relation of the same sort. *)
Example accept_value_rule :
  check_program (Program positive [value_relation]
    [Rule positive [Fun positive 1 [Var 1] None] [Put 1 [Var 1] None]]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A duplicate declaration cannot override the first declaration's value argument. *)
Example accept_first_value_declaration :
  check_program (Program positive [Decl 1 [SVal] ORel; Decl 1 [SId] ORel]
    [Rule positive [Fun positive 1 [Lit 1%positive] None] []]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Reversing duplicate declarations makes the same literal argument ill sorted. *)
Example reject_first_class_declaration :
  check_program (Program positive [Decl 1 [SId] ORel; Decl 1 [SVal] ORel]
    [Rule positive [Fun positive 1 [Lit 1%positive] None] []]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** One query variable cannot occupy both a class position and a value position. *)
Example reject_conflicting_variable_sorts :
  check_program (Program positive [Decl 3 [SId; SVal] ORel]
    [Rule positive [Fun positive 3 [Var 1; Var 1] None] []]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Repeated occurrences of a variable may share a value sort. *)
Example accept_repeated_value_variable :
  check_program (Program positive [Decl 3 [SVal; SVal] ORel]
    [Rule positive [Fun positive 3 [Var 1; Var 1] None] []]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A lattice function produces a value that cannot be used by union. *)
Example reject_union_analysis_result :
  check_program (Program positive [Decl 4 [] (OLat 1)]
    [Rule positive [Fun positive 4 [] (Some (Var 1))] [Union (Var 1) (Var 1)]]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** A constructor may take a literal value while producing a class for union. *)
Example accept_constructor_with_literal :
  check_program (Program positive [Decl 5 [SVal] OId]
    [Rule positive [Fun positive 5 [Lit 1%positive] (Some (Var 1))]
      [Union (Var 1) (Var 1)]]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A make action binds the class identifier used by the following action. *)
Example accept_make_then_union :
  check_program (Program positive [Decl 5 [] OId]
    [Rule positive [] [Make 1 5 []; Union (Var 1) (Var 1)]]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Let changes its bound variable to a value even when it previously held a class. *)
Example reject_union_after_let :
  check_program (Program positive [Decl 5 [] OId]
    [Rule positive [] [Make 1 5 []; Let 1 7 []; Union (Var 1) (Var 1)]]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** A primitive query checks an existing result binding rather than creating one. *)
Example reject_unbound_primitive_result :
  check_program (Program positive [] [Rule positive [Prim positive 7 [] (Var 1)] []]) = false.
Proof.
  vm_compute. reflexivity.
Qed.
