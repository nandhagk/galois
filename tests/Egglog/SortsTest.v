(** * Program sort checks

    The program checker rejects actions that misuse values and class identifiers.
    For example, union requires two bound class identifiers.
    Builds on: Egglog syntax and sorts.

    Groups:
    - [DeclarationTests] Arity and the sorts that a duplicate declaration keeps.
    - [VariableTests] Query variables and their sorts.
    - [ActionTests] The sorts of make, let, union and primitive results. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Sorts.

Import List.ListNotations.

(** * Fixtures *)

(** A relation of one value argument. *)
Definition value_relation : decl := Decl 1 [SVal] ORel.

(** A relation of one class argument. *)
Definition class_relation : decl := Decl 2 [SId] ORel.

Module DeclarationTests.

  Local Open Scope positive_scope.

  (** A relation application must use the declared arity. *)
  Example wrong_arity_rejected :
    check_program (Program positive [value_relation]
      [Rule positive [Fun positive 1 [] None] []]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The first of two duplicate declarations fixes the sort of the value argument. *)
  Example first_declaration_accepts_literal :
    check_program (Program positive [Decl 1 [SVal] ORel; Decl 1 [SId] ORel]
      [Rule positive [Fun positive 1 [Lit 1] None] []]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Reversing the duplicate declarations makes the same literal argument ill sorted. *)
  Example reversed_declaration_rejects_literal :
    check_program (Program positive [Decl 1 [SId] ORel; Decl 1 [SVal] ORel]
      [Rule positive [Fun positive 1 [Lit 1] None] []]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End DeclarationTests.

Module VariableTests.

  Local Open Scope positive_scope.

  (** A value cannot be united as a class identifier. *)
  Example union_of_values_rejected :
    check_program (Program positive [value_relation]
      [Rule positive [Fun positive 1 [Var 1] None] [Union (Var 1) (Var 1)]]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A bound value can be copied into a relation of the same sort. *)
  Example bound_value_copied_to_same_sort :
    check_program (Program positive [value_relation]
      [Rule positive [Fun positive 1 [Var 1] None] [Put 1 [Var 1] None]]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An action cannot refer to a variable absent from its query. *)
  Example unbound_variable_rejected :
    check_program (Program positive [value_relation]
      [Rule positive [] [Put 1 [Var 1] None]]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A literal cannot occupy a class identifier position. *)
  Example literal_in_class_position_rejected :
    check_program (Program positive [class_relation]
      [Rule positive [Fun positive 2 [Lit 1] None] []]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** One query variable cannot occupy both a class position and a value position. *)
  Example variable_with_two_sorts_rejected :
    check_program (Program positive [Decl 3 [SId; SVal] ORel]
      [Rule positive [Fun positive 3 [Var 1; Var 1] None] []]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Repeated occurrences of a variable may share a value sort. *)
  Example repeated_value_variable_accepted :
    check_program (Program positive [Decl 3 [SVal; SVal] ORel]
      [Rule positive [Fun positive 3 [Var 1; Var 1] None] []]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End VariableTests.

Module ActionTests.

  Local Open Scope positive_scope.

  (** A constructor may take a literal value while producing a class for union. *)
  Example constructor_with_literal_accepted :
    check_program (Program positive [Decl 5 [SVal] OId]
      [Rule positive [Fun positive 5 [Lit 1] (Some (Var 1))]
        [Union (Var 1) (Var 1)]]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A make action binds the class identifier used by the following action. *)
  Example make_binds_class_for_union :
    check_program (Program positive [Decl 5 [] OId]
      [Rule positive [] [Make 1 5 []; Union (Var 1) (Var 1)]]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Let changes its bound variable to a value even when it previously held a class. *)
  Example let_turns_class_into_value :
    check_program (Program positive [Decl 5 [] OId]
      [Rule positive [] [Make 1 5 []; Let 1 7 []; Union (Var 1) (Var 1)]]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A lattice function produces a value that cannot be used by union. *)
  Example lattice_result_union_rejected :
    check_program (Program positive [Decl 4 [] (OLat 1)]
      [Rule positive [Fun positive 4 [] (Some (Var 1))] [Union (Var 1) (Var 1)]]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A primitive query checks an existing result binding rather than creating one. *)
  Example primitive_result_must_be_bound :
    check_program (Program positive [] [Rule positive [Prim positive 7 [] (Var 1)] []]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ActionTests.
