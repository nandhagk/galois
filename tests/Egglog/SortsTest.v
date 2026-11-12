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
