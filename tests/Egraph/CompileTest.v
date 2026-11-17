(** * Flat rewrite compilation examples

    These examples check fresh variables, literal children and shared node references.
    For example, [f(x) = x] compiles to one query and one identifier union.

    Groups:
    - [RewriteTests] A rewrite compiles to a query and the unions of its right side.
    - [ConditionTests] A condition takes fresh variables after the left side's nodes.
    - [AnalysisTests] Compiling a program keeps its analysis rules.

    Builds on: Compile, Egraph syntax and the operations-only value interface. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax.
From Galois.Egraph Require Import Syntax Compile.

Import List.ListNotations.

(** * Fixtures *)

Module CompileValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) := Pos.max.
End CompileValue.

Module Compiler := CompileCode CompileValue.

(** A rewrite that erases a unary wrapper node, so that its argument replaces the node. *)
Definition erase_wrapper : rewrite positive :=
  Rewrite positive (FPat positive [PHole 1%positive; PApp 2%positive [0]] 1)
    (FPat positive [PHole 1%positive] 0) [].

(** * Rewrite *)

Module RewriteTests.

  (** The rule that the erasing rewrite compiles to, a query on node 2 and a union of its result. *)
  Definition erase_wrapper_rule : rule positive :=
    Rule positive [Fun positive 2%positive [Var 1%positive] (Some (Var 2%positive))]
      [Union (Var 2%positive) (Var 1%positive)].

  (** A rewrite that erases a wrapper becomes one query and one union of the two identifiers. *)
  Example wrapper_becomes_query_and_union :
    Compiler.compile_rule erase_wrapper = erase_wrapper_rule.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rewrite that replaces a literal child keeps the literal as a value in the new node. *)
  Definition rewrite_literal : rewrite positive :=
    Rewrite positive (FPat positive [PLit 7%positive; PApp 3%positive [0]] 1)
      (FPat positive [PLit 7%positive; PApp 4%positive [0]] 1) [].

  (** A literal child stays a value and is not turned into a class identifier. *)
  Example literal_children_remain_values :
    Compiler.compile_rule rewrite_literal =
      Rule positive [Fun positive 3%positive [Lit 7%positive] (Some (Var 2%positive))]
        [Make 3%positive 4%positive [Lit 7%positive];
         Union (Var 2%positive) (Var 3%positive)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A node that a left side names twice is matched once and reused for both children. *)
  Definition shared_wrapper : rewrite positive :=
    Rewrite positive
      (FPat positive [PHole 1%positive; PApp 2%positive [0]; PApp 3%positive [1; 1]] 2)
      (FPat positive [PHole 1%positive] 0) [].

  (** Shared children reuse the node that the left side names. *)
  Example shared_children_reuse_the_named_node :
    Compiler.flatten_lhs shared_wrapper =
      [Fun positive 2%positive [Var 1%positive] (Some (Var 3%positive));
       Fun positive 3%positive [Var 3%positive; Var 3%positive] (Some (Var 2%positive))].
  Proof.
    vm_compute. reflexivity.
  Qed.

End RewriteTests.

(** * Condition *)

Module ConditionTests.

  Local Open Scope positive_scope.

  (** A rewrite with a condition has a fresh root variable after the condition's variables. *)
  Definition guarded_wrapper : rewrite positive :=
    Rewrite positive (lhs positive erase_wrapper) (rhs positive erase_wrapper)
      [Fun positive 5 [Var 1] (Some (Var 31))].

  (** The root variable of the guarded rewrite is 32, one above the condition's variable 31. *)
  Example root_var_is_fresh_above_condition :
    Compiler.root_var guarded_wrapper = 32.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The condition's nodes follow the left side's nodes in the flattened left side. *)
  Example condition_follows_lhs_nodes :
    Compiler.flatten_lhs guarded_wrapper =
      [Fun positive 2 [Var 1] (Some (Var 32));
       Fun positive 5 [Var 1] (Some (Var 31))].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ConditionTests.

(** * Analysis *)

Module AnalysisTests.

  Local Open Scope positive_scope.

  (** An analysis rule with no query, which puts an empty tuple into relation 8. *)
  Definition analysis_rule : rule positive := Rule positive [] [Put 8 [] None].

  (** Compiling a program keeps its analysis rules unchanged. *)
  Example analysis_rules_pass_through :
    Compiler.compile [Decl 8 [] ORel] [] [analysis_rule] =
      Program positive [Decl 8 [] ORel] [analysis_rule].
  Proof.
    vm_compute. reflexivity.
  Qed.

End AnalysisTests.
