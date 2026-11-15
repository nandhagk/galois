(** * Flat rewrite compilation examples

    These examples check fresh variables, literal children and shared node references.
    For example, [f(x) = x] compiles to one query and one identifier union.
    Builds on: Compile, Egraph syntax and the operations-only value interface. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax.
From Galois.Egraph Require Import Syntax Compile.

Import List.ListNotations.

Module CompileValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) := Pos.max.
End CompileValue.

Module Compiler := CompileCode CompileValue.

Definition erase_wrapper : rewrite positive :=
  Rewrite positive (FPat positive [PHole 1%positive; PApp 2%positive [0]] 1)
    (FPat positive [PHole 1%positive] 0) [].

Example wrapper_becomes_query_and_union :
  Compiler.compile_rule erase_wrapper =
    Rule positive [Fun positive 2%positive [Var 1%positive] (Some (Var 2%positive))]
      [Union (Var 2%positive) (Var 1%positive)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition rewrite_literal : rewrite positive :=
  Rewrite positive (FPat positive [PLit 7%positive; PApp 3%positive [0]] 1)
    (FPat positive [PLit 7%positive; PApp 4%positive [0]] 1) [].

Example literal_children_remain_values :
  Compiler.compile_rule rewrite_literal =
    Rule positive [Fun positive 3%positive [Lit 7%positive] (Some (Var 2%positive))]
      [Make 3%positive 4%positive [Lit 7%positive];
       Union (Var 2%positive) (Var 3%positive)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition guarded_wrapper : rewrite positive :=
  Rewrite positive (lhs positive erase_wrapper) (rhs positive erase_wrapper)
    [Fun positive 5%positive [Var 1%positive] (Some (Var 31%positive))].

Example condition_variables_stay_fresh :
  Compiler.root_var guarded_wrapper = 32%positive /\
  Compiler.flatten_lhs guarded_wrapper =
    [Fun positive 2%positive [Var 1%positive] (Some (Var 32%positive));
     Fun positive 5%positive [Var 1%positive] (Some (Var 31%positive))].
Proof.
  vm_compute. split; reflexivity.
Qed.

Definition shared_wrapper : rewrite positive :=
  Rewrite positive
    (FPat positive [PHole 1%positive; PApp 2%positive [0]; PApp 3%positive [1; 1]] 2)
    (FPat positive [PHole 1%positive] 0) [].

Example shared_children_reuse_the_named_node :
  Compiler.flatten_lhs shared_wrapper =
    [Fun positive 2%positive [Var 1%positive] (Some (Var 3%positive));
     Fun positive 3%positive [Var 3%positive; Var 3%positive] (Some (Var 2%positive))].
Proof.
  vm_compute. reflexivity.
Qed.

Example compilation_keeps_analysis_rules :
  Compiler.compile [Decl 8%positive [] ORel] []
    [Rule positive [] [Put 8%positive [] None]] =
  Program positive [Decl 8%positive [] ORel]
    [Rule positive [] [Put 8%positive [] None]].
Proof.
  vm_compute. reflexivity.
Qed.
