(** * Sorted front-end inputs

    These examples distinguish constructor classes, literal values and declared analyses.
    For example, an analysis may bind a value for a rewrite but cannot union two values.
    Builds on: Saturate and the flat Egraph syntax. *)

From Stdlib Require Import List PArith NArith Arith Lia Bool.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Egraph Require Import Syntax Saturate.

Import List.ListNotations.

Definition front_declarations : list decl :=
  [Decl 1%positive [SVal] OId;
   Decl 2%positive [SId; SId] OId;
   Decl 3%positive [SVal] ORel;
   Decl 4%positive [SId] (OLat 1%positive)].

Definition repeated_class : fpat positive :=
  FPat positive [PHole 7%positive; PApp 2%positive [0; 0]] 1.

Definition class_identity : rewrite positive :=
  Rewrite positive repeated_class (FPat positive [PHole 7%positive] 0) [].

Example accepts_constructor_to_class_hole :
  front_check front_declarations [class_identity] [] [] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition analysis_guarded : rewrite positive :=
  Rewrite positive repeated_class
    (FPat positive [PHole 9%positive; PApp 1%positive [0]] 1)
    [Fun positive 4%positive [Var 7%positive] (Some (Var 9%positive))].

Example accepts_value_hole_bound_by_analysis :
  front_check front_declarations [analysis_guarded] [] [] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unbound_right_hole :
  front_check front_declarations
    [Rewrite positive repeated_class (FPat positive [PHole 8%positive] 0) []] [] [] =
    Some (BadRewrite 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unused_pattern_node :
  front_check front_declarations
    [Rewrite positive
      (FPat positive [PHole 7%positive; PLit 1%positive; PApp 1%positive [0]] 2)
      (FPat positive [PHole 7%positive; PApp 1%positive [0]] 1) []] [] [] =
    Some (BadRewrite 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_inconsistent_hole_positions :
  front_check front_declarations
    [Rewrite positive
      (FPat positive [PHole 7%positive; PApp 1%positive [0]; PApp 2%positive [0; 1]] 2)
      (FPat positive [PHole 7%positive] 0) []] [] [] = Some (BadRewrite 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example reports_first_bad_analysis :
  @front_check positive front_declarations []
    [Rule positive [] [Put 3%positive [Lit 1%positive] None];
     Rule positive [] [Union (Lit 1%positive) (Lit 1%positive)]] [] =
    Some (BadAnalysis 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_literal_constructor_children :
  @front_check positive front_declarations [] []
    [FExpr positive [ELit 8%positive; EApp 1%positive [0]] 1] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_literal_input_root :
  @front_check positive front_declarations [] [] [FExpr positive [ELit 8%positive] 0] =
    Some (BadInput 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_forward_child :
  @front_check positive front_declarations [] []
    [FExpr positive [EApp 1%positive [1]; ELit 8%positive] 0] = Some (BadInput 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_unused_well_sorted_input_nodes :
  @front_check positive front_declarations [] []
    [FExpr positive [ELit 8%positive; EApp 1%positive [0]; ELit 9%positive] 1] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_declarations_keep_the_first_sort :
  @front_check positive [Decl 1%positive [SVal] OId; Decl 1%positive [SId] OId] [] []
    [FExpr positive [ELit 8%positive; EApp 1%positive [0]] 1] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_front_is_accepted :
  @front_check positive [] [] [] [] = None.
Proof.
  vm_compute. reflexivity.
Qed.
