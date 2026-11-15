(** * Constructor inventories and checked certificates

    Inventories select full constructor slots, and certificates unfold through earlier entries.
    For example, shared children contribute their tree cost each time they occur, while a
    forward reference is rejected before costing.
    Builds on: Extract, Database and Index code towers. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig Syntax Index Database ExtractSig Extract.

Import List.ListNotations.

Module InventoryValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End InventoryValue.

Module InventoryIndex := IndexCode InventoryValue.
Module InventoryDatabase := DatabaseCode InventoryValue InventoryIndex.

Module InventoryCost <: COST_OPS InventoryValue.
  Definition fn_cost (_ : positive) (cs : list N) := N.succ (fold_right N.add 0%N cs).
  Definition val_cost (_ : positive) := 1%N.
End InventoryCost.

Module InventoryExtract :=
  ExtractCode InventoryValue InventoryIndex InventoryDatabase InventoryCost.

Example inventory_full_slots_only :
  InventoryExtract.inventory
    [Decl 3%positive [SId; SVal] OId; Decl 4%positive [] ORel;
     Decl 3%positive [] ORel; Decl 5%positive [] OId; Decl 6%positive [] (OLat 1%positive)]
    [(3%positive, [0; 2; 1]); (4%positive, []); (3%positive, [0; 1; 2]);
     (5%positive, [0]); (3%positive, [0; 1; 2]); (99%positive, [0])] =
    [(3%positive, 2%N); (5%positive, 3%N)].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_first_declaration_wins :
  InventoryExtract.inventory [Decl 3%positive [] ORel; Decl 3%positive [] OId]
    [(3%positive, [0])] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_matching_arity :
  InventoryExtract.inventory [Decl 3%positive [SVal] OId]
    [(3%positive, [0]); (3%positive, [0; 1; 2]); (3%positive, [0; 1])] =
    [(3%positive, 2%N)].
Proof.
  vm_compute. reflexivity.
Qed.

Example inventory_empty_layout :
  InventoryExtract.inventory [Decl 3%positive [SVal] OId] [] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_shared_children :
  dag_unfold [(1%positive, (10%positive, [Val 7%positive]));
    (2%positive, (20%positive, [Id 1%positive; Id 1%positive]))] 2%positive =
    Some (Model.EApp 20%positive
      [Model.EApp 10%positive [Model.ELit 7%positive];
       Model.EApp 10%positive [Model.ELit 7%positive]]).
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_forward_reference :
  @dag_unfold positive
    [(1%positive, (10%positive, [Id 2%positive])); (2%positive, (20%positive, []))]
    1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_self_reference :
  @dag_unfold positive [(1%positive, (10%positive, [Id 1%positive]))] 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_independent_root :
  @dag_unfold positive
    [(1%positive, (10%positive, [Id 1%positive])); (2%positive, (20%positive, []))]
    2%positive = Some (Model.EApp 20%positive []).
Proof.
  vm_compute. reflexivity.
Qed.

Example unfold_missing_root :
  @dag_unfold positive [(1%positive, (10%positive, []))] 2%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition checker_database : InventoryDatabase.t :=
  let db := InventoryDatabase.init
    [Decl 10%positive [SVal] OId; Decl 20%positive [SId; SId] OId;
     Decl 30%positive [] OId]
    [(10%positive, [0; 1]); (20%positive, [0; 1; 2]); (30%positive, [0])] in
  let db := snd (InventoryDatabase.make 10%positive [Val 7%positive] db) in
  let db := snd (InventoryDatabase.make 20%positive [Id 1%positive; Id 1%positive] db) in
  snd (InventoryDatabase.make 30%positive [] db).

Definition checker_graph : extraction_dag positive :=
  [(1%positive, (10%positive, [Val 7%positive]));
   (2%positive, (20%positive, [Id 1%positive; Id 1%positive]));
   (3%positive, (30%positive, []))].

Example check_dag_shared_children :
  InventoryExtract.check_dag checker_database 2%positive checker_graph = Some 5%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_root_before_unrelated_rows :
  InventoryExtract.check_dag checker_database 1%positive checker_graph = Some 2%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_unrelated_invalid_row :
  InventoryExtract.check_dag checker_database 2%positive
    (checker_graph ++ [(4%positive, (99%positive, []))]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_forward_child :
  InventoryExtract.check_dag checker_database 2%positive
    [(2%positive, (20%positive, [Id 1%positive; Id 1%positive]));
     (1%positive, (10%positive, [Val 7%positive]))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_duplicate_name :
  InventoryExtract.check_dag checker_database 1%positive
    [(1%positive, (10%positive, [Val 7%positive]));
     (1%positive, (10%positive, [Val 7%positive]))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_wrong_output :
  InventoryExtract.check_dag checker_database 2%positive
    [(2%positive, (10%positive, [Val 7%positive]))] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_missing_root :
  InventoryExtract.check_dag checker_database 4%positive checker_graph = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example check_dag_empty :
  InventoryExtract.check_dag checker_database 1%positive [] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example dag_needed_excludes_unrelated_rows :
  dag_seen (dag_needed checker_graph (PTrieCode.set 1%positive tt Empty)) 2%positive = false.
Proof.
  vm_compute. reflexivity.
Qed.
