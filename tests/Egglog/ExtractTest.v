(** * Constructor inventory examples

    Inventory construction selects one unpermuted full slot per declared constructor.
    For example, repeated full slots produce one entry, and an earlier relation declaration
    prevents a later declaration of the same name from turning it into a constructor.
    Builds on: Extract, Database and Index code towers. *)

From Stdlib Require Import List PArith NArith.
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
