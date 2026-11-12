(** * Map lattice fixtures

    These examples check a sparse map with a bottom default.
    For example, joining two singleton maps keeps both bindings.
    Builds on: MapLattice, Map, Key and Simple. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import MapLattice Simple JoinWidening.
Import List.ListNotations.

Module PosMap := TrieMapCode PosKeyCode.
Module Env := MapLatticeCode PosKeyCode PosMap BoolLatCode.
Module EnvWide := JoinWideningCode Env.
Definition e0 : PosMap.t bool := PosMap.empty.
Definition e1 := PosMap.set 1%positive true e0.
Definition e2 := PosMap.set 2%positive true e0.

Example bottom_default_operations :
  (Env.leb e0 e1, Env.leb e1 e2, PosMap.elements (Env.join e1 e2)) =
  (true, false, [(2%positive, true); (1%positive, true)]).
Proof. vm_compute. reflexivity. Qed.

Example constructed_bottom_default_comparison_reflexive :
  let m := PosMap.set 1%positive true (PosMap.set 1%positive false PosMap.empty) in
  Env.leb m m = true.
Proof. vm_compute. reflexivity. Qed.

Example bottom_default_widen_narrow :
  (PosMap.elements (EnvWide.widen tt e1 e2), PosMap.elements (EnvWide.narrow e1 e2)) =
  ([(2%positive, true); (1%positive, true)], [(1%positive, true)]).
Proof. vm_compute. reflexivity. Qed.

(* Top-default, cost and law examples are in LatticeEnvTest.v at 87192fe. *)
