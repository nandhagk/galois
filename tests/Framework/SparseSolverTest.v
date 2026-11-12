(** * Sparse constant propagation observations

    Certified sparse rows propagate constants through definitions and incoming operands.
    For example, one plus one reaches a join parameter as the 32-bit value two.
    Builds on: Framework.Sparse, Domains.Const and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith PArith ZArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig ValueSig ConstSig Const WordSig BitsLang.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Framework Require Import SparseSig Sparse.
Import List.ListNotations.
Local Open Scope nat_scope.

Module Prog <: TYPE. Definition t := nat. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module K <: TYPE. Definition t := BitsLangCode.op. End K.
Module G <: TYPE. Definition t := BitsLangCode.guard. End G.
Module Graph <: CFG_INDEXED_OPS Prog NatKeyCode Edge.
  Definition entries p := if Nat.eqb p 2 then [] else [0].
  Definition edges p := if Nat.eqb p 1 then [0; 1; 2; 3] else if Nat.eqb p 0 then [0; 1; 2] else [].
  Definition src (_ : nat) e := match e with 2 => 1 | 3 => 2 | _ => 0 end.
  Definition dst (_ : nat) e := match e with 0 => 1 | 1 => 2 | _ => 3 end.
  Definition nodes p := if Nat.eqb p 2 then [] else [0; 1; 2; 3].
  Definition out (_ : nat) n := match n with 0 => [0; 1] | 1 => [2] | 2 => [3] | _ => [] end.
  Definition inc (_ : nat) n := match n with 1 => [0] | 2 => [1] | 3 => [2; 3] | _ => [] end.
End Graph.
Module Ssa <: SSA_OPS Prog NatKeyCode Edge Graph NatKeyCode K G.
  Definition values p := if Nat.eqb p 2 then [] else if Nat.eqb p 3 then [0] else if Nat.eqb p 1 then [0; 1; 2; 3] else [0; 1].
  Definition def (_ : nat) x : definition nat nat BitsLangCode.op := match x with
    | 0 => Param 0 0
    | 1 => Op (BOp bvadd) [0; 0]
    | 2 => Param 3 0
    | _ => Arbitrary
    end.
  Definition home (_ : nat) x := if Nat.eqb x 2 then 3 else 0.
  Definition params p n := if Nat.eqb n 0 then [0] else if Nat.eqb p 1 && Nat.eqb n 3 then [2] else [].
  Definition args p e := if Nat.eqb p 1 && (Nat.eqb e 2 || Nat.eqb e 3) then [(2, 1)] else [].
  Definition guards (_ _ : nat) : list (BitsLangCode.guard * list nat) := [].
End Ssa.
Module WordEq <: VAL_EQ_OPS BitsLangCode.
  Definition eqb (a b : word) := Pos.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
End WordEq.
Module V := ConstCode BitsLangCode WordEq.
Module Transfer <: SSA_TRANSFER_OPS Prog NatKeyCode BitsLangCode V.
  Definition seed (p _ : nat) : V.t := FVal (32%positive, if Nat.eqb p 3 then 7%Z else 1%Z).
End Transfer.
Module S := SparseCode Prog NatKeyCode Edge Graph NatKeyCode BitsLangCode K G Ssa V Transfer.
Module P := PolicyCode V.
Module C := CheckCode V S.
Module W := WorklistCode V S P HeapCode.
Module R := NarrowCode V S C.
Module A := CertifiedCode V S W C R.
Definition flat_policy : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.
Definition number (z : Z) : tagged (flat Z) := TVal 32%positive (FVal z).
Definition old_value (a : V.t) : option (tagged (flat Z)) := match a with
  | FBot => None
  | FVal (w, z) => Some (TVal w (FVal z))
  | FTop => Some TAny
  end.
Definition observe p fuel xs := match A.analyze p flat_policy fuel with
  | Solved m => Some (map (fun x => old_value (C.look m x)) xs)
  | _ => None
  end.

Example sparse_numeric_values : observe 0 16%N [0; 1] = Some [Some (number 1); Some (number 2)].
Proof. vm_compute; reflexivity. Qed.

Example diamond_constant_through_phi_values : observe 1 32%N [0; 1; 2; 3] =
  Some [Some (number 1); Some (number 2); Some (number 2); Some TAny].
Proof. vm_compute; reflexivity. Qed.

Example diamond_analyze_finishes :
  match A.analyze 1 flat_policy 32%N with Solved _ => true | _ => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example diamond_zero_fuel : observe 1 1%N [2] = None.
Proof. vm_compute; reflexivity. Qed.

Example sparse_empty_values : observe 2 1%N [0] = Some [None].
Proof. vm_compute; reflexivity. Qed.

Definition candidate :=
  PTrieCode.set (NatKeyCode.encode 3) (3, V.top)
  (PTrieCode.set (NatKeyCode.encode 2) (2, FVal (32%positive, 2%Z))
  (PTrieCode.set (NatKeyCode.encode 1) (1, FVal (32%positive, 2%Z))
  (PTrieCode.set (NatKeyCode.encode 0) (0, FVal (32%positive, 1%Z)) PTrieCode.empty))).

Example sparse_candidate_accepted : C.check 0 candidate = true.
Proof. vm_compute; reflexivity. Qed.

Example sparse_candidate_rejected : C.check 0 PTrieCode.empty = false.
Proof. vm_compute; reflexivity. Qed.

Example diamond_post_solution_checked : C.check 1 candidate = true.
Proof. vm_compute; reflexivity. Qed.

Example diamond_unsound_phi_rejected : C.check 1
  (PTrieCode.set (NatKeyCode.encode 2) (2, FVal (32%positive, 0%Z)) candidate) = false.
Proof. vm_compute; reflexivity. Qed.

Example one_block_entry_parameter_value : observe 3 4%N [0] = Some [Some (number 7)].
Proof. vm_compute; reflexivity. Qed.

Definition tagged_value (a : V.t) : tagged (flat Z) := match a with
  | FBot => TBot
  | FVal (w, z) => TVal w (FVal z)
  | FTop => TAny
  end.

Example constant_arithmetic :
  tagged_value (V.forward (BOp bvadd) [FVal (32%positive, 1%Z); FVal (32%positive, 1%Z)]) =
    number 2.
Proof. vm_compute; reflexivity. Qed.

Example malformed_expression_has_bottom_forward_result :
  tagged_value (V.forward (BOp bvadd) [FVal (32%positive, 1%Z)]) = TBot.
Proof. vm_compute; reflexivity. Qed.

Example false_zero_subject :
  map tagged_value (V.guard (BTruth false) [FVal (32%positive, 0%Z)]) = [number 0].
Proof. vm_compute; reflexivity. Qed.

Example unknown_width_truth :
  (map tagged_value (V.guard (BTruth true) [FTop]),
   map tagged_value (V.guard (BTruth false) [FTop])) = ([TAny], [TAny]).
Proof. vm_compute; reflexivity. Qed.
