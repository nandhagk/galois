(** * Sparse constant propagation observations

    Certified sparse rows propagate constants through definitions and incoming operands.
    For example, one plus one reaches a join parameter as the 32-bit value two.

    Groups:
    - [NumericTests] The numeric program gives its constants by node, and the fuel bounds the
      solution.
    - [CheckTests] Candidates for the numeric and diamond systems are accepted or rejected.
    - [ValueTests] The constant domain adds, guards and orders its values as stated.
    - [TreeTests] The supplied dominator trees pass the tree checker.
    - [IdentityTests] A system whose seeds are top gives top at every node.

    Builds on: Framework.Sparse, Domains.Const and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith PArith ZArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Bits Require Import Word Op.
From Galois.Graph Require Import Data Digraph Dom.
From Galois.Domains Require Import LangSig ValueSig ConstSig Const WordSig BitsLang.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Framework Require Import SparseSig Sparse.
Import List.ListNotations.
Local Open Scope nat_scope.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := nat. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module K <: TYPE. Definition t := BitsLangCode.op. End K.
Module G <: TYPE. Definition t := BitsLangCode.guard. End G.

(** A CFG with four nodes and four edges, where program 2 has no entries or nodes. *)
Module Graph <: CFG_INDEXED_OPS Prog NatKeyCode Edge.
  Definition entries p := if Nat.eqb p 2 then [] else [0].
  Definition edges p := if Nat.eqb p 1 then [0; 1; 2; 3] else if Nat.eqb p 0 then [0; 1; 2] else [].
  Definition src (_ : nat) e := match e with 2 => 1 | 3 => 2 | _ => 0 end.
  Definition dst (_ : nat) e := match e with 0 => 1 | 1 => 2 | _ => 3 end.
  Definition nodes p := if Nat.eqb p 2 then [] else [0; 1; 2; 3].
  Definition out (_ : nat) n := match n with 0 => [0; 1] | 1 => [2] | 2 => [3] | _ => [] end.
  Definition inc (_ : nat) n := match n with 1 => [0] | 2 => [1] | 3 => [2; 3] | _ => [] end.
End Graph.

(** The SSA of the numeric program: values 0 and 1, where value 1 adds value 0 to itself. *)
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
  Definition entry_params p := flat_map (params p) (Graph.entries p).
  Definition arg_rows p := flat_map (fun e => map (pair e) (args p e)) (Graph.edges p).
End Ssa.

(** Words compared by their width and value. *)
Module WordEq <: VAL_EQ_OPS BitsLangCode.
  Definition eqb (a b : word) := Pos.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
End WordEq.

Module V := ConstCode BitsLangCode WordEq.

(** The seed of program p is the 32-bit value 1, or 7 in program 3. *)
Module Transfer <: SSA_TRANSFER_OPS Prog NatKeyCode BitsLangCode V.
  Definition seed (p _ : nat) : V.t := FVal (32%positive, if Nat.eqb p 3 then 7%Z else 1%Z).
End Transfer.

Module S := SparseCode Prog NatKeyCode Edge Graph NatKeyCode BitsLangCode K G Ssa V Transfer.
Module P := PolicyCode V.
Module C := CheckCode V S.
Module W := WorklistCode V S P HeapCode.
Module R := NarrowCode V S C.
Module A := CertifiedCode V S W C R.

(** The policy with empty tries, unit parameter and bound 0. *)
Definition flat_policy : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** The 32-bit tagged constant with the value z. *)
Definition number (z : Z) : tagged (flat Z) := TVal 32%positive (FVal z).

(** The tagged form of a constant-domain value. *)
Definition old_value (a : V.t) : option (tagged (flat Z)) := match a with
  | FBot => None
  | FVal (w, z) => Some (TVal w (FVal z))
  | FTop => Some TAny
  end.

(** The tagged values of the nodes xs in the solution of program p, if it is solved within fuel. *)
Definition observe p fuel xs := match A.analyze p flat_policy fuel with
  | Solved m => Some (map (fun x => old_value (C.look m x)) xs)
  | _ => None
  end.

(** A candidate that gives 1 at node 0, 2 at nodes 1 and 2, and top at node 3. *)
Definition candidate :=
  PTrieCode.set (NatKeyCode.encode 3) (3, V.top)
  (PTrieCode.set (NatKeyCode.encode 2) (2, FVal (32%positive, 2%Z))
  (PTrieCode.set (NatKeyCode.encode 1) (1, FVal (32%positive, 2%Z))
  (PTrieCode.set (NatKeyCode.encode 0) (0, FVal (32%positive, 1%Z)) PTrieCode.empty))).

(** * Numeric *)

Module NumericTests.

  (** The numeric program gives 1 at node 0 and 2 at node 1. *)
  Example numeric_values_by_node : observe 0 16%N [0; 1] = Some [Some (number 1); Some (number 2)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The constant 2 reaches nodes 1 and 2, and node 3 is top. *)
  Example phi_constant_through_join : observe 1 32%N [0; 1; 2; 3] =
    Some [Some (number 1); Some (number 2); Some (number 2); Some TAny].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With fuel 32 the diamond program is solved. *)
  Example diamond_solution_found :
    match A.analyze 1 flat_policy 32%N with Solved _ => true | _ => false end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With fuel 1 the diamond program gives no solution at node 2. *)
  Example one_fuel_gives_none : observe 1 1%N [2] = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty program 2 has no values, so its node has no constant. *)
  Example empty_program_gives_none : observe 2 1%N [0] = Some [None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The single entry parameter of program 3 holds 7. *)
  Example entry_parameter_value : observe 3 4%N [0] = Some [Some (number 7)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The numeric program is solved within fuel 16. *)
  Example numeric_run_solved :
    match A.analyze 0 flat_policy 16%N with Solved _ => true | _ => false end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The constant 2 propagates to node 1 of the numeric program. *)
  Example constant_propagates_to_one : observe 0 16%N [1] = Some [Some (number 2)].
  Proof.
    vm_compute; reflexivity.
  Qed.

End NumericTests.

(** * Checks *)

Module CheckTests.

  (** The numeric candidate passes the checker for program 0. *)
  Example numeric_candidate_accepted : C.check 0 candidate = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty candidate fails the checker for program 0. *)
  Example empty_candidate_rejected : C.check 0 PTrieCode.empty = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The numeric candidate is a checked post-solution of the diamond program. *)
  Example diamond_solution_checked : C.check 1 candidate = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Giving node 2 the value 0 makes the candidate unsound for the diamond. *)
  Example unsound_phi_rejected : C.check 1
    (PTrieCode.set (NatKeyCode.encode 2) (2, FVal (32%positive, 0%Z)) candidate) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CheckTests.

(** * Values *)

Module ValueTests.

  (** The tagged value of a constant of the domain. *)
  Definition tagged_value (a : V.t) : tagged (flat Z) := match a with
    | FBot => TBot
    | FVal (w, z) => TVal w (FVal z)
    | FTop => TAny
    end.

  (** Adding 1 to 1 under bvadd gives the constant 2. *)
  Example bvadd_of_one_and_one :
    tagged_value (V.forward (BOp bvadd) [FVal (32%positive, 1%Z); FVal (32%positive, 1%Z)]) =
      number 2.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A malformed addition with a single operand has bottom as its forward result. *)
  Example malformed_add_is_bottom :
    tagged_value (V.forward (BOp bvadd) [FVal (32%positive, 1%Z)]) = TBot.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A false truth guard keeps the zero subject as the constant 0. *)
  Example false_guard_keeps_zero :
    map tagged_value (V.guard (BTruth false) [FVal (32%positive, 0%Z)]) = [number 0].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A true truth guard on an unknown width gives Any. *)
  Example true_guard_on_top_any :
    map tagged_value (V.guard (BTruth true) [FTop]) = [TAny].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A false truth guard on an unknown width gives Any. *)
  Example false_guard_on_top_any :
    map tagged_value (V.guard (BTruth false) [FTop]) = [TAny].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The constant 2 is below the top value. *)
  Example constant_below_top :
    V.leb (FVal (32%positive, 2%Z)) FTop = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The top value is not below the constant 2. *)
  Example top_not_below_constant :
    V.leb FTop (FVal (32%positive, 2%Z)) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ValueTests.

(** * Trees *)

Module TreeTests.

  (** Builds the digraph with the given vertices and edges, in their order. *)
  Definition graph_fixture (vertices : list positive) (edges : list (positive * positive)) :=
    Digraph vertices (fold_right (fun u tr =>
      PTrieCode.set u (map snd (filter (fun e => Pos.eqb (fst e) u) edges)) tr) Empty vertices).

  (** The map from each child to its parent, given as the list of pairs. *)
  Definition parents (pairs : list (positive * positive)) :=
    fold_right (fun p m => PTrieCode.set (fst p) (snd p) m) Empty pairs.

  (** The dominator tree of the diamond is accepted by the tree checker. *)
  Example supplied_diamond_tree_accepted :
    DomCode.check (DigraphCode.prepare (graph_fixture [1; 2; 3; 4]%positive
      [(1, 2); (1, 3); (2, 4); (3, 4)]%positive)) 1%positive
      (parents [(2, 1); (3, 1); (4, 1)]%positive) [1; 2; 4; 3]%positive = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The dominator tree of the triangle is accepted by the tree checker. *)
  Example supplied_triangle_tree_accepted :
    DomCode.check (DigraphCode.prepare (graph_fixture [1; 2; 3]%positive
      [(1, 2); (1, 3); (2, 3)]%positive)) 1%positive
      (parents [(2, 1); (3, 1)]%positive) [1; 2; 3]%positive = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The tree of a repeated edge is accepted by the tree checker. *)
  Example repeated_edge_tree_accepted :
    DomCode.check (DigraphCode.prepare (graph_fixture [1; 2]%positive
      [(1, 2); (1, 2)]%positive)) 1%positive (parents [(2, 1)]%positive) [1; 2]%positive = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End TreeTests.

(** * Identity *)

Module IdentityTests.

  (** A language whose single operation is the identity on words. *)
  Module IdentityLang <: LANG_OPS.
    Definition op := unit.
    Definition guard := unit.
    Definition val := word.
    Definition eval (_ : unit) (xs : list word) := match xs with [x] => Some x | _ => None end.
    Definition literal (_ : unit) : option Z := None.
  End IdentityLang.

  Module IdentityOp <: TYPE. Definition t := IdentityLang.op. End IdentityOp.
  Module IdentityGuard <: TYPE. Definition t := IdentityLang.guard. End IdentityGuard.

  (** A four-node graph whose entry 1 has two edges to nodes 2 and 3. *)
  Module EqualGraph <: CFG_INDEXED_OPS Prog NatKeyCode Edge.
    Definition entries (_ : nat) := [1].
    Definition edges (_ : nat) := [0; 1; 2; 3].
    Definition src (_ : nat) e := match e with 0 | 1 => 1 | 2 => 2 | _ => 3 end.
    Definition dst (_ : nat) e := match e with 0 => 2 | 1 => 3 | _ => 4 end.
    Definition nodes (_ : nat) := [1; 2; 3; 4].
    Definition out (_ : nat) n := match n with 1 => [0; 1] | 2 => [2] | 3 => [3] | _ => [] end.
    Definition inc (_ : nat) n := match n with 2 => [0] | 3 => [1] | 4 => [2; 3] | _ => [] end.
  End EqualGraph.

  (** The SSA of the equal graph: value 1 is the identity of value 0, and value 0 is a parameter. *)
  Module EqualSsa <: SSA_OPS Prog NatKeyCode Edge EqualGraph NatKeyCode IdentityOp IdentityGuard.
    Definition values (_ : nat) := [0; 1].
    Definition def (_ : nat) x : definition nat nat unit :=
      if Nat.eqb x 1 then Op tt [0] else Param 1 0.
    Definition home (_ _ : nat) := 1.
    Definition params (_ : nat) n := if Nat.eqb n 1 then [0] else [].
    Definition args (_ _ : nat) : list (nat * nat) := [].
    Definition guards (_ _ : nat) : list (unit * list nat) := [].
    Definition entry_params p := flat_map (params p) (EqualGraph.entries p).
    Definition arg_rows p := flat_map (fun e => map (pair e) (args p e)) (EqualGraph.edges p).
  End EqualSsa.

  Module EqualV := ConstCode IdentityLang WordEq.

  (** Every seed is top. *)
  Module EqualTransfer <: SSA_TRANSFER_OPS Prog NatKeyCode IdentityLang EqualV.
    Definition seed (_ _ : nat) : EqualV.t := FTop.
  End EqualTransfer.

  Module EqualS := SparseCode Prog NatKeyCode Edge EqualGraph NatKeyCode IdentityLang
    IdentityOp IdentityGuard EqualSsa EqualV EqualTransfer.
  Module EqualP := PolicyCode EqualV.
  Module EqualC := CheckCode EqualV EqualS.
  Module EqualW := WorklistCode EqualV EqualS EqualP HeapCode.
  Module EqualR := NarrowCode EqualV EqualS EqualC.
  Module EqualA := CertifiedCode EqualV EqualS EqualW EqualC EqualR.

  (** Nodes 0 and 1 of the equal system both get the top value Any. *)
  Example equal_system_gives_any :
    match EqualA.analyze 0 flat_policy 16%N with
    | Solved m => Some (map (fun x => old_value (EqualC.look m x)) [0; 1])
    | _ => None
    end = Some [Some TAny; Some TAny].
  Proof.
    vm_compute; reflexivity.
  Qed.

End IdentityTests.
