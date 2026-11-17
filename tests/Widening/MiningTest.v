(** * Threshold mining observations

    Mining collects nested literals and expands their neighbors.
    For example, literal four contributes three, four and five.
    Builds on: Mining, ZLang and Thresholds. *)

From Stdlib Require Import List ZArith NArith.
From Argent Require Import Std.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig IntervalSig ZLang Thresholds ThresholdsSig.
From Galois.Widening Require Import Mining.
Import List.ListNotations.
Local Open Scope Z_scope.

Module M := MiningCode NatKeyCode ZLangCode ThresholdsCode.
Definition nested := Node ZAdd [Node (ZConst 4) []; Node (ZConst (-2)) []; Leaf 0%nat].

Example literal_collection : M.lits nested = [4; -2].
Proof. vm_compute. reflexivity. Qed.
Example mining_neighbors :
  let t := M.mine [nested] [10] in
  (ThresholdsCode.below t 0, ThresholdsCode.above t 0,
   ThresholdsCode.below t 4, ThresholdsCode.above t 8) =
  (Some (-1), Some 3, Some 4, Some 9).
Proof. vm_compute. reflexivity. Qed.
Example empty_mining : M.mine [] [] = TLeaf.
Proof. vm_compute. reflexivity. Qed.

Module TimedMining := MiningT PosKeyT ZLangT ThresholdsT.
Definition timed_nested :=
  Node ZAdd [Node (ZConst 4) []; Node (ZConst (-2)) []; Leaf 1%positive].

(** The literal collector fits the linear bound on a nested term. *)
Example literal_collection_bigO_bound :
  (TimedMining.T_lits timed_nested <=
    TimedMining.c_mining * (N.of_nat (tsize timed_nested) + 1))%N.
Proof.
  vm_compute. discriminate.
Qed.

(** Mining fits the composed traversal, seed and threshold-construction bound. *)
Example mining_bigO_bound :
  let es := [timed_nested] in
  let extra := [10] in
  let work := (fold_right Nat.add 0%nat (map tsize es) +
    fold_right Nat.add 0%nat
      (map (fun z => (Z.size_nat z + 1)%nat) (TimedMining.seeds es extra)) +
    ((length (TimedMining.expanded es extra) *
      (Nat.log2 (length (TimedMining.expanded es extra)) + 1) + 1) *
      (ThresholdsT.zb (TimedMining.expanded es extra) + 1)))%nat in
  (TimedMining.T_mine es extra <=
    (TimedMining.c_mining * (ThresholdsT.c_thresholds + 1)) * (N.of_nat work + 1))%N.
Proof.
  vm_compute. discriminate.
Qed.
