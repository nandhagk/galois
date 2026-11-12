(** * Threshold mining observations

    Mining collects nested literals and expands their neighbors.
    For example, literal four contributes three, four and five.
    Builds on: Mining, ZLang and Thresholds. *)

From Stdlib Require Import List ZArith.
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
