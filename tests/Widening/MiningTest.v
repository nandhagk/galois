(** * Threshold mining observations

    Mining collects nested literals and expands their neighbors.
    For example, literal four contributes three, four and five.
    Builds on: Mining, ZLang and Thresholds.

    Groups:
    - [LiteralTests] Collecting the literals of a term, and the linear bound on it.
    - [NeighborTests] The thresholds that mining produces around the literals.
    - [BoundTests] The time bound of mining, composed from its parts. *)

From Stdlib Require Import List ZArith NArith.
From Argent Require Import Std.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig IntervalSig ZLang Thresholds ThresholdsSig.
From Galois.Widening Require Import Mining.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** Mining over natural-number keys, the integer language and the threshold structure. *)
Module M := MiningCode NatKeyCode ZLangCode ThresholdsCode.

(** A term that adds the constant 4, the constant minus 2 and a leaf. *)
Definition nested := Node ZAdd [Node (ZConst 4) []; Node (ZConst (-2)) []; Leaf 0%nat].

(** The timed mining structure, for the time bounds. *)
Module TimedMining := MiningT PosKeyT ZLangT ThresholdsT.

(** The term of the bound, with a positive leaf. *)
Definition timed_nested :=
  Node ZAdd [Node (ZConst 4) []; Node (ZConst (-2)) []; Leaf 1%positive].

(** * Literal *)

Module LiteralTests.

  (** The literals of the nested term are 4 and -2, in order. *)
  Example collects_literals_in_order : M.lits nested = [4; -2].
  Proof. vm_compute. reflexivity. Qed.

  (** The literal collector fits the linear bound on a nested term. *)
  Example literal_collection_is_linear :
    (TimedMining.T_lits timed_nested <=
      TimedMining.c_mining * (N.of_nat (tsize timed_nested) + 1))%N.
  Proof.
    vm_compute. discriminate.
  Qed.

End LiteralTests.

(** * Neighbors *)

Module NeighborTests.

  (** The mined thresholds of the nested term and the seed 10. *)
  Definition mined := M.mine [nested] [10].

  (** The threshold below zero is -1. *)
  Example below_zero_is_minus_one : ThresholdsCode.below mined 0 = Some (-1).
  Proof. vm_compute. reflexivity. Qed.

  (** The threshold above zero is 3. *)
  Example above_zero_is_three : ThresholdsCode.above mined 0 = Some 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The threshold below four is four. *)
  Example below_four_is_four : ThresholdsCode.below mined 4 = Some 4.
  Proof. vm_compute. reflexivity. Qed.

  (** The threshold above eight is nine. *)
  Example above_eight_is_nine : ThresholdsCode.above mined 8 = Some 9.
  Proof. vm_compute. reflexivity. Qed.

  (** Mining no terms and no seeds gives the empty threshold tree. *)
  Example empty_input_mines_leaf : M.mine [] [] = TLeaf.
  Proof. vm_compute. reflexivity. Qed.

End NeighborTests.

(** * Bound *)

Module BoundTests.

  (** The terms that the bound example mines. *)
  Definition bound_terms := [timed_nested].

  (** The extra seeds that the bound example adds. *)
  Definition bound_extra : list Z := [10].

  (** The thresholds that mining expands from the terms and the extra seeds. *)
  Definition bound_expanded := TimedMining.expanded bound_terms bound_extra.

  (** The work measure of the bound, the sum of three parts. The first is the size of the terms,
      the second the bit length of the seeds, and the third the cost of building a threshold
      structure over the expanded thresholds. *)
  Definition bound_work : nat :=
    (fold_right Nat.add 0%nat (map tsize bound_terms) +
     fold_right Nat.add 0%nat
       (map (fun z => (Z.size_nat z + 1)%nat) (TimedMining.seeds bound_terms bound_extra)) +
     ((length bound_expanded * (Nat.log2 (length bound_expanded) + 1) + 1) *
      (ThresholdsT.zb bound_expanded + 1)))%nat.

  (** Mining fits the composed traversal, seed and threshold-construction bound. *)
  Example mining_bigO_bound :
    (TimedMining.T_mine bound_terms bound_extra <=
      (TimedMining.c_mining * (ThresholdsT.c_thresholds + 1)) * (N.of_nat bound_work + 1))%N.
  Proof.
    vm_compute. discriminate.
  Qed.

End BoundTests.
