(** * Charged numeric rank comparison

    Numeric comparison follows the binary digits and retains its comparison evidence.
    For example, rank two precedes rank three even though trie enumeration uses a different order.
    Builds on: CostMonad and the standard positive comparison specification. *)

From Stdlib Require Import PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad.
Import Cost.Notations.

Module DomRank.

(** The continuation records the order of the less significant digits already examined. *)
Fixpoint compare_cont_c (tail : comparison) (a b : positive) : Cost.t comparison :=
  Cost.step ;;
  match a, b with
  | xH, xH => Cost.ret tail
  | xH, _ => Cost.ret Lt
  | _, xH => Cost.ret Gt
  | xO a, xO b => compare_cont_c tail a b
  | xI a, xI b => compare_cont_c tail a b
  | xO a, xI b => compare_cont_c Lt a b
  | xI a, xO b => compare_cont_c Gt a b
  end.

(** Digit comparison agrees with the standard binary continuation comparator. *)
Theorem compare_cont_value tail a b :
  Cost.value (compare_cont_c tail a b) = Pos.compare_cont tail a b.
Proof.
  revert tail b. induction a as [a IH|a IH|]; intros tail [b|b|];
    cbn [compare_cont_c Pos.compare_cont]; autorewrite with galois_cost;
    try reflexivity; apply IH.
Qed.

Definition compare_c := compare_cont_c Eq.

(** The rank comparator uses numeric order, independently of trie-key enumeration order. *)
Theorem compare_value a b : Cost.value (compare_c a b) = Pos.compare a b.
Proof.
  apply compare_cont_value.
Qed.

(** Numeric comparison inspects at most either input's digit count. *)
Theorem compare_cont_cost tail a b :
  (Cost.ticks (compare_cont_c tail a b) <= N.pos (Pos.size a))%N /\
  (Cost.ticks (compare_cont_c tail a b) <= N.pos (Pos.size b))%N.
Proof.
  revert tail b. induction a as [a IH|a IH|]; intros tail [b|b|];
    cbn [compare_cont_c Pos.size]; autorewrite with galois_cost.
  all: try solve [pose proof (IH tail b); lia
    |pose proof (IH Gt b); lia|pose proof (IH Lt b); lia].
  all: lia.
Qed.

(** A numeric comparison charges no more than the left rank's bit width. *)
Theorem compare_cost a b :
  (Cost.ticks (compare_c a b) <= N.pos (Pos.size a))%N.
Proof.
  exact (proj1 (compare_cont_cost Eq a b)).
Qed.

(** Comparison evidence selects a constructive strict-rank decision without changing its domain. *)
Definition decision a b (result : {c : comparison | c = Pos.compare a b})
    : {Pos.to_nat a < Pos.to_nat b} + {~ Pos.to_nat a < Pos.to_nat b}.
Proof.
  destruct result as [c Hcompare]. destruct c.
  - right. symmetry in Hcompare. apply Pos.compare_eq_iff in Hcompare.
    subst b. lia.
  - left. apply Pos2Nat.inj_lt. apply Pos.compare_lt_iff. symmetry. exact Hcompare.
  - right. symmetry in Hcompare. apply Pos.compare_gt_iff in Hcompare.
    apply Pos2Nat.inj_lt in Hcompare. lia.
Defined.

(** Rank descent is decided by the charged comparator and needs no runtime unary conversion. *)
Definition smaller_c a b :=
  Cost.map (decision a b)
    (Cost.refine (compare_c a b) (compare_value a b)).

(** Rank-descent evidence retains exactly the binary comparison charge. *)
Theorem smaller_cost a b :
  (Cost.ticks (smaller_c a b) <= N.pos (Pos.size a))%N.
Proof.
  unfold smaller_c. rewrite Cost.ticks_map, Cost.ticks_refine. apply compare_cost.
Qed.

End DomRank.
