(** * Concrete asymptotic bounds

    These examples check sums, products and composition on nonconstant sizes.
    For example, a quadratic cost is bounded by the product size.
    Builds on: CostBound. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostBound.
Open Scope N_scope.

Example linear_bound : bigO (fun n : N => n) (fun n => 3 * n + 7).
Proof.
  exists 7. intro n. nia.
Qed.

Example quadratic_bound :
  bigO (fun n : N => n + n + n * n) (fun n => (3 * n + 7) * (3 * n + 7)).
Proof.
  apply bigO_mul; exact linear_bound.
Qed.

Example composed_bound :
  bigO (fun n : N => n * n) (fun n => 3 * (n * n) + 7).
Proof.
  exact (bigO_comp _ _ (fun n => n * n) linear_bound).
Qed.
