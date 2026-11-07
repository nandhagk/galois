(** * Automation for cost contracts

    These tactics normalize projections and combine proved cost bounds.
    For example, [cost_simpl] turns a bind's tick count into addition.
    Builds on: CostList, CostLoop and CostBound. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.

Create HintDb galois_bigO.

(** Discharge binary arithmetic side conditions while bound search can still use their rule. *)
#[export] Hint Extern 4 (_ <= _)%N => lia : galois_bigO.

(** Normalize registered result and tick equations, leaving arithmetic for the caller. *)
Ltac cost_simpl :=
  repeat progress (autorewrite with galois_cost; cbn beta iota zeta).

(** Search six bound-composition layers with arithmetic, then try arithmetic on residual goals. *)
Ltac bigO_solver :=
  eauto 6 using bigO_refl, bigO_trans, bigO_le, bigO_mono, bigO_add,
    bigO_scale, bigO_mul, bigO_comp with galois_bigO;
  try lia.

(** Apply the strict-decrease loop bound, leaving its step contract and initial invariant. *)
Ltac iterate_invariant I Phi k :=
  eapply (iterate_cost _ I Phi k).
