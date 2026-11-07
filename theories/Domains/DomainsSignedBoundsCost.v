(** * Costs of signed-bound search and lattice operations

    The bounds count the complete binary search tree and retain each reduction in a lattice call.
    For example, a join retains three half reductions for each sign.
    Builds on: DomainsSignedBounds, DomainsSignedOrder, DomainsSignedWiden and CostBound. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds DomainsSignedOrder
  DomainsSignedWiden DomainsSignedBoundsRange DomainsSignedBoundsDomain.
Import List.ListNotations Cost.Notations.

Local Open Scope N_scope.

(** Pruning can only decrease the number of nodes below the full marker-driven binary tree. *)
Theorem sb_search_cost : forall p w t lo hi,
  Cost.ticks (sb_search_c p w t lo hi) + 1 <= 2 * N.pos p.
Proof.
  intro p. induction p as [p IH|p IH|]; intros w t lo hi;
    cbn [sb_search_c]; autorewrite with galois_cost;
    destruct (tnum_empty w t); autorewrite with galois_cost; try nia;
    destruct ((tnum_max w t <? lo) || (hi <? tnum_min w t))%Z;
      autorewrite with galois_cost; try nia;
    destruct ((lo <=? tnum_min w t) && (tnum_max w t <=? hi))%Z;
      autorewrite with galois_cost; try nia.
  all: pose proof (IH w (sb_fix_bit w t (Z.log2 (Zpos p)) false) lo hi) as Hlow.
  all: pose proof (IH w (sb_fix_bit w t (Z.log2 (Zpos p)) true) lo hi) as Hhigh.
  - change (N.pos (xI p)) with (2 * N.pos p + 1). nia.
  - change (N.pos (xO p)) with (2 * N.pos p). nia.
Qed.

Definition sb_reduce_tick_bound (w : width) : N := 2 * N.pos (Z.to_pos (modulus w)).

(** Half reduction retains its invocation and the entire pruned search. *)
Theorem sb_reduce_half_cost : forall w s h,
  Cost.ticks (sb_reduce_half_c w s h) <= sb_reduce_tick_bound w.
Proof.
  intros w s [|t lo hi]; unfold sb_reduce_half_c, sb_reduce_tick_bound;
    autorewrite with galois_cost; [lia|].
  destruct (Z.min (modulus w - 1) hi <? Z.max 0 lo)%Z; autorewrite with galois_cost; [lia|].
  pose proof (sb_search_cost (Z.to_pos (modulus w)) w
    (sb_fix_bit w t (Zpos w - 1) s) (Z.max 0 lo) (Z.min (modulus w - 1) hi)). lia.
Qed.

(** Payload normalization pays both independent hemisphere reductions. *)
Theorem signed_bounds_reduce_cost : forall w a,
  Cost.ticks (signed_bounds_reduce_c w a) <= 2 * sb_reduce_tick_bound w.
Proof.
  intros w a. unfold signed_bounds_reduce_c. autorewrite with galois_cost.
  pose proof (sb_reduce_half_cost w false (sb_zero a)).
  pose proof (sb_reduce_half_cost w true (sb_one a)). nia.
Qed.

(** Half join retains both input reductions and the merged-hull reduction. *)
Theorem sb_join_cost : forall w s a b,
  Cost.ticks (sb_join_c w s a b) <= 3 * sb_reduce_tick_bound w.
Proof.
  intros w s a b. unfold sb_join_c. autorewrite with galois_cost.
  fold sb_reduce_half.
  pose proof (sb_reduce_half_cost w s a).
  pose proof (sb_reduce_half_cost w s b).
  pose proof (sb_reduce_half_cost w s
    (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b))).
  unfold sb_reduce_half in *. nia.
Qed.

(** Payload join retains all six half reductions. *)
Theorem signed_bounds_join_cost : forall w a b,
  Cost.ticks (signed_bounds_join_c w a b) <= 6 * sb_reduce_tick_bound w.
Proof.
  intros w a b. unfold signed_bounds_join_c. autorewrite with galois_cost.
  pose proof (sb_join_cost w false (sb_zero a) (sb_zero b)).
  pose proof (sb_join_cost w true (sb_one a) (sb_one b)). nia.
Qed.

(** Queries retain their exact selected-half reduction and add no hidden search. *)
Theorem signed_bounds_query_cost : forall w a s,
  Cost.ticks (signed_bounds_query_c w a s) <= sb_reduce_tick_bound w.
Proof.
  intros w a s. unfold signed_bounds_query_c. autorewrite with galois_cost.
  rewrite N.add_0_r.
  apply sb_reduce_half_cost.
Qed.

(** Each lower-threshold scan visits every supplied threshold exactly once. *)
Theorem sb_threshold_lower_cost : forall ts x best,
  Cost.ticks (sb_threshold_lower_c ts x best) = N.of_nat (length ts).
Proof.
  intro ts. induction ts as [|t rest IH]; intros x best; cbn [sb_threshold_lower_c length];
    autorewrite with galois_cost; rewrite ?IH, ?Nat2N.inj_succ; lia.
Qed.

(** Each upper-threshold scan visits every supplied threshold exactly once. *)
Theorem sb_threshold_upper_cost : forall ts x best,
  Cost.ticks (sb_threshold_upper_c ts x best) = N.of_nat (length ts).
Proof.
  intro ts. induction ts as [|t rest IH]; intros x best; cbn [sb_threshold_upper_c length];
    autorewrite with galois_cost; rewrite ?IH, ?Nat2N.inj_succ; lia.
Qed.

Lemma sb_threshold_half_cost : forall ts w s a b,
  Cost.ticks (sb_threshold_half_c ts w s a b) <= 2 * N.of_nat (length ts).
Proof.
  intros ts w s [|ta la ua] [|tb lb ub]; cbn [sb_threshold_half_c];
    autorewrite with galois_cost; try lia.
  rewrite sb_threshold_lower_cost, sb_threshold_upper_cost. nia.
Qed.

(** Actual doubling is constant-size mask and endpoint arithmetic under the word-RAM boundary. *)
Theorem sb_widen_double_cost : forall w a b,
  Cost.ticks (sb_widen_with_c WidenDouble w a b) = 1.
Proof.
  reflexivity.
Qed.

(** Every selected widening retains its complete reduction or threshold-scan budget. *)
Theorem sb_widen_with_cost : forall strategy w a b,
  Cost.ticks (sb_widen_with_c strategy w a b) <=
    match strategy with
    | WidenJoin => 6 * sb_reduce_tick_bound w
    | WidenDouble => 1
    | WidenThresholds ts => 4 * N.of_nat (length ts)
    end.
Proof.
  intros strategy w a b. destruct strategy as [| |ts].
  - apply signed_bounds_join_cost.
  - rewrite sb_widen_double_cost. lia.
  - cbn [sb_widen_with_c]. autorewrite with galois_cost.
    pose proof (sb_threshold_half_cost ts w false (sb_zero a) (sb_zero b)).
    pose proof (sb_threshold_half_cost ts w true (sb_one a) (sb_one b)). nia.
Qed.

(** Exact normalization has a full-tree exponential-width bound, independent of runtime proofs. *)
Theorem signed_bounds_reduce_bigO : forall a,
  bigO (fun w => N.pos (Z.to_pos (modulus w)))
    (fun w => Cost.ticks (signed_bounds_reduce_c w a)).
Proof.
  intro a. exists 4. intro w. pose proof (signed_bounds_reduce_cost w a).
  unfold sb_reduce_tick_bound in *. nia.
Qed.
