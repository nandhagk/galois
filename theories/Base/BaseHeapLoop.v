(** * Terminal credit for binary heap loops

    Continuing steps pay for their own work and leave credit for binary descent.
    For example, a stale discard funds the next loop block without a global operation counter.
    Builds on: CostLoop. *)

From Stdlib Require Import NArith PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostLoop.
Import Cost.Notations.

Module HeapLoop.

Local Open Scope N_scope.

(** Both exhausted states and successful results retain their own potential. *)
Definition potential {S R} (Phi : S -> N) (Psi : R -> N) (r : S + R) :=
  match r with
  | inl s => Phi s
  | inr r => Psi r
  end.

Local Definition credit {S R} (I : S -> Prop) (Phi : S -> N) (Psi : R -> N)
    B d s (m : Cost.t (S + R)) : Prop :=
  match Cost.value m with
  | inl s' => I s' /\ Cost.ticks m + Phi s' + 1 <= Phi s
  | inr r => Cost.ticks m + Psi r <= B + Phi s + d
  end.

Local Lemma continue_credit {S R} (I : S -> Prop) Phi Psi B d s
    (m : Cost.t (S + R)) next :
  credit I Phi Psi B d s m ->
  (forall s', I s' -> credit I Phi Psi B d s' (next s')) ->
  credit I Phi Psi B (d + 1) s (Cost.step ;; continue_c m next).
Proof.
  intros Hm Hnext. unfold credit in *.
  autorewrite with galois_cost. rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [s'|r].
  - destruct Hm as [HI Hcost]. specialize (Hnext s' HI).
    destruct (Cost.value (next s')) as [s''|r].
    + destruct Hnext as [HI' Hcost']. split; [exact HI'|lia].
    + lia.
  - lia.
Qed.

(** Stale-step credit pays for arbitrary early termination and the returned result potential. *)
Theorem iterate_credit {S R} (step : S -> Cost.t (S + R))
    (I : S -> Prop) (Phi : S -> N) (Psi : R -> N) B :
  (forall s, I s ->
    match Cost.value (step s) with
    | inl s' => I s' /\ Cost.ticks (step s) + Phi s' + 2 <= Phi s
    | inr r => Cost.ticks (step s) + Psi r <= B + Phi s
    end) ->
  forall fuel s, I s ->
  Cost.ticks (iterate step fuel s) +
    potential Phi Psi (Cost.value (iterate step fuel s)) <=
    B + Phi s + N.pos (Pos.size fuel).
Proof.
  intros Hstep.
  assert (Hcredit : forall fuel s, I s ->
    credit I Phi Psi B (N.pos (Pos.size fuel)) s (iterate step fuel s)).
  { intro fuel. induction fuel as [p IH|p IH|]; intros s HI.
    - pose proof (Hstep s HI) as Hlocal.
      cbn [iterate]. unfold credit at 1.
      autorewrite with galois_cost. rewrite value_continue_c, ticks_continue_c.
      autorewrite with galois_cost.
      destruct (Cost.value (step s)) as [s'|r].
      + destruct Hlocal as [HI' Hcost].
        pose proof (continue_credit I Phi Psi B (N.pos (Pos.size p)) s'
          (iterate step p s') (iterate step p) (IH s' HI') IH) as Hblocks.
        unfold credit in Hblocks. autorewrite with galois_cost in Hblocks.
        destruct (Cost.value (continue_c (iterate step p s') (iterate step p))) as [s''|r].
        * destruct Hblocks as [HI'' Hbound]. split; [exact HI''|lia].
        * change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))). lia.
      + change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))). lia.
    - change (credit I Phi Psi B (N.succ (N.pos (Pos.size p))) s
        (Cost.step ;; continue_c (iterate step p s) (iterate step p))).
      replace (N.succ (N.pos (Pos.size p))) with (N.pos (Pos.size p) + 1) by lia.
      apply continue_credit; [apply IH; exact HI|exact IH].
    - pose proof (Hstep s HI) as Hlocal.
      cbn [iterate]. unfold credit at 1. autorewrite with galois_cost.
      destruct (Cost.value (step s)) as [s'|r].
      + destruct Hlocal as [HI' Hcost]. split; [exact HI'|lia].
      + change (N.pos (Pos.size xH)) with 1. lia. }
  intros fuel s HI. specialize (Hcredit fuel s HI).
  unfold credit in Hcredit.
  destruct (Cost.value (iterate step fuel s)); cbn [potential] in *.
  - destruct Hcredit as [_ Hcost]. lia.
  - exact Hcredit.
Qed.

(** Natural and binary logarithms agree after conversion, including at zero. *)
Theorem log2_nat_N n : N.of_nat (Nat.log2 n) = N.log2 (N.of_nat n).
Proof.
  destruct n as [|n]; [reflexivity|].
  pose proof (Nat.log2_spec (S n) ltac:(lia)) as [Hlower Hupper].
  assert (HlowerN : N.of_nat (2 ^ Nat.log2 (S n)) <= N.of_nat (S n)) by lia.
  assert (HupperN : N.of_nat (S n) < N.of_nat (2 ^ S (Nat.log2 (S n)))) by lia.
  rewrite Nat2N.inj_pow in HlowerN.
  rewrite Nat2N.inj_pow, !Nat2N.inj_succ in HupperN.
  symmetry. apply N.log2_unique; [lia|]. split; [exact HlowerN|].
  rewrite Nat2N.inj_succ. exact HupperN.
Qed.

End HeapLoop.
