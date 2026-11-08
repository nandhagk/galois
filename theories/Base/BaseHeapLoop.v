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
  unfold potential. apply iterate_terminal_credit.
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
