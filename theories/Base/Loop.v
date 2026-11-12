(** * Binary-fuel loops

    This driver runs a callback with a binary counter and reports fuel exhaustion explicitly.
    For example, zero fuel returns the initial state without calling the callback.
    Builds on: Stdlib accessibility and binary arithmetic, and Argent loops and time derivation. *)

From Stdlib Require Import NArith Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std Loop.

(** Continuing states decrease the binary fuel component. *)
Definition loopN_lt {S : Type} (a b : N * S) : Prop := (fst a < fst b)%N.

(** A positive counter pays one unit of fuel before the next callback. *)
Definition loopN_step {S R : Type} (step : S -> S + R) (fs : N * S) :
    {fs1 : N * S | loopN_lt fs1 fs} + (S + R) :=
  match fs as fs0 return {fs1 : N * S | loopN_lt fs1 fs0} + (S + R) with
  | (N0, s) => inr (inl s)
  | (N.pos p, s) =>
    match step s with
    | inl s1 =>
      inl (exist _ (N.pred (N.pos p), s1)
        (N.lt_pred_l (N.pos p)
          (fun Hzero => eq_ind (N.pos p)
            (fun n => match n with N0 => False | N.pos _ => True end) I N0 Hzero)))
    | inr r => inr (inr r)
    end
  end.

TimeFun loopN_step.

(** Binary fuel bounds the number of callback calls without constructing unary fuel. *)
Definition loopN {S R : Type} (step : S -> S + R) (fuel : N) (s : S) : S + R :=
  loop loopN_lt (loopN_step step) (fuel, s)
    (Acc_intro_generator 32
      (wf_inverse_image (N * S) N N.lt fst N.lt_wf_0) (fuel, s)).

TimeFun loopN.

Definition c_loopN : N := 1. (* STUB *)

(** A decreasing state potential guarantees completion with sufficient fuel. *)
Lemma loopN_done : forall S R (step : S -> S + R) (Inv : S -> Prop) (Phi : S -> nat)
    fuel s,
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ Phi s1 < Phi s) ->
  Inv s -> (N.of_nat (Phi s) < fuel)%N -> exists r, loopN step fuel s = inr r.
Proof. Admitted. (* STUB *)

(** State potential pays callback work and amortised decrements after the first borrow. *)
Lemma T_loopN_le : forall S R (step : S -> S + R) T_step Inv Phi Tstop fuel s,
  ((forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  Inv s -> T_loopN step T_step fuel s <=
    c_loopN * (Phi s + Tstop + N.of_nat (N.size_nat fuel) + 1))%N.
Proof. Admitted. (* STUB *)

(** The loop spends input credit once and keeps credit in its returned result. *)
Lemma T_loopN_amort : forall S R (step : S -> S + R) T_step (Inv : S -> Prop)
    (Phi : S -> N) (Psi : R -> N) fuel s,
  ((forall s s1, Inv s -> step s = inl s1 ->
     Inv s1 /\ T_step s + c_loopN + Phi s1 <= Phi s) ->
  (forall s r, Inv s -> step s = inr r ->
     T_step s + c_loopN + Psi r <= Phi s) ->
  Inv s ->
  T_loopN step T_step fuel s +
    match loopN step fuel s with inr r => Psi r | inl _ => 0 end
  <= Phi s + c_loopN * N.of_nat (N.size_nat fuel + 1))%N.
Proof. Admitted. (* STUB *)
