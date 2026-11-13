(** * Binary-fuel loops

    This driver runs a callback with a binary counter and reports fuel exhaustion explicitly.
    For example, zero fuel returns the initial state without calling the callback.
    Builds on: Stdlib accessibility and binary arithmetic, and Argent loops and time derivation. *)

From Stdlib Require Import NArith Lia Wellfounded.Inverse_Image.
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

Definition c_loopN : N := 8.

(** Proof-only fuel credit counts every zero bit in the binary representation. *)
Fixpoint loopN_zero_bits_pos (p : positive) : N :=
  match p with
  | xI q => loopN_zero_bits_pos q
  | xO q => (1 + loopN_zero_bits_pos q)%N
  | xH => 0%N
  end.

Definition loopN_zero_bits (n : N) : N :=
  match n with
  | N0 => 0%N
  | N.pos p => loopN_zero_bits_pos p
  end.

Lemma loopN_pred_double_credit (p : positive) :
  (Pos.T_pred_double p + loopN_zero_bits_pos (Pos.pred_double p) <=
    loopN_zero_bits_pos p + 2)%N.
Proof.
  induction p as [p IH | p IH |]; time_unfold Pos.T_pred_double;
    cbn [Pos.pred_double loopN_zero_bits_pos] in *; lia.
Qed.

Lemma loopN_pred_credit (n : N) :
  (N.T_pred n + loopN_zero_bits (N.pred n) <= loopN_zero_bits n + 3)%N.
Proof.
  destruct n as [| p].
  - time_unfold N.T_pred. cbn [N.pred loopN_zero_bits]. lia.
  - destruct p as [p | p |]; time_unfold N.T_pred; time_unfold Pos.T_pred_N;
      cbn [N.pred Pos.pred_N loopN_zero_bits loopN_zero_bits_pos];
      try pose proof (loopN_pred_double_credit p); lia.
Qed.

Lemma loopN_zero_bits_pos_le_size (p : positive) :
  (loopN_zero_bits_pos p <= N.of_nat (Pos.size_nat p))%N.
Proof.
  induction p as [p IH | p IH |]; cbn [loopN_zero_bits_pos Pos.size_nat];
    rewrite ?Nat2N.inj_succ; lia.
Qed.

Lemma loopN_zero_bits_le_size (n : N) :
  (loopN_zero_bits n <= N.of_nat (N.size_nat n))%N.
Proof.
  destruct n as [| p]; cbn [loopN_zero_bits N.size_nat].
  - lia.
  - apply loopN_zero_bits_pos_le_size.
Qed.

(** Completion holds for every accessibility proof used by the binary-fuel driver. *)
Local Lemma loopN_done_acc {S R} (step : S -> S + R) (Inv : S -> Prop) (Phi : S -> nat)
    (Hstep : forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ Phi s1 < Phi s) :
  forall fs (H : Acc loopN_lt fs), Inv (snd fs) ->
    (N.of_nat (Phi (snd fs)) < fst fs)%N ->
    exists r, loop loopN_lt (loopN_step step) fs H = inr r.
Proof.
  intros fs H. induction H as [[fuel s] Hacc IH] using Acc_ind_dep.
  cbn [fst snd]. intros Hinv Hfuel. destruct fuel as [|p]; [lia|].
  cbn [loop loopN_step Acc_inv]. destruct (step s) as [s1|r] eqn:Hnext.
  - destruct (Hstep s s1 Hinv Hnext) as [Hinv1 Hphi].
    eapply IH; [exact Hinv1|]. cbn [fst snd]. lia.
  - exists r. reflexivity.
Qed.

(** A decreasing state potential guarantees completion with sufficient fuel. *)
Lemma loopN_done : forall S R (step : S -> S + R) (Inv : S -> Prop) (Phi : S -> nat)
    fuel s,
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ Phi s1 < Phi s) ->
  Inv s -> (N.of_nat (Phi s) < fuel)%N -> exists r, loopN step fuel s = inr r.
Proof.
  intros S R step Inv Phi fuel s Hstep Hinv Hfuel.
  unfold loopN. apply (loopN_done_acc step Inv Phi Hstep (fuel, s)); assumption.
Qed.

(** State potential pays callback work and amortised decrements after the first borrow. *)
Lemma T_loopN_le : forall S R (step : S -> S + R) T_step Inv Phi Tstop fuel s,
  ((forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  Inv s -> T_loopN step T_step fuel s <=
    c_loopN * (Phi s + Tstop + N.of_nat (N.size_nat fuel) + 1))%N.
Proof.
  intros S R step T_step Inv Phi Tstop fuel s Hgo Hstop Hinv.
  assert (Hbound : forall (fs : N * S) (Hacc : Acc loopN_lt fs),
    Inv (snd fs) ->
    (T_loop loopN_lt (loopN_step step) (fun fs => T_loopN_step step T_step fs) fs Hacc <=
      (8 * Phi (snd fs) + loopN_zero_bits (fst fs)) + (Tstop + 1) + 1)%N).
  { apply T_loop_le.
    - intros [n s0] [n1 s1] Hlt Hinv0 Hstep.
      destruct n as [| p].
      + discriminate Hstep.
      + cbn [loopN_step] in Hstep.
        destruct (step s0) as [s2 | r] eqn:E; [| discriminate].
        inversion Hstep; subst n1 s1.
        destruct (Hgo s0 s2 Hinv0 E) as [Hinv2 Hdec].
        split; [exact Hinv2 |].
        pose proof (loopN_pred_credit (N.pos p)) as Hcredit.
        cbn [N.pred] in Hcredit.
        time_unfold @T_loopN_step. cbn [fst snd]. rewrite E. lia.
    - intros [n s0] r Hinv0 Hstep.
      destruct n as [| p].
      + time_unfold @T_loopN_step. lia.
      + cbn [loopN_step] in Hstep.
        destruct (step s0) as [s1 | r0] eqn:E; [discriminate |].
        specialize (Hstop s0 r0 Hinv0 E).
        time_unfold @T_loopN_step. rewrite E. lia. }
  time_unfold @T_loopN.
  match goal with
  | |- context [T_loop _ _ _ _ ?Hacc] =>
      pose proof (Hbound (fuel, s) Hacc Hinv) as Hloop
  end.
  pose proof (loopN_zero_bits_le_size fuel) as Hsize.
  cbn [fst snd] in Hloop. unfold c_loopN. lia.
Qed.

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
