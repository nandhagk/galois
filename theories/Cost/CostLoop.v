(** * Binary-fuel loops

    A loop returns a continuation state on exhaustion and a result on early stopping.
    For example, fuel one invokes its callback once.
    Builds on: CostMonad and Stdlib well-founded recursion. *)

From Stdlib Require Import NArith PArith Lia List Init.Wf Arith.Wf_nat.
From Galois.Cost Require Import CostMonad.
Import Cost.Notations.

Open Scope N_scope.

(** A run uses its entire budget unless its callback returns a stopping result. *)
Inductive runs {S R} (step : S -> Cost.t (S + R)) : nat -> S -> S + R -> Prop :=
  | runs_zero s : runs step O s (inl s)
  | runs_stop n s r : Cost.value (step s) = inr r -> runs step (Datatypes.S n) s (inr r)
  | runs_next n s s' result :
      Cost.value (step s) = inl s' ->
      runs step n s' result -> runs step (Datatypes.S n) s result.

(** Continuing an exhausted block runs the next block; a stopped block propagates its result. *)
Definition continue_c {S R} (m : Cost.t (S + R)) (next : S -> Cost.t (S + R))
    : Cost.t (S + R) :=
  let* result := m in
  match result with
  | inl s => next s
  | inr r => Cost.ret (inr r)
  end.

(** Binary blocks charge their descent, and each callback invocation charges one extra tick. *)
Fixpoint iterate {S R} (step : S -> Cost.t (S + R)) (fuel : positive) (s : S)
    : Cost.t (S + R) :=
  match fuel with
  | xH => Cost.step ;; step s
  | xO p =>
    Cost.step ;;
    continue_c (iterate step p s) (iterate step p)
  | xI p =>
    Cost.step ;;
    continue_c (Cost.step ;; step s)
      (fun s' => continue_c (iterate step p s') (iterate step p))
  end.

(** One public unfolding layer exposes the same costed binary blocks and selected continuations. *)
Theorem iterate_equation {S R} (step : S -> Cost.t (S + R)) fuel s :
  iterate step fuel s =
  match fuel with
  | xH => Cost.step ;; step s
  | xO p =>
    Cost.step ;; continue_c (iterate step p s) (iterate step p)
  | xI p =>
    Cost.step ;; continue_c (Cost.step ;; step s)
      (fun next => continue_c (iterate step p next) (iterate step p))
  end.
Proof.
  destruct fuel; reflexivity.
Qed.

(** Sequential run budgets add when the first block continues. *)
Theorem runs_append {S R} (step : S -> Cost.t (S + R)) n m s result :
  runs step n s result ->
  forall final,
    (match result with inl s' => runs step m s' final | inr r => final = inr r end) ->
    runs step (n + m) s final.
Proof.
  intro Hrun. induction Hrun as [s |n s r Hstop |n s s' result Hnext Hrun IH];
    intros final Hfinal; cbn in *.
  - exact Hfinal.
  - subst final. apply runs_stop, Hstop.
  - eapply runs_next; [exact Hnext | apply IH, Hfinal].
Qed.

(** Continuing costed blocks agrees with concatenation of their run relations. *)
Theorem continue_runs {S R} (step : S -> Cost.t (S + R)) n m s
    (a : Cost.t (S + R)) (b : S -> Cost.t (S + R)) :
  runs step n s (Cost.value a) ->
  (forall s', runs step m s' (Cost.value (b s'))) ->
  runs step (n + m) s (Cost.value (continue_c a b)).
Proof.
  intros Ha Hb. unfold continue_c. rewrite Cost.value_bind.
  eapply runs_append; [exact Ha |].
  destruct (Cost.value a) as [s'|r]; [apply Hb | reflexivity].
Qed.

(** The binary driver performs at most the numeric fuel's number of callback steps. *)
Theorem iterate_value {S R} (step : S -> Cost.t (S + R)) fuel s :
  runs step (Pos.to_nat fuel) s (Cost.value (iterate step fuel s)).
Proof.
  revert s. induction fuel as [p IH |p IH |]; intro s; cbn [iterate];
    autorewrite with galois_cost.
  - rewrite Pos2Nat.inj_xI.
    replace (Datatypes.S (2 * Pos.to_nat p)) with
      (1 + (Pos.to_nat p + Pos.to_nat p))%nat by lia.
    apply continue_runs.
    + autorewrite with galois_cost. destruct (Cost.value (step s)) as [s'|r] eqn:Hstep.
      * eapply runs_next; [exact Hstep | apply runs_zero].
      * apply runs_stop, Hstep.
    + intro s'. apply continue_runs; apply IH.
  - rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by lia.
    apply continue_runs; apply IH.
  - destruct (Cost.value (step s)) as [s'|r] eqn:Hstep.
    + eapply runs_next; [exact Hstep | apply runs_zero].
    + apply runs_stop, Hstep.
Qed.

(** Exhaustion witnesses exactly as many continuation transitions as the supplied budget. *)
Theorem runs_inl_exact {S R} (step : S -> Cost.t (S + R)) n s s' :
  runs step n s (inl s') ->
  exists states, length states = n /\
    (fix follows (xs : list S) (s : S) : Prop :=
      match xs with
      | nil => s = s'
      | cons next rest => Cost.value (step s) = inl next /\ follows rest next
      end) states s.
Proof.
  intro Hrun. remember (inl s') as result eqn:Hresult.
  induction Hrun as [s |n s r Hstop |n s next result Hnext Hrun IH].
  - inversion Hresult; subst. exists nil. split; reflexivity.
  - discriminate Hresult.
  - destruct (IH Hresult) as [states [Hlength Hfollows]].
    exists (cons next states). cbn. split; [congruence | auto].
Qed.

(** An inl result of the driver certifies exhaustion of all callback fuel. *)
Theorem iterate_inl_runs_out {S R} (step : S -> Cost.t (S + R)) fuel s s' :
  Cost.value (iterate step fuel s) = inl s' ->
  exists states, length states = Pos.to_nat fuel /\
    (fix follows (xs : list S) (s : S) : Prop :=
      match xs with
      | nil => s = s'
      | cons next rest => Cost.value (step s) = inl next /\ follows rest next
      end) states s.
Proof.
  intro Hresult. apply runs_inl_exact.
  rewrite <- Hresult. apply iterate_value.
Qed.

(** A stopping run reaches an actual stopping callback within its budget. *)
Theorem runs_inr_stop {S R} (step : S -> Cost.t (S + R)) n s r :
  runs step n s (inr r) ->
  exists used last, (used < n)%nat /\
    runs step used s (inl last) /\ Cost.value (step last) = inr r.
Proof.
  intro Hrun. remember (inr r) as result eqn:Hresult.
  induction Hrun as [s |n s r' Hstop |n s next result Hnext Hrun IH].
  - discriminate Hresult.
  - inversion Hresult; subst. exists O, s. split; [lia |].
    split; [apply runs_zero | exact Hstop].
  - destruct (IH Hresult) as [used [last [Hused [Hprefix Hstop]]]].
    exists (Datatypes.S used), last. split; [lia |].
    split; [eapply runs_next; eassumption | exact Hstop].
Qed.

(** An inr result witnesses a callback returning that result before the fuel is exhausted. *)
Theorem iterate_inr_stops {S R} (step : S -> Cost.t (S + R)) fuel s r :
  Cost.value (iterate step fuel s) = inr r ->
  exists used last, (used < Pos.to_nat fuel)%nat /\
    runs step used s (inl last) /\ Cost.value (step last) = inr r.
Proof.
  intro Hresult. apply runs_inr_stop.
  rewrite <- Hresult. apply iterate_value.
Qed.

(** Continuation exposes the reached callback value without inspecting its cost. *)
Theorem value_continue_c {S R} (m : Cost.t (S + R)) next :
  Cost.value (continue_c m next) =
    match Cost.value m with
    | inl s => Cost.value (next s)
    | inr r => inr r
    end.
Proof.
  unfold continue_c. rewrite Cost.value_bind.
  destruct (Cost.value m); reflexivity.
Qed.

(** Continuation charges its first block and only the reached second block. *)
Theorem ticks_continue_c {S R} (m : Cost.t (S + R)) next :
  Cost.ticks (continue_c m next) =
    Cost.ticks m +
    match Cost.value m with
    | inl s => Cost.ticks (next s)
    | inr _ => 0
    end.
Proof.
  unfold continue_c. rewrite Cost.ticks_bind.
  destruct (Cost.value m); reflexivity.
Qed.

(** Two blocks spend their intermediate potential and leave a spare descent tick. *)
Local Lemma continue_credit {S R} (I : S -> Prop) (Phi : S -> N) K d s
    (m : Cost.t (S + R)) next :
  (match Cost.value m with
   | inl s' => I s' /\ Cost.ticks m + K * Phi s' + 1 <= K * Phi s
   | inr _ => Cost.ticks m <= K * (Phi s + 1) + d
   end) ->
  (forall s', I s' ->
   match Cost.value (next s') with
   | inl s'' => I s'' /\ Cost.ticks (next s') + K * Phi s'' + 1 <= K * Phi s'
   | inr _ => Cost.ticks (next s') <= K * (Phi s' + 1) + d
   end) ->
  match Cost.value (continue_c m next) with
  | inl s' => I s' /\ 1 + Cost.ticks (continue_c m next) + K * Phi s' + 1 <= K * Phi s
  | inr _ => 1 + Cost.ticks (continue_c m next) <= K * (Phi s + 1) + (d + 1)
  end.
Proof.
  intros Hm Hnext. rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [s'|r].
  - destruct Hm as [HI Hcost]. specialize (Hnext s' HI).
    destruct (Cost.value (next s')) as [s''|r].
    + destruct Hnext as [HI' Hcost']. split; [exact HI' | nia].
    + nia.
  - nia.
Qed.

(** Exhausted blocks refund all final potential; stopped blocks pay only binary descent overhead. *)
Theorem iterate_credit {S R} (step : S -> Cost.t (S + R))
    (I : S -> Prop) (Phi : S -> N) k :
  (forall s, I s -> Cost.ticks (step s) <= k /\
    match Cost.value (step s) with
    | inl s' => I s' /\ Phi s' < Phi s
    | inr _ => True
    end) ->
  forall fuel s, I s ->
  match Cost.value (iterate step fuel s) with
  | inl s' =>
    I s' /\ Cost.ticks (iterate step fuel s) + (k + 2) * Phi s' + 1 <= (k + 2) * Phi s
  | inr _ =>
    Cost.ticks (iterate step fuel s) <= (k + 2) * (Phi s + 1) + N.pos (Pos.size fuel)
  end.
Proof.
  intros Hstep fuel. induction fuel as [p IH |p IH |]; intros s HI.
  - destruct (Hstep s HI) as [Hcost Hnext].
    cbn [iterate]. autorewrite with galois_cost.
    rewrite value_continue_c, ticks_continue_c.
    autorewrite with galois_cost.
    destruct (Cost.value (step s)) as [s'|r].
    + destruct Hnext as [HI' Hdecrease].
      pose proof (continue_credit I Phi (k + 2) (N.pos (Pos.size p)) s'
        (iterate step p s') (iterate step p) (IH s' HI') IH) as Hblocks.
      destruct (Cost.value (continue_c (iterate step p s') (iterate step p))) as [s''|r].
      * destruct Hblocks as [HI'' Hblocks]. split; [exact HI'' | nia].
      * change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))).
        nia.
    + change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))).
      nia.
  - pose proof (continue_credit I Phi (k + 2) (N.pos (Pos.size p)) s
      (iterate step p s) (iterate step p) (IH s HI) IH) as Hblocks.
    cbn [iterate]. autorewrite with galois_cost.
    change (N.pos (Pos.size (xO p))) with (N.succ (N.pos (Pos.size p))).
    destruct (Cost.value (continue_c (iterate step p s) (iterate step p))) as [s'|r].
    + exact Hblocks.
    + nia.
  - destruct (Hstep s HI) as [Hcost Hnext].
    cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (step s)) as [s'|r].
    + destruct Hnext as [HI' Hdecrease]. split; [exact HI' | nia].
    + cbn [Pos.size]. nia.
Qed.

(** A strictly decreasing potential bounds callback work independently of unused fuel. *)
Theorem iterate_cost {S R} (step : S -> Cost.t (S + R))
    (I : S -> Prop) (Phi : S -> N) k fuel s :
  (forall s, I s -> Cost.ticks (step s) <= k /\
    match Cost.value (step s) with
    | inl s' => I s' /\ Phi s' < Phi s
    | inr _ => True
    end) ->
  I s ->
  Cost.ticks (iterate step fuel s) <=
    (k + 2) * (Phi s + 1) + 2 * N.pos (Pos.size fuel).
Proof.
  intros Hstep HI. pose proof (iterate_credit step I Phi k Hstep fuel s HI) as Hcredit.
  destruct (Cost.value (iterate step fuel s)) as [s'|r].
  - destruct Hcredit as [_ Hcost]. nia.
  - nia.
Qed.

(** A stopped loop has no residual state potential. *)
Definition result_potential {S R} (Phi : S -> N) (result : S + R) : N :=
  match result with
  | inl s => Phi s
  | inr _ => 0
  end.

(** A zero state potential leaves no residual credit for either loop outcome. *)
Theorem result_potential_zero {S R} (result : S + R) :
  result_potential (fun _ => 0) result = 0.
Proof.
  destruct result; reflexivity.
Qed.

(** Composition adds budgets and retains two units of credit before charging descent. *)
Local Lemma continue_budget {S R} (I : S -> Prop) (Phi : S -> N) c d s
    (m : Cost.t (S + R)) next :
  1 <= d ->
  (match Cost.value m with inl s' => I s' | inr _ => True end) ->
  Cost.ticks m + result_potential Phi (Cost.value m) + 1 <= c + Phi s ->
  (forall s', I s' ->
    (match Cost.value (next s') with inl s'' => I s'' | inr _ => True end) /\
    Cost.ticks (next s') + result_potential Phi (Cost.value (next s')) + 1 <= d + Phi s') ->
  (match Cost.value (continue_c m next) with inl s' => I s' | inr _ => True end) /\
  Cost.ticks (continue_c m next) +
    result_potential Phi (Cost.value (continue_c m next)) + 2 <= c + d + Phi s.
Proof.
  intros Hd HI Hm Hnext. rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [s'|r]; cbn [result_potential] in *.
  - destruct (Hnext s' HI) as [HI' Hcost]. split; [exact HI' | nia].
  - split; [constructor | nia].
Qed.

(** Amortised callback credits give a fuel-linear bound and refund the final state potential. *)
Theorem iterate_cost_amortised {S R} (step : S -> Cost.t (S + R))
    (I : S -> Prop) (Phi : S -> N) k :
  (forall s, I s ->
    (match Cost.value (step s) with inl s' => I s' | inr _ => True end) /\
    Cost.ticks (step s) + result_potential Phi (Cost.value (step s)) <= k + Phi s) ->
  forall fuel s, I s ->
  (match Cost.value (iterate step fuel s) with inl s' => I s' | inr _ => True end) /\
  Cost.ticks (iterate step fuel s) +
    result_potential Phi (Cost.value (iterate step fuel s)) + 1 <=
      (k + 2) * N.pos fuel + Phi s.
Proof.
  intros Hstep fuel. induction fuel as [p IH |p IH |]; intros s HI.
  - destruct (Hstep s HI) as [Hnext Hcost].
    cbn [iterate]. autorewrite with galois_cost.
    rewrite value_continue_c, ticks_continue_c. autorewrite with galois_cost.
    destruct (Cost.value (step s)) as [s'|r].
    + destruct (continue_budget I Phi ((k + 2) * N.pos p) ((k + 2) * N.pos p)
        s' (iterate step p s') (iterate step p) ltac:(nia)
        (proj1 (IH s' Hnext)) (proj2 (IH s' Hnext)) IH) as [HI' Hblocks].
      split; [exact HI' |].
      change (N.pos (xI p)) with (1 + 2 * N.pos p).
      cbn [result_potential] in Hcost. nia.
    + cbn [result_potential] in *. split; [constructor |].
      change (N.pos (xI p)) with (1 + 2 * N.pos p). nia.
  - destruct (continue_budget I Phi ((k + 2) * N.pos p) ((k + 2) * N.pos p)
      s (iterate step p s) (iterate step p) ltac:(nia)
      (proj1 (IH s HI)) (proj2 (IH s HI)) IH) as [HI' Hblocks].
    cbn [iterate]. autorewrite with galois_cost. split; [exact HI' |].
    change (N.pos (xO p)) with (2 * N.pos p). nia.
  - destruct (Hstep s HI) as [Hnext Hcost].
    cbn [iterate]. autorewrite with galois_cost. split; [exact Hnext |].
    change (N.pos xH) with 1. nia.
Qed.

Local Definition terminal_credit {S R} (I : S -> Prop) (Phi : S -> N) (Psi : R -> N)
    B d s (m : Cost.t (S + R)) : Prop :=
  match Cost.value m with
  | inl s' => I s' /\ Cost.ticks m + Phi s' + 1 <= Phi s
  | inr r => Cost.ticks m + Psi r <= B + Phi s + d
  end.

Local Lemma continue_terminal_credit {S R} (I : S -> Prop) Phi Psi B d s
    (m : Cost.t (S + R)) next :
  terminal_credit I Phi Psi B d s m ->
  (forall s', I s' -> terminal_credit I Phi Psi B d s' (next s')) ->
  terminal_credit I Phi Psi B (d + 1) s (Cost.step ;; continue_c m next).
Proof.
  intros Hm Hnext. unfold terminal_credit in *.
  autorewrite with galois_cost. rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [s'|r].
  - destruct Hm as [HI Hcost]. specialize (Hnext s' HI).
    destruct (Cost.value (next s')) as [s''|r].
    + destruct Hnext as [HI' Hcost']. split; [exact HI'|lia].
    + lia.
  - lia.
Qed.

(** Continuing credit pays for binary descent and stopping retains the result's own potential. *)
Theorem iterate_terminal_credit {S R} (step : S -> Cost.t (S + R))
    (I : S -> Prop) (Phi : S -> N) (Psi : R -> N) B :
  (forall s, I s ->
    match Cost.value (step s) with
    | inl s' => I s' /\ Cost.ticks (step s) + Phi s' + 2 <= Phi s
    | inr r => Cost.ticks (step s) + Psi r <= B + Phi s
    end) ->
  forall fuel s, I s ->
  Cost.ticks (iterate step fuel s) +
    (match Cost.value (iterate step fuel s) with
     | inl s' => Phi s'
     | inr r => Psi r
     end) <= B + Phi s + N.pos (Pos.size fuel).
Proof.
  intros Hstep.
  assert (Hcredit : forall fuel s, I s ->
    terminal_credit I Phi Psi B (N.pos (Pos.size fuel)) s (iterate step fuel s)).
  { intro fuel. induction fuel as [p IH|p IH|]; intros s HI.
    - pose proof (Hstep s HI) as Hlocal.
      cbn [iterate]. unfold terminal_credit at 1.
      autorewrite with galois_cost. rewrite value_continue_c, ticks_continue_c.
      autorewrite with galois_cost.
      destruct (Cost.value (step s)) as [s'|r].
      + destruct Hlocal as [HI' Hcost].
        pose proof (continue_terminal_credit I Phi Psi B (N.pos (Pos.size p)) s'
          (iterate step p s') (iterate step p) (IH s' HI') IH) as Hblocks.
        unfold terminal_credit in Hblocks. autorewrite with galois_cost in Hblocks.
        destruct (Cost.value (continue_c (iterate step p s') (iterate step p))) as [s''|r].
        * destruct Hblocks as [HI'' Hbound]. split; [exact HI''|lia].
        * change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))). lia.
      + change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))). lia.
    - change (terminal_credit I Phi Psi B (N.succ (N.pos (Pos.size p))) s
        (Cost.step ;; continue_c (iterate step p s) (iterate step p))).
      replace (N.succ (N.pos (Pos.size p))) with (N.pos (Pos.size p) + 1) by lia.
      apply continue_terminal_credit; [apply IH; exact HI|exact IH].
    - pose proof (Hstep s HI) as Hlocal.
      cbn [iterate]. unfold terminal_credit at 1. autorewrite with galois_cost.
      destruct (Cost.value (step s)) as [s'|r].
      + destruct Hlocal as [HI' Hcost]. split; [exact HI'|lia].
      + change (N.pos (Pos.size xH)) with 1. lia. }
  intros fuel s HI. specialize (Hcredit fuel s HI).
  unfold terminal_credit in Hcredit.
  destruct (Cost.value (iterate step fuel s)).
  - destruct Hcredit as [_ Hcost]. lia.
  - exact Hcredit.
Qed.

Local Lemma continue_residual_credit {A} (I : A -> Prop) (credit : A -> N) d start
    (m : Cost.t (A + A)) next :
  (match Cost.value m with
  | inl a => I a /\ Cost.ticks m + credit a + 1 <= credit start
  | inr a => I a /\ Cost.ticks m + credit a <= credit start + d
  end) ->
  (forall a, I a ->
    match Cost.value (next a) with
    | inl b => I b /\ Cost.ticks (next a) + credit b + 1 <= credit a
    | inr b => I b /\ Cost.ticks (next a) + credit b <= credit a + d
    end) ->
  match Cost.value (continue_c m next) with
  | inl a => I a /\ 1 + Cost.ticks (continue_c m next) + credit a + 1 <= credit start
  | inr a => I a /\ 1 + Cost.ticks (continue_c m next) + credit a <= credit start + d + 1
  end.
Proof.
  intros Hfirst Hnext. rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [a|a].
  - destruct Hfirst as [Ha Hfirst]. specialize (Hnext a Ha).
    destruct (Cost.value (next a)) as [b|b]; destruct Hnext as [Hb Hnext];
      split; [exact Hb|nia|exact Hb|nia].
  - destruct Hfirst as [Ha Hfirst]. split; [exact Ha|nia].
Qed.

Local Lemma continue_residual_plain_credit {A} (I : A -> Prop) (credit : A -> N) d start
    (m : Cost.t (A + A)) next :
  (match Cost.value m with
  | inl a => I a /\ Cost.ticks m + credit a + 1 <= credit start
  | inr a => I a /\ Cost.ticks m + credit a <= credit start + d
  end) ->
  (forall a, I a ->
    match Cost.value (next a) with
    | inl b => I b /\ Cost.ticks (next a) + credit b + 1 <= credit a
    | inr b => I b /\ Cost.ticks (next a) + credit b <= credit a + d
    end) ->
  match Cost.value (continue_c m next) with
  | inl a => I a /\ Cost.ticks (continue_c m next) + credit a + 1 <= credit start
  | inr a => I a /\ Cost.ticks (continue_c m next) + credit a <= credit start + d
  end.
Proof.
  intros Hfirst Hnext.
  pose proof (continue_residual_credit I credit d start m next Hfirst Hnext) as Hcredit.
  destruct (Cost.value (continue_c m next)); destruct Hcredit; split; try assumption; nia.
Qed.

(** Both outcomes retain their invariant and credit, with an extra exhausted refund. *)
Theorem iterate_residual_credit {A} (step : A -> Cost.t (A + A)) (I : A -> Prop)
    (credit : A -> N) fuel start :
  (forall a, I a ->
    match Cost.value (step a) with
    | inl b => I b /\ Cost.ticks (step a) + credit b + 3 <= credit a
    | inr b => I b /\ Cost.ticks (step a) + credit b <= credit a + 1
    end) ->
  I start ->
  match Cost.value (iterate step fuel start) with
  | inl a => I a /\ Cost.ticks (iterate step fuel start) + credit a + 1 <= credit start
  | inr a =>
    I a /\ Cost.ticks (iterate step fuel start) + credit a <=
      credit start + (1 + N.pos (Pos.size fuel))
  end.
Proof.
  intros Hstep. revert start. induction fuel as [fuel IH|fuel IH|]; intros start HI.
  - assert (Hfirst :
      match Cost.value (Cost.step ;; step start) with
      | inl b => I b /\ Cost.ticks (Cost.step ;; step start) + credit b + 1 <= credit start
      | inr b => I b /\ Cost.ticks (Cost.step ;; step start) + credit b <=
          credit start + (1 + N.pos (Pos.size fuel))
      end).
    { specialize (Hstep start HI). autorewrite with galois_cost.
      destruct (Cost.value (step start)); destruct Hstep; split; try assumption; nia. }
    pose proof (continue_residual_credit I credit (1 + N.pos (Pos.size fuel)) start
      (Cost.step ;; step start)
      (fun a => continue_c (iterate step fuel a) (iterate step fuel)) Hfirst
      (fun a Ha => continue_residual_plain_credit I credit (1 + N.pos (Pos.size fuel)) a
        (iterate step fuel a) (iterate step fuel) (IH a Ha) IH))
      as Hcredit.
    cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (continue_c (Cost.step ;; step start)
      (fun a => continue_c (iterate step fuel a) (iterate step fuel))));
      destruct Hcredit; split; try assumption;
      change (N.pos (Pos.size (xI fuel))) with (N.succ (N.pos (Pos.size fuel))); nia.
  - pose proof (continue_residual_credit I credit (1 + N.pos (Pos.size fuel)) start
      (iterate step fuel start) (iterate step fuel) (IH start HI) IH) as Hcredit.
    cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (continue_c (iterate step fuel start) (iterate step fuel)));
      destruct Hcredit; split; try assumption;
      change (N.pos (Pos.size (xO fuel))) with (N.succ (N.pos (Pos.size fuel))); nia.
  - specialize (Hstep start HI). cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (step start)); destruct Hstep; split; try assumption;
      cbn [Pos.size].
    all: nia.
Qed.

(** Well-founded recursion runs the functional without charging its proof arguments. *)
Definition fix_wf {A B : Type} (measure : A -> nat)
    (F : forall x, (forall y, (measure y < measure x)%nat -> Cost.t B) -> Cost.t B)
    : A -> Cost.t B :=
  Fix (well_founded_ltof A measure) (fun _ => Cost.t B) F.

(** Extensional functionals unfold the well-founded wrapper by one recursive layer. *)
Theorem fix_wf_unfold {A B} (measure : A -> nat)
    (F : forall x, (forall y, (measure y < measure x)%nat -> Cost.t B) -> Cost.t B) :
  (forall x f g, (forall y H, f y H = g y H) -> F x f = F x g) ->
  forall x, fix_wf measure F x = F x (fun y _ => fix_wf measure F y).
Proof.
  intro Hext. apply Fix_eq. exact Hext.
Qed.

(** A functional's local cost rule lifts to every input by strict measure induction. *)
Theorem fix_wf_cost {A B} (measure : A -> nat)
    (F : forall x, (forall y, (measure y < measure x)%nat -> Cost.t B) -> Cost.t B)
    (bound : A -> N) :
  (forall x f g, (forall y H, f y H = g y H) -> F x f = F x g) ->
  (forall x rec,
    (forall y H, Cost.ticks (rec y H) <= bound y) -> Cost.ticks (F x rec) <= bound x) ->
  forall x, Cost.ticks (fix_wf measure F x) <= bound x.
Proof.
  intros Hext Hcost. apply (well_founded_induction (well_founded_ltof A measure)).
  intros x IH. rewrite fix_wf_unfold; [|exact Hext].
  apply Hcost. intros y Hlt. apply IH, Hlt.
Qed.
