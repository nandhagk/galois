(** * Checked simultaneous narrowing

    Each pass evaluates queries against one frozen assignment and narrows their aggregate.
    For example, decreasing a read can invalidate a candidate, which the full checker discards.
    Builds on: FixpointEval, FixpointCheck, FixpointAnalysis and CostLoop. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointIndex FixpointCheck
  FixpointAnalysis FixpointSolver.
Import List.ListNotations Cost.Notations.

Module Narrow.

(** Collection joins outputs through the shared update contract against a separate aggregate. *)
Definition collect_c {X C A} (a : Analysis.t X C A) (old : assignment X A) :=
  fold_left_c (fun sums c =>
    let* r := Eval.outputs_c (Analysis.system a)
      (lookup_c (Analysis.key_enc a) (Analysis.lat a) old) c in
    Cost.map fst
      (Update.apply_c (Analysis.key_enc a) (Analysis.lat a)
        (join_c (Analysis.lat a)) (fst r) sums))
    (System.constraints (Analysis.system a)) Map.empty.

(** Declared outputs retain all occurrences until the charged distinct-set construction. *)
Definition outputs_c {X C A} (a : Analysis.t X C A) :=
  fold_right_c (fun c xs =>
    Cost.step ;;
    let* target := System.target_c (Analysis.system a) c in
    Cost.step ;;
    let* sides := System.side_targets_c (Analysis.static a) c in
    let* tail := app_c sides xs in
    Cost.ret (target :: tail)) [] (System.constraints (Analysis.system a)).

Definition outputs {X C A} (a : Analysis.t X C A) := Cost.value (outputs_c a).

(** An output reads its old value and aggregate, then invokes narrowing when the order permits. *)
Definition output_c {X A} (EX : encoding X) (L : lattice A)
    (old sums acc : assignment X A) x :=
  let* before := lookup_c EX L old x in
  let* aggregate := lookup_c EX L sums x in
  Cost.step ;;
  let* below := leb_c L aggregate before in
  let* after := if below then Cost.step ;; narrow_c L before aggregate
    else Cost.ret before in
  Map.set_c EX x after acc.

Definition output {X A} (EX : encoding X) (L : lattice A) old sums acc x :=
  Cost.value (output_c EX L old sums acc x).

(** A simultaneous pass retains unrelated stored bindings and reads only the input assignment. *)
Definition pass_c {X C A} (a : Analysis.t X C A) (old : assignment X A) :=
  let* declared := outputs_c a in
  let* keys := distinct_c (Analysis.key_enc a) declared in
  let* sums := collect_c a old in
  fold_left_c (output_c (Analysis.key_enc a) (Analysis.lat a) old sums) keys old.

Definition pass {X C A} (a : Analysis.t X C A) old := Cost.value (pass_c a old).

(** A countdown makes the binary iterator perform the requested number of simultaneous passes. *)
Definition step_c {X C A} (a : Analysis.t X C A) (s : nat * assignment X A)
    : Cost.t ((nat * assignment X A) + assignment X A) :=
  match fst s with
  | O => Cost.ret (inr (snd s))
  | S n => Cost.map (fun m => inl (n, m)) (pass_c a (snd s))
  end.

(** Fuel conversion charges each unary policy-count cell that it consumes. *)
Fixpoint fuel_c (rounds : nat) : Cost.t positive :=
  match rounds with
  | O => Cost.ret 1%positive
  | S n => Cost.step ;; Cost.map Pos.succ (fuel_c n)
  end.

(** Rounds use the common binary driver, including the terminal zero-count probe. *)
Definition rounds_c {X C A} (a : Analysis.t X C A) rounds old :=
  let* fuel := fuel_c rounds in
  let* result := iterate (step_c a) fuel (rounds, old) in
  Cost.ret (match result with inl s => snd s | inr m => m end).

Definition rounds {X C A} (a : Analysis.t X C A) n old := Cost.value (rounds_c a n old).

(** The full checker is the sole acceptance gate for a candidate. *)
Definition checked_c {X C A} (a : Analysis.t X C A) n old :=
  let* candidate := rounds_c a n old in
  let* accepted := check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) candidate) in
  Cost.ret (if accepted then candidate else old).

Definition checked {X C A} (a : Analysis.t X C A) n old :=
  Cost.value (checked_c a n old).

(** Wrapping leaves exhaustion and rejection unchanged and checks a narrowed solved candidate. *)
Definition wrap {X C A} (sv : Solver.t X C A) : Solver.t X C A :=
  Solver.Make (fun a fuel =>
    Cost.step ;;
    let* result := Solver.run_c sv a fuel in
    match result with
    | Outcome.Solved old =>
      Cost.map (@Outcome.Solved X A (assignment X A))
        (checked_c a (Policy.narrowing (Analysis.policy a)) old)
    | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
    | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
    end).

(** Output updates expose their order guard and selected stored value. *)
Theorem output_equation {X A} EX (L : lattice A) (old sums acc : assignment X A) x :
  output EX L old sums acc x =
    Map.set EX x
      (if leb L (lookup EX L sums x) (lookup EX L old x)
       then narrow L (lookup EX L old x) (lookup EX L sums x)
       else lookup EX L old x) acc.
Proof.
  unfold output, output_c; autorewrite with galois_cost.
  fold (lookup EX L old x) (lookup EX L sums x).
  fold (leb L (lookup EX L sums x) (lookup EX L old x)).
  destruct (leb L (lookup EX L sums x) (lookup EX L old x));
    autorewrite with galois_cost; rewrite ?narrow_equation; reflexivity.
Qed.

(** Each narrowed output keeps map well-formedness. *)
Theorem output_wf {X A} EX (L : lattice A) (old sums acc : assignment X A) x :
  Map.wf EX acc -> Map.wf EX (output EX L old sums acc x).
Proof.
  intro Hwf; rewrite output_equation; apply Map.wf_set, Hwf.
Qed.

(** Weak narrowing laws suffice for pointwise decrease of each output write. *)
Theorem output_below {X A} EX (HE : encoding_laws EX) (L : lattice A)
    (HL : lattice_laws L) (old sums acc : assignment X A) x :
  Map.wf EX acc -> fun_leb L (lookup EX L acc) (lookup EX L old) ->
  fun_leb L (lookup EX L (output EX L old sums acc x)) (lookup EX L old).
Proof.
  intros Hwf Hacc y; rewrite output_equation, lookup_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x) eqn:Hsame.
  - apply (eqb_true_iff EX HE) in Hsame; subst y.
    destruct (leb L (lookup EX L sums x) (lookup EX L old x)) eqn:Hle.
    + apply (narrow_lower HL), Hle.
    + apply (leb_refl HL).
  - rewrite <- lookup_equation; apply Hacc.
Qed.

(** The pass equation exposes the frozen collection and the output fold. *)
Theorem pass_equation {X C A} (a : Analysis.t X C A) old :
  pass a old =
    fold_left (output (Analysis.key_enc a) (Analysis.lat a) old
      (Cost.value (collect_c a old)))
      (distinct (Analysis.key_enc a) (outputs a)) old.
Proof.
  unfold pass, pass_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Simultaneous passes decrease pointwise and keep the assignment well formed. *)
Theorem pass_below {X C A} (a : Analysis.t X C A) old :
  encoding_laws (Analysis.key_enc a) -> lattice_laws (Analysis.lat a) ->
  Map.wf (Analysis.key_enc a) old ->
  Map.wf (Analysis.key_enc a) (pass a old) /\
  fun_leb (Analysis.lat a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (pass a old))
    (lookup (Analysis.key_enc a) (Analysis.lat a) old).
Proof.
  intros HE HL Hwf; rewrite pass_equation.
  set (sums := Cost.value (collect_c a old)).
  assert (Hfold : forall xs acc, Map.wf (Analysis.key_enc a) acc ->
    fun_leb (Analysis.lat a) (lookup (Analysis.key_enc a) (Analysis.lat a) acc)
      (lookup (Analysis.key_enc a) (Analysis.lat a) old) ->
    Map.wf (Analysis.key_enc a)
      (fold_left (output (Analysis.key_enc a) (Analysis.lat a) old sums) xs acc) /\
    fun_leb (Analysis.lat a)
      (lookup (Analysis.key_enc a) (Analysis.lat a)
        (fold_left (output (Analysis.key_enc a) (Analysis.lat a) old sums) xs acc))
      (lookup (Analysis.key_enc a) (Analysis.lat a) old)).
  { intro xs; induction xs as [|x xs IH]; intros acc Hacc Hbelow.
    - split; assumption.
    - cbn [fold_left]; apply IH.
      + apply output_wf, Hacc.
      + apply output_below; assumption. }
  apply Hfold; [exact Hwf|intro x; apply (leb_refl HL)].
Qed.

(** Policy fuel has one terminal probe in addition to the requested passes. *)
Theorem fuel_value n : Pos.to_nat (Cost.value (fuel_c n)) = S n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [fuel_c]; autorewrite with galois_cost; rewrite Pos2Nat.inj_succ; lia.
Qed.

Local Lemma countdown_runs {X C A} (a : Analysis.t X C A) n s result budget :
  runs (step_c a) budget (n, s) result -> (n < budget)%nat ->
  result = inr (Nat.iter n (pass a) s).
Proof.
  intro Hrun; remember (n, s) as start eqn:Hstart.
  revert n s Hstart; induction Hrun as
    [state|budget state m Hstep|budget state next result Hstep Hrun IH];
    intros n s Hstart Hbudget; subst state.
  - cbn in Hbudget; lia.
  - destruct n as [|n].
    + cbn [step_c fst snd] in Hstep; rewrite Cost.value_ret in Hstep.
      injection Hstep as <-; reflexivity.
    + cbn [step_c fst snd] in Hstep; rewrite Cost.value_map in Hstep; discriminate.
  - destruct n as [|n].
    + cbn [step_c fst] in Hstep; rewrite Cost.value_ret in Hstep; discriminate.
    + cbn [step_c fst snd] in Hstep; rewrite Cost.value_map in Hstep.
      injection Hstep as <-; specialize (IH n (pass a s) eq_refl ltac:(lia)).
      rewrite IH; f_equal; symmetry; apply Nat.iter_succ_r.
Qed.

(** The binary countdown returns precisely the requested number of passes. *)
Theorem rounds_equation {X C A} (a : Analysis.t X C A) n old :
  rounds a n old = Nat.iter n (pass a) old.
Proof.
  unfold rounds, rounds_c; rewrite !Cost.value_bind, Cost.value_ret.
  pose proof (iterate_value (step_c a) (Cost.value (fuel_c n)) (n, old)) as Hrun.
  rewrite (countdown_runs a n old _ _ Hrun ltac:(rewrite fuel_value; lia)).
  reflexivity.
Qed.

(** Checked narrowing either returns its candidate or retains the input assignment. *)
Theorem checked_equation {X C A} (a : Analysis.t X C A) n old :
  checked a n old =
    if check_post (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (rounds a n old))
    then rounds a n old else old.
Proof.
  unfold checked, checked_c; rewrite !Cost.value_bind.
  rewrite (check_post_c_spec _ _ _ _) by reflexivity.
  reflexivity.
Qed.

(** The full checker certifies an accepted candidate and rejection retains the input proof. *)
Theorem checked_post {X C A} (a : Analysis.t X C A) n old :
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) old) ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (checked a n old)).
Proof.
  intro Hpost; rewrite checked_equation.
  destruct (check_post _ _ _) eqn:Hcheck; [apply check_post_sound, Hcheck|exact Hpost].
Qed.

(** The wrapper exports soundness alone because narrowing need not keep joining reachability. *)
Theorem narrow_wrap_sound {X C A} (sv : Solver.t X C A) :
  (forall a fuel m, Analysis.laws a -> Solver.run sv a fuel = Outcome.Solved m ->
    post_solution (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m)) ->
  forall a fuel m, Analysis.laws a ->
    Solver.run (wrap sv) a fuel = Outcome.Solved m ->
    post_solution (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros Hsound a fuel m HL Hrun.
  unfold Solver.run, wrap in Hrun; cbn [Solver.run_c] in Hrun.
  autorewrite with galois_cost in Hrun.
  fold (Solver.run sv a fuel) in Hrun.
  destruct (Solver.run sv a fuel) as [old|have|why] eqn:Hsv;
    autorewrite with galois_cost in Hrun; try discriminate.
  injection Hrun as <-; apply checked_post; eapply Hsound; eassumption.
Qed.

Arguments pass_c {X C A} a old : simpl never.
Arguments pass {X C A} a old : simpl never.
Arguments checked_c {X C A} a n old : simpl never.
Arguments checked {X C A} a n old : simpl never.
Arguments wrap {X C A} sv : simpl never.

End Narrow.
Import Narrow.
