(** * Round-robin joining

    Each round applies the shared constraint update in list order.
    For example, a cyclic boolean system needs a propagation round and a final stable probe.
    Builds on: FixpointSolver, FixpointCheck and CostLoop. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeKit.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointCheck FixpointAnalysis FixpointSolver.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module Kleene.

Fixpoint round_c {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    cs (m : assignment X A) : Cost.t (assignment X A * bool) :=
  match cs with
  | [] => Cost.ret (m, false)
  | c :: rest =>
    Cost.step ;;
    let* first := raise_c EX L S c m in
    let* next := round_c EX L S rest (fst first) in
    Cost.ret (fst next, snd first || snd next)
  end.

Definition round {X C A} EX L (S : System.t X C A) cs m :=
  Cost.value (round_c EX L S cs m).

(** A round is a sequence of shared raises, preserving the change flag disjunction. *)
Theorem round_equation {X C A} EX L (S : System.t X C A) cs m :
  round EX L S cs m =
  match cs with
  | [] => (m, false)
  | c :: rest =>
    let first := raise_result EX L S c m in
    let next := round EX L S rest (fst first) in
    (fst next, snd first || snd next)
  end.
Proof.
  destruct cs; reflexivity.
Qed.

(** A round stops at its first stationary pass; binary fuel counts complete rounds. *)
Definition step_c {X C A} (a : Analysis.t X C A) m
    : Cost.t (assignment X A + assignment X A) :=
  let* r := round_c (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (System.constraints (Analysis.system a)) m in
  if snd r then Cost.ret (inl (fst r)) else Cost.ret (inr (fst r)).

Definition run_c {X C A} (a : Analysis.t X C A) fuel :=
  let* r := iterate (step_c a) fuel Map.empty in
  Cost.ret (match r with
    | inl m => Outcome.OutOfFuel m
    | inr m => Outcome.Solved m
    end).

(** The reference engine ignores widening requests and always performs joining rounds. *)
Definition solver {X C A} : Solver.t X C A := Solver.Make run_c.

Section RoundLaws.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).

Local Lemma raise_wf c m :
  Map.wf EX m -> Map.wf EX (fst (raise_result EX L S c m)).
Proof.
  rewrite raise_equation; apply Update.apply_wf.
Qed.

Local Lemma raise_unchanged c m :
  snd (raise_result EX L S c m) = false -> fst (raise_result EX L S c m) = m.
Proof.
  rewrite raise_equation; apply Update.apply_unchanged.
Qed.

(** Every complete round preserves map well-formedness. *)
Theorem round_wf cs m :
  Map.wf EX m -> Map.wf EX (fst (round EX L S cs m)).
Proof.
  revert m; induction cs as [|c cs IH]; intros m Hwf; rewrite round_equation.
  - exact Hwf.
  - cbn [fst]; apply IH, raise_wf, Hwf.
Qed.

Local Lemma round_unchanged cs m :
  snd (round EX L S cs m) = false -> fst (round EX L S cs m) = m.
Proof.
  revert m; induction cs as [|c cs IH]; intro m; rewrite round_equation.
  - reflexivity.
  - cbn [fst snd]; rewrite orb_false_iff; intros [Hfirst Hnext].
    rewrite (IH _ Hnext); now apply raise_unchanged.
Qed.

Local Lemma round_stationary cs m :
  snd (round EX L S cs m) = false -> forall c, In c cs ->
    forall x b, In (x, b) (fst (Eval.outputs S c (lookup EX L m))) ->
      leb L b (lookup EX L m x) = true.
Proof.
  revert m; induction cs as [|c cs IH]; intros m Hstable d Hd x b Hb.
  - contradiction.
  - rewrite round_equation in Hstable; cbn [snd] in Hstable.
    apply orb_false_iff in Hstable as [Hfirst Hnext].
    rewrite (raise_unchanged c m Hfirst) in Hnext.
    destruct Hd as [<-|Hd].
    + rewrite raise_equation in Hfirst.
      exact (Update.apply_stationary EX L (join_c L) _ m Hfirst x b Hb).
    + exact (IH m Hnext d Hd x b Hb).
Qed.

(** A stationary round satisfies all listed primary and side constraints. *)
Theorem round_sound m :
  snd (round EX L S (System.constraints S) m) = false ->
  post_solution L S (lookup EX L (fst (round EX L S (System.constraints S) m))).
Proof.
  intro Hstable; rewrite (round_unchanged _ _ Hstable).
  intros c Hc; pose proof (round_stationary _ _ Hstable c Hc) as Hbounds.
  rewrite Eval.outputs_spec in Hbounds; cbn [fst] in Hbounds.
  split.
  - apply Hbounds; now left.
  - intros x b Hb; apply Hbounds; now right.
Qed.

(** Each round is a finite path of listed raises when its input map is well formed. *)
Theorem round_reached cs m :
  incl cs (System.constraints S) -> Map.wf EX m ->
  clos_refl_trans (assignment X A) (raise EX L S) m (fst (round EX L S cs m)).
Proof.
  revert m; induction cs as [|c cs IH]; intros m Hlisted Hwf; rewrite round_equation.
  - apply rt_refl.
  - cbn [fst]; eapply rt_trans.
    + apply rt_step; split; [exact Hwf|exists c; split; [apply Hlisted; now left|reflexivity]].
    + apply IH; [intros d Hd; apply Hlisted; now right|apply raise_wf, Hwf].
Qed.

End RoundLaws.

Section SolverLaws.
Context {X C A : Type} (a : Analysis.t X C A).

Local Lemma step_result m :
  Cost.value (step_c a m) =
    if snd (round (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
      (System.constraints (Analysis.system a)) m)
    then inl (fst (round (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
      (System.constraints (Analysis.system a)) m))
    else inr (fst (round (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
      (System.constraints (Analysis.system a)) m)).
Proof.
  unfold step_c; rewrite Cost.value_bind.
  fold (round (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (System.constraints (Analysis.system a)) m).
  destruct (snd (round _ _ _ _ m)); reflexivity.
Qed.

Local Lemma runs_reached n m result :
  runs (step_c a) n m result -> Map.wf (Analysis.key_enc a) m ->
  let final := match result with inl s => s | inr s => s end in
  Map.wf (Analysis.key_enc a) final /\
    clos_refl_trans (assignment X A)
      (raise (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)) m final.
Proof.
  intro Hrun; induction Hrun as [m|n m r Hstop|n m next result Hnext Hrun IH]; intro Hwf.
  - split; [exact Hwf|apply rt_refl].
  - rewrite step_result in Hstop.
    destruct (snd (round _ _ _ _ m)); [discriminate|].
    injection Hstop as <-; split; [apply round_wf, Hwf|].
    apply round_reached; [intros c Hc; exact Hc|exact Hwf].
  - rewrite step_result in Hnext.
    destruct (snd (round _ _ _ _ m)); [|discriminate].
    injection Hnext as <-.
    destruct (IH (round_wf _ _ _ _ _ Hwf)) as [Hfinal Hpath].
    split; [exact Hfinal|]; eapply rt_trans; [|exact Hpath].
    apply round_reached; [intros c Hc; exact Hc|exact Hwf].
Qed.

Local Lemma runs_sound n m r :
  runs (step_c a) n m (inr r) ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) r).
Proof.
  intro Hrun; destruct (runs_inr_stop _ _ _ _ Hrun) as [used [last [_ [_ Hstop]]]].
  rewrite step_result in Hstop.
  destruct (snd (round _ _ _ _ last)) eqn:Hstable; [discriminate|].
  injection Hstop as <-; apply round_sound, Hstable.
Qed.

End SolverLaws.

(** The reference solver returns sound reached candidates without assuming termination. *)
Theorem kleene_solver_laws {X C A} : Solver.laws (@solver X C A).
Proof.
  constructor; intros a fuel m Hl.
  - cbn [Solver.run Solver.run_c solver run_c]; autorewrite with galois_cost.
    pose proof (iterate_value (step_c a) fuel (@Map.empty X A)) as Hrun.
    destruct (Cost.value (iterate (step_c a) fuel Map.empty)) as [pending|done] eqn:Hloop;
      cbn; intro H; rewrite Hloop in H; [discriminate|].
    injection H as <-; exact (runs_sound a _ _ _ Hrun).
  - intros Hlub Hjoining; cbn [Solver.run Solver.run_c solver run_c].
    autorewrite with galois_cost.
    pose proof (iterate_value (step_c a) fuel (@Map.empty X A)) as Hrun.
    destruct (Cost.value (iterate (step_c a) fuel Map.empty)) as [pending|done] eqn:Hloop;
      cbn; intro H; rewrite Hloop in H; [discriminate|].
    injection H as <-.
    destruct (runs_reached a _ _ _ Hrun (Map.wf_empty _)) as [_ Hpath].
    exists done; split; [exact Hpath|reflexivity].
Qed.

(** Every solved reference candidate is reached because this engine always joins from bottom. *)
Theorem kleene_reached {X C A} (a : Analysis.t X C A) fuel m :
  Solver.run solver a fuel = Outcome.Solved m ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  cbn [Solver.run Solver.run_c solver run_c]; autorewrite with galois_cost.
  pose proof (iterate_value (step_c a) fuel (@Map.empty X A)) as Hrun.
  destruct (Cost.value (iterate (step_c a) fuel Map.empty)) as [pending|done] eqn:Hloop;
    cbn; intro H; rewrite Hloop in H; [discriminate|].
  injection H as <-.
  destruct (runs_reached a _ _ _ Hrun (Map.wf_empty _)) as [_ Hpath].
  exists done; split; [exact Hpath|reflexivity].
Qed.

Fixpoint output_keys_c {X C A} (S : System.t X C A) (SS : System.static S) cs
    : Cost.t (list X) :=
  match cs with
  | [] => Cost.ret []
  | c :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* target := System.target_c S c in
    Cost.step ;;
    let* sides := System.side_targets_c SS c in
    let* tail := output_keys_c S SS rest in
    app_c (target :: sides) tail
  end.

Definition output_keys {X C A} (S : System.t X C A) SS cs :=
  Cost.value (output_keys_c S SS cs).

(** The finite rank support includes every declared output occurrence. *)
Theorem output_keys_spec {X C A} (S : System.t X C A) SS cs :
  output_keys S SS cs = flat_map (fun c => System.target S c :: side_targets SS c) cs.
Proof.
  induction cs as [|c cs IH]; [reflexivity|].
  unfold output_keys in *; cbn [output_keys_c flat_map]; autorewrite with galois_cost.
  rewrite ?value_app_c, IH; reflexivity.
Qed.

Section Adequacy.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a).

Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let U := output_keys S (Analysis.static a) (System.constraints S).
Let R := Terminates.hgt HT.

Definition good (m : assignment X A) :=
  Map.wf EX m /\ forall x, Terminates.inv HT (lookup EX L m x).

Definition rank_sum (m : assignment X A) :=
  msum U (fun x => rank R (lookup EX L m x)).

Local Lemma lookup_set m x b y :
  Map.wf EX m ->
  lookup EX L (Map.set EX x b m) y = if eqb EX y x then b else lookup EX L m y.
Proof.
  intro Hwf; rewrite !lookup_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x); reflexivity.
Qed.

Local Lemma good_empty : good Map.empty.
Proof.
  split; [apply Map.wf_empty|].
  intro x; rewrite lookup_empty; apply Terminates.inv_bot.
Qed.

Local Lemma rank_sum_monotone m n :
  good m -> good n -> fun_leb L (lookup EX L m) (lookup EX L n) ->
  rank_sum m <= rank_sum n.
Proof.
  intros [_ Hm] [_ Hn] Hle; apply msum_bounded.
  intros x Hx; apply (rank_monotone R); [apply Hm|apply Hn|apply Hle].
Qed.

Local Lemma rank_sum_bound m : good m -> rank_sum m <= length U * bound R.
Proof.
  intros [_ Hm]; unfold rank_sum.
  rewrite <- msum_constant; apply msum_bounded.
  intros x Hx; apply (rank_bounded R), Hm.
Qed.

Local Lemma rule_good m x b :
  good m -> Terminates.inv HT b ->
  good (fst (Update.rule EX L (join_c L) m x b)).
Proof.
  intros [Hwf Hinv] Hb; split; [apply Update.rule_wf, Hwf|].
  intro y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
  destruct (leb L b (lookup EX L m x)); [apply Hinv|].
  destruct (eqb EX y x); [|apply Hinv].
  rewrite <- join_equation; apply Terminates.inv_join; [apply Hinv|exact Hb].
Qed.

Local Lemma rule_ascending m x b :
  Map.wf EX m ->
  fun_leb L (lookup EX L m) (lookup EX L (fst (Update.rule EX L (join_c L) m x b))).
Proof.
  intro Hwf; intro y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
  destruct (leb L b (lookup EX L m x)); [apply (leb_refl (Analysis.lattice_law HL))|].
  destruct (eqb EX y x) eqn:Hy; [|apply (leb_refl (Analysis.lattice_law HL))].
  apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hy; subst y.
  rewrite <- join_equation; apply (join_upper_l (Analysis.lattice_law HL)).
Qed.

Local Lemma rule_rank_grows m x b :
  good m -> Terminates.inv HT b -> In x U ->
  snd (Update.rule EX L (join_c L) m x b) = true ->
  rank_sum m < rank_sum (fst (Update.rule EX L (join_c L) m x b)).
Proof.
  intros Hgood Hb Hx Hchanged.
  pose proof (rule_good m x b Hgood Hb) as Hnext.
  pose proof (rule_ascending m x b (proj1 Hgood)) as Hascending.
  unfold rank_sum; apply msum_grows.
  - intros y Hy; apply (rank_monotone R).
    + apply (proj2 Hgood).
    + apply (proj2 Hnext).
    + apply Hascending.
  - exists x; split; [exact Hx|].
    rewrite Update.rule_equation in Hchanged |- *.
    destruct (leb L b (lookup EX L m x)) eqn:Hbelow; [discriminate|].
    cbn [fst]; rewrite lookup_set by exact (proj1 Hgood); rewrite eqb_refl.
    rewrite <- join_equation.
    apply (join_rank_grows R); [apply (proj2 Hgood)|exact Hb|].
    destruct (leb L (join L (lookup EX L m x) b) (lookup EX L m x)) eqn:Hjoin;
      [|exact Hjoin].
    pose proof (leb_trans (Analysis.lattice_law HL) _ _ _
      (join_upper_r (Analysis.lattice_law HL) _ _) Hjoin) as Hbad.
    change (leb L b (lookup EX L m x) = true) in Hbad.
    rewrite Hbelow in Hbad; discriminate.
Qed.

Local Lemma apply_good outs m :
  good m -> (forall x b, In (x, b) outs -> Terminates.inv HT b) ->
  good (fst (Update.apply EX L (join_c L) outs m)).
Proof.
  revert m; induction outs as [|[x b] outs IH]; intros m Hgood Houts;
    rewrite Update.apply_equation; [exact Hgood|].
  cbn [fst]; apply IH.
  - apply rule_good; [exact Hgood|exact (Houts x b (or_introl eq_refl))].
  - intros y d Hin; exact (Houts y d (or_intror Hin)).
Qed.

Local Lemma apply_ascending outs m :
  Map.wf EX m ->
  fun_leb L (lookup EX L m) (lookup EX L (fst (Update.apply EX L (join_c L) outs m))).
Proof.
  revert m; induction outs as [|[x b] outs IH]; intros m Hwf;
    rewrite Update.apply_equation; cbn [fst].
  - intro y; apply (leb_refl (Analysis.lattice_law HL)).
  - intro y; eapply (leb_trans (Analysis.lattice_law HL)).
    + apply rule_ascending, Hwf.
    + apply IH, Update.rule_wf, Hwf.
Qed.

Local Lemma apply_rank_grows outs m :
  good m -> (forall x b, In (x, b) outs -> Terminates.inv HT b /\ In x U) ->
  snd (Update.apply EX L (join_c L) outs m) = true ->
  rank_sum m < rank_sum (fst (Update.apply EX L (join_c L) outs m)).
Proof.
  revert m; induction outs as [|[x b] outs IH]; intros m Hgood Houts;
    rewrite Update.apply_equation; [discriminate|].
  cbn [snd fst]; rewrite orb_true_iff; intro Hchanged.
  destruct (Houts x b (or_introl eq_refl)) as [Hb Hx].
  pose proof (rule_good m x b Hgood Hb) as Hfirst.
  assert (Htail : forall y d, In (y, d) outs -> Terminates.inv HT d /\ In y U).
  { intros y d Hin; apply Houts; now right. }
  pose proof (apply_good outs _ Hfirst (fun y d Hin => proj1 (Htail y d Hin))) as Hfinal.
  pose proof (rank_sum_monotone _ _ Hgood Hfirst
    (rule_ascending m x b (proj1 Hgood))) as Hle1.
  pose proof (rank_sum_monotone _ _ Hfirst Hfinal
    (apply_ascending outs _ (proj1 Hfirst))) as Hle2.
  destruct Hchanged as [Hchanged|Hchanged].
  - pose proof (rule_rank_grows m x b Hgood Hb Hx Hchanged); lia.
  - pose proof (IH _ Hfirst Htail Hchanged); lia.
Qed.

Local Lemma outputs_invariant m c :
  good m -> In c (System.constraints S) ->
  forall x b, In (x, b) (fst (Eval.outputs S c (lookup EX L m))) ->
    Terminates.inv HT b /\ In x U.
Proof.
  intros [_ Hinv] Hc x b Hb; split.
  - exact (Terminates.inv_closed HT _ Hinv c Hc (x, b) Hb).
  - unfold U; rewrite output_keys_spec, in_flat_map.
    exists c; split; [exact Hc|].
    rewrite Eval.outputs_spec in Hb; cbn [fst] in Hb.
    destruct Hb as [Heq|Hb]; [injection Heq as <- <-; now left|].
    right; apply (System.sides_within (Analysis.static_law HL) c (lookup EX L m)).
    apply in_map_iff; exists (x, b); now split.
Qed.

Local Lemma raise_good m c :
  good m -> In c (System.constraints S) -> good (fst (raise_result EX L S c m)).
Proof.
  intros Hgood Hc; rewrite raise_equation; apply apply_good; [exact Hgood|].
  intros x b Hb; exact (proj1 (outputs_invariant m c Hgood Hc x b Hb)).
Qed.

Local Lemma round_good cs m :
  incl cs (System.constraints S) -> good m -> good (fst (round EX L S cs m)).
Proof.
  revert m; induction cs as [|c cs IH]; intros m Hlisted Hgood; rewrite round_equation.
  - exact Hgood.
  - cbn [fst]; apply IH.
    + intros d Hd; apply Hlisted; now right.
    + apply raise_good; [exact Hgood|apply Hlisted; now left].
Qed.

Local Lemma round_ascending cs m :
  Map.wf EX m ->
  fun_leb L (lookup EX L m) (lookup EX L (fst (round EX L S cs m))).
Proof.
  revert m; induction cs as [|c cs IH]; intros m Hwf; rewrite round_equation; cbn [fst].
  - intro x; apply (leb_refl (Analysis.lattice_law HL)).
  - intro x; eapply (leb_trans (Analysis.lattice_law HL)) with
      (b := lookup EX L (fst (raise_result EX L S c m)) x).
    + rewrite raise_equation; apply apply_ascending, Hwf.
    + apply IH, raise_wf, Hwf.
Qed.

Local Lemma round_rank_grows cs m :
  incl cs (System.constraints S) -> good m -> snd (round EX L S cs m) = true ->
  rank_sum m < rank_sum (fst (round EX L S cs m)).
Proof.
  revert m; induction cs as [|c cs IH]; intros m Hlisted Hgood;
    rewrite round_equation; [discriminate|].
  cbn [snd fst]; rewrite orb_true_iff; intro Hchanged.
  assert (Hc : In c (System.constraints S)) by (apply Hlisted; now left).
  assert (Htail : incl cs (System.constraints S)).
  { intros d Hd; apply Hlisted; now right. }
  pose proof (raise_good m c Hgood Hc) as Hfirst.
  pose proof (round_good cs _ Htail Hfirst) as Hfinal.
  assert (Hle1 : rank_sum m <= rank_sum (fst (raise_result EX L S c m))).
  { apply rank_sum_monotone; [exact Hgood|exact Hfirst|].
    rewrite raise_equation; apply apply_ascending, (proj1 Hgood). }
  pose proof (rank_sum_monotone _ _ Hfirst Hfinal
    (round_ascending cs _ (proj1 Hfirst))) as Hle2.
  destruct Hchanged as [Hchanged|Hchanged].
  - rewrite raise_equation in Hchanged |- *.
    pose proof (apply_rank_grows _ m Hgood (outputs_invariant m c Hgood Hc) Hchanged).
    rewrite raise_equation in Hle2; lia.
  - pose proof (IH _ Htail Hfirst Hchanged); lia.
Qed.

Local Lemma runs_exhaustion n m last :
  runs (step_c a) n m (inl last) -> good m ->
  good last /\ rank_sum m + n <= rank_sum last.
Proof.
  intro Hrun; remember (inl last) as result eqn:Hresult.
  induction Hrun as [m|n m r Hstop|n m next result Hnext Hrun IH]; intro Hgood.
  - injection Hresult as <-; split; [exact Hgood|lia].
  - discriminate.
  - rewrite step_result in Hnext.
    fold EX L S in Hnext.
    destruct (snd (round EX L S (System.constraints S) m)) eqn:Hchanged;
      [|discriminate].
    injection Hnext as <-.
    pose proof (round_good (System.constraints S) m (fun c Hc => Hc) Hgood) as Hnext.
    destruct (IH Hresult Hnext) as [Hlast Hrank].
    split; [exact Hlast|].
    pose proof (round_rank_grows _ m (fun c Hc => Hc) Hgood Hchanged); lia.
Qed.

(** More rounds than total rank capacity force a stationary, solved round. *)
Theorem kleene_fuel_adequate fuel :
  length U * bound R < Pos.to_nat fuel ->
  exists m, Solver.run solver a fuel = Outcome.Solved m.
Proof.
  intro Hfuel; pose proof (iterate_value (step_c a) fuel (@Map.empty X A)) as Hrun.
  cbn [Solver.run Solver.run_c solver run_c]; autorewrite with galois_cost.
  destruct (Cost.value (iterate (step_c a) fuel Map.empty)) as [last|done] eqn:Hloop.
  - destruct (runs_exhaustion _ _ _ Hrun good_empty) as [Hlast Hrank].
    pose proof (rank_sum_bound last Hlast); lia.
  - exists done; cbn; rewrite Hloop; reflexivity.
Qed.

End Adequacy.

(** A uniform charged-round bound gives a fuel-linear bound without termination assumptions. *)
Theorem kleene_cost {X C A} (a : Analysis.t X C A) fuel k :
  (forall m, (Cost.ticks (step_c a m) <= k)%N) ->
  (Cost.ticks (run_c a fuel) <= (k + 2) * N.pos fuel)%N.
Proof.
  intro Hround.
  assert (Hstep : forall m, True ->
    (match Cost.value (step_c a m) with inl _ => True | inr _ => True end) /\
    (Cost.ticks (step_c a m) +
      result_potential (fun _ => 0%N) (Cost.value (step_c a m)) <= k + 0)%N).
  { intros m _; destruct (Cost.value (step_c a m)); split; try exact I;
      cbn [result_potential]; specialize (Hround m); lia. }
  pose proof (iterate_cost_amortised (step_c a) (fun _ => True) (fun _ => 0%N)
    k Hstep fuel Map.empty I) as [_ Hcost].
  unfold run_c; rewrite Cost.ticks_bind.
  rewrite Cost.ticks_ret, N.add_0_r.
  destruct (Cost.value (iterate (step_c a) fuel Map.empty));
    cbn [result_potential] in Hcost; lia.
Qed.

Arguments round_c {X C A} EX L S cs m : simpl never.
Arguments round {X C A} EX L S cs m : simpl never.
Arguments run_c {X C A} a fuel : simpl never.
Arguments solver {X C A} : simpl never.

End Kleene.
Import Kleene.
