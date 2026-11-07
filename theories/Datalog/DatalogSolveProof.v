(** * Reference-program exactness and fuel adequacy

    Completed strata preserve the declarative model and a uniform finite capacity bounds fuel.
    For example, fact-only programs need a propagation round and a stationary probe.
    Builds on: DatalogSolve and DatalogExact. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointAnalysis FixpointAnalyze
  FixpointCertified FixpointSolver FixpointKleene.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel DatalogRelation
  DatalogCompile DatalogCompileProof DatalogExact DatalogSolve.
Import List.ListNotations.

Section Program.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) (HE : encoding_laws (penc prog)).

Lemma store_wf ps s db : Map.wf (penc prog) db ->
  Map.wf (penc prog) (store_relations prog ps s db).
Proof.
  rewrite store_relations_equation; intro Hdb; induction ps as [|p ps IH];
    cbn [fold_right]; [exact Hdb | apply Map.wf_set, IH].
Qed.

Lemma store_member ps s db p : Map.wf (penc prog) db -> In p ps ->
  rel_of prog (store_relations prog ps s db) p = Cost.value (s p).
Proof.
  intro Hwf; induction ps as [|q ps IH]; intro Hin; [contradiction |].
  rewrite store_relations_equation; cbn [fold_right].
  rewrite <- (store_relations_equation prog ps s db).
  change (lookup (penc prog) relation_lattice
    (Map.set (penc prog) q (Cost.value (s q))
      (store_relations prog ps s db)) p = Cost.value (s p)).
  rewrite lookup_equation, Map.get_set by (apply store_wf, Hwf).
  destruct (eqb (penc prog) p q) eqn:Heq.
  - apply (eqb_true_iff _ HE) in Heq; subst q; reflexivity.
  - change (rel_of prog (store_relations prog ps s db) p = Cost.value (s p)).
    apply IH; destruct Hin as [Heq' | Hin]; [subst q; rewrite eqb_refl in Heq; discriminate |].
    exact Hin.
Qed.

Lemma store_absent ps s db p : Map.wf (penc prog) db -> ~ In p ps ->
  rel_of prog (store_relations prog ps s db) p = rel_of prog db p.
Proof.
  intro Hwf; induction ps as [|q ps IH]; intro Hout; [reflexivity |].
  rewrite store_relations_equation; cbn [fold_right].
  rewrite <- (store_relations_equation prog ps s db).
  change (lookup (penc prog) relation_lattice
    (Map.set (penc prog) q (Cost.value (s q))
      (store_relations prog ps s db)) p = rel_of prog db p).
  rewrite lookup_equation, Map.get_set by (apply store_wf, Hwf).
  assert (Heq : eqb (penc prog) p q = false).
  { apply (eqb_false_iff _ HE); intro Heq; subst q; apply Hout; now left. }
  rewrite Heq.
  change (rel_of prog (store_relations prog ps s db) p = rel_of prog db p).
  apply IH; intro Hin; apply Hout; now right.
Qed.

Lemma target_level k p : In p (stratum_targets prog facts st k) -> level st p = k.
Proof.
  rewrite stratum_targets_equation, in_map_iff.
  intros [[i h | q] [Heq Hc]]; cbn [Constraint.target] in Heq; subst p.
  - destruct (rule_constraint_view prog facts st k i h Hc) as [r [_ [_ [Hl _]]]].
    exact Hl.
  - apply (fact_constraint_level prog facts st k q), Hc.
Qed.

Lemma derives_target k f :
  derives prog facts st k (model_below prog facts st k) f ->
  In (fst f) (stratum_targets prog facts st k).
Proof.
  rewrite stratum_targets_equation.
  intro Hderive; destruct Hderive as [f Hfact Hl | r sigma Hr Hl Hlow Hsame Hneg].
  - destruct f as [p ts]; apply in_map_iff; exists (Constraint.FromFact p); split;
      [reflexivity | apply (fact_constraint_member prog facts st k p ts); assumption].
  - destruct (rule_constraint_member prog facts st k r Hr Hl) as [i [Hc _]].
    apply in_map_iff; exists (Constraint.FromRule i (pred (head r))); auto.
Qed.

Lemma solved_stratum_least k lower fuel m :
  program_wf prog facts -> stratified prog st ->
  solve_stratum prog facts st lower k fuel = Outcome.Solved m ->
  least_solution relation_lattice (stratum_system prog facts st lower k)
    (rel_of prog m).
Proof.
  intros Hwf Hst Hsolve; rewrite solve_stratum_equation in Hsolve.
  destruct (analyze (stratum_analysis prog facts st lower k) fuel)
    as [cert | have | why] eqn:Hcert; try discriminate.
  pose proof (analyze_least (stratum_analysis prog facts st lower k) fuel cert
    (stratum_analysis_laws prog facts st lower k HE) relation_lub_laws
    (stratum_system_monotone prog facts st lower k HE Hwf Hst)
    (fun _ => eq_refl) eq_refl Hcert) as Hleast.
  pose proof (Kleene.kleene_reached
    (stratum_analysis prog facts st lower k) fuel m Hsolve) as Hreached.
  pose proof (Solver.solved_sound Kleene.kleene_solver_laws
    (stratum_analysis prog facts st lower k) fuel m
    (stratum_analysis_laws prog facts st lower k HE) Hsolve) as Hpost.
  split; [exact Hpost |].
  intros u Hu p.
  eapply (leb_trans relation_laws).
  - exact (reached_below (penc prog) HE relation_lattice
      (stratum_system prog facts st lower k) (rel_of prog m) (proj1_sig cert)
      relation_laws relation_lub_laws
      (stratum_system_monotone prog facts st lower k HE Hwf Hst)
      Hreached (proj1 Hleast) p).
  - exact (proj2 Hleast u Hu p).
Qed.

Lemma solve_levels_exact fuel n db :
  program_wf prog facts -> stratified prog st ->
  solve_levels prog facts st fuel n = Outcome.Solved db ->
  Map.wf (penc prog) db /\ represents (rel_of prog db) (model_below prog facts st n).
Proof.
  intros Hwf Hst; revert db; induction n as [|k IH]; intros db Hsolve;
    rewrite solve_levels_equation in Hsolve.
  - injection Hsolve as <-; split; [apply Map.wf_empty |].
    intros p ts; change (member ts (lookup (penc prog) relation_lattice Map.empty p) = true
      <-> False).
    rewrite lookup_empty, relation_bot; split; [discriminate | contradiction].
  - destruct (solve_levels prog facts st fuel k) as [previous | have | why] eqn:Hprevious;
      try discriminate.
    destruct (IH previous eq_refl) as [Hmap Hlower].
    destruct (solve_stratum prog facts st (rel_of_c prog previous) k fuel)
      as [current | have | why] eqn:Hcurrent; try discriminate.
    injection Hsolve as <-; split; [apply store_wf, Hmap |].
    intros p ts; destruct (in_dec (eqb_dec (penc prog) HE) p
      (stratum_targets prog facts st k)) as [Hin | Hout].
    + rewrite store_member by assumption.
      pose proof (target_level k p Hin) as Hl.
      rewrite (stratum_least_is_derives prog facts st HE k (rel_of_c prog previous)
        Hwf Hst Hlower (rel_of prog current)
        (solved_stratum_least k _ fuel current Hwf Hst Hcurrent) p ts).
      cbn [model_below]; split; [now right |].
      intros [Hbad | Hderive]; [|exact Hderive].
      pose proof (model_below_level prog facts st k (p, ts) Hbad); cbn in *; lia.
    + rewrite store_absent by assumption.
      rewrite (Hlower p ts); cbn [model_below]; split; [now left |].
      intros [Hbelow | Hderive]; [exact Hbelow |].
      exfalso; apply Hout, (derives_target k (p, ts)), Hderive.
Qed.

Lemma rule_constraints_length k start rs :
  length (rule_constraints st k start rs) <= length rs.
Proof.
  revert start; induction rs as [|r rs IH]; intro start; rewrite rule_constraints_equation;
    [reflexivity |].
  destruct (Nat.eqb (level st (pred (head r))) k); cbn [length]; specialize (IH (S start));
    lia.
Qed.

Lemma filter_length_le {A} (f : A -> bool) xs : length (filter f xs) <= length xs.
Proof.
  induction xs as [|x xs IH]; cbn [filter length]; [lia |].
  destruct (f x); cbn [length]; lia.
Qed.

Lemma constraints_length k :
  length (stratum_constraints prog facts st k) <= length (rules prog) + length facts.
Proof.
  rewrite stratum_constraints_equation, length_app, length_map.
  apply Nat.add_le_mono; [apply rule_constraints_length | apply filter_length_le].
Qed.

(** Capacity bounds all stratum rounds independently of completed lower databases. *)
Definition program_capacity :=
  (length (rules prog) + length facts) * length (universe prog facts).

Lemma stratum_solved_enough k lower fuel :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  program_capacity < Pos.to_nat fuel ->
  exists m, solve_stratum prog facts st lower k fuel = Outcome.Solved m.
Proof.
  intros Hwf Hst Hlower Hfuel.
  set (a := stratum_analysis prog facts st lower k).
  set (HL := stratum_analysis_laws prog facts st lower k HE).
  set (HT := stratum_terminates prog facts st lower k HE Hwf
    (represented_support prog facts st k lower Hwf Hst Hlower)).
  assert (Hkeys : length (Kleene.output_keys (Analysis.system a) (Analysis.static a)
    (System.constraints (Analysis.system a))) =
    length (stratum_constraints prog facts st k)).
  { rewrite Kleene.output_keys_spec.
    change (length (flat_map (fun c => [Constraint.target c])
      (stratum_constraints prog facts st k)) = length (stratum_constraints prog facts st k)).
    induction (stratum_constraints prog facts st k) as [|c cs IH]; cbn; lia. }
  destruct (Kleene.kleene_fuel_adequate a HL HT fuel) as [m Hrun].
  - rewrite Hkeys.
    change (length (stratum_constraints prog facts st k) * length (universe prog facts)
      < Pos.to_nat fuel).
    pose proof (constraints_length k); unfold program_capacity in Hfuel; nia.
  - destruct (analyze_with_accepts Kleene.solver a fuel m Hrun
      (Solver.solved_sound Kleene.kleene_solver_laws a fuel m HL Hrun)) as [cert Hcert].
    exists m; rewrite solve_stratum_equation.
    change (analyze a fuel = Outcome.Solved cert) in Hcert.
    fold a.
    rewrite Hcert; exact Hrun.
Qed.

Lemma solve_levels_adequate fuel n :
  program_wf prog facts -> stratified prog st -> program_capacity < Pos.to_nat fuel ->
  exists db, solve_levels prog facts st fuel n = Outcome.Solved db.
Proof.
  intros Hwf Hst Hfuel; induction n as [|k IH].
  - exists Map.empty; reflexivity.
  - destruct IH as [db Hdb].
    destruct (solve_levels_exact fuel k db Hwf Hst Hdb) as [_ Hlower].
    destruct (stratum_solved_enough k (rel_of_c prog db) fuel Hwf Hst Hlower Hfuel)
      as [m Hm].
    rewrite solve_levels_equation, Hdb, Hm; eexists; reflexivity.
Qed.

End Program.

(** Successful reference solving represents the perfect model under separate predicate-key laws. *)
Theorem solve_program_exact {P} (prog : program P) facts fuel db :
  encoding_laws (penc prog) -> program_wf prog facts ->
  solve_program prog facts fuel = Outcome.Solved db ->
  represents (rel_of prog db) (least_model prog facts).
Proof.
  intros HE Hwf Hsolve; rewrite solve_program_equation in Hsolve.
  destruct (stratify prog) as [st |] eqn:Hst; [|discriminate].
  unfold least_model; rewrite Hst; unfold perfect_model.
  exact (proj2 (solve_levels_exact prog facts st HE fuel (count st) db Hwf
    (stratify_sound prog st Hst) Hsolve)).
Qed.

(** A stratifiable well-formed program is solved at every fuel above a finite threshold. *)
Theorem solve_program_adequate {P} (prog : program P) facts :
  encoding_laws (penc prog) -> program_wf prog facts ->
  (exists st, stratified prog st) ->
  exists fuel, forall fuel', (fuel <= fuel')%positive ->
    exists db, solve_program prog facts fuel' = Outcome.Solved db.
Proof.
  intros HE Hwf Hstrat; destruct (stratify_complete prog HE Hstrat) as [st Hst].
  exists (Pos.of_succ_nat (program_capacity prog facts)).
  intros fuel Hle; rewrite solve_program_equation, Hst.
  apply (solve_levels_adequate prog facts st HE fuel (count st) Hwf
    (stratify_sound prog st Hst)).
  apply Pos2Nat.inj_le in Hle; rewrite SuccNat2Pos.id_succ in Hle; lia.
Qed.
