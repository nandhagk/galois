(** * Exactness of compiled strata

    Post-solutions contain all declarative derivations and reached assignments contain no others.
    For example, a recursive seed is both derivable and present in every post-solution.
    Builds on: DatalogCompileProof and FixpointLeast. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointAnalysis FixpointSolver FixpointKleene.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel
  DatalogRelation DatalogFire DatalogCompile DatalogCompileProof.
Import List.ListNotations.

Section Stratum.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) (HE : encoding_laws (penc prog)).

(** Every post-solution contains the stratum's declarative closure over represented lower levels. *)
Theorem stratum_post_solution_contains k lower :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  forall s, post_solution relation_lattice (stratum_system prog facts st lower k) s ->
  forall f, derives prog facts st k (model_below prog facts st k) f ->
    member (snd f) (s (fst f)) = true.
Proof.
  intros Hwf Hst Hlower s Hpost f Hderive.
  induction Hderive as [f Hfact Hl | r sigma Hr Hl Hlow Hsame IH Hneg].
  - destruct f as [p ts]; cbn [fst snd] in *.
    pose proof (proj1 (Hpost (Constraint.FromFact p)
      (fact_constraint_member prog facts st k p ts Hfact Hl))) as Hle.
    rewrite stratum_rhs_equation in Hle.
    apply (proj1 (relation_leb _ _) Hle), (facts_at_exact prog HE), Hfact.
  - destruct (rule_constraint_member prog facts st k r Hr Hl) as [i [Hc Hi]].
    pose proof (proj1 (Hpost (Constraint.FromRule i (pred (head r))) Hc)) as Hle.
    rewrite (rule_rhs_eval prog facts st lower k s i _ r Hi) in Hle.
    apply (proj1 (relation_leb _ _) Hle).
    apply (proj2 (fire_rule_exact prog r _ (proj1 (proj1 Hwf r Hr)) _)).
    exists sigma; split; [reflexivity | split].
    + intros a Ha; pose proof (proj2 Hst r (LPos a) Hr Ha) as Hbound; cbn in Hbound.
      destruct (Nat.eq_dec (level st (pred a)) k) as [Heq | Hne].
      * rewrite rule_env_same by assumption; apply IH; assumption.
      * rewrite rule_env_lower by exact Hne; apply (proj2 (Hlower _ _)).
        apply Hlow; [exact Ha | lia].
    + intros a Ha; rewrite rule_env_lower by
        (pose proof (proj2 Hst r (LNeg a) Hr Ha); cbn in *; lia).
      change (member (map (inst sigma) (args a)) (Cost.value (lower (pred a))) = false).
      destruct (member (map (inst sigma) (args a)) (Cost.value (lower (pred a))))
        eqn:Hmem; [|reflexivity].
      exfalso; apply (Hneg a Ha), (proj1 (Hlower _ _)), Hmem.
Qed.

Definition stratum_derived k (s : P -> relation) :=
  forall p ts, member ts (s p) = true ->
    derives prog facts st k (model_below prog facts st k) (p, ts).

Lemma stratum_rhs_derives k lower s c :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  stratum_derived k s -> In c (stratum_constraints prog facts st k) ->
  forall ts, member ts
    (Query.eval (System.rhs (stratum_system prog facts st lower k) c) s) = true ->
  derives prog facts st k (model_below prog facts st k)
    (Constraint.target c, ts).
Proof.
  intros Hwf Hst Hlower Hderived Hc ts Hmem; destruct c as [i h | p].
  - destruct (rule_constraint_view prog facts st k i h Hc) as [r [Hr [Hhead [Hl Hi]]]].
    rewrite (rule_rhs_eval prog facts st lower k s i h r Hi) in Hmem.
    apply (proj1 (fire_rule_exact prog r _ (proj1 (proj1 Hwf r Hr)) ts)) in Hmem
      as [sigma [Heq [Hpos Hneg]]].
    subst h ts; change (derives prog facts st k (model_below prog facts st k)
      (ground sigma (head r))).
    apply derive_rule with (r := r) (sigma := sigma); [exact Hr | exact Hl | | |].
    + intros a Ha Hlt; apply (proj1 (Hlower _ _)).
      specialize (Hpos a Ha); rewrite rule_env_lower in Hpos by lia; exact Hpos.
    + intros a Ha Heq; apply Hderived.
      specialize (Hpos a Ha); rewrite rule_env_same in Hpos by assumption; exact Hpos.
    + intros a Ha Hbelow; apply (proj2 (Hlower _ _)) in Hbelow.
      specialize (Hneg a Ha); rewrite rule_env_lower in Hneg by
        (pose proof (proj2 Hst r (LNeg a) Hr Ha); cbn in *; lia).
      change (member (map (inst sigma) (args a)) (Cost.value (lower (pred a))) = false)
        in Hneg.
      congruence.
  - rewrite stratum_rhs_equation in Hmem; apply derive_fact.
    + apply (facts_at_exact prog HE), Hmem.
    + apply (fact_constraint_level prog facts st k p), Hc.
Qed.

Lemma stratum_update_preserved k m p v :
  Map.wf (penc prog) m -> stratum_derived k (lookup (penc prog) relation_lattice m) ->
  (forall ts, member ts v = true ->
    derives prog facts st k (model_below prog facts st k) (p, ts)) ->
  stratum_derived k (lookup (penc prog) relation_lattice
    (fst (Update.rule (penc prog) relation_lattice (join_c relation_lattice) m p v))).
Proof.
  intros Hwf Hm Hv q ts Hmem.
  rewrite (proj2 (Update.rule_spec (penc prog) relation_lattice
    (join_c relation_lattice) m p v Hwf)) in Hmem.
  destruct (leb relation_lattice v (lookup (penc prog) relation_lattice m p));
    [apply Hm, Hmem |].
  destruct (eqb (penc prog) q p) eqn:Heq; [|apply Hm, Hmem].
  apply (eqb_true_iff _ HE) in Heq; subst q.
  rewrite <- join_equation in Hmem; rewrite relation_join, orb_true_iff in Hmem.
  destruct Hmem as [Hmem | Hmem]; [apply Hm | apply Hv]; exact Hmem.
Qed.

Lemma stratum_raise_preserved k lower m n :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  stratum_derived k (lookup (penc prog) relation_lattice m) ->
  raise (penc prog) relation_lattice (stratum_system prog facts st lower k) m n ->
  stratum_derived k (lookup (penc prog) relation_lattice n).
Proof.
  intros Hwf Hst Hlower Hm [Hmap [c [Hc ->]]].
  rewrite raise_equation, Eval.outputs_spec, stratum_sides_nil; cbn [fst].
  rewrite Update.apply_equation; cbn [fst snd]; rewrite Update.apply_equation; cbn [fst].
  apply stratum_update_preserved; [exact Hmap | exact Hm |].
  intros ts Hmem; apply (stratum_rhs_derives k lower
    (lookup (penc prog) relation_lattice m) c Hwf Hst Hlower Hm Hc ts Hmem).
Qed.

(** Joining from bottom introduces only inductively derivable tuples. *)
Theorem stratum_reached_derives k lower :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  forall s, reached (penc prog) relation_lattice (stratum_system prog facts st lower k) s ->
    stratum_derived k s.
Proof.
  intros Hwf Hst Hlower s [m [Hpath Hagree]].
  assert (Hpreserve : forall m n,
    clos_refl_trans _ (raise (penc prog) relation_lattice
      (stratum_system prog facts st lower k)) m n ->
    stratum_derived k (lookup (penc prog) relation_lattice m) ->
    stratum_derived k (lookup (penc prog) relation_lattice n)).
  { intros u v Hsteps; induction Hsteps as [u v Hstep | u | u v w Huv IHuv Hvw IHvw];
      intro Hu.
    - eapply stratum_raise_preserved; eassumption.
    - exact Hu.
    - apply IHvw, IHuv, Hu. }
  intros p ts Hmem; rewrite Hagree in Hmem.
  apply (Hpreserve _ _ Hpath).
  - intros q us Hus; rewrite lookup_empty, relation_bot in Hus; discriminate.
  - exact Hmem.
Qed.

Lemma represented_support k lower :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  forall p, within_set tuple_encoding (universe prog facts) (Cost.value (lower p)).
Proof.
  intros Hwf Hst Hlower p ts Hmem.
  apply (model_constants prog facts st Hwf Hst k (p, ts)), (proj1 (Hlower p ts)), Hmem.
Qed.

Local Lemma total_stratum_reached k lower :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  exists m,
    post_solution relation_lattice (stratum_system prog facts st lower k)
      (lookup (penc prog) relation_lattice m) /\
    reached (penc prog) relation_lattice (stratum_system prog facts st lower k)
      (lookup (penc prog) relation_lattice m).
Proof.
  intros Hwf Hst Hlower.
  set (a := stratum_analysis prog facts st lower k).
  set (HL := stratum_analysis_laws prog facts st lower k HE).
  set (HT := stratum_terminates prog facts st lower k HE Hwf
    (represented_support k lower Hwf Hst Hlower)).
  set (fuel := Pos.of_succ_nat
    (length (Kleene.output_keys (Analysis.system a) (Analysis.static a)
      (System.constraints (Analysis.system a))) * bound (Terminates.hgt HT))).
  destruct (Kleene.kleene_fuel_adequate a HL HT fuel) as [m Hrun].
  - unfold fuel; rewrite SuccNat2Pos.id_succ; apply Nat.lt_succ_diag_r.
  - exists m; split.
    + exact (Solver.solved_sound Kleene.kleene_solver_laws a fuel m HL Hrun).
    + exact (Kleene.kleene_reached a fuel m Hrun).
Qed.

(** Every least compiled solution agrees with declarative derivation at every predicate. *)
Theorem stratum_least_is_derives k lower :
  program_wf prog facts -> stratified prog st ->
  represents (fun p => Cost.value (lower p)) (model_below prog facts st k) ->
  forall s, least_solution relation_lattice (stratum_system prog facts st lower k) s ->
  forall p ts, member ts (s p) = true <->
    derives prog facts st k (model_below prog facts st k) (p, ts).
Proof.
  intros Hwf Hst Hlower s Hleast.
  destruct (total_stratum_reached k lower Hwf Hst Hlower) as [m [Hpost Hreached]].
  set (reference := lookup (penc prog) relation_lattice m).
  assert (Hreference : least_solution relation_lattice
    (stratum_system prog facts st lower k) reference).
  { exact (reached_least (penc prog) HE relation_lattice
      (stratum_system prog facts st lower k) reference relation_laws relation_lub_laws
      (stratum_system_monotone prog facts st lower k HE Hwf Hst) Hreached Hpost). }
  intros p ts; split.
  - intro Hmem; apply (stratum_reached_derives k lower Hwf Hst Hlower reference).
    + exact Hreached.
    + apply (proj1 (relation_leb _ _) (proj2 Hleast reference (proj1 Hreference) p)), Hmem.
  - intro Hderive; exact (stratum_post_solution_contains k lower Hwf Hst Hlower s
      (proj1 Hleast) (p, ts) Hderive).
Qed.

End Stratum.
