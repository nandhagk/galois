(** * Semi-naive provenance and pivot completeness

    Reachable states contain derivations and account for every enabled valuation by a known head or pivot.
    For example, a newly satisfied nonlinear body retains one of its fresh premises in the frontier.
    Builds on: DatalogSemiNaivePivot and the compiled stratum exactness interface. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel DatalogRelation
  DatalogFire DatalogCompile DatalogCompileProof DatalogExact DatalogJoinPreparedFire DatalogSolve
  DatalogSemiNaive DatalogSemiNaiveSyntax DatalogSemiNaiveIndex DatalogSemiNaiveReady
  DatalogSemiNaivePivot.
Import List.ListNotations SemiNaive SemiNaiveSyntax SemiNaiveIndex SemiNaiveReady SemiNaivePivot.
Local Open Scope nat_scope.

Module SemiNaiveProof.

Section Correctness.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (HE : encoding_laws (penc prog)) (st : stratification P)
  (lower : P -> Cost.t relation) (k : nat).
Hypotheses (Hwf : program_wf prog facts) (Hstrat : stratified prog st)
  (Hlower : represents (fun p => Cost.value (lower p)) (model_below prog facts st k)).
Local Abbreviation E := (ground_encoding prog).
Local Abbreviation GE := (ground_encoding_laws prog HE).
Local Abbreviation env s := (current prog st k lower (accumulated_index s)).
Local Abbreviation derivation := (derives prog facts st k (model_below prog facts st k)).
Local Abbreviation batch s := (fresh prog st lower k s).
Local Abbreviation next s := (advance prog s (batch s)).

(** Provenance records actual accumulated tuples as inductive stratum derivations. *)
Definition derived (s : state P) :=
  forall f, FinSet.mem E f (accumulated s) = true -> derivation f.

(** Fact coverage persists independently of how recursive jobs are scheduled. *)
Definition facts_present (s : state P) :=
  forall f, In f facts -> level st (fst f) = k ->
    FinSet.mem E f (accumulated s) = true.

(** Each enabled source valuation is already known or owns an actual recursive frontier occurrence. *)
Definition pending (s : state P) :=
  forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
    body_holds r (env s) sigma ->
    FinSet.mem E (ground sigma (head r)) (accumulated s) = true \/
    exists i a, In (i, a) (occurrences 0 (body r)) /\ level st (pred a) = k /\
      FinSet.mem E (ground sigma a) (frontier s) = true.

(** Correctness combines maintained storage, provenance, fact coverage and pending pivot work. *)
Definition correct (s : state P) :=
  ready prog st lower k s /\ derived s /\ facts_present s /\ pending s.

Lemma current_lower db p : level st p <> k ->
  current prog st k lower db p = Cost.value (lower p).
Proof.
  intro Hne; rewrite current_equation; apply Nat.eqb_neq in Hne; rewrite Hne; reflexivity.
Qed.

Lemma negative_lower r db a : In r (rules prog) -> level st (pred (head r)) = k ->
  In (LNeg a) (body r) -> current prog st k lower db (pred a) = Cost.value (lower (pred a)).
Proof.
  intros Hr Hl Ha; apply current_lower.
  pose proof (proj2 Hstrat r (LNeg a) Hr Ha); cbn in *; lia.
Qed.

Lemma nonrecursive_absent r a : pivots st k r = [] ->
  In (LPos a) (body r) -> level st (pred a) <> k.
Proof.
  intros Hempty Ha Hl.
  destruct (proj2 (occurrences_spec 0 (body r) a) Ha) as [i Hi].
  assert (Hpivot : In i (pivots st k r)).
  { apply (pivots_from_spec st k 0 (body r) i); exists a; auto. }
  rewrite Hempty in Hpivot; contradiction.
Qed.

Lemma candidates_derived s : ready prog st lower k s -> derived s ->
  forall f, FinSet.mem E f (candidates prog st lower k s) = true -> derivation f.
Proof.
  intros Hready Hderived f Hf.
  destruct (candidates_satisfy prog HE st lower k s Hready
    (fun r Hr => proj1 (proj1 Hwf r Hr)) f Hf) as [r [sigma [Hr [Hl [-> [Hpos Hneg]]]]]].
  apply derive_rule with (r := r) (sigma := sigma); [exact Hr | exact Hl | | |].
  - intros a Ha Hlt; apply (proj1 (Hlower _ _)).
    specialize (Hpos a Ha); rewrite current_lower in Hpos by lia; exact Hpos.
  - intros a Ha Heq; apply Hderived.
    specialize (Hpos a Ha); rewrite current_equation, Heq, Nat.eqb_refl in Hpos.
    rewrite (accumulated_exact _ _ _ _ _ Hready) in Hpos; exact Hpos.
  - intros a Ha Hbelow; apply (proj2 (Hlower _ _)) in Hbelow.
    specialize (Hneg a Ha); rewrite (negative_lower r _ a Hr Hl Ha) in Hneg; congruence.
Qed.

Lemma seed_derived f : In f (seed_atoms prog facts st lower k) -> derivation f.
Proof.
  unfold seed_atoms; rewrite in_app_iff, seed_rules_equation; intros [Hfact | Hrule].
  - apply filter_In in Hfact as [Hfact Hl]; apply derive_fact; [exact Hfact | apply Nat.eqb_eq, Hl].
  - apply in_flat_map in Hrule as [r [Hr Hrow]].
    apply classify_seeds in Hr as [Hr [Hl Hnone]].
    apply in_map_iff in Hrow as [row [<- Hrow]].
    apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws) in Hrow;
      [|exact (proj2_sig (PreparedFire.fire prog r lower))].
    change (member row (PreparedFire.fire prog r lower) = true) in Hrow.
    apply (proj1 (PreparedFire.fire_exact prog r lower (proj1 (proj1 Hwf r Hr)) row))
      in Hrow as [sigma [-> [Hpos Hneg]]].
    apply derive_rule with (r := r) (sigma := sigma); [exact Hr | exact Hl | | |].
    + intros a Ha _; apply (proj1 (Hlower _ _)), Hpos, Ha.
    + intros a Ha Heq; exfalso; exact (nonrecursive_absent r a Hnone Ha Heq).
    + intros a Ha Hbelow; apply (proj2 (Hlower _ _)) in Hbelow.
      specialize (Hneg a Ha); congruence.
Qed.

Lemma initial_derived : derived (initial prog facts st lower k).
Proof.
  intros f Hf; rewrite initial_equation in Hf; cbn [accumulated] in Hf.
  apply seed_derived, (mem_of_list E GE), Hf.
Qed.

Lemma initial_facts : facts_present (initial prog facts st lower k).
Proof.
  intros f Hfact Hl; rewrite initial_equation; cbn [accumulated].
  apply (mem_of_list E GE); unfold seed_atoms; apply in_app_iff; left.
  apply filter_In; split; [exact Hfact | rewrite Hl; apply Nat.eqb_refl].
Qed.

Lemma seed_rule_member r sigma :
  In r (rules prog) -> level st (pred (head r)) = k -> pivots st k r = [] ->
  body_holds r (env (initial prog facts st lower k)) sigma ->
  In (ground sigma (head r)) (seed_atoms prog facts st lower k).
Proof.
  intros Hr Hl Hnone [Hpos Hneg]; unfold seed_atoms; apply in_app_iff; right.
  rewrite seed_rules_equation; apply in_flat_map; exists r; split.
  - apply classify_seeds; auto.
  - apply in_map_iff; exists (map (inst sigma) (args (head r))); split; [reflexivity |].
    apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws);
      [exact (proj2_sig (PreparedFire.fire prog r lower)) |].
    change (member (map (inst sigma) (args (head r))) (PreparedFire.fire prog r lower) = true).
    apply (proj2 (PreparedFire.fire_exact prog r lower (proj1 (proj1 Hwf r Hr)) _)).
    exists sigma; split; [reflexivity | split].
    + intros a Ha; specialize (Hpos a Ha).
      rewrite current_lower in Hpos by (apply (nonrecursive_absent r a Hnone Ha)); exact Hpos.
    + intros a Ha; specialize (Hneg a Ha).
      rewrite (negative_lower r _ a Hr Hl Ha) in Hneg; exact Hneg.
Qed.

Lemma initial_pending : pending (initial prog facts st lower k).
Proof.
  intros r sigma Hr Hl Hbody; destruct (pivots st k r) as [|i positions] eqn:Hp.
  - left; rewrite initial_equation; cbn [accumulated]; apply (mem_of_list E GE).
    apply (seed_rule_member r sigma Hr Hl Hp Hbody).
  - assert (Hi : In i (pivots st k r)) by (rewrite Hp; now left).
    apply (pivots_from_spec st k 0 (body r) i) in Hi as [a [Ha Halevel]].
    right; exists i, a; split; [exact Ha | split; [exact Halevel |]].
    pose proof (proj1 Hbody a (proj1 (occurrences_spec 0 (body r) a) (ex_intro _ i Ha))) as Hmem.
    rewrite current_equation, Halevel, Nat.eqb_refl in Hmem.
    rewrite (accumulated_exact _ _ _ _ _ (initial_ready prog HE facts st lower k)) in Hmem.
    rewrite initial_equation in Hmem |- *; exact Hmem.
Qed.

(** Initial facts and nonrecursive rules establish the semantic invariant for the actual loop. *)
Theorem initial_correct : correct (initial prog facts st lower k).
Proof.
  split; [apply initial_ready, HE | split; [exact initial_derived | split]].
  - exact initial_facts.
  - exact initial_pending.
Qed.

Lemma advance_environment s p row : ready prog st lower k s ->
  (member row (env (next s) p) = true <->
    member row (env s p) = true \/ FinSet.mem E (p, row) (batch s) = true).
Proof.
  intro Hready; rewrite !current_equation.
  destruct (Nat.eqb (level st p) k) eqn:Hp.
  - apply (advance_index_exact prog HE st lower k s (batch s) p row Hready).
    apply fresh_wf, (accumulated_wf _ _ _ _ _ Hready).
  - assert (Habsent : FinSet.mem E (p, row) (batch s) = false).
    { destruct (FinSet.mem E (p, row) (batch s)) eqn:Hmem; [|reflexivity].
      pose proof (fresh_level prog HE st lower k s Hready (p, row) Hmem) as Hl.
      cbn [fst] in Hl; rewrite Hl, Nat.eqb_refl in Hp; discriminate. }
    rewrite Habsent; intuition discriminate.
Qed.

Lemma candidate_inserted s f : ready prog st lower k s ->
  FinSet.mem E f (candidates prog st lower k s) = true ->
  FinSet.mem E f (accumulated (next s)) = true.
Proof.
  intros Hready Hcandidate; rewrite advance_equation; cbn [accumulated].
  rewrite FinSet.mem_union;
    [|exact (accumulated_wf _ _ _ _ _ Hready) |
      apply fresh_wf, (accumulated_wf _ _ _ _ _ Hready)].
  apply orb_true_iff; destruct (FinSet.mem E f (accumulated s)) eqn:Hold; [now left |].
  right; apply (fresh_members prog st lower k s f Hready); auto.
Qed.

Lemma advance_pending s : ready prog st lower k s -> pending s -> pending (next s).
Proof.
  intros Hready Hpending r sigma Hr Hl [Hpos Hneg].
  destruct (existsb (fun a => FinSet.mem E (ground sigma a) (batch s))
    (positive_atoms (body r))) eqn:Hnew.
  - apply existsb_exists in Hnew as [a [Ha Hmem]].
    apply positive_atoms_spec in Ha.
    destruct (proj2 (occurrences_spec 0 (body r) a) Ha) as [i Hi].
    right; exists i, a; split; [exact Hi | split].
    + exact (fresh_level prog HE st lower k s Hready (ground sigma a) Hmem).
    + rewrite advance_equation; exact Hmem.
  - assert (Hold : body_holds r (env s) sigma).
    { split.
      - intros a Ha; specialize (Hpos a Ha).
        apply (advance_environment s (pred a) _ Hready) in Hpos as [Hpos | Hfresh];
          [exact Hpos |].
        assert (Hyes : existsb (fun a => FinSet.mem E (ground sigma a) (batch s))
          (positive_atoms (body r)) = true).
        { apply existsb_exists; exists a; split; [apply positive_atoms_spec, Ha | exact Hfresh]. }
        congruence.
      - intros a Ha; specialize (Hneg a Ha).
        rewrite (negative_lower r _ a Hr Hl Ha) in Hneg.
        rewrite (negative_lower r _ a Hr Hl Ha); exact Hneg. }
    destruct (Hpending r sigma Hr Hl Hold) as [Hknown | [i [a [Ha [Halevel Hfront]]]]].
    + left; rewrite advance_equation; cbn [accumulated].
      rewrite FinSet.mem_union;
        [apply orb_true_iff; now left | exact (accumulated_wf _ _ _ _ _ Hready) |
          apply fresh_wf, (accumulated_wf _ _ _ _ _ Hready)].
    + left; apply candidate_inserted; [exact Hready |].
      exact (candidates_cover prog HE st lower k s r sigma i a Hready Hr Hl
        (proj1 (proj1 Hwf r Hr)) Ha Halevel Hold Hfront).
Qed.

Lemma advance_derived s : ready prog st lower k s -> derived s -> derived (next s).
Proof.
  intros Hready Hderived f Hf; rewrite advance_equation in Hf; cbn [accumulated] in Hf.
  rewrite FinSet.mem_union in Hf;
    [|exact (accumulated_wf _ _ _ _ _ Hready) |
      apply fresh_wf, (accumulated_wf _ _ _ _ _ Hready)].
  apply orb_true_iff in Hf as [Hf | Hf]; [apply Hderived, Hf |].
  apply (fresh_members prog st lower k s f Hready) in Hf.
  apply (candidates_derived s Hready Hderived f (proj1 Hf)).
Qed.

Lemma advance_facts s : ready prog st lower k s -> facts_present s -> facts_present (next s).
Proof.
  intros Hready Hfacts f Hf Hl; rewrite advance_equation; cbn [accumulated].
  rewrite FinSet.mem_union;
    [apply orb_true_iff; left; apply Hfacts; assumption |
      exact (accumulated_wf _ _ _ _ _ Hready) |
      apply fresh_wf, (accumulated_wf _ _ _ _ _ Hready)].
Qed.

(** Every continuing step preserves the semantic invariant using its actual frontier pivots. *)
Theorem step_correct s result :
  correct s -> step prog st lower k s = inl result -> correct result.
Proof.
  intros [Hready [Hderived [Hfacts Hpending]]] Hstep.
  pose proof (step_ready prog HE st lower k s result Hready Hstep) as Hnext.
  rewrite step_equation in Hstep; destruct (FinSet.is_empty (batch s)); [discriminate |].
  injection Hstep as <-; split; [exact Hnext | split].
  - apply advance_derived; assumption.
  - split; [apply advance_facts | apply advance_pending]; assumption.
Qed.

Lemma stopped_candidates s result :
  ready prog st lower k s -> step prog st lower k s = inr result ->
  result = s /\
    forall f, FinSet.mem E f (candidates prog st lower k s) = true ->
      FinSet.mem E f (accumulated s) = true.
Proof.
  intros Hready Hstep; rewrite step_equation in Hstep.
  destruct (FinSet.is_empty (batch s)) eqn:Hempty; [|discriminate].
  injection Hstep as <-; split; [reflexivity |].
  intros f Hcandidate; destruct (FinSet.mem E f (accumulated s)) eqn:Hknown;
    [reflexivity |].
  pose proof (proj1 (FinSet.is_empty_spec E (batch s)
    (fresh_wf prog st lower k s (accumulated_wf _ _ _ _ _ Hready))) Hempty f) as Hnone.
  assert (Hfresh : FinSet.mem E f (batch s) = true).
  { apply (fresh_members prog st lower k s f Hready); auto. }
  congruence.
Qed.

Lemma stopped_rule_closed s result r sigma :
  correct s -> step prog st lower k s = inr result ->
  In r (rules prog) -> level st (pred (head r)) = k ->
  body_holds r (env s) sigma ->
  FinSet.mem E (ground sigma (head r)) (accumulated s) = true.
Proof.
  intros [Hready [Hderived [Hfacts Hpending]]] Hstep Hr Hl Hbody.
  destruct (Hpending r sigma Hr Hl Hbody) as [Hknown | [i [a [Ha [Hlevel Hfront]]]]];
    [exact Hknown |].
  apply (proj2 (stopped_candidates s result Hready Hstep)).
  exact (candidates_cover prog HE st lower k s r sigma i a Hready Hr Hl
    (proj1 (proj1 Hwf r Hr)) Ha Hlevel Hbody Hfront).
Qed.

Lemma compiled_body s r sigma :
  In r (rules prog) -> level st (pred (head r)) = k ->
  body_holds r
    (fun p => Cost.value (rule_env prog st lower k (rel_of prog (accumulated_index s)) r p))
    sigma -> body_holds r (env s) sigma.
Proof.
  intros Hr Hl [Hpos Hneg]; split.
  - intros a Ha; specialize (Hpos a Ha); rewrite current_equation.
    destruct (Nat.eq_dec (level st (pred a)) k) as [Heq | Hne].
    + rewrite Heq, Nat.eqb_refl.
      rewrite (rule_env_same prog HE st lower k _ r a Ha Heq) in Hpos; exact Hpos.
    + apply Nat.eqb_neq in Hne as Hfalse; rewrite Hfalse.
      rewrite rule_env_lower in Hpos by exact Hne; exact Hpos.
  - intros a Ha; specialize (Hneg a Ha).
    rewrite (negative_lower r _ a Hr Hl Ha).
    rewrite rule_env_lower in Hneg by
      (pose proof (proj2 Hstrat r (LNeg a) Hr Ha); cbn in *; lia).
    exact Hneg.
Qed.

(** A stationary pivot round closes every compiled rule and fact constraint. *)
Theorem stopped_complete s result :
  correct s -> step prog st lower k s = inr result ->
  post_solution relation_lattice (stratum_system prog facts st lower k)
    (rel_of prog (accumulated_index result)).
Proof.
  intros Hcorrect Hstep.
  pose proof (proj1 Hcorrect) as Hready.
  pose proof (proj1 (stopped_candidates s result Hready Hstep)) as ->.
  intros [i h | p] Hconstraint; split.
  - destruct (rule_constraint_view prog facts st k i h Hconstraint)
      as [r [Hr [-> [Hl Hi]]]].
    rewrite (rule_rhs_eval prog facts st lower k _ i _ r Hi).
    apply relation_leb; intros row Hrow.
    apply (proj1 (fire_rule_exact prog r _ (proj1 (proj1 Hwf r Hr)) row)) in Hrow
      as [sigma [-> Hbody]].
    rewrite (accumulated_exact _ _ _ _ _ Hready).
    apply (stopped_rule_closed s s r sigma Hcorrect Hstep Hr Hl).
    apply compiled_body; [exact Hr | exact Hl | exact Hbody].
  - intros q v Hside; rewrite stratum_sides_nil in Hside; contradiction.
  - rewrite stratum_rhs_equation; apply relation_leb; intros row Hrow.
    apply (facts_at_exact prog HE) in Hrow.
    rewrite (accumulated_exact _ _ _ _ _ Hready).
    apply (proj1 (proj2 (proj2 Hcorrect)) (p, row) Hrow).
    apply (fact_constraint_level prog facts st k p), Hconstraint.
  - intros q v Hside; rewrite stratum_sides_nil in Hside; contradiction.
Qed.

Lemma runs_correct n s result :
  runs (step_c prog st lower k) n s result -> correct s ->
  match result with
  | inl interrupted => correct interrupted
  | inr stopped =>
    correct stopped /\
    post_solution relation_lattice (stratum_system prog facts st lower k)
      (rel_of prog (accumulated_index stopped))
  end.
Proof.
  intro Hrun; induction Hrun as [s | n s result Hstop | n s next result Hnext Hrun IH];
    intro Hcorrect.
  - exact Hcorrect.
  - split.
    + pose proof (proj1 (stopped_candidates s result (proj1 Hcorrect) Hstop)) as ->.
      exact Hcorrect.
    + exact (stopped_complete s result Hcorrect Hstop).
  - apply IH, (step_correct s next Hcorrect Hnext).
Qed.

(** Both actual iterator outcomes retain provenance and a stopped outcome is a post-solution. *)
Theorem run_correct fuel :
  match run prog st lower k fuel (initial prog facts st lower k) with
  | inl interrupted => correct interrupted
  | inr stopped =>
    correct stopped /\
    post_solution relation_lattice (stratum_system prog facts st lower k)
      (rel_of prog (accumulated_index stopped))
  end.
Proof.
  exact (runs_correct (Pos.to_nat fuel) (initial prog facts st lower k) _
    (iterate_value (step_c prog st lower k) fuel _) initial_correct).
Qed.

Lemma solved_state fuel db :
  stratum prog facts st lower k fuel = Outcome.Solved db ->
  exists stopped, db = accumulated_index stopped /\ correct stopped /\
    post_solution relation_lattice (stratum_system prog facts st lower k) (rel_of prog db).
Proof.
  unfold stratum, stratum_c; repeat rewrite Cost.value_bind.
  fold (@initial P prog facts st lower k).
  fold (@run P prog st lower k fuel (initial prog facts st lower k)).
  pose proof (run_correct fuel) as Hrun.
  destruct (run prog st lower k fuel (initial prog facts st lower k)) as [have | stopped];
    [discriminate |].
  intros Heq; injection Heq as <-; exists stopped; tauto.
Qed.

(** Successful stratum evaluation returns only inductive derivations over the represented lower model. *)
Theorem semi_naive_sound fuel db :
  stratum prog facts st lower k fuel = Outcome.Solved db ->
  forall p row, member row (rel_of prog db p) = true -> derivation (p, row).
Proof.
  intro Hsolve; destruct (solved_state fuel db Hsolve) as [s [-> [[Hready [Hderived _]] _]]].
  intros p row Hmem; apply Hderived.
  rewrite <- (accumulated_exact _ _ _ _ _ Hready); exact Hmem.
Qed.

(** Successful stratum evaluation satisfies the compiled system without a final-invariant premise. *)
Theorem semi_naive_complete fuel db :
  stratum prog facts st lower k fuel = Outcome.Solved db ->
  post_solution relation_lattice (stratum_system prog facts st lower k) (rel_of prog db).
Proof.
  intro Hsolve; destruct (solved_state fuel db Hsolve) as [s [_ [_ Hpost]]]; exact Hpost.
Qed.

(** Successful stratum evaluation agrees with declarative derivation at every predicate and tuple. *)
Theorem semi_naive_agrees fuel db :
  stratum prog facts st lower k fuel = Outcome.Solved db ->
  forall p row, member row (rel_of prog db p) = true <-> derivation (p, row).
Proof.
  intros Hsolve p row; split.
  - apply (semi_naive_sound fuel db Hsolve).
  - apply (stratum_post_solution_contains prog facts st HE k lower Hwf Hstrat Hlower
      (rel_of prog db) (semi_naive_complete fuel db Hsolve) (p, row)).
Qed.

(** Provenance and compiled closure make the returned assignment the least compiled post-solution. *)
Theorem semi_naive_least fuel db :
  stratum prog facts st lower k fuel = Outcome.Solved db ->
  least_solution relation_lattice (stratum_system prog facts st lower k) (rel_of prog db).
Proof.
  intro Hsolve; split; [apply (semi_naive_complete fuel db Hsolve) |].
  intros other Hpost p; apply relation_leb; intros row Hmem.
  apply (stratum_post_solution_contains prog facts st HE k lower Hwf Hstrat Hlower
    other Hpost (p, row)).
  apply (semi_naive_sound fuel db Hsolve p row Hmem).
Qed.

(** A solved local database retains the key well-formedness established by actual index updates. *)
Theorem semi_naive_map_wf fuel db :
  stratum prog facts st lower k fuel = Outcome.Solved db -> Map.wf (penc prog) db.
Proof.
  intro Hsolve; destruct (solved_state fuel db Hsolve) as [s [-> [[Hready _] _]]].
  exact (accumulated_map_wf _ _ _ _ _ Hready).
Qed.

End Correctness.

End SemiNaiveProof.
Import SemiNaiveProof.
