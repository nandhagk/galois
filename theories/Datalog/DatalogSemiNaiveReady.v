(** * Maintained semi-naive indexes

    Initialization and advancement establish the exact predicate and Join indexes used by rounds.
    For example, a frontier reset replaces its rows while the accumulated index keeps older rows.
    Builds on: DatalogSemiNaiveIndex and the public Join maintenance theorem. *)

From Stdlib Require Import List Bool PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogJoin DatalogJoinProof DatalogSolve DatalogSemiNaive DatalogSemiNaiveSyntax
  DatalogSemiNaiveIndex.
Import List.ListNotations SemiNaive SemiNaiveSyntax SemiNaiveIndex.
Local Open Scope nat_scope.

Module SemiNaiveReady.

(** Readiness links computational storage to actual source occurrences and exact cached indexes. *)
Record ready {P} (prog : program P) st lower k (s : state P) : Prop := Ready {
  accumulated_wf : FinSet.wf (ground_encoding prog) (accumulated s);
  frontier_wf : FinSet.wf (ground_encoding prog) (frontier s);
  accumulated_map_wf : Map.wf (penc prog) (accumulated_index s);
  frontier_map_wf : Map.wf (penc prog) (frontier_index s);
  accumulated_exact : forall p row,
    member row (rel_of prog (accumulated_index s) p) =
      FinSet.mem (ground_encoding prog) (p, row) (accumulated s);
  frontier_exact : forall p row,
    member row (rel_of prog (frontier_index s) p) =
      FinSet.mem (ground_encoding prog) (p, row) (frontier s);
  frontier_subset : forall f, FinSet.mem (ground_encoding prog) f (frontier s) = true ->
    FinSet.mem (ground_encoding prog) f (accumulated s) = true;
  accumulated_level : forall f, FinSet.mem (ground_encoding prog) f (accumulated s) = true ->
    level st (fst f) = k;
  job_specs : map (fun j => (source_rule j, pivot j)) (jobs s) =
    snd (classify st k (rules prog));
  job_layout : forall j, In j (jobs s) ->
    tagged_rule j = tag_rule (source_rule j) (pivot j) /\
    JoinProof.ready [] (positive_atoms (body (tagged_rule j)))
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j)
}.

Section Indexes.
Context {P : Type} (prog : program P) (HE : encoding_laws (penc prog)).
Local Abbreviation E := (ground_encoding prog).
Local Abbreviation GE := (ground_encoding_laws prog HE).

Lemma batch_index_exact batch p row : FinSet.wf E batch ->
  member row (rel_of prog (add_atoms prog (FinSet.elements batch) Map.empty) p) =
    FinSet.mem E (p, row) batch.
Proof.
  intro Hbatch; apply eq_true_iff_eq.
  rewrite (add_atoms_exact prog HE) by apply Map.wf_empty.
  rewrite rel_empty, (FinSet.elements_spec E GE _ _ Hbatch); intuition discriminate.
Qed.

Lemma initial_specs facts st lower k :
  map (fun j => (source_rule j, pivot j)) (jobs (initial prog facts st lower k)) =
    snd (classify st k (rules prog)).
Proof.
  rewrite initial_equation; cbn [jobs]; rewrite map_map.
  generalize (snd (classify st k (rules prog))) as specs.
  intro specs; induction specs as [|[r i] specs IH]; cbn [map]; [reflexivity |].
  rewrite prepare_job_equation; cbn [source_rule pivot fst snd]; rewrite IH; reflexivity.
Qed.

(** Initial preparation establishes readiness without any semantic or cache-invariant premise. *)
Theorem initial_ready facts st lower k : ready prog st lower k (initial prog facts st lower k).
Proof.
  constructor.
  - rewrite initial_equation; apply FinSet.wf_of_list.
  - rewrite initial_equation; apply FinSet.wf_of_list.
  - rewrite initial_equation; apply add_atoms_wf, Map.wf_empty.
  - rewrite initial_equation; apply add_atoms_wf, Map.wf_empty.
  - intros p row; rewrite initial_equation; apply batch_index_exact, FinSet.wf_of_list.
  - intros p row; rewrite initial_equation; apply batch_index_exact, FinSet.wf_of_list.
  - intros f Hf; exact Hf.
  - intros f Hf; rewrite initial_equation in Hf; cbn [accumulated] in Hf.
    apply (mem_of_list E GE) in Hf; apply (seed_atoms_level prog facts st lower k f Hf).
  - apply initial_specs.
  - intros j Hj; rewrite initial_equation in Hj; cbn [jobs] in Hj.
    apply in_map_iff in Hj as [spec [<- Hspec]].
    rewrite initial_equation; cbn [accumulated_index frontier_index].
    rewrite prepare_job_equation; cbn [source_rule pivot tagged_rule plan]; split.
    + reflexivity.
    + apply JoinProof.prepare_ready.
Qed.

Lemma job_member st lower k s j : ready prog st lower k s -> In j (jobs s) ->
  In (source_rule j) (rules prog) /\ level st (pred (head (source_rule j))) = k /\
    In (pivot j) (pivots st k (source_rule j)).
Proof.
  intros Hready Hj; apply classify_jobs.
  rewrite <- (job_specs _ _ _ _ _ Hready).
  apply in_map_iff; exists j; split; [reflexivity | exact Hj].
Qed.

(** Candidate heads stay in their source stratum independently of valuation satisfaction. *)
Theorem candidates_level st lower k s : ready prog st lower k s ->
  forall f, FinSet.mem E f (candidates prog st lower k s) = true -> level st (fst f) = k.
Proof.
  intros Hready f Hf; rewrite candidates_equation in Hf.
  apply (mem_of_list E GE) in Hf; apply in_flat_map in Hf as [j [Hj Hrow]].
  apply in_map_iff in Hrow as [row [<- _]].
  exact (proj1 (proj2 (job_member st lower k s j Hready Hj))).
Qed.

Lemma fresh_members st lower k s f : ready prog st lower k s ->
  (FinSet.mem E f (fresh prog st lower k s) = true <->
    FinSet.mem E f (candidates prog st lower k s) = true /\
    FinSet.mem E f (accumulated s) = false).
Proof.
  intro Hready; rewrite fresh_equation, FinSet.mem_diff;
    [rewrite andb_true_iff, negb_true_iff; reflexivity |
      apply candidates_wf | exact (accumulated_wf _ _ _ _ _ Hready)].
Qed.

Lemma fresh_level st lower k s : ready prog st lower k s ->
  forall f, FinSet.mem E f (fresh prog st lower k s) = true -> level st (fst f) = k.
Proof.
  intros Hready f Hf; apply (fresh_members st lower k s f Hready) in Hf.
  exact (candidates_level st lower k s Hready f (proj1 Hf)).
Qed.

Lemma advance_index_exact st lower k s batch p row :
  ready prog st lower k s -> FinSet.wf E batch ->
  (member row (rel_of prog (accumulated_index (advance prog s batch)) p) = true <->
    member row (rel_of prog (accumulated_index s) p) = true \/
      FinSet.mem E (p, row) batch = true).
Proof.
  intros Hready Hbatch; rewrite advance_equation; cbn [accumulated_index].
  rewrite (add_atoms_exact prog HE) by exact (accumulated_map_wf _ _ _ _ _ Hready).
  rewrite (FinSet.elements_spec E GE _ _ Hbatch); reflexivity.
Qed.

Lemma advance_tagged st lower k s batch :
  ready prog st lower k s -> FinSet.wf E batch ->
  (forall f, FinSet.mem E f batch = true -> level st (fst f) = k) ->
  forall q row,
    member row (JoinProof.updated_env (fun q => Cost.ret (snd q)) (batch_rows_c prog
      (add_atoms prog (FinSet.elements batch) Map.empty))
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) q) =
    member row (tagged prog st k lower (accumulated_index (advance prog s batch))
      (frontier_index (advance prog s batch)) q).
Proof.
  intros Hready Hbatch Hlevel [p side] row; apply eq_true_iff_eq.
  rewrite JoinProof.updated_env_members, batch_rows_equation.
  rewrite (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
    (proj2_sig (rel_of prog (add_atoms prog (FinSet.elements batch) Map.empty) p))).
  change (member row (rel_of prog (add_atoms prog (FinSet.elements batch) Map.empty) p) =
    true \/ (side = false /\ member row
      (tagged prog st k lower (accumulated_index s) (frontier_index s) (p, side)) = true) <->
    member row (tagged prog st k lower (accumulated_index (advance prog s batch))
      (frontier_index (advance prog s batch)) (p, side)) = true).
  rewrite batch_index_exact by exact Hbatch.
  rewrite !tagged_equation; destruct side.
  - rewrite advance_equation; cbn [frontier_index].
    rewrite batch_index_exact by exact Hbatch; intuition discriminate.
  - change (FinSet.mem E (p, row) batch = true \/
      (false = false /\ member row
        (current prog st k lower (accumulated_index s) p) = true) <->
      member row (current prog st k lower (accumulated_index (advance prog s batch)) p) = true).
    rewrite !current_equation; destruct (Nat.eqb (level st p) k) eqn:Hp.
    + rewrite (advance_index_exact st lower k s batch p row Hready Hbatch); tauto.
    + assert (Habsent : FinSet.mem E (p, row) batch = false).
      { destruct (FinSet.mem E (p, row) batch) eqn:Hmem; [|reflexivity].
        specialize (Hlevel (p, row) Hmem); cbn [fst] in Hlevel.
        rewrite Hlevel, Nat.eqb_refl in Hp; discriminate. }
      rewrite Habsent; intuition discriminate.
Qed.

(** Advancing a same-level batch preserves every predicate index and cached occurrence-pivot plan. *)
Theorem advance_ready st lower k s batch :
  ready prog st lower k s -> FinSet.wf E batch ->
  (forall f, FinSet.mem E f batch = true -> level st (fst f) = k) ->
  ready prog st lower k (advance prog s batch).
Proof.
  intros Hready Hbatch Hlevel; constructor.
  - rewrite advance_equation; apply FinSet.wf_union;
      [exact (accumulated_wf _ _ _ _ _ Hready) | exact Hbatch].
  - rewrite advance_equation; exact Hbatch.
  - rewrite advance_equation; apply add_atoms_wf, (accumulated_map_wf _ _ _ _ _ Hready).
  - rewrite advance_equation; apply add_atoms_wf, Map.wf_empty.
  - intros p row; apply eq_true_iff_eq.
    rewrite (advance_index_exact st lower k s batch p row Hready Hbatch).
    rewrite (accumulated_exact _ _ _ _ _ Hready).
    rewrite advance_equation; cbn [accumulated].
    rewrite FinSet.mem_union;
      [symmetry; apply orb_true_iff | exact (accumulated_wf _ _ _ _ _ Hready) | exact Hbatch].
  - intros p row; rewrite advance_equation; cbn [frontier_index frontier].
    apply batch_index_exact, Hbatch.
  - intros [p row] Hmem; rewrite advance_equation in Hmem |- *.
    cbn [accumulated frontier] in *.
    rewrite FinSet.mem_union;
      [| exact (accumulated_wf _ _ _ _ _ Hready) | exact Hbatch].
    apply orb_true_iff; now right.
  - intros f Hf; rewrite advance_equation in Hf; cbn [accumulated] in Hf.
    rewrite FinSet.mem_union in Hf;
      [| exact (accumulated_wf _ _ _ _ _ Hready) | exact Hbatch].
    apply orb_true_iff in Hf as [Hf | Hf].
    + exact (accumulated_level _ _ _ _ _ Hready f Hf).
    + exact (Hlevel f Hf).
  - rewrite advance_equation; cbn [jobs]; rewrite map_map.
    rewrite <- (job_specs _ _ _ _ _ Hready).
    apply map_ext; intro j; rewrite update_job_equation; reflexivity.
  - intros j Hj; rewrite advance_equation in Hj; cbn [jobs] in Hj.
    apply in_map_iff in Hj as [old [<- Hold]].
    rewrite update_job_equation; cbn [tagged_rule source_rule pivot plan].
    destruct (job_layout _ _ _ _ _ Hready old Hold) as [Htag Hplan].
    split; [exact Htag |].
    eapply (plan_ready_ext [] _ (fun q => Cost.ret
      (JoinProof.updated_env (fun q => Cost.ret (snd q))
        (batch_rows_c prog (add_atoms prog (FinSet.elements batch) Map.empty))
        (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) q))).
    + intros q row; apply (advance_tagged st lower k s batch Hready Hbatch Hlevel q row).
    + apply JoinProof.join_insert_ready, Hplan.
Qed.

(** The actual continuation transition preserves readiness from its derived fresh batch. *)
Theorem step_ready st lower k s next :
  ready prog st lower k s -> step prog st lower k s = inl next ->
  ready prog st lower k next.
Proof.
  intros Hready Hstep; rewrite step_equation in Hstep.
  destruct (FinSet.is_empty (fresh prog st lower k s)); [discriminate |].
  injection Hstep as <-; apply advance_ready.
  - exact Hready.
  - apply fresh_wf, (accumulated_wf _ _ _ _ _ Hready).
  - apply fresh_level, Hready.
Qed.

End Indexes.

End SemiNaiveReady.
Import SemiNaiveReady.
