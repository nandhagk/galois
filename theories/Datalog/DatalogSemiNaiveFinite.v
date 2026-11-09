(** * Finite growth of the semi-naive iterator

    Every continuing round adds an absent ground fact from finite source support.
    For example, a cycle cannot consume fuel after all supported tuples have been inserted.
    Builds on: DatalogSemiNaiveProof, source-universe support and CostLoop runs. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel DatalogRelation
  DatalogCompileProof DatalogSolve DatalogSemiNaive DatalogSemiNaiveIndex DatalogSemiNaiveReady
  DatalogSemiNaiveProof.
Import List.ListNotations SemiNaive SemiNaiveIndex SemiNaiveReady SemiNaiveProof.
Local Open Scope nat_scope.

Module SemiNaiveFinite.

(** Source head and fact occurrences bound all predicates that a stratum can derive. *)
Definition predicates {P} (prog : program P) (facts : list (ground_atom P)) :=
  map (fun r => pred (head r)) (rules prog) ++ map fst facts.

(** The finite support is proof-only and never materialized by the executable engine. *)
Definition support {P} (prog : program P) facts :=
  flat_map (fun p => map (fun row => (p, row)) (universe prog facts)) (predicates prog facts).

(** Support capacity retains source occurrences and the finite tuple universe. *)
Definition capacity {P} (prog : program P) facts := length (support prog facts).

(** The capacity equals the source predicate occurrence count times the tuple-universe length. *)
Theorem capacity_equation {P} (prog : program P) facts :
  capacity prog facts = (length (rules prog) + length facts) * length (universe prog facts).
Proof.
  unfold capacity, support.
  assert (Hlength : forall ps : list P,
    length (flat_map (fun p => map (fun row => (p, row)) (universe prog facts)) ps) =
      length ps * length (universe prog facts)).
  { intro ps; induction ps as [|p ps IH]; cbn [flat_map length]; [reflexivity |].
    rewrite length_app, length_map, IH; lia. }
  rewrite Hlength; unfold predicates; rewrite length_app, !length_map; reflexivity.
Qed.

Section Growth.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (HE : encoding_laws (penc prog)) (st : stratification P)
  (lower : P -> Cost.t relation) (k : nat).
Hypotheses (Hwf : program_wf prog facts) (Hstrat : stratified prog st)
  (Hlower : represents (fun p => Cost.value (lower p)) (model_below prog facts st k)).
Local Abbreviation E := (ground_encoding prog).
Local Abbreviation GE := (ground_encoding_laws prog HE).
Local Abbreviation invariant :=
  (correct prog facts st lower k).

Lemma derivation_support f :
  derives prog facts st k (model_below prog facts st k) f -> In f (support prog facts).
Proof.
  intro Hderive.
  assert (Htuple : In (snd f) (universe prog facts)).
  { apply (derives_support prog facts st k (model_below prog facts st k) Hwf Hstrat);
      [intros g Hg; exact (model_constants prog facts st Hwf Hstrat k g Hg) | exact Hderive]. }
  assert (Hpred : In (fst f) (predicates prog facts)).
  { unfold predicates; apply in_app_iff; destruct Hderive as [f Hfact Hl | r sigma Hr Hl Hp Hs Hn].
    - right; apply in_map, Hfact.
    - left; change (In (pred (head r)) (map (fun r => pred (head r)) (rules prog))).
      exact (in_map (fun x : rule P => pred (head x)) (rules prog) r Hr). }
  destruct f as [p row]; unfold support; apply in_flat_map; exists p; split;
    [exact Hpred | apply in_map, Htuple].
Qed.

Lemma accumulated_support s : invariant s ->
  incl (FinSet.elements (accumulated s)) (support prog facts).
Proof.
  intros [Hready [Hderived _]] f Hf.
  apply derivation_support, Hderived.
  apply (FinSet.elements_spec E GE _ _ (accumulated_wf _ _ _ _ _ Hready)), Hf.
Qed.

Lemma accumulated_size s : invariant s -> FinSet.size (accumulated s) <= capacity prog facts.
Proof.
  intro Hcorrect; unfold capacity; rewrite FinSet.size_elements.
  apply NoDup_incl_length.
  - apply (FinSet.elements_nodup E), (accumulated_wf _ _ _ _ _ (proj1 Hcorrect)).
  - apply accumulated_support, Hcorrect.
Qed.

Lemma step_growth s next :
  ready prog st lower k s -> step prog st lower k s = inl next ->
  FinSet.size (accumulated s) < FinSet.size (accumulated next).
Proof.
  intros Hready Hstep.
  pose proof (fresh_wf prog st lower k s (accumulated_wf _ _ _ _ _ Hready)) as Hfresh.
  pose proof (step_ready prog HE st lower k s next Hready Hstep) as Hnext.
  rewrite step_equation in Hstep.
  destruct (FinSet.is_empty (fresh prog st lower k s)) eqn:Hempty; [discriminate |].
  assert (Hexists : exists f, In f (FinSet.elements (fresh prog st lower k s))).
  { destruct (FinSet.elements (fresh prog st lower k s)) as [|f fs] eqn:Hrows.
    - exfalso; assert (Htrue : FinSet.is_empty (fresh prog st lower k s) = true).
      { apply (FinSet.is_empty_spec E _ Hfresh); intro f.
        destruct (FinSet.mem E f (fresh prog st lower k s)) eqn:Hmem; [|reflexivity].
        apply (FinSet.elements_spec E GE _ _ Hfresh) in Hmem; rewrite Hrows in Hmem;
          contradiction. }
      congruence.
    - exists f; now left. }
  destruct Hexists as [f Hf].
  apply (FinSet.elements_spec E GE _ _ Hfresh) in Hf.
  pose proof (proj2 (proj1 (fresh_members prog st lower k s f Hready) Hf)) as Habsent.
  assert (Hlength :
    length (f :: FinSet.elements (accumulated s)) <=
      length (FinSet.elements (accumulated next))).
  { apply NoDup_incl_length.
    - constructor.
      + intro Hin; apply (FinSet.elements_spec E GE _ _
          (accumulated_wf _ _ _ _ _ Hready)) in Hin; congruence.
      + apply (FinSet.elements_nodup E), (accumulated_wf _ _ _ _ _ Hready).
    - intros g [<- | Hg];
        apply (FinSet.elements_spec E GE _ _ (accumulated_wf _ _ _ _ _ Hnext));
        injection Hstep as <-; rewrite advance_equation; cbn [accumulated];
        rewrite FinSet.mem_union by
          (first [exact (accumulated_wf _ _ _ _ _ Hready) | exact Hfresh]);
        apply orb_true_iff.
      + right; exact Hf.
      + left; apply (FinSet.elements_spec E GE _ _
          (accumulated_wf _ _ _ _ _ Hready)), Hg. }
  change (S (length (FinSet.elements (accumulated s))) <=
    length (FinSet.elements (accumulated next))) in Hlength.
  rewrite <- !FinSet.size_elements in Hlength; exact Hlength.
Qed.

(** Remaining capacity counts supported facts absent from the current accumulated set. *)
Definition remaining (s : state P) :=
  capacity prog facts - FinSet.size (accumulated s).

(** Continuing transitions of the actual iterator strictly decrease remaining finite capacity. *)
Theorem step_decreases s next :
  invariant s -> step prog st lower k s = inl next -> remaining next < remaining s.
Proof.
  intros Hcorrect Hstep.
  pose proof (step_correct prog facts HE st lower k Hwf Hstrat Hlower s next Hcorrect Hstep)
    as Hnext.
  pose proof (step_growth s next (proj1 Hcorrect) Hstep) as Hgrowth.
  pose proof (accumulated_size next Hnext) as Hbound.
  unfold remaining; lia.
Qed.

Lemma exhausted_bound n s last :
  runs (step_c prog st lower k) n s (inl last) -> invariant s -> n <= remaining s.
Proof.
  intro Hrun; remember (inl last) as result eqn:Hresult.
  induction Hrun as [s | n s result Hstop | n s next result Hnext Hrun IH];
    intro Hcorrect.
  - lia.
  - discriminate.
  - pose proof (step_correct prog facts HE st lower k Hwf Hstrat Hlower s next
      Hcorrect Hnext) as Hcorrect_next.
    pose proof (step_decreases s next Hcorrect Hnext) as Hdecrease.
    specialize (IH Hresult Hcorrect_next); lia.
Qed.

(** Fuel above source capacity solves the same Cost.iterate runtime including its stop probe. *)
Theorem semi_naive_solved_enough fuel :
  capacity prog facts < Pos.to_nat fuel ->
  exists db, stratum prog facts st lower k fuel = Outcome.Solved db.
Proof.
  intro Hfuel.
  pose proof (iterate_value (step_c prog st lower k) fuel
    (initial prog facts st lower k)) as Hrun.
  change (runs (step_c prog st lower k) (Pos.to_nat fuel)
    (initial prog facts st lower k)
    (run prog st lower k fuel (initial prog facts st lower k))) in Hrun.
  unfold stratum, stratum_c; repeat rewrite Cost.value_bind.
  fold (@initial P prog facts st lower k).
  fold (@run P prog st lower k fuel (initial prog facts st lower k)).
  destruct (run prog st lower k fuel (initial prog facts st lower k)) as [last | stopped].
  - pose proof (exhausted_bound _ _ _ Hrun
      (initial_correct prog facts HE st lower k Hwf Hstrat Hlower)) as Hbound.
    unfold remaining in Hbound; lia.
  - eexists; reflexivity.
Qed.

(** Every fuel above the named source-capacity threshold yields a solved local database. *)
Theorem semi_naive_adequate :
  forall fuel, (Pos.of_succ_nat (capacity prog facts) <= fuel)%positive ->
    exists db, stratum prog facts st lower k fuel = Outcome.Solved db.
Proof.
  intros fuel Hfuel; apply semi_naive_solved_enough.
  apply Pos2Nat.inj_le in Hfuel; rewrite SuccNat2Pos.id_succ in Hfuel; lia.
Qed.

End Growth.

End SemiNaiveFinite.
Import SemiNaiveFinite.
