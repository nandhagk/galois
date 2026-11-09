(** * Exactness of the fast stratified program wrapper

    Successful fast strata compose into the perfect model through the existing database interface.
    For example, a higher negative literal observes the completed lower stratum's exact relation.
    Builds on: DatalogSemiNaiveProof, DatalogSemiNaiveFinite and DatalogSolveProof. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel DatalogRelation
  DatalogCompileProof DatalogSolve DatalogSolveProof DatalogSemiNaive DatalogSemiNaiveProof
  DatalogSemiNaiveFinite DatalogEngine.
Import List.ListNotations SemiNaiveProof SemiNaiveFinite.
Local Open Scope nat_scope.

Lemma solve_levels_fast_equation {P} (prog : program P) facts st fuel n :
  solve_levels_fast prog facts st fuel n =
  match n with
  | O => Outcome.Solved Map.empty
  | S k =>
    match solve_levels_fast prog facts st fuel k with
    | Outcome.OutOfFuel have => Outcome.OutOfFuel have
    | Outcome.Rejected why => Outcome.Rejected why
    | Outcome.Solved db =>
      match SemiNaive.stratum prog facts st (rel_of_c prog db) k fuel with
      | Outcome.OutOfFuel have => Outcome.OutOfFuel have
      | Outcome.Rejected why => Outcome.Rejected why
      | Outcome.Solved local => Outcome.Solved (store_relations prog
          (stratum_targets prog facts st k) (rel_of_c prog local) db)
      end
    end
  end.
Proof.
  destruct n as [|k]; [reflexivity |].
  unfold solve_levels_fast at 1; cbn [solve_levels_fast_c]; repeat rewrite Cost.value_bind.
  fold (@solve_levels_fast P prog facts st fuel k).
  destruct (solve_levels_fast prog facts st fuel k) as [db | have | why]; try reflexivity.
  rewrite Cost.value_bind.
  fold (@SemiNaive.stratum P prog facts st (rel_of_c prog db) k fuel).
  destruct (SemiNaive.stratum prog facts st (rel_of_c prog db) k fuel); reflexivity.
Qed.

Lemma solve_program_fast_equation {P} (prog : program P) facts fuel :
  solve_program_fast prog facts fuel =
  match stratify prog with
  | None => Outcome.Rejected Reason.Bad_stratification
  | Some st => solve_levels_fast prog facts st fuel (count st)
  end.
Proof.
  unfold solve_program_fast, solve_program_fast_c; rewrite Cost.value_bind.
  fold (@stratify P prog); destruct (stratify prog); reflexivity.
Qed.

Section Program.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) (HE : encoding_laws (penc prog)).
Hypotheses (Hwf : program_wf prog facts) (Hstrat : stratified prog st).

Lemma solve_levels_fast_exact fuel n db :
  solve_levels_fast prog facts st fuel n = Outcome.Solved db ->
  Map.wf (penc prog) db /\ represents (rel_of prog db) (model_below prog facts st n).
Proof.
  revert db; induction n as [|k IH]; intros db Hsolve;
    rewrite solve_levels_fast_equation in Hsolve.
  - injection Hsolve as <-; split; [apply Map.wf_empty |].
    intros p row; change (member row (lookup (penc prog) relation_lattice Map.empty p) = true
      <-> False).
    rewrite lookup_empty, relation_bot; intuition discriminate.
  - destruct (solve_levels_fast prog facts st fuel k) as [previous | have | why]
      eqn:Hprevious; try discriminate.
    destruct (IH previous eq_refl) as [Hmap Hlower].
    destruct (SemiNaive.stratum prog facts st (rel_of_c prog previous) k fuel)
      as [local | have | why] eqn:Hlocal; try discriminate.
    injection Hsolve as <-; split; [apply store_wf, Hmap |].
    intros p row; destruct (in_dec (eqb_dec (penc prog) HE) p
      (stratum_targets prog facts st k)) as [Hin | Hout].
    + rewrite store_member by assumption.
      pose proof (target_level prog facts st k p Hin) as Hl.
      rewrite (semi_naive_agrees prog facts HE st (rel_of_c prog previous) k
        Hwf Hstrat Hlower fuel local Hlocal p row).
      cbn [model_below]; split; [now right |].
      intros [Hbad | Hderive]; [|exact Hderive].
      pose proof (model_below_level prog facts st k (p, row) Hbad); cbn in *; lia.
    + rewrite store_absent by assumption.
      rewrite (Hlower p row); cbn [model_below]; split; [now left |].
      intros [Hbelow | Hderive]; [exact Hbelow |].
      exfalso; apply Hout, (derives_target prog facts st k (p, row)), Hderive.
Qed.

Lemma solve_levels_fast_adequate fuel n :
  capacity prog facts < Pos.to_nat fuel ->
  exists db, solve_levels_fast prog facts st fuel n = Outcome.Solved db.
Proof.
  intro Hfuel; induction n as [|k IH].
  - exists Map.empty; reflexivity.
  - destruct IH as [db Hdb].
    destruct (solve_levels_fast_exact fuel k db Hdb) as [_ Hlower].
    destruct (semi_naive_solved_enough prog facts HE st (rel_of_c prog db) k
      Hwf Hstrat Hlower fuel Hfuel) as [local Hlocal].
    rewrite solve_levels_fast_equation, Hdb, Hlocal; eexists; reflexivity.
Qed.

End Program.

(** A solved fast program represents the least model under source well-formedness and key laws. *)
Theorem solve_program_fast_exact {P} (prog : program P) facts fuel db :
  encoding_laws (penc prog) -> program_wf prog facts ->
  solve_program_fast prog facts fuel = Outcome.Solved db ->
  represents (rel_of prog db) (least_model prog facts).
Proof.
  intros HE Hwf Hsolve; rewrite solve_program_fast_equation in Hsolve.
  destruct (stratify prog) as [st |] eqn:Hst; [|discriminate].
  unfold least_model; rewrite Hst; unfold perfect_model.
  exact (proj2 (solve_levels_fast_exact prog facts st HE Hwf
    (stratify_sound prog st Hst) fuel (count st) db Hsolve)).
Qed.

(** Solved fast and reference runs agree on all relations even when their fuel values differ. *)
Theorem solve_program_fast_agrees {P} (prog : program P) facts fast_fuel reference_fuel fast ref :
  encoding_laws (penc prog) -> program_wf prog facts ->
  solve_program_fast prog facts fast_fuel = Outcome.Solved fast ->
  solve_program prog facts reference_fuel = Outcome.Solved ref ->
  forall p row, member row (rel_of prog fast p) = member row (rel_of prog ref p).
Proof.
  intros HE Hwf Hfast Href p row; apply eq_true_iff_eq.
  rewrite (solve_program_fast_exact prog facts fast_fuel fast HE Hwf Hfast p row),
    (solve_program_exact prog facts reference_fuel ref HE Hwf Href p row); reflexivity.
Qed.

(** Every fuel above finite source capacity solves a stratifiable well-formed fast program. *)
Theorem solve_program_fast_adequate {P} (prog : program P) facts :
  encoding_laws (penc prog) -> program_wf prog facts -> (exists st, stratified prog st) ->
  forall fuel, (Pos.of_succ_nat (capacity prog facts) <= fuel)%positive ->
    exists db, solve_program_fast prog facts fuel = Outcome.Solved db.
Proof.
  intros HE Hwf Hstrat fuel Hfuel.
  destruct (stratify_complete prog HE Hstrat) as [st Hst].
  rewrite solve_program_fast_equation, Hst.
  apply (solve_levels_fast_adequate prog facts st HE Hwf (stratify_sound prog st Hst)).
  apply Pos2Nat.inj_le in Hfuel; rewrite SuccNat2Pos.id_succ in Hfuel; lia.
Qed.
