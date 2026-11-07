(** * Reference and legacy solver comparison

    The cycle and empty fixtures reproduce the joining fixtures of FixpointFIX2b.
    For example, the repeated constraint and repeated side target reach the same boolean values.
    Builds on: FixpointAnalyzeTest and the legacy total solver. *)

From Stdlib Require Import List Bool Arith PArith Lia Relations.Relation_Operators.
From Galois.Base Require Import BaseEncoding.
From Galois.Fixpoint Require Import FixpointAnalyze FixpointSolver.
From Galois.Tests.Fixpoint Require Import FixpointAnalyzeTest.
From GaloisLegacy.Collections Require Import CollectionsEncoding CollectionsMap.
From GaloisLegacy.Order Require Import OrderLattice OrderBasic.
From GaloisLegacy.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCycles
  FixpointWorklist FixpointTotal.
Import List.ListNotations.

Definition legacy_schedule : scheduler nat :=
  Scheduler (fun _ => 1%positive) (fun _ => false).

Definition legacy_cycle : System.t nat nat bool :=
  System.Make [0; 1; 2; 0] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 0 Query.Ret
      else Query.Side 0 true (Query.Side 0 false (Query.Ret false))).

Definition legacy_static : System.static legacy_cycle.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [0] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then [] else [0; 0]) _ _);
    intros c s x Hin; unfold legacy_cycle in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
Defined.

Definition legacy_evidence : terminates bool_lattice legacy_static legacy_schedule Joining :=
  inhabits (base_height bool_height).

Definition legacy_values : assignment nat bool :=
  Map.set nat_encoding 1 true (Map.set nat_encoding 0 true Map.empty).

Definition legacy_answer :=
  solve_total nat_encoding nat_encoding bool_lattice bool_laws legacy_schedule Joining
    legacy_cycle legacy_static legacy_evidence.

Local Lemma legacy_answer_values :
  proj1_sig legacy_answer = lookup nat_encoding bool_lattice legacy_values.
Proof.
  destruct (solve_total_run nat_encoding nat_encoding bool_lattice legacy_cycle legacy_schedule
    Joining bool_laws legacy_static legacy_evidence) as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [m [Hrun Heq]].
  assert (Hfixture : run_worklist nat_encoding nat_encoding bool_lattice legacy_schedule Joining
    legacy_cycle (Declared legacy_static (index_system nat_encoding legacy_cycle legacy_static))
    6 = Some legacy_values).
  { vm_compute; reflexivity. }
  pose proof (total_completed_runs_unique nat_encoding nat_encoding bool_lattice legacy_schedule
    Joining legacy_cycle _ fuel 6 m legacy_values Hrun Hfixture) as Hmaps.
  unfold legacy_answer; now rewrite Hmaps in Heq.
Qed.

Example cycle_differential :
  cycle_observe 3 = Some (map (proj1_sig legacy_answer) [0; 1; 2; 99]).
Proof.
  rewrite legacy_answer_values; vm_compute; reflexivity.
Qed.

Definition legacy_empty : System.t nat nat bool :=
  System.Make [] (fun c => c) (fun _ => Query.Ret true).

Definition legacy_empty_static : System.static legacy_empty.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _); intros c s x Hin; exact Hin.
Defined.

Definition legacy_empty_evidence :
  terminates bool_lattice legacy_empty_static legacy_schedule Joining :=
  inhabits (base_height bool_height).

Definition legacy_empty_answer :=
  solve_total nat_encoding nat_encoding bool_lattice bool_laws legacy_schedule Joining
    legacy_empty legacy_empty_static legacy_empty_evidence.

Local Lemma legacy_empty_values :
  proj1_sig legacy_empty_answer = lookup nat_encoding bool_lattice Map.empty.
Proof.
  destruct (solve_total_run nat_encoding nat_encoding bool_lattice legacy_empty legacy_schedule
    Joining bool_laws legacy_empty_static legacy_empty_evidence) as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [m [Hrun Heq]].
  assert (Hfixture : run_worklist nat_encoding nat_encoding bool_lattice legacy_schedule Joining
    legacy_empty (Declared legacy_empty_static
      (index_system nat_encoding legacy_empty legacy_empty_static)) 1 = Some Map.empty).
  { vm_compute; reflexivity. }
  pose proof (total_completed_runs_unique nat_encoding nat_encoding bool_lattice legacy_schedule
    Joining legacy_empty _ fuel 1 m Map.empty Hrun Hfixture) as Hmaps.
  unfold legacy_empty_answer; now rewrite Hmaps in Heq.
Qed.

Example empty_differential :
  match analyze_ref empty_analysis 1 with
  | Outcome.Solved s => Some (map (proj1_sig s) [0; 99])
  | _ => None
  end = Some (map (proj1_sig legacy_empty_answer) [0; 99]).
Proof.
  rewrite legacy_empty_values; vm_compute; reflexivity.
Qed.

Definition legacy_number_lattice : lattice (option nat) :=
  Lattice (option nat) number_le (Some 0) number_join (fun _ _ => None) (fun _ b => b).

Definition legacy_number_laws : lattice_laws legacy_number_lattice.
Proof.
  constructor.
  - intros [a|]; cbn; [apply Nat.leb_refl|reflexivity].
  - intros [a|] [b|] [c|]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc; apply Nat.leb_le in Hab; apply Nat.leb_le in Hbc; apply Nat.leb_le; lia.
  - intros [a|]; cbn; reflexivity.
  - intros [a|] [b|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_l.
  - intros [a|] [b|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_r.
  - intros [a|] [b|]; reflexivity.
  - intros [a|] [b|]; reflexivity.
  - intros a b Hab; exact Hab.
  - intros [a|] [b|] Hab; cbn; [apply Nat.leb_refl|reflexivity|apply Nat.leb_refl|reflexivity].
Qed.

Definition legacy_number_rank : widening_rank legacy_number_lattice.
Proof.
  refine (@WideningRank (option nat) legacy_number_lattice
    (fun a => match a with Some _ => 1 | None => 0 end) _ _).
  - intros [a|] [b|] Hbelow; cbn; lia.
  - intros [a|] [b|] Hbelow; cbn in *; try discriminate; lia.
Defined.

Definition legacy_number_system : System.t nat nat (option nat) :=
  System.Make [0; 1; 2; 3] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 2 (fun a => Query.Ret (number_succ a))
      else if Nat.eqb c 1 then Query.Ask 0 Query.Ret
      else if Nat.eqb c 2 then Query.Ask 1 Query.Ret
      else Query.Side 1 (Some 2) (Query.Side 1 (Some 1) (Query.Ret (Some 0)))).

Definition legacy_number_static : System.static legacy_number_system.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [2] else if Nat.eqb c 1 then [0]
      else if Nat.eqb c 2 then [1] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then []
      else if Nat.eqb c 2 then [] else [1; 1]) _ _);
    intros c s x Hin; unfold legacy_number_system in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2); cbn in *; exact Hin.
Defined.

Definition legacy_number_schedule : scheduler nat :=
  Scheduler (fun x => if Nat.eqb x 3 then 1%positive else 2%positive) (fun x => Nat.eqb x 0).

Local Lemma legacy_number_edge y z :
  flows legacy_number_static y z /\ widening_point legacy_number_schedule z = false -> y < z.
Proof.
  intros [[c [Hc [Hread Hout]]] Hnonwidening].
  cbn in Hc; destruct Hc as [Heq|[Heq|[Heq|[Heq|Hbad]]]]; try contradiction;
    subst c; cbn in Hread, Hout, Hnonwidening; try contradiction;
    destruct Hread as [Heq|Hbad]; try contradiction; subst y;
    destruct Hout as [Heq|Hbad]; try contradiction; subst z; cbn in Hnonwidening;
    discriminate || lia.
Qed.

Definition legacy_number_cuts :
  cuts_every_cycle legacy_number_static (widening_point legacy_number_schedule).
Proof.
  intros x Hcycle.
  assert (Hgrows : forall y z,
    clos_trans nat (fun y z => flows legacy_number_static y z /\
      widening_point legacy_number_schedule z = false) y z -> y < z).
  { intros y z Hpath; induction Hpath as [y z Hedge|y z w Hyz IH1 Hzw IH2].
    - apply legacy_number_edge, Hedge.
    - lia. }
  pose proof (Hgrows x x Hcycle); lia.
Qed.

Definition legacy_number_evidence :
  terminates legacy_number_lattice legacy_number_static legacy_number_schedule Widening :=
  conj (inhabits legacy_number_rank) legacy_number_cuts.

Definition legacy_number_values : assignment nat (option nat) :=
  Map.set nat_encoding 2 None
    (Map.set nat_encoding 1 None (Map.set nat_encoding 0 None Map.empty)).

Definition legacy_number_answer :=
  solve_total nat_encoding nat_encoding legacy_number_lattice legacy_number_laws
    legacy_number_schedule Widening legacy_number_system legacy_number_static
    legacy_number_evidence.

Local Lemma legacy_number_result :
  proj1_sig legacy_number_answer = lookup nat_encoding legacy_number_lattice legacy_number_values.
Proof.
  destruct (solve_total_run nat_encoding nat_encoding legacy_number_lattice legacy_number_system
    legacy_number_schedule Widening legacy_number_laws legacy_number_static legacy_number_evidence)
    as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [m [Hrun Heq]].
  assert (Hfixture : run_worklist nat_encoding nat_encoding legacy_number_lattice
    legacy_number_schedule Widening legacy_number_system
    (Declared legacy_number_static
      (index_system nat_encoding legacy_number_system legacy_number_static)) 6 =
    Some legacy_number_values).
  { vm_compute; reflexivity. }
  pose proof (total_completed_runs_unique nat_encoding nat_encoding legacy_number_lattice
    legacy_number_schedule Widening legacy_number_system _ fuel 6 m legacy_number_values
    Hrun Hfixture)
    as Hmaps.
  unfold legacy_number_answer; now rewrite Hmaps in Heq.
Qed.

Example widening_fixture_strategy_difference :
  (match analyze_ref number_analysis 8 with
   | Outcome.OutOfFuel _ => true
   | _ => false
   end, map (proj1_sig legacy_number_answer) [0; 1; 2; 3; 99]) =
    (true, [None; None; None; Some 0; Some 0]).
Proof.
  rewrite legacy_number_result; vm_compute; reflexivity.
Qed.
