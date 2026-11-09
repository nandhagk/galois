(** * Original point liveness and dense reference clients

    These examples retain use-before-definition and exit uses in unreachable components.
    For example, an unreachable exit use does not make the value live at the entry.
    Builds on: AnalysesSsaLiveSpec, FixpointAnalyze and FrameworkGenkillLeast. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Fixpoint Require Import FixpointLeast FixpointAnalysis FixpointSolver FixpointCheck
  FixpointAnalyze.
From Galois.Framework Require Import FrameworkBitvector FrameworkGenkillSound FrameworkGenkillLeast.
From Galois.Analyses.Ssa Require Import AnalysesSsaLiveSpec.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Module SpecFixture.

Definition cfg : Cfg.t nat unit :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => match n with 0 => [tt] | _ => [] end)
    (fun _ => 0) (fun _ => 1)) nat_encoding unit_encoding.

Definition vars : Vars.t nat unit nat :=
  Vars.of_pure cfg nat_encoding (fun _ => [7; 7]) (fun _ => [7])
    (fun n => match n with 1 => [8] | 2 => [9; 9] | _ => [] end).

Definition model := Live.Model vars [7; 8; 9].

Definition problem := Live.problem model.

Definition sigma n : set_t nat_encoding :=
  set_of_list nat_encoding
    (match n with 0 => [7; 8] | 1 => [8] | 2 => [9] | _ => [] end).

Definition oracle : Live.oracle nat nat :=
  Live.Oracle (fun n x => FinSet.mem_c nat_encoding x (set_raw (sigma n))).

Definition rows fuel :=
  match analyze (Bitvector.may_analysis problem) fuel with
  | Outcome.Solved result =>
    Some (map (fun n => map (fun x =>
      FinSet.mem nat_encoding x (set_raw (proj1_sig result n))) [7; 8; 9; 99]) [0; 1; 2; 99])
  | _ => None
  end.

Example dense_solver_retains_actual_rows :
  rows 32%positive =
    Some [[true; true; false; false]; [false; true; false; false];
      [false; false; true; false]; [false; false; false; false]].
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_solver_exhaustion_is_explicit :
  match analyze (Bitvector.may_analysis problem) 1%positive with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example use_before_definition_is_live : Live.live_at model 0 7.
Proof.
  eapply live_edge_use with (e := tt); vm_compute; auto.
Qed.

Example unreachable_exit_use_is_live : Live.live_at model 2 9.
Proof.
  apply live_exit; vm_compute; auto.
Qed.

Example exit_reader_retains_its_charge :
  Cost.ticks (Bitvector.boundary_c problem 2) = 2%N.
Proof.
  unfold problem; rewrite Live.problem_boundary_cost; vm_compute; reflexivity.
Qed.

Example exit_reader_retains_duplicates :
  Bitvector.boundary problem 2 = Some [9; 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example same_edge_use_survives_kill :
  (Bitvector.gen problem tt, Bitvector.kill problem tt) = ([7; 7], [7]).
Proof.
  vm_compute; reflexivity.
Qed.

Lemma graph_closed : graph_wf (live_graph vars).
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [<-|Hnone]; [vm_compute; auto|contradiction].
  - intros [|n] e He; vm_compute in He |- *; [reflexivity|contradiction].
  - intros [|n] [] Hn He; vm_compute in He |- *; [auto|contradiction].
Qed.

Lemma source_laws : Live.laws model.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact nat_encoding_laws.
  - exact graph_closed.
  - intros [] _; split; intros x Hx; vm_compute in Hx |- *; intuition congruence.
  - intros n Hn x Hx.
    change (0 = n \/ 1 = n \/ 2 = n \/ False) in Hn.
    destruct Hn as [<-|[<-|[<-|Hnone]]]; try contradiction;
      vm_compute in Hx |- *; intuition congruence.
Qed.

Example supplied_inventory_is_supported : Bitvector.supported problem.
Proof.
  apply Live.problem_supported; exact source_laws.
Qed.

Example actual_checker_accepts_reference :
  check_post (Analysis.lat (Bitvector.may_analysis problem))
    (Analysis.system (Bitvector.may_analysis problem)) sigma = true.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma sigma_least :
  least_solution (Analysis.lat (Bitvector.may_analysis problem))
    (Analysis.system (Bitvector.may_analysis problem)) sigma.
Proof.
  split.
  - apply check_post_sound; exact actual_checker_accepts_reference.
  - intros candidate Hpost n; apply (may_leb _ nat_encoding_laws); intros x Hx.
    apply (GenkillLeast.produces_in_post problem nat_encoding_laws unit_encoding_laws
      nat_encoding_laws candidate n x Hpost).
    apply (GenkillSound.member_list _ nat_encoding_laws) in Hx.
    destruct n as [|[|[|n]]]; cbn in Hx; try contradiction.
    + destruct Hx as [<-|[<-|Hnone]]; [| |contradiction].
      * replace 0 with (GenkillLeast.into problem tt) by reflexivity.
        apply (GenkillLeast.produces_step problem unit_encoding_laws nat_encoding_laws tt 7
          graph_closed ltac:(vm_compute; auto)).
        right; vm_compute; auto.
      * replace 0 with (GenkillLeast.into problem tt) by reflexivity.
        apply (GenkillLeast.produces_step problem unit_encoding_laws nat_encoding_laws tt 8
          graph_closed ltac:(vm_compute; auto)).
        left; split.
        -- apply (GenkillLeast.produces_seed problem nat_encoding_laws 1 [8] 8);
             vm_compute; auto.
        -- vm_compute; intuition discriminate.
    + destruct Hx as [<-|Hnone]; [|contradiction].
      apply (GenkillLeast.produces_seed problem nat_encoding_laws 1 [8] 8); vm_compute; auto.
    + destruct Hx as [<-|Hnone]; [|contradiction].
      apply (GenkillLeast.produces_seed problem nat_encoding_laws 2 [9; 9] 9);
        vm_compute; auto.
Qed.

Example importing_path_client n x :
  In n [0; 1; 2] ->
  (GenkillSound.member (sigma n) x <->
    exists m es, path (live_graph vars) n es m /\
      Forall (fun e => ~ In x (Vars.defs vars e)) es /\ point_use_at vars m x).
Proof.
  intro Hn.
  rewrite (Live.problem_least_live_at model sigma source_laws sigma_least n x Hn).
  apply Live.live_at_path; exact graph_closed.
Qed.

Lemma oracle_all_exact : Live.oracle_all_exact model oracle.
Proof.
  intros n x Hn.
  exact (Live.problem_least_live_at model sigma source_laws sigma_least n x Hn).
Qed.

Example shared_dense_template_client n x :
  reachable (live_graph vars) n ->
  (Live.live oracle n x = true <-> GenkillSound.member (sigma n) x).
Proof.
  apply (Live.oracle_dense model oracle sigma source_laws).
  - apply Live.oracle_all_reachable; [exact graph_closed|exact oracle_all_exact].
  - exact sigma_least.
Qed.

Example unreachable_use_does_not_leak_to_entry : ~ Live.live_at model 0 9.
Proof.
  intro Hlive.
  pose proof (proj2 (Live.problem_least_live_at model sigma source_laws sigma_least 0 9
    ltac:(vm_compute; auto)) Hlive) as Hmember.
  vm_compute in Hmember; discriminate.
Qed.

Example unsupported_value_is_absent : ~ Live.live_at model 1 99.
Proof.
  intro Hlive.
  pose proof (proj2 (Live.problem_least_live_at model sigma source_laws sigma_least 1 99
    ltac:(vm_compute; auto)) Hlive) as Hmember.
  vm_compute in Hmember; discriminate.
Qed.

End SpecFixture.
Import SpecFixture.
