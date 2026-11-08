(** * Gen/kill path regressions

    These fixtures distinguish implicit may starts from strict must reachability.
    For example, an unreachable edge can generate a may fact at its target.
    Builds on: FrameworkBitvectorTest and FrameworkDenseTest. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet BaseRel.
From Galois.Lattice Require Import LatticeCore LatticeSet LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointCheck FixpointAnalysis.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector FrameworkGenkillSound
  FrameworkGenkillLeast.
From Galois.Tests.Framework Require Import FrameworkDenseTest FrameworkBitvectorTest.
Import List.ListNotations.
Import GenkillSound GenkillLeast.

Definition disconnected : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => if Nat.eqb n 1 then [0] else [])
    (fun _ => 1) (fun _ => 2)) nat_encoding nat_encoding.

Definition unreachable_generation :=
  Bitvector.of_pure disconnected nat_encoding [7] Forward
    (fun _ => [7]) (fun _ => []) (fun _ => Some []).

Example unreachable_generation_solver :
  sets_observe (Bitvector.may_analysis unreachable_generation) [0; 1; 2] =
    Some [[]; []; [7]].
Proof.
  vm_compute; reflexivity.
Qed.

Example unreachable_generation_equation_rejects_empty :
  check_post (Analysis.lat (Bitvector.may_analysis unreachable_generation))
    (Analysis.system (Bitvector.may_analysis unreachable_generation))
    (fun _ => set_empty nat_encoding) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unreachable_generation_must_stays_fresh :
  must_observe (Bitvector.must_analysis unreachable_generation) [0; 1; 2] =
    Some [Some []; None; None].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma diamond_wf : graph_wf (Cfg.graph diamond).
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [<-|Hbad]; [vm_compute; tauto|contradiction].
  - intros n e He; destruct n as [|[|[|n]]]; cbn in He; try contradiction;
      destruct He as [<-|He]; try contradiction; try reflexivity;
      destruct He as [<-|Hbad]; [reflexivity|contradiction].
  - intros n e Hn He; destruct n as [|[|[|n]]]; cbn in He; try contradiction;
      destruct He as [<-|He]; try contradiction; try (vm_compute; tauto);
      destruct He as [<-|Hbad]; [vm_compute; tauto|contradiction].
Qed.

Lemma loop_wf : graph_wf (Cfg.graph loop).
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [<-|Hbad]; [vm_compute; tauto|contradiction].
  - intros n e He; destruct n as [|[|n]]; cbn in He; try contradiction;
      destruct He as [<-|He]; try contradiction; try reflexivity;
      destruct He as [<-|Hbad]; [reflexivity|contradiction].
  - intros n e Hn He; destruct n as [|[|n]]; cbn in He; try contradiction;
      destruct He as [<-|He]; try contradiction; try (vm_compute; tauto);
      destruct He as [<-|Hbad]; [vm_compute; tauto|contradiction].
Qed.

Definition diamond_sigma n :=
  set_of_list nat_encoding (match n with 1 => [7] | 3 => [7; 8] | _ => [] end).

Definition diamond_must_sigma n :=
  match n with
  | 0 | 2 | 3 => Only (set_empty nat_encoding)
  | 1 => Only (set_of_list nat_encoding [7])
  | _ => All
  end.

Lemma diamond_path_left : path available_problem 0 [0; 2] 3.
Proof.
  econstructor; [vm_compute; tauto|].
  econstructor; [vm_compute; tauto|constructor].
Qed.

Lemma diamond_path_right : path available_problem 0 [1; 3] 3.
Proof.
  econstructor; [vm_compute; tauto|].
  econstructor; [vm_compute; tauto|constructor].
Qed.

Lemma diamond_path_one : path available_problem 0 [0] 1.
Proof.
  econstructor; [vm_compute; tauto|constructor].
Qed.

Lemma diamond_path_two : path available_problem 0 [1] 2.
Proof.
  econstructor; [vm_compute; tauto|constructor].
Qed.

Lemma diamond_support : Bitvector.supported available_problem.
Proof.
  split.
  - intros e He; change (0 = e \/ 1 = e \/ 2 = e \/ 3 = e \/ False) in He.
    destruct He as [<-|[<-|[<-|[<-|Hbad]]]]; try contradiction;
      split; intros x Hx; vm_compute in Hx |- *; tauto.
  - intros n xs Hn Hb; change (Some [] = Some xs) in Hb.
    inversion Hb; subst xs; intros x Hbad; contradiction.
Qed.

Lemma diamond_may_least :
  least_solution (Analysis.lat (Bitvector.may_analysis available_problem))
    (Analysis.system (Bitvector.may_analysis available_problem)) diamond_sigma.
Proof.
  split.
  - apply check_post_sound; vm_compute; reflexivity.
  - intros candidate Hpost n; apply (may_leb _ nat_encoding_laws); intros u Hu.
    apply (produces_in_post available_problem nat_encoding_laws nat_encoding_laws
      nat_encoding_laws candidate n u Hpost).
    unfold diamond_sigma in Hu; destruct n as [|[|[|[|n]]]];
      apply (member_list _ nat_encoding_laws) in Hu; cbn in Hu; try contradiction.
    + destruct Hu as [<-|Hbad]; [|contradiction].
      exists 0, (set_of_list nat_encoding []), [0].
      split; [eapply start_boundary; [vm_compute; tauto|reflexivity]|].
      split; [exact diamond_path_one|vm_compute; reflexivity].
    + destruct Hu as [<-|[<-|Hbad]]; try contradiction; solve [
        exists 0, (set_of_list nat_encoding []), [0; 2];
        split; [eapply start_boundary; [vm_compute; tauto|reflexivity]|];
        split; [exact diamond_path_left|vm_compute; reflexivity]].
Qed.

Lemma diamond_must_least :
  least_solution (Analysis.lat (Bitvector.must_analysis available_problem))
    (Analysis.system (Bitvector.must_analysis available_problem)) diamond_must_sigma.
Proof.
  split.
  - apply check_post_sound; vm_compute; reflexivity.
  - intros candidate Hpost n; destruct n as [|[|[|[|n]]]]; try reflexivity.
    + exact (must_boundary_path_bound available_problem nat_encoding_laws nat_encoding_laws
        nat_encoding_laws candidate 0 [] [] 0 Hpost
        (conj (or_introl eq_refl) (conj eq_refl (Rel.lpath_nil _ 0)))).
    + exact (must_boundary_path_bound available_problem nat_encoding_laws nat_encoding_laws
        nat_encoding_laws candidate 0 [] [0] 1 Hpost
        (conj (or_introl eq_refl) (conj eq_refl diamond_path_one))).
    + exact (must_boundary_path_bound available_problem nat_encoding_laws nat_encoding_laws
        nat_encoding_laws candidate 0 [] [1] 2 Hpost
        (conj (or_introl eq_refl) (conj eq_refl diamond_path_two))).
    + exact (must_boundary_path_bound available_problem nat_encoding_laws nat_encoding_laws
        nat_encoding_laws candidate 0 [] [1; 3] 3 Hpost
        (conj (or_introl eq_refl) (conj eq_refl diamond_path_right))).
Qed.

Example diamond_may_path_client :
  member (diamond_sigma 3) 8 <-> produces available_problem 3 8.
Proof.
  apply (may_least_paths available_problem nat_encoding_laws nat_encoding_laws
    nat_encoding_laws diamond_sigma diamond_wf diamond_support diamond_may_least).
  vm_compute; tauto.
Qed.

Example diamond_must_path_client :
  must_member (diamond_must_sigma 3) 7 <-> keeps available_problem 3 7.
Proof.
  apply (must_greatest_paths available_problem nat_encoding_laws nat_encoding_laws
    nat_encoding_laws diamond_must_sigma diamond_wf diamond_must_least).
  vm_compute; tauto.
Qed.

Example diamond_enumerated_path_values :
  (FinSet.elements (set_raw (path_value available_problem [] [0; 2])),
   FinSet.elements (set_raw (path_value available_problem [] [1; 3]))) = ([7; 8], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_must_negative : ~ keeps available_problem 3 7.
Proof.
  intro Hkeep; specialize (Hkeep 0 [] [1; 3]).
  assert (Hp : boundary_path available_problem 0 [] [1; 3] 3).
  { split; [vm_compute; tauto|split; [reflexivity|exact diamond_path_right]]. }
  specialize (Hkeep Hp); vm_compute in Hkeep; discriminate.
Qed.

Definition singleton_problem :=
  Bitvector.of_pure singleton nat_encoding [7] Forward
    (fun _ => []) (fun _ => []) (fun _ => Some [7]).

Example singleton_path_value :
  FinSet.elements (set_raw (path_value singleton_problem [7] [])) = [7].
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_may_solver :
  sets_observe (Bitvector.may_analysis singleton_problem) [0; 1] = Some [[7]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_must_solver :
  must_observe (Bitvector.must_analysis singleton_problem) [0; 1] = Some [Some [7]; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example strict_all_is_not_finite_universe :
  Bitvector.must_transfer (Bitvector.prepare unreachable_generation) 0 All = All /\
  Bitvector.must_transfer (Bitvector.prepare unreachable_generation) 0
    (Only (set_of_list nat_encoding [7])) <> All.
Proof.
  vm_compute; split; [reflexivity|discriminate].
Qed.

Lemma disconnected_wf : graph_wf (Cfg.graph disconnected).
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [<-|Hbad]; [vm_compute; tauto|contradiction].
  - intros n e He; destruct n as [|[|n]]; cbn in He; try contradiction.
    destruct He as [<-|Hbad]; [reflexivity|contradiction].
  - intros n e Hn He; destruct n as [|[|n]]; cbn in He; try contradiction.
    destruct He as [<-|Hbad]; [vm_compute; tauto|contradiction].
Qed.

Definition disconnected_must_sigma n :=
  if Nat.eqb n 0 then Only (set_empty nat_encoding) else All.

Lemma disconnected_must_least :
  least_solution (Analysis.lat (Bitvector.must_analysis unreachable_generation))
    (Analysis.system (Bitvector.must_analysis unreachable_generation)) disconnected_must_sigma.
Proof.
  split.
  - apply check_post_sound; vm_compute; reflexivity.
  - intros candidate Hpost [|n]; [|reflexivity].
    destruct (proj1 (Bitvector.must_source_post_iff unreachable_generation candidate
      nat_encoding_laws nat_encoding_laws) Hpost) as [Hseed Hflow].
    exact (Hseed 0 [] (or_introl eq_refl) eq_refl).
Qed.

Example listed_unreachable_all_client :
  disconnected_must_sigma 2 = All <-> ~ boundary_reaches unreachable_generation 2.
Proof.
  apply (must_no_path_all unreachable_generation nat_encoding_laws nat_encoding_laws
    nat_encoding_laws disconnected_must_sigma 2 disconnected_wf disconnected_must_least).
  vm_compute; tauto.
Qed.

Example unreachable_implicit_path :
  produces unreachable_generation 2 7.
Proof.
  exists 1, (set_empty nat_encoding), [0]; split.
  - apply start_empty; vm_compute; tauto.
  - split.
    + econstructor; [vm_compute; tauto|constructor].
    + vm_compute; reflexivity.
Qed.

Example unreachable_no_boundary_path : ~ boundary_reaches unreachable_generation 2.
Proof.
  apply (proj1 listed_unreachable_all_client); reflexivity.
Qed.

Definition finite_use_problem :=
  Bitvector.of_pure loop nat_encoding [7] Backward
    (fun e => if Nat.eqb e 1 then [7] else []) (fun _ => []) (fun _ => None).

Example backward_finite_use_solver :
  sets_observe (Bitvector.may_analysis finite_use_problem) [0; 1; 2] =
    Some [[7]; [7]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example backward_finite_use_without_boundary :
  produces finite_use_problem 1 7 /\
    (forall n, Bitvector.boundary finite_use_problem n = None).
Proof.
  split; [|intro n; reflexivity].
  exists 1, (set_empty nat_encoding), [1]; split.
  - apply start_empty; vm_compute; tauto.
  - split.
    + econstructor; [vm_compute; tauto|constructor].
    + vm_compute; reflexivity.
Qed.

Example path_height_bounds :
  (bound (may_height_on available_problem nat_encoding_laws),
   bound (must_height_on available_problem nat_encoding_laws)) = (2, 3).
Proof.
  vm_compute; reflexivity.
Qed.

Lemma diamond_coverage : boundary_coverage available_problem 3.
Proof.
  intros root es Hroot Hpath.
  change (0 = root \/ 1 = root \/ 2 = root \/ 3 = root \/ False) in Hroot.
  destruct Hroot as [<-|[<-|[<-|[<-|Hbad]]]]; try contradiction.
  - exists 0, [], []; split; [vm_compute; tauto|]; split; [reflexivity|constructor].
  - exists 0, [], [0]; split; [vm_compute; tauto|]; split; [reflexivity|exact diamond_path_one].
  - exists 0, [], [1]; split; [vm_compute; tauto|]; split; [reflexivity|exact diamond_path_two].
  - exists 0, [], [0; 2]; split; [vm_compute; tauto|].
    split; [reflexivity|exact diamond_path_left].
Qed.

Example boundary_only_client :
  member (diamond_sigma 3) 8 <-> boundary_produces available_problem 3 8.
Proof.
  apply (may_boundary_paths available_problem nat_encoding_laws nat_encoding_laws
    nat_encoding_laws diamond_sigma 3 8 diamond_wf diamond_support diamond_may_least).
  - vm_compute; tauto.
  - exact diamond_coverage.
Qed.

Definition reachable_query_problem :=
  Bitvector.of_pure
    (Cfg.Make (Graph.of_pure [0] [0; 1; 2]
      (fun n => match n with 0 => [0] | 1 => [1] | _ => [] end)
      (fun e => e) (fun _ => 2)) nat_encoding nat_encoding)
    nat_encoding [7] Forward (fun e => if Nat.eqb e 1 then [7] else [])
    (fun _ => []) (fun _ => Some []).

Example query_reachability_does_not_absorb_implicit_starts :
  sets_observe (Bitvector.may_analysis reachable_query_problem) [0; 1; 2] =
    Some [[]; []; [7]] /\
  FinSet.elements (set_raw (path_value reachable_query_problem [] [0])) = [].
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition unreachable_kill :=
  Bitvector.of_pure disconnected nat_encoding [7] Forward
    (fun _ => []) (fun _ => [7]) (fun _ => Some [7]).

Example unreachable_kill_is_strict :
  must_observe (Bitvector.must_analysis unreachable_kill) [0; 1; 2] =
    Some [Some [7]; None; None] /\
  (match Bitvector.must_transfer (Bitvector.prepare unreachable_kill) 0
    (Only (set_of_list nat_encoding [7])) with
   | All => None
   | Only a => Some (FinSet.elements (set_raw a))
   end) = Some [].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example empty_path_charges_preparation :
  Cost.ticks (apply_path_c singleton_problem [] (set_empty nat_encoding)) =
    Cost.ticks (Bitvector.prepare_c singleton_problem).
Proof.
  vm_compute; reflexivity.
Qed.

Example path_charges_transfer_visits :
  (Cost.ticks (Bitvector.prepare_c available_problem) <
    Cost.ticks (path_value_c available_problem [] [0%nat; 2%nat]))%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition finite_use_sigma n :=
  set_of_list nat_encoding (match n with 0 | 1 => [7] | _ => [] end).

Lemma finite_use_support : Bitvector.supported finite_use_problem.
Proof.
  split.
  - intros e He; change (0 = e \/ 1 = e \/ 2 = e \/ False) in He.
    destruct He as [<-|[<-|[<-|Hbad]]]; try contradiction;
      split; intros u Hu; vm_compute in Hu |- *; tauto.
  - intros n xs Hn Hbad; discriminate.
Qed.

Lemma finite_use_least :
  least_solution (Analysis.lat (Bitvector.may_analysis finite_use_problem))
    (Analysis.system (Bitvector.may_analysis finite_use_problem)) finite_use_sigma.
Proof.
  split.
  - apply check_post_sound; vm_compute; reflexivity.
  - intros candidate Hpost n; apply (may_leb _ nat_encoding_laws); intros u Hu.
    apply (produces_in_post finite_use_problem nat_encoding_laws nat_encoding_laws
      nat_encoding_laws candidate n u Hpost).
    unfold finite_use_sigma in Hu; destruct n as [|[|n]];
      apply (member_list _ nat_encoding_laws) in Hu; cbn in Hu; try contradiction;
      destruct Hu as [<-|Hbad]; try contradiction.
    + exists 1, (set_empty nat_encoding), [1; 0]; split.
      * apply start_empty; vm_compute; tauto.
      * split.
        { econstructor; [vm_compute; tauto|].
          econstructor; [vm_compute; tauto|constructor]. }
        { vm_compute; reflexivity. }
    + exact (proj1 backward_finite_use_without_boundary).
Qed.

Example finite_use_syntactic_client :
  member (finite_use_sigma 0) 7 <-> syntactic_live finite_use_problem 7 0.
Proof.
  apply (syntactic_live_least finite_use_problem nat_encoding_laws nat_encoding_laws
    nat_encoding_laws finite_use_sigma loop_wf finite_use_support eq_refl finite_use_least).
  vm_compute; tauto.
Qed.

Lemma singleton_wf : graph_wf (Cfg.graph singleton).
Proof.
  constructor.
  - repeat constructor; cbn; tauto.
  - intros n Hn; exact Hn.
  - intros n e Hbad; contradiction.
  - intros n e Hn Hbad; contradiction.
Qed.

Definition singleton_sigma n :=
  set_of_list nat_encoding (match n with 0 => [7] | _ => [] end).

Definition singleton_must_sigma n :=
  match n with 0 => Only (set_of_list nat_encoding [7]) | _ => All end.

Lemma singleton_may_least :
  least_solution (Analysis.lat (Bitvector.may_analysis singleton_problem))
    (Analysis.system (Bitvector.may_analysis singleton_problem)) singleton_sigma.
Proof.
  split.
  - apply check_post_sound; vm_compute; reflexivity.
  - intros candidate Hpost [|n].
    + destruct (proj1 (Bitvector.may_source_post_iff singleton_problem candidate
        nat_encoding_laws nat_encoding_laws) Hpost) as [Hseed Hflow].
      exact (Hseed 0 [7] (or_introl eq_refl) eq_refl).
    + change (leb (may nat_encoding) (set_empty nat_encoding) (candidate (S n)) = true).
      apply (bot_least (may_laws _ nat_encoding_laws)).
Qed.

Lemma singleton_must_least :
  least_solution (Analysis.lat (Bitvector.must_analysis singleton_problem))
    (Analysis.system (Bitvector.must_analysis singleton_problem)) singleton_must_sigma.
Proof.
  split.
  - apply check_post_sound; vm_compute; reflexivity.
  - intros candidate Hpost [|n]; [|reflexivity].
    destruct (proj1 (Bitvector.must_source_post_iff singleton_problem candidate
      nat_encoding_laws nat_encoding_laws) Hpost) as [Hseed Hflow].
    exact (Hseed 0 [7] (or_introl eq_refl) eq_refl).
Qed.

Lemma singleton_support : Bitvector.supported singleton_problem.
Proof.
  split.
  - intros e Hbad; contradiction.
  - intros n xs Hn Hb; inversion Hb; subst xs; apply incl_refl.
Qed.

Example singleton_may_path_client :
  member (singleton_sigma 0) 7 <-> produces singleton_problem 0 7.
Proof.
  apply (may_least_paths singleton_problem nat_encoding_laws nat_encoding_laws
    nat_encoding_laws singleton_sigma singleton_wf singleton_support singleton_may_least).
  vm_compute; tauto.
Qed.

Example singleton_must_path_client :
  must_member (singleton_must_sigma 0) 7 <-> keeps singleton_problem 0 7.
Proof.
  apply (must_greatest_paths singleton_problem nat_encoding_laws nat_encoding_laws
    nat_encoding_laws singleton_must_sigma singleton_wf singleton_must_least).
  vm_compute; tauto.
Qed.
