(** * Total-query loop reference controls

    Raw unlisted definitions retain their original finite-round classifications.
    For example, an unlisted pure nullary operation is recognized after one round.
    Builds on: AnalysesEqualityLoopReference and AnalysesEqualityProblemTest. *)

From Stdlib Require Import List Bool Arith Lia NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramSsa
  ProgramStrict.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem
  AnalysesEqualityLoopReference AnalysesEqualityLoopWorklist AnalysesEqualityLoopCorrect
  AnalysesEqualityLoopCost AnalysesEqualityLoop.
From Galois.Tests.Analyses.Equality Require Import AnalysesEqualityProblemTest.
Import List.ListNotations.

Definition reference_loop :=
  Numbering.LoopInfo 1 (Cost.lift (fun _ => 1%N) (fun b => Nat.eqb b 1)).

Definition raw_loop_ssa (inventory : list nat) : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure EqualityFixture.cfg nat_encoding inventory
    (fun x =>
      match x with
      | 0 => Op 0 [1]
      | 1 => Op 0 []
      | 3 => Op 1 []
      | 4 => Param 1 0
      | _ => Arbitrary
      end)
    (fun _ => 1) (fun _ => []) (fun _ => []) (fun _ => []).

Definition unlisted_nullary_problem :=
  Numbering.of_pure (raw_loop_ssa [2]) nat_encoding (Nat.eqb 0).

Definition malformed_operand_problem :=
  Numbering.of_pure (raw_loop_ssa [0; 2]) nat_encoding (Nat.eqb 0).

Example unlisted_nullary_is_true :
  NumberingLoopReference.invariant_in_ref unlisted_nullary_problem reference_loop 1 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_inside_operand_uses_its_total_definition :
  NumberingLoopReference.invariant_in_ref malformed_operand_problem reference_loop 0 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example costed_reference_retains_unlisted_query :
  Cost.value (NumberingLoopReference.reference_c unlisted_nullary_problem reference_loop 1) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example costed_reference_retains_malformed_operand :
  Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 0) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example impurity_and_parameters_are_not_invariant :
  (Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 3),
    Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 4)) =
    (false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_inventory_performs_no_reference_round :
  Cost.value (NumberingLoopReference.reference_c
    (Numbering.of_pure (raw_loop_ssa []) nat_encoding (Nat.eqb 0)) reference_loop 1) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example outside_body_initial_observation :
  Cost.value (NumberingLoopReference.reference_c malformed_operand_problem
    (Numbering.LoopInfo 2 (Cost.lift (fun _ => 1%N) (fun b => Nat.eqb b 2))) 0) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reference_agreement_contract :
  Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 0) =
    NumberingLoopReference.invariant_in_ref malformed_operand_problem reference_loop 0.
Proof.
  exact (NumberingLoopReference.reference_agrees malformed_operand_problem reference_loop 0).
Qed.

Definition countdown_nodes : FinSet.t nat := FinSet.of_list nat_encoding [0; 1; 2; 3; 4; 5].
Definition countdown_rules : Map.t nat (list nat) :=
  Map.of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])].
Definition countdown_prepared :=
  NumberingLoopWorklist.prepare nat_encoding countdown_nodes countdown_rules.
Definition countdown_result :=
  Cost.value (NumberingLoopWorklist.solve_c nat_encoding countdown_nodes countdown_rules).
Definition countdown_final := NumberingLoopWorklist.last_state countdown_result.

Example repeated_operands_keep_both_user_occurrences :
  Index.find nat_encoding 0 (NumberingLoopWorklist.users countdown_prepared) = [(0, 1); (0, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

Example countdown_chain_and_cycle :
  let marks := NumberingLoopWorklist.marked countdown_final in
  (FinSet.mem nat_encoding 0 marks, FinSet.mem nat_encoding 1 marks,
    FinSet.mem nat_encoding 2 marks, FinSet.mem nat_encoding 3 marks,
    FinSet.mem nat_encoding 4 marks, FinSet.mem nat_encoding 5 marks) =
    (true, true, true, false, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example each_ready_node_is_popped_once :
  NumberingLoopWorklist.processed countdown_final = 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_dependency_count_reaches_zero :
  Map.get nat_encoding 1 (NumberingLoopWorklist.remaining countdown_final) = Some 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example raw_countdown_drains_its_queue :
  match countdown_result with inl _ => false | inr _ => true end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_reference_control :
  (NumberingLoopWorklist.reference nat_encoding countdown_rules 6 1,
    NumberingLoopWorklist.reference nat_encoding countdown_rules 6 2,
    NumberingLoopWorklist.reference nat_encoding countdown_rules 6 3) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example importing_countdown_resource_contract :
  exists final,
    Cost.value (NumberingLoopWorklist.solve_c nat_encoding countdown_nodes countdown_rules) =
      inr final /\
    NumberingLoopWorklist.todo final = [] /\
    NumberingLoopWorklist.state_wf nat_encoding final /\
    NumberingLoopWorklist.processed final <= FinSet.size countdown_nodes.
Proof.
  exact (NumberingLoopWorklist.solve_finishes nat_encoding nat_encoding_laws
    countdown_nodes countdown_rules
    (FinSet.wf_of_list nat_encoding [0; 1; 2; 3; 4; 5])
    (Map.wf_of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])])).
Qed.

Local Lemma countdown_rules_supported :
  NumberingLoopCorrect.rules_supported nat_encoding countdown_nodes countdown_rules.
Proof.
  intros x deps Hget.
  pose proof (proj2 (Map.elements_spec nat_encoding nat_encoding_laws x deps countdown_rules
    (Map.wf_of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])])) Hget)
    as Hin.
  vm_compute in Hin.
  destruct Hin as [Hpair|[Hpair|[Hpair|[Hpair|[Hpair|Hfalse]]]]]; try contradiction;
    injection Hpair as <- <-; vm_compute; reflexivity.
Qed.

Local Lemma countdown_primitive_prices :
  NumberingLoopCost.primitive_prices nat_encoding countdown_nodes countdown_rules 1%N 3%N.
Proof.
  intros x [Hin|Hin]; vm_compute in Hin;
    repeat (destruct Hin as [<-|Hin]; [vm_compute; split; discriminate|]); contradiction.
Qed.

Example importing_nonempty_countdown_numeric_contract :
  (Cost.ticks (NumberingLoopWorklist.solve_c nat_encoding countdown_nodes countdown_rules) <=
    NumberingLoopCost.kernel_k * (1 + 6 + 5) * (1 + 1 + 3))%N.
Proof.
  exact (NumberingLoopCost.solve_cost nat_encoding nat_encoding_laws countdown_nodes
    countdown_rules 1%N 3%N (FinSet.wf_of_list nat_encoding _)
    (Map.wf_of_list nat_encoding _) countdown_rules_supported countdown_primitive_prices).
Qed.

Example universal_countdown_reference_agreement :
  forall x,
    FinSet.mem nat_encoding x (NumberingLoopWorklist.marked countdown_final) =
      NumberingLoopWorklist.reference nat_encoding countdown_rules 6 x.
Proof.
  apply (NumberingLoopCorrect.solve_agrees nat_encoding nat_encoding_laws
    countdown_nodes countdown_rules 6).
  - exact (FinSet.wf_of_list nat_encoding [0; 1; 2; 3; 4; 5]).
  - exact (Map.wf_of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])]).
  - exact countdown_rules_supported.
  - vm_compute; lia.
Qed.

Example public_unlisted_nullary_fallback :
  (NumberingLoop.invariant_in unlisted_nullary_problem reference_loop 1,
    NumberingLoop.route (Cost.value
      (NumberingLoop.query_c unlisted_nullary_problem reference_loop 1))) =
    (true, NumberingLoop.Unlisted_fallback).
Proof.
  vm_compute; reflexivity.
Qed.

Example public_malformed_operand_fallback :
  (NumberingLoop.invariant_in malformed_operand_problem reference_loop 0,
    NumberingLoop.route (Cost.value
      (NumberingLoop.query_c malformed_operand_problem reference_loop 0))) =
    (true, NumberingLoop.Malformed_fallback).
Proof.
  vm_compute; reflexivity.
Qed.

Example unlisted_query_falls_back_even_when_finite_preparation_accepts :
  match Cost.value (NumberingLoop.prepare_checked_c unlisted_nullary_problem reference_loop) with
  | NumberingLoop.Accepted _ => true
  | NumberingLoop.Rejected => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition closed_loop_ssa : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure EqualityFixture.cfg nat_encoding [0; 1; 2; 3; 4; 5; 6]
    (fun x =>
      match x with
      | 0 => Op 0 []
      | 1 => Op 0 [0; 0]
      | 2 => Op 0 [1]
      | 3 => Op 0 [4]
      | 4 => Op 0 [3]
      | 5 => Param 1 0
      | 6 => Op 1 [2]
      | _ => Arbitrary
      end)
    (fun _ => 1) (fun b => if Nat.eqb b 1 then [5] else [])
    (fun _ => []) (fun _ => []).

Definition closed_loop_problem :=
  Numbering.of_pure closed_loop_ssa nat_encoding (Nat.eqb 0).

Example indexed_public_chain_cycle_and_impurity :
  (NumberingLoop.invariant_in closed_loop_problem reference_loop 0,
    NumberingLoop.invariant_in closed_loop_problem reference_loop 1,
    NumberingLoop.invariant_in closed_loop_problem reference_loop 2,
    NumberingLoop.invariant_in closed_loop_problem reference_loop 3,
    NumberingLoop.invariant_in closed_loop_problem reference_loop 4,
    NumberingLoop.invariant_in closed_loop_problem reference_loop 5,
    NumberingLoop.invariant_in closed_loop_problem reference_loop 6) =
    (true, true, true, false, false, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example closed_listed_query_uses_indexed_path :
  NumberingLoop.route (Cost.value (NumberingLoop.query_c closed_loop_problem reference_loop 2)) =
    NumberingLoop.Indexed.
Proof.
  vm_compute; reflexivity.
Qed.

Definition outside_operand_ssa : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure EqualityFixture.cfg nat_encoding [0]
    (fun x => if Nat.eqb x 0 then Op 0 [9] else Arbitrary)
    (fun x => if Nat.eqb x 9 then 0 else 1)
    (fun _ => []) (fun _ => []) (fun _ => []).

Definition outside_operand_problem :=
  Numbering.of_pure outside_operand_ssa nat_encoding (fun _ => true).

Example unlisted_outside_operand_does_not_reject_finite_closure :
  (NumberingLoop.invariant_in outside_operand_problem reference_loop 0,
    NumberingLoop.route (Cost.value (NumberingLoop.query_c outside_operand_problem reference_loop 0))) =
      (true, NumberingLoop.Indexed).
Proof.
  vm_compute; reflexivity.
Qed.

Example public_raw_agreement_contract :
  forall x, NumberingLoop.invariant_in malformed_operand_problem reference_loop x =
    NumberingLoop.invariant_in_ref malformed_operand_problem reference_loop x.
Proof.
  intro x.
  exact (NumberingLoop.invariant_in_agrees malformed_operand_problem reference_loop
    nat_encoding_laws x).
Qed.

Module LoopSemantic.

Local Open Scope nat_scope.

Definition graph : Graph.t nat (nat * nat) :=
  Graph.of_pure [0] [0; 1]
    (fun n => if Nat.eqb n 0 then [(0, 1)] else if Nat.eqb n 1 then [(1, 1)] else [])
    fst snd.

Definition cfg := Cfg.Make graph nat_encoding (Cfg.edge_enc EqualityFixture.cfg).

Definition presentation : Ssa.t nat (nat * nat) nat unit unit :=
  Ssa.of_pure cfg nat_encoding [0; 1; 2]
    (fun x => if Nat.eqb x 2 then Op tt [0; 1] else Arbitrary)
    (fun x => if Nat.eqb x 2 then 1 else 0)
    (fun _ => []) (fun _ => []) (fun _ => []).

Definition problem := Numbering.of_pure presentation unit_encoding (fun _ => true).
Definition lp := reference_loop.
Definition point s := match s with 0 => 0 | S _ => 1 end.
Definition machine : semantics nat unit :=
  Semantics (fun s => s = 0) (fun s events t => t = S s /\ events = []).

Local Lemma advances s : step machine s [] (S s).
Proof.
  split; reflexivity.
Qed.

Definition control : Link.t nat unit nat (nat * nat) :=
  Link.Make point (fun s _ _ e => s = 0 /\ e = (0, 1)) (fun s _ _ => s <> 0).
Definition valuation s x : option nat :=
  match x with
  | 0 => Some 7
  | 1 => Some 8
  | 2 => if Nat.leb 2 s then Some 15 else None
  | _ => None
  end.
Definition link := SsaLink.Make control valuation.
Definition evaluate (_ : unit) (args : list nat) :=
  match args with [a; b] => Some (a + b) | _ => None end.
Definition holds (_ : unit) (_ : list nat) : Prop := True.

Local Lemma graph_valid : graph_wf graph.
Proof.
  constructor.
  - change (NoDup [0; 1]); repeat constructor; cbn; intuition discriminate.
  - intros n Hn; change (In n [0]) in Hn; change (In n [0; 1]).
    destruct Hn as [<-|Hfalse]; [now left|contradiction].
  - intros n e He; destruct n as [|[|n]]; vm_compute in He; try contradiction;
      destruct He as [<-|Hfalse]; [reflexivity|contradiction|reflexivity|contradiction].
  - intros n e Hn He; destruct n as [|[|n]]; vm_compute in He; try contradiction;
      destruct He as [<-|Hfalse]; try contradiction; change (In 1 [0; 1]); now right; left.
Qed.

Local Lemma control_laws : link_laws machine graph control.
Proof.
  constructor.
  - exact graph_valid.
  - intros s ->; change (In 0 [0]); now left.
  - intros s events t Hreachable Hstep; destruct s as [|s].
    + right; exists (0, 1); split; reflexivity.
    + left; discriminate.
  - intros e s events t Hreachable [Ht Hevents] [Hs He].
    subst s t e; vm_compute; split; [now left|reflexivity].
  - intros s events t Hreachable [Ht Hevents] Hstay; subst t.
    destruct s; [exfalso; apply Hstay; reflexivity|reflexivity].
Qed.

Local Lemma entry_frame x : valuation 1 x = valuation 0 x.
Proof.
  destruct x as [|[|[|x]]]; reflexivity.
Qed.

Local Lemma operands s :
  Forall2 (fun y c => SsaLink.val link s y = Some c) [0; 1] [7; 8].
Proof.
  constructor; [reflexivity|constructor; [reflexivity|constructor]].
Qed.

Local Lemma presentation_laws : ssa_laws machine presentation link evaluate holds.
Proof.
  constructor.
  - exact control_laws.
  - intros x b i Hdef; destruct x as [|[|[|x]]]; vm_compute in Hdef; discriminate.
  - intros e s events t Hreachable Hstep Htaken g ys Hguard.
    change (In (g, ys) []) in Hguard; contradiction.
  - intros e s events t Hreachable Hstep Htaken g ys x op args Hguard.
    change (In (g, ys) []) in Hguard; contradiction.
  - intros x c s events t Hreachable Hstep Hpost.
    change (valuation t x = Some c) in Hpost.
    destruct x as [|[|[|x]]].
    + left; exact Hpost.
    + left; exact Hpost.
    + change ((if Nat.leb 2 t then Some 15 else None) = Some c) in Hpost.
      destruct (Nat.leb 2 t); [|discriminate]; injection Hpost as <-.
      right; left; exists tt, [0; 1], [7; 8]; split; [reflexivity|split].
      * apply operands.
      * reflexivity.
    + discriminate.
  - intros s x c Hreachable Hvalue; destruct x as [|[|[|x]]].
    + change (In 0 [0; 1; 2]); now left.
    + change (In 1 [0; 1; 2]); right; now left.
    + change (In 2 [0; 1; 2]); right; right; now left.
    + discriminate.
Qed.

Local Lemma root_dominates n : dominates graph 0 n.
Proof.
  intros start edges Hentry Hpath; change (In start [0]) in Hentry.
  destruct Hentry as [<-|Hfalse]; [now left|contradiction].
Qed.

Local Lemma strict_laws : strict_ssa_laws machine presentation link.
Proof.
  constructor.
  - intros x s events t Hreachable Hstep Hstay Hchanged.
    destruct x as [|[|[|x]]].
    + exfalso; apply Hchanged; reflexivity.
    + exfalso; apply Hchanged; reflexivity.
    + destruct s; [exfalso; apply Hstay; reflexivity|reflexivity].
    + exfalso; apply Hchanged; reflexivity.
  - intros e x s events t Hreachable [Ht Hevents] [Hs He] Hchanged.
    subst s t; exfalso; apply Hchanged; apply entry_frame.
  - intros x s events t Hreachable Hstep Hstay Haway.
    destruct s; [exfalso; apply Hstay; reflexivity|].
    destruct x as [|[|[|x]]]; try reflexivity.
    exfalso; apply Haway; reflexivity.
  - intros e x s events t Hreachable [Ht Hevents] [Hs He] Haway.
    subst s t; apply entry_frame.
  - intros e g ys x Hedge Hguard.
    change (In (g, ys) []) in Hguard; contradiction.
  - intros x op args y Hdef Hy.
    destruct x as [|[|[|x]]]; vm_compute in Hdef; try discriminate;
      injection Hdef as <- <-.
    destruct Hy as [<-|[<-|Hfalse]]; [| |contradiction];
      change (dominates graph 0 1); apply root_dominates.
Qed.

Local Lemma pure_binding_laws : Numbering.loop_laws machine problem link evaluate.
Proof.
  constructor; intros s events t x op args Hreachable [Ht Hevents] Hdef Hp Hchanged.
  subst t; destruct x as [|[|[|x]]]; vm_compute in Hdef; try discriminate;
    injection Hdef as <- <-.
  destruct s as [|[|s]].
  - exfalso; apply Hchanged; reflexivity.
  - exists [7; 8], 15; split; [apply operands|split; reflexivity].
  - exfalso; apply Hchanged; reflexivity.
Qed.

Local Lemma loop_valid : Numbering.loop_info_wf graph lp.
Proof.
  constructor.
  - reflexivity.
  - intros n Hbody; change (Nat.eqb n 1 = true) in Hbody.
    apply Nat.eqb_eq in Hbody; subst n; apply dominates_refl.
  - intros e Hedge Htarget Hsource; change (Nat.eqb (snd e) 1 = true) in Htarget.
    now apply Nat.eqb_eq.
Qed.

Local Lemma stable_operands : Numbering.loop_operands_stable machine problem link lp 2.
Proof.
  intros op args y s events t Hinside Hdef Hp Hy Hreachable Hrun.
  vm_compute in Hdef; injection Hdef as <- <-.
  destruct Hy as [<-|[<-|Hfalse]]; [reflexivity|reflexivity|contradiction].
Qed.

Local Lemma classified : NumberingLoop.invariant_in problem lp 2 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Local Lemma reachable_header : reachable_state machine 1.
Proof.
  exists 0, []; split; [reflexivity|].
  exact (exec_step 0 [] 1 [] 1 (advances 0) (exec_refl 1)).
Qed.

Local Lemma first_run :
  exec_in machine (fun u => Numbering.body lp (Link.point control u) = true) 1 [] 1.
Proof.
  apply exec_in_refl; reflexivity.
Qed.

Local Lemma binding_run :
  exec_in machine (fun u => Numbering.body lp (Link.point control u) = true) 1 [] 2.
Proof.
  apply (exec_in_step 1 [] 2 [] 2).
  - reflexivity.
  - apply advances.
  - apply exec_in_refl; reflexivity.
Qed.

Local Lemma repeated_run :
  exec_in machine (fun u => Numbering.body lp (Link.point control u) = true) 2 [] 3.
Proof.
  apply (exec_in_step 2 [] 3 [] 3).
  - reflexivity.
  - apply advances.
  - apply exec_in_refl; reflexivity.
Qed.

Example actual_binding_changes_then_stays :
  SsaLink.val link 1 2 <> SsaLink.val link 2 2 /\
  SsaLink.val link 2 2 = SsaLink.val link 3 2.
Proof.
  split; [discriminate|].
  exact (NumberingLoop.loop_invariant_sound machine problem link evaluate holds lp 2
    nat_encoding_laws presentation_laws strict_laws pure_binding_laws loop_valid classified
    stable_operands 1 [] 1 [] 2 [] 3 reachable_header first_run binding_run repeated_run
    ltac:(discriminate)).
Qed.

End LoopSemantic.
