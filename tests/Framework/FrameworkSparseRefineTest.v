(** * Stored-subject and dominating-guard regressions

    These fixtures pin the legacy truth cases under the prepared refinement rule.
    For example, equality of an identity result refines its previously unrestricted operand.
    Builds on: FrameworkSparseRefine, FrameworkSparseTest and GraphFixtures. *)

From Stdlib Require Import List Bool Arith ZArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeDisjunction LatticeAdjoin.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom GraphFixtures.
From Galois.Program Require Import ProgramSemantics ProgramCfg ProgramLink ProgramSsa
  ProgramStrict ProgramEdgeProjection.
From Galois.Domains Require Import DomainsValue DomainsPoint DomainsTagged DomainsNumeric
  DomainsBitsValue.
From Galois.Fixpoint Require Import FixpointAnalysis FixpointAnalyze FixpointSolver FixpointCheck
  FixpointSystem.
From Galois.Framework Require Import FrameworkSparse FrameworkSparseRefine.
From Galois.Tests.Framework Require Import FrameworkDenseTest FrameworkSparseTest
  FrameworkSparseSoundTest.
Import List.ListNotations Cost.Notations Expr Sparse SparseRefine.
Local Open Scope nat_scope.

(** The subject is stored separately from its immediate operand occurrences. *)
Definition guard_arguments (e : expr) b subject (fs : list (tagged point)) :=
  let xs := seq 0 (length fs) in
  let m := Map.of_list nat_encoding
    ((100, Some subject) :: combine xs (map (@Some (tagged point)) fs)) in
  match Cost.value (guard_one_c (N := nat) nat_encoding values m
    (Truth b, [100], [(100, Op e xs)])) with
  | None => None
  | Some m => Cost.value (collect_c (map (fun x => Map.find_or nat_encoding None x m) xs))
  end.

Example constant_arithmetic :
  ValueAbs.op values (App bvadd [Var 0; Var 1]) [number 1; number 1] = number 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example true_32_bit_one_plus_one_keeps_arguments :
  guard_arguments (App bvadd [Var 0; Var 1]) true (number 2) [number 1; number 1] =
    Some [number 1; number 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example false_zero_keeps_argument :
  guard_arguments (Var 0) false (number 0) [number 0] = Some [number 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example true_nonzero_keeps_argument :
  guard_arguments (Var 0) true (number 7) [number 7] = Some [number 7].
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_width_variable_true :
  guard_arguments (Var 0) true TAny [TAny] = Some [TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_width_variable_false :
  guard_arguments (Var 0) false TAny [TAny] = Some [TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example root_comparison_preserves_inputs :
  guard_arguments (App bvult [Var 0; Var 1]) true
    (TVal 1%positive (PVal 1)) [number 1; number 2] =
    Some [number 1; number 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example root_truncation_tests_result_truth :
  guard_arguments (App (bvtrunc 1%positive) [Var 0]) false
    (TVal 1%positive (PVal 0)) [number 2] = Some [number 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_expression_has_bottom_forward_result :
  ValueAbs.op values (App bvadd [Var 0]) [number 1] = TBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_expression_refinement_preserves_input_arity :
  option_map (@length (tagged point))
    (guard_arguments (App bvadd [Var 0]) true TBot [number 1; number 2]) = Some 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_expression_impossible_subject_refines_all_operands :
  guard_arguments (App bvadd [Var 0]) true TBot [number 1; number 2] =
    Some [TBot; TBot].
Proof.
  vm_compute; reflexivity.
Qed.

Definition unmapped_bridge : op_bridge unit word :=
  {| op_expr_c := fun _ => Cost.ret None;
     to_word_c := to_word_c bridge;
     truth_words := true;
     differ_words_c := fun _ => Cost.ret false |}.

Definition unmapped_values :=
  bits_values (tagged_domain point_word_domain) unmapped_bridge TAny.

Example unmapped_expression_retains_facts_in_order :
  ValueAbs.back unmapped_values tt TAny [number 7; TAny; number 0] =
    [number 7; TAny; number 0].
Proof.
  vm_compute; reflexivity.
Qed.

(** Concretisations pin the concrete operand witnesses alongside the precision equations. *)
Definition numeric_gamma :=
  numeric_conc (tagged_domain point_word_domain) (tagged_gamma point_gamma) bridge.

Example true_32_bit_one_plus_one_contains_concrete_arguments :
  match guard_arguments (App bvadd [Var 0; Var 1]) true (number 2) [number 1; number 1] with
  | Some fs => Forall2 (gamma numeric_gamma) fs [(32%positive, 1%Z); (32%positive, 1%Z)]
  | None => False
  end.
Proof.
  vm_compute; repeat constructor; discriminate.
Qed.

Example false_zero_contains_concrete_argument :
  match guard_arguments (Var 0) false (number 0) [number 0] with
  | Some fs => Forall2 (gamma numeric_gamma) fs [(32%positive, 0%Z)]
  | None => False
  end.
Proof.
  vm_compute; repeat constructor; discriminate.
Qed.

Example true_nonzero_contains_concrete_argument :
  match guard_arguments (Var 0) true (number 7) [number 7] with
  | Some fs => Forall2 (gamma numeric_gamma) fs [(32%positive, 7%Z)]
  | None => False
  end.
Proof.
  vm_compute; repeat constructor; discriminate.
Qed.

Example unknown_width_both_branches_contain_valid_arguments :
  match guard_arguments (Var 0) true TAny [TAny],
    guard_arguments (Var 0) false TAny [TAny] with
  | Some fs, Some gs =>
    Forall2 (gamma numeric_gamma) fs [(64%positive, 19%Z)] /\
    Forall2 (gamma numeric_gamma) gs [(32%positive, 0%Z)]
  | _, _ => False
  end.
Proof.
  vm_compute; split; constructor; [exact I|constructor|exact I|constructor].
Qed.

Example root_comparison_contains_concrete_arguments :
  match guard_arguments (App bvult [Var 0; Var 1]) true
    (TVal 1%positive (PVal 1)) [number 1; number 2] with
  | Some fs => Forall2 (gamma numeric_gamma) fs [(32%positive, 1%Z); (32%positive, 2%Z)]
  | None => False
  end.
Proof.
  vm_compute; repeat constructor; discriminate.
Qed.

Example root_truncation_contains_concrete_argument :
  match guard_arguments (App (bvtrunc 1%positive) [Var 0]) false
    (TVal 1%positive (PVal 0)) [number 2] with
  | Some fs => Forall2 (gamma numeric_gamma) fs [(32%positive, 2%Z)]
  | None => False
  end.
Proof.
  vm_compute; repeat constructor; discriminate.
Qed.

Definition equal_cfg : Cfg.t nat (nat * nat) :=
  Cfg.Make (Prepared.graph Fixtures.Diamond.prepared) nat_encoding
    (codec_enc (pair_codec nat_codec nat_codec)).

Definition equal_ssa : Ssa.t nat (nat * nat) nat expr (bits_guard word) :=
  Ssa.of_pure equal_cfg nat_encoding [0; 1]
    (fun x => if Nat.eqb x 1 then Op (Var 0) [0] else Param 1 0)
    (fun _ => 1) (fun b => if Nat.eqb b 1 then [0] else []) (fun _ => [])
    (fun e => if Nat.eqb (fst e) 1 then [(Equal (32%positive, 2%Z), [1])] else []).

Definition equal_problem := Sparse.Make equal_ssa values (fun _ => Cost.ret TAny).
Definition unknown_facts (_ : unknown nat (nat * nat) nat) := Some (@TAny point).
Definition equal_context := make_dom_context Fixtures.Diamond.prepared Fixtures.Diamond.tree.

Example equal_refines_through_definition :
  refine_on_edge equal_problem unknown_facts (1, 2) 0 = Some (number 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example equal_operand_strictly_smaller :
  (leb (ValueAbs.lat values) (number 2) TAny,
    leb (ValueAbs.lat values) TAny (number 2)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dominating_equal_refines_operand :
  refined_fact equal_problem equal_context unknown_facts 2 0 = Some (number 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example no_dominating_edge_retains_stored_fact :
  refined_fact equal_problem equal_context unknown_facts 4 0 = unknown_facts (UVal 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example equal_analyze_runs :
  observe (sparse_analysis equal_problem 1) 16 [UVal 0; UVal 1; UEdge (1, 2)] =
    Some [Some TAny; Some TAny; Some TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example supplied_tree_checker_accepts :
  DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_run_finishes :
  match analyze FrameworkSparseTest.analysis 16 with
  | Outcome.Solved _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_checker_accepts :
  check_post (Analysis.lat FrameworkSparseTest.analysis)
    (Analysis.system FrameworkSparseTest.analysis) candidate = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_constant_propagation :
  observe FrameworkSparseTest.analysis 16 [UVal 1] = Some [Some (number 2)].
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_infeasible_edge :
  observe FrameworkSparseTest.analysis 16 [UEdge 1] = Some [None] /\
  edge_feasible problem candidate 1 = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example sparse_numeric_feasible_edge :
  observe FrameworkSparseTest.analysis 16 [UEdge 0] = Some [Some TAny] /\
  edge_feasible problem candidate 0 = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition path_values k :=
  ValueAbs.disjunctive k (disjunction k (ValueAbs.lat values))
    (fun k xs => compact_c k (ValueAbs.lat values) xs) values.

Example bounded_path_merge :
  join (ValueAbs.lat (path_values 1)) [number 1] [number 2] =
    [TVal 32%positive PTop].
Proof.
  vm_compute; reflexivity.
Qed.

Example path_arithmetic_preserves_alternatives :
  ValueAbs.op (path_values 2) (App bvadd [Var 0; Var 1])
    [[number 1; number 2]; [number 1]] = [number 2; number 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example path_guard_refines_joined_subject :
  ValueAbs.guard (path_values 2) (Equal (32%positive, 2%Z))
    [[number 1; number 2]] = [[number 2]].
Proof.
  vm_compute; reflexivity.
Qed.

Example path_backward_refines_joined_arguments :
  match ValueAbs.guard (path_values 2) (Truth false) [[number 7]] with
  | [subject] => ValueAbs.back (path_values 2) (Var 0) subject [[number 7]]
  | _ => []
  end = [[TBot]].
Proof.
  vm_compute; reflexivity.
Qed.

Definition numeric_prepared := Prepared.prepare nat_encoding (Cfg.graph ssa_cfg).
Definition numeric_parents := Map.of_list positive_encoding [(2, 1); (3, 1)]%positive.
Definition numeric_tree := DomCheck.of_parents numeric_prepared numeric_parents.
Definition numeric_context := make_dom_context numeric_prepared numeric_tree.

Example numeric_supplied_tree_checker_accepts :
  DomCheck.check numeric_prepared numeric_parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dominated_guard_chain :
  flat_map (Ssa.guards ssa_program) (dominating_edges_in numeric_context 1) =
    [(Equal (32%positive, 2%Z), [1])].
Proof.
  vm_compute; reflexivity.
Qed.

Example dominated_guard_refines_the_use :
  refined_fact problem numeric_context (fun _ => Some TAny) 1 1 = Some (number 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example stored_subject_is_not_recomputed :
  option_map (fun m => Map.find_or nat_encoding None 0 m)
    (Cost.value (guard_one_c (N := nat) nat_encoding values
      (Map.of_list nat_encoding [(0, Some (number 1)); (1, Some (number 0))])
      (Truth true, [1], [(1, Op (App bvadd [Var 0; Var 1]) [0; 0])]))) =
    Some (Some TBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_operand_first_occurrence :
  option_map (fun m => Map.find_or nat_encoding None 0 m)
    (Cost.value (guard_one_c (N := nat) nat_encoding unequal_occurrence_values
      (Map.of_list nat_encoding [(0, Some PTop)])
      (tt, [0; 0], [(0, Arbitrary); (0, Arbitrary)]))) = Some (Some (PVal 1)).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ordered_values : ValueAbs.t point unit nat :=
  @ValueAbs.Make point unit nat point_lattice PTop (fun _ _ => Cost.ret PTop)
    (fun _ _ xs => Cost.ret xs)
    (fun g xs => map_c (fun _ => Cost.ret (PVal (Z.of_nat g))) xs).

Example guards_thread_the_changing_map :
  option_map (fun m => Map.find_or nat_encoding None 0 m)
    (Cost.value (guards_c (N := nat) nat_encoding ordered_values
      [(1, [0], [(0, Arbitrary)]); (2, [0], [(0, Arbitrary)])]
      (Map.of_list nat_encoding [(0, Some PTop)]))) = Some (Some (PVal 2)).
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_subject_rejects_refinement :
  Cost.value (guard_one_c (N := nat) nat_encoding values Map.empty
    (Truth true, [0], [(0, Arbitrary)])) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_guards_preserve_supplied_fact :
  refine_fact problem candidate 2 0 (Some (number 7)) = Some (number 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_guard_engine_cost :
  Cost.ticks (guards_c (N := nat) nat_encoding values [] Map.empty) = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition strict_program : Ssa.t nat (nat * nat) nat unit bool :=
  Ssa.of_pure equal_cfg nat_encoding [0] (fun _ => Op tt []) (fun _ => 1)
    (fun _ => []) (fun _ => [])
    (fun e => if Nat.eqb (fst e) 1 then [(true, [0])] else []).

Definition strict_machine : semantics nat unit :=
  Semantics (fun s => s = 1)
    (fun s l t => l = [] /\ In (s, t) [(1, 2); (1, 3); (2, 4); (3, 4)]).

Definition strict_link : Link.t nat unit nat (nat * nat) :=
  Link.Make (fun s => s) (fun s _ t e => e = (s, t)) (fun _ _ _ => False).

Definition strict_values : SsaLink.t nat unit nat (nat * nat) nat unit :=
  SsaLink.Make strict_link (fun _ x => if Nat.eqb x 0 then Some tt else None).

Example strict_link_laws :
  link_laws strict_machine (Cfg.graph equal_cfg) strict_link.
Proof.
  constructor.
  - exact (proj1 Fixtures.Diamond.fixture_ready).
  - intros s ->; vm_compute; left; reflexivity.
  - intros s l t _ _; right; exists (s, t); reflexivity.
  - intros e s l t _ [-> Hedge] ->.
    vm_compute in Hedge; destruct Hedge as [Heq|[Heq|[Heq|[Heq|Hbad]]]];
      [| | | |contradiction]; inversion Heq; subst; vm_compute; tauto.
  - intros s l t _ _ Hbad; contradiction.
Qed.

Example strict_ssa_sound_laws :
  ssa_laws strict_machine strict_program strict_values
    (ValueSem.eval unit_semantics) (ValueSem.holds unit_semantics).
Proof.
  constructor.
  - exact strict_link_laws.
  - intros x b i Hdef; discriminate.
  - intros e s l t _ _ _ g ys Hguard.
    change (In (g, ys) (if Nat.eqb (fst e) 1 then [(true, [0])] else [])) in Hguard.
    destruct (Nat.eqb (fst e) 1); [|contradiction].
    destruct Hguard as [Heq|Hbad]; [inversion Heq; subst|contradiction].
    exists [tt]; split; [constructor; [reflexivity|constructor]|reflexivity].
  - intros e s l t _ _ _ g ys x k args Hguard Hx Hdef.
    change (In (g, ys) (if Nat.eqb (fst e) 1 then [(true, [0])] else [])) in Hguard.
    destruct (Nat.eqb (fst e) 1); [|contradiction].
    destruct Hguard as [Heq|Hbad]; [inversion Heq; subst|contradiction].
    destruct Hx as [<-|Hbad]; [|contradiction].
    cbn in Hdef; injection Hdef as <- <-.
    exists [], tt; split; [constructor|split; reflexivity].
  - intros x c s l t _ _ Hvalue; left; exact Hvalue.
  - intros s [|x] c _ Hvalue; [left; reflexivity|discriminate].
Qed.

Example strict_transport_laws : strict_ssa_laws strict_machine strict_program strict_values.
Proof.
  constructor.
  - intros x s l t _ _ _ Hchange; exfalso; apply Hchange; reflexivity.
  - intros e x s l t _ _ _ Hchange; exfalso; apply Hchange; reflexivity.
  - intros x s l t _ _ _ _; reflexivity.
  - intros e x s l t _ _ _ _; reflexivity.
  - intros e g ys x _ Hguard Hx.
    change (In (g, ys) (if Nat.eqb (fst e) 1 then [(true, [0])] else [])) in Hguard.
    destruct (Nat.eqb (fst e) 1); [|contradiction].
    destruct Hguard as [Heq|Hbad]; [inversion Heq; subst|contradiction].
    destruct Hx as [<-|Hbad]; [|contradiction].
    intros s es Hentry Hpath; vm_compute in Hentry.
    destruct Hentry as [<-|Hbad]; [left; reflexivity|contradiction].
  - intros x k args y Hdef Hy; cbn in Hdef; injection Hdef as <- <-; contradiction.
Qed.

Definition strict_problem := Sparse.Make strict_program unit_domain (fun _ => Cost.ret true).
Definition strict_facts (_ : unknown nat (nat * nat) nat) := Some true.

Example dominated_refinement_sound_client :
  gamma (lift_bot_gamma unit_gamma)
    (refined_fact strict_problem equal_context strict_facts 2 0) tt.
Proof.
  eapply (refined_fact_sound strict_machine strict_problem strict_values unit_semantics
    unit_gamma strict_facts Fixtures.Diamond.prepared Fixtures.Diamond.tree).
  - reflexivity.
  - exact Fixtures.Diamond.fixture_ready.
  - exact Fixtures.Diamond.tree_exact.
  - exact nat_encoding_laws.
  - exact strict_ssa_sound_laws.
  - exact strict_transport_laws.
  - exact unit_domain_laws.
  - exists 1, []; split; [reflexivity|].
    apply exec_one; split; [reflexivity|left; reflexivity].
  - intros x c _; reflexivity.
  - reflexivity.
Qed.

Definition repeated_graph : Graph.t nat unit :=
  Graph.of_pure [1] [1; 2] (fun n => if Nat.eqb n 1 then [tt; tt] else [])
    (fun _ => 1) (fun _ => 2).

Definition repeated_ssa : Ssa.t nat unit nat expr (bits_guard word) :=
  Ssa.of_pure (Cfg.Make repeated_graph nat_encoding unit_encoding) nat_encoding [0]
    (fun _ => Param 1 0) (fun _ => 1) (fun _ => [0]) (fun _ => [])
    (fun _ => [(Equal (32%positive, 2%Z), [0])]).

Definition repeated_problem := Sparse.Make repeated_ssa values (fun _ => Cost.ret TAny).
Definition repeated_prepared :=
  Prepared.prepare nat_encoding (EdgeProjection.occurrence_graph repeated_graph).
Definition repeated_parents := Map.of_list positive_encoding [(2, 1)]%positive.
Definition repeated_tree := DomCheck.of_parents repeated_prepared repeated_parents.

Example repeated_graph_wf : graph_wf repeated_graph.
Proof.
  constructor.
  - change (NoDup [1; 2]); repeat (apply NoDup_cons; [cbn; intuition congruence|]).
    apply NoDup_nil.
  - intros n [<-|Hbad]; [left; reflexivity|contradiction].
  - intros n e Hin; unfold repeated_graph in Hin; rewrite Graph.of_pure_out in Hin.
    destruct (Nat.eqb n 1) eqn:Heq; [|contradiction].
    apply Nat.eqb_eq in Heq; subst n; reflexivity.
  - intros n e _ _; right; left; reflexivity.
Qed.

Example repeated_ready : Prepared.ready repeated_prepared.
Proof.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - apply EdgeProjection.occurrence_graph_wf; exact repeated_graph_wf.
  - intro n; rewrite EdgeProjection.occurrence_out; apply EdgeProjection.occurrences_nodup.
Qed.

Example repeated_tree_checked :
  DomCheck.check repeated_prepared repeated_parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_supplied_tree_exact : Dom.exact repeated_prepared repeated_tree.
Proof.
  apply DomCheck.check_sound; [exact repeated_ready|apply Map.wf_of_list|].
  exact repeated_tree_checked.
Qed.

Example repeated_edge_projection_conservative :
  dominating_edges_projected (make_dom_context repeated_prepared repeated_tree) 2 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_edge_refinement_keeps_stored_fact :
  refined_fact_projected repeated_problem (make_dom_context repeated_prepared repeated_tree)
    (fun _ => Some TAny) 2 0 = Some TAny.
Proof.
  vm_compute; reflexivity.
Qed.

(** A pure reader adapter has no internal lookup charge but still pays invocation overhead. *)
Definition ret_reader {N E V A} (sigma : unknown N E V -> option A) u :=
  Cost.ret (sigma u).

Definition charged_reader {N E V A} charge (sigma : unknown N E V -> option A) u :=
  Cost.tick charge ;; Cost.ret (sigma u).

Definition rejected_facts (u : unknown nat (nat * nat) nat) :=
  match u with UVal 1 => Some (number 0) | _ => Some TAny end.

Definition missing_facts (u : unknown nat (nat * nat) nat) :=
  match u with UVal 1 => None | _ => Some (@TAny point) end.

Definition equal_edge : nat * nat := (1, 2).

Example costed_refinement_retains_reader_charge :
  Cost.value (refine_fact_c equal_problem (charged_reader 7 unknown_facts) equal_edge 0
    (Some TAny)) = Some (number 2) /\
  Cost.ticks (refine_fact_c equal_problem (charged_reader 7 unknown_facts) equal_edge 0
    (Some TAny)) =
    (7 + Cost.ticks (refine_fact_c equal_problem (ret_reader unknown_facts) equal_edge 0%nat
      (Some TAny)))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example accepted_edge_retains_both_reader_charges :
  Cost.value (edge_feasible_c equal_problem (charged_reader 7 unknown_facts) equal_edge) = true /\
  Cost.ticks (edge_feasible_c equal_problem (charged_reader 7 unknown_facts) equal_edge) =
    (14 + Cost.ticks (edge_feasible_c equal_problem (ret_reader unknown_facts) equal_edge))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example edge_refinement_retains_initial_and_subject_reader_charges :
  Cost.value (refine_on_edge_c equal_problem (charged_reader 7 unknown_facts) equal_edge 0) =
    Some (number 2) /\
  Cost.ticks (refine_on_edge_c equal_problem (charged_reader 7 unknown_facts) equal_edge 0) =
    (14 + Cost.ticks
      (refine_on_edge_c equal_problem (ret_reader unknown_facts) equal_edge 0%nat))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example infeasible_edge_retains_both_reader_charges :
  Cost.value (edge_feasible_c equal_problem (charged_reader 7 rejected_facts) equal_edge) = false /\
  Cost.ticks (edge_feasible_c equal_problem (charged_reader 7 rejected_facts) equal_edge) =
    (14 + Cost.ticks (edge_feasible_c equal_problem (ret_reader rejected_facts) equal_edge))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example missing_subject_retains_snapshot_reader_charges :
  Cost.value (edge_feasible_c equal_problem (charged_reader 7 missing_facts) equal_edge) = false /\
  Cost.ticks (edge_feasible_c equal_problem (charged_reader 7 missing_facts) equal_edge) =
    (14 + Cost.ticks (edge_feasible_c equal_problem (ret_reader missing_facts) equal_edge))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example ordinary_fold_retains_initial_and_operand_reader_charges :
  Cost.value (refined_fact_c equal_problem equal_context (charged_reader 7 unknown_facts) 2 0) =
    Some (number 2) /\
  Cost.ticks (refined_fact_c equal_problem equal_context (charged_reader 7 unknown_facts) 2 0) =
    (14 + Cost.ticks
      (refined_fact_c equal_problem equal_context (ret_reader unknown_facts) 2%nat 0%nat))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example nonempty_fold_symbolic_reader_cost
    (reader : unknown nat (nat * nat) nat -> Cost.t (option (tagged point))) :
  Cost.ticks (refined_fact_c equal_problem equal_context reader 2 0) =
    (Cost.ticks (dominating_edges_in_c equal_context 2%nat) + 2 +
      Cost.ticks (reader (UVal 0%nat)) +
      Cost.ticks (refine_fact_c equal_problem reader equal_edge 0%nat
        (Cost.value (reader (UVal 0%nat)))))%N.
Proof.
  rewrite refined_fact_cost_equation.
  change (dominating_edges_in equal_context 2) with [equal_edge].
  rewrite ticks_fold_left_c_cons, ticks_fold_left_c_nil; lia.
Qed.

Definition lookup_facts : Map.t (unknown nat (nat * nat) nat) (option (tagged point)) :=
  Map.of_list (Sparse.key_enc equal_problem) [(UVal 0, Some TAny); (UVal 1, Some TAny)].

Definition map_reader :=
  lookup_c (Sparse.key_enc equal_problem)
    (Analysis.lat (sparse_analysis equal_problem 1)) lookup_facts.

(** Value-only adapters are comparison controls, not costed runtime lookup implementations. *)
Definition value_only_map_reader u := Cost.ret (Cost.value (map_reader u)).

Example map_reader_has_nonzero_lookup_cost :
  N.ltb 0 (Cost.ticks (map_reader (UVal 1))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example real_map_reader_refinement_cost :
  Cost.value (refine_fact_c equal_problem map_reader equal_edge 0 (Some TAny)) =
    Some (number 2) /\
  Cost.ticks (refine_fact_c equal_problem map_reader equal_edge 0 (Some TAny)) =
    (Cost.ticks (map_reader (UVal 1%nat)) +
      Cost.ticks
        (refine_fact_c equal_problem value_only_map_reader equal_edge 0%nat (Some TAny)))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example real_map_reader_feasibility_cost :
  Cost.value (edge_feasible_c equal_problem map_reader equal_edge) = true /\
  Cost.ticks (edge_feasible_c equal_problem map_reader equal_edge) =
    (Cost.ticks (map_reader (UVal 1%nat)) + Cost.ticks (map_reader (UVal 0%nat)) +
      Cost.ticks (edge_feasible_c equal_problem value_only_map_reader equal_edge))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition rejected_lookup_facts :=
  Map.set (Sparse.key_enc equal_problem) (UVal 1) (Some (number 0)) lookup_facts.

Definition rejected_map_reader :=
  lookup_c (Sparse.key_enc equal_problem)
    (Analysis.lat (sparse_analysis equal_problem 1)) rejected_lookup_facts.

Definition value_only_rejected_map_reader u := Cost.ret (Cost.value (rejected_map_reader u)).

Example real_map_reader_rejection_cost :
  Cost.value (edge_feasible_c equal_problem rejected_map_reader equal_edge) = false /\
  Cost.ticks (edge_feasible_c equal_problem rejected_map_reader equal_edge) =
    (Cost.ticks (rejected_map_reader (UVal 1%nat)) +
      Cost.ticks (rejected_map_reader (UVal 0%nat)) +
      Cost.ticks (edge_feasible_c equal_problem value_only_rejected_map_reader equal_edge))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example real_map_reader_fold_cost :
  Cost.value (refined_fact_c equal_problem equal_context map_reader 2 0) = Some (number 2) /\
  Cost.ticks (refined_fact_c equal_problem equal_context map_reader 2 0) =
    (Cost.ticks (map_reader (UVal 0%nat)) + Cost.ticks (map_reader (UVal 1%nat)) +
      Cost.ticks (refined_fact_c equal_problem equal_context value_only_map_reader 2%nat 0%nat))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition occurrence_prepared :=
  Prepared.prepare nat_encoding (EdgeProjection.occurrence_graph (Cfg.graph equal_cfg)).
Definition occurrence_tree := DomCheck.of_parents occurrence_prepared Fixtures.Diamond.parents.
Definition occurrence_context := make_dom_context occurrence_prepared occurrence_tree.

Example nonempty_occurrence_tree_checker_accepts :
  DomCheck.check occurrence_prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nonempty_projected_fold_preserves_value :
  dominating_edges_projected occurrence_context 2 = [(1, 2)] /\
  refined_fact_projected equal_problem occurrence_context unknown_facts 2 0 = Some (number 2).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example projected_fold_retains_initial_and_operand_reader_charges :
  Cost.value (refined_fact_projected_c equal_problem occurrence_context
    (charged_reader 7 unknown_facts) 2 0) = Some (number 2) /\
  Cost.ticks (refined_fact_projected_c equal_problem occurrence_context
    (charged_reader 7 unknown_facts) 2 0) =
    (14 + Cost.ticks (refined_fact_projected_c equal_problem occurrence_context
      (ret_reader unknown_facts) 2%nat 0%nat))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example projected_fold_symbolic_reader_cost
    (reader : unknown nat (nat * nat) nat -> Cost.t (option (tagged point))) :
  Cost.ticks (refined_fact_projected_c equal_problem occurrence_context reader 2 0) =
    (Cost.ticks (dominating_edges_projected_c occurrence_context 2%nat) + 2 +
      Cost.ticks (reader (UVal 0%nat)) +
      Cost.ticks (refine_fact_c equal_problem reader equal_edge 0%nat
        (Cost.value (reader (UVal 0%nat)))))%N.
Proof.
  rewrite refined_fact_projected_cost_equation.
  change (dominating_edges_projected occurrence_context 2) with [equal_edge].
  rewrite ticks_fold_left_c_cons, ticks_fold_left_c_nil; lia.
Qed.

Example projected_fold_real_map_reader_cost :
  Cost.value (refined_fact_projected_c equal_problem occurrence_context map_reader 2 0) =
    Some (number 2) /\
  Cost.ticks (refined_fact_projected_c equal_problem occurrence_context map_reader 2 0) =
    (Cost.ticks (map_reader (UVal 0%nat)) + Cost.ticks (map_reader (UVal 1%nat)) +
      Cost.ticks (refined_fact_projected_c equal_problem occurrence_context
        value_only_map_reader 2%nat 0%nat))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example unknown_block_refinement_identity :
  refined_fact equal_problem equal_context unknown_facts 9 0 = unknown_facts (UVal 0).
Proof.
  vm_compute; reflexivity.
Qed.

Definition disconnected_ssa :=
  Ssa.of_pure
    (Cfg.Make (Prepared.graph Fixtures.Unreachable.prepared) nat_encoding
      (codec_enc (pair_codec nat_codec nat_codec)))
    nat_encoding [0; 1] (Ssa.def equal_ssa) (Ssa.home equal_ssa)
    (Ssa.params equal_ssa) (Ssa.args equal_ssa) (Ssa.guards equal_ssa).

Definition disconnected_problem := Sparse.Make disconnected_ssa values (fun _ => Cost.ret TAny).
Definition disconnected_context :=
  make_dom_context Fixtures.Unreachable.prepared Fixtures.Unreachable.tree.

Example listed_unreachable_block_refinement_identity :
  dominating_edges_in disconnected_context 5 = [] /\
  refined_fact disconnected_problem disconnected_context unknown_facts 5 0 = unknown_facts (UVal 0).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example empty_query_retains_initial_reader_charge :
  Cost.ticks (refined_fact_c equal_problem equal_context (charged_reader 7 unknown_facts) 9 0) =
    (7 + Cost.ticks
      (refined_fact_c equal_problem equal_context (ret_reader unknown_facts) 9%nat 0%nat))%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example nonempty_guard_reader_invocation_cost :
  Cost.ticks (plans_c equal_problem equal_edge) =
    (1 + Cost.ticks (Ssa.guards_c equal_ssa equal_edge) +
      Cost.ticks (map_c (guard_plan_c equal_ssa) [(Equal (32%positive, 2%Z), [1%nat])]))%N.
Proof.
  vm_compute; reflexivity.
Qed.
