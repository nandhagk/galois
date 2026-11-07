(** * Reference Datalog computations

    Fixtures discriminate recursive closure, completed negation and explicit failure outcomes.
    For example, nonlinear closure of a four-node chain contains six pairs.
    Builds on: DatalogSolveProof and FixpointCertified. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointAnalysis FixpointAnalyze
  FixpointSolver FixpointCertified FixpointKleene.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel DatalogRelation
  DatalogFire DatalogCompile DatalogCompileProof DatalogSolve DatalogSolveProof.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition nat_program (arity : nat -> nat) rs : program nat :=
  Program nat_encoding (fun p => Cost.ret (arity p)) rs.
Definition unary (p : nat) := Atom p [TVar 0].
Definition copy (h b : nat) := Rule (unary h) [LPos (unary b)].
Definition empty_program := nat_program (fun _ => 1) [].
Definition recursive_program := nat_program (fun _ => 1) [copy 0 1; copy 1 0].
Definition recursive_facts : list (ground_atom nat) := [(0, [2%positive])].
Definition negation_program := nat_program (fun _ => 1)
  [Rule (unary 2) [LPos (unary 1); LNeg (unary 3)]].
Definition negation_facts : list (ground_atom nat) :=
  [(1, [2%positive]); (1, [3%positive]); (3, [3%positive])].
Definition self_negation := nat_program (fun _ => 1)
  [Rule (Atom 0 [TConst 2%positive]) [LNeg (Atom 0 [TConst 2%positive])]].
Definition cycle_program := nat_program (fun _ => 1)
  [Rule (Atom 0 [TConst 2%positive]) [LNeg (Atom 1 [TConst 2%positive])];
   Rule (Atom 1 [TConst 2%positive]) [LPos (Atom 0 [TConst 2%positive])]].

Definition observe {P} (prog : program P) facts fuel queries :=
  match solve_program prog facts fuel with
  | Outcome.Solved db => Some (map (fun f => db_holds prog db (fst f) (snd f)) queries)
  | _ => None
  end.

Example empty_solver :
  observe empty_program [] 1%positive [(42, []); (0, [1%positive])] = Some [false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example recursive_solver :
  observe recursive_program recursive_facts 8%positive
    [(0, [2%positive]); (1, [2%positive]); (1, [3%positive])] = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example negation_solver :
  observe negation_program negation_facts 8%positive
    [(2, [2%positive]); (2, [3%positive])] = Some [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example failure_solver :
  solve_program self_negation [] 8%positive = Outcome.Rejected Reason.Bad_stratification /\
  solve_program cycle_program [] 8%positive = Outcome.Rejected Reason.Bad_stratification.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition chosen_strata {P} (prog : program P) :=
  match stratify prog with
  | Some st => st
  | None => Stratification (fun _ => Cost.ret 0) 1
  end.

Example empty_system :
  option_map count (stratify empty_program) = Some 1 /\
  stratum_constraints empty_program [] (chosen_strata empty_program) 0 = [].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example recursive_constraints :
  stratum_constraints recursive_program recursive_facts (chosen_strata recursive_program) 0 =
    [Constraint.FromRule 0 0; Constraint.FromRule 1 1; Constraint.FromFact 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example negation_strata :
  option_map (fun st => (level st 1, level st 2, level st 3, count st))
    (stratify negation_program) = Some (0, 1, 0, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Definition path x y := Atom 0 [TVar x; TVar y].
Definition nonlinear := nat_program (fun _ => 2)
  [Rule (path 0 2) [LPos (path 0 1); LPos (path 1 2)]].
Definition chain : list (ground_atom nat) :=
  [(0, [1%positive; 2%positive]); (0, [2%positive; 3%positive]);
   (0, [3%positive; 4%positive])].
Definition closure : list tuple :=
  [[1%positive; 2%positive]; [1%positive; 3%positive]; [1%positive; 4%positive];
   [2%positive; 3%positive]; [2%positive; 4%positive]; [3%positive; 4%positive]].

Definition relation_equals {P} (prog : program P) facts fuel p expected :=
  match solve_program prog facts fuel with
  | Outcome.Solved db =>
    FinSet.equal (set_raw (rel_of prog db p))
      (set_raw (set_of_list tuple_encoding expected))
  | _ => false
  end.

Example nonlinear_four_node_chain : relation_equals nonlinear chain 8%positive 0 closure = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition linear := nat_program (fun _ => 2)
  [Rule (Atom 1 [TVar 0; TVar 1]) [LPos (path 0 1)];
   Rule (Atom 1 [TVar 0; TVar 2])
     [LPos (Atom 1 [TVar 0; TVar 1]); LPos (path 1 2)]].

Example linear_four_node_chain : relation_equals linear chain 8%positive 1 closure = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example chain_out_of_fuel :
  match solve_program nonlinear chain 1%positive with Outcome.OutOfFuel _ => true | _ => false end
    = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition reachability := nat_program (fun p => if Nat.eqb p 0 then 2 else 1)
  [Rule (unary 2) [LPos (unary 1)];
   Rule (Atom 2 [TVar 1]) [LPos (unary 2); LPos (Atom 0 [TVar 0; TVar 1])];
   Rule (unary 4) [LPos (unary 3); LNeg (unary 2)]].
Definition reachability_facts : list (ground_atom nat) :=
  chain ++ [(1, [1%positive]); (3, [1%positive]); (3, [2%positive]); (3, [3%positive]);
    (3, [4%positive]); (3, [5%positive])].

Example reachable_and_unreachable :
  relation_equals reachability reachability_facts 8%positive 2
    [[1%positive]; [2%positive]; [3%positive]; [4%positive]] = true /\
  relation_equals reachability reachability_facts 8%positive 4 [[5%positive]] = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example fact_only :
  relation_equals empty_program [(7, []); (7, []); (8, [3%positive])]
    2%positive 7 [[]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition ground_rule := Rule (Atom 0 [TConst 5%positive]) [].
Example ground_rule_without_facts :
  relation_equals (nat_program (fun _ => 1) [ground_rule]) [] 2%positive 0
    [[5%positive]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nullary_rule :
  relation_equals (nat_program (fun _ => 0) [Rule (Atom 0 []) []]) [] 2%positive 0 [[]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition repeated_rule := Rule (unary 1)
  [LPos (Atom 0 [TVar 0; TVar 0]); LPos (Atom 2 [TVar 0; TConst 3%positive])].
Definition repeated_program :=
  nat_program (fun p => if Nat.eqb p 1 then 1 else 2) [repeated_rule].
Definition repeated_facts : list (ground_atom nat) :=
  [(0, [2%positive; 2%positive]); (0, [2%positive; 3%positive]);
   (0, [3%positive; 3%positive]); (2, [2%positive; 3%positive]);
   (2, [3%positive; 2%positive])].

Example repeated_and_constant :
  relation_equals repeated_program repeated_facts 4%positive 1 [[2%positive]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition rows_env := facts_at_c repeated_program repeated_facts.

Example rejects_short_unequal_and_constant :
  let prog := repeated_program in
  (FinSet.is_empty (set_raw (fire_rule prog repeated_rule
      (fun _ => Cost.ret (set_of_list tuple_encoding [[2%positive]])))),
   FinSet.is_empty (set_raw (fire_rule prog repeated_rule
      (fun _ => Cost.ret (set_of_list tuple_encoding [[2%positive; 3%positive]])))),
   FinSet.is_empty (set_raw (fire_rule prog repeated_rule
      (fun _ => Cost.ret (set_of_list tuple_encoding [[2%positive; 2%positive]]))))) =
    (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example compile_missing_rule :
  let sys := stratum_system empty_program [] (chosen_strata empty_program)
    (fun _ => Cost.ret (bot relation_lattice)) 0 in
  (Query.reads (System.rhs sys (Constraint.FromRule 99 1)) (fun _ => bot relation_lattice),
   member [] (Query.eval (System.rhs sys (Constraint.FromRule 99 1))
     (fun _ => bot relation_lattice))) = ([], false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition bad_solver : Solver.t nat (Constraint.t nat) relation :=
  Solver.Make (fun _ _ => Cost.ret (Outcome.Solved Map.empty)).

Example certified_bad_solver :
  match analyze_with bad_solver
    (stratum_analysis empty_program recursive_facts (chosen_strata empty_program)
      (fun _ => Cost.ret (bot relation_lattice)) 0) 2%positive with
  | Outcome.Rejected Reason.Check_failed => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition aliased : program bool := Program (BaseEncoding.of_pure (fun _ => 1%positive))
  (fun _ => Cost.ret 0) [].
Definition lawful : program bool := Program bool_encoding (fun _ => Cost.ret 0) [].

Example aliased_program_wf : program_wf aliased [(false, [])].
Proof.
  split; [intros r Hbad; contradiction |].
  intros f [<- | Hbad]; [reflexivity | contradiction].
Qed.

Example aliased_lookup_and_lawful_control :
  (observe aliased [(false, [])] 2%positive [(false, []); (true, [])],
   observe lawful [(false, [])] 2%positive [(false, []); (true, [])]) =
    (Some [true; true], Some [true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example aliased_has_no_encoding_law : ~ encoding_laws (penc aliased).
Proof.
  intro HE; pose proof (encode_injective HE false true eq_refl) as Hbad; discriminate.
Qed.

Example aliased_source_distinguishes_true : ~ least_model aliased [(false, [])] (true, []).
Proof.
  intro Hmodel.
  change (False \/ derives aliased [(false, [])] (chosen_strata aliased) 0
    (fun _ => False) (true, [])) in Hmodel.
  destruct Hmodel as [Hbad | Hderive]; [contradiction |].
  remember (true, []) as f eqn:Hf in Hderive; revert Hf.
  destruct Hderive as [f Hfact Hl | r sigma Hrule Hl Hlow Hsame Hneg]; intro Hf.
  - destruct Hfact as [Hbad | Hbad]; [rewrite <- Hbad in Hf; discriminate | contradiction].
  - contradiction.
Qed.

Example matching_cost_is_positive :
  N.ltb 0 (Cost.ticks (fire_rule_c repeated_program repeated_rule rows_env)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example four_node_chain_needs_stationary_probe :
  (match solve_program nonlinear chain 3%positive with
   | Outcome.OutOfFuel _ => true
   | _ => false
   end,
   relation_equals nonlinear chain 4%positive 0 closure) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition triangle_atoms : list (literal nat) :=
  [LPos (Atom 1 [TVar 0; TVar 1]);
   LPos (Atom 2 [TVar 1; TVar 2]);
   LPos (Atom 3 [TVar 0; TVar 2])].
Definition triangle_rule := Rule (unary 0) triangle_atoms.
Definition triangle_reversed := Rule (unary 0) (rev triangle_atoms).
Definition join_facts : list (ground_atom nat) :=
  [(1, [2%positive; 2%positive]); (1, [2%positive; 2%positive]);
   (1, [2%positive; 3%positive]); (1, [3%positive; 3%positive]);
   (1, [4%positive; 4%positive]); (2, [2%positive; 5%positive]);
   (2, [3%positive; 6%positive]); (3, [2%positive; 5%positive]);
   (3, [4%positive; 6%positive]); (4, [3%positive; 3%positive])].
Definition join_program rs := nat_program (fun p => if Nat.eqb p 0 then 1 else 2) rs.
Definition join_env := facts_at_c (join_program []) join_facts.

Example triangle_orders :
  (FinSet.elements (set_raw (fire_rule (join_program [triangle_rule]) triangle_rule join_env)),
   FinSet.elements (set_raw
     (fire_rule (join_program [triangle_reversed]) triangle_reversed join_env))) =
    ([[2%positive]], [[2%positive]]).
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_seeds_and_repeated_body :
  observe (nat_program (fun _ => 1)
    [Rule (unary 1) [LPos (unary 0); LPos (unary 0)]])
    [(0, [2%positive]); (0, [2%positive])] 4%positive
    [(1, [2%positive]); (1, [3%positive])] = Some [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example ground_positive_literals :
  let r := Rule (Atom 0 [TConst 2%positive])
    [LPos (Atom 1 [TConst 2%positive; TConst 2%positive])] in
  let missing := Rule (Atom 0 [TConst 2%positive])
    [LPos (Atom 1 [TConst 2%positive; TConst 4%positive])] in
  (FinSet.elements (set_raw (fire_rule (join_program [r]) r join_env)),
   FinSet.elements (set_raw (fire_rule (join_program [missing]) missing join_env))) =
    ([[2%positive]], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example nullary_positive :
  let r := Rule (Atom 0 []) [LPos (Atom 1 [])] in
  relation_equals (nat_program (fun _ => 0) [r]) [(1, [])] 4%positive 0 [[]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ground_negative_literals :
  let r := Rule (Atom 0 [TConst 2%positive])
    [LNeg (Atom 4 [TConst 3%positive; TConst 3%positive])] in
  (FinSet.elements (set_raw (fire_rule (join_program [r]) r
      (fun _ => Cost.ret (bot relation_lattice)))),
   FinSet.elements (set_raw (fire_rule (join_program [r]) r join_env))) =
    ([[2%positive]], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example completed_recursive_lower_negation :
  observe (nat_program (fun _ => 1)
    [copy 1 0;
     Rule (unary 2) [LPos (unary 0); LNeg (unary 1)];
     Rule (unary 3) [LPos (unary 0); LNeg (unary 4)]])
    [(0, [2%positive])] 8%positive
    [(1, [2%positive]); (2, [2%positive]); (3, [2%positive])] = Some [true; false; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example foreign_constant_firing_is_unrestricted :
  let r := Rule (unary 0) [LPos (unary 1)] in
  FinSet.elements (set_raw (fire_rule (nat_program (fun _ => 1) [r]) r
    (fun _ => Cost.ret (set_of_list tuple_encoding [[9%positive]])))) = [[9%positive]].
Proof.
  vm_compute; reflexivity.
Qed.

Example compile_atom_order_and_fixed_lower :
  let st := chosen_strata negation_program in
  let lower := fun p => Cost.ret (facts_at negation_program negation_facts p) in
  let sys := stratum_system negation_program negation_facts st lower 1 in
  (Query.reads (System.rhs sys (Constraint.FromRule 0 2)) (fun _ => bot relation_lattice),
   FinSet.elements (set_raw (Query.eval (System.rhs sys (Constraint.FromRule 0 2))
     (fun _ => bot relation_lattice)))) = ([], [[2%positive]]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition outcome_tag {X A R} (outcome : Outcome.t X A R) :=
  match outcome with
  | Outcome.Solved _ => 0
  | Outcome.OutOfFuel _ => 1
  | Outcome.Rejected _ => 2
  end.

Definition empty_analysis := stratum_analysis empty_program [] (chosen_strata empty_program)
  (fun _ => Cost.ret (bot relation_lattice)) 0.

Example finish_stratum_invocation_controls :
  let raw := Solver.run_c Kleene.solver empty_analysis 1%positive in
  let success := finish_stratum_c empty_analysis 1%positive (Outcome.Solved tt) in
  let exhausted := finish_stratum_c empty_analysis 1%positive
    (Outcome.OutOfFuel Map.empty : Outcome.t nat relation unit) in
  let rejected := finish_stratum_c empty_analysis 1%positive
    (Outcome.Rejected Reason.Check_failed : Outcome.t nat relation unit) in
  ((Cost.ticks success, outcome_tag (Cost.value success)),
   (Cost.ticks exhausted, outcome_tag (Cost.value exhausted)),
   (Cost.ticks rejected, outcome_tag (Cost.value rejected))) =
  (((1 + Cost.ticks raw)%N, 0), (0%N, 1), (0%N, 2)).
Proof.
  vm_compute; reflexivity.
Qed.

Example solved_stratum_full_charge :
  let st := chosen_strata empty_program in
  let lower := fun _ : nat => Cost.ret (bot relation_lattice) in
  let computed := solve_stratum_c empty_program [] st lower 0 1%positive in
  (outcome_tag (Cost.value computed), Cost.ticks computed) =
  (0, (Cost.ticks (stratum_analysis_c empty_program [] st lower 0) +
    Cost.ticks (analyze_ref_c empty_analysis 1%positive) + 1 +
    Cost.ticks (Solver.run_c Kleene.solver empty_analysis 1%positive))%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example exhausted_stratum_skips_second_charge :
  let st := chosen_strata empty_program in
  let lower := fun _ : nat => Cost.ret (bot relation_lattice) in
  let a := stratum_analysis empty_program recursive_facts st lower 0 in
  let computed := solve_stratum_c empty_program recursive_facts st lower 0 1%positive in
  (outcome_tag (analyze_ref a 1%positive), outcome_tag (Cost.value computed), Cost.ticks computed) =
  (1, 1, (Cost.ticks (stratum_analysis_c empty_program recursive_facts st lower 0) +
    Cost.ticks (analyze_ref_c a 1%positive))%N).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ordered_read_rule := Rule (unary 4)
  [LPos (unary 2); LPos (unary 0); LPos (unary 1); LPos (unary 2); LPos (unary 1);
   LNeg (unary 3)].
Definition ordered_read_program := nat_program (fun _ => 1) [ordered_read_rule].
Definition ordered_read_strata := Stratification
  (fun p : nat => Cost.ret (if Nat.eqb p 0 || Nat.eqb p 3 then 0 else 1)) 2.
Definition ordered_read_lower := facts_at_c ordered_read_program
  [(0, [2%positive]); (0, [3%positive]); (3, [3%positive])].
Definition ordered_read_assignment (p : nat) : relation :=
  if Nat.eqb p 1 || Nat.eqb p 2
  then set_of_list tuple_encoding [[2%positive]; [3%positive]]
  else bot relation_lattice.

Example repeated_same_level_trace_and_fixed_lower :
  let sys := stratum_system ordered_read_program [] ordered_read_strata ordered_read_lower 1 in
  let summary := stratum_static ordered_read_program [] ordered_read_strata ordered_read_lower 1 in
  let row := Constraint.FromRule 0 4 in
  (System.deps summary row, Query.reads (System.rhs sys row) ordered_read_assignment,
   FinSet.elements (set_raw (Query.eval (System.rhs sys row) ordered_read_assignment))) =
  ([2; 1; 2; 1], [2; 1; 2; 1], [[2%positive]]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition independent_atoms : list (atom nat) :=
  [Atom 1 [TVar 0]; Atom 2 [TVar 1]].
Definition independent_program := nat_program (fun _ => 1) [].
Definition independent_environment := facts_at_c independent_program
  [(1, [1%positive]); (1, [2%positive]); (2, [3%positive]); (2, [4%positive])].
Definition raw_binding_pairs ps :=
  map (fun b => (binding_value b 0, binding_value b 1))
    (join_positive_ref ps independent_environment [[]]).

Example independent_raw_binding_order :
  (raw_binding_pairs independent_atoms, raw_binding_pairs (rev independent_atoms)) =
  ([(2%positive, 4%positive); (2%positive, 3%positive);
    (1%positive, 4%positive); (1%positive, 3%positive)],
   [(2%positive, 4%positive); (1%positive, 4%positive);
    (2%positive, 3%positive); (1%positive, 3%positive)]).
Proof.
  vm_compute; reflexivity.
Qed.

Example independent_final_relations_agree :
  let forward := Rule (Atom 0 [TVar 0; TVar 1]) (map LPos independent_atoms) in
  let backward := Rule (Atom 0 [TVar 0; TVar 1]) (map LPos (rev independent_atoms)) in
  FinSet.equal
    (set_raw (fire_rule independent_program forward independent_environment))
    (set_raw (fire_rule independent_program backward independent_environment)) = true.
Proof.
  vm_compute; reflexivity.
Qed.
