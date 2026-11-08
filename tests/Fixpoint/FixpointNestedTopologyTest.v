(** * Semantic nested and sibling feedback

    Three-level feedback exposes outer and inner cycles, and unbounded siblings widen separately.
    For example, changing the outer input to top changes the inner row's result from middle to top.
    Builds on: FixpointNestedClientsTest and the public nested and reference solvers. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointAnalysis
  FixpointSolver FixpointKleene FixpointNested FixpointNestedWiden.
From Galois.Tests.Fixpoint Require Import FixpointNestedTest FixpointNestedClientsTest.
Import List.ListNotations Cost.Notations NestedClients.

Local Open Scope nat_scope.

Module NestedTopology.

Definition level_system : System.t nat nat nested_level :=
  System.Make [0; 1; 2] (fun c => Cost.ret c)
    (fun c => Cost.ret
      (if Nat.eqb c 0 then Query.Ask 1 (fun b => Cost.ret (Query.Ret b))
       else if Nat.eqb c 1 then Query.Ask 2 (fun b => Cost.ret (Query.Ret b))
       else Query.Ask 0 (fun a => Cost.ret (Query.Ask 2 (fun b =>
         Cost.step ;;
         let* combined := join_c nested_level_lattice a b in
         Cost.step ;;
         let* seeded := join_c nested_level_lattice NestedMiddle combined in
         Cost.ret (Query.Ret seeded)))))).

Definition level_static : System.static level_system :=
  System.Static
    (fun c => Cost.ret (if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [2] else [0; 2]))
    (fun _ => Cost.ret []).

Definition level_analysis (policy : Policy.t nat) :=
  Analysis.Make nat_encoding nat_encoding nested_level_lattice level_system level_static policy.

Definition level_observe (result : Outcome.t nat nested_level (assignment nat nested_level)) :=
  match result with
  | Outcome.Solved m => Some (map (lookup nat_encoding nested_level_lattice m) [0; 1; 2])
  | _ => None
  end.

Example both_feedback_edges_affect_inner_results :
  (Query.eval (System.rhs level_system 2) (fun _ => NestedBottom),
    Query.eval (System.rhs level_system 2)
      (fun x => if Nat.eqb x 0 then NestedTop else NestedBottom),
    Query.eval (System.rhs level_system 2)
      (fun x => if Nat.eqb x 2 then NestedTop else NestedBottom)) =
    (NestedMiddle, NestedTop, NestedTop).
Proof.
  vm_compute; reflexivity.
Qed.

Example semantic_nested_joining_matches_reference :
  (level_observe (Nested.run (level_analysis (Policy.flat nat)) feedback_code 256),
    level_observe (Solver.run Kleene.solver (level_analysis (Policy.flat nat)) 256)) =
    (Some [NestedMiddle; NestedMiddle; NestedMiddle],
      Some [NestedMiddle; NestedMiddle; NestedMiddle]).
Proof.
  vm_compute; reflexivity.
Qed.

Example semantic_nested_full_assignment_matches_reference :
  Nested.run (level_analysis (Policy.flat nat)) feedback_code 256 =
    Solver.run Kleene.solver (level_analysis (Policy.flat nat)) 256.
Proof.
  vm_compute; reflexivity.
Qed.

Definition immediate_policy : Policy.t nat :=
  Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret true) 0 0.

Example semantic_nested_heads_really_widen :
  level_observe (Nested.run (level_analysis immediate_policy) feedback_code 256) =
    Some [NestedTop; NestedTop; NestedTop].
Proof.
  vm_compute; reflexivity.
Qed.

Example semantic_nested_code_ok policy :
  Nested.code_ok (level_analysis policy) feedback_code.
Proof.
  exact nested_feedback_code_ok.
Qed.

Definition independent_system : System.t nat nat unbounded_value :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (Query.Ask c (fun v => Cost.ret (Query.Ret (increment v))))).

Definition independent_static : System.static independent_system :=
  System.Static (fun c => Cost.ret [c]) (fun _ => Cost.ret []).

Definition independent_analysis :=
  Analysis.Make nat_encoding nat_encoding unbounded_lattice independent_system independent_static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret true) 1 0).

Definition independent_laws : Analysis.laws independent_analysis.
Proof.
  constructor; try exact nat_encoding_laws; [exact unbounded_laws|].
  constructor; intros c s x Hin; exact Hin.
Qed.

Definition independent_invariant :
  NestedWiden.invariant_laws independent_analysis (fun _ => True).
Proof.
  constructor; intros; exact I.
Qed.

Definition independent_selected : NestedWiden.all_selected independent_analysis sibling_code.
Proof.
  intros x Hx; change (In x [0; 1]) in Hx.
  destruct Hx as [Hx|[Hx|Hbad]]; [subst x|subst x|contradiction]; vm_compute; reflexivity.
Qed.

Example independent_unbounded_code_ok : Nested.code_ok independent_analysis sibling_code.
Proof.
  exact independent_sibling_code_ok.
Qed.

Example first_unbounded_sibling_stabilizes_before_second :
  let ix := index_system nat_encoding independent_system independent_static in
  let hs := FinSet.of_list nat_encoding (Nested.heads sibling_code) in
  match Cost.value (iterate (Nested.step_c independent_analysis sibling_code ix hs 1%N)
      10 (Nested.start sibling_code)) with
  | inl s => (Nested.State.pointer s,
      map (lookup nat_encoding unbounded_lattice (Nested.State.values s)) [0; 1])
  | inr _ => (Nested.End, [])
  end = (Nested.Component 1 Nested.End Nested.End, [Infinity; Finite 0]).
Proof.
  vm_compute; reflexivity.
Qed.

Example both_unbounded_siblings_need_and_finish_widening :
  match Nested.run independent_analysis sibling_code 128 with
  | Outcome.Solved m => map (lookup nat_encoding unbounded_lattice m) [0; 1]
  | _ => []
  end = [Infinity; Infinity].
Proof.
  vm_compute; reflexivity.
Qed.

Example joining_only_siblings_cannot_finish_that_prefix :
  match Solver.run Kleene.solver independent_analysis 16 with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Both independent semantic cycles instantiate the derived rank-and-delay fuel theorem. *)
Theorem independent_widening_fuel_client :
  exists m, Nested.run independent_analysis sibling_code 128 = Outcome.Solved m.
Proof.
  apply (NestedWiden.fuel_enough independent_analysis sibling_code independent_laws
    independent_selected unbounded_wrank independent_invariant 128 independent_unbounded_code_ok).
  vm_compute; lia.
Qed.

End NestedTopology.
Import NestedTopology.
