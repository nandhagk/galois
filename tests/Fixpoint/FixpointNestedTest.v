(** * Nested contributor multiplicity

    A side contributor can occur in several visited buckets during one stationary pass.
    For example, one constraint with two output keys occurs in both corresponding buckets.
    Builds on: FixpointNested, FixpointIndex, FixpointEval and LatticeHeight. *)

From Stdlib Require Import List Bool Arith NArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointCycles FixpointSolver FixpointKleene FixpointNested
  FixpointNestedProof FixpointNestedCost.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Definition nested_unit_lattice : lattice unit :=
  simple (fun _ _ => true) tt (fun _ _ => tt).

Definition nested_unit_laws : lattice_laws nested_unit_lattice.
Proof.
  constructor; intros; reflexivity.
Qed.

Definition nested_unit_lub : lub_laws nested_unit_lattice.
Proof.
  constructor; intros; reflexivity.
Qed.

Definition nested_unit_height : height nested_unit_lattice.
Proof.
  refine (@Height unit nested_unit_lattice (fun _ => True) (fun _ => 0) 0 _ _ _).
  - intros; lia.
  - intros; lia.
  - intros [] [] _ _ Hstrict; discriminate Hstrict.
Defined.

Definition nested_side_system : System.t nat nat unit :=
  System.Make [0] (fun _ => Cost.ret 0)
    (fun _ => Cost.ret (Query.Side 1 tt (Query.Ret tt))).

Definition nested_side_static : System.static nested_side_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret [1]).

Definition nested_side_static_laws : System.static_laws nested_side_static.
Proof.
  constructor; intros c s x Hin; exact Hin.
Qed.

Definition nested_side_analysis : Analysis.t nat nat unit :=
  Analysis.Make nat_encoding nat_encoding nested_unit_lattice
    nested_side_system nested_side_static (Policy.flat nat).

Definition nested_side_laws : Analysis.laws nested_side_analysis.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact nested_unit_laws.
  - exact nested_side_static_laws.
Qed.

Definition nested_side_terminates : Terminates.t nested_side_analysis.
Proof.
  refine (@Terminates.Finite nat nat unit nested_side_analysis (fun _ => True)
    nested_unit_height I _ _).
  - intros; exact I.
  - intros; exact I.
Defined.

Definition nested_side_code : Nested.code nat :=
  Nested.Visit 0 (Nested.Visit 1 Nested.End).

Example nested_side_code_vertices :
  Nested.vertices nested_side_code = [0; 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_code_depth : Nested.depth nested_side_code = 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_code_unique : NoDup (Nested.vertices nested_side_code).
Proof.
  vm_compute; constructor.
  - cbn; intros [Hbad|Hbad]; [discriminate|contradiction].
  - constructor; [cbn; tauto|constructor].
Qed.

Local Lemma nested_side_no_flow x y : ~ flows nested_side_static x y.
Proof.
  intros [c [_ [Hread _]]]; exact Hread.
Qed.

(** Target coverage, cycle cuts and unique vertices all allow this side-contributor fixture. *)
Theorem nested_side_code_ok : Nested.code_ok nested_side_analysis nested_side_code.
Proof.
  split.
  - intros c Hc; change (In c [0]) in Hc.
    destruct Hc as [<-|Hbad]; [vm_compute; auto|contradiction].
  - intros x Hcycle.
    induction Hcycle as [x y [Hflow _]|x y z Hxy IHxy Hyz IHyz].
    + exact (nested_side_no_flow x y Hflow).
    + exact IHxy.
Qed.

Definition nested_side_index :=
  index_system nat_encoding nested_side_system nested_side_static.

Example nested_side_buckets :
  (contributors_of nat_encoding nested_side_index 0,
    contributors_of nat_encoding nested_side_index 1) = ([0], [0]).
Proof.
  vm_compute; reflexivity.
Qed.

(** One pass following every contributor bucket evaluates the same row twice. *)
Definition nested_side_pass_rows :=
  flat_map (contributors_of nat_encoding nested_side_index) (Nested.vertices nested_side_code).

Example nested_side_pass_occurrences : nested_side_pass_rows = [0; 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_outputs :
  Eval.outputs nested_side_system 0 (fun _ => tt) = ([(0, tt); (1, tt)], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_stationary :
  Update.apply nat_encoding nested_unit_lattice (join_c nested_unit_lattice)
    (fst (Eval.outputs nested_side_system 0 (fun _ => tt))) Map.empty = (Map.empty, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_height_zero : bound nested_unit_height = 0.
Proof.
  vm_compute; reflexivity.
Qed.

(** The card's C-based evaluation bound is smaller than the stationary contributor pass. *)
Theorem nested_side_pass_exceeds_card_bound :
  length nested_side_pass_rows >
    length (System.constraints nested_side_system) *
      (1 + (Nested.depth nested_side_code + 1) * bound nested_unit_height * 2).
Proof.
  vm_compute; lia.
Qed.

Example nested_side_actual_pass :
  let ix := nested_side_index in
  let result := Cost.value (iterate (Nested.step_c nested_side_analysis nested_side_code ix
    (FinSet.of_list nat_encoding []) 0%N) 4 (Nested.start nested_side_code)) in
  match result with
  | inl s => (Nested.State.evals s, Nested.State.epoch s)
  | inr _ => (0%N, 1%N)
  end = (2%N, 0%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_solved :
  Nested.run nested_side_analysis nested_side_code 5 = Outcome.Solved Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Definition nested_repeated_system : System.t nat nat unit :=
  System.Make [0; 0] (fun _ => Cost.ret 0)
    (fun _ => Cost.ret (Query.Side 1 tt (Query.Side 1 tt (Query.Ret tt)))).

Definition nested_repeated_static : System.static nested_repeated_system :=
  System.Static (fun _ => Cost.ret [0; 0]) (fun _ => Cost.ret [1; 1]).

Example nested_repeated_buckets :
  let ix := index_system nat_encoding nested_repeated_system nested_repeated_static in
  (contributors_of nat_encoding ix 0, contributors_of nat_encoding ix 1,
    Nested.scheduled nat_encoding ix nested_side_code) = ([0; 0], [0; 0], 4).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_repeated_readers :
  let ix := index_system nat_encoding nested_repeated_system nested_repeated_static in
  (readers_of nat_encoding ix 0, readers_of nat_encoding ix 1) = ([0; 0], []).
Proof.
  vm_compute; reflexivity.
Qed.

Definition nested_bool_system : System.t nat nat bool :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then Query.Ask 0 (fun _ => Cost.ret (Query.Ret true))
      else Query.Ask 0 (fun b => Cost.ret (Query.Ret b)))).

Definition nested_bool_static : System.static nested_bool_system :=
  System.Static (fun _ => Cost.ret [0]) (fun _ => Cost.ret []).

Definition nested_bool_analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice nested_bool_system nested_bool_static
    (Policy.flat nat).

Definition nested_two_levels : Nested.code nat :=
  Nested.Component 0 (Nested.Component 1 Nested.End Nested.End) Nested.End.

Definition nested_siblings : Nested.code nat :=
  Nested.Component 0 Nested.End (Nested.Component 1 Nested.End Nested.End).

Definition nested_one_loop : Nested.code nat :=
  Nested.Component 0 (Nested.Visit 1 Nested.End) Nested.End.

Definition nested_observe (result : Outcome.t nat bool (assignment nat bool)) :=
  match result with
  | Outcome.Solved m => Some (map (lookup nat_encoding bool_lattice m) [0; 1])
  | _ => None
  end.

Example nested_nested_matches_kleene :
  nested_observe (Nested.run nested_bool_analysis nested_two_levels 100) =
    nested_observe (Solver.run Kleene.solver nested_bool_analysis 100) /\
  nested_observe (Nested.run nested_bool_analysis nested_two_levels 100) = Some [true; true].
Proof.
  vm_compute; auto.
Qed.

Example nested_sibling_loops_solved :
  nested_observe (Nested.run nested_bool_analysis nested_siblings 100) = Some [true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_single_loop_solved :
  nested_observe (Nested.run nested_bool_analysis nested_one_loop 100) = Some [true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_fuel_exhausted :
  match Nested.run nested_bool_analysis nested_two_levels 1 with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_omitted_target_rejected :
  Nested.run nested_bool_analysis (Nested.Visit 0 Nested.End) 100 =
    Outcome.Rejected Reason.Bad_wto.
Proof.
  vm_compute; reflexivity.
Qed.

Definition nested_single_system : System.t nat nat bool :=
  System.Make [0] (fun _ => Cost.ret 0) (fun _ => Cost.ret (Query.Ret false)).

Definition nested_single_static : System.static nested_single_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret []).

Definition nested_single_analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice nested_single_system nested_single_static
    (Policy.flat nat).

Example nested_single_vertex_one_pass :
  Nested.run nested_single_analysis (Nested.Visit 0 Nested.End) 3 = Outcome.Solved Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_delay_conversion_cost : Cost.ticks (Nested.delay_c 4) = 4%N.
Proof.
  vm_compute; reflexivity.
Qed.

Local Lemma nested_bool_code_valid p :
  Nested.vertices p = [0; 1] ->
  existsb (eqb nat_encoding 0) (Nested.heads p) = true ->
  Nested.code_ok nested_bool_analysis p.
Proof.
  intros Hvertices Hselected; split.
  - intros c Hc; change (In c [0; 1]) in Hc.
    rewrite Hvertices; destruct Hc as [<-|[<-|Hbad]];
      [vm_compute; auto|vm_compute; auto|contradiction].
  - set (selected := fun x => existsb (eqb nat_encoding x) (Nested.heads p)).
    assert (Hsource : forall x y, flows nested_bool_static x y -> selected x = true).
    { intros x y [c [Hc [Hread Hout]]].
      change (In x [0]) in Hread; destruct Hread as [<-|Hbad];
        [exact Hselected|contradiction]. }
    assert (Hpath : forall x y,
      clos_trans nat (fun x y => flows nested_bool_static x y /\ selected y = false) x y ->
      selected x = true /\ selected y = false).
    { intros x y Hrun; induction Hrun as [x y [Hflow Hno]|x y z Hxy IHxy Hyz IHyz].
      - split; [exact (Hsource x y Hflow)|exact Hno].
      - exact (conj (proj1 IHxy) (proj2 IHyz)). }
    intros x Hcycle; destruct (Hpath x x Hcycle); congruence.
Qed.

Example nested_one_loop_code_ok : Nested.code_ok nested_bool_analysis nested_one_loop.
Proof.
  apply nested_bool_code_valid; vm_compute; reflexivity.
Qed.

Example nested_two_levels_code_ok : Nested.code_ok nested_bool_analysis nested_two_levels.
Proof.
  apply nested_bool_code_valid; vm_compute; reflexivity.
Qed.

Example nested_siblings_code_ok : Nested.code_ok nested_bool_analysis nested_siblings.
Proof.
  apply nested_bool_code_valid; vm_compute; reflexivity.
Qed.

Example nested_missing_target_not_ok :
  ~ Nested.code_ok nested_bool_analysis (Nested.Visit 0 Nested.End).
Proof.
  intros [Hcover Hcuts]; specialize (Hcover 1 (or_intror (or_introl eq_refl))).
  vm_compute in Hcover; destruct Hcover as [Hbad|Hbad]; [discriminate|contradiction].
Qed.

Definition nested_side_bool_system : System.t nat nat bool :=
  System.Make [0; 1; 2] (fun c => Cost.ret c)
    (fun c => Cost.ret
      (if Nat.eqb c 0 then Query.Ask 0 (fun b => Cost.ret (Query.Ret b))
       else if Nat.eqb c 1 then
         Query.Ask 1 (fun b => Cost.ret (Query.Side 0 b (Query.Ret false)))
       else Query.Side 1 true (Query.Ret false))).

Definition nested_side_bool_static : System.static nested_side_bool_system :=
  System.Static
    (fun c => Cost.ret (if Nat.eqb c 0 then [0] else if Nat.eqb c 1 then [1] else []))
    (fun c => Cost.ret (if Nat.eqb c 0 then [] else if Nat.eqb c 1 then [0] else [1])).

Definition nested_side_bool_analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice nested_side_bool_system
    nested_side_bool_static (Policy.flat nat).

Definition nested_side_bool_code :=
  Nested.Component 0 Nested.End (Nested.Component 1 Nested.End (Nested.Visit 2 Nested.End)).

Example nested_side_requires_another_outer_pass :
  let ix := index_system nat_encoding nested_side_bool_system nested_side_bool_static in
  let hs := FinSet.of_list nat_encoding (Nested.heads nested_side_bool_code) in
  match Cost.value (iterate
    (Nested.step_c nested_side_bool_analysis nested_side_bool_code ix hs 0%N)
    20 (Nested.start nested_side_bool_code)) with
  | inl s => (Nested.State.pointer s, Nested.State.frames s,
      Nested.State.outer s, Nested.State.epoch s)
  | inr _ => (Nested.End, [], 0%N, 0%N)
  end = (Nested.End, [], 0%N, 2%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_side_finishes_after_clean_outer_pass :
  (match Nested.run nested_side_bool_analysis nested_side_bool_code 33 with
   | Outcome.OutOfFuel _ => true
   | _ => false
   end,
   nested_observe (Nested.run nested_side_bool_analysis nested_side_bool_code 34)) =
    (true, Some [true; true]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition nested_charged_system (target_charge rhs_charge continuation_charge : N)
    : System.t nat nat unit :=
  System.Make [0]
    (fun _ => Cost.tick target_charge ;; Cost.ret 0)
    (fun _ => Cost.tick rhs_charge ;;
      Cost.ret (Query.Ask 0 (fun _ => Cost.tick continuation_charge ;; Cost.ret (Query.Ret tt)))).

Definition nested_charged_static t r k : System.static (nested_charged_system t r k) :=
  System.Static (fun _ => Cost.ret [0]) (fun _ => Cost.ret []).

Definition nested_charged_analysis t r k :=
  Analysis.Make nat_encoding nat_encoding nested_unit_lattice (nested_charged_system t r k)
    (nested_charged_static t r k) (Policy.flat nat).

Example nested_callback_charges_retained :
  Cost.ticks (Nested.run_c (nested_charged_analysis 5 9 11) (Nested.Visit 0%nat Nested.End) 3) =
    (Cost.ticks (Nested.run_c (nested_charged_analysis 0 0 0)
      (Nested.Visit 0%nat Nested.End) 3) + 3 * 5 + 9 + 11)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Inductive nested_level : Type :=
  | NestedBottom
  | NestedMiddle
  | NestedTop.

Definition nested_level_rank (v : nested_level) : nat :=
  match v with
  | NestedBottom => 0
  | NestedMiddle => 1
  | NestedTop => 2
  end.

Definition nested_level_lattice : lattice nested_level :=
  LatticeCore.of_pure
    (fun x y => Nat.leb (nested_level_rank x) (nested_level_rank y)) NestedBottom
    (fun x y => if Nat.leb (nested_level_rank x) (nested_level_rank y) then y else x)
    (fun _ _ => NestedTop) (fun x _ => x).

Definition nested_level_system : System.t nat nat nested_level :=
  System.Make [0] (fun _ => Cost.ret 0) (fun _ => Cost.ret (Query.Ret NestedMiddle)).

Definition nested_level_static : System.static nested_level_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret []).

Definition nested_level_policy (delay : nat) (charge : N) : Policy.t nat :=
  Policy.Make (fun _ => Cost.ret 1%positive)
    (fun _ => Cost.tick charge ;; Cost.ret true) delay 0.

Definition nested_level_analysis delay charge :=
  Analysis.Make nat_encoding nat_encoding nested_level_lattice
    nested_level_system nested_level_static (nested_level_policy delay charge).

Definition nested_level_observe
    (result : Outcome.t nat nested_level (assignment nat nested_level)) :=
  match result with
  | Outcome.Solved m => Some (lookup nat_encoding nested_level_lattice m 0)
  | _ => None
  end.

Example nested_widen_only_selected_heads :
  (nested_level_observe (Nested.run (nested_level_analysis 0 0)
      (Nested.Component 0 Nested.End Nested.End) 100),
   nested_level_observe (Nested.run (nested_level_analysis 0 0)
      (Nested.Visit 0 Nested.End) 100)) = (Some NestedTop, Some NestedMiddle).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_widen_delay_counts_changed_updates :
  nested_level_observe (Nested.run (nested_level_analysis 1 0)
    (Nested.Component 0 Nested.End Nested.End) 100) = Some NestedMiddle.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_widen_policy_charge_retained :
  Cost.ticks (Nested.run_c (nested_level_analysis 0 7)
    (Nested.Component 0%nat Nested.End Nested.End) 100) =
  (Cost.ticks (Nested.run_c (nested_level_analysis 0 0)
    (Nested.Component 0%nat Nested.End Nested.End) 100) + 7)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition nested_empty_system : System.t nat nat unit :=
  System.Make [] (fun _ => Cost.ret 0) (fun _ => Cost.ret (Query.Ret tt)).

Definition nested_empty_static : System.static nested_empty_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret []).

Definition nested_empty_analysis :=
  Analysis.Make nat_encoding nat_encoding nested_unit_lattice
    nested_empty_system nested_empty_static (Policy.flat nat).

Example nested_empty_solved_in_one_step :
  Nested.run nested_empty_analysis Nested.End 1 = Outcome.Solved Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_empty_component_needs_administrative_fuel :
  (match Nested.run nested_empty_analysis (Nested.Component 99 Nested.End Nested.End) 3 with
   | Outcome.OutOfFuel _ => true
   | _ => false
   end,
   Nested.run nested_empty_analysis (Nested.Component 99 Nested.End Nested.End) 4) =
    (true, Outcome.Solved Map.empty).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_repeated_visit_occurrences :
  Nested.scheduled nat_encoding
    (index_system nat_encoding nested_repeated_system nested_repeated_static)
    (Nested.Visit 0 (Nested.Visit 0 Nested.End)) = 4.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_repeated_visits_accepted :
  Nested.code_ok nested_side_analysis (Nested.Visit 0 (Nested.Visit 0 Nested.End)).
Proof.
  split.
  - intros c Hc; change (In c [0]) in Hc.
    destruct Hc as [<-|Hbad]; [vm_compute; auto|contradiction].
  - intros x Hcycle.
    induction Hcycle as [x y [Hflow _]|x y z Hxy IHxy Hyz IHyz].
    + exact (nested_side_no_flow x y Hflow).
    + exact IHxy.
Qed.

Example nested_height_zero_budgets :
  (NestedCost.eval_budget nested_side_analysis nested_side_terminates nested_side_code,
    NestedCost.fuel_budget nested_side_analysis nested_side_terminates nested_side_code) = (2, 5).
Proof.
  vm_compute; reflexivity.
Qed.

(** The height-zero side fixture inhabits the universal fuel theorem's actual domain. *)
Theorem nested_side_fuel_contract :
  exists m, Nested.run nested_side_analysis nested_side_code 6 = Outcome.Solved m.
Proof.
  apply (NestedCost.nested_fuel_enough nested_side_analysis nested_side_laws
    nested_side_terminates ltac:(intro x; reflexivity) nested_side_code 6).
  - exact nested_side_code_ok.
  - vm_compute; lia.
Qed.
