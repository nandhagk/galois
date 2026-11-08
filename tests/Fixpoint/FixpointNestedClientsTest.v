(** * Nested feedback and delayed-widening clients

    These clients distinguish feedback topology from merely nested syntax.
    For example, an ascending natural-number loop needs widening after two changed joins.
    Builds on: FixpointNestedWiden, FixpointNestedPrimitive and the public solver contracts. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointCycles FixpointSolver FixpointKleene FixpointNested
  FixpointNestedCost FixpointNestedWiden FixpointNestedPrimitive FixpointNestedCredit
  FixpointNestedDebt FixpointWorklistCost FixpointWorklistWiden.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module NestedClients.

Definition feedback_system : System.t nat nat bool :=
  System.Make [0; 1; 2] (fun c => Cost.ret c)
    (fun c => Cost.ret
      (if Nat.eqb c 0 then Query.Ask 1 (fun b => Cost.ret (Query.Ret b))
       else if Nat.eqb c 1 then Query.Ask 2 (fun b => Cost.ret (Query.Ret b))
       else Query.Ask 0 (fun a => Cost.ret
         (Query.Ask 2 (fun b => Cost.ret (Query.Ret (true || a || b))))))).

Definition feedback_static : System.static feedback_system :=
  System.Static
    (fun c => Cost.ret (if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [2] else [0; 2]))
    (fun _ => Cost.ret []).

Definition feedback_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice feedback_system feedback_static
    (Policy.flat nat).

Definition feedback_code :=
  Nested.Component 1 (Nested.Visit 0 (Nested.Component 2 Nested.End Nested.End)) Nested.End.

Definition sibling_system : System.t nat nat bool :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (Query.Ask c (fun _ => Cost.ret (Query.Ret true)))).

Definition sibling_static : System.static sibling_system :=
  System.Static (fun c => Cost.ret [c]) (fun _ => Cost.ret []).

Definition sibling_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice sibling_system sibling_static
    (Policy.flat nat).

Definition sibling_code :=
  Nested.Component 0 Nested.End (Nested.Component 1 Nested.End Nested.End).

Definition bool_observe xs (result : Outcome.t nat bool (assignment nat bool)) :=
  match result with
  | Outcome.Solved m => Some (map (lookup nat_encoding bool_lattice m) xs)
  | _ => None
  end.

Example nested_feedback_matches_reference :
  (bool_observe [0; 1; 2] (Nested.run feedback_analysis feedback_code 100),
    bool_observe [0; 1; 2] (Solver.run Kleene.solver feedback_analysis 100)) =
    (Some [true; true; true], Some [true; true; true]).
Proof.
  vm_compute; reflexivity.
Qed.

Example independent_sibling_cycles_solved :
  bool_observe [0; 1] (Nested.run sibling_analysis sibling_code 100) = Some [true; true].
Proof.
  vm_compute; reflexivity.
Qed.

(** A residual path must start at a selected source and finish at an unselected target. *)
Local Lemma source_cut {X} (R : X -> X -> Prop) (selected : X -> bool) :
  (forall x y, R x y -> selected y = false -> selected x = true) ->
  forall x, ~ clos_trans X (fun x y => R x y /\ selected y = false) x x.
Proof.
  intros Hsource x Hcycle.
  assert (Hpath : forall x y, clos_trans X (fun x y => R x y /\ selected y = false) x y ->
    selected x = true /\ selected y = false).
  { intros s t Hp; induction Hp as [s t [Hedge Hno]|s t u Hst IHst Htu IHtu].
    - split; [exact (Hsource s t Hedge Hno)|exact Hno].
    - exact (conj (proj1 IHst) (proj2 IHtu)). }
  destruct (Hpath x x Hcycle); congruence.
Qed.

Example nested_feedback_code_ok : Nested.code_ok feedback_analysis feedback_code.
Proof.
  split.
  - intros c Hc; change (In c [0; 1; 2]) in Hc.
    destruct Hc as [<-|[<-|[<-|Hbad]]]; try contradiction; vm_compute; auto.
  - intro start; apply (source_cut (flows feedback_static)
      (fun x => existsb (eqb nat_encoding x) (Nested.heads feedback_code))).
    intros x y [c [Hc [Hread Hout]]] Hno.
    change (In c [0; 1; 2]) in Hc.
    destruct Hout as [Hy|Hbad]; [subst y|exfalso; exact Hbad].
    destruct Hc as [<-|[<-|[<-|Hbad]]]; try contradiction.
    + change (In x [1]) in Hread; destruct Hread as [<-|Hbad];
        [vm_compute; reflexivity|contradiction].
    + vm_compute in Hno; discriminate.
    + vm_compute in Hno; discriminate.
Qed.

Example independent_sibling_code_ok : Nested.code_ok sibling_analysis sibling_code.
Proof.
  split.
  - intros c Hc; change (In c [0; 1]) in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction; vm_compute; auto.
  - intro start; apply (source_cut (flows sibling_static)
      (fun x => existsb (eqb nat_encoding x) (Nested.heads sibling_code))).
    intros x y [c [Hc [Hread Hout]]] Hno.
    destruct Hout as [Hy|Hbad]; [subst y|exfalso; exact Hbad].
    change (In c [0; 1]) in Hc; destruct Hc as [<-|[<-|Hbad]]; try contradiction;
      vm_compute in Hno; discriminate.
Qed.

Inductive unbounded_value : Type :=
  | Finite (n : nat)
  | Infinity.

Definition unbounded_le x y :=
  match x, y with
  | _, Infinity => true
  | Infinity, Finite _ => false
  | Finite n, Finite m => Nat.leb n m
  end.

Definition unbounded_join x y :=
  match x, y with
  | Finite n, Finite m => Finite (Nat.max n m)
  | _, _ => Infinity
  end.

Definition unbounded_lattice : lattice unbounded_value :=
  LatticeCore.of_pure unbounded_le (Finite 0) unbounded_join
    (fun _ _ => Infinity) (fun x _ => x).

Definition unbounded_laws : lattice_laws unbounded_lattice.
Proof.
  constructor.
  - intros [n|]; cbn; [apply Nat.leb_refl|reflexivity].
  - intros [n|] [m|] [k|]; cbn; intros Hnm Hmk; try discriminate; try reflexivity;
      apply Nat.leb_le; apply Nat.leb_le in Hnm, Hmk; lia.
  - intros [n|]; reflexivity.
  - intros [n|] [m|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_l.
  - intros [n|] [m|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_r.
  - intros [] []; reflexivity.
  - intros [] []; reflexivity.
  - intros x y H; destruct x; cbn; [apply Nat.leb_refl|reflexivity].
  - intros x y H; exact H.
Qed.

Definition unbounded_rank x :=
  match x with
  | Finite _ => 1
  | Infinity => 0
  end.

Definition unbounded_wrank : widening_rank_on unbounded_lattice (fun _ => True).
Proof.
  refine (@WideningRank unbounded_value unbounded_lattice (fun _ => True)
    unbounded_rank 1 _ _ _).
  - intros []; cbn; lia.
  - intros [] [] _ _ H; cbn; lia.
  - intros [] [] _ _ H; cbn in H |- *; try discriminate; lia.
Defined.

Definition increment x :=
  match x with
  | Finite n => Finite (S n)
  | Infinity => Infinity
  end.

Definition delayed_system : System.t nat nat unbounded_value :=
  System.Make [0] (fun _ => Cost.ret 0)
    (fun _ => Cost.ret (Query.Ask 0 (fun v => Cost.ret (Query.Ret (increment v))))).

Definition delayed_static : System.static delayed_system :=
  System.Static (fun _ => Cost.ret [0]) (fun _ => Cost.ret []).

Definition delayed_analysis :=
  Analysis.Make nat_encoding nat_encoding unbounded_lattice delayed_system delayed_static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret true) 2 0).

Definition delayed_code := Nested.Component 0 Nested.End Nested.End.

Definition delayed_laws : Analysis.laws delayed_analysis.
Proof.
  constructor; try exact nat_encoding_laws; [exact unbounded_laws|].
  constructor; intros c s x Hin; exact Hin.
Qed.

Definition delayed_invariant : NestedWiden.invariant_laws delayed_analysis (fun _ => True).
Proof.
  constructor; intros; exact I.
Qed.

Definition delayed_all_selected : NestedWiden.all_selected delayed_analysis delayed_code.
Proof.
  intros x Hx; change (In x [0]) in Hx; destruct Hx as [<-|Hbad];
    [vm_compute; reflexivity|contradiction].
Qed.

Definition delayed_code_ok : Nested.code_ok delayed_analysis delayed_code.
Proof.
  split.
  - intros c Hc; vm_compute; auto.
  - intro start; apply (source_cut (flows delayed_static)
      (fun x => existsb (eqb nat_encoding x) (Nested.heads delayed_code))).
    intros x y [c [Hc [Hread Hout]]] Hno.
    destruct Hout as [Hy|Hbad]; [subst y|exfalso; exact Hbad].
    vm_compute in Hno; discriminate.
Qed.

(** Finite iterates have strictly larger finite successors, so joins cannot stabilize. *)
Theorem unbounded_join_never_stationary n :
  leb unbounded_lattice (increment (Finite n)) (Finite n) = false.
Proof.
  change (Nat.leb (S n) n = false); apply Nat.leb_gt; lia.
Qed.

(** The fixture carrier admits no global finite-height dictionary for its actual join. *)
Theorem unbounded_has_no_height (H : height unbounded_lattice) : False.
Proof.
  assert (Hgrows : forall n, rank H (Finite n) < rank H (Finite (S n))).
  { intro n.
    assert (Hjoin : join unbounded_lattice (Finite n) (Finite (S n)) = Finite (S n)).
    { change (Finite (Nat.max n (S n)) = Finite (S n)).
      rewrite Nat.max_r by lia; reflexivity. }
    assert (Hstrict : leb unbounded_lattice
      (join unbounded_lattice (Finite n) (Finite (S n))) (Finite n) = false).
    { rewrite Hjoin; apply unbounded_join_never_stationary. }
    pose proof (join_rank_grows H (Finite n) (Finite (S n)) I I Hstrict) as Hgrow.
    now rewrite Hjoin in Hgrow. }
  assert (Hlower : forall n, n <= rank H (Finite n)).
  { intro n; induction n; [lia|pose proof (Hgrows n); lia]. }
  pose proof (Hlower (S (bound H))).
  pose proof (rank_bounded H (Finite (S (bound H))) I); lia.
Qed.

Example delayed_loop_uses_two_joins_before_widening :
  let ix := index_system nat_encoding delayed_system delayed_static in
  let hs := FinSet.of_list nat_encoding [0] in
  match Cost.value (iterate (Nested.step_c delayed_analysis delayed_code ix hs 2%N)
      6 (Nested.start delayed_code)) with
  | inl s => lookup nat_encoding unbounded_lattice (Nested.State.values s) 0
  | inr _ => Infinity
  end = Finite 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example delayed_unbounded_loop_widens :
  match Nested.run delayed_analysis delayed_code 100 with
  | Outcome.Solved m => lookup nat_encoding unbounded_lattice m 0
  | _ => Finite 0
  end = Infinity.
Proof.
  vm_compute; reflexivity.
Qed.

(** The delayed unbounded loop instantiates the derived rank/counter laws. *)
Theorem delayed_derived_fuel_client :
  exists m, Nested.run delayed_analysis delayed_code 56 = Outcome.Solved m.
Proof.
  apply (NestedWiden.fuel_enough delayed_analysis delayed_code delayed_laws
    delayed_all_selected unbounded_wrank delayed_invariant 56 delayed_code_ok).
  vm_compute; lia.
Qed.

Definition unselected_analysis :=
  Analysis.Make nat_encoding nat_encoding unbounded_lattice delayed_system delayed_static
    (Policy.flat nat).

Example head_cut_does_not_imply_selected_cut :
  Nested.code_ok unselected_analysis delayed_code /\
    ~ NestedWiden.selected_cuts unselected_analysis delayed_code.
Proof.
  split; [exact delayed_code_ok|].
  intro Hcut; apply (Hcut 0); apply t_step; split.
  - exists 0; split; [now left|]; split; [now left|now left].
  - reflexivity.
Qed.

Example unselected_unbounded_loop_exhausts :
  match Nested.run unselected_analysis delayed_code 100 with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition delayed_budget : NestedPrimitive.budget :=
  NestedPrimitive.Budget 2 1 1 0 1 1 0 1 0 0.

Local Lemma delayed_cost_key x :
  NestedPrimitive.key delayed_analysis delayed_code x -> x = 0.
Proof.
  change ((In x [0] \/ In x [0] \/ exists c, In c [0] /\ In x [0]) -> x = 0).
  intros [Hx|[Hx|[c [Hc Hx]]]]; cbn in Hx; intuition congruence.
Qed.

Definition delayed_cost_model : NestedPrimitive.model delayed_analysis delayed_code delayed_budget.
Proof.
  constructor.
  - intros x Hkey; apply delayed_cost_key in Hkey; subst x; split; vm_compute; easy.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros x Hx; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros m c Hc; apply Query.within_ask; [reflexivity|apply Query.within_ret].
  - intros m c Hc; change (1 <= 1); lia.
Qed.

(** Actual delayed-loop row costs instantiate primitive callback and width contracts. *)
Theorem delayed_primitive_evaluation_client m counts :
  (Cost.ticks (Eval.outputs_c delayed_system
      (lookup_c nat_encoding unbounded_lattice m) 0%nat) +
    Cost.ticks (Nested.updates_c delayed_analysis
      (FinSet.of_list nat_encoding [0%nat]) 2%N
      (fst (Eval.outputs delayed_system 0%nat (lookup nat_encoding unbounded_lattice m)))
      m counts) <= NestedPrimitive.evaluation_k delayed_budget)%N.
Proof.
  apply (NestedPrimitive.evaluation_cost delayed_analysis delayed_code delayed_laws
    delayed_budget delayed_cost_model); now left.
Qed.

Example coverage_has_separate_invocation_charge :
  Cost.ticks (Nested.cover_c delayed_analysis
    (FinSet.of_list nat_encoding [0]) [0]) = 5%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition feedback_static_laws : System.static_laws feedback_static.
Proof.
  constructor; intros c s x Hin;
    unfold feedback_static, feedback_system, System.rhs, System.deps, System.side_targets in *;
    cbn in *; destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
Qed.

Definition feedback_laws : Analysis.laws feedback_analysis.
Proof.
  constructor; try exact nat_encoding_laws; [exact bool_laws|exact feedback_static_laws].
Qed.

Definition feedback_terminates : Terminates.t feedback_analysis.
Proof.
  refine (@Terminates.Finite nat nat bool feedback_analysis (fun _ => True) bool_height I _ _).
  - intros; exact I.
  - intros; exact I.
Defined.

Definition feedback_budget : NestedPrimitive.budget :=
  NestedPrimitive.Budget 3 1 2 0 1 2 0 1 0 0.

Local Lemma feedback_cost_key x :
  NestedPrimitive.key feedback_analysis feedback_code x -> x = 0 \/ x = 1 \/ x = 2.
Proof.
  change ((In x [1; 0; 2] \/ In x [0; 1; 2] \/
    exists c, In c [0; 1; 2] /\
      In x (if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [2] else [0; 2])) ->
    x = 0 \/ x = 1 \/ x = 2).
  intros [Hx|[Hx|[c [Hc Hx]]]].
  - cbn in Hx; intuition congruence.
  - cbn in Hx; intuition congruence.
  - destruct Hc as [<-|[<-|[<-|Hbad]]]; try contradiction; cbn in Hx; intuition congruence.
Qed.

Definition feedback_cost_model :
  NestedPrimitive.model feedback_analysis feedback_code feedback_budget.
Proof.
  constructor.
  - intros x Hkey; apply feedback_cost_key in Hkey.
    destruct Hkey as [Hkey|[Hkey|Hkey]]; subst x; split; vm_compute; easy.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros x Hx; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; change (In c [0; 1; 2]) in Hc.
    destruct Hc as [<-|[<-|[<-|Hbad]]]; try contradiction; vm_compute; lia.
  - intros c Hc; reflexivity.
  - intros m c Hc; change (In c [0; 1; 2]) in Hc.
    destruct Hc as [<-|[<-|[<-|Hbad]]]; try contradiction.
    + eapply Query.within_bound with (n := 2).
      * apply Query.within_ask; [reflexivity|apply Query.within_ret].
      * change (2 <= 3); lia.
    + eapply Query.within_bound with (n := 2).
      * apply Query.within_ask; [reflexivity|apply Query.within_ret].
      * change (2 <= 3); lia.
    + apply Query.within_ask; [reflexivity|].
      apply Query.within_ask; [reflexivity|apply Query.within_ret].
  - intros m c Hc; change (In c [0; 1; 2]) in Hc.
    destruct Hc as [<-|[<-|[<-|Hbad]]]; try contradiction; change (1 <= 1); lia.
Qed.

Example feedback_primitive_numeric_parts :
  (NestedPrimitive.evaluation_k feedback_budget,
    NestedPrimitive.non_index_k feedback_analysis feedback_code feedback_budget) = (50, 138)%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The concrete prepared feedback index also has a closed computed numeric budget. *)
Example feedback_index_budget :
  (Cost.ticks (index_system_c nat_encoding feedback_system feedback_static) <= 1000)%N.
Proof.
  vm_compute; easy.
Qed.

(** Primitive callback/size contracts give a whole-run numeric client for every supplied fuel. *)
Theorem feedback_numeric_cost_client fuel :
  (Cost.ticks (Nested.run_c feedback_analysis feedback_code fuel) <=
    7354 + 2 * N.pos (Pos.size fuel))%N.
Proof.
  pose proof (NestedPrimitive.cost_from_index feedback_analysis feedback_code
    feedback_laws feedback_terminates feedback_budget feedback_cost_model fuel 1000%N
    ltac:(intro x; reflexivity) nested_feedback_code_ok feedback_index_budget) as Hcost.
  change (Cost.ticks (Nested.run_c feedback_analysis feedback_code fuel) <=
    7354 + 2 * N.pos (Pos.size fuel))%N in Hcost.
  exact Hcost.
Qed.

(** The final primitive corollary consumes no computed or assumed index-price premise. *)
Theorem feedback_primitive_cost_client fuel :
  (Cost.ticks (Nested.run_c feedback_analysis feedback_code fuel) <=
    NestedPrimitive.preparation_k feedback_analysis feedback_code feedback_budget +
    (NestedPrimitive.step_k feedback_budget + 2) *
      (N.of_nat (NestedPrimitive.driver_bound feedback_analysis feedback_terminates
        feedback_code feedback_budget) + 1) +
    2 * N.pos (Pos.size fuel))%N.
Proof.
  apply (NestedPrimitive.primitive_cost feedback_analysis feedback_code feedback_laws
    feedback_terminates feedback_budget feedback_cost_model fuel).
  - intro x; reflexivity.
  - exact nested_feedback_code_ok.
Qed.

Definition body_system : System.t nat nat unbounded_value :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then
      Query.Ask 1 (fun v => Cost.ret (Query.Ret (increment v)))
      else Query.Ask 0 (fun v => Cost.ret (Query.Ret v)))).

Definition body_static : System.static body_system :=
  System.Static (fun c => Cost.ret (if Nat.eqb c 0 then [1] else [0]))
    (fun _ => Cost.ret []).

Definition body_analysis :=
  Analysis.Make nat_encoding nat_encoding unbounded_lattice body_system body_static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret true) 2 0).

Definition body_code := Nested.Component 0 (Nested.Visit 1 Nested.End) Nested.End.

Definition body_laws : Analysis.laws body_analysis.
Proof.
  constructor; try exact nat_encoding_laws; [exact unbounded_laws|].
  constructor; intros c s x Hin;
    unfold body_static, body_system, System.rhs, System.deps, System.side_targets in *;
    cbn in *; destruct (Nat.eqb c 0); cbn in *; exact Hin.
Qed.

Definition body_cut : NestedWiden.selected_cuts body_analysis body_code.
Proof.
  intro start; apply (source_cut (flows body_static)
    (NestedWiden.selected body_analysis body_code)).
  intros x y [c [Hc [Hread Hout]]] Hno.
  destruct Hout as [Hy|Hbad]; [subst y|exfalso; exact Hbad].
  change (In c [0; 1]) in Hc; destruct Hc as [<-|[<-|Hbad]]; try contradiction.
  - vm_compute in Hno; discriminate.
  - change (In x [0]) in Hread; destruct Hread as [<-|Hbad];
      [vm_compute; reflexivity|contradiction].
Qed.

Definition body_code_ok : Nested.code_ok body_analysis body_code.
Proof.
  split.
  - intros c Hc; change (In c [0; 1]) in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction; vm_compute; auto.
  - intro start; apply (source_cut (flows body_static)
      (fun x => existsb (eqb nat_encoding x) (Nested.heads body_code))).
    intros x y [c [Hc [Hread Hout]]] Hno.
    destruct Hout as [Hy|Hbad]; [subst y|exfalso; exact Hbad].
    change (In c [0; 1]) in Hc; destruct Hc as [<-|[<-|Hbad]]; try contradiction.
    + vm_compute in Hno; discriminate.
    + change (In x [0]) in Hread; destruct Hread as [<-|Hbad];
        [vm_compute; reflexivity|contradiction].
Qed.

Example body_is_not_all_selected :
  ~ NestedWiden.all_selected body_analysis body_code.
Proof.
  intro Hall; specialize (Hall 1 (or_intror (or_introl eq_refl))).
  vm_compute in Hall; discriminate.
Qed.

Example unselected_body_joins_need_general_widening :
  match Nested.run body_analysis body_code 400 with
  | Outcome.Solved m => map (lookup nat_encoding unbounded_lattice m) [0; 1]
  | _ => []
  end = [Infinity; Infinity].
Proof.
  vm_compute; reflexivity.
Qed.

(** The public unknown-weight equation derives the concrete non-head path budget. *)
Theorem body_budget_value :
  NestedDebt.initial_budget body_analysis body_code body_laws unbounded_wrank body_cut = 28.
Proof.
  set (adapted := NestedCredit.masked body_analysis (FinSet.of_list nat_encoding [0])).
  set (ix := index_system nat_encoding body_system body_static).
  set (HI := index_system_laws nat_encoding (Analysis.key_laws body_laws)
    body_system body_static).
  set (HC := NestedCredit.masked_cuts body_analysis body_code body_cut).
  set (uw := WorklistWiden.unknown_weight adapted ix HI HC).
  set (weight := NestedDebt.weight body_analysis body_code body_laws body_cut).
  assert (Hread : readers_of nat_encoding ix 1 = [0]) by (vm_compute; reflexivity).
  assert (Hsucc : WorklistWiden.successors adapted ix 1 = []) by (vm_compute; reflexivity).
  assert (Huw : uw 1 = 1).
  { pose proof (WorklistWiden.unknown_weight_equation adapted ix HI HC 1) as Heq.
    change (uw 1 = length (readers_of nat_encoding ix 1) +
      WorklistCost.sum uw (WorklistWiden.successors adapted ix 1)) in Heq.
    rewrite Hread, Hsucc in Heq; exact Heq. }
  assert (Hout0 : WorklistWiden.noncut_outputs adapted 0 = []) by (vm_compute; reflexivity).
  assert (Hout1 : WorklistWiden.noncut_outputs adapted 1 = [1]) by (vm_compute; reflexivity).
  assert (Hw0 : weight 0 = 1).
  { change (1 + WorklistCost.sum uw (WorklistWiden.noncut_outputs adapted 0) = 1).
    rewrite Hout0; reflexivity. }
  assert (Hw1 : weight 1 = 2).
  { change (1 + WorklistCost.sum uw (WorklistWiden.noncut_outputs adapted 1) = 2).
    rewrite Hout1; change (1 + (uw 1 + 0) = 2); rewrite Huw; reflexivity. }
  assert (Hrows : NestedDebt.rows body_analysis = [0; 1] \/
    NestedDebt.rows body_analysis = [1; 0]) by (vm_compute; auto).
  assert (Hcap : WorklistCost.sum weight (NestedDebt.rows body_analysis) = 3).
  { destruct Hrows as [Hrows|Hrows]; rewrite Hrows.
    - change (weight 0 + (weight 1 + 0) = 3); rewrite Hw0, Hw1; reflexivity.
    - change (weight 1 + (weight 0 + 0) = 3); rewrite Hw0, Hw1; reflexivity. }
  unfold NestedDebt.initial_budget, NestedDebt.debt_cap; fold weight.
  rewrite Hcap; reflexivity.
Qed.

(** A genuine non-head join cycle instantiates the complete derived selected-cut fuel theorem. *)
Theorem body_general_fuel_client :
  exists m, Nested.run body_analysis body_code 400 = Outcome.Solved m.
Proof.
  apply (NestedDebt.fuel_enough body_analysis body_code body_laws
    unbounded_wrank body_cut 400 body_code_ok).
  rewrite body_budget_value; vm_compute; lia.
Qed.

Definition body_budget : NestedPrimitive.budget := NestedPrimitive.Budget 2 1 1 0 1 2 0 1 0 0.

Local Lemma body_cost_key x :
  NestedPrimitive.key body_analysis body_code x -> x = 0 \/ x = 1.
Proof.
  change ((In x [0; 1] \/ In x [0; 1] \/
    exists c, In c [0; 1] /\ In x (if Nat.eqb c 0 then [1] else [0])) -> x = 0 \/ x = 1).
  intros [Hx|[Hx|[c [Hc Hx]]]].
  - cbn in Hx; intuition congruence.
  - cbn in Hx; intuition congruence.
  - destruct (Nat.eqb c 0); cbn in Hx; intuition congruence.
Qed.

Definition body_cost_model : NestedPrimitive.model body_analysis body_code body_budget.
Proof.
  constructor.
  - intros x Hx; apply body_cost_key in Hx; destruct Hx as [Hx|Hx];
      subst x; split; vm_compute; easy.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros x Hx; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; reflexivity.
  - intros c Hc; change (In c [0; 1]) in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction; reflexivity.
  - intros c Hc; reflexivity.
  - intros m c Hc; change (In c [0; 1]) in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction.
    all: apply Query.within_ask; [reflexivity|apply Query.within_ret].
  - intros m c Hc; change (In c [0; 1]) in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction; change (1 <= 1); lia.
Qed.

(** Derived path weights and primitive prices give a widening whole-run numeric client. *)
Theorem body_numeric_widen_cost_client fuel :
  (Cost.ticks (Nested.run_c body_analysis body_code fuel) <=
    NestedPrimitive.preparation_k body_analysis body_code body_budget +
    19600 + 2 * N.pos (Pos.size fuel))%N.
Proof.
  pose proof (NestedDebt.primitive_cost body_analysis body_code body_laws
    unbounded_wrank body_cut body_budget body_cost_model fuel body_code_ok) as Hcost.
  rewrite body_budget_value in Hcost.
  change (Cost.ticks (Nested.run_c body_analysis body_code fuel) <=
    NestedPrimitive.preparation_k body_analysis body_code body_budget +
    19600 + 2 * N.pos (Pos.size fuel))%N in Hcost.
  exact Hcost.
Qed.

End NestedClients.
Import NestedClients.
