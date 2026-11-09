(** * Gen/kill fixture solutions

    Examples run loop liveness, reaching definitions and diamond availability.
    For example, a fact generated on only one diamond arm is unavailable at the join.
    Builds on: FrameworkBitvector and FrameworkDenseTest. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis FixpointAnalyze.
From Galois.Framework Require Import FrameworkUtil FrameworkDense FrameworkBitvector.
From Galois.Tests.Framework Require Import FrameworkDenseTest.
Import List.ListNotations Cost.Notations.

Definition live_problem :=
  Bitvector.of_pure loop nat_encoding [0; 1] Backward
    (fun e => match e with 1 => [0] | 2 => [1] | _ => [] end)
    (fun e => match e with 0 => [0] | _ => [] end) (fun _ => Some []).

Definition reaching_problem :=
  Bitvector.of_pure loop nat_encoding [0; 1] Forward
    (fun e => match e with 0 => [0] | 1 => [1] | _ => [] end)
    (fun e => match e with 1 => [0] | _ => [] end) (fun _ => Some []).

Definition available_problem :=
  Bitvector.of_pure diamond nat_encoding [7; 8] Forward
    (fun e => match e with 0 => [7] | 2 => [8] | _ => [] end)
    (fun _ => []) (fun _ => Some []).

(** The guide's liveness constructor uses costed Vars readers without a semantics. *)
Definition liveness {N E X} (P : Vars.t N E X) :=
  Bitvector.may_analysis
    (Bitvector.Make (Vars.cfg P) (Vars.var_enc P) (Vars.universe P) Backward
      (Vars.uses_c P) (Vars.defs_c P)
      (fun n => Cost.map Some (Vars.exits_c P n))).

Definition sets_observe {C} (a : Analysis.t nat C (set_t nat_encoding)) ns :=
  option_map (map (fun s => FinSet.elements (set_raw s))) (observe a 16 ns).

Definition must_observe {C} (a : Analysis.t nat C (must_t nat_encoding)) ns :=
  option_map (map (fun s => match s with
    | All => None
    | Only s => Some (FinSet.elements (set_raw s))
    end)) (observe a 16 ns).

Example liveness_loop :
  sets_observe (Bitvector.may_analysis live_problem) [0; 1; 2] =
    Some [[1]; [1; 0]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example reaching_loop :
  sets_observe (Bitvector.may_analysis reaching_problem) [0; 1; 2] =
    Some [[]; [1; 0]; [1; 0]].
Proof.
  vm_compute; reflexivity.
Qed.

Example available_diamond :
  must_observe (Bitvector.must_analysis available_problem) [0; 1; 2; 3; 99] =
    Some [Some []; Some [7]; Some []; Some []; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example may_hand_candidate :
  check_post (Analysis.lat (Bitvector.may_analysis live_problem))
    (Analysis.system (Bitvector.may_analysis live_problem))
    (fun n => set_of_list nat_encoding
      (match n with 0 => [1] | 1 => [0; 1] | _ => [] end)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example must_hand_candidate :
  check_post (Analysis.lat (Bitvector.must_analysis available_problem))
    (Analysis.system (Bitvector.must_analysis available_problem))
    (fun n => Only (set_of_list nat_encoding (if Nat.eqb n 1 then [7] else []))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example may_missing_uses_rejected :
  check_post (Analysis.lat (Bitvector.may_analysis live_problem))
    (Analysis.system (Bitvector.may_analysis live_problem))
    (fun _ => set_empty nat_encoding) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example must_wrong_join_rejected :
  check_post (Analysis.lat (Bitvector.must_analysis available_problem))
    (Analysis.system (Bitvector.must_analysis available_problem))
    (fun _ => Only (set_of_list nat_encoding [7])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_problem :=
  Bitvector.of_pure empty nat_encoding [] Forward
    (fun _ => []) (fun _ => []) (fun _ => None).

Example empty_may :
  sets_observe (Bitvector.may_analysis empty_problem) [0] = Some [[]].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_must :
  must_observe (Bitvector.must_analysis empty_problem) [0] = Some [None].
Proof.
  vm_compute; reflexivity.
Qed.

Definition tick_problem (es : list nat) :=
  Bitvector.of_pure
    (Cfg.Make (Graph.of_pure [0] [0] (fun _ => es) (fun _ => 0) (fun _ => 0))
      nat_encoding nat_encoding)
    nat_encoding [0] Forward (fun _ => [0]) (fun _ => []) (fun _ => None).

Example prepare_tick_doubling :
  (Cost.ticks (Bitvector.prepare_c (tick_problem [0])),
   Cost.ticks (Bitvector.prepare_c (tick_problem [0; 0]))) = (41%N, 68%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example prepare_tick_second_doubling :
  Cost.ticks (Bitvector.prepare_c (tick_problem [0; 0; 0; 0])) = 122%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition raw_seed_problem nodes :=
  Bitvector.of_pure
    (Cfg.Make (Graph.of_pure [0] nodes (fun _ => []) (fun _ => 0) (fun _ => 0))
      nat_encoding nat_encoding)
    nat_encoding [7] Forward (fun _ => []) (fun _ => [])
    (fun n => if Nat.eqb n 0 then Some [7] else None).

Example may_entry_absent_from_nodes :
  sets_observe (Bitvector.may_analysis (raw_seed_problem [])) [0; 99] =
    Some [[7]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example must_entry_absent_from_nodes :
  must_observe (Bitvector.must_analysis (raw_seed_problem [])) [0; 99] =
    Some [Some [7]; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example may_closed_seed_control :
  sets_observe (Bitvector.may_analysis (raw_seed_problem [0])) [0; 99] =
    Some [[7]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example must_closed_seed_control :
  must_observe (Bitvector.must_analysis (raw_seed_problem [0])) [0; 99] =
    Some [Some [7]; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_may_raw_seed_rejected :
  check_post (Analysis.lat (Bitvector.may_analysis (raw_seed_problem [])))
    (Analysis.system (Bitvector.may_analysis (raw_seed_problem [])))
    (fun _ => set_empty nat_encoding) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_must_raw_seed_rejected :
  check_post (Analysis.lat (Bitvector.must_analysis (raw_seed_problem [])))
    (Analysis.system (Bitvector.must_analysis (raw_seed_problem [])))
    (fun _ => All) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition seed_only_problem :=
  Bitvector.of_pure
    (Cfg.Make (Graph.of_pure [0] [0; 1] (fun _ => []) (fun _ => 0) (fun _ => 0))
      nat_encoding nat_encoding)
    nat_encoding [7] Forward (fun _ => []) (fun _ => [])
    (fun n => Some (if Nat.eqb n 0 then [7] else [99])).

Example unseeded_node_boundary_is_not_cached :
  option_map (fun s => FinSet.elements (set_raw s))
    (Bitvector.boundary_set (Bitvector.prepare seed_only_problem) 1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example source_support_uses_only_generated_seeds : Bitvector.supported seed_only_problem.
Proof.
  split.
  - intros e Hin; vm_compute in Hin; contradiction.
  - intros n xs Hn Hb; change (0 = n \/ False) in Hn.
    destruct Hn as [<-|Hbad]; [|contradiction].
    change (Some [7] = Some xs) in Hb; inversion Hb; subst xs.
    apply incl_refl.
Qed.

(** Original optional boundaries agree on every raw seed without a graph-closure premise. *)
Theorem source_boundary_client {N E U} (P : Bitvector.t N E U) n :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) -> In n (Bitvector.seeds P) ->
  Bitvector.boundary_set (Bitvector.prepare P) n =
    option_map (set_of_list (Bitvector.fact_enc P)) (Bitvector.boundary P n).
Proof.
  apply Bitvector.prepare_boundary_source.
Qed.

(** Later may clients can use source boundaries without assuming universe support. *)
Theorem source_may_client {N E U} (P : Bitvector.t N E U) s :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) ->
  post_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) s ->
  forall n xs, In n (Bitvector.seeds P) -> Bitvector.boundary P n = Some xs ->
    leb (may (Bitvector.fact_enc P)) (set_of_list (Bitvector.fact_enc P) xs) (s n) = true.
Proof.
  intros HN HU Hpost; exact (proj1 ((proj1 (Bitvector.may_source_post_iff P s HN HU)) Hpost)).
Qed.

(** Later must clients obtain the same source boundary as a reached Only fact. *)
Theorem source_must_client {N E U} (P : Bitvector.t N E U) s :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) ->
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) s ->
  forall n xs, In n (Bitvector.seeds P) -> Bitvector.boundary P n = Some xs ->
    leb (must (Bitvector.fact_enc P)) (Only (set_of_list (Bitvector.fact_enc P) xs))
      (s n) = true.
Proof.
  intros HN HU Hpost; exact (proj1 ((proj1 (Bitvector.must_source_post_iff P s HN HU)) Hpost)).
Qed.

Module BitvectorConstruction.

Definition nonunit_problem :=
  Bitvector.Make (Bitvector.cfg (tick_problem [0])) nat_encoding [0] Forward
    (fun _ => Cost.tick 11 ;; Cost.ret [0])
    (fun _ => Cost.tick 13 ;; Cost.ret [])
    (fun _ => Cost.tick 17 ;; Cost.ret None).

Example may_constructor_counts_prepare_and_system :
  Cost.ticks (Bitvector.may_analysis_c nonunit_problem) = 86%N.
Proof.
  rewrite Bitvector.may_analysis_cost, Dense.system_cost; vm_compute; reflexivity.
Qed.

Example must_constructor_counts_prepare_and_system :
  Cost.ticks (Bitvector.must_analysis_c nonunit_problem) = 86%N.
Proof.
  rewrite Bitvector.must_analysis_cost, Dense.system_cost; vm_compute; reflexivity.
Qed.

Example duplicate_constructor_costs :
  (Cost.ticks (Bitvector.may_analysis_c (tick_problem [0])),
   Cost.ticks (Bitvector.may_analysis_c (tick_problem [0; 0])),
   Cost.ticks (Bitvector.must_analysis_c (tick_problem [0; 0; 0; 0]))) =
    (48%N, 77%N, 135%N).
Proof.
  rewrite !Bitvector.may_analysis_cost, Bitvector.must_analysis_cost, !Dense.system_cost.
  vm_compute; reflexivity.
Qed.

Example duplicate_constructor_keeps_flow_occurrences :
  System.constraints (Analysis.system
    (Cost.value (Bitvector.may_analysis_c (tick_problem [0; 0])))) =
    [Dense.Seed 0; Dense.Flow 0; Dense.Flow 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_constructors_have_no_setup_work :
  (Cost.ticks (Bitvector.may_analysis_c empty_problem),
   Cost.ticks (Bitvector.must_analysis_c empty_problem)) = (0%N, 0%N).
Proof.
  rewrite Bitvector.may_analysis_cost, Bitvector.must_analysis_cost, !Dense.system_cost.
  vm_compute; reflexivity.
Qed.

Example charged_may_constructor_runs :
  sets_observe (Cost.value (Bitvector.may_analysis_c live_problem)) [0; 1; 2] =
    Some [[1]; [1; 0]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example charged_must_constructor_runs :
  must_observe (Cost.value (Bitvector.must_analysis_c available_problem)) [0; 1; 2; 3; 99] =
    Some [Some []; Some [7]; Some []; Some []; None].
Proof.
  vm_compute; reflexivity.
Qed.

(** An importing may client sees exactly the original analysis record. *)
Theorem original_may_client {N E U} (P : Bitvector.t N E U) :
  Cost.value (Bitvector.may_analysis_c P) =
    Dense.analysis (Bitvector.may_dense P (Bitvector.prepare P))
      (Policy.by_code (Cfg.node_enc (Bitvector.cfg P))).
Proof.
  apply Bitvector.may_analysis_equation.
Qed.

(** An importing must client sees exactly the original analysis record. *)
Theorem original_must_client {N E U} (P : Bitvector.t N E U) :
  Cost.value (Bitvector.must_analysis_c P) =
    Dense.analysis (Bitvector.must_dense P (Bitvector.prepare P))
      (Policy.by_code (Cfg.node_enc (Bitvector.cfg P))).
Proof.
  apply Bitvector.must_analysis_equation.
Qed.

(** May callers compose the actual preparation and dense-construction charges. *)
Theorem may_cost_client {N E U} (P : Bitvector.t N E U) :
  Cost.ticks (Bitvector.may_analysis_c P) =
    (Cost.ticks (Bitvector.prepare_c P) +
      Cost.ticks (Dense.system_c (Bitvector.may_dense P (Bitvector.prepare P))))%N.
Proof.
  apply Bitvector.may_analysis_cost.
Qed.

(** Must callers compose the actual preparation and dense-construction charges. *)
Theorem must_cost_client {N E U} (P : Bitvector.t N E U) :
  Cost.ticks (Bitvector.must_analysis_c P) =
    (Cost.ticks (Bitvector.prepare_c P) +
      Cost.ticks (Dense.system_c (Bitvector.must_dense P (Bitvector.prepare P))))%N.
Proof.
  apply Bitvector.must_analysis_cost.
Qed.

End BitvectorConstruction.
Import BitvectorConstruction.

Module BitvectorPreparationCost.

Definition priced_encoding {K} (E : encoding K) price : encoding K :=
  Encoding (fun x => Cost.tick price ;; encode_c E x).

(** Symbolic encoder prices retain the actual delegated encoder charge. *)
Theorem priced_encoding_cost {K} (E : encoding K) price x :
  Cost.ticks (encode_c (priced_encoding E price) x) =
    (price + Cost.ticks (encode_c E x))%N.
Proof.
  unfold priced_encoding; cbn [encode_c].
  rewrite Cost.ticks_bind, Cost.ticks_tick; reflexivity.
Qed.

Definition priced_problem es :=
  Bitvector.Make
    (Cfg.Make (Graph.Make [0; 0] [0]
      (fun _ => Cost.tick 5 ;; Cost.ret es)
      (fun _ => Cost.ret 0) (fun _ => Cost.ret 0))
      (priced_encoding nat_encoding 3) (priced_encoding nat_encoding 7))
    (priced_encoding nat_encoding 11) [0] Forward
    (fun _ => Cost.tick 13 ;; Cost.ret [0; 0])
    (fun _ => Cost.tick 17 ;; Cost.ret [])
    (fun _ => Cost.tick 19 ;; Cost.ret None).

Definition none_boundary price :=
  Bitvector.Make singleton nat_encoding [] Forward
    (fun _ => Cost.ret []) (fun _ => Cost.ret [])
    (fun _ => Cost.tick price ;; Cost.ret None).

Definition some_boundary price :=
  Bitvector.Make singleton nat_encoding [7] Forward
    (fun _ => Cost.ret []) (fun _ => Cost.ret [])
    (fun _ => Cost.tick price ;; Cost.ret (Some [7; 7])).

(** An absent boundary retains its symbolic reader price and performs no set construction. *)
Theorem absent_boundary_symbolic price :
  Cost.ticks (Bitvector.boundary_rows_c (none_boundary price)) = (2 + price)%N.
Proof.
  assert (Hseeds : Bitvector.seeds (none_boundary price) = [0]) by reflexivity.
  assert (Hboundary : Bitvector.boundary (none_boundary price) 0 = None) by reflexivity.
  rewrite Bitvector.boundary_rows_cost, Hseeds; cbn [fold_right].
  rewrite Hboundary; cbn [none_boundary Bitvector.boundary_c].
  rewrite Cost.ticks_bind, Cost.ticks_tick, Cost.ticks_ret; lia.
Qed.

(** A present boundary retains the same symbolic reader and its full duplicate-list conversion. *)
Theorem present_boundary_symbolic price :
  Cost.ticks (Bitvector.boundary_rows_c (some_boundary price)) =
    (2 + price + Cost.ticks (set_of_list_c nat_encoding [7%nat; 7%nat]))%N.
Proof.
  assert (Hseeds : Bitvector.seeds (some_boundary price) = [0]) by reflexivity.
  assert (Hboundary : Bitvector.boundary (some_boundary price) 0 = Some [7; 7]) by reflexivity.
  rewrite Bitvector.boundary_rows_cost, Hseeds; cbn [fold_right].
  rewrite Hboundary; cbn [some_boundary Bitvector.boundary_c Bitvector.fact_enc].
  rewrite Cost.ticks_bind, Cost.ticks_tick, Cost.ticks_ret; lia.
Qed.

Example duplicate_absent_boundaries_pay_both_readers :
  Cost.ticks (Bitvector.boundary_rows_c (priced_problem [0])) = 42%N.
Proof.
  rewrite Bitvector.boundary_rows_cost; vm_compute; reflexivity.
Qed.

Example duplicate_emission_retains_reader_and_pair_work :
  Bitvector.occurrences (priced_problem [0; 0]) [0; 0]
    (Bitvector.gen_c (priced_problem [0; 0])) = [(0, 0); (0, 0); (0, 0); (0, 0)].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_nonunit_input_costs_more :
  N.ltb (Cost.ticks (Bitvector.prepare_c (priced_problem [0])))
    (Cost.ticks (Bitvector.prepare_c (priced_problem [0; 0]))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example present_boundary_retains_duplicate_work :
  N.ltb (Cost.ticks (Bitvector.boundary_rows_c (none_boundary 19)))
    (Cost.ticks (Bitvector.boundary_rows_c (some_boundary 19))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_preparation_retains_no_hidden_work :
  Cost.ticks (Bitvector.prepare_c empty_problem) = 0%N.
Proof.
  rewrite Bitvector.prepare_cost, !Bitvector.prepare_sets_cost, Bitvector.boundary_rows_cost.
  vm_compute; reflexivity.
Qed.

(** An importing caller can compose the exact graph, edge-index and boundary-map charges. *)
Theorem preparation_cost_client {N E U} (P : Bitvector.t N E U) :
  Cost.ticks (Bitvector.prepare_c P) =
    (Cost.ticks (fw_edges_c (Bitvector.cfg P)) +
      Cost.ticks (Bitvector.prepare_sets_c P (Cfg.edges (Bitvector.cfg P)) (Bitvector.gen_c P)) +
      Cost.ticks (Bitvector.prepare_sets_c P (Cfg.edges (Bitvector.cfg P)) (Bitvector.kill_c P)) +
      Cost.ticks (Bitvector.boundary_rows_c P) +
      Cost.ticks (Map.of_list_c (Cfg.node_enc (Bitvector.cfg P))
        (map (fun n => (n, option_map (set_of_list (Bitvector.fact_enc P))
          (Bitvector.boundary P n))) (Bitvector.seeds P))))%N.
Proof.
  apply Bitvector.prepare_cost.
Qed.

End BitvectorPreparationCost.
Import BitvectorPreparationCost.
