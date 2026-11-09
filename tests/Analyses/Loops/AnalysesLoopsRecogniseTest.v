(** * Scalar-evolution compilation and context keys

    These examples check ordered compilation and actual context-sensitive Memo execution.
    For example, changing a referenced phi adds a new entry and adding an unrelated phi reuses it.
    Builds on: AnalysesLoopsRecognise and BaseMemo. *)

From Stdlib Require Import List Bool Arith ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseIntern BaseMap BaseMemo.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Loops Require Import
  AnalysesLoopsChrec AnalysesLoopsPrepared AnalysesLoopsRecognise.
Import List.ListNotations Chrec Recognise.
Local Open Scope nat_scope.

Definition scev_test_nested_plan : scev_plan nat :=
  ScevPlan
    [ScevBinding 0 10 20 SAddUpdate (Some (SOutside 11)) true;
     ScevBinding 1 12 21 SAddUpdate (Some (SPhi 0)) true] 1.

Example scev_compiler_ranked_nested_phi :
  scev_compile_plan nat_encoding scev_test_nested_plan =
    Some (CRec (CInv (IVar 12)) (CRec (CInv (IVar 10)) (CInv (IVar 11)))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_geometric :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 0 10 20 SMulUpdate (Some (SOutside 11)) false] 0) =
    Some (CGeo (CInv (IVar 10)) (CInv (IVar 11))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_doubling_coefficient :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 0 10 20 SDoubleUpdate None true] 0) =
    Some (CGeo (CInv (IVar 10)) (CInv (IConst 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_shared_expression :
  let e := SAdd 30 (SOutside 11) (SOutside 12) in
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 0 10 20 SAddUpdate (Some (SMul 31 e e)) true] 0) =
    Some (CRec (CInv (IVar 10))
      (CInv (IMul (IAdd (IVar 11) (IVar 12)) (IAdd (IVar 11) (IVar 12))))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_missing_prior_phi :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 1 12 21 SAddUpdate (Some (SPhi 0)) true] 1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_missing_other :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 1 12 21 SAddUpdate None true] 1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_empty_plan :
  scev_compile_plan nat_encoding (ScevPlan [] 0) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scev_shared_lookup (z : Z) (extra : bool) (x : nat) : option (Chrec.t nat) :=
  if Nat.eqb x 3 then Some (CInv (IConst z)) else
    if extra && Nat.eqb x 6 then Some (CInv (IConst 9)) else None.

Definition compile_lookup (z : Z) (extra : bool) :=
  Cost.lift (fun _ => 1%N) (scev_shared_lookup z extra).

Example scev_compiler_support_change_invalidates_then_reuses :
  let '((_, m0), _) := scev_compile_expr nat_encoding (compile_lookup 0 false) (SPhi 3)
    ScevPrepared.session_empty in
  let '((_, m1), _) := scev_compile_expr nat_encoding (compile_lookup 1 false) (SPhi 3) m0 in
  let '((c, m2), _) := scev_compile_expr nat_encoding (compile_lookup 1 true) (SPhi 3) m1 in
  c = Some (CInv (IConst 1)) /\ Map.size (fst m1) = 2 /\ Map.size (fst m2) = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_compiler_missing_observation_invalidates :
  let missing := Cost.lift (fun _ => 1%N) (fun _ : nat => @None (Chrec.t nat)) in
  let '((r0, m0), _) := scev_compile_expr nat_encoding missing (SPhi 3)
    ScevPrepared.session_empty in
  let '((r1, m1), _) := scev_compile_expr nat_encoding (compile_lookup 0 false) (SPhi 3) m0 in
  r0 = None /\ r1 = Some (CInv (IConst 0)) /\ Map.size (fst m1) = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_compiler_same_root_distinct_tree :
  let lookup := Cost.lift (fun _ => 1%N) (fun _ : nat => @None (Chrec.t nat)) in
  let '((_, m0), _) := scev_compile_expr nat_encoding lookup
    (SAdd 8 (SOutside 2) (SOutside 2)) ScevPrepared.session_empty in
  let '((c, m1), _) := scev_compile_expr nat_encoding lookup
    (SAdd 8 (SOutside 2) (SConst 9 7)) m0 in
  c = Some (CInv (IAdd (IVar 2) (IWordConst 7))) /\
    Map.size (fst m0) = 2 /\ Map.size (fst m1) = 4.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_compiler_actual_hit_avoids_recursive_miss :
  let lookup := Cost.lift (fun _ => 1%N) (fun _ : nat => @None (Chrec.t nat)) in
  let e := SMul 8 (SAdd 7 (SOutside 2) (SOutside 3))
    (SAdd 7 (SOutside 2) (SOutside 3)) in
  let cold := scev_compile_expr_c nat_encoding lookup e ScevPrepared.session_empty in
  let '((_, table), _) := Cost.value cold in
  let warm := scev_compile_expr_c nat_encoding lookup e table in
  (Cost.ticks warm <? Cost.ticks cold)%N = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition inventory_graph : Graph.t nat nat :=
  Graph.of_pure [0] [0; 1] (fun _ => []) (fun _ => 0) (fun _ => 1).

Definition inventory_ssa : Ssa.t nat nat nat nat unit :=
  Ssa.of_pure (Cfg.Make inventory_graph nat_encoding nat_encoding) nat_encoding [0; 1]
    (fun x => if Nat.eqb x 1 then Op 7 [0] else Arbitrary)
    (fun x => x) (fun _ => []) (fun _ => []) (fun _ => []).

Example scev_inventory_preserves_source_and_missing :
  let table := scev_inventory_index inventory_ssa [0; 1; 0] in
  Map.get nat_encoding 1 table = Some (1, Op 7 [0]) /\
    Map.get nat_encoding 2 table = None /\ Map.size table = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_inventory_empty_cost :
  Cost.ticks (scev_inventory_index_c inventory_ssa []) = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition compile_pilot_lookup :=
  Cost.lift (fun _ => 1%N) (fun _ : nat => @None (Chrec.t nat)).
Definition compile_pilot_seed :=
  scev_compile_expr nat_encoding compile_pilot_lookup (SOutside 2) ScevPrepared.session_empty.
Definition compile_pilot_cache := snd (fst compile_pilot_seed).
Definition compile_pilot_source := SAdd 8 (SOutside 2) (SConst 9 7).

Example nonempty_compiler_pilot_initial_validity :
  compile_valid nat_encoding compile_pilot_cache.
Proof.
  exact (proj2 (scev_compile_expr_correct nat_encoding nat_encoding_laws compile_pilot_lookup
    (SOutside 2) ScevPrepared.session_empty (ScevPrepared.session_empty_valid _ _ _ _))).
Qed.

Example nonempty_compiler_pilot_agreement :
  compile_expr_state_valid nat_encoding (fun x => Cost.value (compile_pilot_lookup x))
    compile_pilot_source compile_pilot_cache
    (Cost.value (scev_compile_expr_trace_c nat_encoding compile_pilot_lookup
      compile_pilot_source compile_pilot_cache trace_empty)).
Proof.
  apply scev_compile_expr_state_correct; [exact nat_encoding_laws|].
  exact nonempty_compiler_pilot_initial_validity.
Qed.

Example nonempty_compiler_pilot_retains_child_allocations :
  let '((value, (cache, names)), events) := Cost.value (scev_compile_expr_trace_c nat_encoding
    compile_pilot_lookup compile_pilot_source compile_pilot_cache trace_empty) in
  value = Some (CInv (IAdd (IVar 2) (IWordConst 7))) /\
  Map.get positive_encoding 1%positive cache = Some (Some (CInv (IVar 2))) /\
  Map.get positive_encoding 3%positive cache = Some (Some (CInv (IWordConst 7))) /\
  Intern.size (ScevPrepared.codes (ScevPrepared.source_names names)) = 3 /\
  Intern.size (ScevPrepared.context_names names) = 3 /\
  length (trace_hits events) = 1 /\ length (trace_misses events) = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
