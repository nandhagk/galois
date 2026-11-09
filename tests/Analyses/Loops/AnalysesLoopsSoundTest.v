(** * Checked scalar-evolution recognition

    These examples retain the legacy recognizer's recurrence and rejection observations.
    For example, direct self-addition keeps the idiom-owned geometric coefficient two.
    Builds on: AnalysesLoopsSound and the indexed checker fixtures. *)

From Stdlib Require Import List Bool Arith ZArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMemo.
From Galois.Bits Require Import BitsWord.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns
  ProgramSsa ProgramStrict.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsFailure
  AnalysesLoopsRecognise AnalysesLoopsCheck AnalysesLoopsSound.
From Galois.Tests.Analyses.Loops Require Import AnalysesLoopsCheckTest.
Import List.ListNotations Chrec Recognise PlanCheck LoopSound Failure.
Local Open Scope nat_scope.

Example scev_recognise_nested_phis :
  run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 6 =
    Some (CRec (CInv (IVar 1)) (CRec (CInv (IVar 0)) (CInv (IVar 2)))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_geometric :
  run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 1 [3; 2] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = Some (CGeo (CInv (IVar 0)) (CInv (IVar 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_direct_doubling :
  run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = Some (CGeo (CInv (IVar 0)) (CInv (IConst 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_mutual_feedback_rejected :
  run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 6] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_nonlinear_self_feedback_rejected :
  run (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else
    if Nat.eqb x 8 then Op 1 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_missing_inventory_rejected :
  run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops [0; 1; 3; 5; 6; 7; 8] 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scev_descending_env (x : nat) : Z :=
  if Nat.eqb x 2 then 255%Z else if Nat.eqb x 0 then 2%Z else 0%Z.

Example scev_recognise_signed_descending_variable :
  match run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 3 with
  | Some c =>
    trip_count (fun y => view_z 8%positive Signed (scev_descending_env y)) 8%positive Signed CmpNe
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253)) =
        Some 5%N
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_signed_descending_literal :
  match run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 with
  | Some c =>
    c = CRec (CInv (IVar 0)) (CInv (IWordConst 255)) /\
    trip_count (fun y => view_z 8%positive Signed (scev_descending_env y)) 8%positive Signed CmpNe
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253)) =
        Some 5%N
  | None => False
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_signed_descending_variable_nowrap :
  match run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 3 with
  | Some c => nowrap_check 8%positive Signed
      (fun y => view_z 8%positive Signed (scev_descending_env y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253))
      5%N = true
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_signed_descending_literal_nowrap :
  match run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 with
  | Some c => nowrap_check 8%positive Signed
      (fun y => view_z 8%positive Signed (scev_descending_env y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253))
      5%N = true
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_signed_minimum_wrap_rejected :
  let inv := fun x => if Nat.eqb x 0 then 128%Z else if Nat.eqb x 2 then 255%Z else 0%Z in
  match run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 3 with
  | Some c =>
    trip_count (fun y => view_z 8%positive Signed (inv y)) 8%positive Signed CmpLt
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 129)) =
        Some 1%N /\
    nowrap_check 8%positive Signed (fun y => view_z 8%positive Signed (inv y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 129))
      1%N = false
  | None => False
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_machine_fuel_construction :
  N.pos (Cost.value (command_fuel_c scev_shape_inventory)) = 36%N /\
    Cost.ticks (command_fuel_c scev_shape_inventory) = 9%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_machine_root_completion_trace :
  match Cost.value (run_execution_c (scev_shape_loop scev_shape_defs [0; 1])
    scev_shape_ops scev_shape_inventory 6) with
  | Some out =>
    preparation_reuses out = [] /\ prepared_nodes out = [6; 3; 2] /\
      plan out = scev_shape_nested_plan
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition scev_shared_defs (x : nat) : definition nat nat nat :=
  match x with
  | 3 => Param 1 0
  | 6 => Param 1 1
  | 13 => Param 1 2
  | 5 => Op 0 [3; 2]
  | 7 => Op 0 [6; 11]
  | 14 => Op 0 [13; 12]
  | 8 => Op 0 [3; 2]
  | 9 => Op 0 [8; 8]
  | 10 => Op 0 [9; 9]
  | 11 => Op 0 [10; 10]
  | 12 => Op 0 [6; 11]
  | _ => Arbitrary
  end.

Definition scev_shared_inventory := [0; 1; 2; 3; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14].

Definition scev_shared_loop : loop_view nat nat nat nat unit :=
  LoopView
    (Ssa.of_pure (Cfg.Make scev_shape_graph nat_encoding nat_encoding)
      nat_encoding scev_shared_inventory scev_shared_defs
      (fun x => match x with
      | 3 | 6 | 13 => 1
      | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 14 => 2
      | _ => 0
      end)
      (fun _ => [3; 6; 13])
      (fun e => if Nat.eqb e 0 then [0; 1; 0] else [5; 7; 14]) (fun _ => []))
    1 (Cost.lift (fun _ => 1%N) (fun n => Nat.eqb n 1 || Nat.eqb n 2)) 0 1 None.

Definition scev_shared_e8 : scev_expr nat := SAdd 8 (SPhi 3) (SOutside 2).
Definition scev_shared_e9 : scev_expr nat := SAdd 9 scev_shared_e8 scev_shared_e8.
Definition scev_shared_e10 : scev_expr nat := SAdd 10 scev_shared_e9 scev_shared_e9.
Definition scev_shared_e11 : scev_expr nat := SAdd 11 scev_shared_e10 scev_shared_e10.

Definition scev_shared_plan : scev_plan nat :=
  ScevPlan
    [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true;
     ScevBinding 6 1 7 SAddUpdate (Some scev_shared_e11) true;
     ScevBinding 13 0 14 SAddUpdate (Some (SAdd 12 (SPhi 6) scev_shared_e11)) true] 13.

Example scev_integrated_dag_preparation_reuses :
  match Cost.value (run_execution_c scev_shared_loop scev_shape_ops scev_shared_inventory 13) with
  | Some out =>
    prepared_nodes out = [13; 12; 6; 11; 10; 9; 8; 3; 2] /\
    preparation_reuses out = [11; 10; 9; 8; 2] /\ plan out = scev_shared_plan
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_integrated_shared_plan_checked :
  scev_plan_check scev_shared_loop scev_shape_ops scev_shared_inventory scev_shared_plan = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_integrated_dag_checker_and_compiler_reuse :
  match Cost.value (run_execution_c scev_shared_loop scev_shape_ops scev_shared_inventory 13) with
  | Some out =>
    length (trace_hits (checker_events out)) = 5 /\
    length (trace_misses (checker_events out)) = 8 /\
    length (trace_hits (compiler_events out)) = 5 /\
    length (trace_misses (compiler_events out)) = 8 /\
    hd 1%positive (trace_hits (checker_events out)) =
      scev_expr_code nat_encoding scev_shared_e11 /\
    hd 1%positive (trace_hits (compiler_events out)) =
      scev_expr_code nat_encoding scev_shared_e11
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition scev_shared_index :=
  prepare_index scev_shared_loop scev_shared_inventory scev_shared_plan.

Example scev_checker_rank_change_invalidates_then_reuses :
  let e := SPhi 3 in
  let '((r0, m0), t0) := Cost.value (scev_check_expr_trace_c nat_encoding (lbody_c scev_shared_loop)
    (indexed_values scev_shared_index) scev_shape_ops
    (phi_before_c nat_encoding scev_shared_index 0) e Memo.empty trace_empty) in
  let '((r1, m1), t1) := Cost.value (scev_check_expr_trace_c nat_encoding (lbody_c scev_shared_loop)
    (indexed_values scev_shared_index) scev_shape_ops
    (phi_before_c nat_encoding scev_shared_index 1) e m0 t0) in
  let '((r2, _), t2) := Cost.value (scev_check_expr_trace_c nat_encoding (lbody_c scev_shared_loop)
    (indexed_values scev_shared_index) scev_shape_ops
    (phi_before_c nat_encoding scev_shared_index 2) e m1 t1) in
  fst r0 = false /\ fst r1 = true /\ fst r2 = true /\
    length (trace_misses t2) = 2 /\ length (trace_hits t2) = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition scev_shared_lookup (z : Z) (extra : bool) (x : nat) : option (Chrec.t nat) :=
  if Nat.eqb x 3 then Some (CInv (IConst z)) else
    if extra && Nat.eqb x 6 then Some (CInv (IConst 9)) else None.

Example scev_compiler_environment_change_invalidates_then_reuses :
  let lookup z extra := Cost.lift (fun _ => 1%N) (scev_shared_lookup z extra) in
  let e := SPhi 3 in
  let '((r0, m0), t0) := Cost.value (scev_compile_expr_trace_c nat_encoding (lookup 0%Z false)
    e Memo.empty trace_empty) in
  let '((r1, m1), t1) := Cost.value (scev_compile_expr_trace_c nat_encoding (lookup 1%Z false)
    e m0 t0) in
  let '((r2, _), t2) := Cost.value (scev_compile_expr_trace_c nat_encoding (lookup 1%Z true)
    e m1 t1) in
  r0 = Some (CInv (IConst 0)) /\ r1 = Some (CInv (IConst 1)) /\
    r2 = Some (CInv (IConst 1)) /\ length (trace_misses t2) = 2 /\ length (trace_hits t2) = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_checker_same_root_malformed_tree_is_distinct :
  let before := phi_before_c nat_encoding scev_shared_index 1 in
  let '((r0, m0), t0) := Cost.value (scev_check_expr_trace_c nat_encoding (lbody_c scev_shared_loop)
    (indexed_values scev_shared_index) scev_shape_ops before scev_shared_e8 Memo.empty trace_empty) in
  let '((r1, _), t1) := Cost.value (scev_check_expr_trace_c nat_encoding (lbody_c scev_shared_loop)
    (indexed_values scev_shared_index) scev_shape_ops before
    (SAdd 8 (SOutside 2) (SOutside 2)) m0 t0) in
  fst r0 = true /\ fst r1 = false /\ length (trace_misses t1) = 4 /\ length (trace_hits t1) = 0.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_compiler_same_root_different_tree_is_distinct :
  let lookup := Cost.lift (fun _ => 1%N) (fun _ : nat => @None (Chrec.t nat)) in
  let '((_, m0), t0) := Cost.value (scev_compile_expr_trace_c nat_encoding lookup
    (SAdd 8 (SOutside 2) (SOutside 2)) Memo.empty trace_empty) in
  let '((c, _), t1) := Cost.value (scev_compile_expr_trace_c nat_encoding lookup
    (SAdd 8 (SOutside 2) (SConst 9 7)) m0 t0) in
  c = Some (CInv (IAdd (IVar 2) (IWordConst 7))) /\
    length (trace_misses t1) = 4 /\ length (trace_hits t1) = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** * A nonempty semantic client *)

Module SemanticClient.

Inductive state := Start | HeaderZero | HeaderOne.
Inductive transition : state -> list unit -> state -> Prop :=
  | Enter : transition Start [] HeaderZero
  | Back : transition HeaderZero [] HeaderOne
  | Stay : transition HeaderZero [] HeaderZero.

Definition model : semantics state unit := Semantics (fun s => s = Start) transition.
Definition point (s : state) := match s with Start => false | _ => true end.
Definition taken s (_ : list unit) t e :=
  match s, t with
  | Start, HeaderZero => e = false
  | HeaderZero, HeaderOne => e = true
  | _, _ => False
  end.
Definition stays s (_ : list unit) t := s = HeaderZero /\ t = HeaderZero.
Definition graph : Graph.t bool bool :=
  Graph.of_pure [false] [false; true] (fun n => [n]) (fun e => e) (fun _ => true).
Definition cfg := Cfg.Make graph bool_encoding bool_encoding.
Definition definition (x : nat) : ProgramSsa.definition bool nat nat :=
  match x with
  | 1 => Param true 0
  | 3 => Op 0 [1; 2]
  | _ => Arbitrary
  end.
Definition home (x : nat) := Nat.eqb x 1 || Nat.eqb x 3.
Definition inventory := [0; 1; 2; 3].
Definition ssa : Ssa.t bool bool nat nat unit :=
  Ssa.of_pure cfg nat_encoding inventory definition home
    (fun b => if b then [1] else []) (fun e => if e then [3] else [0]) (fun _ => []).
Definition value s (x : nat) : option Z :=
  match x with
  | 0 => Some 0%Z
  | 1 => Some (match s with HeaderOne => 1%Z | _ => 0%Z end)
  | 2 | 3 => Some 1%Z
  | _ => None
  end.
Definition link : SsaLink.t state unit bool bool nat Z :=
  SsaLink.Make (Link.Make point taken stays) value.
Definition eval (o : nat) (args : list Z) :=
  match o, args with
  | 0, [a; b] => Some (wrap 4%positive (a + b))
  | 1, [a; b] => Some (wrap 4%positive (a * b))
  | _, _ => None
  end.
Definition holds (_ : unit) (_ : list Z) := True.
Definition ops : scev_ops nat Z :=
  ops_of_pure 4%positive (wrap 4%positive) (Nat.eqb 0) (Nat.eqb 1) (fun _ => None).
Definition test := LoopTest CmpLt Unsigned 1 (IConst 1).
Definition loop : loop_view bool bool nat nat unit :=
  LoopView ssa true (Cost.lift (fun _ => 1%N) (fun b => b)) false true (Some test).

Lemma graph_laws : graph_wf graph.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros v [<-|Hbad]; [change (In false [false; true]); left; reflexivity|contradiction].
  - intros v e Hin; change (In e [v]) in Hin.
    destruct Hin as [<-|Hbad]; [reflexivity|contradiction].
  - intros v e Hin Hout; change (In true [false; true]); right; left; reflexivity.
Qed.

Lemma link_laws_hold : link_laws model graph (SsaLink.link link).
Proof.
  constructor.
  - exact graph_laws.
  - intros s ->; change (In false [false]); left; reflexivity.
  - intros s tr t Hreach Hstep; inversion Hstep; subst.
    + right; exists false; reflexivity.
    + right; exists true; reflexivity.
    + left; split; reflexivity.
  - intros e s tr t Hreach Hstep Htaken; inversion Hstep; subst;
      cbn [link SsaLink.link Link.taken Link.point taken point] in Htaken |- *;
      try contradiction; subst e; (split; [left; reflexivity|reflexivity]).
  - intros s tr t Hreach Hstep [-> ->]; reflexivity.
Qed.

Lemma values_change_only_at_phi s tr t x :
  transition s tr t -> value t x <> value s x -> s = HeaderZero /\ t = HeaderOne /\ x = 1.
Proof.
  intros Hstep Hchange; inversion Hstep; subst; destruct x as [|[|[|[|x]]]];
    cbn [value] in Hchange; try congruence; auto.
Qed.

Lemma ssa_laws_hold : ssa_laws model ssa link eval holds.
Proof.
  constructor.
  - exact link_laws_hold.
  - intros x b i Hdef; change (definition x = Param b i) in Hdef.
    destruct x as [|[|[|[|x]]]]; cbn [definition] in Hdef; try discriminate.
    injection Hdef as <- <-; reflexivity.
  - intros e s tr t Hreach Hstep Htaken g ys Hin; contradiction.
  - intros e s tr t Hreach Hstep Htaken g ys x o args Hin; contradiction.
  - intros x c s tr t Hreach Hstep Hvalue.
    change (value t x = Some c) in Hvalue.
    inversion Hstep; subst; try (left; exact Hvalue).
    destruct x as [|[|[|[|x]]]]; try (left; exact Hvalue).
    cbn [value] in Hvalue; injection Hvalue as <-.
    right; right; left; exists true, true, 0, 3; repeat split; reflexivity.
  - intros s x c Hreach Hvalue; change (value s x = Some c) in Hvalue.
    change (In x inventory).
    destruct x as [|[|[|[|x]]]]; cbn [value] in Hvalue; cbn [inventory In];
      intuition discriminate.
Qed.

Lemma strict_laws_hold : strict_ssa_laws model ssa link.
Proof.
  constructor.
  - intros x s tr t Hreach Hstep [-> ->] Hchange; contradiction.
  - intros e x s tr t Hreach Hstep Htaken Hchange.
    destruct (values_change_only_at_phi s tr t x Hstep Hchange) as [-> [-> ->]]; reflexivity.
  - intros x s tr t Hreach Hstep [-> ->] Hhome; reflexivity.
  - intros e x s tr t Hreach Hstep Htaken Hhome.
    inversion Hstep; subst; try reflexivity.
    destruct x as [|[|[|[|x]]]]; try reflexivity; exfalso; apply Hhome; reflexivity.
  - intros e g ys x Hlisted Hin; contradiction.
  - intros x o args y Hdef Hin; change (definition x = Op o args) in Hdef.
    destruct x as [|[|[|[|x]]]]; cbn [definition] in Hdef; try discriminate.
    injection Hdef as <- <-; destruct Hin as [<-|[<-|Hbad]]; [apply dominates_refl| |contradiction].
    intros root es [<-|Hbad] Hpath; [left; reflexivity|contradiction].
Qed.

Lemma ops_laws_hold : scev_ops_laws ops eval.
Proof.
  constructor.
  - intro c; change (wrap 4%positive c = wrap 4%positive (wrap 4%positive c)).
    symmetry; apply wrap_wrap.
  - intros o a b r Hflag Heval; change (Nat.eqb 0 o = true) in Hflag.
    apply Nat.eqb_eq in Hflag; subst o; cbn [eval] in Heval; injection Heval as <-.
    change (wrap 4%positive (wrap 4%positive (a + b)) =
      wrap 4%positive (wrap 4%positive a + wrap 4%positive b)).
    rewrite wrap_wrap; apply wrap_add.
  - intros o a b r Hflag Heval; change (Nat.eqb 1 o = true) in Hflag.
    apply Nat.eqb_eq in Hflag; subst o; cbn [eval] in Heval; injection Heval as <-.
    change (wrap 4%positive (wrap 4%positive (a * b)) =
      wrap 4%positive (wrap 4%positive a * wrap 4%positive b)).
    rewrite wrap_wrap; apply wrap_mul.
  - intros o z r Hliteral; discriminate.
Qed.

Lemma back_source s tr t :
  transition s tr t -> taken s tr t true -> s = HeaderZero /\ t = HeaderOne.
Proof.
  intros Hstep Htaken; inversion Hstep; subst; cbn [taken] in Htaken; intuition discriminate.
Qed.

Lemma loop_laws_hold : loop_laws model loop ops link eval holds inventory.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact bool_encoding_laws.
  - exact bool_encoding_laws.
  - exact ssa_laws_hold.
  - exact strict_laws_hold.
  - change (~ In true [false]); cbn [In]; intuition discriminate.
  - vm_compute; auto.
  - vm_compute; auto.
  - intros e Hlisted Htarget; destruct e; [right|left]; reflexivity.
  - reflexivity.
  - intros n [<-|Hbad]; [reflexivity|contradiction].
  - intros e Hlisted Houtside Hinside; destruct e; [discriminate|reflexivity].
  - intros e x i s tr t Hreach Hstep Htaken Htarget Hdef.
    change (definition x = Param true i) in Hdef.
    destruct x as [|[|[|[|x]]]]; cbn [definition] in Hdef; try discriminate.
    injection Hdef as <-; inversion Hstep; subst; destruct e;
      cbn [link SsaLink.link Link.taken taken] in Htaken; try discriminate; try contradiction;
      reflexivity.
  - intros x i s tr t Hreach Hstep [-> ->] Hpoint Hdef; reflexivity.
  - intros tst y Htest Hin; injection Htest as <-; contradiction.
  - intros s tr t Hreach Hstep Htaken tst Htest.
    injection Htest as <-.
    destruct (back_source s tr t Hstep Htaken) as [-> ->].
    exists 0%Z; split; reflexivity || (vm_compute; lia).
  - intros p x o args c s tr t Hreach Hstep Htaken Hcheck Hin Hdef Hvalue.
    destruct (back_source s tr t Hstep Htaken) as [-> ->].
    change (definition x = Op o args) in Hdef.
    destruct x as [|[|[|[|x]]]]; cbn [definition] in Hdef; try discriminate.
    injection Hdef as <- <-; change (Some 1%Z = Some c) in Hvalue; injection Hvalue as <-.
    exists [0%Z; 1%Z]; split; [repeat constructor|]; reflexivity.
Qed.

Lemma history : run_edges model (SsaLink.link link) Start [false; true] HeaderOne.
Proof.
  eapply run_take; [constructor|reflexivity|].
  eapply run_stay; [apply Stay|split; reflexivity|].
  eapply run_take; [apply Back|reflexivity|constructor].
Qed.

Definition recurrence : Chrec.t nat := CRec (CInv (IVar 0)) (CInv (IVar 2)).

Example program_recurrence_at_header :
  to_Z ops 1%Z = wrap (width_of ops)
    (Chrec.eval (inv_env link ops HeaderOne) recurrence (stay_arrivals loop [false; true])).
Proof.
  eapply (scev_sound model loop ops link eval holds inventory loop_laws_hold ops_laws_hold
    1 recurrence).
  - vm_compute; reflexivity.
  - reflexivity.
  - exact history.
  - reflexivity.
  - reflexivity.
Qed.

Example program_trip_bound :
  (N.of_nat (stay_arrivals loop [false; true]) <= 1)%N.
Proof.
  eapply (loop_trip_sound model loop ops link eval holds inventory loop_laws_hold ops_laws_hold
    test recurrence 1%N).
  - reflexivity.
  - vm_compute; reflexivity.
  - reflexivity.
  - exact history.
  - reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

End SemanticClient.
