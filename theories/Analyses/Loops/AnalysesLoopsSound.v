(** * Scalar-evolution recognition machine

    The producer processes one visit or finish command per shared iteration callback.
    For example, visiting a completed dependency records a hit without expanding its children.
    Builds on: AnalysesLoopsRecognise, AnalysesLoopsCheck and CostLoop. *)

From Stdlib Require Import List Bool Arith NArith ZArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMemo.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsRecognise
  AnalysesLoopsCheck.
Import List.ListNotations Cost.Notations Chrec Recognise PlanCheck.

Module LoopSound.

Inductive work (V : Type) :=
  | Visit (x : V)
  | FinishBinary (multiply : bool) (x a b : V)
  | FinishPhi (x base update other : V) (kind : scev_update) (phi_first : bool).
Arguments Visit {V}.
Arguments FinishBinary {V}.
Arguments FinishPhi {V}.

(** Producer state contains data alone and retains reverse-ordered preparation traces. *)
Record producer_state (V : Type) := State {
  pending : list (work V);
  active : FinSet.t V;
  completed : Map.t V (scev_expr V);
  bindings : list (scev_binding V);
  preparation_hits : list V;
  preparation_nodes : list V
}.
Arguments State {V}.
Arguments pending {V}.
Arguments active {V}.
Arguments completed {V}.
Arguments bindings {V}.
Arguments preparation_hits {V}.
Arguments preparation_nodes {V}.

Definition finish_c {V} (EV : encoding V) (st : producer_state V) rest x e new_binding :=
  let* active' := FinSet.remove_c EV x (active st) in
  let* done := Map.set_c EV x e (completed st) in
  Cost.ret (State rest active' done
    (match new_binding with Some b => b :: bindings st | None => bindings st end)
    (preparation_hits st) (x :: preparation_nodes st)).

Definition schedule_c {V} (EV : encoding V) (st : producer_state V) commands x :=
  let* active' := FinSet.add_c EV x (active st) in
  Cost.ret (State commands active' (completed st) (bindings st)
    (preparation_hits st) (preparation_nodes st)).

Definition expand_phi_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    (ix : static_index N V K) (st : producer_state V) rest x header i :=
  let EV := Ssa.val_enc (lssa lv) in
  let* header_ok := eqb_c (Cfg.node_enc (Ssa.cfg (lssa lv))) header (lheader lv) in
  if header_ok then
    let* base := Map.get_c nat_encoding i (entry_args ix) in
    let* update := Map.get_c nat_encoding i (back_args ix) in
    match base, update with
    | Some base, Some update =>
      let* base_info := Map.get_c EV base (indexed_values ix) in
      let* update_info := Map.get_c EV update (indexed_values ix) in
      match base_info, update_info with
      | Some (base_n, _), Some (update_n, Op o [arg_a; arg_b]) =>
        Cost.step ;;
        let* base_inside := lbody_c lv base_n in
        Cost.step ;;
        let* update_inside := lbody_c lv update_n in
        if negb base_inside && update_inside then
          let* phi_a := eqb_c EV arg_a x in
          let* phi_b := eqb_c EV arg_b x in
          Cost.step ;;
          let* add := add_op_c so o in
          if add && phi_a && phi_b then
            Cost.map Some (finish_c EV st rest x (SPhi x)
              (Some (ScevBinding x base update SDoubleUpdate None true)))
          else if phi_a || phi_b then
            let other := if phi_a then arg_b else arg_a in
            if add then
              Cost.map Some (schedule_c EV st
                (Visit other :: FinishPhi x base update other SAddUpdate phi_a :: rest) x)
            else
              Cost.step ;;
              let* mul := mul_op_c so o in
              if mul then
                Cost.map Some (schedule_c EV st
                  (Visit other :: FinishPhi x base update other SMulUpdate phi_a :: rest) x)
              else Cost.ret None
          else Cost.ret None
        else Cost.ret None
      | _, _ => Cost.ret None
      end
    | _, _ => Cost.ret None
    end
  else Cost.ret None.

Definition expand_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    (ix : static_index N V K) (st : producer_state V) rest x :=
  let EV := Ssa.val_enc (lssa lv) in
  let* source := Map.get_c EV x (indexed_values ix) in
  match source with
  | None => Cost.ret None
  | Some (n, d) =>
    Cost.step ;;
    let* inside := lbody_c lv n in
    if inside then
      match d with
      | Param header i => expand_phi_c lv so ix st rest x header i
      | Op o [] =>
        Cost.step ;;
        let* literal := const_op_c so o in
        match literal with
        | Some z => Cost.map Some (finish_c EV st rest x (SConst x z) None)
        | None => Cost.ret None
        end
      | Op o [a; b] =>
        Cost.step ;;
        let* add := add_op_c so o in
        if add then
          Cost.map Some (schedule_c EV st (Visit a :: Visit b :: FinishBinary false x a b :: rest) x)
        else
          Cost.step ;;
          let* mul := mul_op_c so o in
          if mul then
            Cost.map Some (schedule_c EV st (Visit a :: Visit b :: FinishBinary true x a b :: rest) x)
          else Cost.ret None
      | _ => Cost.ret None
      end
    else Cost.map Some (finish_c EV st rest x (SOutside x) None)
  end.

(** Every callback processes one command and reports rejection explicitly at its first bad dependency. *)
Definition producer_step_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    (ix : static_index N V K) (st : producer_state V)
    : Cost.t (producer_state V + option (producer_state V)) :=
  let EV := Ssa.val_enc (lssa lv) in
  match pending st with
  | [] => Cost.ret (inr (Some st))
  | command :: rest =>
    Cost.step ;;
    let* next :=
      match command with
      | Visit x =>
        let* old := Map.get_c EV x (completed st) in
        match old with
        | Some _ =>
          Cost.ret (Some (State rest (active st) (completed st) (bindings st)
            (x :: preparation_hits st) (preparation_nodes st)))
        | None =>
          let* cycling := FinSet.mem_c EV x (active st) in
          if cycling then Cost.ret None else expand_c lv so ix st rest x
        end
      | FinishBinary multiply x a b =>
        let* ca := Map.get_c EV a (completed st) in
        let* cb := Map.get_c EV b (completed st) in
        match ca, cb with
        | Some ea, Some eb =>
          Cost.map Some (finish_c EV st rest x
            (if multiply then SMul x ea eb else SAdd x ea eb) None)
        | _, _ => Cost.ret None
        end
      | FinishPhi x base update other kind first =>
        let* child := Map.get_c EV other (completed st) in
        match child with
        | Some e => Cost.map Some (finish_c EV st rest x (SPhi x)
            (Some (ScevBinding x base update kind (Some e) first)))
        | None => Cost.ret None
        end
      end in
    Cost.ret (match next with Some state => inl state | None => inr None end)
  end.

Fixpoint inventory_count_c {V} (inventory : list V) : Cost.t positive :=
  match inventory with
  | [] => Cost.ret 1%positive
  | _ :: rest =>
    Cost.step ;;
    Cost.map Pos.succ (inventory_count_c rest)
  end.

(** Internal fuel counts commands and includes room for the terminal callback after the root. *)
Definition command_fuel_c {V} (inventory : list V) :=
  let* count := inventory_count_c inventory in
  Cost.step ;;
  Cost.ret (xO (xO count)).

(** Fuel construction quadruples the successor inventory length without unary conversion. *)
Theorem command_fuel_value {V} (inventory : list V) :
  N.pos (Cost.value (command_fuel_c inventory)) =
    (4 * (N.of_nat (length inventory) + 1))%N.
Proof.
  assert (Hcount : N.pos (Cost.value (inventory_count_c inventory)) =
    (N.of_nat (length inventory) + 1)%N).
  { induction inventory as [|x rest IH]; [reflexivity|].
    cbn [inventory_count_c length]; autorewrite with galois_cost.
    change (N.succ (N.pos (Cost.value (inventory_count_c rest))) =
      N.of_nat (S (length rest)) + 1)%N.
    rewrite Nat2N.inj_succ; lia. }
  unfold command_fuel_c; autorewrite with galois_cost.
  change (4 * N.pos (Cost.value (inventory_count_c inventory)) =
    4 * (N.of_nat (length inventory) + 1))%N.
  rewrite Hcount; reflexivity.
Qed.

(** Internal fuel construction charges every inventory cell and its binary shift. *)
Theorem command_fuel_cost {V} (inventory : list V) :
  Cost.ticks (command_fuel_c inventory) = (N.of_nat (length inventory) + 1)%N.
Proof.
  assert (Hcount : Cost.ticks (inventory_count_c inventory) = N.of_nat (length inventory)).
  { induction inventory as [|x rest IH]; [reflexivity|].
    cbn [inventory_count_c length]; autorewrite with galois_cost.
    rewrite IH, Nat2N.inj_succ; lia. }
  unfold command_fuel_c; autorewrite with galois_cost; rewrite Hcount; lia.
Qed.

(** The raw engine distinguishes command exhaustion from a rejected or completed traversal. *)
Inductive producer_outcome (V : Type) :=
  | Completed (state : producer_state V)
  | Rejected
  | OutOfFuel (state : producer_state V).
Arguments Completed {V}.
Arguments Rejected {V}.
Arguments OutOfFuel {V}.

Definition produce_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    ix (inventory : list V) target :=
  let* fuel := command_fuel_c inventory in
  let* empty_active := @FinSet.empty_c V in
  let* empty_done := @Map.empty_c V (scev_expr V) in
  let* result := iterate (producer_step_c lv so ix) fuel
    (State [Visit target] empty_active empty_done [] [] []) in
  Cost.ret
    (match result with
    | inl state => OutOfFuel state
    | inr None => Rejected
    | inr (Some state) => Completed state
    end).

(** Checked execution exposes the exact plan, preparation trace and consumer tables used by the run. *)
Record execution (V : Type) := Execution {
  recurrence : Chrec.t V;
  plan : scev_plan V;
  preparation_reuses : list V;
  prepared_nodes : list V;
  checker_bindings : check_binding_memo V;
  checker_expressions : check_memo V;
  compiler_bindings : binding_memo V;
  compiler_expressions : compile_memo V
}.
Arguments Execution {V}.
Arguments recurrence {V}.
Arguments plan {V}.
Arguments preparation_reuses {V}.
Arguments prepared_nodes {V}.
Arguments checker_bindings {V}.
Arguments checker_expressions {V}.
Arguments compiler_bindings {V}.
Arguments compiler_expressions {V}.

(** Checked recognition prepares source metadata once and retains the actual checker/compiler tables. *)
Definition run_execution_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    inventory target : Cost.t (option (execution V)) :=
  let* source := prepare_index_c lv inventory (ScevPlan [] target) in
  let* produced := produce_c lv so source inventory target in
  match produced with
  | Rejected | OutOfFuel _ => Cost.ret None
  | Completed state =>
    let* bs := rev_c (bindings state) in
    let p := ScevPlan bs target in
    let* ranks := rank_index_c (Ssa.val_enc (lssa lv)) O bs in
    let ix := Index (indexed_values source) (entry_args source) (back_args source) ranks in
    let* checked := scev_plan_check_index_c lv so ix p in
    let '((accepted, check_bindings), check_expressions) := checked in
    if accepted then
      let* compiled := scev_compile_plan_execution_c (Ssa.val_enc (lssa lv)) p in
      let '((found, compile_bindings), compile_expressions) := compiled in
      match found with
      | None => Cost.ret None
      | Some c => Cost.ret (Some (Execution c p (preparation_hits state) (preparation_nodes state)
          check_bindings check_expressions compile_bindings compile_expressions))
      end
    else Cost.ret None
  end.

Definition run_c {N E V K G C} lv so inventory target :=
  Cost.map (option_map recurrence) (@run_execution_c N E V K G C lv so inventory target).

Definition run {N E V K G C} lv so inventory target :=
  Cost.value (@run_c N E V K G C lv so inventory target).

(** Every returned execution carries its actual accepted plan and its actual compiled recurrence. *)
Theorem recognise_plan_checked {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) inventory target out :
  Cost.value (run_execution_c lv so inventory target) = Some out ->
  sp_target (plan out) = target /\ scev_plan_check lv so inventory (plan out) = true /\
    scev_compile_plan (Ssa.val_enc (lssa lv)) (plan out) = Some (recurrence out).
Proof.
  unfold run_execution_c; autorewrite with galois_cost.
  fold (prepare_index lv inventory (ScevPlan [] target)).
  destruct (Cost.value (produce_c lv so (prepare_index lv inventory (ScevPlan [] target))
    inventory target)) as [state| |state]; autorewrite with galois_cost; try discriminate.
  fold (prepare_ranks (Ssa.val_enc (lssa lv)) O (rev (bindings state))).
  set (p := ScevPlan (rev (bindings state)) target).
  assert (Hindex :
    Index (indexed_values (prepare_index lv inventory (ScevPlan [] target)))
      (entry_args (prepare_index lv inventory (ScevPlan [] target)))
      (back_args (prepare_index lv inventory (ScevPlan [] target)))
      (prepare_ranks (Ssa.val_enc (lssa lv)) O (rev (bindings state))) =
    prepare_index lv inventory p).
  { rewrite !prepare_index_equation; reflexivity. }
  rewrite Hindex.
  destruct (Cost.value (scev_plan_check_index_c lv so (prepare_index lv inventory p) p))
    as [[accepted check_bindings] check_expressions] eqn:Hcheck.
  destruct accepted; autorewrite with galois_cost; [|discriminate].
  destruct (Cost.value (scev_compile_plan_execution_c (Ssa.val_enc (lssa lv)) p))
    as [[[c|] compile_bindings] compile_expressions] eqn:Hcompile;
    autorewrite with galois_cost; [|discriminate].
  intro Heq; injection Heq as Heq; subst out.
  cbn [plan recurrence sp_target]; split; [reflexivity|]; split.
  - rewrite scev_plan_check_equation, Hcheck; reflexivity.
  - rewrite scev_compile_plan_execution_equation, Hcompile; reflexivity.
Qed.

End LoopSound.
