(** * Scalar-evolution recognition machine

    The producer processes one visit or finish command per shared iteration callback.
    For example, visiting a completed dependency records a hit without expanding its children.
    Builds on: AnalysesLoopsRecognise, AnalysesLoopsCheck and CostLoop. *)

From Stdlib Require Import List Bool Arith NArith ZArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMemo.
From Galois.Bits Require Import BitsWord.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns
  ProgramSsa ProgramStrict.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsRecognise
  AnalysesLoopsCheck AnalysesLoopsIdioms AnalysesLoopsFailure.
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

(** Unseen inventory occurrences pay for fresh expansions, including duplicate inventory entries. *)
Definition unseen {V} (EV : encoding V) (st : producer_state V) x : bool :=
  negb (FinSet.mem EV x (active st)) &&
    match Map.get EV x (completed st) with None => true | Some _ => false end.

Fixpoint remaining {V} (EV : encoding V) (inventory : list V) (st : producer_state V) : nat :=
  match inventory with
  | [] => O
  | x :: rest => (if unseen EV st x then 1 else 0) + remaining EV rest st
  end.

(** Three credits per unseen occurrence pay for the largest two-child command expansion. *)
Definition command_credit {V} (EV : encoding V) inventory (st : producer_state V) : nat :=
  3 * remaining EV inventory st + length (pending st).

Local Lemma remaining_ext {V} (EV : encoding V) inventory (a b : producer_state V) :
  (forall x, unseen EV a x = unseen EV b x) ->
  remaining EV inventory a = remaining EV inventory b.
Proof.
  intro Hagree; induction inventory; cbn [remaining]; rewrite ?Hagree, ?IHinventory; reflexivity.
Qed.

Local Lemma finish_unseen {V} (EV : encoding V) st rest x e b y :
  unseen EV (Cost.value (@finish_c V EV st rest x e b)) y =
    (negb (eqb EV y x) && unseen EV st y).
Proof.
  change (unseen EV (State rest (FinSet.remove EV x (active st))
    (Map.set EV x e (completed st))
    (match b with Some b => b :: bindings st | None => bindings st end)
    (preparation_hits st) (x :: preparation_nodes st)) y =
    (negb (eqb EV y x) && unseen EV st y)).
  unfold unseen; cbn [active completed].
  rewrite FinSet.mem_remove, Map.get_set_raw.
  destruct (eqb EV y x), (FinSet.mem EV y (active st)), (Map.get EV y (completed st));
    reflexivity.
Qed.

Local Lemma schedule_unseen {V} (EV : encoding V) st commands x y :
  unseen EV (Cost.value (@schedule_c V EV st commands x)) y =
    (negb (eqb EV y x) && unseen EV st y).
Proof.
  change (unseen EV (State commands (FinSet.add EV x (active st)) (completed st)
    (bindings st) (preparation_hits st) (preparation_nodes st)) y =
    (negb (eqb EV y x) && unseen EV st y)).
  unfold unseen; cbn [active completed].
  rewrite FinSet.mem_add_raw.
  destruct (eqb EV y x), (FinSet.mem EV y (active st)), (Map.get EV y (completed st));
    reflexivity.
Qed.

Local Lemma remaining_marked {V} (EV : encoding V) (HV : encoding_laws EV) st next x :
  (forall y, unseen EV next y = negb (eqb EV y x) && unseen EV st y) ->
  forall inventory,
  (remaining EV inventory next <= remaining EV inventory st)%nat /\
    (In x inventory -> unseen EV st x = true ->
      (remaining EV inventory next < remaining EV inventory st)%nat).
Proof.
  intro Hmark; induction inventory as [|y rest [Hle Hlt]]; cbn [remaining].
  - split; [lia|contradiction].
  - rewrite Hmark.
    destruct (eqb_spec EV HV y x) as [Hequal|Hdifferent].
    + subst y; cbn; destruct (unseen EV st x) eqn:Hfresh; split; lia.
    + cbn; destruct (unseen EV st y); split; try lia;
        (intros [Hequal|Hin] Hfresh; [congruence|specialize (Hlt Hin Hfresh); lia]).
Qed.

Local Lemma finish_credit {V} (EV : encoding V) (HV : encoding_laws EV)
    inventory st command rest x e b :
  pending st = command :: rest ->
  (command_credit EV inventory (Cost.value (finish_c EV st rest x e b)) <
    command_credit EV inventory st)%nat.
Proof.
  intro Hwork.
  pose proof (proj1 (remaining_marked EV HV st _ x (finish_unseen EV st rest x e b) inventory)).
  unfold command_credit; rewrite Hwork.
  change (3 * remaining EV inventory (Cost.value (finish_c EV st rest x e b)) + length rest <
    3 * remaining EV inventory st + S (length rest))%nat.
  lia.
Qed.

Local Lemma schedule_credit {V} (EV : encoding V) (HV : encoding_laws EV)
    inventory st commands x :
  In x inventory -> unseen EV st x = true ->
  (length commands <= length (pending st) + 2)%nat ->
  (command_credit EV inventory (Cost.value (schedule_c EV st commands x)) <
    command_credit EV inventory st)%nat.
Proof.
  intros Hin Hfresh Hcommands.
  pose proof (proj2 (remaining_marked EV HV st _ x (schedule_unseen EV st commands x)
    inventory) Hin Hfresh) as Hless.
  unfold command_credit.
  change (3 * remaining EV inventory (Cost.value (schedule_c EV st commands x)) +
    length commands < 3 * remaining EV inventory st + length (pending st))%nat.
  lia.
Qed.

Local Lemma expand_phi_credit {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix inventory
    st rest x header i next :
  pending st = Visit x :: rest -> In x inventory -> unseen (Ssa.val_enc (lssa lv)) st x = true ->
  Cost.value (expand_phi_c lv so ix st rest x header i) = Some next ->
  (command_credit (Ssa.val_enc (lssa lv)) inventory next <
    command_credit (Ssa.val_enc (lssa lv)) inventory st)%nat.
Proof.
  intros Hwork Hin Hfresh.
  unfold expand_phi_c; autorewrite with galois_cost.
  destruct (Cost.value (eqb_c _ header (lheader lv))); [|discriminate].
  autorewrite with galois_cost.
  destruct (Cost.value (Map.get_c nat_encoding i (entry_args ix))) as [base|];
    [|discriminate].
  destruct (Cost.value (Map.get_c nat_encoding i (back_args ix))) as [update|];
    [|discriminate].
  autorewrite with galois_cost.
  destruct (Cost.value (Map.get_c _ base (indexed_values ix))) as [[base_n base_d]|];
    [|discriminate].
  destruct (Cost.value (Map.get_c _ update (indexed_values ix))) as [[update_n d]|];
    [|discriminate].
  destruct d as [o args|n k|]; try discriminate.
  destruct args as [|a [|b [|extra rest_args]]]; try discriminate.
  autorewrite with galois_cost.
  destruct (negb (Cost.value (lbody_c lv base_n)) && Cost.value (lbody_c lv update_n));
    [|discriminate].
  autorewrite with galois_cost.
  destruct (Cost.value (add_op_c so o) &&
    Cost.value (eqb_c _ a x) && Cost.value (eqb_c _ b x)).
  - autorewrite with galois_cost; intro Heq; injection Heq as <-.
    exact (finish_credit (Ssa.val_enc (lssa lv)) HV inventory st (Visit x) rest x
      (SPhi x) (Some (ScevBinding x base update SDoubleUpdate None true)) Hwork).
  - destruct (Cost.value (eqb_c _ a x) || Cost.value (eqb_c _ b x)); [|discriminate].
    destruct (Cost.value (add_op_c so o)); autorewrite with galois_cost.
    + intro Heq; injection Heq as <-.
      eapply (schedule_credit (Ssa.val_enc (lssa lv)) HV inventory st _ x); try assumption.
      rewrite Hwork; cbn [length]; lia.
    + destruct (Cost.value (mul_op_c so o)); autorewrite with galois_cost; [|discriminate].
      intro Heq; injection Heq as <-.
      eapply (schedule_credit (Ssa.val_enc (lssa lv)) HV inventory st _ x); try assumption.
      rewrite Hwork; cbn [length]; lia.
Qed.

Local Lemma expand_credit {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix inventory
    st rest x next :
  (forall y data, Map.get (Ssa.val_enc (lssa lv)) y (indexed_values ix) = Some data ->
    In y inventory) ->
  pending st = Visit x :: rest -> unseen (Ssa.val_enc (lssa lv)) st x = true ->
  Cost.value (expand_c lv so ix st rest x) = Some next ->
  (command_credit (Ssa.val_enc (lssa lv)) inventory next <
    command_credit (Ssa.val_enc (lssa lv)) inventory st)%nat.
Proof.
  intros Hsource Hwork Hfresh; unfold expand_c; autorewrite with galois_cost.
  fold (Map.get (Ssa.val_enc (lssa lv)) x (indexed_values ix)).
  destruct (Map.get _ x (indexed_values ix)) as [[n d]|] eqn:Hget; [|discriminate].
  pose proof (Hsource x _ Hget) as Hin.
  autorewrite with galois_cost.
  destruct (Cost.value (lbody_c lv n)); autorewrite with galois_cost.
  - destruct d as [o args|header i|]; [|eapply expand_phi_credit; eassumption|discriminate].
    destruct args as [|a [|b [|extra rest_args]]]; autorewrite with galois_cost;
      try discriminate.
    + destruct (Cost.value (const_op_c so o)) as [z|]; autorewrite with galois_cost;
        [|discriminate].
      intro Heq; injection Heq as <-.
      exact (finish_credit (Ssa.val_enc (lssa lv)) HV inventory st (Visit x) rest x
        (SConst x z) None Hwork).
    + destruct (Cost.value (add_op_c so o)); autorewrite with galois_cost.
      * intro Heq; injection Heq as <-.
        eapply (schedule_credit (Ssa.val_enc (lssa lv)) HV inventory st _ x); try assumption.
        rewrite Hwork; cbn [length]; lia.
      * destruct (Cost.value (mul_op_c so o)); autorewrite with galois_cost; [|discriminate].
        intro Heq; injection Heq as <-.
        eapply (schedule_credit (Ssa.val_enc (lssa lv)) HV inventory st _ x); try assumption.
        rewrite Hwork; cbn [length]; lia.
  - intro Heq; injection Heq as <-.
    exact (finish_credit (Ssa.val_enc (lssa lv)) HV inventory st (Visit x) rest x
      (SOutside x) None Hwork).
Qed.

(** Every continuing command strictly spends the actual inventory-and-work potential. *)
Theorem producer_step_credit {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix inventory st next :
  (forall x data, Map.get (Ssa.val_enc (lssa lv)) x (indexed_values ix) = Some data ->
    In x inventory) ->
  Cost.value (producer_step_c lv so ix st) = inl next ->
  (command_credit (Ssa.val_enc (lssa lv)) inventory next <
    command_credit (Ssa.val_enc (lssa lv)) inventory st)%nat.
Proof.
  intros Hsource; unfold producer_step_c.
  destruct (pending st) as [|command rest] eqn:Hwork; [discriminate|].
  autorewrite with galois_cost; destruct command as [x|multiply x a b|x base update other kind first].
  all: autorewrite with galois_cost.
  - fold (Map.get (Ssa.val_enc (lssa lv)) x (completed st)).
    destruct (Map.get (Ssa.val_enc (lssa lv)) x (completed st)) as [old|] eqn:Hdone;
      autorewrite with galois_cost.
    + intro Heq; injection Heq as <-.
      unfold command_credit; cbn [pending].
      match goal with
      | |- context [remaining ?EV inventory ?after] =>
        assert (Hremaining : remaining EV inventory after = remaining EV inventory st)
          by (apply remaining_ext; intro y; reflexivity);
        rewrite Hremaining
      end.
      rewrite Hwork; cbn [length]; lia.
    + fold (FinSet.mem (Ssa.val_enc (lssa lv)) x (active st)).
      destruct (FinSet.mem (Ssa.val_enc (lssa lv)) x (active st)) eqn:Hactive; [discriminate|].
      destruct (Cost.value (expand_c lv so ix st rest x)) as [expanded|] eqn:Hexpand;
        [|discriminate].
      intro Heq; injection Heq as <-; eapply expand_credit; try eassumption.
      unfold unseen; rewrite Hdone, Hactive; reflexivity.
  - destruct (Cost.value (Map.get_c _ a (completed st))) as [ea|]; [|discriminate].
    autorewrite with galois_cost.
    destruct (Cost.value (Map.get_c _ b (completed st))) as [eb|]; [|discriminate].
    autorewrite with galois_cost; intro Heq; injection Heq as <-.
    exact (finish_credit (Ssa.val_enc (lssa lv)) HV inventory st
      (FinishBinary multiply x a b) rest x (if multiply then SMul x ea eb else SAdd x ea eb)
      None Hwork).
  - destruct (Cost.value (Map.get_c _ other (completed st))) as [e|]; [|discriminate].
    autorewrite with galois_cost; intro Heq; injection Heq as <-.
    exact (finish_credit (Ssa.val_enc (lssa lv)) HV inventory st
      (FinishPhi x base update other kind first) rest x (SPhi x)
      (Some (ScevBinding x base update kind (Some e) first)) Hwork).
Qed.

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

Local Lemma source_inventory_covered {N E V K G} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) inventory p x data :
  Map.get (Ssa.val_enc (lssa lv)) x (indexed_values (prepare_index lv inventory p)) = Some data ->
  In x inventory.
Proof.
  rewrite prepare_index_equation; cbn [indexed_values].
  rewrite scev_inventory_index_get by exact HV.
  destruct (existsb _ inventory) eqn:Hlisted; [intros _|discriminate].
  apply existsb_exists in Hlisted.
  destruct Hlisted as [y [Hin Hequal]].
  apply eqb_true_iff in Hequal; [subst y; exact Hin|exact HV].
Qed.

Local Lemma remaining_initial {V} (EV : encoding V) inventory target :
  remaining EV inventory (State [Visit target] FinSet.empty Map.empty [] [] []) = length inventory.
Proof.
  induction inventory as [|x rest IH]; cbn [remaining length]; [reflexivity|].
  unfold unseen; cbn [active completed].
  rewrite FinSet.mem_empty, Map.get_empty; cbn; rewrite IH; reflexivity.
Qed.

Local Lemma runs_credit {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix inventory :
  (forall x data, Map.get (Ssa.val_enc (lssa lv)) x (indexed_values ix) = Some data ->
    In x inventory) ->
  forall count st result, runs (producer_step_c lv so ix) count st result ->
  match result with
  | inl next => (count + command_credit (Ssa.val_enc (lssa lv)) inventory next <=
      command_credit (Ssa.val_enc (lssa lv)) inventory st)%nat
  | inr _ => True
  end.
Proof.
  intros Hsource count st result Hrun.
  induction Hrun as [st|count st result Hstop|count st next result Hstep Hrun IH].
  - cbn; lia.
  - exact I.
  - destruct result as [last|result]; [|exact I].
    pose proof (producer_step_credit lv HV so ix inventory st next Hsource Hstep) as Hdecrease.
    cbv beta iota zeta in IH |- *; lia.
Qed.

(** Every prepared-source command machine stops within its internally constructed budget. *)
Theorem command_budget_adequate {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) inventory p target :
  exists result, Cost.value (iterate (producer_step_c lv so (prepare_index lv inventory p))
    (Cost.value (command_fuel_c inventory))
    (State [Visit target] FinSet.empty Map.empty [] [] [])) = inr result.
Proof.
  pose proof (iterate_value (producer_step_c lv so (prepare_index lv inventory p))
    (Cost.value (command_fuel_c inventory))
    (State [Visit target] FinSet.empty Map.empty [] [] [])) as Hrun.
  destruct (Cost.value (iterate (producer_step_c lv so (prepare_index lv inventory p))
    (Cost.value (command_fuel_c inventory))
    (State [Visit target] FinSet.empty Map.empty [] [] []))) as [last|result] eqn:Hresult.
  - pose proof (runs_credit lv HV so (prepare_index lv inventory p) inventory
      (source_inventory_covered lv HV inventory p) _ _ _ Hrun) as Hcredit.
    cbv beta iota zeta in Hcredit; unfold command_credit in Hcredit.
    rewrite remaining_initial in Hcredit.
    change (Pos.to_nat (Cost.value (command_fuel_c inventory)) +
      (3 * remaining (Ssa.val_enc (lssa lv)) inventory last + length (pending last)) <=
      3 * length inventory + 1)%nat in Hcredit.
    pose proof (f_equal N.to_nat (command_fuel_value inventory)) as Hfuel.
    rewrite N2Nat.inj_mul, N2Nat.inj_add, Nat2N.id in Hfuel.
    change (Pos.to_nat (Cost.value (command_fuel_c inventory)) =
      4 * (length inventory + 1))%nat in Hfuel.
    lia.
  - exists result; reflexivity.
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

(** Prepared-source execution never conflates an exhausted command budget with rejection. *)
Theorem produce_no_exhaustion {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) inventory p target state :
  Cost.value (produce_c lv so (prepare_index lv inventory p) inventory target) <> OutOfFuel state.
Proof.
  destruct (command_budget_adequate lv HV so inventory p target) as [result Hstop].
  unfold produce_c; autorewrite with galois_cost.
  fold (@FinSet.empty V).
  change (Cost.value (@Map.empty_c V (scev_expr V))) with (@Map.empty V (scev_expr V)).
  rewrite Hstop; destruct result; discriminate.
Qed.

(** Checked execution exposes the exact plan, preparation trace and consumer tables used by the run. *)
Record execution (V : Type) := Execution {
  recurrence : Chrec.t V;
  plan : scev_plan V;
  preparation_reuses : list V;
  prepared_nodes : list V;
  checker_bindings : check_binding_memo V;
  checker_expressions : check_memo V;
  checker_events : trace;
  compiler_bindings : binding_memo V;
  compiler_expressions : compile_memo V;
  compiler_events : trace
}.
Arguments Execution {V}.
Arguments recurrence {V}.
Arguments plan {V}.
Arguments preparation_reuses {V}.
Arguments prepared_nodes {V}.
Arguments checker_bindings {V}.
Arguments checker_expressions {V}.
Arguments checker_events {V}.
Arguments compiler_bindings {V}.
Arguments compiler_expressions {V}.
Arguments compiler_events {V}.

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
          check_bindings (fst check_expressions) (snd check_expressions)
          compile_bindings (fst compile_expressions)
          (snd compile_expressions)))
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

Fixpoint invariant_variables {V} (e : iexpr V) : list V :=
  match e with
  | IVar x => [x]
  | IAdd a b | IMul a b => invariant_variables a ++ invariant_variables b
  | _ => []
  end.

(** Arrival observations reset on entry and count actual feedback edges in the same stay. *)
Definition stay_arrivals {N E V K G} (lv : loop_view N E V K G) (es : list E) : nat :=
  fold_left (fun count e =>
    if eqb (Cfg.edge_enc (Ssa.cfg (lssa lv))) e (lentry lv) then O else
    if eqb (Cfg.edge_enc (Ssa.cfg (lssa lv))) e (lback lv) then S count else count) es O.

Section Semantics.
Context {S O N E V K G C : Type}.
Context (m : semantics S O) (lv : loop_view N E V K G) (so : scev_ops K C).
Context (sl : SsaLink.t S O N E V C) (op_eval : K -> list C -> option C)
  (holds : G -> list C -> Prop) (inventory : list V).
Let sv := lssa lv.
Let lk := SsaLink.link sl.
Let graph := Cfg.graph (Ssa.cfg sv).
Let body := lbody lv.
Let val := SsaLink.val sl.
Let point := Link.point lk.
Let EV := Ssa.val_enc sv.
Let EN := Cfg.node_enc (Ssa.cfg sv).
Let EE := Cfg.edge_enc (Ssa.cfg sv).

(** Loop laws retain the original local SSA, ingress, phi-copy and back-source operation duties. *)
Record loop_laws : Prop := {
  loop_value_encoding : encoding_laws EV;
  loop_node_encoding : encoding_laws EN;
  loop_edge_encoding : encoding_laws EE;
  loop_ssa : ssa_laws m sv sl op_eval holds;
  loop_strict : strict_ssa_laws m sv sl;
  header_not_entry : ~ In (lheader lv) (Graph.entries graph);
  entry_edge : In (lentry lv) (Cfg.edges (Ssa.cfg sv)) /\
    Graph.target graph (lentry lv) = lheader lv /\ body (Graph.source graph (lentry lv)) = false;
  back_edge : In (lback lv) (Cfg.edges (Ssa.cfg sv)) /\
    Graph.target graph (lback lv) = lheader lv /\ body (Graph.source graph (lback lv)) = true;
  simple_header : forall e, In e (Cfg.edges (Ssa.cfg sv)) ->
    Graph.target graph e = lheader lv -> e = lentry lv \/ e = lback lv;
  header_inside : body (lheader lv) = true;
  initial_outside : forall n, In n (Graph.entries graph) -> body n = false;
  single_ingress : forall e, In e (Cfg.edges (Ssa.cfg sv)) ->
    body (Graph.source graph e) = false -> body (Graph.target graph e) = true -> e = lentry lv;
  phi_binding : forall e x i, on_steps m (fun s tr t =>
    Link.taken lk s tr t e -> Graph.target graph e = lheader lv ->
    Ssa.def sv x = Param (lheader lv) i ->
    val t x = match nth_error (Ssa.args sv e) i with Some y => val s y | None => None end);
  phi_stay : forall x i, on_steps m (fun s tr t =>
    Link.stays lk s tr t -> point s = lheader lv -> Ssa.def sv x = Param (lheader lv) i ->
    val t x = val s x);
  bound_outside : forall tst y, ltest lv = Some tst ->
    In y (invariant_variables (t_bound tst)) -> body (Ssa.home sv y) = false;
  back_test : on_steps m (fun s tr t => Link.taken lk s tr t (lback lv) ->
    forall tst, ltest lv = Some tst -> exists c, val s (t_lhs tst) = Some c /\
      test_holds (width_of so) (t_sign tst) (t_cmp tst) (to_Z so c)
        (eval_iexpr (inv_env sl so s) (t_bound tst)));
  operations_at_back : forall p x o args c, on_steps m (fun s tr t =>
    Link.taken lk s tr t (lback lv) -> scev_plan_check lv so inventory p = true ->
    In x (scev_plan_operations p) -> Ssa.def sv x = Op o args -> val s x = Some c ->
    exists cs, Forall2 (fun y d => val s y = Some d) args cs /\ op_eval o cs = Some c)
}.

(** Steps wholly inside the body preserve every exact outside-home option value. *)
Theorem body_step_outside_frame (Hloop : loop_laws) s tr t x :
  reachable_state m s -> step m s tr t -> body (point s) = true -> body (point t) = true ->
  body (Ssa.home sv x) = false -> val t x = val s x.
Proof.
  intros Hreachable Hstep Hinside Hinside' Houtside.
  destruct (edge_covers (link_ok (loop_ssa Hloop)) s tr t Hreachable Hstep)
    as [Hstay|[e Htaken]].
  - apply (frame_in_stay (loop_strict Hloop) x s tr t Hreachable Hstep Hstay).
    intro Hequal; change (point s = Ssa.home sv x) in Hequal.
    rewrite Hequal in Hinside; congruence.
  - apply (frame_on_edge (loop_strict Hloop) e x s tr t Hreachable Hstep Htaken).
    intro Hequal; change (Ssa.home sv x = point t) in Hequal.
    rewrite Hequal in Houtside; congruence.
Qed.

(** Header phi options survive actual stays at the header and at every other program point. *)
Theorem phi_stay_frame (Hloop : loop_laws) s tr t x i :
  reachable_state m s -> step m s tr t -> Link.stays lk s tr t ->
  Ssa.def sv x = Param (lheader lv) i -> Ssa.home sv x = lheader lv -> val t x = val s x.
Proof.
  intros Hreachable Hstep Hstay Hdef Hhome.
  destruct (eqb_spec EN (loop_node_encoding Hloop) (point s) (lheader lv))
    as [Hequal|Hdifferent].
  - exact (phi_stay Hloop x i s tr t Hreachable Hstep Hstay Hequal Hdef).
  - apply (frame_in_stay (loop_strict Hloop) x s tr t Hreachable Hstep Hstay).
    rewrite Hhome; exact Hdifferent.
Qed.

(** A same-stay history with no new header edge preserves every header phi option. *)
Theorem phi_run_frame (Hloop : loop_laws) s es t x i :
  reachable_state m s -> run_edges m lk s es t ->
  Forall (fun e => Graph.target graph e <> lheader lv) es ->
  Ssa.def sv x = Param (lheader lv) i -> Ssa.home sv x = lheader lv -> val t x = val s x.
Proof.
  intros Hreachable Hrun; revert Hreachable.
  induction Hrun as [s|s tr u e es t Hstep Htaken Hrun IH|
    s tr u es t Hstep Hstay Hrun IH]; intros Hreachable Hedges Hdef Hhome; [reflexivity| |].
  - inversion Hedges as [|edge edges Htarget Htail]; subst.
    rewrite (IH (reachable_state_step m s tr u Hreachable Hstep) Htail Hdef Hhome).
    apply (frame_on_edge (loop_strict Hloop) e x s tr u Hreachable Hstep Htaken).
    destruct (taken_edge (link_ok (loop_ssa Hloop)) e s tr u Hreachable Hstep Htaken)
      as [_ Hpoint].
    change (Graph.target graph e = point u) in Hpoint.
    change (Ssa.home sv x <> point u).
    rewrite Hhome, <- Hpoint; congruence.
  - rewrite (IH (reachable_state_step m s tr u Hreachable Hstep) Hedges Hdef Hhome).
    eapply phi_stay_frame; eassumption.
Qed.

(** Body-restricted actual transition histories preserve the same source outside values. *)
Theorem body_run_outside_frame (Hloop : loop_laws) s tr t :
  reachable_state m s ->
  run_steps m (fun a _ b => body (point a) = true /\ body (point b) = true) s tr t ->
  forall x, body (Ssa.home sv x) = false -> val t x = val s x.
Proof.
  intros Hreachable Hrun; revert Hreachable.
  induction Hrun as [s|s events u rest t [Hinside Hinside'] Hstep Hrun IH];
    intros Hreachable x Houtside; [reflexivity|].
  rewrite (IH (reachable_state_step m s events u Hreachable Hstep) x Houtside).
  eapply body_step_outside_frame; eassumption.
Qed.

Section PlanSemantics.
Context (p : scev_plan V) (lookup : V -> option (Chrec.t V)).
Let ix := prepare_index lv inventory p.

(** Completed equations connect every listed phi to its final-environment binding translation. *)
Definition compilation_equations : Prop :=
  forall b c, In b (sp_bindings p) -> lookup (sb_phi b) = Some c ->
    scev_translate_binding lookup b = Some c.

(** Simultaneous phi values refer to one environment, index and actual concrete source state. *)
Definition phi_values inv k s : Prop :=
  forall x c d, In x (List.map sb_phi (sp_bindings p)) ->
    lookup x = Some c -> val s x = Some d ->
    to_Z so d = wrap (width_of so) (Chrec.eval inv c k).

(** A consistent state supports every invariant environment matching its own outside-home values. *)
Definition state_consistent k s : Prop :=
  forall inv, (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so s x) ->
    phi_values inv k s.

Local Lemma binding_conditions_member bs start :
  bindings_conditions lv so ix start bs ->
  forall b, In b bs -> exists rank, binding_conditions lv so ix
    (phi_before EV ix rank) b.
Proof.
  revert start; induction bs as [|b rest IH]; intros start Hconditions x Hin; [contradiction|].
  destruct Hconditions as [Hhead Hrest]; destruct Hin as [<-|Hin].
  - exists start; exact Hhead.
  - eapply IH; eassumption.
Qed.

Local Lemma checked_binding_conditions (Hloop : loop_laws) b :
  scev_plan_check lv so inventory p = true -> In b (sp_bindings p) ->
  exists rank, binding_conditions lv so ix (phi_before EV ix rank) b.
Proof.
  rewrite scev_plan_check_correct by
    first [exact (loop_node_encoding Hloop)|exact (loop_value_encoding Hloop)].
  intros [_ [_ [_ [Hbindings _]]]]; apply (binding_conditions_member _ 0%nat Hbindings).
Qed.

Local Lemma before_member (Hloop : loop_laws) rank x :
  phi_before EV ix rank x = true -> In x (List.map sb_phi (sp_bindings p)).
Proof.
  unfold phi_before, phi_before_c; autorewrite with galois_cost.
  unfold ix; rewrite prepare_index_equation; cbn [phi_index].
  change ((match Map.get EV x (ranks (prepare_ranks EV 0%nat (sp_bindings p))) with
    | Some i => Nat.ltb i rank
    | None => false
    end) = true -> In x (List.map sb_phi (sp_bindings p))).
  destruct (Map.get EV x (ranks (prepare_ranks EV 0%nat (sp_bindings p)))) as [i|] eqn:Hrank;
    [intros _|discriminate].
  apply (proj1 (prepare_ranks_mem EV (loop_value_encoding Hloop) (sp_bindings p) 0%nat x)).
  apply Map.mem_spec; exists i; exact Hrank.
Qed.

Local Lemma binary_operands s operations update phi other (first : bool) o d combine :
  (forall a b, combine a b = combine b a) ->
  (forall a b r, op_eval o [a; b] = Some r ->
    to_Z so r = wrap (width_of so) (combine (to_Z so a) (to_Z so b))) ->
  operation_equations sv sl op_eval s operations -> In update operations ->
  Ssa.def sv update = Op o (if first then [phi; other] else [other; phi]) ->
  val s update = Some d ->
  exists a b, val s phi = Some a /\ val s other = Some b /\
    to_Z so d = wrap (width_of so) (combine (to_Z so a) (to_Z so b)).
Proof.
  intros Hcomm Heval Hlocal Hin Hdef Hvalue.
  destruct (Hlocal update o _ d Hin Hdef Hvalue) as [cs [Hcs Hresult]].
  destruct first.
  - destruct (forall2_pair _ _ _ _ Hcs) as [a [b [-> [Ha Hb]]]].
    exists a, b; split; [exact Ha|]; split; [exact Hb|apply Heval; exact Hresult].
  - destruct (forall2_pair _ _ _ _ Hcs) as [b [a [-> [Hb Ha]]]].
    exists a, b; split; [exact Ha|]; split; [exact Hb|].
    rewrite Hcomm; apply Heval; exact Hresult.
Qed.

Local Lemma binding_initial b c inv :
  scev_translate_binding lookup b = Some c -> Chrec.eval inv c 0%nat = inv (sb_base b).
Proof.
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [scev_translate_binding sb_kind sb_other sb_base]; try discriminate.
  all: try (destruct (scev_translate_expr lookup e); [|discriminate]).
  all: intro Happly; exact (proj1 (Idiom.apply_sound _ _ _ _ Happly inv)).
Qed.

Local Lemma other_expression_sound (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval)
    rank e inv k s update c d :
  (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so s x) ->
  phi_values inv k s ->
  expression_conditions EV (lbody_c lv) (indexed_values ix) so (phi_before EV ix rank) e ->
  scev_translate_expr lookup e = Some c ->
  operation_equations sv sl op_eval s (update :: scev_expr_operations e) ->
  val s (scev_expr_root e) = Some d ->
  to_Z so d = wrap (width_of so) (Chrec.eval inv c k).
Proof.
  intros Hinv Hphis Hexpr Htranslation Hlocal Hvalue.
  eapply expression_value_sound; [exact Hops|exact Hinv| | |exact Htranslation| |exact Hvalue].
  - intros x own value Hearlier Hlookup Hactual.
    apply (Hphis x own value (before_member Hloop rank x Hearlier) Hlookup Hactual).
  - apply (prepared_expression_source lv (loop_value_encoding Hloop) so inventory p); exact Hexpr.
  - intros x o args value Hin Hdef Hactual.
    exact (Hlocal x o args value (or_intror Hin) Hdef Hactual).
Qed.

(** Actual feedback-update values equal the next recurrence point for each supported idiom. *)
Theorem binding_update_sound (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval)
    rank b inv k s c d :
  (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so s x) ->
  phi_values inv k s -> In b (sp_bindings p) -> lookup (sb_phi b) = Some c ->
  binding_conditions lv so ix (phi_before EV ix rank) b ->
  scev_translate_binding lookup b = Some c ->
  operation_equations sv sl op_eval s (sb_update_value b ::
    match sb_other b with Some e => scev_expr_operations e | None => [] end) ->
  val s (sb_update_value b) = Some d ->
  to_Z so d = wrap (width_of so) (Chrec.eval inv c (Datatypes.S k)).
Proof.
  intros Hinv Hphis Hmember Hlookup [_ [Hupdate Hexpr]] Htranslation Hlocal Hvalue.
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [update_conditions sb_kind sb_other sb_base sb_phi sb_update_value sb_phi_first]
      in Hupdate, Hexpr, Htranslation, Hlookup, Hlocal, Hvalue |- *; try contradiction.
  - cbn [scev_translate_binding sb_kind sb_other sb_base] in Htranslation.
    destruct (scev_translate_expr lookup e) as [other|] eqn:Hother; [|discriminate].
    destruct Hupdate as [_ [n [o [Hget [Hinside Hflag]]]]].
    destruct (prepared_value_source lv (loop_value_encoding Hloop) inventory p update _ Hget)
      as [_ Hsource]; injection Hsource as Hhome Hdef.
    assert (Hdefinition : Ssa.def sv update =
      Op o (if first then [phi; scev_expr_root e] else [scev_expr_root e; phi])).
    { destruct first; exact (eq_sym Hdef). }
    destruct (binary_operands s _ update phi (scev_expr_root e) first o d Z.add Z.add_comm
      (fun a b r => addition_sound _ _ Hops o a b r Hflag) Hlocal (or_introl eq_refl)
      Hdefinition Hvalue) as [a [b [Ha [Hb Hresult]]]].
    pose proof (Hphis phi c a (in_map sb_phi _ _ Hmember) Hlookup Ha) as Hphi.
    pose proof (other_expression_sound Hloop Hops rank e inv k s update other b
      Hinv Hphis Hexpr Hother Hlocal Hb) as Hrhs.
    rewrite (proj2 (Idiom.apply_sound _ _ _ _ Htranslation inv) k).
    rewrite Hresult, Hphi, Hrhs; symmetry; apply wrap_add.
  - cbn [scev_translate_binding sb_kind sb_other sb_base] in Htranslation.
    destruct (scev_translate_expr lookup e) as [other|] eqn:Hother; [|discriminate].
    destruct Hupdate as [_ [n [o [Hget [Hinside Hflag]]]]].
    destruct (prepared_value_source lv (loop_value_encoding Hloop) inventory p update _ Hget)
      as [_ Hsource]; injection Hsource as Hhome Hdef.
    assert (Hdefinition : Ssa.def sv update =
      Op o (if first then [phi; scev_expr_root e] else [scev_expr_root e; phi])).
    { destruct first; exact (eq_sym Hdef). }
    destruct (binary_operands s _ update phi (scev_expr_root e) first o d Z.mul Z.mul_comm
      (fun a b r => multiplication_sound _ _ Hops o a b r Hflag) Hlocal (or_introl eq_refl)
      Hdefinition Hvalue) as [a [b [Ha [Hb Hresult]]]].
    pose proof (Hphis phi c a (in_map sb_phi _ _ Hmember) Hlookup Ha) as Hphi.
    pose proof (other_expression_sound Hloop Hops rank e inv k s update other b
      Hinv Hphis Hexpr Hother Hlocal Hb) as Hrhs.
    rewrite (proj2 (Idiom.apply_sound _ _ _ _ Htranslation inv) k).
    rewrite Hresult, Hphi, Hrhs; symmetry; apply wrap_mul.
  - cbn [scev_translate_binding sb_kind sb_other sb_base] in Htranslation.
    destruct Hupdate as [Hfirst [n [o [Hget [Hinside Hflag]]]]]; subst first.
    destruct (prepared_value_source lv (loop_value_encoding Hloop) inventory p update _ Hget)
      as [_ Hsource]; injection Hsource as Hhome Hdef.
    destruct (binary_operands s _ update phi phi true o d Z.add Z.add_comm
      (fun a b r => addition_sound _ _ Hops o a b r Hflag) Hlocal (or_introl eq_refl)
      (eq_sym Hdef) Hvalue) as [a [b [Ha [Hb Hresult]]]].
    assert (Hequal : a = b) by congruence; subst b.
    pose proof (Hphis phi c a (in_map sb_phi _ _ Hmember) Hlookup Ha) as Hphi.
    rewrite (proj2 (Idiom.apply_sound _ _ _ _ Htranslation inv) k).
    rewrite Hresult, Hphi; symmetry; apply wrap_add.
Qed.

Local Lemma binding_operations b :
  In b (sp_bindings p) ->
  incl (sb_update_value b :: match sb_other b with Some e => scev_expr_operations e | None => [] end)
    (scev_plan_operations p).
Proof.
  intros Hb x Hx; unfold scev_plan_operations; apply in_flat_map; exists b; auto.
Qed.

Local Lemma state_frames k s t :
  (forall x, body (Ssa.home sv x) = false -> val t x = val s x) ->
  (forall x, In x (List.map sb_phi (sp_bindings p)) -> val t x = val s x) ->
  state_consistent k s -> state_consistent k t.
Proof.
  intros Houtside Hphi Hstate inv Hinv x c d Hin Hlookup Hvalue.
  assert (Hmatch : forall y, body (Ssa.home sv y) = false -> inv y = inv_env sl so s y).
  { intros y Hy; rewrite Hinv by exact Hy; unfold inv_env; rewrite Houtside by exact Hy;
      reflexivity. }
  rewrite Hphi in Hvalue by exact Hin; exact (Hstate inv Hmatch x c d Hin Hlookup Hvalue).
Qed.

(** Actual loop entry initializes every compiled recurrence from its selected outside base. *)
Theorem entry_values (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval)
    (Hequations : compilation_equations) s tr t :
  scev_plan_check lv so inventory p = true ->
  reachable_state m s -> step m s tr t -> Link.taken lk s tr t (lentry lv) ->
  state_consistent 0%nat t.
Proof.
  intros Hcheck Hreachable Hstep Htaken inv Hinv x c d Hin Hlookup Hvalue.
  apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
  destruct (checked_binding_conditions Hloop b Hcheck Hb) as [rank [Hheader Hupdate]].
  destruct (prepared_header_source lv (loop_value_encoding Hloop) inventory p b Hheader)
    as [Hhome [Hbase [Hupdate_home [i [Hdef [Hentry Hback]]]]]].
  fold sv in Hhome, Hbase, Hupdate_home, Hdef, Hentry, Hback.
  fold body in Hbase, Hupdate_home.
  destruct (taken_edge (link_ok (loop_ssa Hloop)) (lentry lv) s tr t Hreachable Hstep Htaken)
    as [_ Htarget].
  change (Graph.target graph (lentry lv) = point t) in Htarget.
  destruct (entry_edge Hloop) as [_ [Hentry_target _]].
  assert (Hpoint : point t = lheader lv) by congruence.
  pose proof (phi_binding Hloop (lentry lv) (sb_phi b) i s tr t
    Hreachable Hstep Htaken Hentry_target Hdef) as Hcopy.
  rewrite Hentry in Hcopy; change (val t (sb_phi b) = val s (sb_base b)) in Hcopy.
  rewrite Hcopy in Hvalue.
  assert (Hframe : val t (sb_base b) = val s (sb_base b)).
  { apply (frame_on_edge (loop_strict Hloop) (lentry lv) (sb_base b) s tr t
      Hreachable Hstep Htaken).
    change (Ssa.home sv (sb_base b) <> point t).
    rewrite Hpoint; intro Hequal; rewrite Hequal in Hbase.
    pose proof (header_inside Hloop); congruence. }
  rewrite (binding_initial b c inv (Hequations b c Hb Hlookup)), Hinv by exact Hbase.
  unfold inv_env; fold val; rewrite Hframe, Hvalue; apply (observation_canonical _ _ Hops).
Qed.

(** Actual feedback copies the checked updates and advances all recurrences in the same environment. *)
Theorem back_values (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval)
    (Hequations : compilation_equations) s tr t k :
  scev_plan_check lv so inventory p = true ->
  reachable_state m s -> step m s tr t -> Link.taken lk s tr t (lback lv) ->
  state_consistent k s -> state_consistent (Datatypes.S k) t.
Proof.
  intros Hcheck Hreachable Hstep Htaken Hstate inv Hinv x c d Hin Hlookup Hvalue.
  destruct (link_taken_edge m (Ssa.cfg sv) lk s tr t (lback lv)
    (link_ok (loop_ssa Hloop)) Hreachable Hstep Htaken) as [_ [Hsource Htarget]].
  change (Graph.source graph (lback lv) = point s) in Hsource.
  change (Graph.target graph (lback lv) = point t) in Htarget.
  destruct (back_edge Hloop) as [_ [Hback_target Hback_inside]].
  assert (Hinside : body (point s) = true) by (rewrite <- Hsource; exact Hback_inside).
  assert (Hinside' : body (point t) = true).
  { rewrite <- Htarget, Hback_target; exact (header_inside Hloop). }
  assert (Hmatch : forall y, body (Ssa.home sv y) = false -> inv y = inv_env sl so s y).
  { intros y Hy; rewrite Hinv by exact Hy; unfold inv_env; fold val.
    rewrite (body_step_outside_frame Hloop s tr t y Hreachable Hstep Hinside Hinside' Hy);
      reflexivity. }
  apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
  destruct (checked_binding_conditions Hloop b Hcheck Hb) as [rank Hbinding].
  destruct (prepared_header_source lv (loop_value_encoding Hloop) inventory p b (proj1 Hbinding))
    as [Hhome [Hbase [Hupdate_home [i [Hdef [Hentry Hback]]]]]].
  fold sv in Hhome, Hbase, Hupdate_home, Hdef, Hentry, Hback.
  fold body in Hbase, Hupdate_home.
  pose proof (phi_binding Hloop (lback lv) (sb_phi b) i s tr t
    Hreachable Hstep Htaken Hback_target Hdef) as Hcopy.
  rewrite Hback in Hcopy; change (val t (sb_phi b) = val s (sb_update_value b)) in Hcopy.
  rewrite Hcopy in Hvalue.
  eapply binding_update_sound; [exact Hloop|exact Hops|exact Hmatch|
    exact (Hstate inv Hmatch)|exact Hb|exact Hlookup|exact Hbinding|
    exact (Hequations b c Hb Hlookup)| |exact Hvalue].
  intros y o args value Hy Hdefinition Hactual.
  exact (operations_at_back Hloop p y o args value s tr t Hreachable Hstep Htaken Hcheck
    (binding_operations b Hb y Hy) Hdefinition Hactual).
Qed.

Local Lemma ordinary_edge_inside (Hloop : loop_laws) s tr t e :
  reachable_state m s -> step m s tr t -> Link.taken lk s tr t e ->
  e <> lentry lv -> e <> lback lv -> body (point t) = true ->
  body (point s) = true /\ Graph.target graph e <> lheader lv.
Proof.
  intros Hreachable Hstep Htaken Hentry Hback Hinside'.
  destruct (link_taken_edge m (Ssa.cfg sv) lk s tr t e (link_ok (loop_ssa Hloop))
    Hreachable Hstep Htaken) as [Hlisted [Hsource Htarget]].
  change (Graph.source graph e = point s) in Hsource.
  change (Graph.target graph e = point t) in Htarget.
  split.
  - destruct (body (point s)) eqn:Hinside; [reflexivity|].
    exfalso; apply Hentry; apply (single_ingress Hloop e Hlisted);
      [rewrite Hsource; exact Hinside|rewrite Htarget; exact Hinside'].
  - intro Hequal; destruct (simple_header Hloop e Hlisted Hequal); contradiction.
Qed.

Local Lemma arrivals_snoc es e :
  stay_arrivals lv (es ++ [e]) =
    if eqb EE e (lentry lv) then 0%nat else
    if eqb EE e (lback lv) then Datatypes.S (stay_arrivals lv es) else stay_arrivals lv es.
Proof.
  unfold stay_arrivals; rewrite fold_left_app; reflexivity.
Qed.

Local Lemma history_induction s0 (P : S -> list E -> Prop) :
  (forall s tr t e prefix, reachable_state m s -> run_edges m lk s0 prefix s -> P s prefix ->
    step m s tr t -> Link.taken lk s tr t e -> P t (prefix ++ [e])) ->
  (forall s tr t prefix, reachable_state m s -> run_edges m lk s0 prefix s -> P s prefix ->
    step m s tr t -> Link.stays lk s tr t -> P t prefix) ->
  forall es s, run_edges m lk s0 es s -> reachable_state m s0 -> P s0 [] -> P s es.
Proof.
  intros Hedge Hstay es s Hrun Hreachable Hinitial.
  assert (Hgeneral : forall start edges stop, run_edges m lk start edges stop ->
    forall prefix, reachable_state m start -> run_edges m lk s0 prefix start ->
    P start prefix -> P stop (prefix ++ edges)).
  { intros start edges stop Hhistory; induction Hhistory as [u|
      u tr v e edges t Hstep Htaken Hhistory IH|u tr v edges t Hstep Hstays Hhistory IH];
      intros prefix Hreach Hprefix HP.
    - rewrite app_nil_r; exact HP.
    - replace (prefix ++ e :: edges) with ((prefix ++ [e]) ++ edges)
        by (rewrite <- app_assoc; reflexivity).
      apply IH; [eapply reachable_state_step; eassumption| |eapply Hedge; eassumption].
      eapply run_edges_app; [exact Hprefix|eapply run_take; [exact Hstep|exact Htaken|constructor]].
    - apply IH; [eapply reachable_state_step; eassumption| |eapply Hstay; eassumption].
      rewrite <- (app_nil_r prefix); eapply run_edges_app; [exact Hprefix|].
      eapply run_stay; [exact Hstep|exact Hstays|constructor]. }
  exact (Hgeneral s0 es s Hrun [] Hreachable (run_refl s0) Hinitial).
Qed.

(** Every actual body state satisfies all checked-plan recurrences at its current stay arrival index. *)
Theorem scev_plan_run_sound (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval)
    (Hequations : compilation_equations) s0 es s :
  scev_plan_check lv so inventory p = true -> initial m s0 -> run_edges m lk s0 es s ->
  body (point s) = true -> state_consistent (stay_arrivals lv es) s.
Proof.
  intros Hcheck Hinitial Hrun.
  eapply (history_induction s0 (fun u prefix =>
    body (point u) = true -> state_consistent (stay_arrivals lv prefix) u));
    [| |exact Hrun|exists s0, []; split; [exact Hinitial|constructor]|].
  - intros u tr t e prefix Hreachable Hprefix Hstate Hstep Htaken Hinside'.
    destruct (eqb EE e (lentry lv)) eqn:Hentry.
    + apply eqb_true_iff in Hentry; [subst e|exact (loop_edge_encoding Hloop)].
      rewrite arrivals_snoc, eqb_refl; eapply entry_values; eassumption.
    + destruct (eqb EE e (lback lv)) eqn:Hback.
      * rewrite arrivals_snoc, Hentry, Hback.
        apply eqb_true_iff in Hback; [subst e|exact (loop_edge_encoding Hloop)].
        eapply back_values; try eassumption; apply Hstate.
        destruct (link_taken_edge m (Ssa.cfg sv) lk u tr t (lback lv)
          (link_ok (loop_ssa Hloop)) Hreachable Hstep Htaken) as [_ [Hsource _]].
        change (Graph.source graph (lback lv) = point u) in Hsource.
        rewrite <- Hsource; exact (proj2 (proj2 (back_edge Hloop))).
      * rewrite arrivals_snoc, Hentry, Hback.
        apply (proj1 (eqb_false_iff EE (loop_edge_encoding Hloop) e (lentry lv))) in Hentry.
        apply (proj1 (eqb_false_iff EE (loop_edge_encoding Hloop) e (lback lv))) in Hback.
        destruct (ordinary_edge_inside Hloop u tr t e Hreachable Hstep Htaken Hentry Hback Hinside')
          as [Hinside Htarget].
        apply (state_frames _ u t); [| |exact (Hstate Hinside)].
        -- intros x Houtside; eapply body_step_outside_frame; eassumption.
        -- intros x Hin; apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
           destruct (checked_binding_conditions Hloop b Hcheck Hb) as [rank [Hheader _]].
           destruct (prepared_header_source lv (loop_value_encoding Hloop) inventory p b Hheader)
             as [Hhome _].
           fold sv in Hhome.
           apply (frame_on_edge (loop_strict Hloop) e (sb_phi b) u tr t
             Hreachable Hstep Htaken).
           destruct (taken_edge (link_ok (loop_ssa Hloop)) e u tr t Hreachable Hstep Htaken)
             as [_ Hpoint].
           change (Graph.target graph e = point t) in Hpoint.
           change (Ssa.home sv (sb_phi b) <> point t).
           rewrite Hhome, <- Hpoint; congruence.
  - intros u tr t prefix Hreachable Hprefix Hstate Hstep Hstay Hinside'.
    assert (Hinside : body (point u) = true).
    { pose proof (stays_point (link_ok (loop_ssa Hloop)) u tr t Hreachable Hstep Hstay)
        as Hpoints.
      change (point t = point u) in Hpoints; rewrite <- Hpoints; exact Hinside'. }
    apply (state_frames _ u t); [| |exact (Hstate Hinside)].
    + intros x Houtside; eapply body_step_outside_frame; eassumption.
    + intros x Hin; apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
      destruct (checked_binding_conditions Hloop b Hcheck Hb) as [rank [Hheader _]].
      destruct (prepared_header_source lv (loop_value_encoding Hloop) inventory p b Hheader)
        as [Hhome [_ [_ [i [Hdef _]]]]].
      eapply phi_stay_frame; eassumption.
  - intro Hinside.
    pose proof (entry_points (link_ok (loop_ssa Hloop)) s0 Hinitial) as Hentry.
    pose proof (initial_outside Hloop _ Hentry) as Houtside.
    change (body (point s0) = false) in Houtside; congruence.
Qed.

Local Lemma invariant_eval_agree (a b : V -> Z) e :
  (forall x, In x (invariant_variables e) -> a x = b x) ->
  eval_iexpr a e = eval_iexpr b e.
Proof.
  induction e as [x|z|z|l IHl r IHr|l IHl r IHr]; intro Hagree; cbn [eval_iexpr];
    try reflexivity.
  - apply Hagree; left; reflexivity.
  - rewrite IHl, IHr; try reflexivity; intros x Hin; apply Hagree;
      cbn [invariant_variables]; apply in_app_iff; auto.
  - rewrite IHl, IHr; try reflexivity; intros x Hin; apply Hagree;
      cbn [invariant_variables]; apply in_app_iff; auto.
Qed.

Local Lemma test_congruent w sg cmp a a' b b' :
  wrap w a = wrap w a' -> wrap w b = wrap w b' ->
  test_holds w sg cmp a b <-> test_holds w sg cmp a' b'.
Proof.
  intros Ha Hb; unfold test_holds.
  rewrite (Failure.view_z_congruent w sg a a' Ha), (Failure.view_z_congruent w sg b b' Hb);
    reflexivity.
Qed.

(** Normalized trip evidence denotes the original exact wrapped first failure. *)
Definition normalized_trip (inv : V -> Z) (tst : loop_test V) c t : Prop :=
  Failure.trip_count (fun x => view_z (width_of so) (t_sign tst) (inv x))
    (width_of so) (t_sign tst) (t_cmp tst) (signed_chrec (width_of so) (t_sign tst) c)
    (signed_iexpr (width_of so) (t_sign tst) (t_bound tst)) = Some t.

Local Lemma normalized_failure_excludes_guard inv tst c t k :
  normalized_trip inv tst c t ->
  test_holds (width_of so) (t_sign tst) (t_cmp tst) (Chrec.eval inv c k)
    (eval_iexpr inv (t_bound tst)) -> N.of_nat k <> t.
Proof.
  intros Htrip Hguard Hequal.
  destruct (Failure.trip_count_first_failure _ _ _ _ _ _ t Htrip) as [_ Hfailed].
  rewrite <- Hequal, Nat2N.id in Hfailed; apply Hfailed.
  apply (proj1 (test_congruent _ _ _ _ _ _ _
    (signed_chrec_wrap (width_of so) (t_sign tst) inv c k)
    (signed_iexpr_wrap (width_of so) (t_sign tst) inv (t_bound tst)))).
  exact Hguard.
Qed.

Local Lemma back_recurrence_guard (Hloop : loop_laws) tst c s tr t inv k :
  ltest lv = Some tst -> In (t_lhs tst) (List.map sb_phi (sp_bindings p)) ->
  lookup (t_lhs tst) = Some c ->
  reachable_state m s -> step m s tr t -> Link.taken lk s tr t (lback lv) ->
  (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so s x) ->
  phi_values inv k s ->
  test_holds (width_of so) (t_sign tst) (t_cmp tst) (Chrec.eval inv c k)
    (eval_iexpr inv (t_bound tst)).
Proof.
  intros Htest Hmember Hlookup Hreachable Hstep Htaken Hinv Hphis.
  destruct (back_test Hloop s tr t Hreachable Hstep Htaken tst Htest)
    as [actual [Hvalue Hguard]].
  pose proof (Hphis (t_lhs tst) c actual Hmember Hlookup Hvalue) as Hphi.
  assert (Hbound : eval_iexpr inv (t_bound tst) = eval_iexpr (inv_env sl so s) (t_bound tst)).
  { apply invariant_eval_agree; intros x Hin; apply Hinv; eapply bound_outside; eassumption. }
  assert (Hwrapped : wrap (width_of so) (to_Z so actual) =
    wrap (width_of so) (Chrec.eval inv c k)) by (rewrite Hphi, wrap_wrap; reflexivity).
  exact (proj1 (test_congruent (width_of so) (t_sign tst) (t_cmp tst)
    (to_Z so actual) (Chrec.eval inv c k) (eval_iexpr (inv_env sl so s) (t_bound tst))
    (eval_iexpr inv (t_bound tst)) Hwrapped ltac:(rewrite Hbound; reflexivity)) Hguard).
Qed.

Local Lemma environment_step (Hloop : loop_laws) s tr t inv :
  reachable_state m s -> step m s tr t -> body (point s) = true -> body (point t) = true ->
  (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so t x) ->
  forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so s x.
Proof.
  intros Hreachable Hstep Hinside Hinside' Hinv x Houtside.
  rewrite Hinv by exact Houtside; unfold inv_env; fold val.
  rewrite (body_step_outside_frame Hloop s tr t x Hreachable Hstep Hinside Hinside' Houtside);
    reflexivity.
Qed.

(** A checked plan's exact first failure bounds every arrival in its actual stay environment. *)
Theorem scev_plan_trip_bound (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval)
    (Hequations : compilation_equations) tst c :
  scev_plan_check lv so inventory p = true ->
  ltest lv = Some tst -> In (t_lhs tst) (List.map sb_phi (sp_bindings p)) ->
  lookup (t_lhs tst) = Some c ->
  forall s0 es s, initial m s0 -> run_edges m lk s0 es s -> body (point s) = true ->
  forall inv t, (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so s x) ->
  normalized_trip inv tst c t -> (N.of_nat (stay_arrivals lv es) <= t)%N.
Proof.
  intros Hcheck Htest Hmember Hlookup s0 es s Hinitial Hrun.
  eapply (history_induction s0 (fun u prefix => body (point u) = true ->
    forall inv t, (forall x, body (Ssa.home sv x) = false -> inv x = inv_env sl so u x) ->
      normalized_trip inv tst c t -> (N.of_nat (stay_arrivals lv prefix) <= t)%N));
    [| |exact Hrun|exists s0, []; split; [exact Hinitial|constructor]|].
  - intros u events v e prefix Hreachable Hprefix Hbound Hstep Htaken Hinside' inv t Hinv Htrip.
    destruct (eqb EE e (lentry lv)) eqn:Hentry.
    + rewrite arrivals_snoc, Hentry; apply N.le_0_l.
    + destruct (eqb EE e (lback lv)) eqn:Hback.
      * rewrite arrivals_snoc, Hentry, Hback, Nat2N.inj_succ.
        apply eqb_true_iff in Hback; [subst e|exact (loop_edge_encoding Hloop)].
        destruct (link_taken_edge m (Ssa.cfg sv) lk u events v (lback lv)
          (link_ok (loop_ssa Hloop)) Hreachable Hstep Htaken) as [_ [Hsource _]].
        change (Graph.source graph (lback lv) = point u) in Hsource.
        assert (Hinside : body (point u) = true)
          by (rewrite <- Hsource; exact (proj2 (proj2 (back_edge Hloop)))).
        pose proof (environment_step Hloop u events v inv Hreachable Hstep Hinside Hinside' Hinv)
          as Hmatch.
        specialize (Hbound Hinside inv t Hmatch Htrip).
        pose proof (scev_plan_run_sound Hloop Hops Hequations s0 prefix u Hcheck Hinitial Hprefix
          Hinside inv Hmatch) as Hphis.
        pose proof (back_recurrence_guard Hloop tst c u events v inv (stay_arrivals lv prefix)
          Htest Hmember Hlookup Hreachable Hstep Htaken Hmatch Hphis) as Hguard.
        pose proof (normalized_failure_excludes_guard inv tst c t _ Htrip Hguard); lia.
      * rewrite arrivals_snoc, Hentry, Hback.
        apply (proj1 (eqb_false_iff EE (loop_edge_encoding Hloop) e (lentry lv))) in Hentry.
        apply (proj1 (eqb_false_iff EE (loop_edge_encoding Hloop) e (lback lv))) in Hback.
        destruct (ordinary_edge_inside Hloop u events v e Hreachable Hstep Htaken Hentry Hback
          Hinside') as [Hinside _].
        apply (Hbound Hinside inv t); [|exact Htrip].
        eapply environment_step; eassumption.
  - intros u events v prefix Hreachable Hprefix Hbound Hstep Hstay Hinside' inv t Hinv Htrip.
    pose proof (stays_point (link_ok (loop_ssa Hloop)) u events v Hreachable Hstep Hstay)
      as Hpoints.
    change (point v = point u) in Hpoints.
    assert (Hinside : body (point u) = true) by (rewrite <- Hpoints; exact Hinside').
    apply (Hbound Hinside inv t); [|exact Htrip]; eapply environment_step; eassumption.
  - intros _ inv t Hinv Htrip; apply N.le_0_l.
Qed.

End PlanSemantics.

Local Lemma last_phi_member (bs : list (scev_binding V)) x :
  last_phi bs = Some x -> In x (List.map sb_phi bs).
Proof.
  induction bs as [|b rest IH]; [discriminate|].
  cbn [last_phi List.map].
  destruct (last_phi rest) as [last|] eqn:Hlast.
  - intro Hequal; injection Hequal as <-; right; apply IH; reflexivity.
  - intro Hequal; injection Hequal as <-; left; reflexivity.
Qed.

Local Lemma recognised_equations (Hloop : loop_laws) target c :
  run lv so inventory target = Some c ->
  exists p lookup, scev_plan_check lv so inventory p = true /\
    lookup target = Some c /\ In target (List.map sb_phi (sp_bindings p)) /\
    compilation_equations p lookup.
Proof.
  unfold run, run_c; autorewrite with galois_cost.
  destruct (Cost.value (run_execution_c lv so inventory target)) as [out|] eqn:Hrun;
    [|discriminate].
  cbn [option_map]; intro Hequal; injection Hequal as <-.
  destruct (recognise_plan_checked lv so inventory target out Hrun)
    as [Htarget [Hcheck Hcompiled]].
  pose proof (proj1 (scev_plan_check_correct lv (loop_node_encoding Hloop)
    (loop_value_encoding Hloop) so inventory (plan out)) Hcheck) as Hsource.
  destruct Hsource as [_ [Hdistinct [Hlast _]]].
  destruct (compiled_plan_equations EV (loop_value_encoding Hloop) (plan out) (recurrence out)
    Hdistinct (checked_future_independent lv (loop_node_encoding Hloop)
      (loop_value_encoding Hloop) so inventory (plan out) Hcheck) Hcompiled)
    as [env [Hlookup Hequations]].
  exists (plan out), (fun x => Map.get EV x env); split; [exact Hcheck|].
  rewrite Htarget in Hlookup; split; [exact Hlookup|]; split.
  - apply last_phi_member; rewrite <- Htarget; exact Hlast.
  - intros b c Hb Hc; destruct (Hequations b Hb) as [own [Hown Htranslation]].
    assert (Hequal : own = c) by congruence; subst own; exact Htranslation.
Qed.

(** Recognition equals the wrapped recurrence at every actual header arrival of every loop stay. *)
Theorem scev_sound (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval) target c :
  run lv so inventory target = Some c ->
  forall s0 es s d, initial m s0 -> run_edges m lk s0 es s ->
  point s = lheader lv -> val s target = Some d ->
  to_Z so d = wrap (width_of so) (Chrec.eval (inv_env sl so s) c (stay_arrivals lv es)).
Proof.
  intro Hrun; destruct (recognised_equations Hloop target c Hrun)
    as [p [lookup [Hcheck [Hlookup [Hmember Hequations]]]]].
  intros s0 es s d Hinitial Hhistory Hheader Hvalue.
  pose proof (scev_plan_run_sound p lookup Hloop Hops Hequations s0 es s
    Hcheck Hinitial Hhistory) as Hstate.
  assert (Hinside : body (point s) = true) by
    (rewrite Hheader; exact (header_inside Hloop)).
  exact (Hstate Hinside (inv_env sl so s) (fun _ _ => eq_refl)
    target c d Hmember Hlookup Hvalue).
Qed.

(** Exact normalized trip counts bound every actual stay, retaining the separate no-wrap premise. *)
Theorem loop_trip_sound (Hloop : loop_laws) (Hops : scev_ops_laws so op_eval) tst c t :
  ltest lv = Some tst -> run lv so inventory (t_lhs tst) = Some c ->
  forall s0 es s, initial m s0 -> run_edges m lk s0 es s -> point s = lheader lv ->
  Failure.trip_count (fun x => view_z (width_of so) (t_sign tst) (inv_env sl so s x))
    (width_of so) (t_sign tst) (t_cmp tst) (signed_chrec (width_of so) (t_sign tst) c)
    (signed_iexpr (width_of so) (t_sign tst) (t_bound tst)) = Some t ->
  Failure.nowrap_check (width_of so) (t_sign tst)
    (fun x => view_z (width_of so) (t_sign tst) (inv_env sl so s x))
    (signed_chrec (width_of so) (t_sign tst) c)
    (signed_iexpr (width_of so) (t_sign tst) (t_bound tst)) t = true ->
  (N.of_nat (stay_arrivals lv es) <= t)%N.
Proof.
  intros Htest Hrun.
  destruct (recognised_equations Hloop (t_lhs tst) c Hrun)
    as [p [lookup [Hcheck [Hlookup [Hmember Hequations]]]]].
  intros s0 es s Hinitial Hhistory Hheader Htrip Hnowrap.
  eapply (scev_plan_trip_bound p lookup Hloop Hops Hequations tst c Hcheck Htest
    Hmember Hlookup s0 es s Hinitial Hhistory).
  - rewrite Hheader; exact (header_inside Hloop).
  - intros x Houtside; reflexivity.
  - exact Htrip.
Qed.

End Semantics.

End LoopSound.
