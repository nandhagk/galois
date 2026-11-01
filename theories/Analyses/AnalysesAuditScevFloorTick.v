(** * Fixed strict floor-tick model

    This file fixes a source-shaped event vocabulary for one floor tick.
    For example, an already-completed tick records its projection and branch.
    Builds on: AnalysesAuditScevCost, AnalysesAuditScevModCountPlain and CollectionsAuditCost. *)

From Stdlib Require Import List NArith ZArith Bool Lia.
From Galois.Analyses Require Import AnalysesAuditScevCost AnalysesAuditScevModCountPlain.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.
Local Open Scope N_scope.

(** * Source-level floor-tick events *)

(** Events retain the source site, the actual operands and the result state. *)
Inductive floor_strict_event : Type :=
  | FloorProjection (site : nat) (value : N)
  | FloorBranch (site : nat) (value : bool)
  | FloorPred (a : N)
  | FloorSucc (a : N)
  | FloorAdd (a b : N)
  | FloorMul (a b : N)
  | FloorDiv (a b : N)
  | FloorMod (a b : N)
  | FloorCompare (a b : N)
  | FloorConstruct (out : audit_floor_state).

(** Encode a Boolean projection in its source event. *)
Definition floor_bool (b : bool) : N := if b then 1 else 0.

(** List the fixed source operations before the final branch of an active tick. *)
Definition floor_active_prefix (st : audit_floor_state) : list floor_strict_event :=
  let n := audit_floor_n st in
  let m := audit_floor_m st in
  let a := audit_floor_a st in
  let b := audit_floor_b st in
  let acc := audit_floor_acc st in
  let ar := a mod m in
  let br := b mod m in
  let pred := N.pred n in
  let prod := n * pred in
  let triangle := prod / 2 in
  let aq := a / m in
  let first := triangle * aq in
  let acc1 := acc + first in
  let bq := b / m in
  let second := n * bq in
  let scaled := ar * n in
  let y := scaled + br in
  [FloorProjection 0 (floor_bool (audit_floor_done st)); FloorBranch 0 false;
   FloorProjection 1 n; FloorProjection 2 m; FloorProjection 3 a; FloorProjection 4 b;
   FloorMod a m; FloorMod b m; FloorProjection 5 acc; FloorPred n;
   FloorMul n pred; FloorDiv prod 2; FloorDiv a m; FloorMul triangle aq;
   FloorAdd acc first; FloorDiv b m; FloorMul n bq; FloorAdd acc1 second;
   FloorMul ar n; FloorAdd scaled br; FloorCompare y m; FloorBranch 1 (y <? m)].

(** Describe the actual output of a finished active tick. *)
Definition floor_finish_output (st : audit_floor_state) : audit_floor_state :=
  let n := audit_floor_n st in
  let m := audit_floor_m st in
  let a := audit_floor_a st in
  let b := audit_floor_b st in
  let acc := audit_floor_acc st + (n * N.pred n / 2) * (a / m) + n * (b / m) in
  AuditFloorState n m (a mod m) (b mod m) acc true (N.succ (audit_floor_updates st)).

(** Describe the actual output of a continuing active tick. *)
Definition floor_continue_output (st : audit_floor_state) : audit_floor_state :=
  let n := audit_floor_n st in
  let m := audit_floor_m st in
  let a := audit_floor_a st in
  let b := audit_floor_b st in
  let ar := a mod m in
  let br := b mod m in
  let acc := audit_floor_acc st + (n * N.pred n / 2) * (a / m) + n * (b / m) in
  let y := ar * n + br in
  AuditFloorState (y / m) ar m (y mod m) acc false (N.succ (audit_floor_updates st)).

(** The source relation has exactly the done, finished and continuing cases. *)
Inductive floor_strict_run :
    audit_floor_state -> audit_floor_state -> list floor_strict_event -> Prop :=
  | FloorRunDone : forall st,
      audit_floor_done st = true ->
      floor_strict_run st st [FloorProjection 0 1; FloorBranch 0 true]
  | FloorRunFinish : forall st,
      audit_floor_done st = false ->
      let y := audit_floor_a st mod audit_floor_m st * audit_floor_n st +
        audit_floor_b st mod audit_floor_m st in
      (y <? audit_floor_m st) = true ->
      floor_strict_run st (floor_finish_output st)
        (floor_active_prefix st ++
          [FloorProjection 6 (audit_floor_updates st); FloorSucc (audit_floor_updates st);
           FloorConstruct (floor_finish_output st)])
  | FloorRunContinue : forall st,
      audit_floor_done st = false ->
      let y := audit_floor_a st mod audit_floor_m st * audit_floor_n st +
        audit_floor_b st mod audit_floor_m st in
      (y <? audit_floor_m st) = false ->
      floor_strict_run st (floor_continue_output st)
        (floor_active_prefix st ++
          [FloorDiv y (audit_floor_m st); FloorMod y (audit_floor_m st);
           FloorProjection 6 (audit_floor_updates st); FloorSucc (audit_floor_updates st);
           FloorConstruct (floor_continue_output st)]).

(** * Prospective implementation and laws *)

(** The fixed literal observer follows exactly the source relation's selected branch. *)
Definition floor_tick_counted (st : audit_floor_state)
    : audit_floor_state * list floor_strict_event :=
  if audit_floor_done st then (st, [FloorProjection 0 1; FloorBranch 0 true]) else
  let y := (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st)%N in
  if (y <? audit_floor_m st)%N then
    (floor_finish_output st, floor_active_prefix st ++
      [FloorProjection 6 (audit_floor_updates st); FloorSucc (audit_floor_updates st);
       FloorConstruct (floor_finish_output st)])
  else
    (floor_continue_output st, floor_active_prefix st ++
      [FloorDiv y (audit_floor_m st); FloorMod y (audit_floor_m st);
       FloorProjection 6 (audit_floor_updates st); FloorSucc (audit_floor_updates st);
       FloorConstruct (floor_continue_output st)]).

(** The counted output and trace belong to the fixed source-shaped branch. *)
Definition floor_tick_correspondence_type : Prop := forall st,
  let '(out, events) := floor_tick_counted st in
  floor_strict_run st out events /\ out = audit_floor_step st.

(** Every source tick admits an exact result and trace. *)
Definition floor_tick_total_type : Prop := forall st,
  exists out events, floor_strict_run st out events /\ out = audit_floor_step st.

(** The fixed direct-operation trace has a nonzero finite bound. *)
Definition floor_tick_count_type : Prop := forall st,
  let '(_, events) := floor_tick_counted st in
  (2 <= length events <= 27)%nat.

(** * Shared-vocabulary source frames *)

(** Map a literal floor event to its fixed common source-frame site. *)
Definition floor_shared_event (e : floor_strict_event) : audit_event unit :=
  match e with
  | FloorProjection site value => AuditCase (100 + site)%nat [value]
  | FloorBranch site value => AuditCase site [floor_bool value]
  | FloorPred a => AuditArithmetic 0 [a]
  | FloorSucc a => AuditArithmetic 1 [a]
  | FloorAdd a b => AuditArithmetic 2 [a; b]
  | FloorMul a b => AuditArithmetic 3 [a; b]
  | FloorDiv a b => AuditArithmetic 4 [a; b]
  | FloorMod a b => AuditArithmetic 5 [a; b]
  | FloorCompare a b => AuditArithmetic 6 [a; b]
  | FloorConstruct out =>
    AuditConstruct 0 [audit_floor_n out; audit_floor_m out; audit_floor_a out;
      audit_floor_b out; audit_floor_acc out; floor_bool (audit_floor_done out);
      audit_floor_updates out]
  end.

(** A shared trace represents the very same fixed floor-source branch. *)
Definition floor_shared_run (st out : audit_floor_state) (events : audit_trace unit) : Prop :=
  exists frames, floor_strict_run st out frames /\ events = List.map floor_shared_event frames.

(** Sum the fixed source-frame weights without a caller-selected valuation. *)
Definition floor_source_weight (events : audit_trace unit) : nat :=
  fold_right (fun event total => (floor_source_frame_weight event + total)%nat) 0%nat events.

(** Input size includes every natural field, including the update counter. *)
Definition floor_input_size (st : audit_floor_state) : nat :=
  (1 + audit_z_bits (Z.of_N (audit_floor_n st)) + audit_z_bits (Z.of_N (audit_floor_m st)) +
   audit_z_bits (Z.of_N (audit_floor_a st)) + audit_z_bits (Z.of_N (audit_floor_b st)) +
   audit_z_bits (Z.of_N (audit_floor_acc st)) +
   audit_z_bits (Z.of_N (audit_floor_updates st)))%nat.

(** Compute one tick while retaining the very operands used by that execution. *)
Definition audit_floor_tick_counted (st : audit_floor_state)
    : audit_floor_state * audit_trace unit :=
  let done := audit_floor_done st in
  if done then (st, [AuditCase 100 [1]; AuditCase 0 [1]]) else
  let n := audit_floor_n st in
  let m := audit_floor_m st in
  let a := audit_floor_a st in
  let b := audit_floor_b st in
  let ar := a mod m in
  let br := b mod m in
  let acc0 := audit_floor_acc st in
  let pred := N.pred n in
  let prod := n * pred in
  let triangle := prod / 2 in
  let aq := a / m in
  let first := triangle * aq in
  let acc1 := acc0 + first in
  let bq := b / m in
  let second := n * bq in
  let acc := acc1 + second in
  let scaled := ar * n in
  let y := scaled + br in
  let finished := y <? m in
  let prefix :=
    [AuditCase 100 [0]; AuditCase 0 [0]; AuditCase 101 [n]; AuditCase 102 [m];
     AuditCase 103 [a]; AuditCase 104 [b]; AuditArithmetic 5 [a; m];
     AuditArithmetic 5 [b; m]; AuditCase 105 [acc0]; AuditArithmetic 0 [n];
     AuditArithmetic 3 [n; pred]; AuditArithmetic 4 [prod; 2]; AuditArithmetic 4 [a; m];
     AuditArithmetic 3 [triangle; aq]; AuditArithmetic 2 [acc0; first];
     AuditArithmetic 4 [b; m]; AuditArithmetic 3 [n; bq]; AuditArithmetic 2 [acc1; second];
     AuditArithmetic 3 [ar; n]; AuditArithmetic 2 [scaled; br]; AuditArithmetic 6 [y; m];
     AuditCase 1 [floor_bool finished]] in
  if finished then
    let old_updates := audit_floor_updates st in
    let updates := N.succ old_updates in
    let out := AuditFloorState n m ar br acc true updates in
    (out, prefix ++ [AuditCase 106 [old_updates]; AuditArithmetic 1 [old_updates];
      AuditConstruct 0 [n; m; ar; br; acc; 1; updates]])
  else
    let quotient := y / m in
    let remainder := y mod m in
    let old_updates := audit_floor_updates st in
    let updates := N.succ old_updates in
    let out := AuditFloorState quotient ar m remainder acc false updates in
    (out, prefix ++ [AuditArithmetic 4 [y; m]; AuditArithmetic 5 [y; m];
      AuditCase 106 [old_updates]; AuditArithmetic 1 [old_updates];
      AuditConstruct 0 [quotient; ar; m; remainder; acc; 0; updates]]).

(** Count list cells in the actual recorded frame payloads. *)
Definition floor_payload_cells (events : audit_trace unit) : nat :=
  fold_right (fun event total =>
    match event with
    | AuditCase _ operands | AuditConstruct _ operands | AuditArithmetic _ operands =>
      (length operands + total)%nat
    | _ => total
    end) 0%nat events.

(** Charge trace frame constructors, list cells, append visits and the returned pair. *)
Definition floor_instrumentation_work (st : audit_floor_state) : nat :=
  let '(_, events) := audit_floor_tick_counted st in
  let copied := if audit_floor_done st then 0%nat else 22%nat in
  let inspections := if audit_floor_done st then 0%nat else 24%nat in
  (1 + audit_work events + audit_work events + copied + floor_payload_cells events +
    inspections)%nat.

Section FutureSharedTick.

  (** The counted output and events are those of one fixed source branch. *)
  Definition audit_floor_tick_source_correct_type : Prop := forall st,
    let '(out, events) := audit_floor_tick_counted st in
    floor_shared_run st out events /\ out = audit_floor_step st.

  (** Every actual tick has one source-shaped result and trace. *)
  Definition audit_floor_tick_source_total_type : Prop := forall st,
    exists out events, floor_shared_run st out events /\ out = audit_floor_step st.

  (** Direct source frames include the done and branch even after completion. *)
  Definition audit_floor_tick_source_count_type : Prop := forall st,
    let '(_, events) := audit_floor_tick_counted st in
    (2 <= audit_work events <= 27)%nat.

  (** The branch-specific frame count includes the completed terminal check. *)
  Definition audit_floor_tick_source_counts_exact_type : Prop := forall st,
    let '(_, events) := audit_floor_tick_counted st in
    if audit_floor_done st then audit_work events = 2%nat else
    let y := (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
      audit_floor_b st mod audit_floor_m st)%N in
    audit_work events = if (y <? audit_floor_m st)%N then 25%nat else 27%nat.

  (** Event and trace construction have a fixed finite abstract bound. *)
  Definition audit_floor_tick_instrumentation_bound_type : Prop := forall st,
    (floor_instrumentation_work st <= 200)%nat.

  (** Instrumentation work follows the exact done, finished and continuing cases. *)
  Definition audit_floor_tick_instrumentation_exact_type : Prop := forall st,
    if audit_floor_done st then floor_instrumentation_work st = 7%nat else
    let y := (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
      audit_floor_b st mod audit_floor_m st)%N in
    floor_instrumentation_work st = if (y <? audit_floor_m st)%N then 141%nat else 149%nat.

  (** Direct primitive weights are bounded by the actual input field sizes. *)
  Definition audit_floor_tick_source_weight_type : Prop := forall st,
    let '(_, events) := audit_floor_tick_counted st in
    let size := floor_input_size st in
    (floor_source_weight events <= 27 * (1 + (20 * size) * (20 * size)))%nat.
End FutureSharedTick.

(** * Correspondence and counts *)

(** The literal trace follows the source branch and returns the original tick output. *)
Theorem floor_tick_correspondence : forall st,
  let '(out, events) := floor_tick_counted st in
  floor_strict_run st out events /\ out = audit_floor_step st.
Proof.
  intro st.
  unfold floor_tick_counted, audit_floor_step.
  destruct (audit_floor_done st) eqn:Hdone.
  - split; [constructor; exact Hdone | reflexivity].
  - destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
      audit_floor_b st mod audit_floor_m st <? audit_floor_m st) eqn:Hfinish.
    + split; [apply FloorRunFinish; assumption | reflexivity].
    + split; [apply FloorRunContinue; assumption | reflexivity].
Qed.

(** Every input has a literal source execution with the tick's result. *)
Theorem floor_tick_total : forall st,
  exists out events, floor_strict_run st out events /\ out = audit_floor_step st.
Proof.
  intro st.
  pose proof (floor_tick_correspondence st) as Hrun.
  destruct (floor_tick_counted st) as [out events].
  exists out, events.
  exact Hrun.
Qed.

(** A literal tick emits between two and twenty-seven frames. *)
Theorem floor_tick_count : forall st,
  let '(_, events) := floor_tick_counted st in
  (2 <= length events <= 27)%nat.
Proof.
  intro st.
  unfold floor_tick_counted.
  destruct (audit_floor_done st); [cbn; lia |].
  destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st <? audit_floor_m st);
    unfold floor_active_prefix; cbn; lia.
Qed.

(** Shared frames are the pointwise image of the literal execution. *)
Lemma floor_tick_shared_agrees : forall st,
  audit_floor_tick_counted st =
  let '(out, events) := floor_tick_counted st in
  (out, List.map floor_shared_event events).
Proof.
  intro st.
  unfold audit_floor_tick_counted, floor_tick_counted.
  destruct (audit_floor_done st) eqn:Hdone; [reflexivity |].
  destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st <? audit_floor_m st) eqn:Hfinish;
    unfold floor_active_prefix, floor_finish_output, floor_continue_output;
    cbn [floor_shared_event floor_bool]; rewrite Hdone, Hfinish; reflexivity.
Qed.

(** Shared frames retain the literal source branch and the tick result. *)
Theorem audit_floor_tick_source_correct : forall st,
  let '(out, events) := audit_floor_tick_counted st in
  floor_shared_run st out events /\ out = audit_floor_step st.
Proof.
  intro st.
  rewrite floor_tick_shared_agrees.
  pose proof (floor_tick_correspondence st) as Hrun.
  destruct (floor_tick_counted st) as [out events].
  cbn in *.
  destruct Hrun as [Hrun Hout].
  split; [exists events; split; [exact Hrun | reflexivity] | exact Hout].
Qed.

(** Every input has a shared-frame execution with the tick's result. *)
Theorem audit_floor_tick_source_total : forall st,
  exists out events, floor_shared_run st out events /\ out = audit_floor_step st.
Proof.
  intro st.
  pose proof (audit_floor_tick_source_correct st) as Hrun.
  destruct (audit_floor_tick_counted st) as [out events].
  exists out, events.
  exact Hrun.
Qed.

(** The shared trace count distinguishes the three tick branches. *)
Theorem audit_floor_tick_source_counts_exact : forall st,
  let '(_, events) := audit_floor_tick_counted st in
  if audit_floor_done st then audit_work events = 2%nat else
  let y := (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st)%N in
  audit_work events = if (y <? audit_floor_m st)%N then 25%nat else 27%nat.
Proof.
  intro st.
  unfold audit_floor_tick_counted, audit_work.
  destruct (audit_floor_done st); [reflexivity |].
  destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st <? audit_floor_m st); reflexivity.
Qed.

(** The shared trace has a nonzero, fixed upper bound. *)
Theorem audit_floor_tick_source_count : forall st,
  let '(_, events) := audit_floor_tick_counted st in
  (2 <= audit_work events <= 27)%nat.
Proof.
  intro st.
  pose proof (audit_floor_tick_source_counts_exact st) as Hcount.
  destruct (audit_floor_tick_counted st) as [out events].
  destruct (audit_floor_done st); [cbn in Hcount; rewrite Hcount; lia |].
  destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st <? audit_floor_m st);
    cbn in Hcount; rewrite Hcount; destruct (audit_floor_a st mod audit_floor_m st *
      audit_floor_n st + audit_floor_b st mod audit_floor_m st <? audit_floor_m st); lia.
Qed.

(** The instrumentation charge is exact for each branch of this execution. *)
Theorem audit_floor_tick_instrumentation_exact : forall st,
  if audit_floor_done st then floor_instrumentation_work st = 7%nat else
  let y := (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st)%N in
  floor_instrumentation_work st = if (y <? audit_floor_m st)%N then 141%nat else 149%nat.
Proof.
  intro st.
  unfold floor_instrumentation_work, audit_floor_tick_counted, audit_work, floor_payload_cells.
  destruct (audit_floor_done st); [reflexivity |].
  destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st <? audit_floor_m st); reflexivity.
Qed.

(** Each branch's instrumentation charge is at most two hundred units. *)
Theorem audit_floor_tick_instrumentation_bound : forall st,
  (floor_instrumentation_work st <= 200)%nat.
Proof.
  intro st.
  pose proof (audit_floor_tick_instrumentation_exact st) as Hexact.
  destruct (audit_floor_done st); [rewrite Hexact; lia |].
  destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
    audit_floor_b st mod audit_floor_m st <? audit_floor_m st);
    rewrite Hexact; destruct (audit_floor_a st mod audit_floor_m st * audit_floor_n st +
      audit_floor_b st mod audit_floor_m st <? audit_floor_m st); lia.
Qed.

(** The bit charge is monotone on binary naturals, including zero. *)
Lemma floor_bits_mono : forall a b : N, (a <= b)%N ->
  (audit_z_bits (Z.of_N a) <= audit_z_bits (Z.of_N b))%nat.
Proof.
  intros a b Hle.
  unfold audit_z_bits.
  rewrite !Z.abs_eq by apply N2Z.is_nonneg.
  apply le_n_S, Z2Nat.inj_le; try apply Z.log2_nonneg.
  apply Z.log2_le_mono, N2Z.inj_le.
  exact Hle.
Qed.

(** Addition increases bit charge by at most the sum of operand charges. *)
Lemma floor_bits_add : forall a b : N,
  (audit_z_bits (Z.of_N (a + b)) <=
   audit_z_bits (Z.of_N a) + audit_z_bits (Z.of_N b))%nat.
Proof.
  intros a b.
  unfold audit_z_bits.
  rewrite N2Z.inj_add, !Z.abs_eq by (pose proof (N2Z.is_nonneg a);
    pose proof (N2Z.is_nonneg b); lia).
  assert (Hlog : (Z.log2 (Z.of_N a + Z.of_N b) <=
    Z.log2 (Z.of_N a) + Z.log2 (Z.of_N b) + 1)%Z).
  { destruct (N.eq_dec a 1) as [-> | Ha].
    - replace (Z.of_N 1 + Z.of_N b)%Z with (Z.succ (Z.of_N b)) by lia.
      pose proof (Z.log2_succ_le (Z.of_N b)); cbn; lia.
    - destruct (N.eq_dec b 1) as [-> | Hb].
      + replace (Z.of_N a + Z.of_N 1)%Z with (Z.succ (Z.of_N a)) by lia.
        pose proof (Z.log2_succ_le (Z.of_N a)); cbn; lia.
      + pose proof (Z.log2_add_le (Z.of_N a) (Z.of_N b)) as H.
        assert (Ha_one : Z.of_N a <> 1%Z) by (intro E; apply Ha; apply N2Z.inj; exact E).
        assert (Hb_one : Z.of_N b <> 1%Z) by (intro E; apply Hb; apply N2Z.inj; exact E).
        specialize (H Ha_one Hb_one); lia. }
  assert (Hnat : (Z.to_nat (Z.log2 (Z.of_N a + Z.of_N b)) <=
    Z.to_nat (Z.log2 (Z.of_N a) + Z.log2 (Z.of_N b) + 1))%nat).
  { apply Z2Nat.inj_le; try apply Z.log2_nonneg;
      pose proof (Z.log2_nonneg (Z.of_N a));
      pose proof (Z.log2_nonneg (Z.of_N b)); lia. }
  clear Hlog; rename Hnat into Hlog.
  pose proof (Z.log2_nonneg (Z.of_N a)) as Ha.
  pose proof (Z.log2_nonneg (Z.of_N b)) as Hb.
  rewrite !Z2Nat.inj_add in Hlog by (try apply Z.log2_nonneg; lia).
  cbn in Hlog.
  lia.
Qed.

(** Multiplication increases bit charge by at most the sum of operand charges. *)
Lemma floor_bits_mul : forall a b : N,
  (audit_z_bits (Z.of_N (a * b)) <=
   audit_z_bits (Z.of_N a) + audit_z_bits (Z.of_N b))%nat.
Proof.
  intros a b.
  unfold audit_z_bits.
  rewrite N2Z.inj_mul, !Z.abs_eq by (pose proof (N2Z.is_nonneg a);
    pose proof (N2Z.is_nonneg b); nia).
  pose proof (Z.log2_mul_above (Z.of_N a) (Z.of_N b)
    (N2Z.is_nonneg a) (N2Z.is_nonneg b)) as Hlog.
  assert (Hnat : (Z.to_nat (Z.log2 (Z.of_N a * Z.of_N b)) <=
    Z.to_nat (Z.log2 (Z.of_N a) + Z.log2 (Z.of_N b) + 1))%nat).
  { apply Z2Nat.inj_le; try apply Z.log2_nonneg;
      pose proof (Z.log2_nonneg (Z.of_N a));
      pose proof (Z.log2_nonneg (Z.of_N b)); lia. }
  clear Hlog; rename Hnat into Hlog.
  pose proof (Z.log2_nonneg (Z.of_N a)) as Ha.
  pose proof (Z.log2_nonneg (Z.of_N b)) as Hb.
  rewrite !Z2Nat.inj_add in Hlog by (try apply Z.log2_nonneg; lia).
  cbn in Hlog.
  lia.
Qed.

(** Division never increases the numerator's bit charge, including a zero divisor. *)
Lemma floor_bits_div : forall a b : N,
  (audit_z_bits (Z.of_N (a / b)) <= audit_z_bits (Z.of_N a))%nat.
Proof.
  intros a b.
  apply floor_bits_mono.
  destruct b as [| b].
  - rewrite N.div_0_r; lia.
  - apply N.Div0.div_le_upper_bound.
    nia.
Qed.

(** Remainder never increases the numerator's bit charge, including a zero divisor. *)
Lemma floor_bits_mod : forall a b : N,
  (audit_z_bits (Z.of_N (a mod b)) <= audit_z_bits (Z.of_N a))%nat.
Proof.
  intros a b.
  apply floor_bits_mono, N.Div0.mod_le.
Qed.

(** Predecessor never increases the input's bit charge. *)
Lemma floor_bits_pred : forall a : N,
  (audit_z_bits (Z.of_N (N.pred a)) <= audit_z_bits (Z.of_N a))%nat.
Proof.
  intro a.
  apply floor_bits_mono.
  destruct a; cbn; lia.
Qed.

(** A uniformly bounded frame trace has weight at most its length times the bound. *)
Lemma floor_weight_trace_bound : forall events bound,
  Forall (fun e => (floor_source_frame_weight e <= bound)%nat) events ->
  (floor_source_weight events <= length events * bound)%nat.
Proof.
  intros events bound Hframes.
  induction Hframes as [| event events Hframe Hrest IH].
  - reflexivity.
  - unfold floor_source_weight in *.
    cbn [fold_right length].
    lia.
Qed.

(** A binary charge fits the quadratic allowance when both operands fit the size. *)
Lemma floor_binary_weight_bound : forall size, (1 <= size)%nat -> forall x y,
  (audit_z_bits x <= 10 * size)%nat -> (audit_z_bits y <= 10 * size)%nat ->
  (audit_binary_weight x y <= 1 + (20 * size) * (20 * size))%nat.
Proof.
  intros size Hsize x y Hx Hy.
  unfold audit_binary_weight.
  nia.
Qed.

(** A multiplication charge fits the same allowance for bounded operands. *)
Lemma floor_multiply_weight_bound : forall size, (1 <= size)%nat -> forall x y,
  (audit_z_bits x <= 10 * size)%nat -> (audit_z_bits y <= 10 * size)%nat ->
  (audit_multiply_weight x y <= 1 + (20 * size) * (20 * size))%nat.
Proof.
  intros size Hsize x y Hx Hy.
  unfold audit_multiply_weight.
  nia.
Qed.

(** A division charge fits the same allowance for bounded operands. *)
Lemma floor_divide_weight_bound : forall size, (1 <= size)%nat -> forall x y,
  (audit_z_bits x <= 10 * size)%nat -> (audit_z_bits y <= 10 * size)%nat ->
  (audit_divide_weight x y <= 1 + (20 * size) * (20 * size))%nat.
Proof.
  intros size Hsize x y Hx Hy.
  unfold audit_divide_weight.
  nia.
Qed.

(** The sum of actual frame weights is bounded by the tick input size. *)
Theorem audit_floor_tick_source_weight : forall st,
  let '(_, events) := audit_floor_tick_counted st in
  let size := floor_input_size st in
  (floor_source_weight events <= 27 * (1 + (20 * size) * (20 * size)))%nat.
Proof.
  intros [n m a b acc done updates].
  pose proof (floor_bits_pred n) as Hpred.
  pose proof (floor_bits_mod a m) as Har.
  pose proof (floor_bits_mod b m) as Hbr.
  pose proof (floor_bits_mul n (N.pred n)) as Hprod.
  pose proof (floor_bits_div (n * N.pred n) 2) as Htriangle.
  pose proof (floor_bits_div a m) as Haq.
  pose proof (floor_bits_div b m) as Hbq.
  pose proof (floor_bits_mul (n * N.pred n / 2) (a / m)) as Hfirst.
  pose proof (floor_bits_add acc ((n * N.pred n / 2) * (a / m))) as Hacc1.
  pose proof (floor_bits_mul n (b / m)) as Hsecond.
  pose proof (floor_bits_mul (a mod m) n) as Hscaled.
  pose proof (floor_bits_add ((a mod m) * n) (b mod m)) as Hy.
  set (size := (1 + audit_z_bits (Z.of_N n) + audit_z_bits (Z.of_N m) +
    audit_z_bits (Z.of_N a) + audit_z_bits (Z.of_N b) + audit_z_bits (Z.of_N acc) +
    audit_z_bits (Z.of_N updates))%nat).
  assert (Hsize : (1 <= size)%nat) by (unfold size; lia).
  (* Every intermediate used by an arithmetic frame has at most ten input sizes. *)
  assert (Hbounds :
    (audit_z_bits (Z.of_N n) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N m) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N a) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N b) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N acc) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (N.pred n)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (a mod m)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (b mod m)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (n * N.pred n)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (n * N.pred n / 2)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (a / m)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (b / m)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N ((n * N.pred n / 2) * (a / m))) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (acc + (n * N.pred n / 2) * (a / m))) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N (n * (b / m))) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N ((a mod m) * n)) <= 10 * size)%nat /\
    (audit_z_bits (Z.of_N ((a mod m) * n + b mod m)) <= 10 * size)%nat).
  { unfold size; repeat split; lia. }
  destruct Hbounds as (Hn & Hm & Ha & Hb & Hacc & Hp & Hra & Hrb & Hpr & Htr &
    Hqa & Hqb & Hf & Ha1 & Hs & Hsc & Hyy).
  clear Hpred Har Hbr Hprod Htriangle Haq Hbq Hfirst Hacc1 Hsecond Hscaled Hy.
  unfold audit_floor_tick_counted, floor_input_size.
  cbn [audit_floor_n audit_floor_m audit_floor_a audit_floor_b audit_floor_acc
    audit_floor_done audit_floor_updates].
  fold size.
  assert (Hup : (audit_z_bits (Z.of_N updates) <= 10 * size)%nat) by
    (unfold size; lia).
  clearbody size.
  (* Price each primitive independently before summing the finite trace. *)
  pose proof (floor_binary_weight_bound size Hsize) as Hbinary.
  pose proof (floor_multiply_weight_bound size Hsize) as Hmul.
  pose proof (floor_divide_weight_bound size Hsize) as Hdiv.
  destruct done.
  - cbn [floor_source_weight fold_right floor_source_frame_weight].
    unfold floor_source_weight; cbn [fold_right floor_source_frame_weight];
      clear Hn Hm Ha Hb Hacc Hp Hra Hrb Hpr Htr Hqa Hqb Hf Ha1 Hs Hsc Hyy
        Hbinary Hmul Hdiv; nia.
  - assert (Hframes : Forall
      (fun e => (floor_source_frame_weight e <= 1 + (20 * size) * (20 * size))%nat)
      (snd (audit_floor_tick_counted (AuditFloorState n m a b acc false updates)))).
    { unfold audit_floor_tick_counted; cbn.
      destruct (a mod m * n + b mod m <? m) eqn:Hfinish;
        repeat (constructor; [unfold floor_source_frame_weight; cbn [Nat.eqb orb];
          first [apply Hbinary; first [assumption | unfold audit_z_bits; cbn; lia] |
            apply Hmul; first [assumption | unfold audit_z_bits; cbn; lia] |
            apply Hdiv; first [assumption | unfold audit_z_bits; cbn; lia] |
            clear Hn Hm Ha Hb Hacc Hp Hra Hrb Hpr Htr Hqa Hqb Hf Ha1 Hs Hsc Hyy
              Hbinary Hmul Hdiv Hup; nia] |]); constructor. }
    pose proof (floor_weight_trace_bound _ _ Hframes) as Hweight.
    unfold audit_floor_tick_counted in Hweight; cbn in Hweight.
    destruct (a mod m * n + b mod m <? m) eqn:Hfinish;
      cbv beta iota zeta delta [snd length] in Hweight;
      eapply Nat.le_trans; try exact Hweight; apply Nat.mul_le_mono_r; lia.
Qed.
