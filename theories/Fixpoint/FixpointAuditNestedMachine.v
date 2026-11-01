(** * Counted explicit nested solver machine

    This candidate retains actual traversal frames, maps, dirty-set operations and query runs.
    It assumes a supplied concrete prepared plan; nested_prepare is a separate source phase.
    For example, a nested solver step records its actual traversal frame.
    Builds on: FixpointNested and the counted shared collections and query models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

Inductive fx_nested_event (X C A : Type) : Type :=
  | FxNestedQuery (events : audit_trace (fx_declared_call X C A))
  | FxNestedRhs (c : C) (out : Query.t X A)
  | FxNestedTarget (c : C) (out : X)
  | FxNestedLeb (lhs rhs : A) (out : bool)
  | FxNestedJoin (lhs rhs out : A)
  | FxNestedWiden (lhs rhs out : A)
  | FxNestedMapGet (x : X) (code : positive) (input : Map.t X (list X))
      (raw : option (list X)) (body : audit_trace (audit_trie_call (X * list X)))
  | FxNestedTargetsGet (x : X) (code : positive) (input : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxNestedValueSet (x : X) (value : A) (code : positive) (input output : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxNestedSetMem (x : X) (input : FinSet.t X) (out : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxNestedSetAdd (x : X) (input output : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxNestedSetRemove (x : X) (input output : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxNestedCase (site : nat).

Arguments FxNestedQuery {X C A} _.

Arguments FxNestedRhs {X C A} _ _.

Arguments FxNestedTarget {X C A} _ _.

Arguments FxNestedLeb {X C A} _ _ _.

Arguments FxNestedJoin {X C A} _ _ _.

Arguments FxNestedWiden {X C A} _ _ _.

Arguments FxNestedMapGet {X C A} _ _ _ _ _.

Arguments FxNestedTargetsGet {X C A} _ _ _ _ _.

Arguments FxNestedValueSet {X C A} _ _ _ _ _ _.

Arguments FxNestedSetMem {X C A} _ _ _ _.

Arguments FxNestedSetAdd {X C A} _ _ _ _.

Arguments FxNestedSetRemove {X C A} _ _ _ _.

Arguments FxNestedCase {X C A} _.

Section NestedMachine.
Context {X C A : Type} (EX : encoding X) (L : lattice A)
  (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A).

Fixpoint fx_nested_mark_heads (heads : list X) (dirty : FinSet.t X) :
    FinSet.t X * list (fx_nested_event X C A) :=
  match heads with
  | [] => (dirty, [FxNestedCase 0])
  | h :: tail =>
      let '(next, add_events) := audit_finset_add (fx_index_encoder EX) h dirty in
      let '(out, events) := fx_nested_mark_heads tail next in
      (out, FxNestedCase 0 :: FxNestedSetAdd h dirty next add_events :: events)
  end.

Definition fx_nested_mark (x : X) (state : NestedState.t X C A) (values : assignment X A) :
    NestedState.t X C A * list (fx_nested_event X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code (NestedPlan.members plan) in
  let heads :=
    match raw with
    | Some hs => hs
    | None => []
    end in
  let '(dirty, mark_events) := fx_nested_mark_heads heads (NestedState.dirty state) in
  (NestedState.Make values (NestedState.ready state) (NestedState.frames state) dirty true,
   FxNestedMapGet x code (NestedPlan.members plan) raw body :: FxNestedCase 1 :: mark_events).

Definition fx_nested_raise (x : X) (old value : A) : A * list (fx_nested_event X C A) :=
  match mode with
  | Joining => let out := join L old value in (out, [FxNestedCase 2; FxNestedJoin old value out])
  | Widening =>
      let '(head, mem_events) := audit_finset_mem (fx_index_encoder EX) x (NestedPlan.heads plan) in
      if head then
        let out := widen L old value in
        (out, [FxNestedCase 2; FxNestedSetMem x (NestedPlan.heads plan) head mem_events;
          FxNestedCase 3; FxNestedWiden old value out])
      else let out := join L old value in
        (out, [FxNestedCase 2; FxNestedSetMem x (NestedPlan.heads plan) head mem_events;
          FxNestedCase 3; FxNestedJoin old value out])
  end.

Definition fx_nested_update (update : X * A) (state : NestedState.t X C A) :
    NestedState.t X C A * list (fx_nested_event X C A) :=
  let '(x, value) := update in
  let '(old, read_events) := @fx_model_lookup X C A EX L (NestedState.current state) x in
  let unchanged := leb L value old in
  let prefix := [FxNestedQuery read_events; FxNestedLeb value old unchanged; FxNestedCase 4] in
  if unchanged then (state, prefix)
  else
    let '(raised, raise_events) := fx_nested_raise x old value in
    let code := encode EX x in
    let '(values, write_events) := audit_trie_set code (x, raised) (NestedState.current state) in
    let '(out, mark_events) := fx_nested_mark x state values in
    (out, prefix ++ raise_events ++ [FxNestedValueSet x raised code (NestedState.current state)
      values write_events] ++ mark_events).

Fixpoint fx_nested_updates (updates : list (X * A)) (state : NestedState.t X C A) :
    NestedState.t X C A * list (fx_nested_event X C A) :=
  match updates with
  | [] => (state, [FxNestedCase 5])
  | update :: rest =>
      let '(next, first) := fx_nested_update update state in
      let '(out, later) := fx_nested_updates rest next in
      (out, FxNestedCase 5 :: first ++ later)
  end.

Definition fx_nested_step (state : NestedState.t X C A) :
    option (NestedState.t X C A) * list (fx_nested_event X C A) :=
  let values := NestedState.current state in
  let dirty := NestedState.dirty state in
  let changed := NestedState.changed state in
  match NestedState.ready state with
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs values in
      let '(v, _, sides) := answer in
      let target := System.target S c in
      let next_state := NestedState.Make values rest (NestedState.frames state) dirty changed in
      let '(out, update_events) := fx_nested_updates ((target, v) :: sides) next_state in
      (Some out, [FxNestedCase 6; FxNestedRhs c rhs; FxNestedQuery query_events;
        FxNestedTarget c target] ++ update_events)
  | [] =>
      match NestedState.frames state with
      | [] => (None, [FxNestedCase 6; FxNestedCase 7])
      | frame :: frames =>
          match NestedFrame.remaining frame with
          | NestedVisit x rest =>
              let code := encode EX x in
              let '(raw, body) := audit_map_code_get code (NestedPlan.targets plan) in
              let targets :=
                match raw with
                | Some cs => cs
                | None => []
                end in
              (Some (NestedState.Make values targets
                (NestedFrame.Make rest (NestedFrame.restart frame) :: frames) dirty changed),
               [FxNestedCase 6; FxNestedCase 7; FxNestedCase 8;
                FxNestedTargetsGet x code (NestedPlan.targets plan) raw body; FxNestedCase 9])
          | NestedComponent h body rest =>
              let pass := NestedVisit h body in
              let '(next_dirty, remove_events) := audit_finset_remove (fx_index_encoder EX) h
  dirty in
              (Some (NestedState.Make values []
                (NestedFrame.Make pass (Some (h, pass)) ::
                  NestedFrame.Make rest (NestedFrame.restart frame) :: frames) next_dirty changed),
               [FxNestedCase 6; FxNestedCase 7; FxNestedCase 8;
                FxNestedSetRemove h dirty next_dirty remove_events])
          | NestedEnd =>
              match NestedFrame.restart frame with
              | Some (h, pass) =>
                  let '(present, mem_events) := audit_finset_mem (fx_index_encoder EX) h dirty in
                  let prefix := [FxNestedCase 6; FxNestedCase 7; FxNestedCase 8; FxNestedCase 10;
                    FxNestedSetMem h dirty present mem_events; FxNestedCase 11] in
                  if present then
                    let '(next_dirty, remove_events) := audit_finset_remove (fx_index_encoder
  EX) h dirty in
                    (Some (NestedState.Make values []
                      (NestedFrame.Make pass (Some (h, pass)) :: frames) next_dirty changed),
                     prefix ++ [FxNestedSetRemove h dirty next_dirty remove_events])
                  else (Some (NestedState.Make values [] frames dirty changed), prefix)
              | None =>
                  if changed then
                    (Some (NestedState.Make values [] [NestedFrame.Make (NestedPlan.root plan) None]
                      dirty false), [FxNestedCase 6; FxNestedCase 7; FxNestedCase 8;
                        FxNestedCase 10; FxNestedCase 12])
                  else (None, [FxNestedCase 6; FxNestedCase 7; FxNestedCase 8;
                    FxNestedCase 10; FxNestedCase 12])
              end
          end
      end
  end.

Definition fx_nested_tick (result : NestedState.t X C A + assignment X A) :
    (NestedState.t X C A + assignment X A) * list (fx_nested_event X C A) :=
  match result with
  | inr values => (inr values, [FxNestedCase 13])
  | inl state =>
      let '(next, events) := fx_nested_step state in
      match next with
      | None => (inr (NestedState.current state), FxNestedCase 13 :: events ++ [FxNestedCase 14])
      | Some out => (inl out, FxNestedCase 13 :: events ++ [FxNestedCase 14])
      end
  end.

Fixpoint fx_nested_loop (fuel : positive) (state : NestedState.t X C A) :
    (NestedState.t X C A + assignment X A) * list (fx_nested_event X C A) :=
  match fuel with
  | xH =>
      let '(out, events) := fx_nested_tick (inl state) in (out, FxNestedCase 15 :: events)
  | xO smaller =>
      let '(first, events) := fx_nested_loop smaller state in
      match first with
      | inr values => (inr values, FxNestedCase 15 :: events ++ [FxNestedCase 16])
      | inl next =>
          let '(out, later) := fx_nested_loop smaller next in
          (out, FxNestedCase 15 :: events ++ FxNestedCase 16 :: later)
      end
  | xI smaller =>
      let '(first, events) := fx_nested_loop smaller state in
      let '(second, later) :=
        match first with
        | inr values => (inr values, [FxNestedCase 16])
        | inl next => let '(out, body) := fx_nested_loop smaller next in
            (out, FxNestedCase 16 :: body)
        end in
      let '(out, last) := fx_nested_tick second in
      (out, FxNestedCase 15 :: events ++ later ++ last)
  end.

(** Erasing counted mark, raise, update, step and loop events recovers the corresponding original
    nested operations. *)
Definition fx_nested_machine_erasure_statement : Prop :=
  (forall x state values,
    fst (fx_nested_mark x state values) = nested_mark EX plan x state values) /\
  (forall x old value, fst (fx_nested_raise x old value) =
    update_value L (nested_scheduler EX plan) mode x old value) /\
  (forall update state, fst (fx_nested_update update state) = nested_update EX L plan mode
  update state) /\
  (forall updates state, fst (fx_nested_updates updates state) =
    nested_updates EX L plan mode updates state) /\
  (forall state, fst (fx_nested_step state) = nested_step EX L plan mode S state) /\
  (forall fuel state, fst (fx_nested_loop fuel state) =
    nested_loop (nested_step EX L plan mode S) fuel state).

End NestedMachine.

(** Positive source-block allowances include the exact nested collection/query bodies. *)

Definition fx_nested_event_work {X C A} (EC : encoding C) (event : fx_nested_event X C A) : nat :=
  match event with
  | FxNestedQuery body => fx_declared_model_work EC body
  | FxNestedMapGet _ code _ _ body
  | FxNestedTargetsGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FxNestedValueSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FxNestedSetMem _ _ _ body
  | FxNestedSetAdd _ _ _ body
  | FxNestedSetRemove _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | _ => 1
  end.

Definition fx_nested_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_nested_event X C A) : nat :=
  match event with
  | FxNestedQuery body => audit_work body + fx_declared_primitive_budget EC body
  | FxNestedMapGet _ code _ _ _
  | FxNestedTargetsGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FxNestedValueSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | FxNestedSetMem x _ _ _ => 12 + 5 * Pos.size_nat (encode EX x)
  | FxNestedSetAdd x _ _ _
  | FxNestedSetRemove x _ _ _ => 12 + 17 * Pos.size_nat (encode EX x)
  | _ => 1
  end.

Definition fx_nested_work {X C A} (EC : encoding C) (events : list (fx_nested_event X C A)) : nat :=
  fold_right (fun event n => fx_nested_event_work EC event + n) 0 events.

Definition fx_nested_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_nested_event X C A)) : nat :=
  fold_right (fun event n => fx_nested_event_budget EX EC event + n) 0 events.

(** The counted nested loop returns the original result and its selected work fits the trace
    budget. *)
Definition fx_nested_loop_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A) fuel state,
    let '(out, events) := fx_nested_loop EX L plan mode S fuel state in
    out = nested_loop (nested_step EX L plan mode S) fuel state /\
    fx_nested_work EC events <= fx_nested_budget EX EC events.

(** These recurrences use original inputs and actual source intermediate states; their
    mathematical evaluation is excluded from the cost of the solver run. *)

Fixpoint fx_nested_mark_input_budget {X} (EX : encoding X) (heads : list X) : nat :=
  match heads with
  | [] => 1
  | h :: rest => 1 + (12 + 17 * Pos.size_nat (encode EX h)) + fx_nested_mark_input_budget EX rest
  end.

Definition fx_nested_update_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (mode : strategy) (update : X * A) (state : NestedState.t X C A) :
  nat :=
  let '(x, value) := update in
  let old := lookup EX L (NestedState.current state) x in
  2 + fx_fullcheck_lookup_input_budget EX x +
  if leb L value old then 0
  else
    5 + (12 + 5 * Pos.size_nat (encode EX x)) +
    (2 + 17 * Pos.size_nat (encode EX x)) + (2 + 6 * Pos.size_nat (encode EX x)) +
    fx_nested_mark_input_budget EX (index_get EX (NestedPlan.members plan) x).

Fixpoint fx_nested_updates_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (mode : strategy) (updates : list (X * A))
    (state : NestedState.t X C A) : nat :=
  match updates with
  | [] => 1
  | update :: rest => 1 + fx_nested_update_input_budget EX L plan mode update state +
      fx_nested_updates_input_budget EX L plan mode rest (nested_update EX L plan mode update state)
  end.

Definition fx_nested_step_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A)
    (state : NestedState.t X C A) : nat :=
  match NestedState.ready state with
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L (NestedState.current state)) in
      let next := NestedState.Make (NestedState.current state) rest (NestedState.frames state)
        (NestedState.dirty state) (NestedState.changed state) in
      3 + fx_fullcheck_query_input_budget EX L (NestedState.current state) rhs +
        fx_nested_updates_input_budget EX L plan mode ((System.target S c, value) :: sides) next
  | [] =>
      match NestedState.frames state with
      | [] => 2
      | frame :: _ =>
          match NestedFrame.remaining frame with
          | NestedVisit x _ => 6 + 6 * Pos.size_nat (encode EX x)
          | NestedComponent h _ _ => 15 + 17 * Pos.size_nat (encode EX h)
          | NestedEnd =>
              match NestedFrame.restart frame with
              | None => 6
              | Some (h, _) => 30 + 22 * Pos.size_nat (encode EX h)
              end
          end
      end
  end.

Definition fx_nested_tick_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A)
    (state : NestedState.t X C A + assignment X A) : nat :=
  match state with
  | inr _ => 1
  | inl current => 2 + fx_nested_step_input_budget EX L plan mode S current
  end.

Fixpoint fx_nested_loop_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A)
    (fuel : positive) (state : NestedState.t X C A) : nat :=
  let step := nested_step EX L plan mode S in
  match fuel with
  | xH => 1 + fx_nested_tick_input_budget EX L plan mode S (inl state)
  | xO smaller =>
      2 + fx_nested_loop_input_budget EX L plan mode S smaller state +
      match nested_loop step smaller state with
      | inr _ => 0
      | inl next => fx_nested_loop_input_budget EX L plan mode S smaller next
      end
  | xI smaller =>
      let first := nested_loop step smaller state in
      let second :=
        match first with
        | inr values => inr values
        | inl next => nested_loop step
          smaller next
        end in
      2 + fx_nested_loop_input_budget EX L plan mode S smaller state +
      (
        match first with
        | inr _ => 0
        | inl next => fx_nested_loop_input_budget EX L plan mode S
          smaller next
        end) +
      fx_nested_tick_input_budget EX L plan mode S second
  end.

(** The counted nested loop returns the original result and its work fits an input-derived
    budget. *)
Definition fx_nested_loop_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (plan : NestedPlan.t X C) mode (S : System.t X C A) fuel state,
    let '(out, events) := fx_nested_loop EX L plan mode S fuel state in
    out = nested_loop (nested_step EX L plan mode S) fuel state /\
    fx_nested_work EC events <= fx_nested_loop_input_budget EX L plan mode S fuel state.
