(** * Counted local solve and checked wrapper

    This proposal composes the actual closure, queue, engine and checker on the same states.
    For example, a duplicate root is tested in the closure and again by the checked wrapper.
    Builds on: FixpointAuditLocalClosure, FixpointAuditWorklist and FixpointAuditLocalPartial. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointLocal.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditFinSet
  CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditLocalPartial FixpointAuditLocalClosure.
Import List.ListNotations.

Definition fx_local_input_bits {X} (EX : encoding X) (xs : list X) : nat :=
  fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 xs.

Inductive fx_local_full_event (X C A : Type) : Type :=
  | FxLocalClosureTrace (events : list (fx_local_event X C))
  | FxLocalEngineTrace (events : audit_trace (fx_declared_call X C A))
  | FxLocalPartialTrace (events : list (fx_partial_event X C A))
  | FxLocalSelectedElements (input : FinSet.t C) (output : list C)
      (body : list (audit_set_elements_event C))
  | FxLocalRegionElements (input : FinSet.t X) (output : list X)
      (body : list (audit_set_elements_event X))
  | FxLocalRegionBuild (input : list X) (output : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxLocalRootMem (root : X) (region : FinSet.t X) (result : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxLocalFullCase (site : nat).

Arguments FxLocalClosureTrace {X C A} _.

Arguments FxLocalEngineTrace {X C A} _.

Arguments FxLocalPartialTrace {X C A} _.

Arguments FxLocalSelectedElements {X C A} _ _ _.

Arguments FxLocalRegionElements {X C A} _ _ _.

Arguments FxLocalRegionBuild {X C A} _ _ _.

Arguments FxLocalRootMem {X C A} _ _ _ _.

Arguments FxLocalFullCase {X C A} _.

Section LocalWhole.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Fixpoint fx_local_roots_init (roots : list X) : list (X + C) * list (fx_local_full_event X C A) :=
  match roots with
  | [] => ([], [FxLocalFullCase 0])
  | x :: xs => let '(rest, events) := fx_local_roots_init xs in
      (inl x :: rest, FxLocalFullCase 0 :: events ++ [FxLocalFullCase 1])
  end.

Definition local_solve_counted (roots : list X) (fuel : positive) :
    option (local_result X A) * list (fx_local_full_event X C A) :=
  let '(pending, initial_events) := fx_local_roots_init roots in
  let initial := LocalClosure.State FinSet.empty FinSet.empty pending in
  let '(closure, closure_events) := fx_local_walk EX EC S SS ix fuel initial in
  let prefix := initial_events ++ [FxLocalClosureTrace closure_events; FxLocalFullCase 2] in
  match closure with
  | LocalClosure.Pending _ => (None, prefix)
  | LocalClosure.Done region selected =>
      let '(constraints, elements_events) := audit_finset_elements selected in
      let '(queue, queue_events) := fx_model_enqueue EC sch S constraints PQueue.empty in
      let initial_engine := Engine.State Map.empty queue Map.empty in
      let '(result, engine_events) := fx_model_loop EX EC L sch mode S ix fuel initial_engine in
      let events := prefix ++ [FxLocalSelectedElements selected constraints elements_events;
        FxLocalEngineTrace queue_events; FxLocalEngineTrace engine_events; FxLocalFullCase 3] in
      match result with
      | FixpointWorklist.Done values => (Some (LocalResult region values), events)
      | FixpointWorklist.Pending _ => (None, events)
      end
  end.

Fixpoint fx_local_roots_checked (region : FinSet.t X) (roots : list X) :
    bool * list (fx_local_full_event X C A) :=
  match roots with
  | [] => (true, [FxLocalFullCase 4])
  | x :: xs =>
      let '(head, body) := audit_finset_mem (fx_index_encoder EX) x region in
      let '(tail, events) := fx_local_roots_checked region xs in
      (andb head tail, FxLocalFullCase 4 :: FxLocalRootMem x region head body :: events ++
        [FxLocalFullCase 5])
  end.

Definition local_checked_counted (roots : list X) (fuel : positive) :
    option (local_result X A) * list (fx_local_full_event X C A) :=
  let '(candidate, solve_events) := local_solve_counted roots fuel in
  match candidate with
  | None => (None, solve_events ++ [FxLocalFullCase 6])
  | Some result =>
      let '(items, elements_events) := audit_finset_elements (explored result) in
      let '(region, build_events) := audit_finset_of_list (fx_index_encoder EX) items in
      let '(partial, partial_events) := check_partial_counted EX L S ix region (values result) in
      let '(covered, root_events) := fx_local_roots_checked region roots in
      let events := solve_events ++ [FxLocalFullCase 6;
        FxLocalRegionElements (explored result) items elements_events;
        FxLocalRegionBuild items region build_events; FxLocalPartialTrace partial_events] ++
        root_events ++ [FxLocalFullCase 7] in
      (if andb partial covered then Some (LocalResult region (values result)) else None, events)
  end.

(** Discarding the event list from a counted local solve yields the original solve result. *)
Definition fx_local_solve_erasure_statement : Prop :=
  forall roots fuel, fst (local_solve_counted roots fuel) =
    local_solve EX EC L sch mode S SS ix roots fuel.

(** Discarding the event list from a counted checked local solve yields the original result. *)
Definition fx_local_checked_erasure_statement : Prop :=
  forall roots fuel, fst (local_checked_counted roots fuel) =
    local_checked EX EC L sch mode S SS ix roots fuel.

End LocalWhole.

(** Fixed selected primitive work is composed from the actual nested execution. *)

Definition fx_local_full_event_work {X C A} (EC : encoding C)
    (event : fx_local_full_event X C A) : nat :=
  match event with
  | FxLocalClosureTrace events => fx_local_work events
  | FxLocalEngineTrace events => fx_declared_model_work EC events
  | FxLocalPartialTrace events => fx_partial_work EC events
  | FxLocalSelectedElements _ _ body => 1 + audit_set_elements_work body
  | FxLocalRegionElements _ _ body => 1 + audit_set_elements_work body
  | FxLocalRegionBuild _ _ body
  | FxLocalRootMem _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxLocalFullCase _ => 1
  end.

Definition fx_local_full_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_local_full_event X C A) : nat :=
  match event with
  | FxLocalClosureTrace events => fx_local_budget EX EC events
  | FxLocalEngineTrace events => audit_work events + fx_declared_primitive_budget EC events
  | FxLocalPartialTrace events => fx_partial_budget EX EC events
  | FxLocalSelectedElements set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxLocalRegionElements set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxLocalRegionBuild items _ _ =>
      12 + 12 * length items + 17 * fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 items
  | FxLocalRootMem x _ _ _ => 12 + 17 * Pos.size_nat (encode EX x)
  | FxLocalFullCase _ => 1
  end.

Definition fx_local_full_work {X C A} (EC : encoding C)
    (events : list (fx_local_full_event X C A)) : nat :=
  fold_right (fun event n => fx_local_full_event_work EC event + n) 0 events.

Definition fx_local_full_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_local_full_event X C A)) : nat :=
  fold_right (fun event n => fx_local_full_event_budget EX EC event + n) 0 events.

(** A checked local solve returns the original result and its recorded work fits the trace
    budget. *)
Definition fx_local_checked_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) roots fuel,
    let '(result, events) := local_checked_counted EX EC L sch mode S SS ix roots fuel in
    result = local_checked EX EC L sch mode S SS ix roots fuel /\
    fx_local_full_work EC events <= fx_local_full_budget EX EC events.

Fixpoint fx_local_roots_input_budget {X} (EX : encoding X) (roots : list X) : nat :=
  match roots with
  | [] => 1
  | x :: rest => 2 + (12 + 5 * Pos.size_nat (encode EX x)) + fx_local_roots_input_budget EX rest
  end.

Definition fx_local_region_build_budget {X} (EX : encoding X) (items : list X) : nat :=
  12 + 12 * length items + 17 * fx_local_input_bits EX items.

Definition fx_local_solve_input_budget {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (roots : list X) (fuel : positive) : nat :=
  let initial := LocalClosure.State FinSet.empty FinSet.empty (map (@inl X C) roots) in
  let closure := LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel initial in
  (1 + 2 * length roots) + fx_local_walk_input_budget EX EC S SS ix fuel initial + 1 +
  match closure with
  | LocalClosure.Pending _ => 0
  | LocalClosure.Done _ selected =>
      let cs := FinSet.elements selected in
      let queue := enqueue EC sch S cs PQueue.empty in
      (7 + 19 * audit_trie_nodes selected + audit_trie_output_bits selected) +
      fx_declared_enqueue_input_budget EC sch S cs PQueue.empty +
      fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel (Engine.State Map.empty queue
        Map.empty) + 1
  end.

Definition fx_local_checked_input_budget {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (roots : list X) (fuel : positive) : nat :=
  fx_local_solve_input_budget EX EC L sch mode S SS ix roots fuel + 1 +
  match local_solve EX EC L sch mode S SS ix roots fuel with
  | None => 0
  | Some result =>
      let items := FinSet.elements (explored result) in
      let region := FinSet.of_list EX items in
      (7 + 19 * audit_trie_nodes (explored result) + audit_trie_output_bits (explored result)) +
      fx_local_region_build_budget EX items + fx_partial_input_budget EX L S ix region (values
        result) +
      fx_local_roots_input_budget EX roots + 1
  end.

(** A checked local solve returns the original result and its selected work fits the input
    budget. *)
Definition fx_local_checked_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix roots fuel,
    let '(result, events) := local_checked_counted EX EC L sch mode S SS ix roots fuel in
    result = local_checked EX EC L sch mode S SS ix roots fuel /\
    fx_local_full_work EC events <= fx_local_checked_input_budget EX EC L sch mode S SS ix roots
      fuel.
