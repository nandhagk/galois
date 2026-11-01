(** * FixpointAuditCache model

    Contextual cache with real index producer and actual epoch/context encoder bodies.
    Engine external callbacks are accounted for by the declared-worklist source adapter.
    For example, a changed context selects the cache rebuild branch.
    Builds on: FixpointAuditCacheSemantic, FixpointAuditIndex and FixpointAuditWorklist. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditPrimitive.
From Galois.Fixpoint Require Import FixpointAuditCacheSemantic FixpointAuditIndex
  FixpointAuditWorklist
  FixpointAuditWorklistCallbacks FixpointAuditWorklistBudget.
Import List.ListNotations.

Record cache_key_models (Epoch Context B : Type) := CacheKeyModels {
  cache_epoch_encoder : Epoch -> positive * list B;
  cache_context_encoder : Context -> positive * list B
}.

Arguments cache_epoch_encoder {Epoch Context B} _ _.

Arguments cache_context_encoder {Epoch Context B} _ _.

(** Both model encoders return the same keys as their corresponding epoch and context encodings. *)
Definition cache_key_models_erase {Epoch Context B} (EE : encoding Epoch) (ET : encoding Context)
    (keys : cache_key_models Epoch Context B) : Prop :=
  (forall e, fst (cache_epoch_encoder keys e) = encode EE e) /\
  (forall t, fst (cache_context_encoder keys t) = encode ET t).

Inductive cache_callback_event (X C A Epoch Context BI BK : Type) :=
  | CacheEpochBody (input : Epoch) (code : positive) (body : list BK)
  | CacheContextBody (input : Context) (code : positive) (body : list BK)
  | CacheCompareBody (left right : positive) (result : bool) (body : list audit_positive_eqb_event)
  | CacheIndexBody (events : list (fx_index_nested_event X C BI))
  | CacheEngineBody (index : sys_index X C) (events : audit_trace (fx_declared_call X C A))
  | CacheCase (site : nat).

Arguments CacheEpochBody {X C A Epoch Context BI BK} _ _ _.

Arguments CacheContextBody {X C A Epoch Context BI BK} _ _ _.

Arguments CacheCompareBody {X C A Epoch Context BI BK} _ _ _ _.

Arguments CacheIndexBody {X C A Epoch Context BI BK} _.

Arguments CacheEngineBody {X C A Epoch Context BI BK} _ _.

Arguments CacheCase {X C A Epoch Context BI BK} _.

Definition cache_init_callbacks {X C A Epoch Context BI BK} (EX : encoding X) (EC : encoding C)
    (cb : fx_index_external_model X C BI) (snap : contextual_snapshot X C A Epoch Context) fuel :
    contextual_cache X C A Epoch Context * list (cache_callback_event X C A Epoch Context BI BK) :=
  let inner := context_snapshot snap in
  let '(ix, index_events) := fx_index_nested_counted (system inner) cb in
  let '(out, engine_events) := run_worklist_declared_model EX EC (lat inner) (schedule inner)
    (mode inner) (system inner) ix fuel in
  (ContextualCache (context_token snap) (SolverCache inner ix fuel out),
   [CacheCase 0; CacheIndexBody index_events; CacheEngineBody ix engine_events]).

Definition cache_query_callbacks {X C A Epoch Context BI BK} (EX : encoding X) (EC : encoding C)
    (cb : fx_index_external_model X C BI) (keys : cache_key_models Epoch Context BK)
    (snap : contextual_snapshot X C A Epoch Context) fuel (c : contextual_cache X C A Epoch Context)
      :
    contextual_cache X C A Epoch Context * list (cache_callback_event X C A Epoch Context BI BK) :=
  let old := context_cached_solver c in
  let e1 := epoch (cached_snapshot old) in let e2 := epoch (context_snapshot snap) in
  let '(p1, be1) := cache_epoch_encoder keys e1 in let '(p2, be2) := cache_epoch_encoder keys e2 in
  let '(eq_epoch, ce) := audit_positive_eqb p1 p2 in
  let prefix := [CacheCase 1; CacheEpochBody e1 p1 be1; CacheEpochBody e2 p2 be2;
    CacheCompareBody p1 p2 eq_epoch ce] in
  if eq_epoch then
    let t1 := context_cached_token c in let t2 := context_token snap in
    let '(q1, bt1) := cache_context_encoder keys t1 in let '(q2, bt2) := cache_context_encoder keys
      t2 in
    let '(eq_context, ct) := audit_positive_eqb q1 q2 in
    let context_prefix := [CacheContextBody t1 q1 bt1; CacheContextBody t2 q2 bt2;
      CacheCompareBody q1 q2 eq_context ct] in
    if eq_context then
      let '(eq_fuel, cf) := audit_positive_eqb (cached_fuel old) fuel in
      if eq_fuel then
        (ContextualCache (context_token snap) (SolverCache (context_snapshot snap)
           (cached_index old) fuel (cached_result old)),
         prefix ++ context_prefix ++ [CacheCompareBody (cached_fuel old) fuel eq_fuel cf; CacheCase
           2])
      else
        let inner := context_snapshot snap in
        let '(out, body) := run_worklist_declared_model EX EC (lat inner) (schedule inner)
          (mode inner) (system inner) (cached_index old) fuel in
        (ContextualCache (context_token snap) (SolverCache inner (cached_index old) fuel out),
         prefix ++ context_prefix ++ [CacheCompareBody (cached_fuel old) fuel eq_fuel cf;
           CacheCase 3; CacheEngineBody (cached_index old) body])
    else let '(out, body) := cache_init_callbacks EX EC cb snap fuel in
      (out, prefix ++ context_prefix ++ CacheCase 4 :: body)
  else let '(out, body) := cache_init_callbacks EX EC cb snap fuel in
    (out, prefix ++ CacheCase 5 :: body).

(** If index and key callbacks erase correctly, initialization and queries return the uncounted
    caches. *)
Definition cache_callbacks_erasure_statement : Prop :=
  forall X C A Epoch Context BI BK (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context) (cb : fx_index_external_model X C BI)
    (keys : cache_key_models Epoch Context BK) (snap : contextual_snapshot X C A Epoch Context) fuel
      c,
    fx_index_external_erases EX (system (context_snapshot snap)) (static (context_snapshot snap)) cb
      ->
    cache_key_models_erase EE ET keys ->
    fst (@cache_init_callbacks X C A Epoch Context BI BK EX EC cb snap fuel) = contextual_init EX EC
      snap fuel /\
    fst (cache_query_callbacks EX EC cb keys snap fuel c) = contextual_query EX EC EE ET snap fuel
      c.

Record cache_key_source (Epoch Context B : Type) := CacheKeySource {
  cache_epoch_source : Epoch -> positive -> list B -> Prop;
  cache_context_source : Context -> positive -> list B -> Prop
}.

Arguments cache_epoch_source {Epoch Context B} _ _ _ _.

Arguments cache_context_source {Epoch Context B} _ _ _ _.

Record cache_key_budget (Epoch Context B : Type) := CacheKeyBudget {
  cache_key_weight : B -> nat;
  cache_epoch_bound : Epoch -> nat;
  cache_context_bound : Context -> nat
}.

Arguments cache_key_weight {Epoch Context B} _ _.

Arguments cache_epoch_bound {Epoch Context B} _ _.

Arguments cache_context_bound {Epoch Context B} _ _.

(** Each epoch and context encoding returns a key and body accepted by its source relation. *)
Definition cache_key_source_laws {Epoch Context B} (keys : cache_key_models Epoch Context B)
    (source : cache_key_source Epoch Context B) : Prop :=
  (forall e, let '(out, body) := cache_epoch_encoder keys e in cache_epoch_source source e out body)
    /\
  (forall t, let '(out, body) := cache_context_encoder keys t in cache_context_source source t out
    body).

(** Every accepted epoch or context encoding body fits its respective input-dependent bound. *)
Definition cache_key_source_bounded {Epoch Context B} (source : cache_key_source Epoch Context B)
    (budget : cache_key_budget Epoch Context B) : Prop :=
  (forall e out body, cache_epoch_source source e out body ->
    fx_one_body_work (cache_key_weight budget) body <= cache_epoch_bound budget e) /\
  (forall t out body, cache_context_source source t out body ->
    fx_one_body_work (cache_key_weight budget) body <= cache_context_bound budget t).

(** Key and index events require their source relations and empty engine-body groups, engine
    events require the declared trace relation, and comparison and case events require empty
    groups. *)
Definition cache_event_source {X C A Epoch Context BI BK BW}
    (index_source : fx_index_external_source X C BI) (key_source : cache_key_source Epoch Context
      BK)
    (source : fx_declared_callback_source X C A BW)
    (event : cache_callback_event X C A Epoch Context BI BK) (bodies : list (list (list BW))) : Prop
      :=
  match event with
  | CacheEpochBody input code body => bodies = [] /\ cache_epoch_source key_source input code body
  | CacheContextBody input code body => bodies = [] /\ cache_context_source key_source input code
    body
  | CacheIndexBody events => bodies = [] /\ fx_index_external_trace_adequacy index_source events
  | CacheEngineBody _ events => fx_declared_trace_source source events bodies
  | _ => bodies = []
  end.

(** The cache events and grouped callback bodies correspond in order, one group per event. *)
Definition cache_trace_source {X C A Epoch Context BI BK BW}
    (index_source : fx_index_external_source X C BI) (key_source : cache_key_source Epoch Context
      BK)
    (source : fx_declared_callback_source X C A BW)
    (events : list (cache_callback_event X C A Epoch Context BI BK))
    (bodies : list (list (list (list BW)))) : Prop :=
  Forall2 (cache_event_source index_source key_source source) events bodies.

Definition cache_callback_event_work {X C A Epoch Context BI BK}
    (EC : encoding C) (ib : fx_index_external_budget X C BI) (kb : cache_key_budget Epoch Context
      BK)
    (event : cache_callback_event X C A Epoch Context BI BK) : nat :=
  match event with
  | CacheEpochBody _ _ body
  | CacheContextBody _ _ body => 1 + fx_one_body_work (cache_key_weight
    kb) body
  | CacheCompareBody _ _ _ body => 1 + audit_positive_eqb_source_work body
  | CacheIndexBody events => fx_index_adapter_work ib events
  | CacheEngineBody _ events => fx_declared_model_work EC events
  | CacheCase _ => 1
  end.

Definition cache_callback_work {X C A Epoch Context BI BK} (EC : encoding C)
    (ib : fx_index_external_budget X C BI) (kb : cache_key_budget Epoch Context BK)
    (events : list (cache_callback_event X C A Epoch Context BI BK)) : nat :=
  fold_right (fun e n => cache_callback_event_work EC ib kb e + n) 0 events.

Definition cache_external_engine_work {BW} (weight : BW -> nat)
    (groups : list (list (list (list BW))) ) : nat :=
  fold_right (fun bodies n => fx_declared_body_work weight bodies + n) 0 groups.

Definition cache_callback_event_budget {X C A Epoch Context BI BK BW}
    (EX : encoding X) (EC : encoding C) (snap : contextual_snapshot X C A Epoch Context) fuel
    (ib : fx_index_external_budget X C BI) (kb : cache_key_budget Epoch Context BK)
    (wb : fx_declared_callback_budget X C A BW)
    (event : cache_callback_event X C A Epoch Context BI BK) : nat :=
  let inner := context_snapshot snap in
  match event with
  | CacheEpochBody e _ _ => 1 + cache_epoch_bound kb e
  | CacheContextBody t _ _ => 1 + cache_context_bound kb t
  | CacheCompareBody a b _ _ => 2 + 2 * Nat.min (Pos.size_nat a) (Pos.size_nat b)
  | CacheIndexBody _ => fx_index_nested_input_budget EX (system inner) (static inner) ib
  | CacheEngineBody ix events =>
      fx_declared_run_input_budget EX EC (lat inner) (schedule inner) (mode inner)
        (system inner) (static inner) ix fuel + fx_declared_external_trace_budget wb events
  | CacheCase _ => 1
  end.

Definition cache_callback_budget {X C A Epoch Context BI BK BW}
    (EX : encoding X) (EC : encoding C) (snap : contextual_snapshot X C A Epoch Context) fuel
    (ib : fx_index_external_budget X C BI) (kb : cache_key_budget Epoch Context BK)
    (wb : fx_declared_callback_budget X C A BW)
    (events : list (cache_callback_event X C A Epoch Context BI BK)) : nat :=
  fold_right (fun e n => cache_callback_event_budget EX EC snap fuel ib kb wb e + n) 0 events.

(** The modeled index encoder, target, side and dependency outputs and bodies satisfy their
    supplied source relations. *)
Definition cache_index_source_laws {X C BI} (cb : fx_index_external_model X C BI)
    (source : fx_index_external_source X C BI) : Prop :=
  (forall x, let '(out, body) := fxi_encode cb x in fxi_encode_source source x out body) /\
  (forall c, let '(out, body) := fxi_target cb c in fxi_target_source source c out body) /\
  (forall c, let '(out, body) := fxi_sides cb c in fxi_sides_source source c out body) /\
  (forall c, let '(out, body) := fxi_deps cb c in fxi_deps_source source c out body).
(** A reused index needs laws only on the same-key branch that actually refuels it. *)

Definition cache_refuel_index_laws {X C A Epoch Context} (EX : encoding X)
    (EE : encoding Epoch) (ET : encoding Context) (snap : contextual_snapshot X C A Epoch Context)
    (fuel : positive) (c : contextual_cache X C A Epoch Context) : Prop :=
  let old := context_cached_solver c in
  let inner := context_snapshot snap in
  if Pos.eqb (encode EE (epoch (cached_snapshot old))) (encode EE (epoch inner)) then
    if Pos.eqb (encode ET (context_cached_token c)) (encode ET (context_token snap)) then
      if Pos.eqb (cached_fuel old) fuel then True
      else sys_index_laws EX (system inner) (static inner) (cached_index old)
    else True
  else True.

(** With refuel index validity, index and key erasure, and index, key and declared source laws
    and bounds, the query has its original result, source receipts and a work bound. *)
Definition cache_query_callbacks_source_statement : Prop :=
  forall X C A Epoch Context BI BK BW (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context) (cb : fx_index_external_model X C BI)
    (ib : fx_index_external_budget X C BI) (index_source : fx_index_external_source X C BI)
    (keys : cache_key_models Epoch Context BK) (kb : cache_key_budget Epoch Context BK)
    (key_source : cache_key_source Epoch Context BK) (source : fx_declared_callback_source X C A BW)
    (wb : fx_declared_callback_budget X C A BW) (snap : contextual_snapshot X C A Epoch Context)
      fuel c,
    let inner := context_snapshot snap in
    cache_refuel_index_laws EX EE ET snap fuel c ->
    fx_index_external_erases EX (system inner) (static inner) cb -> fx_index_external_bounded cb ib
      ->
    cache_index_source_laws cb index_source -> cache_key_models_erase EE ET keys ->
    cache_key_source_laws keys key_source -> cache_key_source_bounded key_source kb ->
    fx_declared_source_laws EX EC (lat inner) (schedule inner) (system inner) source ->
    fx_declared_callback_bounded source wb ->
    let '(out, events) := cache_query_callbacks EX EC cb keys snap fuel c in
    exists groups, cache_trace_source index_source key_source source events groups /\
      out = contextual_query EX EC EE ET snap fuel c /\
      cache_callback_work EC ib kb events + cache_external_engine_work (fx_body_weight wb) groups <=
        cache_callback_budget EX EC snap fuel ib kb wb events.

(** With index erasure and bounds and index and engine source laws and bounds, initialization has
    its original result, source receipts and a work bound. *)
Definition cache_init_callbacks_source_statement : Prop :=
  forall X C A Epoch Context BI BK BW (EX : encoding X) (EC : encoding C)
    (cb : fx_index_external_model X C BI) (ib : fx_index_external_budget X C BI)
    (index_source : fx_index_external_source X C BI) (kb : cache_key_budget Epoch Context BK)
    (key_source : cache_key_source Epoch Context BK) (source : fx_declared_callback_source X C A BW)
    (wb : fx_declared_callback_budget X C A BW) (snap : contextual_snapshot X C A Epoch Context)
      fuel,
    let inner := context_snapshot snap in
    fx_index_external_erases EX (system inner) (static inner) cb -> fx_index_external_bounded cb ib
      ->
    cache_index_source_laws cb index_source ->
    fx_declared_source_laws EX EC (lat inner) (schedule inner) (system inner) source ->
    fx_declared_callback_bounded source wb ->
    let '(out, events) := @cache_init_callbacks X C A Epoch Context BI BK EX EC cb snap fuel in
    exists groups, cache_trace_source index_source key_source source events groups /\
      out = contextual_init EX EC snap fuel /\
      cache_callback_work EC ib kb events + cache_external_engine_work (fx_body_weight wb) groups <=
        cache_callback_budget EX EC snap fuel ib kb wb events.

(** Branch-sensitive mathematical input budget. The fixed 32 covers the finite cache
    branch's local source blocks and records. Actual nested callbacks are charged through
    their separate per-call source budgets. Evaluating this observer is not claimed work. *)

Definition cache_compare_input_budget (a b : positive) : nat :=
  2 + 2 * Nat.min (Pos.size_nat a) (Pos.size_nat b).

Definition cache_rebuild_input_budget {X C A Epoch Context BI}
    (EX : encoding X) (EC : encoding C) (snap : contextual_snapshot X C A Epoch Context) fuel
    (ib : fx_index_external_budget X C BI) : nat :=
  let inner := context_snapshot snap in
  let ix := index_system EX (system inner) (static inner) in
  fx_index_nested_input_budget EX (system inner) (static inner) ib +
    fx_declared_run_input_budget EX EC (lat inner) (schedule inner) (mode inner)
      (system inner) (static inner) ix fuel.

Definition cache_query_input_budget {X C A Epoch Context BI BK}
    (EX : encoding X) (EC : encoding C) (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel (c : contextual_cache X C A Epoch Context)
    (ib : fx_index_external_budget X C BI) (kb : cache_key_budget Epoch Context BK) : nat :=
  let old := context_cached_solver c in
  let inner := context_snapshot snap in
  let e1 := epoch (cached_snapshot old) in let e2 := epoch inner in
  let p1 := encode EE e1 in let p2 := encode EE e2 in
  32 + cache_epoch_bound kb e1 + cache_epoch_bound kb e2 + cache_compare_input_budget p1 p2 +
  if Pos.eqb p1 p2 then
    let t1 := context_cached_token c in let t2 := context_token snap in
    let q1 := encode ET t1 in let q2 := encode ET t2 in
    cache_context_bound kb t1 + cache_context_bound kb t2 + cache_compare_input_budget q1 q2 +
    if Pos.eqb q1 q2 then
      cache_compare_input_budget (cached_fuel old) fuel +
      if Pos.eqb (cached_fuel old) fuel then 0 else
        fx_declared_run_input_budget EX EC (lat inner) (schedule inner) (mode inner)
          (system inner) (static inner) (cached_index old) fuel
    else cache_rebuild_input_budget EX EC snap fuel ib
  else cache_rebuild_input_budget EX EC snap fuel ib.

Definition cache_engine_external_budget {X C A Epoch Context BI BK BW}
    (wb : fx_declared_callback_budget X C A BW)
    (events : list (cache_callback_event X C A Epoch Context BI BK)) : nat :=
  fold_right (fun event n =>
    match event with
    | CacheEngineBody _ calls => fx_declared_external_trace_budget wb calls + n
    | _ => n
    end) 0 events.

(** With refuel index validity, index and key erasure, and index, key and declared source laws
    and bounds, the query has its original result and source receipts within the branch-sensitive
    input and engine work bound. *)
Definition cache_query_input_bound_statement : Prop :=
  forall X C A Epoch Context BI BK BW (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context) (cb : fx_index_external_model X C BI)
    (ib : fx_index_external_budget X C BI) (index_source : fx_index_external_source X C BI)
    (keys : cache_key_models Epoch Context BK) (kb : cache_key_budget Epoch Context BK)
    (key_source : cache_key_source Epoch Context BK) (source : fx_declared_callback_source X C A BW)
    (wb : fx_declared_callback_budget X C A BW) (snap : contextual_snapshot X C A Epoch Context)
      fuel c,
    let inner := context_snapshot snap in
    cache_refuel_index_laws EX EE ET snap fuel c ->
    fx_index_external_erases EX (system inner) (static inner) cb -> fx_index_external_bounded cb ib
      ->
    cache_index_source_laws cb index_source -> cache_key_models_erase EE ET keys ->
    cache_key_source_laws keys key_source -> cache_key_source_bounded key_source kb ->
    fx_declared_source_laws EX EC (lat inner) (schedule inner) (system inner) source ->
    fx_declared_callback_bounded source wb ->
    let '(out, events) := cache_query_callbacks EX EC cb keys snap fuel c in
    exists groups, cache_trace_source index_source key_source source events groups /\
      out = contextual_query EX EC EE ET snap fuel c /\
      cache_callback_work EC ib kb events + cache_external_engine_work (fx_body_weight wb) groups <=
        cache_query_input_budget EX EC EE ET snap fuel c ib kb + cache_engine_external_budget wb
          events.
