(** * Contextual cache semantic declaration pilot

    This pilot re-elaborates the preserved epoch and context cache propositions.
    For example, changing the context takes the original rebuild branch.
    Builds on: Galois.Fixpoint. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointQuery FixpointWorklist.

Record solver_snapshot (X C A Epoch : Type) : Type := SolverSnapshot {
  epoch : Epoch;
  system : System.t X C A;
  static : System.static system;
  lat : lattice A;
  schedule : scheduler X;
  mode : strategy
}.

Arguments epoch {X C A Epoch}.

Arguments system {X C A Epoch}.

Arguments static {X C A Epoch}.

Arguments lat {X C A Epoch}.

Arguments schedule {X C A Epoch}.

Arguments mode {X C A Epoch}.

(** The snapshots agree on constraints, query behavior, static dependencies, lattice operations,
    schedule and strategy mode. *)
Definition snapshot_equiv {X C A Epoch} (a b : solver_snapshot X C A Epoch) : Prop :=
  System.constraints (system a) = System.constraints (system b) /\
  (forall c, System.target (system a) c = System.target (system b) c) /\
  (forall c s, Query.run (System.rhs (system a) c) s =
    Query.run (System.rhs (system b) c) s) /\
  (forall c, System.deps (static a) c = System.deps (static b) c /\
    System.side_targets (static a) c = System.side_targets (static b) c) /\
  bot (lat a) = bot (lat b) /\
  (forall x y, leb (lat a) x y = leb (lat b) x y /\
    join (lat a) x y = join (lat b) x y /\
    widen (lat a) x y = widen (lat b) x y) /\
  (forall x, priority (schedule a) x = priority (schedule b) x /\
    widening_point (schedule a) x = widening_point (schedule b) x) /\
  mode a = mode b.

(** Valid snapshots with the same epoch agree on the system, lattice and scheduler observations. *)
Record epoch_laws {X C A Epoch} (valid : solver_snapshot X C A Epoch -> Prop) : Prop := {
  epoch_sound : forall a b, valid a -> valid b -> epoch a = epoch b -> snapshot_equiv a b
}.

Definition run_indexed {X C A Epoch} (EX : encoding X) (EC : encoding C)
    (snap : solver_snapshot X C A Epoch) (ix : sys_index X C) (fuel : positive) :=
  run_worklist EX EC (lat snap) (schedule snap) (mode snap) (system snap)
    (Declared (static snap) ix) fuel.

Record solver_cache (X C A Epoch : Type) : Type := SolverCache {
  cached_snapshot : solver_snapshot X C A Epoch;
  cached_index : sys_index X C;
  cached_fuel : positive;
  cached_result : option (Map.t X A)
}.

Arguments SolverCache {X C A Epoch}.

Arguments cached_snapshot {X C A Epoch}.

Arguments cached_index {X C A Epoch}.

Arguments cached_fuel {X C A Epoch}.

Arguments cached_result {X C A Epoch}.

(** The cached index is built from its snapshot and its result is the indexed run at the cached
    fuel. *)
Definition cache_valid {X C A Epoch} (EX : encoding X) (EC : encoding C)
    (c : solver_cache X C A Epoch) : Prop :=
  cached_index c = index_system EX (system (cached_snapshot c)) (static (cached_snapshot c)) /\
  cached_result c = run_indexed EX EC (cached_snapshot c) (cached_index c) (cached_fuel c).

Definition cache_init {X C A Epoch} (EX : encoding X) (EC : encoding C)
    (snap : solver_snapshot X C A Epoch) (fuel : positive) : solver_cache X C A Epoch :=
  let ix := index_system EX (system snap) (static snap) in
  SolverCache snap ix fuel (run_indexed EX EC snap ix fuel).

Definition cache_query {X C A Epoch} (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (snap : solver_snapshot X C A Epoch) (fuel : positive)
    (c : solver_cache X C A Epoch) : solver_cache X C A Epoch :=
  if Pos.eqb (encode EE (epoch (cached_snapshot c))) (encode EE (epoch snap)) then
    if Pos.eqb (cached_fuel c) fuel then
      SolverCache snap (cached_index c) fuel (cached_result c)
    else SolverCache snap (cached_index c) fuel (run_indexed EX EC snap (cached_index c) fuel)
  else cache_init EX EC snap fuel.

(** With epoch laws, valid new and old snapshots and a valid old cache, querying returns a valid
    cache whose cached result agrees with the freshly indexed run. *)

Definition cache_query_correct : Prop :=
  forall X C A Epoch (EX : encoding X) (EC : encoding C) (EE : encoding Epoch)
    (valid : solver_snapshot X C A Epoch -> Prop), epoch_laws valid ->
    forall snap fuel c, valid snap -> valid (cached_snapshot c) -> cache_valid EX EC c ->
      let result := cache_query EX EC EE snap fuel c in
      cache_valid EX EC result /\
      cached_result result = run_indexed EX EC snap (index_system EX (system snap) (static snap))
        fuel.

Record contextual_snapshot (X C A Epoch Context : Type) : Type := ContextualSnapshot {
  context_snapshot : solver_snapshot X C A Epoch;
  context_token : Context
}.

Arguments ContextualSnapshot {X C A Epoch Context}.

Arguments context_snapshot {X C A Epoch Context}.

Arguments context_token {X C A Epoch Context}.

(** Allowed snapshots with the same epoch and context token agree on solver observations. *)
Record contextual_laws {X C A Epoch Context}
    (allowed : contextual_snapshot X C A Epoch Context -> Prop) : Prop := {
  context_identity : forall a b, allowed a -> allowed b ->
    epoch (context_snapshot a) = epoch (context_snapshot b) ->
    context_token a = context_token b -> snapshot_equiv (context_snapshot a) (context_snapshot b)
}.

Record contextual_cache (X C A Epoch Context : Type) : Type := ContextualCache {
  context_cached_token : Context;
  context_cached_solver : solver_cache X C A Epoch
}.

Arguments ContextualCache {X C A Epoch Context}.

Arguments context_cached_token {X C A Epoch Context}.

Arguments context_cached_solver {X C A Epoch Context}.

Definition contextual_init {X C A Epoch Context} (EX : encoding X) (EC : encoding C)
    (snap : contextual_snapshot X C A Epoch Context) (fuel : positive) :
    contextual_cache X C A Epoch Context :=
  ContextualCache (context_token snap) (cache_init EX EC (context_snapshot snap) fuel).

Definition contextual_query {X C A Epoch Context} (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context) (snap : contextual_snapshot X C A Epoch Context)
    (fuel : positive) (c : contextual_cache X C A Epoch Context) :
    contextual_cache X C A Epoch Context :=
  let old := context_cached_solver c in
  if Pos.eqb (encode EE (epoch (cached_snapshot old))) (encode EE (epoch (context_snapshot snap)))
    then
    if Pos.eqb (encode ET (context_cached_token c)) (encode ET (context_token snap)) then
      if Pos.eqb (cached_fuel old) fuel then
        ContextualCache (context_token snap)
          (SolverCache (context_snapshot snap) (cached_index old) fuel (cached_result old))
      else ContextualCache (context_token snap)
        (SolverCache (context_snapshot snap) (cached_index old) fuel
          (run_indexed EX EC (context_snapshot snap) (cached_index old) fuel))
    else contextual_init EX EC snap fuel
  else contextual_init EX EC snap fuel.

(** With contextual laws, allowed new and old snapshots and a valid old solver cache, querying
    returns a valid solver cache whose result agrees with fresh initialization. *)

Definition contextual_query_correct : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (allowed : contextual_snapshot X C A Epoch Context -> Prop), contextual_laws allowed ->
    forall snap fuel c,
      allowed snap -> allowed (ContextualSnapshot (cached_snapshot (context_cached_solver c))
        (context_cached_token c)) -> cache_valid EX EC (context_cached_solver c) ->
      let result := contextual_query EX EC EE ET snap fuel c in
      cache_valid EX EC (context_cached_solver result) /\
      cached_result (context_cached_solver result) =
        cached_result (cache_init EX EC (context_snapshot snap) fuel).

(** Changed epoch or context forces the concrete initialization branch. *)

Definition contextual_miss_rebuild : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel c,
    epoch (cached_snapshot (context_cached_solver c)) <> epoch (context_snapshot snap) \/
      context_cached_token c <> context_token snap ->
    contextual_query EX EC EE ET snap fuel c = contextual_init EX EC snap fuel.

(** Initializing any contextual snapshot produces a solver cache with a valid index and result. *)
Definition cache_epoch_initial_valid_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (snap : contextual_snapshot X C A Epoch Context) fuel,
    cache_valid EX EC (context_cached_solver (contextual_init EX EC snap fuel)).

(** A changed epoch or context token makes the query rebuild the entire cache. *)
Definition cache_epoch_miss_rebuild_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel c,
    epoch (cached_snapshot (context_cached_solver c)) <> epoch (context_snapshot snap) \/
      context_cached_token c <> context_token snap ->
    contextual_query EX EC EE ET snap fuel c = contextual_init EX EC snap fuel.

(** Equal epoch, context token and fuel preserve the cached result on a query. *)
Definition cache_epoch_hit_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel c,
    epoch (cached_snapshot (context_cached_solver c)) = epoch (context_snapshot snap) ->
    context_cached_token c = context_token snap ->
    cached_fuel (context_cached_solver c) = fuel ->
    cached_result (context_cached_solver (contextual_query EX EC EE ET snap fuel c)) =
      cached_result (context_cached_solver c).

(** With matching epoch and context but changed fuel, the query reuses the index and reruns the
    solver. *)
Definition cache_epoch_refuel_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel c,
    epoch (cached_snapshot (context_cached_solver c)) = epoch (context_snapshot snap) ->
    context_cached_token c = context_token snap ->
    cached_fuel (context_cached_solver c) <> fuel ->
    let result := context_cached_solver (contextual_query EX EC EE ET snap fuel c) in
    cached_index result = cached_index (context_cached_solver c) /\
    cached_result result = run_indexed EX EC (context_snapshot snap)
      (cached_index (context_cached_solver c)) fuel.

(** With contextual laws, allowed new and old snapshots and a valid old solver cache, querying
    returns a valid solver cache whose result agrees with fresh initialization. *)
Definition cache_epoch_valid : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (allowed : contextual_snapshot X C A Epoch Context -> Prop), contextual_laws allowed ->
    forall snap fuel c,
      allowed snap -> allowed (ContextualSnapshot (cached_snapshot (context_cached_solver c))
        (context_cached_token c)) -> cache_valid EX EC (context_cached_solver c) ->
      let result := contextual_query EX EC EE ET snap fuel c in
      cache_valid EX EC (context_cached_solver result) /\
      cached_result (context_cached_solver result) =
        cached_result (cache_init EX EC (context_snapshot snap) fuel).
