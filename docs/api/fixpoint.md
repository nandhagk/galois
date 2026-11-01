# Galois.Fixpoint

## Nested WTO iteration (FIX-5)

`FixpointNested.v` supplies a selectable directly proved nested iterator for static systems. It
does not change `wto_scheduler`, which remains the static-priority queue scheduler of FIX-3.
The two strategies can produce different widened post-solutions. Construct the dependency graph
and `wto_total` once, using `unknowns`, `dependency_graph` and the graph preparation of FIX-3.
Each target has a prebuilt list of its constraints in `System.constraints` order; do not scan the
constraint list while iterating. The WTO token list is parsed once to a well-nested component
tree with its heads, vertex-to-containing-components index, and ordered target constraint lists.

An ordered pass visits each `WVertex` once. On `WOpen h`, it visits h, then each nested body item
in order, repeating the whole component until no unknown in that component changed during the
pass. Changes by side contributions count, even when their producing constraint targets another
component; mark every containing component dirty. A complete outer pass traverses all top-level
items and repeats until no unknown anywhere changes in that pass. Thus a side contribution to a
previously visited component is not lost. On visiting x, run each constraint with target x once,
in the prebuilt order, using `Query.run` once. Process its returned target value followed by all
side contributions in `Query.run` order. An update is skipped when its contribution is already
below the current value; otherwise use `widen` at a WTO head under `Widening`, and `join` at all
other points or under `Joining`. Track changes through the same `leb` test used by
`engine_step`. Constraints with no reads still run on every required visit. All target and side
outputs are included in the graph and the component membership index.

Each invocation uses binary fuel. One fuel unit performs one constraint evaluation, or one frame
transition if no constraint is ready; it returns `None` if fuel expires before a no-change outer
pass. The implementation uses explicit frames and a binary-recursive loop, not the Gallina call
stack proportional to iteration count. Empty systems finish successfully. An initial assignment
is everywhere bottom. A `None` result never certifies a solution. Definitions and theorems:

```coq
Definition nested_run {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (st : strategy) (S : System.t X C A) (SS : System.static S) (fuel : positive) :
  option (assignment X A).
Definition nested_solve_fuel {X C A} (EX : encoding X) (EC : encoding C)
  (L : lattice A) (HL : lattice_laws L) (T : top L) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (fuel : positive) :
  {s : X -> A | post_solution L S s}.
(* Return the assignment from nested_run when it finishes, otherwise the everywhere-top function. *)
Theorem nested_run_sound {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (fuel : positive) (m : assignment X A) :
  nested_run EX EC L st S SS fuel = Some m -> post_solution L S (lookup EX L m).
Theorem nested_run_eventually {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S) :
  terminates L SS (wto_scheduler EX S SS) st ->
  exists fuel m, nested_run EX EC L st S SS fuel = Some m.
```

Proof obligations include component nesting, dirty propagation for every side target, termination
of each pass, and a well-founded measure for the nested strategy. Prove that parsed heads are
exactly the widening points of `wto_scheduler`, and that a complete outer pass evaluates every
constraint, including those with side targets in earlier components. `nested_run_sound` follows
from the final no-change pass, independently of leastness. `nested_run_eventually` needs finite
height or the existing widening-rank and cycle-cut hypotheses; no leastness or schedule-independent
equality is claimed. The independent full checker remains available for external candidates.
Card: FIX-5.

## Observation-oriented SCC iteration (FIX-6)

`FixpointObserve.v` supplies a memory-conscious mode for static systems with no declared side
targets. It returns selected observations; the full FIX-5 engine remains available for every
static system including side effects. The fixed schedule first computes the SCCs of the declared
read-to-target dependency graph in topological order. Within each SCC it uses the nested WTO
iteration of FIX-5 on that component, initialized to bottom for its members and reading already
stabilized predecessor values as immutable inputs. Build the induced component graph, its WTO,
and the ordered target-constraint lists once. The induced WTO is computed deterministically from
the component and is not an additional field supplied by the caller. No value is evicted during
component stabilization.
A component is complete only when its nested iterator finishes; a singleton without a self-edge
is handled by the same rule. Side-free declarations guarantee that its constraints cannot update
another component. Unknowns with no target constraint retain bottom.

The plan stores the nonempty components in topological order, with each component represented by
its first member, and indexes eviction lists by that representative. Prepare the index from the
last component that declares a read of each value, counting the producer component itself. After
a component stabilizes, record every selected observation in it, then remove each value whose
last reader component is the just-completed component. Earlier external inputs remain available
through every read in the current component. No scan of all unknowns or constraints occurs in
the iteration. Observation keys must be among `unknowns`; duplicate keys are allowed. The result
map contains exactly the distinct observation keys, including bottom-valued observations.

The checker validates component coverage, membership, topological flow, the component WTOs,
side-free declarations, observation coverage, and every lifetime against the declared read
dependencies and the prepared system index. It rejects invalid plans and any declared side target.
A component's schedule, constraint order and widening choices are the same in the two executions
below. Both start with bottom values and a binary fuel budget. A fuel unit pays one nested frame
transition or one constraint evaluation; bookkeeping and component-boundary eviction do not
consume extra fuel. Both return `None` when the plan is invalid or fuel expires before all
components stabilize. On completion both return the observation map. The full-memory reference
keeps all stabilized values, while the memory-conscious execution performs the stated evictions.

```coq
Record observation_plan (X : Type) : Type := ObservationPlan {
  observation_components : list (list X);
  observation_expire : Map.t X (list X)
}.
Definition observation_prepare {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) : option (observation_plan X).
Definition observation_plan_check {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) : bool.
Definition observation_project {X A} (EX : encoding X) (L : lattice A) (roots : list X)
  (m : assignment X A) : assignment X A.
(* Fold Map.set over roots with the corresponding lookup EX L m value, starting from Map.empty. *)
Definition observation_full_reference {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) : option (assignment X A).
(* The fixed-schedule execution without eviction, returning its complete assignment on success. *)
Definition observation_reference {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) : option (assignment X A).
Definition observation_run {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) : option (assignment X A).
Theorem observation_prepare_checked {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_prepare EX S SS ix roots = Some p ->
  observation_plan_check EX S SS ix roots p = true.
Theorem observation_run_refines {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) :
  sys_index_laws EX S SS ix ->
  observation_run EX L st S SS ix roots p fuel =
    observation_reference EX L st S SS ix roots p fuel.
Theorem observation_reference_projection {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) :
  observation_reference EX L st S SS ix roots p fuel =
  option_map (observation_project EX L roots)
    (observation_full_reference EX L st S SS ix roots p fuel).
Theorem observation_full_reference_sound {X C A} (EX : encoding X) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (roots : list X) (p : observation_plan X) (fuel : positive)
  (m : assignment X A) :
  sys_index_laws EX S SS ix ->
  observation_full_reference EX L st S SS ix roots p fuel = Some m ->
  post_solution L S (lookup EX L m).
Theorem observation_plan_complete {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  sys_index_laws EX S SS ix ->
  (forall c, In c (System.constraints S) -> side_targets SS c = []) ->
  (forall x, In x roots -> In x (unknowns EX S SS)) ->
  exists p, observation_prepare EX S SS ix roots = Some p.
Theorem observation_run_eventually {X C A} (EX : encoding X) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_plan_check EX S SS ix roots p = true ->
  terminates L SS (wto_scheduler EX S SS) st ->
  exists fuel m, observation_run EX L st S SS ix roots p fuel = Some m.
```

Prove the reference and optimized executions have identical component-local traces and widening
histories. At each boundary they agree on all values read by a later component and on observations
already recorded. `sides_within` proves that empty declared side lists exclude actual contributions.
Prove that each derived local WTO's heads cut all cycles in its induced component, independently
of the global scheduler's head set, and use this in the eventual-completion argument. The full
reference's post-solution theorem establishes semantic utility; its projection and the refinement
theorem connect that guarantee to the returned observations.
The peak live assignment contains current-component values and earlier values with a later
declared reader; the observation map is additional retained output. No eviction within an SCC,
global memory-optimality claim, equality with a different schedule, or full-assignment result is
promised. Card: FIX-6.
Fixpoint gives every analysis one meaning: a constraint system. Each constraint has a target
unknown and a right-hand side that is a small query tree: return a value, ask another unknown, or
contribute to one. A result is a *post-solution* when every value returned and every value
contributed lies below the result. The package has one full checker, a checker that stores values
only at cut points and recomputes the rest in one pass, one worklist engine whose scheduler is a
parameter (a fuel-bounded run with a top fallback, and a total run whose termination is proved from
evidence), narrowing that is kept only when the checker accepts it, and a demand-driven local
solver whose output is validated by a checker. For example, over sets, the constraints
`a ⊒ {1}`, `b ⊒ a` and `a ⊒ b` have the least solution `a = b = {1}`; the engine returns it and
`check_post` accepts it, while `a = {1}, b = {}` is rejected.

Conventions of this document. Names are those of the anchors, as the rulings amend them.
- Query trees live in `Module Query`: `Query.t`, `Query.Ret`, `Query.Ask`, `Query.Side`,
  `Query.eval`, `Query.reads`, `Query.sides` and `Query.run`. Constraint systems live in
  `Module System`: `System.t X C A` with `System.constraints`, `System.target` and `System.rhs`, and
  `System.static S` with `System.deps`, `System.side_targets`, `System.reads_within` and
  `System.sides_within`. `Abbreviation deps := System.deps` and `Abbreviation side_targets :=
  System.side_targets` make the two summaries bare, as Views writes them. Graphs are `Graph.t V E`
  with `Graph.entries`, `Graph.nodes`, `Graph.out`, `Graph.source` and `Graph.target`, so no
  projection is ever shared between `System` and `Graph`.
- Sets are `FinSet.t K` and maps `Map.t K V` (Collections), written with the encoding first. A
  function that iterates `FinSet.elements` is specified only on well-formed sets, so a theorem
  about it carries `FinSet.wf`; an untrusted producer's set is normalised with
  `FinSet.of_list EX (FinSet.elements s)` before it is trusted.
- `post_solution`, `assignment`, `lookup`, `ask_all` and `side_all` are bare. `fun_leb` and
  `monotone_on_assignments` come from Order.
- Statements sit in `Section`s whose `Context` and `Variables` declare what they mention; a theorem
  is generalised over exactly the ones it uses, in declaration order.
  `Relations.Relation_Operators`, `List` and `Bool` are implicit. Every `Inductive` and `Record`
  takes its parameters implicitly in
  constructors and projections (`Arguments` declarations are omitted).
- Both solvers return a function, `{s : X -> A | post_solution L S s}`; the total solver's function
  is `lookup EX L m` of its internal map.

## Files

| File | Contents | Card |
|---|---|---|
| `FixpointQuery.v` | `Query` (`t`, `eval`, `reads`, `sides`, `run`), `ask_all`, `side_all`; determinism, `run_spec` | FIX-1 |
| `FixpointSystem.v` | `System` (`t`, `static`), `post_solution`, `assignment`, `lookup`, `monotone_query`, `monotone_system` | FIX-1 |
| `FixpointIndex.v` | `sys_index`, `index_system`: prepared contributor and reader indexes | FIX-1 |
| `FixpointCheck.v` | `check_post`, the full checker | FIX-1 |
| `FixpointCut.v` | `cut_certificate`, `plan_valid`, `expand`, `replay` | FIX-1 |
| `FixpointLeast.v` | `raise`, `reached`, `least_solution` | FIX-1 |
| `FixpointCycles.v` | `flows`, `cuts_every_cycle` | FIX-1 |
| `FixpointWorklist.v` | `scheduler`, `strategy`, `dependencies`, `Engine`, `engine_step`, the binary fuel loop, `run_worklist`, `solve_fuel`; soundness and adequacy from accessibility | FIX-2a |
| `FixpointTotal.v` | `terminates`, `engine_acc` (accessibility from the evidence), `solve_total`, `solve_total_run`, `solve_total_reached`, `solve_total_least` | FIX-2b |
| `FixpointSchedule.v` | `unknowns`, `dependency_graph`, RPO, WTO and SCC schedulers, `plan_of` | FIX-3 |
| `FixpointNarrow.v` | `narrow_pass`, `narrow_checked` | FIX-3 |
| `FixpointPartial.v` | `closed_partial`, `check_partial` | FIX-4 |
| `FixpointLocal.v` | `local_solve` (untrusted), `local_checked` | FIX-4 |
| `FixpointNested.v` | nested WTO fuel iterator and direct soundness and termination | FIX-5 |
| `FixpointObserve.v` | SCC observation iterator with validated value lifetimes | FIX-6 |
| `FixpointLocalDirect.v` | directly proved static local closure and solver | FIX-7 |

Prerequisites. FIX-2a needs FIX-1 and COL-2; FIX-2b needs FIX-2a and is the hard card (height,
widening rank, widening points that cut every cycle); FIX-3 needs FIX-2b and GRA-3a, GRA-4b, GRA-4c;
FIX-4 needs FIX-2a. A card that needs `solve_total` lists FIX-2b, one that needs only `solve_fuel`
lists FIX-2a.

## Definitions

### FIX-1: queries, systems, checkers

```coq
(* FixpointQuery.v *)
Module Query.
Inductive t (X A : Type) : Type :=
  | Ret (a : A)
  | Ask (x : X) (k : A -> t X A)
  | Side (x : X) (a : A) (q : t X A).
Fixpoint eval {X A} (q : t X A) (s : X -> A) : A :=
  match q with Ret a => a | Ask x k => eval (k (s x)) s | Side _ _ q' => eval q' s end.
Fixpoint reads {X A} (q : t X A) (s : X -> A) : list X :=
  match q with Ret _ => [] | Ask x k => x :: reads (k (s x)) s | Side _ _ q' => reads q' s end.
Fixpoint sides {X A} (q : t X A) (s : X -> A) : list (X * A) :=
  match q with Ret _ => [] | Ask x k => sides (k (s x)) s | Side x a q' => (x, a) :: sides q' s end.
(* one traversal for the value, the unknowns asked and the contributions made; every engine and
   checker calls run once per right-hand side, never eval, reads and sides separately *)
Fixpoint run {X A} (q : t X A) (s : X -> A) : A * list X * list (X * A) :=
  match q with
  | Ret a => (a, [], [])
  | Ask x k => let '(a, rs, ss) := run (k (s x)) s in (a, x :: rs, ss)
  | Side x a q' => let '(r, rs, ss) := run q' s in (r, rs, (x, a) :: ss)
  end.
End Query.
(* ask every unknown of xs in order, then continue with their values *)
Fixpoint ask_all {X A} (xs : list X) (k : list A -> Query.t X A) : Query.t X A :=
  match xs with
  | [] => k []
  | x :: xs' => Query.Ask x (fun a => ask_all xs' (fun vs => k (a :: vs)))
  end.
(* contribute every pair of l, then continue with q *)
Fixpoint side_all {X A} (l : list (X * A)) (q : Query.t X A) : Query.t X A :=
  match l with [] => q | (x, a) :: l' => Query.Side x a (side_all l' q) end.
```

The bodies of the query functions are part of the contract. Assignments and monotonicity
(`FixpointSystem.v`):

```coq
Module System.
Record t (X C A : Type) : Type := Make {
  constraints : list C;
  target : C -> X;
  rhs : C -> Query.t X A
}.
(* A static system declares over-approximations of what each constraint reads and contributes to *)
Record static {X C A} (S : t X C A) : Type := Static {
  deps : C -> list X;
  side_targets : C -> list X;
  reads_within : forall c s, incl (Query.reads (rhs S c) s) (deps c);
  sides_within : forall c s, incl (map fst (Query.sides (rhs S c) s)) (side_targets c)
}.
End System.
Abbreviation deps := System.deps.
Abbreviation side_targets := System.side_targets.
Definition post_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) ->
    leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true /\
    forall x a, In (x, a) (Query.sides (System.rhs S c) s) -> leb L a (s x) = true.
(* assignments are finite maps with a default: lookup returns bot L for an absent unknown *)
Definition assignment (X A : Type) : Type := Map.t X A.
Definition lookup {X A} (EX : encoding X) (L : lattice A) (m : assignment X A) (x : X) : A :=
  match Map.get EX x m with Some a => a | None => bot L end.
(* a larger assignment gives a larger value, and each contribution is matched by a larger one *)
Definition monotone_query {X A} (L : lattice A) (q : Query.t X A) : Prop :=
  monotone_on_assignments L L (Query.eval q) /\
  forall s1 s2, fun_leb L s1 s2 -> forall x a, In (x, a) (Query.sides q s1) ->
    exists b, In (x, b) (Query.sides q s2) /\ leb L a b = true.
Definition monotone_system {X C A} (L : lattice A) (S : System.t X C A) : Prop :=
  forall c, In c (System.constraints S) -> monotone_query L (System.rhs S c).
```

Prepared indexes (`FixpointIndex.v`), built once per static system and shared by the cut-point
checker, the engine, narrowing and the partial checker:

```coq
Record sys_index (X C : Type) : Type := SysIndex {
  contributors : Map.t X (list C);       (* x -> the constraints with target x, or x among side_targets *)
  readers : Map.t X (list C)             (* x -> the constraints with x among deps *)
}.
Definition index_system {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) :
  sys_index X C.
(* one fold over System.constraints S; a constraint c is added once for each DISTINCT unknown of
   System.target S c :: side_targets SS c (contributors) and of deps SS c (readers), the distinct
   unknowns being FinSet.elements (FinSet.of_list EX ...); no constraint list is scanned later *)
Definition contributors_of {X C} (EX : encoding X) (ix : sys_index X C) (x : X) : list C.   (* or [] *)
Definition readers_of {X C} (EX : encoding X) (ix : sys_index X C) (x : X) : list C.         (* or [] *)
Record sys_index_laws {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) : Prop := {
  contributors_agree : forall x c, In c (contributors_of EX ix x) <->
    In c (System.constraints S) /\ (System.target S c = x \/ In x (side_targets SS c));
  readers_agree : forall x c, In c (readers_of EX ix x) <->
    In c (System.constraints S) /\ In x (deps SS c);
  index_nodup : NoDup (System.constraints S) ->
    forall x, NoDup (contributors_of EX ix x) /\ NoDup (readers_of EX ix x)
}.
```

The full checker (`FixpointCheck.v`) runs every constraint once and needs no dependencies, so it
judges dynamic systems too:

```coq
Definition check_post {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : bool :=
  forallb (fun c =>
    let '(v, _, ss) := Query.run (System.rhs S c) s in
    leb L v (s (System.target S c)) && forallb (fun xa => leb L (snd xa) (s (fst xa))) ss)
    (System.constraints S).
```

The cut-point checker (`FixpointCut.v`). The certificate stores values only at the cut points
(loop heads) and orders the other unknowns; `expand` recomputes them in one pass.

```coq
Record cut_certificate (X A : Type) : Type := CutCertificate {
  cuts : FinSet.t X;                     (* the cut points *)
  stored : assignment X A;               (* the values at the cut points; absent means bot *)
  plan : list X                          (* every other unknown that has a constraint, in order *)
}.
(* the static form of the conditions `expand` tests: no duplicates, no cut point in the plan, every
   target and side target covered, and the contributors of each planned x read only cut points,
   earlier planned unknowns, or unknowns with no contributor (whose value is bot) *)
Definition plan_valid {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) : Prop :=
  NoDup plan /\ (forall x, In x plan -> FinSet.mem EX x cuts = false) /\
  (forall c, In c (System.constraints S) ->
     forall x, (x = System.target S c \/ In x (side_targets SS c)) ->
       FinSet.mem EX x cuts = true \/ In x plan) /\
  forall l1 x l2, plan = l1 ++ x :: l2 -> forall c, In c (contributors_of EX ix x) ->
    forall y, In y (deps SS c) ->
      FinSet.mem EX y cuts = true \/ In y l1 \/ contributors_of EX ix y = [].
Definition expand {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) : option (assignment X A).
(* 1. reject unless plan_valid's first three conditions hold (checked with the index);
   2. for x in plan order, with cur the assignment built so far (stored cut values, planned values,
      bot elsewhere): for each contributor c of x take (v, rs, ss) := Query.run (rhs c) cur; reject if
      rs names an unknown with contributors that is neither a cut point nor already computed;
      otherwise the value of x is the join of bot, of v for each c with target c = x, and of every
      a for (x, a) in ss (keys compared by encode);
   3. for each p in FinSet.elements (cuts cert): every contributor c of p, run on the final
      assignment, has its value (if target c = p) and its contributions to p below the stored value
      of p;
   4. return the stored values at the cut points and the computed values at the planned unknowns. *)
(* replay: fold an observer over the plan (and the cut points) with each unknown's value, keeping no
   other state: replay obs b0 (FinSet.elements (cuts cert) ++ plan cert) (lookup EX L m) *)
Definition replay {X A B} (obs : B -> X -> A -> B) (b0 : B) (order : list X) (s : X -> A) : B :=
  fold_left (fun b x => obs b x (s x)) order b0.
```

The least solution without widening (`FixpointLeast.v`). One *run* of a constraint evaluates it once
at the current assignment and joins its value into its target and each contribution into its
unknown; an update that is already below the current value is skipped, exactly as the engine
skips it. `raise` relates assignments up to pointwise equality, so no functional extensionality
is needed.

```coq
Definition join_update {X A} (EX : encoding X) (L : lattice A) (x : X) (a : A) (s : X -> A) :
  X -> A :=
  fun y => if Pos.eqb (encode EX x) (encode EX y)
           then (if leb L a (s y) then s y else join L (s y) a) else s y.
(* the updates one run of c at s makes: its value for its target, then each contribution *)
Definition run_updates {X C A} (S : System.t X C A) (c : C) (s : X -> A) : list (X * A) :=
  let '(v, _, ss) := Query.run (System.rhs S c) s in (System.target S c, v) :: ss.
Definition apply_updates {X A} (EX : encoding X) (L : lattice A) (ups : list (X * A)) (s : X -> A) :
  X -> A := fold_left (fun s' xa => join_update EX L (fst xa) (snd xa) s') ups s.
Definition raise {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A) (s t : X -> A) : Prop :=
  exists c, In c (System.constraints S) /\
    forall y, t y = apply_updates EX L (run_updates S c s) s y.
(* assignments reachable from all-bottom (up to pointwise equality) by runs *)
Definition reached {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  exists s0, (forall x, s0 x = bot L) /\ clos_refl_trans (X -> A) (raise EX L S) s0 s.
Definition least_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  post_solution L S s /\ forall t, post_solution L S t -> fun_leb L s t.
```

Cycles of a static system (`FixpointCycles.v`). A set `W` of unknowns *cuts* the system when the
flows that do not enter `W` have no cycle; cut points and widening points are such sets.

```coq
(* y flows into x when a constraint that reads y has x as its target or as a side target *)
Definition flows {X C A} {S : System.t X C A} (SS : System.static S) (y x : X) : Prop :=
  exists c, In c (System.constraints S) /\ In y (deps SS c) /\
    (x = System.target S c \/ In x (side_targets SS c)).
(* the cut property: deleting the edges into W leaves no cycle of flows *)
Definition cuts_every_cycle {X C A} {S : System.t X C A} (SS : System.static S) (W : X -> bool) : Prop :=
  forall x, ~ clos_trans X (fun y z => flows SS y z /\ W z = false) x x.
```

### FIX-2a: the worklist engine (`FixpointWorklist.v`)

```coq
Record scheduler (X : Type) : Type := Scheduler {
  priority : X -> positive;              (* a constraint runs with the priority of its target; smaller first *)
  widening_point : X -> bool             (* where an update widens instead of joining *)
}.
Inductive strategy : Type := Joining | Widening.     (* Joining: every update is a join *)
(* where the engine learns what each constraint reads *)
Inductive dependencies {X C A} (S : System.t X C A) : Type :=
  | Declared (SS : System.static S) (ix : sys_index X C)   (* from deps, through the prepared index *)
  | Recorded.                                               (* from reads, as each constraint runs *)
Definition dependencies_ok {X C A} (EX : encoding X) {S : System.t X C A} (dep : dependencies S) : Prop :=
  match dep with Declared SS ix => sys_index_laws EX S SS ix | Recorded => True end.

Module Engine.
Record t (X C A : Type) : Type := State {
  current : assignment X A;              (* the values; an absent unknown holds bot *)
  queue : PQueue.t C;                    (* the constraints still to run, each at the priority of its target *)
  recorded : Map.t X (FinSet.t C)        (* with Recorded: the constraints seen to read each unknown *)
}.
End Engine.
(* every constraint queued at the priority of its target, all values bot, nothing recorded *)
Definition initial_state {X C A} (EC : encoding C) (sch : scheduler X) (S : System.t X C A) :
  Engine.t X C A.
(* one step of the engine: None when the queue is empty *)
Definition engine_step {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (dep : dependencies S) (e : Engine.t X C A) :
  option (Engine.t X C A).
(* None when PQueue.is_empty (Engine.queue e). Otherwise:
   1. pop the least (priority, encode c) constraint c, leaving the queue q1;
   2. s := lookup EX L (Engine.current e); (v, rs, ss) := Query.run (System.rhs S c) s;
   3. with Recorded, add c to Engine.recorded at each x of rs; Declared leaves it unchanged;
   4. for each (x, a) of (System.target S c, v) :: ss in order, with cur the map so far: nothing if
      leb L a (lookup EX L cur x) = true; otherwise the value of x becomes
      widen L (lookup EX L cur x) a when st = Widening and widening_point sch x = true, and
      join L (lookup EX L cur x) a otherwise, and every constraint d among the readers of x
      (readers_of EX ix x with Declared; FinSet.elements of recorded at x with Recorded) is pushed
      on the queue at priority (priority sch (System.target S d)). *)
Definition engine_rel {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (dep : dependencies S) (e' e : Engine.t X C A) : Prop :=
  engine_step EX EC L sch st S dep e = Some e'.
Inductive engine_steps {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    (st : strategy) (S : System.t X C A) (dep : dependencies S) :
    nat -> Engine.t X C A -> Engine.t X C A -> Prop :=
  | steps_zero : forall e, engine_steps EX EC L sch st S dep 0 e e
  | steps_succ : forall n e e' e'', engine_steps EX EC L sch st S dep n e e' ->
      engine_rel EX EC L sch st S dep e'' e' ->
      engine_steps EX EC L sch st S dep (Datatypes.S n) e e''.
(* engine_rel orders successor before predecessor for Acc; reachability follows steps forward *)
Definition engine_reachable {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
    (e : Engine.t X C A) : Prop :=
  clos_refl_trans _ (fun from to => engine_rel EX EC L sch st S dep to from)
    (initial_state EC sch S) e.

(* the fuel loop is binary-recursive, so a fuel of n costs O(log n) stack and performs n steps *)
Inductive outcome (X C A : Type) : Type := Done (m : assignment X A) | Pending (e : Engine.t X C A).
Definition then_run {X C A} (f : Engine.t X C A -> outcome X C A) (o : outcome X C A) :
  outcome X C A := match o with Done m => Done m | Pending e => f e end.
Fixpoint loop {X C A} (step : Engine.t X C A -> outcome X C A) (p : positive) (e : Engine.t X C A) :
    outcome X C A :=
  match p with
  | xH => step e                                           (* loop xH = step *)
  | xO p' => then_run (loop step p') (loop step p' e)      (* loop (xO p) = loop p after loop p *)
  | xI p' => then_run step (then_run (loop step p') (loop step p' e))   (* step after loop p after loop p *)
  end.
(* step_outcome e is Done (current e) when engine_step e = None, else Pending of the next state;
   each then_run returns at once when the queue is empty *)
Definition run_worklist {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (dep : dependencies S) (fuel : positive) :
  option (assignment X A) :=
  match loop (step_outcome EX EC L sch st S dep) fuel (initial_state EC sch S) with
  | Done m => Some m | Pending _ => None
  end.
(* the fuel variant for any system, static or not, with a top fallback *)
Definition solve_fuel {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
  (T : top L) (sch : scheduler X) (st : strategy) (S : System.t X C A) (fuel : positive) :
  {s : X -> A | post_solution L S s}.
(* match run_worklist EX EC L sch st S Recorded fuel with
   | Some m => exist _ (lookup EX L m) (run_worklist_sound ..)
   | None => exist _ (fun _ => top_value T) (top_post_solution ..) end *)
```

### FIX-2b: the total engine (`FixpointTotal.v`)

The evidence is passed as `inhabited`, so extraction erases it. A client builds it from Order:
`inhabits (base_height H)` for `H : monotone_height L`, and `inhabits (base_wrank W)` for
`W : bounded_widening_rank L`. The proof of accessibility destructs `inhabited` only into a `Prop`
goal.

```coq
Definition terminates {X C A} {S : System.t X C A} (L : lattice A) (SS : System.static S)
    (sch : scheduler X) (st : strategy) : Prop :=
  match st with
  | Joining => inhabited (height L)
  | Widening => inhabited (widening_rank L) /\ cuts_every_cycle SS (widening_point sch)
  end.
Definition solve_total {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (HT : terminates L SS sch st) : {s : X -> A | post_solution L S s}.
(* Fix on Acc (engine_rel EX EC L sch st S (Declared SS (index_system EX S SS))) at the initial
   state, accessible by engine_acc. The recursion carries engine_reachable e. At a state e with
   engine_step e = None it returns lookup EX L (Engine.current e), a post-solution by
   engine_finished_sound; at Some e' it recurses on e'. No fuel and no evidence is computed. *)
```

### FIX-3: schedulers and narrowing

```coq
(* FixpointSchedule.v *)
Definition unknowns {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : list X.
(* FinSet.elements of FinSet.of_list EX: the distinct targets, deps and side targets of the constraints *)
Definition dependency_graph {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) :
    Graph.t X (X * X).
(* Graph.nodes = Graph.entries = unknowns; Graph.out y = the edges (y, x), one for each distinct x with
   flows SS y x, found through readers_of of index_system EX S SS, with no repeated edge;
   Graph.source = fst, Graph.target = snd *)
(* each scheduler below prepares its graph once, g := dependency_graph, p := prepare EX g, and its
   theorems use ready EX g p, proved by dependency_graph_ready *)
Definition rpo_scheduler {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : scheduler X.
(* r := dfs p FinSet.empty (Graph.entries g); priority = position in rpo r (a map built once);
   widening points = the targets of the retreating edges, tested with ancestor_b EX r *)
Definition wto_scheduler {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : scheduler X.
(* w := wto_total p, the total producer of Graph (always wto_valid); priority = textual position in
   wto_order w; widening points = the heads of the components of w *)
Definition scc_scheduler {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : scheduler X.
(* priority x = 1 + comp * n + pos, where n = length (unknowns EX S SS), comp = the index of the
   component of x counted from the end of Tarjan's emission order of scc_within p (Graph.nodes g)
   (so a component follows every component that flows into it), and pos = the rpo position of x;
   widening points = the headers of loop_forest_of p *)
Definition plan_of {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (cuts : FinSet.t X) : option (list X).
(* topological_sort of the flows restricted to non-cut targets, over the unknowns that are not cut *)

(* FixpointNarrow.v *)
Definition narrow_pass {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (m : assignment X A) : assignment X A.
(* one simultaneous pass over the unknowns that have contributors, reading only m: with a the join of
   bot and the contributions at lookup EX L m to x (one Query.run per constraint), the new value is
   narrow L (m x) a when leb L a (m x) = true, and m x otherwise *)
Definition narrow_checked {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (rounds : nat) (m : assignment X A) : assignment X A :=
  let m' := Nat.iter rounds (narrow_pass EX L S SS ix) m in
  if check_post L S (lookup EX L m') then m' else m.
```

### FIX-4: closed partial solutions and the local solver

```coq
(* FixpointPartial.v: on the explored set E, every constraint whose target is in E or that may
   contribute to E reads only E and is satisfied on E *)
Definition closed_partial {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (E : FinSet.t X) (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
    (forall y, In y (Query.reads (System.rhs S c) s) -> FinSet.mem EX y E = true) /\
    (FinSet.mem EX (System.target S c) E = true ->
       leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true) /\
    forall y a, In (y, a) (Query.sides (System.rhs S c) s) -> FinSet.mem EX y E = true ->
      leb L a (s y) = true.
Definition check_partial {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (E : FinSet.t X) (m : assignment X A) : bool.
(* for each x in FinSet.elements E and each c in contributors_of EX ix x, one Query.run on
   lookup EX L m and the three conditions *)
(* E is closed under what its constraints read *)
Definition dependency_closed {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (E : FinSet.t X) : Prop :=
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
    forall y, In y (deps SS c) -> FinSet.mem EX y E = true.

(* FixpointLocal.v *)
Record local_result (X A : Type) : Type := LocalResult { explored : FinSet.t X; values : assignment X A }.
Definition local_solve {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
  (roots : list X) (fuel : positive) : option (local_result X A).
(* the worklist over the dependency closure of roots: the least set E that contains roots and is
   closed under "x in E, c in contributors_of x, y in deps c gives y in E"; the queue starts with the
   constraints that contribute to E and the engine runs as engine_step with Declared SS ix, joins or
   widening as st says; explored = E. Untrusted: no theorem about its values. Acceptance evidence:
   a required Example in tests/Fixpoint/FixpointFIX4.v runs local_checked on a three-unknown
   cyclic system and gets Some. *)
Definition local_checked {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    (st : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (roots : list X) (fuel : positive) : option (local_result X A) :=
  match local_solve EX EC L sch st S SS ix roots fuel with
  | Some r =>
      let E := FinSet.of_list EX (FinSet.elements (explored r)) in   (* normalised: FinSet.wf *)
      if check_partial EX L S SS ix E (values r) && forallb (fun x => FinSet.mem EX x E) roots
      then Some (LocalResult E (values r)) else None
  | None => None
  end.
```

### FIX-7: directly proved static local solving

`FixpointLocalDirect.v` adds a trusted internal producer for finite static systems. It does not
replace FIX-4's checker or claim to solve dynamic systems. Build the finite bipartite graph once:
unknown x reaches each indexed constraint that has nominal target x or declares x as a side
target; each such constraint reaches its nominal target, all declared side targets and all
declared reads. Starting from the roots, visit each discovered unknown and constraint at most
once using the existing encodings and indexed collections. Do not scan the constraints or the
unknown universe inside the traversal. Its unknown set is `local_direct_closure`. Roots outside
the system remain in the closure and have bottom values unless constrained.

`local_direct_system` retains exactly the original constraints reached by this closure, in the
original constraint-list order, and retains their original targets and query trees. It is built
once; `local_direct_static` restricts the existing declarations to that system. Run the existing
`solve_total` on the restricted system, then construct an assignment by storing the resulting
value for each closure member. All other unknowns have the assignment's default bottom. The
termination evidence supplied by the caller is for the restricted system and the selected
scheduler and strategy. The producer never calls `check_partial` or gates its result on checker
acceptance. No least-solution claim follows from these statements for weak joins or widening.

```coq
Definition local_direct_closure {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) : FinSet.t X.
Definition local_direct_system {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) : System.t X C A.
Definition local_direct_static {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  System.static (local_direct_system EX EC S SS ix roots).
Definition local_direct {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) : local_result X A.

Theorem local_direct_closure_wf {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  FinSet.wf EX (local_direct_closure EX EC S SS ix roots).
Theorem local_direct_closure_roots {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  forall x, In x roots -> FinSet.mem EX x (local_direct_closure EX EC S SS ix roots) = true.
Theorem local_direct_closure_least {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (E : FinSet.t X) :
  FinSet.wf EX E -> (forall x, In x roots -> FinSet.mem EX x E = true) ->
  (forall x c, FinSet.mem EX x E = true -> In c (contributors_of EX ix x) ->
    FinSet.mem EX (System.target S c) E = true /\
    (forall y, In y (side_targets SS c) -> FinSet.mem EX y E = true) /\
    (forall y, In y (deps SS c) -> FinSet.mem EX y E = true)) ->
  FinSet.subset EX (local_direct_closure EX EC S SS ix roots) E = true.
Theorem local_direct_closure_complete {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  sys_index_laws EX S SS ix ->
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true \/
     exists y, In y (side_targets SS c) /\
       FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true) ->
    FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true /\
    (forall y, In y (side_targets SS c) ->
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true) /\
    (forall y, In y (deps SS c) ->
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true).
Theorem local_direct_system_constraints {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) (c : C) :
  sys_index_laws EX S SS ix ->
  (In c (System.constraints (local_direct_system EX EC S SS ix roots)) <->
   In c (System.constraints S) /\
   (FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true \/
    exists y, In y (side_targets SS c) /\
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true)).
Theorem local_direct_roots {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) :
  forall x, In x roots -> FinSet.mem EX x (explored (local_direct EX EC L HL sch st S SS ix roots HT)) = true.
Theorem local_direct_closed {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) :
  sys_index_laws EX S SS ix ->
  let r := local_direct EX EC L HL sch st S SS ix roots HT in
  closed_partial EX L S SS (explored r) (lookup EX L (values r)).
```

The closure is the least set containing roots and closed under these graph edges. Prove its
termination from the finite discovered support, and prove the restricted constraints are exactly
the reached constraints. The closure theorem and `reads_within` ensure that projecting the
engine's function to a finite assignment preserves each activated query's reads, result and side
contributions. Apply `solve_total`'s direct post-solution theorem to the restricted system and
transfer it to `closed_partial`; no global functional extensionality or per-run checker is needed.
Card: FIX-7.

## Theorems

### FIX-1

```coq
Section Fix1.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).
Variables (q : Query.t X A) (s t s1 s2 : X -> A) (xs : list X) (l : list (X * A))
  (k : list A -> Query.t X A) (m : assignment X A).

(** A query depends only on the unknowns it reads: agreement on them fixes its value, reads and contributions. *)
Theorem query_determined : (forall x, In x (Query.reads q s) -> s x = t x) ->
  Query.eval q s = Query.eval q t /\ Query.reads q s = Query.reads q t /\ Query.sides q s = Query.sides q t.
(* Proof idea: induction on q; at Ask x k the asked unknown agrees, so the continuations agree. Card: FIX-1. *)
(** The one-traversal `run` returns exactly the three separate answers. *)
Theorem run_spec : Query.run q s = (Query.eval q s, Query.reads q s, Query.sides q s).
(* Proof idea: induction on q. Card: FIX-1. *)
(** `ask_all` asks the listed unknowns in order, then continues with their values. *)
Theorem ask_all_spec : Query.reads (ask_all xs k) s = xs ++ Query.reads (k (map s xs)) s /\
  Query.eval (ask_all xs k) s = Query.eval (k (map s xs)) s /\
  Query.sides (ask_all xs k) s = Query.sides (k (map s xs)) s.
(* Proof idea: induction on xs. Card: FIX-1. *)
(** `side_all` contributes the listed pairs first and then behaves as the continuation. *)
Theorem side_all_spec : Query.eval (side_all l q) s = Query.eval q s /\
  Query.reads (side_all l q) s = Query.reads q s /\ Query.sides (side_all l q) s = l ++ Query.sides q s.
(* Proof idea: induction on l. Card: FIX-1. *)

(** The full checker decides post-solutions, and the all-top assignment is one. *)
Theorem check_post_iff : check_post L S s = true <-> post_solution L S s.
(* Proof idea: forallb_forall, run_spec, and leb = true is the Prop. Card: FIX-1. *)
Theorem top_post_solution (T : top L) : post_solution L S (fun _ => top_value T).
(* Proof idea: top_greatest for the value and for every contribution. Card: FIX-1. *)

(** The prepared indexes agree with the system. *)
Theorem index_system_laws (SS : System.static S) : sys_index_laws EX S SS (index_system EX S SS).
(* Proof idea: a fold of Map.set over the constraints, each added once per distinct unknown, then the Map.get_set lemmas and FinSet.of_list_spec. Card: FIX-1. *)

(** An accepted certificate expands to a post-solution that keeps the stored cut values. *)
Theorem expand_sound (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  lattice_laws L -> sys_index_laws EX S SS ix -> FinSet.wf EX (cuts cert) ->
  expand EX L S SS ix cert = Some m ->
  post_solution L S (lookup EX L m) /\
  forall p, FinSet.mem EX p (cuts cert) = true -> lookup EX L m p = lookup EX L (stored cert) p.
(* Proof idea: a planned value is the join of every contribution to it, computed on values that are already final, so query_determined gives the final evaluation the same result; FinSet.elements_spec makes step 3 cover every cut point, checked against the final assignment; join_upper_l and join_upper_r give each leb. Card: FIX-1. *)
(** Completeness: a post-solution, its values at the cut points and a valid plan are accepted, and the expansion lies below it. *)
Theorem expand_complete (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  lattice_laws L -> lub_laws L -> monotone_system L S -> sys_index_laws EX S SS ix ->
  FinSet.wf EX (cuts cert) -> post_solution L S s -> plan_valid EX S SS ix (cuts cert) (plan cert) ->
  (forall p, FinSet.mem EX p (cuts cert) = true -> lookup EX L (stored cert) p = s p) ->
  exists m, expand EX L S SS ix cert = Some m /\ fun_leb L (lookup EX L m) s.
(* Proof idea: induction along the plan: each planned value is below s by monotonicity and join_least, since its reads are cut points or earlier values below s; reads_within makes the declared dependencies of plan_valid cover the dynamic reads; the cut-point check follows from the final assignment lying below s. Card: FIX-1. *)
(** Cycle detection is built in: a valid plan exists only when the cut points cut every cycle. *)
Theorem plan_valid_cuts (SS : System.static S) (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) :
  sys_index_laws EX S SS ix -> plan_valid EX S SS ix cuts plan ->
  cuts_every_cycle SS (fun x => FinSet.mem EX x cuts).
(* Proof idea: along a cycle of non-cut unknowns each flow puts the source earlier in the plan, so positions would increase strictly around the cycle. Card: FIX-1. *)

(** Replaying folds the observer over the order with each value; an invariant kept by every visited step holds at the end. *)
Theorem replay_invariant {B} (I : B -> Prop) (obs : B -> X -> A -> B) (b0 : B) (order : list X) :
  I b0 -> (forall b x, In x order -> I b -> I (obs b x (s x))) -> I (replay obs b0 order s).
(* Proof idea: induction on order, generalising the accumulator. Card: FIX-1. *)
(** The replay order of an accepted certificate lists every unknown that has a constraint, each once. *)
Theorem replay_covers (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  sys_index_laws EX S SS ix -> FinSet.wf EX (cuts cert) -> expand EX L S SS ix cert = Some m ->
  NoDup (FinSet.elements (cuts cert) ++ plan cert) /\
  forall x, (exists c, In c (System.constraints S) /\ (x = System.target S c \/ In x (side_targets SS c))) ->
    In x (FinSet.elements (cuts cert) ++ plan cert).
(* Proof idea: plan_valid's first three conditions, which expand checks, give NoDup and coverage; FinSet.elements_spec and FinSet.elements_nodup turn membership in the cut set into membership in the list. Card: FIX-1. *)

(** Under the strong laws, runs from bottom never exceed a post-solution of a monotone system; a reached post-solution is the least solution, which is unique up to equivalence. *)
Theorem reached_below : lattice_laws L -> lub_laws L -> monotone_system L S ->
  post_solution L S t -> reached EX L S s -> fun_leb L s t.
(* Proof idea: induction on the runs: bot_least, then each update (x, a) of a run at an assignment below t satisfies leb L a (t x) by monotone_query and the post-solution inequalities of t, so join_least keeps every value below t. Card: FIX-1. *)
Theorem reached_least : lattice_laws L -> lub_laws L -> monotone_system L S ->
  reached EX L S s -> post_solution L S s -> least_solution L S s.
(* Proof idea: reached_below for every post-solution. Card: FIX-1. *)
Theorem least_solution_unique : least_solution L S s1 -> least_solution L S s2 ->
  fun_leb L s1 s2 /\ fun_leb L s2 s1.
(* Proof idea: each is below the other by minimality. Card: FIX-1. *)
End Fix1.
```

### FIX-2a

Soundness never depends on the scheduler: it holds for every `sch`.

```coq
Section Fix2a.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy) (dep : dependencies S) (e : Engine.t X C A)
  (m : assignment X A).
Local Notation step := (engine_step EX EC L sch st S dep).
Local Notation start := (initial_state EC sch S).

(** A finished reachable state is a post-solution, whether dependencies are declared or recorded. *)
Theorem engine_finished_sound : lattice_laws L -> dependencies_ok EX dep ->
  engine_reachable EX EC L sch st S dep e -> step e = None ->
  post_solution L S (lookup EX L (Engine.current e)).
(* Proof idea: invariant: every constraint is queued or satisfied by the current values; a pop evaluates c once (run_spec), raises go upward (join_upper_r, widen_upper_r, leb_trans), and every constraint that reads a changed unknown is queued (readers_agree and reads_within with Declared; the recorded reads with Recorded, recorded before the updates), so an unqueued constraint keeps its reads and its value (query_determined); an empty queue (PQueue.pop_none, is_empty_spec) leaves no queued constraint. Card: FIX-2a. *)

(** The binary fuel loop performs exactly one engine step per unit of fuel, and stops at an empty queue. *)
Theorem run_worklist_spec (fuel : positive) :
  run_worklist EX EC L sch st S dep fuel = Some m <->
  exists n e', (n < Pos.to_nat fuel)%nat /\ engine_steps EX EC L sch st S dep n start e' /\
    step e' = None /\ Engine.current e' = m.
(* Proof idea: induction on the fuel: loop step p e is the (Pos.to_nat p)-fold iteration of step_outcome with an early exit, because loop (xO p) and loop (xI p) compose loop p twice, and then_run keeps a Done. Card: FIX-2a. *)
(** A finished run is a post-solution. *)
Theorem run_worklist_sound (fuel : positive) : lattice_laws L -> dependencies_ok EX dep ->
  run_worklist EX EC L sch st S dep fuel = Some m -> post_solution L S (lookup EX L m).
(* Proof idea: run_worklist_spec gives a reachable finished state; engine_finished_sound. Card: FIX-2a. *)
(** Adequacy from accessibility: if the engine's step relation is accessible from the initial state, enough fuel never runs out. *)
Theorem run_worklist_acc : Acc (engine_rel EX EC L sch st S dep) start ->
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S dep fuel = Some m'.
(* Proof idea: Acc induction: from an accessible state the unique step chain reaches a state with an empty queue after some n steps; take f = n + 1 and apply run_worklist_spec. Card: FIX-2a. *)
End Fix2a.
```

### FIX-2b

```coq
Section Fix2b.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy) (T : top L) (m : assignment X A).

(** With termination evidence the step relation is accessible from the initial state, with declared or recorded dependencies. *)
Theorem engine_acc (SS : System.static S) (ix : sys_index X C) : lattice_laws L ->
  terminates L SS sch st -> sys_index_laws EX S SS ix ->
  Acc (engine_rel EX EC L sch st S (Declared SS ix)) (initial_state EC sch S) /\
  Acc (engine_rel EX EC L sch st S Recorded) (initial_state EC sch S).
(* Proof idea: a measure that decreases at every step of a state whose queue holds only constraints of S. Joining: the pair (sum over the finite set unknowns of bound minus rank of the value, queue length), lexicographic: an effective update increases a rank (join_rank_grows, using join_upper_r and leb_trans to turn "not below" into "the join is not below"), any other pop shortens the queue. Widening: (sum over widening points of wrank of the value, sum over queued constraints of weight), where weight c = 1 + the sum, over x in target c :: side_targets c, of 1 if x is a widening point and of the total weight of the readers of x otherwise, well founded because cuts_every_cycle forbids a cycle of constraints through non-widening unknowns; an update at a widening point lowers wrank (widen_rank_progress), and one elsewhere only queues readers of total weight below that of the popped constraint. Recorded readers are among the declared ones (reads_within). The Prop goal alone lets inhabited be destructed. Card: FIX-2b. *)
(** With termination evidence, enough fuel never runs out, with declared or recorded dependencies. *)
Theorem run_worklist_adequate (SS : System.static S) : lattice_laws L -> terminates L SS sch st ->
  (exists f, forall fuel, (f <= fuel)%positive -> exists m',
     run_worklist EX EC L sch st S (Declared SS (index_system EX S SS)) fuel = Some m') /\
  (exists f, forall fuel, (f <= fuel)%positive -> exists m',
     run_worklist EX EC L sch st S Recorded fuel = Some m').
(* Proof idea: engine_acc with index_system_laws, then run_worklist_acc. Card: FIX-2b. *)
(** With evidence, the fuel variant returns the run, not the top fallback. *)
Theorem solve_fuel_exact (HL : lattice_laws L) (SS : System.static S) : terminates L SS sch st ->
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S Recorded fuel = Some m' /\
    proj1_sig (solve_fuel EX EC L HL T sch st S fuel) = lookup EX L m'.
(* Proof idea: run_worklist_adequate for Recorded, then unfold solve_fuel. Card: FIX-2b. *)
(** The Acc-based total solver and the fuel loop compute the same function. *)
Theorem solve_total_run (HL : lattice_laws L) (SS : System.static S) (HT : terminates L SS sch st) :
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S (Declared SS (index_system EX S SS)) fuel = Some m' /\
    proj1_sig (solve_total EX EC L HL sch st S SS HT) = lookup EX L m'.
(* Proof idea: both follow the same deterministic chain of engine_step to its first state with an empty queue; run_worklist_spec for the fuel side, the Fix equation for the other. Card: FIX-2b. *)
(** Without widening, every value of the result was reached from bottom by runs of constraints. *)
Theorem solve_total_reached (HL : lattice_laws L) (SS : System.static S)
    (HT : terminates L SS sch Joining) :
  reached EX L S (proj1_sig (solve_total EX EC L HL sch Joining S SS HT)).
(* Proof idea: each step is one raise (the pops evaluate at the current values; skipped updates are skipped by join_update), so the chain of engine_step from the initial state is a clos_refl_trans chain up to pointwise equality of lookup EX L. Card: FIX-2b. *)
(** Without widening, the total engine returns the least solution of a monotone system. *)
Theorem solve_total_least (HL : lattice_laws L) (SS : System.static S)
    (HT : terminates L SS sch Joining) :
  lub_laws L -> monotone_system L S ->
  least_solution L S (proj1_sig (solve_total EX EC L HL sch Joining S SS HT)).
(* Proof idea: solve_total_reached and the post-solution proof of the sigma give reached_least. Card: FIX-2b. *)
End Fix2b.
```

### FIX-3

```coq
Section Fix3.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A) (SS : System.static S).
Variables (ix : sys_index X C) (rounds : nat) (m : assignment X A) (cuts : FinSet.t X).
Local Notation g := (dependency_graph EX S SS).

(** The unknowns are exactly those that occur, once each. *)
Theorem unknowns_spec : NoDup (unknowns EX S SS) /\ forall x, In x (unknowns EX S SS) <->
  exists c, In c (System.constraints S) /\
    (x = System.target S c \/ In x (deps SS c) \/ In x (side_targets SS c)).
(* Proof idea: FinSet.elements_nodup and FinSet.of_list_spec. Card: FIX-3. *)
(** The flows of the system are the edges of its dependency graph, which is well formed and ready for the Graph algorithms. *)
Theorem dependency_graph_flows : graph_wf g /\ (forall v, NoDup (Graph.out g v)) /\
  forall y x, flows SS y x <-> exists e, In e (Graph.out g y) /\ Graph.target g e = x.
(* Proof idea: unfold dependency_graph; the unknowns list contains every end of a flow, and the edges are collected through FinSet so none repeats. Card: FIX-3. *)
Theorem dependency_graph_ready : ready EX g (prepare EX g).
(* Proof idea: prepare_ready on dependency_graph_flows. Card: FIX-3. *)

(** The widening points of each scheduler cut every cycle of flows, so a widening rank suffices for termination. *)
Theorem rpo_scheduler_cuts : cuts_every_cycle SS (widening_point (rpo_scheduler EX S SS)).
(* Proof idea: a cycle of flows is a cycle of the dependency graph, which contains a retreating edge (cycle_has_retreating_edge, with ancestor_b_agrees) whose target is a widening point on the cycle. Card: FIX-3. *)
Theorem wto_scheduler_cuts : cuts_every_cycle SS (widening_point (wto_scheduler EX S SS)).
(* Proof idea: wto_total_valid holds (the producer falls back to the all-heads order), and
   wto_valid_cycles puts the head of a component on every cycle. Card: FIX-3. *)
Theorem scc_scheduler_cuts : cuts_every_cycle SS (widening_point (scc_scheduler EX S SS)).
(* Proof idea: loop_forest_covers puts a header of loop_forest_of on every cycle. Card: FIX-3. *)

(** `plan_of` succeeds exactly when the cut points cut every cycle, and then its plan is valid. *)
Theorem plan_of_valid : sys_index_laws EX S SS ix ->
  (cuts_every_cycle SS (fun x => FinSet.mem EX x cuts) <-> exists plan, plan_of EX S SS ix cuts = Some plan) /\
  forall plan, plan_of EX S SS ix cuts = Some plan -> plan_valid EX S SS ix cuts plan.
(* Proof idea: topological_sort_correct on the flows into non-cut unknowns; plan_valid_cuts for the converse. Card: FIX-3. *)

(** Narrowing keeps soundness and never moves a value up; the checker guards the output. *)
Theorem narrow_checked_post : post_solution L S (lookup EX L m) ->
  post_solution L S (lookup EX L (narrow_checked EX L S SS ix rounds m)).
(* Proof idea: either the checker accepted the narrowed assignment (check_post_iff) or the input is returned. Card: FIX-3. *)
Theorem narrow_checked_below : lattice_laws L ->
  fun_leb L (lookup EX L (narrow_checked EX L S SS ix rounds m)) (lookup EX L m).
(* Proof idea: a pass narrows only under leb L a (m x) = true, so narrow_lower gives a decrease, else the value is kept (leb_refl); induction on rounds. Card: FIX-3. *)
End Fix3.
```

### FIX-4

```coq
Section Fix4.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A) (SS : System.static S).
Variables (ix : sys_index X C) (E : FinSet.t X) (m : assignment X A) (s t l : X -> A).

(** The checker decides closed partial solutions on a well-formed explored set, reading only the constraints that touch it. *)
Theorem check_partial_correct : sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  (check_partial EX L S SS ix E m = true <-> closed_partial EX L S SS E (lookup EX L m)).
(* Proof idea: contributors_agree says the indexed constraints are exactly those with a target or declared side target in E; FinSet.elements_spec makes the iteration cover E. Card: FIX-4. *)

(** A closed partial solution is the restriction of a global post-solution, so every theorem proved
    for all post-solutions holds at its unknowns, and it lies above the least solution there. *)
Theorem closed_partial_extends (T : top L) : closed_partial EX L S SS E s ->
  exists t, post_solution L S t /\ forall x, FinSet.mem EX x E = true -> t x = s x.
(* Proof idea: t is s on E and top elsewhere; a checked constraint reads only E, so t agrees with s on its reads (query_determined) and satisfies it; any other constraint targets top, and contributes into E only if it was checked, by sides_within. Card: FIX-4. *)
Theorem closed_partial_above_least (T : top L) : closed_partial EX L S SS E s -> least_solution L S l ->
  forall x, FinSet.mem EX x E = true -> leb L (l x) (s x) = true.
(* Proof idea: closed_partial_extends gives a post-solution t; l is below t and t x = s x. Card: FIX-4. *)
(** Conversely, every post-solution restricts to a closed partial solution on each dependency-closed set. *)
Theorem post_solution_closed : post_solution L S t -> dependency_closed EX S SS E ->
  closed_partial EX L S SS E t.
(* Proof idea: reads_within puts the reads of a touched constraint in deps, hence in E; the inequalities are post_solution's. Card: FIX-4. *)

(** An accepted local run is a well-formed closed partial solution that covers its roots. *)
Theorem local_checked_sound (EC : encoding C) (sch : scheduler X) (st : strategy)
    (roots : list X) (fuel : positive) (r : local_result X A) :
  sys_index_laws EX S SS ix -> local_checked EX EC L sch st S SS ix roots fuel = Some r ->
  FinSet.wf EX (explored r) /\
  closed_partial EX L S SS (explored r) (lookup EX L (values r)) /\
  forall x, In x roots -> FinSet.mem EX x (explored r) = true.
(* Proof idea: the explored set is FinSet.of_list of an elements list, well formed by FinSet.wf_ops; the two conjuncts of the test, by check_partial_correct and forallb_forall. Card: FIX-4. *)
End Fix4.
```

## Algorithms and references

- **Worklist iteration** with a priority queue: Kildall, "A unified approach to global program
  optimization" (POPL 1973); chaotic iteration as in Nielson, Nielson and Hankin, *Principles of
  Program Analysis* (1999). Raising an unknown pushes only its readers.
- **Fuel and accessibility.** The fuel loop is binary-recursive, so `n` steps cost O(log n) stack;
  the total solver recurses on an `Acc` proof (Bove and Capretta's method), which extraction erases.
- **Widening and narrowing:** Cousot and Cousot (POPL 1977 and 1979). Widening only at a set that
  cuts every cycle: Bourdoncle, "Efficient chaotic iteration strategies with widenings" (1993).
- **Side-effecting constraint systems:** Apinis, Seidl and Vojdani, "Side-effecting constraint
  systems: a Swiss Army knife for program analysis" (APLAS 2012). The query tree `Ret`/`Ask`/`Side`
  is the free form of such a right-hand side, so reads and contributions are observable.
- **Checking only at cut points:** Besson, Jensen and Pichardie, "Proof-carrying code from
  certified abstract interpretation and fixpoint compression" (TCS 2006); Rose, "Lightweight
  bytecode verification" (J. Automated Reasoning 2003). `expand` is the one-pass recomputation.
- **Local solvers:** Le Charlier and Van Hentenryck, "A universal top-down fixpoint algorithm"
  (1992); Fecht and Seidl, "A faster solver for general systems of equations" (1999). The solver
  is untrusted; `check_partial` is the verified part.
- **Constructive fixpoints in a proof assistant:** Cachera, Jensen, Pichardie and Rusu,
  "Extracting a data flow analyser in constructive logic" (TCS 2005).

## Performance notes

- The engine keeps a `PQueue` of constraints keyed by `encoding C` with the priority of the target.
  A pop evaluates one right-hand side once (`Query.run`), costing its size; an update pushes
  `readers_of` the unknown, a prepared list, so no constraint list is scanned inside the loop. With
  `Recorded`, readers live in a `Map.t X (FinSet.t C)`, so a repeated read is not stored twice.
  The number of pops is bounded by the number of constraints times one plus the number of changes
  of what each reads.
- Each prepared index has an agreement lemma: `contributors` and `readers` with `sys_index_laws`
  (`index_system_laws`); the partial checker and narrowing reuse the same index. The schedulers
  build their dependency graph and its preparation once, outside the closures they return.
- `check_post` is O(sum of right-hand-side sizes). `expand` is one pass: O(sum over constraints of
  (1 + side targets) times right-hand-side size), with the plan position never searched (`cur` is
  a `Map`). `narrow_pass` is one evaluation of every constraint per round. `check_partial` costs the
  constraints that touch `E`, found through `contributors`, not the whole system.
- `solve_total` carries its termination proof in `Prop`, which extraction erases, so no fuel or
  evidence is passed at run time; `solve_fuel` pays one unit per pop.

## Open questions

1. **Constraint encodings.** The engine queues constraints, so the constraint type needs an
   `encoding C`; Views' `dense_constraint N E` has one by `sum_encoding`, and `E` must be encodable.
2. **WTO strategy.** `wto_scheduler` is a priority (textual position) with widening at heads. The
   recursive Bourdoncle strategy, which stabilises a component before leaving it, is not a
   priority order and is left out; the termination and soundness theorems do not need it.
3. **Lattices without a join-least law.** The least-solution theorems need `lub_laws`; for
   weak-law domains (wrapping intervals) only post-solutions are claimed.
4. **Side effects and cut points.** A contribution to `y` from `c` makes `c` a contributor of
   `y`, so a plan must place every unknown `c` reads before `y`; a system whose side effects point
   backwards needs `y` as a cut point. `flows` includes side targets for this reason.
5. **Local solver scope.** `FIX-4` needs a `System.static` (for `side_targets`); the dynamic
   points-to system of Analyses has none, so it is checked by `check_post` only.
6. **Determinism.** Pop order is `(priority, encode c)`, fixed by Collections' `PQueue`, so every
   run is reproducible; the least solution does not depend on it, a widened result may.

## Cross-document contracts

The solver results are functions carrying post-solution proofs. Schedulers prepare the static
system dependency graph; `wto_scheduler` constructs its WTO with `wto_total`. Termination
evidence is `inhabits (base_height H)` or `inhabits (base_wrank W)`. Graph preparation requires
well-formed graphs and duplicate-free outgoing edges.

<!-- AUD-API-FX-BEGIN -->

# Fixpoint source contracts

Definitions specify source work; future theorem types are proof obligations.

The generic full and partial nested adapters describe model-level behavior for opaque
continuations. The rooted checker statements cover the actual full and partial checker bodies
and their per-call source receipts. They use actual system constraints and the stated index laws.

## Galois.Fixpoint.FixpointAuditCache

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditCache.v`.

```rocq
(** Contextual cache with real index producer and actual epoch/context encoder bodies.
    Engine external callbacks are accounted for by the declared-worklist source adapter. *)
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
Definition cache_key_source_laws {Epoch Context B} (keys : cache_key_models Epoch Context B)
    (source : cache_key_source Epoch Context B) : Prop :=
  (forall e, let '(out, body) := cache_epoch_encoder keys e in cache_epoch_source source e out body)
  /\
  (forall t, let '(out, body) := cache_context_encoder keys t in cache_context_source source t out
  body).
Definition cache_key_source_bounded {Epoch Context B} (source : cache_key_source Epoch Context B)
    (budget : cache_key_budget Epoch Context B) : Prop :=
  (forall e out body, cache_epoch_source source e out body ->
    fx_one_body_work (cache_key_weight budget) body <= cache_epoch_bound budget e) /\
  (forall t out body, cache_context_source source t out body ->
    fx_one_body_work (cache_key_weight budget) body <= cache_context_bound budget t).
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
  | CacheEpochBody _ _ body | CacheContextBody _ _ body => 1 + fx_one_body_work (cache_key_weight
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
  fold_right (fun event n => match event with
    | CacheEngineBody _ calls => fx_declared_external_trace_budget wb calls + n
    | _ => n end) 0 events.
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
```

## Galois.Fixpoint.FixpointAuditCacheSemantic

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditCacheSemantic.v`.

```rocq
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

(** Proposed preservation and result theorem type, not a proof. *)
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

(** Proposed result and invariant preservation type under the explicit client law. *)
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

Definition cache_epoch_initial_valid_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (snap : contextual_snapshot X C A Epoch Context) fuel,
    cache_valid EX EC (context_cached_solver (contextual_init EX EC snap fuel)).

Definition cache_epoch_miss_rebuild_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel c,
    epoch (cached_snapshot (context_cached_solver c)) <> epoch (context_snapshot snap) \/
      context_cached_token c <> context_token snap ->
    contextual_query EX EC EE ET snap fuel c = contextual_init EX EC snap fuel.

Definition cache_epoch_hit_statement : Prop :=
  forall X C A Epoch Context (EX : encoding X) (EC : encoding C)
    (EE : encoding Epoch) (ET : encoding Context)
    (snap : contextual_snapshot X C A Epoch Context) fuel c,
    epoch (cached_snapshot (context_cached_solver c)) = epoch (context_snapshot snap) ->
    context_cached_token c = context_token snap ->
    cached_fuel (context_cached_solver c) = fuel ->
    cached_result (context_cached_solver (contextual_query EX EC EE ET snap fuel c)) =
      cached_result (context_cached_solver c).

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


```

## Galois.Fixpoint.FixpointAuditCheckCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditCheckCallbacks.v`.

```rocq
(** * Rooted full-checker callback receipts

    The checker source model relates only callbacks reached from actual system constraints.
    For example, an unrelated constraint identifier supplies no continuation obligation.
    Builds on: FixpointAuditNarrowCheck and the declared callback source model. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNarrowCheck.
Import List.ListNotations.

Definition fx_local_set_entries {K}
    (events : list (audit_set_event K (fx_encoder_entry K))) : list (fx_encoder_entry K) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

Definition fx_local_x_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

Definition fx_local_c_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry C) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry c code => fx_source_encode_c source c code body
  end.

Definition fx_local_x_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry X)) : nat :=
  fold_right (fun entry n => match entry with
    | FxEncodeEntry x _ => fx_budget_encode_x budget x + n
    end) 0 entries.

Definition fx_local_c_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry C)) : nat :=
  fold_right (fun entry n => match entry with
    | FxEncodeEntry c _ => fx_budget_encode_c budget c + n
    end) 0 entries.

Definition fx_narrow_check_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_fullcheck_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FfcQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FfcRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FfcTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FfcLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | _ => bodies = []
  end.

Definition fx_narrow_check_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_fullcheck_event X C A) : nat :=
  match event with
  | FfcQuery events => fx_declared_external_trace_budget budget events
  | FfcRhs c _ => fx_budget_rhs budget c
  | FfcTarget c _ => fx_budget_target budget c
  | FfcLeb a b _ => fx_budget_leb budget a b
  | _ => 0
  end.

Definition fx_fullcheck_rooted_laws {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, In c (System.constraints S) ->
    exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, In c (System.constraints S) ->
    exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c) /\
  (forall k a out body, fx_source_continuation source k a out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b out body, fx_source_leb source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_leb budget a b).

Definition fx_fullcheck_rooted_trace_source {X C A B}
    (source : fx_declared_callback_source X C A B) (events : list (fx_fullcheck_event X C A))
    (bodies : list (list (list B))) : Prop := Forall2 (fx_narrow_check_source source) events bodies.

Definition fx_fullcheck_rooted_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_fullcheck_event X C A)) : nat
  :=
  fold_right (fun event n => fx_narrow_check_budget budget event + n) 0 events.

(** The actual full checker has rooted callback receipts and an independent input bound. *)
Definition fx_fullcheck_rooted_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A) m
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_fullcheck_rooted_laws EX L S source budget ->
    let '(out, events) := fx_fullcheck_counted EX L S m in
    exists bodies, fx_fullcheck_rooted_trace_source source events bodies /\
      out = check_post L S (lookup EX L m) /\
      fx_fullcheck_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_fullcheck_input_budget EX L S m + fx_fullcheck_rooted_external_budget budget events.
```

## Galois.Fixpoint.FixpointAuditContractClosures

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditContractClosures.v`.

```rocq
(** * Closed solver phase contract types

    These propositions quantify every parameter generalized by the original sections.
    For example, a local-solver erasure contract covers each actual scheduler and index.
    Builds on: the individual solver phase contract modules. *)
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointNested
  FixpointAuditWorklist FixpointAuditRecorded FixpointAuditLocalPartial FixpointAuditLocalClosure
  FixpointAuditCut FixpointAuditLocal FixpointAuditNarrowCheck FixpointAuditNarrow
  FixpointAuditNestedMachine.

(** Declared worklist claims quantify the actual strategy and static-system index. *)
Definition fx_declared_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_declared_model_erasure_statement X C A EX EC L sch mode S SS ix.

Definition run_worklist_declared_model_cost_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @run_worklist_declared_model_cost_statement X C A EX EC L sch mode S SS ix.

Definition fx_declared_total_engine_total_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_declared_total_engine_total_statement X C A EX EC L sch mode S SS ix.

Definition fx_declared_total_engine_erases_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_declared_total_engine_erases_statement X C A EX EC L sch mode S SS ix.

(** Recorded claims quantify the actual worklist parameters and source system. *)
Definition fx_recorded_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A), @fx_recorded_model_erasure_statement X C A EX EC L sch mode S.

Definition fx_recorded_model_cost_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A), @fx_recorded_model_cost_statement X C A EX EC L sch mode S.

Definition fx_recorded_successor_count_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A), @fx_recorded_successor_count_statement X C A EX EC L sch mode S.

(** Partial-check claims retain the actual explored set and assignment. *)
Definition fx_partial_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored values,
    @fx_partial_model_erasure_statement X C A EX L S SS ix explored values.

Definition fx_partial_model_cost_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored values,
    @fx_partial_model_cost_statement X C A EX EC L S SS ix explored values.

(** Closure and local-run claims retain the actual index and scheduler. *)
Definition fx_local_step_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) ix, @fx_local_step_erasure_statement X C A EX EC S SS ix.

Definition fx_local_walk_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) ix, @fx_local_walk_erasure_statement X C A EX EC S SS ix.

Definition fx_local_solve_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_local_solve_erasure_statement X C A EX EC L sch mode S SS ix.

Definition fx_local_checked_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_local_checked_erasure_statement X C A EX EC L sch mode S SS ix.

(** Cut, narrow and nested claims quantify their actual phase inputs. *)
Definition fx_cut_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix, @fx_cut_model_erasure_statement X C A EX L S SS ix.

Definition fx_narrow_checked_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix, @fx_narrow_checked_erasure_statement X C A EX L S SS ix.

Definition fx_nested_machine_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X C) mode
    (S : System.t X C A), @fx_nested_machine_erasure_statement X C A EX L plan mode S.

Definition fx_fullcheck_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A) values,
    @fx_fullcheck_erasure_statement X C A EX L S values.
```

## Galois.Fixpoint.FixpointAuditCut

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditCut.v`.

```rocq
(** * Counted cut-certificate expansion

    Each validation, query, contributor lookup and output write retains its concrete input,
    result and nested library execution. Builds on FixpointCut and the shared models. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCut.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditPrimitive.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.
Definition fx_cut_set_nested_work {X} (event : audit_set_event X (fx_encoder_entry X)) : nat :=
  match event with
  | AuditSetAdd _ _ _ _ enc trie | AuditSetRemove _ _ _ _ enc trie =>
      List.length enc + audit_trie_update_trace_source_work trie
  | AuditSetMem _ _ _ _ enc trie => List.length enc + audit_trie_get_trace_source_work trie
  | AuditSetFold _ _ => 0
  end.

Inductive fx_cut_event (X C A : Type) : Type :=
  | FxCutSetMem (x : X) (set : FinSet.t X) (out : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxCutSetAdd (x : X) (before after : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxCutMapGet (x : X) (code : positive) (before : assignment X A) (raw : option A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxCutMapSet (x : X) (value : A) (code : positive) (before after : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxCutIndexGet (x : X) (code : positive) (before : Map.t X (list C)) (raw : option (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FxCutElements (set : FinSet.t X) (items : list X) (body : list (audit_set_elements_event X))
  | FxCutQuery (body : audit_trace (fx_declared_call X C A))
  | FxCutRhs (c : C) (out : Query.t X A)
  | FxCutTarget (c : C) (out : X)
  | FxCutSides (c : C) (out : list X)
  | FxCutEqual (x y : X) (cx cy : positive) (out : bool) (body : list audit_positive_eqb_event)
  | FxCutJoin (lhs rhs out : A)
  | FxCutLeb (lhs rhs : A) (out : bool)
  | FxCutBool (lhs rhs out : bool)
  | FxCutCase (site : nat).
Arguments FxCutSetMem {X C A} _ _ _ _.
Arguments FxCutSetAdd {X C A} _ _ _ _.
Arguments FxCutMapGet {X C A} _ _ _ _ _.
Arguments FxCutMapSet {X C A} _ _ _ _ _ _.
Arguments FxCutIndexGet {X C A} _ _ _ _ _.
Arguments FxCutElements {X C A} _ _ _.
Arguments FxCutQuery {X C A} _.
Arguments FxCutRhs {X C A} _ _.
Arguments FxCutTarget {X C A} _ _.
Arguments FxCutSides {X C A} _ _.
Arguments FxCutEqual {X C A} _ _ _ _ _ _.
Arguments FxCutJoin {X C A} _ _ _.
Arguments FxCutLeb {X C A} _ _ _.
Arguments FxCutBool {X C A} _ _ _.
Arguments FxCutCase {X C A} _.

Section CutModel.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Definition fx_cut_map_mem (m : assignment X A) (x : X) : bool * list (fx_cut_event X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code m in
  (match raw with Some _ => true | None => false end, [FxCutMapGet x code m raw body; FxCutCase 0]).
Definition fx_cut_index_get (x : X) : list C * list (fx_cut_event X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code (contributors ix) in
  (match raw with Some cs => cs | None => [] end,
   [FxCutIndexGet x code (contributors ix) raw body; FxCutCase 1]).
Definition fx_cut_equal (x y : X) : bool * list (fx_cut_event X C A) :=
  let cx := encode EX x in
  let cy := encode EX y in
  let '(out, body) := audit_positive_eqb cx cy in
  (out, [FxCutEqual x y cx cy out body]).
Definition fx_cut_store (m : assignment X A) (x : X) (a : A) :
    assignment X A * list (fx_cut_event X C A) :=
  let code := encode EX x in
  let '(out, body) := audit_trie_set code (x, a) m in
  (out, [FxCutMapSet x a code m out body]).

Fixpoint fx_cut_seed (xs : list X) (stored_values : assignment X A) :
    assignment X A * list (fx_cut_event X C A) :=
  match xs with
  | [] => (Map.empty, [FxCutCase 2])
  | x :: rest =>
      let '(value, get_events) := @fx_model_lookup X C A EX L stored_values x in
      let '(before, tail) := fx_cut_seed rest stored_values in
      let '(out, set_events) := fx_cut_store before x value in
      (out, FxCutCase 2 :: FxCutQuery get_events :: tail ++ set_events)
  end.

Fixpoint fx_cut_prepare (xs : list X) (seen : FinSet.t X) :
    option (FinSet.t X) * list (fx_cut_event X C A) :=
  match xs with
  | [] => (Some seen, [FxCutCase 3])
  | x :: rest =>
      let '(present, mem_body) := audit_finset_mem (fx_index_encoder EX) x seen in
      let prefix := [FxCutCase 3; FxCutSetMem x seen present mem_body; FxCutCase 4] in
      if present then (None, prefix)
      else let '(next, add_body) := audit_finset_add (fx_index_encoder EX) x seen in
        let '(out, events) := fx_cut_prepare rest next in
        (out, prefix ++ FxCutSetAdd x seen next add_body :: events)
  end.

Fixpoint fx_cut_coverage_outputs (covered : FinSet.t X) (xs : list X) :
    bool * list (fx_cut_event X C A) :=
  match xs with
  | [] => (true, [FxCutCase 5])
  | x :: rest =>
      let '(head, body) := audit_finset_mem (fx_index_encoder EX) x covered in
      let '(tail, events) := fx_cut_coverage_outputs covered rest in
      (andb head tail, FxCutCase 5 :: FxCutSetMem x covered head body :: events ++
        [FxCutBool head tail (andb head tail)])
  end.
Fixpoint fx_cut_coverage_constraints (covered : FinSet.t X) (cs : list C) :
    bool * list (fx_cut_event X C A) :=
  match cs with
  | [] => (true, [FxCutCase 6])
  | c :: rest =>
      let target := System.target S c in
      let sides := side_targets SS c in
      let '(head, first) := fx_cut_coverage_outputs covered (target :: sides) in
      let '(tail, events) := fx_cut_coverage_constraints covered rest in
      (andb head tail, FxCutCase 6 :: FxCutTarget c target :: FxCutSides c sides ::
        first ++ events ++ [FxCutBool head tail (andb head tail)])
  end.
Definition fx_cut_ready (cur : assignment X A) (y : X) : bool * list (fx_cut_event X C A) :=
  let '(present, mem_events) := fx_cut_map_mem cur y in
  let '(contributors, index_events) := fx_cut_index_get y in
  let empty := match contributors with [] => true | _ :: _ => false end in
  (orb present empty, mem_events ++ index_events ++ [FxCutCase 7; FxCutBool present empty (orb
  present empty)]).
Fixpoint fx_cut_ready_all (cur : assignment X A) (reads : list X) :
    bool * list (fx_cut_event X C A) :=
  match reads with
  | [] => (true, [FxCutCase 8])
  | x :: rest =>
      let '(head, first) := fx_cut_ready cur x in
      let '(tail, events) := fx_cut_ready_all cur rest in
      (andb head tail, FxCutCase 8 :: first ++ events ++ [FxCutBool head tail (andb head tail)])
  end.
Fixpoint fx_cut_join (x : X) (updates : list (X * A)) (acc : A) :
    A * list (fx_cut_event X C A) :=
  match updates with
  | [] => (acc, [FxCutCase 9])
  | (y, value) :: rest =>
      let '(equal, eq_events) := fx_cut_equal x y in
      let next := if equal then join L acc value else acc in
      let branch := if equal then [FxCutJoin acc value next] else [] in
      let '(out, tail) := fx_cut_join x rest next in
      (out, FxCutCase 9 :: eq_events ++ FxCutCase 10 :: branch ++ tail)
  end.

Fixpoint fx_cut_gather (x : X) (cs : list C) (cur : assignment X A) (acc : A) :
    option A * list (fx_cut_event X C A) :=
  match cs with
  | [] => (Some acc, [FxCutCase 11])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs cur in
      let '(value, reads, sides) := answer in
      let '(ready, ready_events) := fx_cut_ready_all cur reads in
      let prefix := [FxCutCase 11; FxCutRhs c rhs; FxCutQuery query_events] ++
        ready_events ++ [FxCutCase 12] in
      if ready then
        let target := System.target S c in
        let '(next, join_events) := fx_cut_join x ((target, value) :: sides) acc in
        let '(out, events) := fx_cut_gather x rest cur next in
        (out, prefix ++ FxCutTarget c target :: join_events ++ events)
      else (None, prefix)
  end.

Fixpoint fx_cut_compute (xs : list X) (cur : assignment X A) :
    option (assignment X A) * list (fx_cut_event X C A) :=
  match xs with
  | [] => (Some cur, [FxCutCase 13])
  | x :: rest =>
      let '(present, mem_events) := fx_cut_map_mem cur x in
      let prefix := FxCutCase 13 :: mem_events ++ [FxCutCase 14] in
      if present then (None, prefix)
      else
        let '(cs, index_events) := fx_cut_index_get x in
        let '(value, gather_events) := fx_cut_gather x cs cur (bot L) in
        match value with
        | None => (None, prefix ++ index_events ++ gather_events ++ [FxCutCase 15])
        | Some a =>
            let '(next, write_events) := fx_cut_store cur x a in
            let '(out, later) := fx_cut_compute rest next in
            (out, prefix ++ index_events ++ gather_events ++ FxCutCase 15 :: write_events ++ later)
        end
  end.

Definition fx_cut_compare_value (m : assignment X A) (x y : X) (value : A) :
    bool * list (fx_cut_event X C A) :=
  let '(equal, eq_events) := fx_cut_equal x y in
  if equal then
    let '(old, read_events) := @fx_model_lookup X C A EX L m x in
    let le := leb L value old in
    (le, eq_events ++ [FxCutCase 16; FxCutQuery read_events; FxCutLeb value old le])
  else (true, eq_events ++ [FxCutCase 16]).
Fixpoint fx_cut_check_sides (m : assignment X A) (x : X) (sides : list (X * A)) :
    bool * list (fx_cut_event X C A) :=
  match sides with
  | [] => (true, [FxCutCase 17])
  | (y, value) :: rest =>
      let '(head, first) := fx_cut_compare_value m x y value in
      let '(tail, later) := fx_cut_check_sides m x rest in
      (andb head tail, FxCutCase 17 :: first ++ later ++ [FxCutBool head tail (andb head tail)])
  end.
Fixpoint fx_cut_check_constraints (m : assignment X A) (x : X) (cs : list C) :
    bool * list (fx_cut_event X C A) :=
  match cs with
  | [] => (true, [FxCutCase 18])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs m in
      let '(value, _, sides) := answer in
      let target := System.target S c in
      let '(head, compare_events) := fx_cut_compare_value m x target value in
      let '(side_ok, side_events) := fx_cut_check_sides m x sides in
      let current := andb head side_ok in
      let '(tail, later) := fx_cut_check_constraints m x rest in
      (andb current tail, FxCutCase 18 :: FxCutRhs c rhs :: FxCutQuery query_events ::
        FxCutTarget c target :: compare_events ++ side_events ++
        FxCutBool head side_ok current :: later ++ [FxCutBool current tail (andb current tail)])
  end.
Definition fx_cut_check_at (m : assignment X A) (x : X) : bool * list (fx_cut_event X C A) :=
  let '(cs, index_events) := fx_cut_index_get x in
  let '(out, events) := fx_cut_check_constraints m x cs in
  (out, index_events ++ events).
Fixpoint fx_cut_check_all (m : assignment X A) (xs : list X) : bool * list (fx_cut_event X C A) :=
  match xs with
  | [] => (true, [FxCutCase 19])
  | x :: rest =>
      let '(head, first) := fx_cut_check_at m x in
      let '(tail, events) := fx_cut_check_all m rest in
      (andb head tail, FxCutCase 19 :: first ++ events ++ [FxCutBool head tail (andb head tail)])
  end.

Definition fx_cut_expand_counted (cert : cut_certificate X A) :
    option (assignment X A) * list (fx_cut_event X C A) :=
  let '(covered, prepare_events) := fx_cut_prepare (plan cert) (cuts cert) in
  match covered with
  | None => (None, prepare_events ++ [FxCutCase 20])
  | Some cover =>
      let '(complete, coverage_events) := fx_cut_coverage_constraints cover (System.constraints S)
  in
      let prefix := prepare_events ++ FxCutCase 20 :: coverage_events ++ [FxCutCase 21] in
      if complete then
        let '(xs, elements_body) := audit_finset_elements (cuts cert) in
        let '(seed, seed_events) := fx_cut_seed xs (stored cert) in
        let '(computed, compute_events) := fx_cut_compute (plan cert) seed in
        let mid := prefix ++ FxCutElements (cuts cert) xs elements_body :: seed_events ++
          compute_events ++ [FxCutCase 22] in
        match computed with
        | None => (None, mid)
        | Some m =>
            let '(checks, check_elements) := audit_finset_elements (cuts cert) in
            let '(ok, check_events) := fx_cut_check_all m checks in
            (if ok then Some m else None,
             mid ++ FxCutElements (cuts cert) checks check_elements :: check_events ++ [FxCutCase
  23])
        end
      else (None, prefix)
  end.

Definition fx_cut_model_erasure_statement : Prop :=
  (forall xs m, fst (fx_cut_seed xs m) = cut_seed EX xs (lookup EX L m)) /\
  (forall xs seen, fst (fx_cut_prepare xs seen) = cut_prepare EX xs seen) /\
  (forall covered, fst (fx_cut_coverage_constraints covered (System.constraints S)) =
    cut_coverage EX S SS covered) /\
  (forall cur y, fst (fx_cut_ready cur y) = cut_ready EX ix cur y) /\
  (forall x ups a, fst (fx_cut_join x ups a) = cut_join EX L x ups a) /\
  (forall x cs cur a, fst (fx_cut_gather x cs cur a) = cut_gather EX L S ix x cs cur a) /\
  (forall xs cur, fst (fx_cut_compute xs cur) = cut_compute EX L S ix xs cur) /\
  (forall m x, fst (fx_cut_check_at m x) = cut_check_at EX L S ix m x) /\
  forall cert, fst (fx_cut_expand_counted cert) = expand EX L S SS ix cert.
End CutModel.

(** Selected fixed source-block allowances retain each nested primitive derivation. *)
Definition fx_cut_event_work {X C A} (EC : encoding C) (event : fx_cut_event X C A) : nat :=
  match event with
  | FxCutSetMem _ _ _ body | FxCutSetAdd _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxCutMapGet _ code _ _ body | FxCutIndexGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FxCutMapSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FxCutElements _ _ body => 1 + audit_set_elements_work body
  | FxCutQuery body => fx_declared_model_work EC body
  | FxCutEqual _ _ cx cy _ body =>
      audit_encoding_weight (Pos.size_nat cx) + audit_encoding_weight (Pos.size_nat cy) +
      audit_positive_eqb_source_work body
  | _ => 1
  end.
Definition fx_cut_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_cut_event X C A) : nat :=
  match event with
  | FxCutSetMem x _ _ _ => 12 + 5 * Pos.size_nat (encode EX x)
  | FxCutSetAdd x _ _ _ => 12 + 17 * Pos.size_nat (encode EX x)
  | FxCutMapGet _ code _ _ _ | FxCutIndexGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FxCutMapSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | FxCutElements set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxCutQuery events => audit_work events + fx_declared_primitive_budget EC events
  | FxCutEqual _ _ cx cy _ _ =>
      2 + Pos.size_nat cx + Pos.size_nat cy + 2 * Nat.min (Pos.size_nat cx) (Pos.size_nat cy)
  | _ => 1
  end.
Definition fx_cut_work {X C A} (EC : encoding C) (events : list (fx_cut_event X C A)) : nat :=
  fold_right (fun e n => fx_cut_event_work EC e + n) 0 events.
Definition fx_cut_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_cut_event X C A)) : nat :=
  fold_right (fun e n => fx_cut_event_budget EX EC e + n) 0 events.
Definition fx_cut_expand_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) cert,
    let '(result, events) := fx_cut_expand_counted EX L S SS ix cert in
    result = expand EX L S SS ix cert /\
    fx_cut_work EC events <= fx_cut_budget EX EC events.

(** Input-only recurrences are mathematical bounds, not part of the execution being charged. *)
Definition fx_cut_key_budget {X} (EX : encoding X) (x : X) : nat :=
  2 + 6 * Pos.size_nat (encode EX x).
Definition fx_cut_write_budget {X} (EX : encoding X) (x : X) : nat :=
  2 + 17 * Pos.size_nat (encode EX x).
Definition fx_cut_equal_budget {X} (EX : encoding X) (x y : X) : nat :=
  let cx := encode EX x in let cy := encode EX y in
  2 + Pos.size_nat cx + Pos.size_nat cy + 2 * Nat.min (Pos.size_nat cx) (Pos.size_nat cy).
Fixpoint fx_cut_seed_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 1 + (3 + 7 * Pos.size_nat (encode EX x)) +
      fx_cut_seed_budget EX rest + fx_cut_write_budget EX x
  end.
Fixpoint fx_cut_prepare_budget {X} (EX : encoding X) (xs : list X) (seen : FinSet.t X) : nat :=
  match xs with
  | [] => 1
  | x :: rest =>
      2 + (12 + 5 * Pos.size_nat (encode EX x)) +
      if FinSet.mem EX x seen then 0
      else 12 + 17 * Pos.size_nat (encode EX x) +
        fx_cut_prepare_budget EX rest (FinSet.add EX x seen)
  end.
Fixpoint fx_cut_coverage_outputs_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 2 + (12 + 5 * Pos.size_nat (encode EX x)) + fx_cut_coverage_outputs_budget EX rest
  end.
Fixpoint fx_cut_coverage_constraints_budget {X C A} (EX : encoding X)
    (S : System.t X C A) (SS : System.static S) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 4 + fx_cut_coverage_outputs_budget EX (System.target S c :: side_targets SS c) +
      fx_cut_coverage_constraints_budget EX S SS rest
  end.
Fixpoint fx_cut_ready_budget {X} (EX : encoding X) (reads : list X) : nat :=
  match reads with
  | [] => 1
  | x :: rest => 6 + 2 * fx_cut_key_budget EX x + fx_cut_ready_budget EX rest
  end.
Fixpoint fx_cut_join_budget {X A} (EX : encoding X) (x : X) (updates : list (X * A)) : nat :=
  match updates with
  | [] => 1
  | (y, _) :: rest => 3 + fx_cut_equal_budget EX x y + fx_cut_join_budget EX x rest
  end.
Fixpoint fx_cut_gather_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (x : X) (cs : list C)
    (cur : assignment X A) (acc : A) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, reads, sides) := Query.run rhs (lookup EX L cur) in
      3 + fx_fullcheck_query_input_budget EX L cur rhs + fx_cut_ready_budget EX reads +
      if forallb (cut_ready EX ix cur) reads then
        let updates := (System.target S c, value) :: sides in
        1 + fx_cut_join_budget EX x updates +
          fx_cut_gather_budget EX L S ix x rest cur (cut_join EX L x updates acc)
      else 0
  end.
Fixpoint fx_cut_compute_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (xs : list X) (cur : assignment X A) : nat :=
  match xs with
  | [] => 1
  | x :: rest =>
      3 + fx_cut_key_budget EX x +
      if Map.mem EX x cur then 0
      else let cs := contributors_of EX ix x in
        2 + fx_cut_key_budget EX x + fx_cut_gather_budget EX L S ix x cs cur (bot L) +
        match cut_gather EX L S ix x cs cur (bot L) with
        | None => 0
        | Some value => fx_cut_write_budget EX x +
            fx_cut_compute_budget EX L S ix rest (Map.set EX x value cur)
        end
  end.
Definition fx_cut_compare_budget {X} (EX : encoding X) (x y : X) : nat :=
  1 + fx_cut_equal_budget EX x y + (3 + 7 * Pos.size_nat (encode EX x)) + 1.
Fixpoint fx_cut_check_sides_budget {X A} (EX : encoding X) (x : X) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 1
  | (y, _) :: rest => 2 + fx_cut_compare_budget EX x y + fx_cut_check_sides_budget EX x rest
  end.
Fixpoint fx_cut_check_constraints_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (x : X) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(_, _, sides) := Query.run rhs (lookup EX L m) in
      5 + fx_fullcheck_query_input_budget EX L m rhs +
        fx_cut_compare_budget EX x (System.target S c) + fx_cut_check_sides_budget EX x sides +
        fx_cut_check_constraints_budget EX L S m x rest
  end.
Fixpoint fx_cut_check_all_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (m : assignment X A) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 3 + fx_cut_key_budget EX x +
      fx_cut_check_constraints_budget EX L S m x (contributors_of EX ix x) +
      fx_cut_check_all_budget EX L S ix m rest
  end.
Definition fx_cut_elements_budget {X} (set : FinSet.t X) : nat :=
  7 + 19 * audit_trie_nodes set + audit_trie_output_bits set.
Definition fx_cut_expand_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cert : cut_certificate X A) : nat :=
  fx_cut_prepare_budget EX (plan cert) (cuts cert) + 1 +
  match cut_prepare EX (plan cert) (cuts cert) with
  | None => 0
  | Some cover =>
      fx_cut_coverage_constraints_budget EX S SS (System.constraints S) + 1 +
      if cut_coverage EX S SS cover then
        let xs := FinSet.elements (cuts cert) in
        let seed := cut_seed EX xs (lookup EX L (stored cert)) in
        fx_cut_elements_budget (cuts cert) + fx_cut_seed_budget EX xs +
        fx_cut_compute_budget EX L S ix (plan cert) seed + 1 +
        match cut_compute EX L S ix (plan cert) seed with
        | None => 0
        | Some m => fx_cut_elements_budget (cuts cert) +
            fx_cut_check_all_budget EX L S ix m xs + 1
        end
      else 0
  end.
Definition fx_cut_expand_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) cert,
    let '(result, events) := fx_cut_expand_counted EX L S SS ix cert in
    result = expand EX L S SS ix cert /\
    fx_cut_work EC events <= fx_cut_expand_input_budget EX L S SS ix cert.
```

## Galois.Fixpoint.FixpointAuditCutCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditCutCallbacks.v`.

```rocq
(** Cut source receipts: exact same-run external callback and set-encoder bodies. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCut
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditCut.
Import List.ListNotations.
Definition fx_cut_set_entries {X} (events : list (audit_set_event X (fx_encoder_entry X))) : list
  (fx_encoder_entry X) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
      AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => [] end) events.
Definition fx_cut_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with FxEncodeEntry x code => fx_source_encode_x source x code body end.
Definition fx_cut_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (event : fx_cut_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxCutSetMem _ _ _ events | FxCutSetAdd _ _ _ events =>
      Forall2 (fx_cut_entry_source source) (fx_cut_set_entries events) bodies
  | FxCutMapGet x code _ _ _ | FxCutMapSet x _ code _ _ _ | FxCutIndexGet x code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxCutQuery events => exists groups, fx_declared_trace_source source events groups /\ bodies =
  concat groups
  | FxCutRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FxCutTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxCutSides c out => exists body, bodies = [body] /\ fxi_sides_source index_source c out body
  | FxCutEqual x y cx cy _ _ => exists first second, bodies = [first; second] /\
      fx_source_encode_x source x cx first /\ fx_source_encode_x source y cy second
  | FxCutJoin a b out => exists body, bodies = [body] /\ fx_source_join source a b out body
  | FxCutLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | _ => bodies = []
  end.
Definition fx_cut_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (events : list (fx_cut_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_cut_event_source source index_source) events bodies.
Definition fx_cut_source_laws {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fxi_sides_source index_source c (side_targets SS c) body) /\
  (forall (k : A -> Query.t X A) a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body).
Definition fx_cut_sides_bounded {X C B} (source : fx_index_external_source X C B)
    (ib : fx_index_external_budget X C B) (weight : B -> nat) : Prop :=
  forall c out body, fxi_sides_source source c out body ->
    fx_one_body_work weight body <= fxi_sides_bound ib c.
Definition fx_cut_event_external_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (event : fx_cut_event X C A) : nat :=
  match event with
  | FxCutSetMem _ _ _ events | FxCutSetAdd _ _ _ events =>
      fold_right (fun entry n => match entry with FxEncodeEntry x _ => fx_budget_encode_x wb x + n
  end)
        0 (fx_cut_set_entries events)
  | FxCutMapGet x _ _ _ _ | FxCutMapSet x _ _ _ _ _ | FxCutIndexGet x _ _ _ _ => fx_budget_encode_x
  wb x
  | FxCutQuery events => fx_declared_external_trace_budget wb events
  | FxCutRhs c _ => fx_budget_rhs wb c
  | FxCutTarget c _ => fx_budget_target wb c
  | FxCutSides c _ => fxi_sides_bound ib c
  | FxCutEqual x y _ _ _ _ => fx_budget_encode_x wb x + fx_budget_encode_x wb y
  | FxCutJoin a b _ => fx_budget_join wb a b
  | FxCutLeb a b _ => fx_budget_leb wb a b
  | _ => 0 end.
Definition fx_cut_external_trace_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (events : list (fx_cut_event X C A)) : nat :=
  fold_right (fun event n => fx_cut_event_external_budget wb ib event + n) 0 events.
Definition fx_cut_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix cert (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B),
    sys_index_laws EX S SS ix ->
    fx_cut_source_laws EX L S SS source index_source -> fx_declared_callback_bounded source wb ->
    fx_cut_sides_bounded index_source ib (fx_body_weight wb) ->
    let '(out, events) := fx_cut_expand_counted EX L S SS ix cert in
    exists bodies, fx_cut_trace_source source index_source events bodies /\
      out = expand EX L S SS ix cert /\
      fx_cut_work EC events + fx_declared_body_work (fx_body_weight wb) bodies <=
        fx_cut_expand_input_budget EX L S SS ix cert + fx_cut_external_trace_budget wb ib events.
```

## Galois.Fixpoint.FixpointAuditFallback

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditFallback.v`.

```rocq
(** * Fixed-fuel solver fallback and closure use

    Construction retains the actual solver run and the selected result or top branch.
    For example, evaluating a successful returned closure incurs its own lookup work.
    Builds on: FixpointAuditRecorded and FixpointAuditNested. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditCost.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditRecorded
  FixpointAuditRecordedBudget FixpointAuditNested.
Import List.ListNotations.

Inductive fx_fallback_event (X C A B : Type) : Type :=
  | FxFallbackRecorded (body : list (fx_recorded_event X C A))
  | FxFallbackNested (body : list (fx_nested_whole_event X C A B))
  | FxFallbackCase (is_result : bool).
Arguments FxFallbackRecorded {X C A B} _.
Arguments FxFallbackNested {X C A B} _.
Arguments FxFallbackCase {X C A B} _.

Definition fx_fallback_result {X A} (EX : encoding X) (L : lattice A) (T : top L)
    (result : option (assignment X A)) : X -> A :=
  match result with
  | Some values => lookup EX L values
  | None => fun _ => top_value T
  end.

Definition fx_recorded_fallback_counted {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (fuel : positive) : option (assignment X A) * list (fx_fallback_event X C A B) :=
  let '(out, events) := run_worklist_recorded_model EX EC L sch mode S fuel in
  (out, [FxFallbackRecorded events; FxFallbackCase (match out with Some _ => true | None =>
  false end)]).

Definition fx_nested_fallback_counted {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (fuel : positive) :
    option (assignment X A) * list (fx_fallback_event X C A B) :=
  let '(out, events) := fx_nested_run_counted EX L mode S SS cb fuel in
  (out, [FxFallbackNested events; FxFallbackCase (match out with Some _ => true | None => false
  end)]).

(** Construction preserves both original proof-erased fallback functions pointwise. *)
Definition fx_fallback_erasure_statement : Prop :=
  (forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (T : top L) (sch : scheduler X) mode (S : System.t X C A) fuel x,
    fx_fallback_result EX L T (fst (@fx_recorded_fallback_counted X C A B EX EC L sch mode S
  fuel)) x =
      proj1_sig (solve_fuel EX EC L HL T sch mode S fuel) x) /\
  (forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (T : top L) mode (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) fuel x,
    fx_index_external_erases EX S SS cb ->
    fx_fallback_result EX L T (fst (fx_nested_fallback_counted EX L mode S SS cb fuel)) x =
      proj1_sig (nested_solve_fuel EX EC L HL T mode S SS fuel) x).

Definition fx_fallback_event_work {X C A B} (EC : encoding C)
    (ib : fx_index_external_budget X C B) (event : fx_fallback_event X C A B) : nat :=
  match event with
  | FxFallbackRecorded events => fx_recorded_work EC events
  | FxFallbackNested events => fx_nested_whole_work EC ib events
  | FxFallbackCase _ => 1
  end.

Definition fx_fallback_work {X C A B} (EC : encoding C) (ib : fx_index_external_budget X C B)
    (events : list (fx_fallback_event X C A B)) : nat :=
  fold_right (fun event n => fx_fallback_event_work EC ib event + n) 0 events.

(** Construction budgets exclude later applications of the returned function. *)
Definition fx_recorded_fallback_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) (ib : fx_index_external_budget X C B) fuel,
    let '(out, events) := @fx_recorded_fallback_counted X C A B EX EC L sch mode S fuel in
    out = run_worklist EX EC L sch mode S Recorded fuel /\
    fx_fallback_work EC ib events <= fx_recorded_run_input_budget EX EC L sch mode S fuel + 1.

(** Nested construction uses its graph, WTO, plan and machine allowance. *)
Definition fx_nested_fallback_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(out, events) := fx_nested_fallback_counted EX L mode S SS cb fuel in
    out = nested_run EX EC L mode S SS fuel /\
    fx_fallback_work EC ib events <= fx_nested_run_input_budget EX L mode S SS ib fuel + 1.

(** Applying a returned closure performs the actual lookup or top branch once. *)
Definition fx_fallback_apply_counted {X C A} (EX : encoding X) (L : lattice A) (T : top L)
    (result : option (assignment X A)) (x : X) : A * audit_trace (fx_declared_call X C A) :=
  match result with
  | Some values => fx_model_lookup EX L values x
  | None => (top_value T, [AuditCase 0 []])
  end.

(** The application boundary is separate from solver construction. *)
Definition fx_fallback_apply_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (T : top L) result x,
    let '(out, events) := @fx_fallback_apply_counted X C A EX L T result x in
    out = fx_fallback_result EX L T result x /\
    fx_declared_model_work EC events <= 1 + fx_fullcheck_lookup_input_budget EX x.
```

## Galois.Fixpoint.FixpointAuditFallbackCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditFallbackCallbacks.v`.

```rocq
(** * Fallback callback receipts

    Fallback construction retains the actual recorded or nested solver callback bodies.
    For example, exhaustion selects top without performing a later lookup.
    Builds on: FixpointAuditFallback and the recorded and nested source adapters. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks FixpointAuditRecordedBudget FixpointAuditRecordedCallbacks
  FixpointAuditNested FixpointAuditScheduleWrapper FixpointAuditNestedCallbacks
  FixpointAuditFallback.
Import List.ListNotations.

Definition fx_fallback_event_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_fallback_event X C A B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxFallbackRecorded events => exists groups,
      fx_recorded_trace_source source events groups /\ bodies = concat groups
  | FxFallbackNested events => exists groups,
      fx_nested_trace_source index_source source events groups /\ bodies = concat groups
  | FxFallbackCase _ => bodies = []
  end.

Definition fx_fallback_trace_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (events : list (fx_fallback_event X C A B))
    (bodies : list (list (list D))) : Prop :=
  Forall2 (fx_fallback_event_source index_source source) events bodies.

Definition fx_fallback_external_trace_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (events : list (fx_fallback_event X C A B)) :
  nat :=
  fold_right (fun event total => total + match event with
    | FxFallbackRecorded nested => fx_recorded_external_trace_budget budget nested
    | FxFallbackNested nested => fx_nested_external_trace_budget budget nested
    | FxFallbackCase _ => 0
    end) 0 events.

(** Recorded construction has the same-run callback receipts and per-call body allowance. *)
Definition fx_recorded_fallback_external_source_statement : Prop :=
  forall X C A B D (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) (ib : fx_index_external_budget X C B) fuel
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D),
    fx_declared_source_laws EX EC L sch S source -> fx_declared_callback_bounded source budget ->
    let '(out, events) := @fx_recorded_fallback_counted X C A B EX EC L sch mode S fuel in
    exists bodies, fx_fallback_trace_source index_source source events bodies /\
      out = run_worklist EX EC L sch mode S Recorded fuel /\
      fx_fallback_work EC ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_recorded_run_input_budget EX EC L sch mode S fuel + 1 +
          fx_fallback_external_trace_budget budget events.

(** Nested construction includes the actual indexed graph and solver callback source bodies. *)
Definition fx_nested_fallback_external_source_statement : Prop :=
  forall X C A B D (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_nested_fallback_counted EX L mode S SS cb fuel in
    exists bodies, fx_fallback_trace_source index_source source events bodies /\
      out = nested_run EX EC L mode S SS fuel /\
      fx_fallback_work EC ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_nested_run_input_budget EX L mode S SS ib fuel + 1 +
          fx_fallback_external_trace_budget budget events.

(** A later closure application retains its own encoder body, separately from construction. *)
Definition fx_fallback_apply_external_source_statement : Prop :=
  forall X C A D (EX : encoding X) (EC : encoding C) (L : lattice A) (T : top L)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    result x,
    (forall key, exists body, fx_source_encode_x source key (encode EX key) body) ->
    (forall key out body, fx_source_encode_x source key out body ->
      fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget key) ->
    let '(out, events) := @fx_fallback_apply_counted X C A EX L T result x in
    exists bodies, fx_declared_trace_source source events bodies /\
      out = fx_fallback_result EX L T result x /\
      fx_declared_model_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        1 + fx_fullcheck_lookup_input_budget EX x + fx_declared_external_trace_budget budget events.
```

## Galois.Fixpoint.FixpointAuditFullCheck

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditFullCheck.v`.

```rocq
(** * Full checker with explicit external callback bodies

    Every callback is invoked once at the real source call, and its body observations are
    retained inside that same event. Only externally supplied functions use these adapters;
    concrete internally constructed callbacks must instantiate their literal models.
    Builds on FixpointCheck and the frozen shared trie model. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

Record fx_check_external_model (X C A B : Type) : Type := FxCheckExternalModel {
  fx_check_encode_model : X -> positive * list B;
  fx_check_rhs_model : C -> Query.t X A * list B;
  fx_check_target_model : C -> X * list B;
  fx_check_continue_model : (A -> Query.t X A) -> A -> Query.t X A * list B;
  fx_check_leb_model : A -> A -> bool * list B
}.
Arguments fx_check_encode_model {X C A B} _ _.
Arguments fx_check_rhs_model {X C A B} _ _.
Arguments fx_check_target_model {X C A B} _ _.
Arguments fx_check_continue_model {X C A B} _ _ _.
Arguments fx_check_leb_model {X C A B} _ _ _.

Definition fx_check_external_erases {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (cb : fx_check_external_model X C A B) : Prop :=
  (forall x, fst (fx_check_encode_model cb x) = encode EX x) /\
  (forall c, fst (fx_check_rhs_model cb c) = System.rhs S c) /\
  (forall c, fst (fx_check_target_model cb c) = System.target S c) /\
  (forall k a, fst (fx_check_continue_model cb k a) = k a) /\
  (forall a b, fst (fx_check_leb_model cb a b) = leb L a b).

Inductive fx_check_nested_event (X C A B : Type) : Type :=
  | FcnGet (x : X) (code : positive) (input : assignment X A) (raw : option A)
      (encode_body : list B) (trie_body : audit_trace (audit_trie_call (X * A)))
  | FcnRhs (c : C) (out : Query.t X A) (body : list B)
  | FcnTarget (c : C) (out : X) (body : list B)
  | FcnContinue (k : A -> Query.t X A) (value : A) (out : Query.t X A) (body : list B)
  | FcnLeb (lhs rhs : A) (out : bool) (body : list B)
  | FcnCase (site : nat).
Arguments FcnGet {X C A B} _ _ _ _ _ _.
Arguments FcnRhs {X C A B} _ _ _.
Arguments FcnTarget {X C A B} _ _ _.
Arguments FcnContinue {X C A B} _ _ _ _.
Arguments FcnLeb {X C A B} _ _ _ _.
Arguments FcnCase {X C A B} _.

Section NestedCheck.
Context {X C A B : Type} (L : lattice A) (S : System.t X C A) (m : assignment X A)
  (cb : fx_check_external_model X C A B).
Definition fcn_lookup (x : X) : A * list (fx_check_nested_event X C A B) :=
  let '(code, enc_body) := fx_check_encode_model cb x in
  let '(raw, trie_body) := audit_map_code_get code m in
  (match raw with Some value => value | None => bot L end,
   [FcnGet x code m raw enc_body trie_body; FcnCase 0]).
Inductive fcn_query_run : Query.t X A -> (A * list X * list (X * A)) ->
    list (fx_check_nested_event X C A B) -> Prop :=
  | FcnQueryRet : forall a, fcn_query_run (Query.Ret a) (a, [], []) [FcnCase 1]
  | FcnQueryAsk : forall x k value read_events next cont_body out reads sides later,
      fcn_lookup x = (value, read_events) ->
      fx_check_continue_model cb k value = (next, cont_body) ->
      fcn_query_run next (out, reads, sides) later ->
      fcn_query_run (Query.Ask x k) (out, x :: reads, sides)
        (FcnCase 1 :: read_events ++ FcnContinue k value next cont_body :: later ++ [FcnCase 2])
  | FcnQuerySide : forall x a next out reads sides later,
      fcn_query_run next (out, reads, sides) later ->
      fcn_query_run (Query.Side x a next) (out, reads, (x, a) :: sides)
        (FcnCase 1 :: later ++ [FcnCase 3]).
Fixpoint fcn_sides (sides : list (X * A)) : bool * list (fx_check_nested_event X C A B) :=
  match sides with
  | [] => (true, [FcnCase 4])
  | (x, value) :: rest =>
      let '(old, lookup_events) := fcn_lookup x in
      let '(head, leb_body) := fx_check_leb_model cb value old in
      let '(tail, later) := fcn_sides rest in
      (andb head tail, FcnCase 4 :: lookup_events ++ FcnLeb value old head leb_body ::
        later ++ [FcnCase 5])
  end.
Inductive fcn_constraints_run : list C -> bool -> list (fx_check_nested_event X C A B) -> Prop :=
  | FcnConstraintsNil : fcn_constraints_run [] true [FcnCase 6]
  | FcnConstraintsCons : forall c rest rhs rhs_body value reads sides query_events
      target target_body old lookup_events direct leb_body side_ok side_events tail later,
      fx_check_rhs_model cb c = (rhs, rhs_body) ->
      fcn_query_run rhs (value, reads, sides) query_events ->
      fx_check_target_model cb c = (target, target_body) ->
      fcn_lookup target = (old, lookup_events) ->
      fx_check_leb_model cb value old = (direct, leb_body) ->
      fcn_sides sides = (side_ok, side_events) ->
      fcn_constraints_run rest tail later ->
      fcn_constraints_run (c :: rest) (andb (andb direct side_ok) tail)
        (FcnCase 6 :: FcnRhs c rhs rhs_body :: query_events ++
          FcnTarget c target target_body :: lookup_events ++ FcnLeb value old direct leb_body ::
          side_events ++ FcnCase 7 :: later ++ [FcnCase 8]).
Definition fx_fullcheck_nested_run := fcn_constraints_run (System.constraints S).
End NestedCheck.

Definition fx_fullcheck_nested_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> forall out events,
    fx_fullcheck_nested_run L S m cb out events -> out = check_post L S (lookup EX L m).

Definition fx_fullcheck_nested_total_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> exists out events, fx_fullcheck_nested_run L S m cb
  out events.

(** These interfaces describe individual genuinely external callbacks, never a whole-check
    budget premise. Each client must prove its concrete callback-body source adequacy. *)
Record fx_check_external_budget (X C A B : Type) : Type := FxCheckExternalBudget {
  fx_check_body_weight : B -> nat;
  fx_check_encode_bound : X -> nat;
  fx_check_rhs_bound : C -> nat;
  fx_check_target_bound : C -> nat;
  fx_check_continue_bound : (A -> Query.t X A) -> A -> nat;
  fx_check_leb_bound : A -> A -> nat
}.
Arguments fx_check_body_weight {X C A B} _ _.
Arguments fx_check_encode_bound {X C A B} _ _.
Arguments fx_check_rhs_bound {X C A B} _ _.
Arguments fx_check_target_bound {X C A B} _ _.
Arguments fx_check_continue_bound {X C A B} _ _ _.
Arguments fx_check_leb_bound {X C A B} _ _ _.
Definition fx_check_body_work {X C A B} (budget : fx_check_external_budget X C A B)
    (body : list B) : nat := fold_right (fun e n => fx_check_body_weight budget e + n) 0 body.
Definition fx_check_external_bounded {X C A B} (cb : fx_check_external_model X C A B)
    (budget : fx_check_external_budget X C A B) : Prop :=
  (forall b, 1 <= fx_check_body_weight budget b) /\
  (forall x, fx_check_body_work budget (snd (fx_check_encode_model cb x)) <=
  fx_check_encode_bound budget x) /\
  (forall c, fx_check_body_work budget (snd (fx_check_rhs_model cb c)) <= fx_check_rhs_bound
  budget c) /\
  (forall c, fx_check_body_work budget (snd (fx_check_target_model cb c)) <=
  fx_check_target_bound budget c) /\
  (forall k a, fx_check_body_work budget (snd (fx_check_continue_model cb k a)) <=
    fx_check_continue_bound budget k a) /\
  (forall a b, fx_check_body_work budget (snd (fx_check_leb_model cb a b)) <= fx_check_leb_bound
  budget a b).

Definition fx_check_nested_event_work {X C A B} (budget : fx_check_external_budget X C A B)
    (event : fx_check_nested_event X C A B) : nat :=
  match event with
  | FcnGet _ _ _ _ enc_body trie_body =>
      8 + fx_check_body_work budget enc_body + audit_trie_get_trace_source_work trie_body
  | FcnRhs _ _ body | FcnTarget _ _ body | FcnContinue _ _ _ body | FcnLeb _ _ _ body =>
      3 + fx_check_body_work budget body
  | FcnCase _ => 3
  end.
Definition fx_check_nested_work {X C A B} (budget : fx_check_external_budget X C A B)
    (events : list (fx_check_nested_event X C A B)) : nat :=
  fold_right (fun e n => fx_check_nested_event_work budget e + n) 0 events.
Definition fx_check_nested_lookup_budget {X C A B} (EX : encoding X)
    (budget : fx_check_external_budget X C A B) (x : X) : nat :=
  11 + fx_check_encode_bound budget x + 5 * Pos.size_nat (encode EX x).
Fixpoint fx_check_nested_query_budget {X C A B} (EX : encoding X) (L : lattice A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (q : Query.t X A) : nat :=
  match q with
  | Query.Ret _ => 3
  | Query.Ask x k =>
      let value := lookup EX L m x in
      9 + fx_check_nested_lookup_budget EX budget x + fx_check_continue_bound budget k value +
        fx_check_nested_query_budget EX L budget m (k value)
  | Query.Side _ _ next => 6 + fx_check_nested_query_budget EX L budget m next
  end.
Fixpoint fx_check_nested_sides_budget {X C A B} (EX : encoding X) (L : lattice A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 3
  | (x, value) :: rest =>
      9 + fx_check_nested_lookup_budget EX budget x +
      fx_check_leb_bound budget value (lookup EX L m x) +
      fx_check_nested_sides_budget EX L budget m rest
  end.
Fixpoint fx_check_nested_constraints_budget {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (budget : fx_check_external_budget X C A B)
    (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 3
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L m) in
      let target := System.target S c in
      18 + fx_check_rhs_bound budget c + fx_check_nested_query_budget EX L budget m rhs +
      fx_check_target_bound budget c + fx_check_nested_lookup_budget EX budget target +
      fx_check_leb_bound budget value (lookup EX L m target) +
      fx_check_nested_sides_budget EX L budget m sides +
      fx_check_nested_constraints_budget EX L S budget m rest
  end.
Definition fx_fullcheck_nested_input_budget {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (budget : fx_check_external_budget X C A B) (m : assignment X A) : nat :=
  fx_check_nested_constraints_budget EX L S budget m (System.constraints S).
Definition fx_fullcheck_nested_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B) (budget : fx_check_external_budget X C A B),
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_fullcheck_nested_run L S m cb out events ->
    out = check_post L S (lookup EX L m) /\
    fx_check_nested_work budget events <= fx_fullcheck_nested_input_budget EX L S budget m.

(** A client supplies source relations only for its external callback bodies. They are not
    relations for the checker or its total cost. The client must define and prove the actual
    source rules for these relations before using this adapter as implementation adequacy. *)
Record fx_check_external_source (X C A B : Type) : Type := FxCheckExternalSource {
  fx_check_encode_source : X -> positive -> list B -> Prop;
  fx_check_rhs_source : C -> Query.t X A -> list B -> Prop;
  fx_check_target_source : C -> X -> list B -> Prop;
  fx_check_continue_source : (A -> Query.t X A) -> A -> Query.t X A -> list B -> Prop;
  fx_check_leb_source : A -> A -> bool -> list B -> Prop
}.
Arguments fx_check_encode_source {X C A B} _ _ _ _.
Arguments fx_check_rhs_source {X C A B} _ _ _ _.
Arguments fx_check_target_source {X C A B} _ _ _ _.
Arguments fx_check_continue_source {X C A B} _ _ _ _ _.
Arguments fx_check_leb_source {X C A B} _ _ _ _ _.
Definition fx_check_external_source_adequacy {X C A B}
    (source : fx_check_external_source X C A B) (cb : fx_check_external_model X C A B) : Prop :=
  (forall x, let '(out, body) := fx_check_encode_model cb x in fx_check_encode_source source x
  out body) /\
  (forall c, let '(out, body) := fx_check_rhs_model cb c in fx_check_rhs_source source c out
  body) /\
  (forall c, let '(out, body) := fx_check_target_model cb c in fx_check_target_source source c
  out body) /\
  (forall k a, let '(out, body) := fx_check_continue_model cb k a in
    fx_check_continue_source source k a out body) /\
  (forall a b, let '(out, body) := fx_check_leb_model cb a b in fx_check_leb_source source a b
  out body).

(** Trace-local adequacy asks the client only for callbacks actually invoked by this run.
    Its source relations are individual callback rules, never a whole-check cost law. *)
Definition fx_check_external_trace_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (events : list (fx_check_nested_event X C A B)) : Prop :=
  Forall (fun e => match e with
    | FcnGet x code _ _ body _ => fx_check_encode_source source x code body
    | FcnRhs c out body => fx_check_rhs_source source c out body
    | FcnTarget c out body => fx_check_target_source source c out body
    | FcnContinue k value out body => fx_check_continue_source source k value out body
    | FcnLeb lhs rhs out body => fx_check_leb_source source lhs rhs out body
    | FcnCase _ => True
    end) events.
Definition fx_fullcheck_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B) (budget : fx_check_external_budget X C A B)
    (source : fx_check_external_source X C A B),
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_fullcheck_nested_run L S m cb out events -> fx_check_external_trace_adequacy source events ->
    out = check_post L S (lookup EX L m) /\
    fx_check_nested_work budget events <= fx_fullcheck_nested_input_budget EX L S budget m.
```

## Galois.Fixpoint.FixpointAuditIndex

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditIndex.v`.

```rocq
(** * Indexed preparation with same-call callback bodies

    Each target, side, dependency and encoder model executes at its actual source site.
    The same intermediate sets, enumerations and maps feed the final index.
    Builds on FixpointIndex and the frozen collection source models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditElements.
Import List.ListNotations.

Record fx_index_external_model (X C B : Type) : Type := FxIndexExternalModel {
  fxi_encode : X -> positive * list B;
  fxi_target : C -> X * list B;
  fxi_sides : C -> list X * list B;
  fxi_deps : C -> list X * list B
}.
Arguments fxi_encode {X C B} _ _.
Arguments fxi_target {X C B} _ _.
Arguments fxi_sides {X C B} _ _.
Arguments fxi_deps {X C B} _ _.
Definition fx_index_external_erases {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) : Prop :=
  (forall x, fst (fxi_encode cb x) = encode EX x) /\
  (forall c, fst (fxi_target cb c) = System.target S c) /\
  (forall c, fst (fxi_sides cb c) = side_targets SS c) /\
  (forall c, fst (fxi_deps cb c) = deps SS c).

Inductive fx_index_nested_event (X C B : Type) : Type :=
  | FxiTarget (c : C) (out : X) (body : list B)
  | FxiSides (c : C) (out : list X) (body : list B)
  | FxiDeps (c : C) (out : list X) (body : list B)
  | FxiDistinctBuild (input : list X) (set : FinSet.t X) (body : list (audit_set_event X B))
  | FxiDistinctElements (set : FinSet.t X) (output : list X) (body : list (audit_set_elements_event
  X))
  | FxiRead (x : X) (code : positive) (input : Map.t X (list C)) (raw : option (list C))
      (encode_body : list B) (trie_body : audit_trace (audit_trie_call (X * list C)))
  | FxiWrite (x : X) (code : positive) (value : list C) (before after : Map.t X (list C))
      (encode_body : list B) (trie_body : audit_trace (audit_trie_call (X * list C)))
  | FxiCase (site : nat).
Arguments FxiTarget {X C B} _ _ _.
Arguments FxiSides {X C B} _ _ _.
Arguments FxiDeps {X C B} _ _ _.
Arguments FxiDistinctBuild {X C B} _ _ _.
Arguments FxiDistinctElements {X C B} _ _ _.
Arguments FxiRead {X C B} _ _ _ _ _ _.
Arguments FxiWrite {X C B} _ _ _ _ _ _ _.
Arguments FxiCase {X C B} _.

Definition fxi_distinct_counted {X C B} (cb : fx_index_external_model X C B) (input : list X) :
    list X * list (fx_index_nested_event X C B) :=
  let '(set, build) := audit_finset_of_list (fxi_encode cb) input in
  let '(output, elements) := audit_finset_elements set in
  (output, [FxiDistinctBuild input set build; FxiDistinctElements set output elements]).
Fixpoint fxi_push_many {X C B} (cb : fx_index_external_model X C B) (c : C)
    (xs : list X) (m : Map.t X (list C)) : Map.t X (list C) * list (fx_index_nested_event X C B) :=
  match xs with
  | [] => (m, [FxiCase 0])
  | x :: rest =>
      let '(before, tail) := fxi_push_many cb c rest m in
      let '(read_code, read_body) := fxi_encode cb x in
      let '(raw, get_body) := audit_map_code_get read_code before in
      let prior := match raw with Some values => values | None => [] end in
      let value := c :: prior in
      let '(write_code, write_body) := fxi_encode cb x in
      let '(after, set_body) := audit_trie_set write_code (x, value) before in
      (after, FxiCase 0 :: tail ++ [FxiRead x read_code before raw read_body get_body;
        FxiCase 1; FxiWrite x write_code value before after write_body set_body])
  end.
Fixpoint fxi_fold {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    sys_index X C * list (fx_index_nested_event X C B) :=
  match cs with
  | [] => (SysIndex Map.empty Map.empty, [FxiCase 2])
  | c :: rest =>
      let '(ix, tail) := fxi_fold cb rest in
      let '(target, target_body) := fxi_target cb c in
      let '(sides, sides_body) := fxi_sides cb c in
      let '(outputs, output_events) := fxi_distinct_counted cb (target :: sides) in
      let '(contributors_map, contributor_events) := fxi_push_many cb c outputs (contributors ix) in
      let '(deps, deps_body) := fxi_deps cb c in
      let '(reads, read_events) := fxi_distinct_counted cb deps in
      let '(readers_map, reader_events) := fxi_push_many cb c reads (readers ix) in
      (SysIndex contributors_map readers_map, FxiCase 2 :: tail ++
        [FxiTarget c target target_body; FxiSides c sides sides_body] ++ output_events ++
        contributor_events ++ FxiDeps c deps deps_body :: read_events ++ reader_events)
  end.
Definition fx_index_nested_counted {X C A B} (S : System.t X C A)
    (cb : fx_index_external_model X C B) := fxi_fold cb (System.constraints S).
Definition fx_index_nested_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    fst (fx_index_nested_counted S cb) = index_system EX S SS.

(** Budgets concern each external callback body separately; no whole-index bound is assumed. *)
Record fx_index_external_budget (X C B : Type) : Type := FxIndexExternalBudget {
  fxi_body_weight : B -> nat;
  fxi_encode_bound : X -> nat;
  fxi_target_bound : C -> nat;
  fxi_sides_bound : C -> nat;
  fxi_deps_bound : C -> nat
}.
Arguments fxi_body_weight {X C B} _ _.
Arguments fxi_encode_bound {X C B} _ _.
Arguments fxi_target_bound {X C B} _ _.
Arguments fxi_sides_bound {X C B} _ _.
Arguments fxi_deps_bound {X C B} _ _.
Definition fxi_body_work {X C B} (budget : fx_index_external_budget X C B) (body : list B) : nat :=
  fold_right (fun event n => fxi_body_weight budget event + n) 0 body.
Definition fx_index_external_bounded {X C B} (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) : Prop :=
  (forall b, 1 <= fxi_body_weight budget b) /\
  (forall x, fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x) /\
  (forall c, fxi_body_work budget (snd (fxi_target cb c)) <= fxi_target_bound budget c) /\
  (forall c, fxi_body_work budget (snd (fxi_sides cb c)) <= fxi_sides_bound budget c) /\
  (forall c, fxi_body_work budget (snd (fxi_deps cb c)) <= fxi_deps_bound budget c).
Definition fxi_event_work {X C B} (budget : fx_index_external_budget X C B)
    (event : fx_index_nested_event X C B) : nat :=
  match event with
  | FxiTarget _ _ body | FxiSides _ _ body | FxiDeps _ _ body => 3 + fxi_body_work budget body
  | FxiDistinctBuild _ _ body => 3 + audit_finset_source_work (fxi_body_work budget) body
  | FxiDistinctElements _ _ body => 3 + audit_set_elements_work body
  | FxiRead _ _ _ _ enc trie => 8 + fxi_body_work budget enc + audit_trie_get_trace_source_work trie
  | FxiWrite _ _ _ _ _ enc trie => 8 + fxi_body_work budget enc +
  audit_trie_update_trace_source_work trie
  | FxiCase _ => 3
  end.
Definition fx_index_adapter_work {X C B} (budget : fx_index_external_budget X C B)
    (events : list (fx_index_nested_event X C B)) : nat :=
  fold_right (fun event n => fxi_event_work budget event + n) 0 events.
Fixpoint fxi_set_input_budget {X C B} (EX : encoding X) (budget : fx_index_external_budget X C B)
    (input : list X) : nat :=
  match input with
  | [] => 1
  | x :: rest => 3 + fxi_encode_bound budget x + 16 * Pos.size_nat (encode EX x) +
      fxi_set_input_budget EX budget rest
  end.
Definition fxi_distinct_input_budget {X C B} (EX : encoding X)
    (budget : fx_index_external_budget X C B) (input : list X) : nat :=
  let set := FinSet.of_list EX input in
  12 + fxi_set_input_budget EX budget input + 19 * audit_trie_nodes set + audit_trie_output_bits
  set.
Fixpoint fxi_push_input_budget {X C B} (EX : encoding X) (budget : fx_index_external_budget X C B)
    (keys : list X) : nat :=
  match keys with
  | [] => 3
  | x :: rest => 22 + 2 * fxi_encode_bound budget x + 21 * Pos.size_nat (encode EX x) +
      fxi_push_input_budget EX budget rest
  end.
Fixpoint fxi_constraints_input_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (budget : fx_index_external_budget X C B) (cs : list C) : nat :=
  match cs with
  | [] => 3
  | c :: rest =>
      let outputs := System.target S c :: side_targets SS c in
      let reads := deps SS c in
      12 + fxi_target_bound budget c + fxi_sides_bound budget c + fxi_deps_bound budget c +
      fxi_distinct_input_budget EX budget outputs + fxi_push_input_budget EX budget
  (distinct_unknowns EX outputs) +
      fxi_distinct_input_budget EX budget reads + fxi_push_input_budget EX budget (distinct_unknowns
  EX reads) +
      fxi_constraints_input_budget EX S SS budget rest
  end.
Definition fx_index_nested_input_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (budget : fx_index_external_budget X C B) : nat :=
  fxi_constraints_input_budget EX S SS budget (System.constraints S).
Definition fx_index_nested_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (budget : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb budget ->
    let '(result, events) := fx_index_nested_counted S cb in
    result = index_system EX S SS /\
    fx_index_adapter_work budget events <= fx_index_nested_input_budget EX S SS budget.

(** Only individual external callback source relations are supplied by a concrete client.
    Internal set, enumeration and trie bodies are the shared fixed collection models. *)
Record fx_index_external_source (X C B : Type) : Type := FxIndexExternalSource {
  fxi_encode_source : X -> positive -> list B -> Prop;
  fxi_target_source : C -> X -> list B -> Prop;
  fxi_sides_source : C -> list X -> list B -> Prop;
  fxi_deps_source : C -> list X -> list B -> Prop
}.
Arguments fxi_encode_source {X C B} _ _ _ _.
Arguments fxi_target_source {X C B} _ _ _ _.
Arguments fxi_sides_source {X C B} _ _ _ _.
Arguments fxi_deps_source {X C B} _ _ _ _.
Definition fxi_set_external_adequacy {X C B} (source : fx_index_external_source X C B)
    (events : list (audit_set_event X B)) : Prop :=
  Forall (fun e => match e with
    | AuditSetAdd x code _ _ body _ | AuditSetMem x code _ _ body _ |
      AuditSetRemove x code _ _ body _ => fxi_encode_source source x code body
    | AuditSetFold _ _ => True
    end) events.
Definition fx_index_external_trace_adequacy {X C B} (source : fx_index_external_source X C B)
    (events : list (fx_index_nested_event X C B)) : Prop :=
  Forall (fun e => match e with
    | FxiTarget c out body => fxi_target_source source c out body
    | FxiSides c out body => fxi_sides_source source c out body
    | FxiDeps c out body => fxi_deps_source source c out body
    | FxiDistinctBuild _ _ body => fxi_set_external_adequacy source body
    | FxiRead x code _ _ body _ | FxiWrite x code _ _ _ body _ => fxi_encode_source source x code
  body
    | _ => True
    end) events.
Definition fx_index_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (budget : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb budget ->
    let '(result, events) := fx_index_nested_counted S cb in
    fx_index_external_trace_adequacy source events ->
    result = index_system EX S SS /\
    fx_index_adapter_work budget events <= fx_index_nested_input_budget EX S SS budget.
```

## Galois.Fixpoint.FixpointAuditLocal

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditLocal.v`.

```rocq
(** * Counted local solve and checked wrapper

    This proposal composes the actual closure, queue, engine and checker on the same states.
    For example, a duplicate root is tested in the closure and again by the checked wrapper.
    Builds on: FixpointLocalClosureModel, FixpointDeclaredModel and FixpointPartialModel. *)
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

Definition fx_local_solve_erasure_statement : Prop :=
  forall roots fuel, fst (local_solve_counted roots fuel) =
    local_solve EX EC L sch mode S SS ix roots fuel.
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
  | FxLocalRegionBuild _ _ body | FxLocalRootMem _ _ _ body =>
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
Definition fx_local_checked_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix roots fuel,
    let '(result, events) := local_checked_counted EX EC L sch mode S SS ix roots fuel in
    result = local_checked EX EC L sch mode S SS ix roots fuel /\
    fx_local_full_work EC events <= fx_local_checked_input_budget EX EC L sch mode S SS ix roots
  fuel.
```

## Galois.Fixpoint.FixpointAuditLocalCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditLocalCallbacks.v`.

```rocq
(** Same-run local solver callback receipts, including closure and partial checking. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointLocal
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditCheckCallbacks FixpointAuditPartialCallbacks
  FixpointAuditLocalPartial FixpointAuditLocalClosure FixpointAuditLocal.
Import List.ListNotations.
Definition fx_local_closure_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (event : fx_local_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxLocalUnknownMem _ _ _ events | FxLocalUnknownAdd _ _ _ events =>
      Forall2 (fx_local_x_entry_source source) (fx_local_set_entries events) bodies
  | FxLocalConstraintMem _ _ _ events | FxLocalConstraintAdd _ _ _ events =>
      Forall2 (fx_local_c_entry_source source) (fx_local_set_entries events) bodies
  | FxLocalContributors x code _ _ _ => exists body, bodies = [body] /\ fx_source_encode_x source x
  code body
  | FxLocalDeps c out => exists body, bodies = [body] /\ fxi_deps_source index_source c out body
  | _ => bodies = [] end.
Definition fx_local_full_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (event : fx_local_full_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxLocalClosureTrace events => exists groups,
      Forall2 (fx_local_closure_event_source source index_source) events groups /\ bodies = concat
  groups
  | FxLocalEngineTrace events => exists groups, fx_declared_trace_source source events groups /\
  bodies = concat groups
  | FxLocalPartialTrace events => exists groups,
      Forall2 (fx_local_partial_event_source source) events groups /\ bodies = concat groups
  | FxLocalRegionBuild _ _ events | FxLocalRootMem _ _ _ events =>
      Forall2 (fx_local_x_entry_source source) (fx_local_set_entries events) bodies
  | _ => bodies = [] end.
Definition fx_local_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (events : list (fx_local_full_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_local_full_event_source source index_source) events bodies.
Definition fx_local_deps_laws {X C A B} (S : System.t X C A) (SS : System.static S)
    (source : fx_index_external_source X C B) (ib : fx_index_external_budget X C B)
    (weight : B -> nat) : Prop :=
  (forall c, exists body, fxi_deps_source source c (deps SS c) body) /\
  (forall c out body, fxi_deps_source source c out body -> fx_one_body_work weight body <=
  fxi_deps_bound ib c).
Definition fx_local_closure_event_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (event : fx_local_event X C) : nat :=
  match event with
  | FxLocalUnknownMem _ _ _ e | FxLocalUnknownAdd _ _ _ e => fx_local_x_entries_budget wb
  (fx_local_set_entries e)
  | FxLocalConstraintMem _ _ _ e | FxLocalConstraintAdd _ _ _ e => fx_local_c_entries_budget wb
  (fx_local_set_entries e)
  | FxLocalContributors x _ _ _ _ => fx_budget_encode_x wb x
  | FxLocalDeps c _ => fxi_deps_bound ib c | _ => 0 end.
Definition fx_local_full_event_external_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (event : fx_local_full_event X C A) : nat :=
  match event with
  | FxLocalClosureTrace events => fold_right (fun e n => fx_local_closure_event_budget wb ib e + n)
  0 events
  | FxLocalEngineTrace events => fx_declared_external_trace_budget wb events
  | FxLocalPartialTrace events => fold_right (fun e n => fx_local_partial_event_budget wb e + n) 0
  events
  | FxLocalRegionBuild _ _ e | FxLocalRootMem _ _ _ e => fx_local_x_entries_budget wb
  (fx_local_set_entries e)
  | _ => 0 end.
Definition fx_local_external_trace_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (events : list (fx_local_full_event X C A)) : nat :=
  fold_right (fun e n => fx_local_full_event_external_budget wb ib e + n) 0 events.
Definition fx_local_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix roots fuel
    (source : fx_declared_callback_source X C A B) (wb : fx_declared_callback_budget X C A B)
    (index_source : fx_index_external_source X C B) (ib : fx_index_external_budget X C B),
    sys_index_laws EX S SS ix ->
    fx_declared_source_laws EX EC L sch S source -> fx_declared_callback_bounded source wb ->
    fx_local_deps_laws S SS index_source ib (fx_body_weight wb) ->
    let '(out, events) := local_checked_counted EX EC L sch mode S SS ix roots fuel in
    exists bodies, fx_local_trace_source source index_source events bodies /\
      out = local_checked EX EC L sch mode S SS ix roots fuel /\
      fx_local_full_work EC events + fx_declared_body_work (fx_body_weight wb) bodies <=
        fx_local_checked_input_budget EX EC L sch mode S SS ix roots fuel +
          fx_local_external_trace_budget wb ib events.
```

## Galois.Fixpoint.FixpointAuditLocalClosure

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditLocalClosure.v`.

```rocq
(** * Counted local dependency-closure traversal

    This proposed model retains each tested set, contributor lookup and dependency callback.
    A duplicate root is tested again but its dependencies are expanded only on the first visit.
    Builds on: FixpointLocal and counted collection models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointLocal.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
Import List.ListNotations.

Inductive fx_local_event (X C : Type) : Type :=
  | FxLocalUnknownMem (x : X) (input : FinSet.t X) (answer : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxLocalUnknownAdd (x : X) (input output : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxLocalConstraintMem (c : C) (input : FinSet.t C) (answer : bool)
      (body : list (audit_set_event C (fx_encoder_entry C)))
  | FxLocalConstraintAdd (c : C) (input output : FinSet.t C)
      (body : list (audit_set_event C (fx_encoder_entry C)))
  | FxLocalContributors (x : X) (code : positive) (input : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxLocalDeps (c : C) (result : list X)
  | FxLocalFoldUnknown (remaining : list X)
  | FxLocalFoldConstraint (remaining : list C)
  | FxLocalCase (site : nat).
Arguments FxLocalUnknownMem {X C} _ _ _ _.
Arguments FxLocalUnknownAdd {X C} _ _ _ _.
Arguments FxLocalConstraintMem {X C} _ _ _ _.
Arguments FxLocalConstraintAdd {X C} _ _ _ _.
Arguments FxLocalContributors {X C} _ _ _ _ _.
Arguments FxLocalDeps {X C} _ _.
Arguments FxLocalFoldUnknown {X C} _.
Arguments FxLocalFoldConstraint {X C} _.
Arguments FxLocalCase {X C} _.

Fixpoint fx_local_inl {X C} (xs : list X) (rest : list (X + C)) :
    list (X + C) * list (fx_local_event X C) :=
  match xs with
  | [] => (rest, [FxLocalFoldUnknown []])
  | x :: tail => let '(output, events) := fx_local_inl tail rest in
      (inl x :: output, FxLocalFoldUnknown (x :: tail) :: events ++ [FxLocalCase 6])
  end.
Fixpoint fx_local_inr {X C} (cs : list C) (rest : list (X + C)) :
    list (X + C) * list (fx_local_event X C) :=
  match cs with
  | [] => (rest, [FxLocalFoldConstraint []])
  | c :: tail => let '(output, events) := fx_local_inr tail rest in
      (inr c :: output, FxLocalFoldConstraint (c :: tail) :: events ++ [FxLocalCase 6])
  end.

Section Closure.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).
Definition fx_local_step (state : LocalClosure.state X C) :
    LocalClosure.outcome X C * list (fx_local_event X C) :=
  match LocalClosure.pending state with
  | [] => (LocalClosure.Done (LocalClosure.unknowns state) (LocalClosure.constraints state),
           [FxLocalCase 0])
  | inl x :: rest =>
      let seen := LocalClosure.unknowns state in
      let '(present, mem_events) := audit_finset_mem (fx_index_encoder EX) x seen in
      let prefix := [FxLocalCase 0; FxLocalUnknownMem x seen present mem_events;
                     FxLocalCase 1] in
      if present then
        (LocalClosure.Pending (LocalClosure.State seen (LocalClosure.constraints state) rest),
         prefix)
      else
        let '(next, add_events) := audit_finset_add (fx_index_encoder EX) x seen in
        let code := encode EX x in
        let '(raw, trie_events) := audit_map_code_get code (contributors ix) in
        let cs := match raw with Some found => found | None => [] end in
        let '(todo, folds) := fx_local_inr cs rest in
        (LocalClosure.Pending (LocalClosure.State next (LocalClosure.constraints state) todo),
         prefix ++ [FxLocalUnknownAdd x seen next add_events;
                    FxLocalContributors x code (contributors ix) raw trie_events;
                    FxLocalCase 2] ++ folds)
  | inr c :: rest =>
      let seen := LocalClosure.constraints state in
      let '(present, mem_events) := audit_finset_mem (fx_index_encoder EC) c seen in
      let prefix := [FxLocalCase 0; FxLocalConstraintMem c seen present mem_events;
                     FxLocalCase 3] in
      if present then
        (LocalClosure.Pending (LocalClosure.State (LocalClosure.unknowns state) seen rest),
         prefix)
      else
        let '(next, add_events) := audit_finset_add (fx_index_encoder EC) c seen in
        let ds := deps SS c in
        let '(todo, folds) := fx_local_inl ds rest in
        (LocalClosure.Pending (LocalClosure.State (LocalClosure.unknowns state) next todo),
         prefix ++ [FxLocalConstraintAdd c seen next add_events; FxLocalDeps c ds] ++ folds)
  end.

Fixpoint fx_local_walk (fuel : positive) (state : LocalClosure.state X C) :
    LocalClosure.outcome X C * list (fx_local_event X C) :=
  match fuel with
  | xH => let '(out, events) := fx_local_step state in (out, FxLocalCase 4 :: events)
  | xO p =>
      let '(first, events) := fx_local_walk p state in
      match first with
      | LocalClosure.Done region selected =>
          (LocalClosure.Done region selected, FxLocalCase 4 :: events ++ [FxLocalCase 5])
      | LocalClosure.Pending next =>
          let '(out, later) := fx_local_walk p next in
          (out, FxLocalCase 4 :: events ++ FxLocalCase 5 :: later)
      end
  | xI p =>
      let '(first, events) := fx_local_walk p state in
      match first with
      | LocalClosure.Done region selected =>
          (LocalClosure.Done region selected, FxLocalCase 4 :: events ++ [FxLocalCase 5; FxLocalCase
  5])
      | LocalClosure.Pending next =>
          let '(second, later) := fx_local_walk p next in
          match second with
          | LocalClosure.Done region selected =>
              (LocalClosure.Done region selected, FxLocalCase 4 :: events ++
               FxLocalCase 5 :: later ++ [FxLocalCase 5])
          | LocalClosure.Pending last =>
              let '(out, final) := fx_local_step last in
              (out, FxLocalCase 4 :: events ++ FxLocalCase 5 :: later ++ FxLocalCase 5 :: final)
          end
      end
  end.

Definition fx_local_step_erasure_statement : Prop :=
  forall state, fst (fx_local_step state) = LocalClosure.step EX EC S SS ix state.
Definition fx_local_walk_erasure_statement : Prop :=
  forall fuel state, fst (fx_local_walk fuel state) =
    LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel state.
End Closure.

(** Selected primitive source frames use the shared trie and set recurrences. Encoder
    callback entries are counted once; recursive callback-body adequacy is separate. *)
Definition fx_local_event_work {X C} (event : fx_local_event X C) : nat :=
  match event with
  | FxLocalUnknownMem _ _ _ body | FxLocalUnknownAdd _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxLocalConstraintMem _ _ _ body | FxLocalConstraintAdd _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry C)) body
  | FxLocalContributors _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | _ => 1
  end.
Definition fx_local_event_budget {X C} (EX : encoding X) (EC : encoding C)
    (event : fx_local_event X C) : nat :=
  match event with
  | FxLocalUnknownMem x _ _ _ | FxLocalUnknownAdd x _ _ _ =>
      12 + 17 * Pos.size_nat (encode EX x)
  | FxLocalConstraintMem c _ _ _ | FxLocalConstraintAdd c _ _ _ =>
      12 + 17 * Pos.size_nat (encode EC c)
  | FxLocalContributors _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | _ => 1
  end.
Definition fx_local_work {X C} (events : list (fx_local_event X C)) : nat :=
  fold_right (fun event n => fx_local_event_work event + n) 0 events.
Definition fx_local_budget {X C} (EX : encoding X) (EC : encoding C)
    (events : list (fx_local_event X C)) : nat :=
  fold_right (fun event n => fx_local_event_budget EX EC event + n) 0 events.
Definition fx_local_walk_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) fuel state,
    let '(out, events) := fx_local_walk EX EC S SS ix fuel state in
    out = LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel state /\
    fx_local_work events <= fx_local_budget EX EC events.

Definition fx_local_step_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (state : LocalClosure.state X C) : nat :=
  match LocalClosure.pending state with
  | [] => 1
  | inl x :: _ =>
      2 + (12 + 5 * Pos.size_nat (encode EX x)) +
      if FinSet.mem EX x (LocalClosure.unknowns state) then 0 else
        (12 + 17 * Pos.size_nat (encode EX x)) +
        (2 + 6 * Pos.size_nat (encode EX x)) + 1 +
        1 + 2 * length (contributors_of EX ix x)
  | inr c :: _ =>
      2 + (12 + 5 * Pos.size_nat (encode EC c)) +
      if FinSet.mem EC c (LocalClosure.constraints state) then 0 else
        (12 + 17 * Pos.size_nat (encode EC c)) + 1 + 1 + 2 * length (deps SS c)
  end.
Fixpoint fx_local_walk_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (fuel : positive) (state : LocalClosure.state X C) : nat :=
  let step := LocalClosure.step EX EC S SS ix in
  match fuel with
  | xH => 1 + fx_local_step_input_budget EX EC S SS ix state
  | xO smaller =>
      2 + fx_local_walk_input_budget EX EC S SS ix smaller state +
      match LocalClosure.walk step smaller state with
      | LocalClosure.Done _ _ => 0
      | LocalClosure.Pending next => fx_local_walk_input_budget EX EC S SS ix smaller next
      end
  | xI smaller =>
      let first := LocalClosure.walk step smaller state in
      let second := match first with
        | LocalClosure.Done a b => LocalClosure.Done a b
        | LocalClosure.Pending next => LocalClosure.walk step smaller next
        end in
      3 + fx_local_walk_input_budget EX EC S SS ix smaller state +
      (match first with LocalClosure.Done _ _ => 0 | LocalClosure.Pending next =>
        fx_local_walk_input_budget EX EC S SS ix smaller next end) +
      match second with LocalClosure.Done _ _ => 0 | LocalClosure.Pending next =>
        fx_local_step_input_budget EX EC S SS ix next end
  end.
Definition fx_local_walk_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) ix fuel state,
    let '(out, events) := fx_local_walk EX EC S SS ix fuel state in
    out = LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel state /\
    fx_local_work events <= fx_local_walk_input_budget EX EC S SS ix fuel state.
```

## Galois.Fixpoint.FixpointAuditLocalPartial

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditLocalPartial.v`.

```rocq
(** * Strict partial-checker source model

    This proposal retains the actual explored-set and indexed contributor traversals.
    For example, a failed early constraint does not skip later strict boolean arguments.
    Builds on: FixpointPartial and the counted index, set, trie and query models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointPartial.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet
  CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

(** Typed observations retain the actual callbacks and each concrete library subrun. *)
Inductive fx_partial_event (X C A : Type) : Type :=
  | FxPartialQuery (events : audit_trace (fx_declared_call X C A))
  | FxPartialRhs (constraint : C) (result : Query.t X A)
  | FxPartialTarget (constraint : C) (result : X)
  | FxPartialLeb (left right : A) (result : bool)
  | FxPartialMem (key : X) (set : FinSet.t X) (result : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxPartialIndexGet (key : X) (code : positive) (before : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxPartialElements (set : FinSet.t X) (values : list X)
      (body : list (audit_set_elements_event X))
  | FxPartialNot (input result : bool)
  | FxPartialAnd (left right result : bool)
  | FxPartialOr (left right result : bool)
  | FxPartialCase (site : nat).

Arguments FxPartialQuery {X C A} _.
Arguments FxPartialRhs {X C A} _ _.
Arguments FxPartialTarget {X C A} _ _.
Arguments FxPartialLeb {X C A} _ _ _.
Arguments FxPartialMem {X C A} _ _ _ _.
Arguments FxPartialIndexGet {X C A} _ _ _ _ _.
Arguments FxPartialElements {X C A} _ _ _.
Arguments FxPartialNot {X C A} _ _.
Arguments FxPartialAnd {X C A} _ _ _.
Arguments FxPartialOr {X C A} _ _ _.
Arguments FxPartialCase {X C A} _.

Section PartialModel.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (S : System.t X C A) (SS : System.static S) (ix : sys_index X C).
Context (explored : FinSet.t X) (m : assignment X A).

(** Every recorded read is checked even if an earlier read failed. *)
Fixpoint fx_partial_reads (reads : list X) : bool * list (fx_partial_event X C A) :=
  match reads with
  | [] => (true, [FxPartialCase 0])
  | x :: rest =>
      let '(head, body) := audit_finset_mem (fx_index_encoder EX) x explored in
      let '(tail, events) := fx_partial_reads rest in
      (andb head tail, FxPartialCase 0 :: FxPartialMem x explored head body :: events ++
        [FxPartialAnd head tail (andb head tail)])
  end.

(** Strict orb checks the actual membership and lattice comparison for every side. *)
Fixpoint fx_partial_sides (sides : list (X * A)) : bool * list (fx_partial_event X C A) :=
  match sides with
  | [] => (true, [FxPartialCase 1])
  | (x, value) :: rest =>
      let '(member, body) := audit_finset_mem (fx_index_encoder EX) x explored in
      let negated := negb member in
      let '(old, read_events) := @fx_model_lookup X C A EX L m x in
      let within := leb L value old in
      let guard := orb negated within in
      let '(tail, events) := fx_partial_sides rest in
      (andb guard tail,
       FxPartialCase 1 :: FxPartialMem x explored member body :: FxPartialNot member negated ::
       FxPartialQuery read_events :: FxPartialLeb value old within ::
       FxPartialOr negated within guard :: events ++ [FxPartialAnd guard tail (andb guard tail)])
  end.

(** One contributor executes its RHS once, target callback twice, and both strict sides. *)
Definition fx_partial_constraint (c : C) : bool * list (fx_partial_event X C A) :=
  let rhs := System.rhs S c in
  let '(result, query_events) := @fx_model_query X C A EX L rhs m in
  let '(value, reads, sides) := result in
  let '(reads_ok, reads_events) := fx_partial_reads reads in
  let target1 := System.target S c in
  let '(member, member_events) := audit_finset_mem (fx_index_encoder EX) target1 explored in
  let negated := negb member in
  let target2 := System.target S c in
  let '(old, lookup_events) := @fx_model_lookup X C A EX L m target2 in
  let within := leb L value old in
  let guard := orb negated within in
  let first := andb reads_ok guard in
  let '(sides_ok, sides_events) := fx_partial_sides sides in
  (andb first sides_ok,
   [FxPartialRhs c rhs; FxPartialQuery query_events] ++ reads_events ++
   [FxPartialTarget c target1; FxPartialMem target1 explored member member_events;
    FxPartialNot member negated; FxPartialTarget c target2; FxPartialQuery lookup_events;
    FxPartialLeb value old within; FxPartialOr negated within guard;
    FxPartialAnd reads_ok guard first] ++ sides_events ++
   [FxPartialAnd first sides_ok (andb first sides_ok); FxPartialCase 2]).

(** The inner forallb visits every contributor occurrence, including duplicates. *)
Fixpoint fx_partial_contributors (cs : list C) : bool * list (fx_partial_event X C A) :=
  match cs with
  | [] => (true, [FxPartialCase 3])
  | c :: rest =>
      let '(head, first) := fx_partial_constraint c in
      let '(tail, later) := fx_partial_contributors rest in
      (andb head tail, FxPartialCase 3 :: first ++ later ++
        [FxPartialAnd head tail (andb head tail)])
  end.

(** An indexed lookup retains its actual encoding, trie input and result. *)
Fixpoint fx_partial_unknowns (xs : list X) : bool * list (fx_partial_event X C A) :=
  match xs with
  | [] => (true, [FxPartialCase 4])
  | x :: rest =>
      let code := encode EX x in
      let '(raw, get_events) := audit_map_code_get code (contributors ix) in
      let cs := match raw with Some values => values | None => [] end in
      let '(head, first) := fx_partial_contributors cs in
      let '(tail, later) := fx_partial_unknowns rest in
      (andb head tail, FxPartialCase 4 ::
       FxPartialIndexGet x code (contributors ix) raw get_events :: first ++ later ++
       [FxPartialAnd head tail (andb head tail)])
  end.

(** The whole partial checker enumerates exactly the current explored set. *)
Definition check_partial_counted : bool * list (fx_partial_event X C A) :=
  let '(xs, elements_events) := audit_finset_elements explored in
  let '(result, events) := fx_partial_unknowns xs in
  (result, FxPartialElements explored xs elements_events :: events).

(** Every helper and the whole check erase to their original strict computations. *)
Definition fx_partial_model_erasure_statement : Prop :=
  (forall reads, fst (fx_partial_reads reads) = forallb (fun x => FinSet.mem EX x explored) reads)
  /\
  (forall sides, fst (fx_partial_sides sides) =
    forallb (fun ya => negb (FinSet.mem EX (fst ya) explored) ||
      leb L (snd ya) (lookup EX L m (fst ya))) sides) /\
  (forall c, fst (fx_partial_constraint c) = partial_constraint_check EX L S explored (lookup EX L
  m) c) /\
  fst check_partial_counted = check_partial EX L S SS ix explored m.

(** Each typed event has a fixed selected source-frame charge. *)
Definition fx_partial_event_work (event : fx_partial_event X C A) : nat :=
  match event with
  | FxPartialQuery events => fx_declared_model_work EC events
  | FxPartialMem _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxPartialIndexGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FxPartialElements _ _ body => 1 + audit_set_elements_work body
  | _ => 1
  end.

(** The bound uses actual keys, trie states and query events, not a supplied work price. *)
Definition fx_partial_event_budget (event : fx_partial_event X C A) : nat :=
  match event with
  | FxPartialQuery events => audit_work events + fx_declared_primitive_budget EC events
  | FxPartialMem x _ _ _ => 12 + 5 * Pos.size_nat (encode EX x)
  | FxPartialIndexGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FxPartialElements set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | _ => 1
  end.

Definition fx_partial_work (events : list (fx_partial_event X C A)) : nat :=
  fold_right (fun event n => fx_partial_event_work event + n) 0 events.

Definition fx_partial_budget (events : list (fx_partial_event X C A)) : nat :=
  fold_right (fun event n => fx_partial_event_budget event + n) 0 events.

(** The original result and the operand-derived bound refer to the same counted execution. *)
Definition fx_partial_model_cost_statement : Prop :=
  let '(result, events) := check_partial_counted in
  result = check_partial EX L S SS ix explored m /\ fx_partial_work events <= fx_partial_budget
  events.

End PartialModel.

(** The following bounds use only source inputs and the original intermediate query results.
    They are mathematical observations, not executions included in the source-work claim. *)
Fixpoint fx_partial_reads_input_budget {X} (EX : encoding X) (reads : list X) : nat :=
  match reads with
  | [] => 1
  | x :: rest => 2 + (12 + 5 * Pos.size_nat (encode EX x)) + fx_partial_reads_input_budget EX rest
  end.
Fixpoint fx_partial_sides_input_budget {X A} (EX : encoding X) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 1
  | (x, _) :: rest => 5 + (12 + 5 * Pos.size_nat (encode EX x)) +
      fx_fullcheck_lookup_input_budget EX x + fx_partial_sides_input_budget EX rest
  end.
Definition fx_partial_constraint_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (c : C) : nat :=
  let rhs := System.rhs S c in
  let '(_, reads, sides) := Query.run rhs (lookup EX L m) in
  let target := System.target S c in
  9 + fx_fullcheck_query_input_budget EX L m rhs + fx_partial_reads_input_budget EX reads +
    (12 + 5 * Pos.size_nat (encode EX target)) + fx_fullcheck_lookup_input_budget EX target +
    fx_partial_sides_input_budget EX sides.
Fixpoint fx_partial_contributors_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 2 + fx_partial_constraint_input_budget EX L S m c +
      fx_partial_contributors_input_budget EX L S m rest
  end.
Fixpoint fx_partial_unknowns_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (m : assignment X A) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 2 + (2 + 6 * Pos.size_nat (encode EX x)) +
      fx_partial_contributors_input_budget EX L S m (contributors_of EX ix x) +
      fx_partial_unknowns_input_budget EX L S ix m rest
  end.
Definition fx_partial_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (explored : FinSet.t X) (m : assignment X A) : nat :=
  7 + 19 * audit_trie_nodes explored + audit_trie_output_bits explored +
    fx_partial_unknowns_input_budget EX L S ix m (FinSet.elements explored).
Definition fx_partial_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix explored m,
    let '(result, events) := check_partial_counted EX L S ix explored m in
    result = check_partial EX L S SS ix explored m /\
    fx_partial_work EC events <= fx_partial_input_budget EX L S ix explored m.
```

## Galois.Fixpoint.FixpointAuditNarrow

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNarrow.v`.

```rocq
(** * Checked simultaneous narrowing model

    Output discovery is computed once, passes read their original input, and the final
    full checker decides whether the candidate or original map is returned.
    Builds on FixpointNarrow and the counted index, query and checker models. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointNarrow.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditNarrowCheck FixpointAuditNarrowDiscovery.
Import List.ListNotations.

Inductive fx_narrow_event (X C A : Type) : Type :=
  | FnarrowDep (body : list (fx_dependency_event X C))
  | FnarrowQuery (body : audit_trace (fx_declared_call X C A))
  | FnarrowCheck (body : list (fx_fullcheck_event X C A))
  | FnarrowRhs (c : C) (out : Query.t X A)
  | FnarrowTarget (c : C) (out : X)
  | FnarrowJoin (lhs rhs out : A)
  | FnarrowLeb (lhs rhs : A) (out : bool)
  | FnarrowNarrow (lhs rhs out : A)
  | FnarrowIndexGet (x : X) (code : positive) (input : Map.t X (list C)) (raw : option (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FnarrowSet (x : X) (value : A) (code : positive) (input output : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FnarrowCase (site : nat).
Arguments FnarrowDep {X C A} _.
Arguments FnarrowQuery {X C A} _.
Arguments FnarrowCheck {X C A} _.
Arguments FnarrowRhs {X C A} _ _.
Arguments FnarrowTarget {X C A} _ _.
Arguments FnarrowJoin {X C A} _ _ _.
Arguments FnarrowLeb {X C A} _ _ _.
Arguments FnarrowNarrow {X C A} _ _ _.
Arguments FnarrowIndexGet {X C A} _ _ _ _ _.
Arguments FnarrowSet {X C A} _ _ _ _ _ _.
Arguments FnarrowCase {X C A} _.

Section Narrow.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).
Definition fx_narrow_write (x : X) (value : A) (before : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  let code := encode EX x in
  let '(after, body) := audit_trie_set code (x, value) before in
  (after, [FnarrowSet x value code before after body]).
Fixpoint fx_narrow_collect (updates : list (X * A)) (acc : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match updates with
  | [] => (acc, [FnarrowCase 0])
  | (x, value) :: rest =>
      let '(old, read_events) := @fx_model_lookup X C A EX L acc x in
      let joined := join L old value in
      let '(next, write_events) := fx_narrow_write x joined acc in
      let '(out, events) := fx_narrow_collect rest next in
      (out, FnarrowCase 0 :: FnarrowQuery read_events :: FnarrowJoin old value joined ::
        write_events ++ events)
  end.
Fixpoint fx_narrow_constraints (input : assignment X A) (cs : list C) (acc : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match cs with
  | [] => (acc, [FnarrowCase 1])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs input in
      let '(value, _, sides) := answer in
      let target := System.target S c in
      let '(next, collect_events) := fx_narrow_collect ((target, value) :: sides) acc in
      let '(out, tail) := fx_narrow_constraints input rest next in
      (out, FnarrowCase 1 :: FnarrowRhs c rhs :: FnarrowQuery query_events :: FnarrowTarget c
  target ::
        collect_events ++ tail)
  end.
Definition fx_narrow_output (input sums acc : assignment X A) (x : X) :
    assignment X A * list (fx_narrow_event X C A) :=
  let '(old, old_events) := @fx_model_lookup X C A EX L input x in
  let '(value, value_events) := @fx_model_lookup X C A EX L sums x in
  let below := leb L value old in
  let result := if below then narrow L old value else old in
  let branch := if below then [FnarrowNarrow old value result] else [] in
  let '(out, write_events) := fx_narrow_write x result acc in
  (out, FnarrowQuery old_events :: FnarrowQuery value_events :: FnarrowLeb value old below ::
    FnarrowCase 2 :: branch ++ write_events).
Fixpoint fx_narrow_outputs (input sums : assignment X A) (outputs : list X) (acc : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match outputs with
  | [] => (acc, [FnarrowCase 3])
  | x :: rest =>
      let code := encode EX x in
      let '(raw, body) := audit_map_code_get code (contributors ix) in
      let cs := match raw with Some found => found | None => [] end in
      let '(next, events) := match cs with
        | [] => (acc, [FnarrowCase 4])
        | _ :: _ => let '(out, body) := fx_narrow_output input sums acc x in
            (out, FnarrowCase 4 :: body)
        end in
      let '(out, tail) := fx_narrow_outputs input sums rest next in
      (out, FnarrowCase 3 :: FnarrowIndexGet x code (contributors ix) raw body :: events ++ tail)
  end.
Definition fx_narrow_pass (outputs : list X) (input : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  let '(sums, sum_events) := fx_narrow_constraints input (System.constraints S) Map.empty in
  let '(out, output_events) := fx_narrow_outputs input sums outputs input in
  (out, sum_events ++ output_events).
Fixpoint fx_narrow_iter (rounds : nat) (outputs : list X) (input : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  match rounds with
  | 0 => (input, [FnarrowCase 5])
  | Datatypes.S rest =>
      let '(before, events) := fx_narrow_iter rest outputs input in
      let '(out, pass_events) := fx_narrow_pass outputs before in
      (out, FnarrowCase 5 :: events ++ pass_events)
  end.
Definition fx_narrow_checked_counted (rounds : nat) (input : assignment X A) :
    assignment X A * list (fx_narrow_event X C A) :=
  let '(all, all_events) := fx_dependency_outputs_input S SS (System.constraints S) in
  let '(outputs, distinct_events) := @fx_dependency_distinct X C EX all in
  let '(candidate, pass_events) := fx_narrow_iter rounds outputs input in
  let '(accepted, check_events) := fx_fullcheck_counted EX L S candidate in
  (if accepted then candidate else input,
   FnarrowDep all_events :: FnarrowDep distinct_events :: pass_events ++
    [FnarrowCheck check_events; FnarrowCase 6]).
Definition fx_narrow_checked_erasure_statement : Prop :=
  forall rounds input, fst (fx_narrow_checked_counted rounds input) =
    narrow_checked EX L S SS ix rounds input.
End Narrow.

Definition fx_narrow_event_work {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_narrow_event X C A) : nat :=
  match event with
  | FnarrowDep body => fx_dependency_work EX body
  | FnarrowQuery body => fx_declared_model_work EC body
  | FnarrowCheck body => fx_fullcheck_work EC body
  | FnarrowIndexGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FnarrowSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | _ => 1
  end.
Definition fx_narrow_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_narrow_event X C A) : nat :=
  match event with
  | FnarrowDep body => fx_dependency_budget EX body
  | FnarrowQuery body => audit_work body + fx_declared_primitive_budget EC body
  | FnarrowCheck body => fx_fullcheck_budget EC body
  | FnarrowIndexGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FnarrowSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | _ => 1
  end.
Definition fx_narrow_work {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_narrow_event X C A)) : nat :=
  fold_right (fun e n => fx_narrow_event_work EX EC e + n) 0 events.
Definition fx_narrow_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_narrow_event X C A)) : nat :=
  fold_right (fun e n => fx_narrow_event_budget EX EC e + n) 0 events.
Definition fx_narrow_checked_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix rounds input,
    let '(out, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    out = narrow_checked EX L S SS ix rounds input /\
    fx_narrow_work EX EC events <= fx_narrow_budget EX EC events.

(** Input and intermediate-state recurrences below do not consume an observed event list.
    Evaluation of these mathematical budget functions is not part of the source claim. *)
Fixpoint fx_narrow_discovery_rows_budget {X C A} (S : System.t X C A) (SS : System.static S)
    (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 4 + length (System.target S c :: side_targets SS c) +
      fx_narrow_discovery_rows_budget S SS rest
  end.
Definition fx_narrow_discovery_input_budget {X C A} (EX : encoding X)
    (S : System.t X C A) (SS : System.static S) : nat :=
  let rows := flat_map (fun c => System.target S c :: side_targets SS c) (System.constraints S) in
  let set := FinSet.of_list EX rows in
  fx_narrow_discovery_rows_budget S SS (System.constraints S) +
    20 + 12 * length rows + 17 * fx_index_input_bits EX rows +
      19 * audit_trie_nodes set + audit_trie_output_bits set.
Fixpoint fx_narrow_collect_input_budget {X A} (EX : encoding X) (updates : list (X * A)) : nat :=
  match updates with
  | [] => 1
  | (x, _) :: rest => 4 + fx_fullcheck_lookup_input_budget EX x +
      17 * Pos.size_nat (encode EX x) + fx_narrow_collect_input_budget EX rest
  end.
Fixpoint fx_narrow_constraints_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (input : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L input) in
      3 + fx_fullcheck_query_input_budget EX L input rhs +
      fx_narrow_collect_input_budget EX ((System.target S c, value) :: sides) +
      fx_narrow_constraints_input_budget EX L S input rest
  end.
Fixpoint fx_narrow_outputs_input_budget {X C} (EX : encoding X) (ix : sys_index X C)
    (outputs : list X) : nat :=
  match outputs with
  | [] => 1
  | x :: rest =>
      2 + (2 + 6 * Pos.size_nat (encode EX x)) +
      (match contributors_of EX ix x with
       | [] => 0
       | _ :: _ => 3 + 2 * fx_fullcheck_lookup_input_budget EX x +
           (2 + 17 * Pos.size_nat (encode EX x))
       end) + fx_narrow_outputs_input_budget EX ix rest
  end.
Definition fx_narrow_pass_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (ix : sys_index X C) (outputs : list X) (input : assignment X A) : nat :=
  fx_narrow_constraints_input_budget EX L S input (System.constraints S) +
  fx_narrow_outputs_input_budget EX ix outputs.
Fixpoint fx_narrow_rounds_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (outputs : list X) (rounds : nat) (input : assignment X A) : nat :=
  match rounds with
  | 0 => 1
  | Datatypes.S rest =>
      let before := Nat.iter rest (narrow_pass EX L S SS ix) input in
      1 + fx_narrow_rounds_input_budget EX L S SS ix outputs rest input +
        fx_narrow_pass_input_budget EX L S ix outputs before
  end.
Definition fx_narrow_checked_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (rounds : nat) (input : assignment X A) : nat :=
  let outputs := distinct_unknowns EX (flat_map (fun c =>
    System.target S c :: side_targets SS c) (System.constraints S)) in
  let candidate := Nat.iter rounds (narrow_pass EX L S SS ix) input in
  1 + fx_narrow_discovery_input_budget EX S SS +
    fx_narrow_rounds_input_budget EX L S SS ix outputs rounds input +
    fx_fullcheck_input_budget EX L S candidate.
Definition fx_narrow_checked_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix rounds input,
    let '(out, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    out = narrow_checked EX L S SS ix rounds input /\
    fx_narrow_work EX EC events <= fx_narrow_checked_input_budget EX L S SS ix rounds input.

(** A source-shaped derivation explicitly composes the actual output-discovery calls,
    pass iteration, checker and selected branch on one candidate. *)
Inductive fx_narrow_checked_run {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (rounds : nat) (input : assignment X A) : assignment X A -> list (fx_narrow_event X C A) ->
  Prop :=
  | FxNarrowCheckedRun : forall all all_events outputs distinct_events candidate pass_events
  accepted check_events,
      fx_dependency_outputs_input S SS (System.constraints S) = (all, all_events) ->
      @fx_dependency_distinct X C EX all = (outputs, distinct_events) ->
      fx_narrow_iter EX L S ix rounds outputs input = (candidate, pass_events) ->
      fx_fullcheck_counted EX L S candidate = (accepted, check_events) ->
      fx_narrow_checked_run EX L S SS ix rounds input (if accepted then candidate else input)
        (FnarrowDep all_events :: FnarrowDep distinct_events :: pass_events ++
          [FnarrowCheck check_events; FnarrowCase 6]).
Definition fx_narrow_run_total_statement : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix rounds input,
    let '(result, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    fx_narrow_checked_run EX L S SS ix rounds input result events.
Definition fx_narrow_run_correct_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix rounds input result events,
    fx_narrow_checked_run EX L S SS ix rounds input result events ->
    result = narrow_checked EX L S SS ix rounds input /\
    fx_narrow_work EX EC events <= fx_narrow_checked_input_budget EX L S SS ix rounds input.
```

## Galois.Fixpoint.FixpointAuditNarrowCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNarrowCallbacks.v`.

```rocq
(** * Narrowing callback source receipts

    The same narrowing run retains each external callback occurrence and its operand.
    For example, a rejected narrowing test emits no narrowing callback body.
    Builds on: FixpointNarrowModel and FixpointDeclaredCallbacks. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointNarrow.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks FixpointAuditCheckCallbacks FixpointAuditNarrowCheck
  FixpointAuditNarrowDiscovery
  FixpointAuditNarrow.
Import List.ListNotations.

Record fx_narrow_extra_source (X C A B : Type) := FxNarrowExtraSource {
  fx_narrow_sides_source : C -> list X -> list B -> Prop;
  fx_narrow_operation_source : A -> A -> A -> list B -> Prop
}.
Arguments fx_narrow_sides_source {X C A B} _ _ _ _.
Arguments fx_narrow_operation_source {X C A B} _ _ _ _ _.

Record fx_narrow_extra_budget (X C A B : Type) := FxNarrowExtraBudget {
  fx_narrow_sides_bound : C -> nat;
  fx_narrow_operation_bound : A -> A -> nat
}.
Arguments fx_narrow_sides_bound {X C A B} _ _.
Arguments fx_narrow_operation_bound {X C A B} _ _ _.

Definition fx_narrow_entries {X}
    (events : list (audit_set_event X (fx_encoder_entry X))) : list (fx_encoder_entry X) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

Definition fx_narrow_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

Definition fx_narrow_dep_source {X C A B} (source : fx_declared_callback_source X C A B)
    (extra : fx_narrow_extra_source X C A B) (event : fx_dependency_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxDepTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxDepSides c out => exists body, bodies = [body] /\ fx_narrow_sides_source extra c out body
  | FxDepDistinct _ _ _ events _ =>
      Forall2 (fx_narrow_entry_source source) (fx_narrow_entries events) bodies
  | _ => bodies = []
  end.

Definition fx_narrow_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (extra : fx_narrow_extra_source X C A B) (event : fx_narrow_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FnarrowDep events => exists groups,
      Forall2 (fx_narrow_dep_source source extra) events groups /\ bodies = concat groups
  | FnarrowQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FnarrowCheck events => exists groups,
      Forall2 (fx_narrow_check_source source) events groups /\ bodies = concat groups
  | FnarrowRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FnarrowTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FnarrowJoin a b out => exists body, bodies = [body] /\ fx_source_join source a b out body
  | FnarrowLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | FnarrowNarrow a b out => exists body,
      bodies = [body] /\ fx_narrow_operation_source extra a b out body
  | FnarrowIndexGet x code _ _ _ | FnarrowSet x _ code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | _ => bodies = []
  end.

Definition fx_narrow_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (extra : fx_narrow_extra_source X C A B) (events : list (fx_narrow_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_narrow_event_source source extra) events bodies.

Definition fx_narrow_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry X)) : nat :=
  fold_right (fun entry total => match entry with
    | FxEncodeEntry x _ => fx_budget_encode_x budget x + total
    end) 0 entries.

Definition fx_narrow_dep_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (extra : fx_narrow_extra_budget X C A B) (event : fx_dependency_event X C) : nat :=
  match event with
  | FxDepTarget c _ => fx_budget_target budget c
  | FxDepSides c _ => fx_narrow_sides_bound extra c
  | FxDepDistinct _ _ _ events _ => fx_narrow_entries_budget budget (fx_narrow_entries events)
  | _ => 0
  end.

Definition fx_narrow_event_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (extra : fx_narrow_extra_budget X C A B)
    (event : fx_narrow_event X C A) : nat :=
  match event with
  | FnarrowDep events => fold_right (fun e n => fx_narrow_dep_budget budget extra e + n) 0 events
  | FnarrowQuery events => fx_declared_external_trace_budget budget events
  | FnarrowCheck events => fold_right (fun e n => fx_narrow_check_budget budget e + n) 0 events
  | FnarrowRhs c _ => fx_budget_rhs budget c
  | FnarrowTarget c _ => fx_budget_target budget c
  | FnarrowJoin a b _ => fx_budget_join budget a b
  | FnarrowLeb a b _ => fx_budget_leb budget a b
  | FnarrowNarrow a b _ => fx_narrow_operation_bound extra a b
  | FnarrowIndexGet x _ _ _ _ | FnarrowSet x _ _ _ _ _ => fx_budget_encode_x budget x
  | _ => 0
  end.

Definition fx_narrow_external_trace_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (extra : fx_narrow_extra_budget X C A B)
    (events : list (fx_narrow_event X C A)) : nat :=
  fold_right (fun event n => fx_narrow_event_external_budget budget extra event + n) 0 events.

Definition fx_narrow_extra_laws {X C A B} (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (source : fx_narrow_extra_source X C A B)
    (budget : fx_narrow_extra_budget X C A B) (weight : B -> nat) : Prop :=
  (forall c, exists body, fx_narrow_sides_source source c (side_targets SS c) body) /\
  (forall a b, exists body, fx_narrow_operation_source source a b (narrow L a b) body) /\
  (forall c out body, fx_narrow_sides_source source c out body ->
    fx_one_body_work weight body <= fx_narrow_sides_bound budget c) /\
  (forall a b out body, fx_narrow_operation_source source a b out body ->
    fx_one_body_work weight body <= fx_narrow_operation_bound budget a b).

(** Per-call laws cover only callbacks used by the narrowing run. *)
Definition fx_narrow_core_laws {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c) /\
  (forall k a out body, fx_source_continuation source k a out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b out body, fx_source_leb source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_leb budget a b) /\
  (forall a b out body, fx_source_join source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_join budget a b).

(** A checked run has same-invocation callback receipts and an independent phase bound. *)
Definition fx_narrow_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix rounds input
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B)
    (extra : fx_narrow_extra_source X C A B) (extra_budget : fx_narrow_extra_budget X C A B),
    fx_narrow_core_laws EX L S source budget ->
    fx_narrow_extra_laws L S SS extra extra_budget (fx_body_weight budget) ->
    let '(out, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    exists bodies, fx_narrow_trace_source source extra events bodies /\
      out = narrow_checked EX L S SS ix rounds input /\
      fx_narrow_work EX EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_narrow_checked_input_budget EX L S SS ix rounds input +
        fx_narrow_external_trace_budget budget extra_budget events.
```

## Galois.Fixpoint.FixpointAuditNarrowCheck

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNarrowCheck.v`.

```rocq
(** * Strict full checker with concrete assignment lookup

    Every query read and side comparison retains the actual map-lookup subrun.
    Both arguments of boolean conjunction are evaluated even after a false comparison.
    Builds on FixpointCheck and the counted worklist query model. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

Inductive fx_fullcheck_event (X C A : Type) : Type :=
  | FfcQuery (body : audit_trace (fx_declared_call X C A))
  | FfcRhs (c : C) (result : Query.t X A)
  | FfcTarget (c : C) (result : X)
  | FfcLeb (lhs rhs : A) (result : bool)
  | FfcAnd (lhs rhs result : bool)
  | FfcCase (site : nat).
Arguments FfcQuery {X C A} _.
Arguments FfcRhs {X C A} _ _.
Arguments FfcTarget {X C A} _ _.
Arguments FfcLeb {X C A} _ _ _.
Arguments FfcAnd {X C A} _ _ _.
Arguments FfcCase {X C A} _.

Section Check.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (m : assignment X A).
Fixpoint fx_fullcheck_sides (sides : list (X * A)) : bool * list (fx_fullcheck_event X C A) :=
  match sides with
  | [] => (true, [FfcCase 0])
  | (x, value) :: rest =>
      let '(old, lookup_events) := @fx_model_lookup X C A EX L m x in
      let head := leb L value old in
      let '(tail, tail_events) := fx_fullcheck_sides rest in
      (andb head tail, FfcCase 0 :: FfcQuery lookup_events :: FfcLeb value old head ::
        tail_events ++ [FfcAnd head tail (andb head tail)])
  end.
Fixpoint fx_fullcheck_constraints (cs : list C) : bool * list (fx_fullcheck_event X C A) :=
  match cs with
  | [] => (true, [FfcCase 1])
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(answer, query_events) := @fx_model_query X C A EX L rhs m in
      let '(value, _, sides) := answer in
      let target := System.target S c in
      let '(old, lookup_events) := @fx_model_lookup X C A EX L m target in
      let direct := leb L value old in
      let '(side_ok, side_events) := fx_fullcheck_sides sides in
      let current := andb direct side_ok in
      let '(tail, tail_events) := fx_fullcheck_constraints rest in
      (andb current tail, FfcCase 1 :: FfcRhs c rhs :: FfcQuery query_events ::
        FfcTarget c target :: FfcQuery lookup_events :: FfcLeb value old direct :: side_events ++
        FfcAnd direct side_ok current :: tail_events ++ [FfcAnd current tail (andb current tail)])
  end.
Definition fx_fullcheck_counted : bool * list (fx_fullcheck_event X C A) :=
  fx_fullcheck_constraints (System.constraints S).
Definition fx_fullcheck_erasure_statement : Prop :=
  fst fx_fullcheck_counted = check_post L S (lookup EX L m).
End Check.

Definition fx_fullcheck_event_work {X C A} (EC : encoding C) (event : fx_fullcheck_event X C A)
  : nat :=
  match event with FfcQuery body => fx_declared_model_work EC body | _ => 1 end.
Definition fx_fullcheck_event_budget {X C A} (EC : encoding C) (event : fx_fullcheck_event X C
  A) : nat :=
  match event with FfcQuery body => audit_work body + fx_declared_primitive_budget EC body | _
  => 1 end.
Definition fx_fullcheck_work {X C A} (EC : encoding C) (events : list (fx_fullcheck_event X C
  A)) : nat :=
  fold_right (fun event n => fx_fullcheck_event_work EC event + n) 0 events.
Definition fx_fullcheck_budget {X C A} (EC : encoding C) (events : list (fx_fullcheck_event X C
  A)) : nat :=
  fold_right (fun event n => fx_fullcheck_event_budget EC event + n) 0 events.
Definition fx_fullcheck_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A) m,
    let '(out, events) := fx_fullcheck_counted EX L S m in
    out = check_post L S (lookup EX L m) /\ fx_fullcheck_work EC events <= fx_fullcheck_budget
  EC events.

(** These recurrences are functions of source inputs, not the returned event list. The
    budget is a mathematical specification; evaluating it is not part of the claimed run. *)
Fixpoint fx_fullcheck_sides_input_budget {X A} (EX : encoding X) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 1
  | (x, _) :: rest => 3 + fx_fullcheck_lookup_input_budget EX x +
      fx_fullcheck_sides_input_budget EX rest
  end.
Fixpoint fx_fullcheck_constraints_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(_, _, sides) := Query.run rhs (lookup EX L m) in
      6 + fx_fullcheck_query_input_budget EX L m rhs +
        fx_fullcheck_lookup_input_budget EX (System.target S c) +
        fx_fullcheck_sides_input_budget EX sides +
        fx_fullcheck_constraints_input_budget EX L S m rest
  end.
Definition fx_fullcheck_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) : nat :=
  fx_fullcheck_constraints_input_budget EX L S m (System.constraints S).
Definition fx_fullcheck_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A) m,
    let '(result, events) := fx_fullcheck_counted EX L S m in
    result = check_post L S (lookup EX L m) /\
    fx_fullcheck_work EC events <= fx_fullcheck_input_budget EX L S m.
```

## Galois.Fixpoint.FixpointAuditNarrowDiscovery

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNarrowDiscovery.v`.

```rocq
(** * Narrowing output discovery

    The model retains the actual target and side calls and the distinct-set build.
    For example, duplicate outputs are inserted separately before enumeration.
    Builds on: FixpointNarrow and the shared set audit. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditCost
  CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointSystem FixpointAuditWorklist.
Import List.ListNotations.

Inductive fx_dependency_event (X C : Type) : Type :=
  | FxDepTarget (c : C) (out : X)
  | FxDepSides (c : C) (out : list X)
  | FxDepDistinct (input : list X) (set : FinSet.t X) (out : list X)
      (build : list (audit_set_event X (fx_encoder_entry X)))
      (enumerate : list (audit_set_elements_event X))
  | FxDepAppend (size : nat)
  | FxDepCase (site : nat).
Arguments FxDepTarget {X C} _ _.
Arguments FxDepSides {X C} _ _.
Arguments FxDepDistinct {X C} _ _ _ _ _.
Arguments FxDepAppend {X C} _.
Arguments FxDepCase {X C} _.

Definition fx_dependency_distinct {X C} (EX : encoding X) (input : list X) :
    list X * list (fx_dependency_event X C) :=
  let '(set, build) := audit_finset_of_list (fx_index_encoder EX) input in
  let '(out, enumerate) := audit_finset_elements set in
  (out, [FxDepDistinct input set out build enumerate]).

Fixpoint fx_dependency_outputs_input {X C A} (S : System.t X C A) (SS : System.static S)
    (cs : list C) : list X * list (fx_dependency_event X C) :=
  match cs with
  | [] => ([], [FxDepCase 1])
  | c :: rest =>
      let x := System.target S c in
      let sides := side_targets SS c in
      let row := x :: sides in
      let '(tail, events) := fx_dependency_outputs_input S SS rest in
      (row ++ tail, FxDepCase 1 :: FxDepTarget c x :: FxDepSides c sides :: events ++
        [FxDepAppend (length row)])
  end.

Definition fx_index_input_bits {X} (EX : encoding X) (xs : list X) : nat :=
  fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 xs.

Definition fx_dependency_event_work {X C} (event : fx_dependency_event X C) : nat :=
  match event with
  | FxDepDistinct _ _ _ build enumerate =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) build +
        audit_set_elements_work enumerate
  | FxDepAppend n => 1 + n
  | _ => 1
  end.

Definition fx_dependency_event_budget {X C} (EX : encoding X)
    (event : fx_dependency_event X C) : nat :=
  match event with
  | FxDepDistinct input set _ _ _ =>
      20 + 12 * length input + 17 * fx_index_input_bits EX input +
        19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxDepAppend n => 1 + n
  | _ => 1
  end.

Definition fx_dependency_work {X C} (_ : encoding X) (events : list (fx_dependency_event X C)) :
  nat :=
  fold_right (fun e n => fx_dependency_event_work e + n) 0 events.

Definition fx_dependency_budget {X C} (EX : encoding X)
    (events : list (fx_dependency_event X C)) : nat :=
  fold_right (fun e n => fx_dependency_event_budget EX e + n) 0 events.
```

## Galois.Fixpoint.FixpointAuditNested

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNested.v`.

```rocq
(** * Nested solver preparation and execution

    One captured dependency index feeds graph preparation, WTO and the solver machine.
    For example, each graph outgoing call retains the body for its actual vertex.
    Builds on: FixpointAuditScheduleWrapper, GraphAuditWto and the nested phase models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphPrepare GraphWto GraphAuditBase GraphAuditDfs
  GraphAuditWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointNested FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditNestedPlan
  FixpointAuditNestedMachine.
Import List.ListNotations.

Inductive fx_nested_whole_event (X C A B : Type) : Type :=
  | FnWholeDependency (events : list (fx_dep_event X C B))
  | FnWholePrepare (events : list (audit_prepare_source_event X (X * X) (fx_dep_event X C B)))
  | FnWholeWto (events : list (audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))))
  | FnWholePlan (events : list (fx_nested_plan_event X C))
  | FnWholeMachine (events : list (fx_nested_event X C A))
  | FnWholeCase (site : nat).
Arguments FnWholeDependency {X C A B} _.
Arguments FnWholePrepare {X C A B} _.
Arguments FnWholeWto {X C A B} _.
Arguments FnWholePlan {X C A B} _.
Arguments FnWholeMachine {X C A B} _.
Arguments FnWholeCase {X C A B} _.

Definition fx_nested_run_counted {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (fuel : positive) : option (assignment X A) * list (fx_nested_whole_event X C A B) :=
  let '(graph, ix, graph_events) := fx_dep_graph_build EX S SS cb in
  let '(prepared, prepare_events) := audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb
  ix) in
  let '(tokens, wto_events) := audit_wto_source_counted prepared (fx_dep_dfs_cb cb) in
  let '(plan, plan_events) := fx_nested_plan_from_tokens EX S tokens in
  let '(result, machine_events) := fx_nested_loop EX L plan mode S fuel (nested_start plan) in
  (match result with inl _ => None | inr values => Some values end,
   [FnWholeDependency graph_events; FnWholePrepare prepare_events; FnWholeWto wto_events;
    FnWholePlan plan_events; FnWholeMachine machine_events; FnWholeCase 0]).

(** The counted phases erase to the same nested solve when index callbacks erase. *)
Definition fx_nested_run_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B) fuel,
    fx_index_external_erases EX S SS cb ->
    fst (fx_nested_run_counted EX L mode S SS cb fuel) = nested_run EX EC L mode S SS fuel.

Definition fx_nested_whole_event_work {X C A B} (EC : encoding C)
    (ib : fx_index_external_budget X C B) (event : fx_nested_whole_event X C A B) : nat :=
  match event with
  | FnWholeDependency events => fx_dep_events_work ib events
  | FnWholePrepare events => audit_prepare_source_work (fx_dep_event_work ib) events
  | FnWholeWto events => audit_wto_source_work (fx_dep_event_work ib) events
  | FnWholePlan events => fx_nested_plan_work events
  | FnWholeMachine events => fx_nested_work EC events
  | FnWholeCase _ => 1
  end.

Definition fx_nested_whole_work {X C A B} (EC : encoding C)
    (ib : fx_index_external_budget X C B) (events : list (fx_nested_whole_event X C A B)) : nat :=
  fold_right (fun e n => fx_nested_whole_event_work EC ib e + n) 0 events.

Definition fx_nested_run_input_budget {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (ib : fx_index_external_budget X C B) (fuel : positive) : nat :=
  let graph := dependency_graph EX S SS in
  let prepared := prepare EX graph in
  let tokens := wto_total prepared in
  let plan := nested_prepare EX S SS in
  let count := audit_graph_prepare_full_event_bound graph + audit_wto_input_event_bound prepared in
  fx_dep_build_budget EX S SS ib + audit_prepare_source_budget EX graph +
    audit_wto_source_budget EX graph prepared +
    64 * (1 + count) * fx_rpo_callback_max EX S SS ib +
    fx_nested_plan_input_budget EX S tokens +
    fx_nested_loop_input_budget EX L plan mode S fuel (nested_start plan) + 1.

(** The phase allowance depends on inputs and native intermediate structures. *)
Definition fx_nested_run_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(result, events) := fx_nested_run_counted EX L mode S SS cb fuel in
    result = nested_run EX EC L mode S SS fuel /\
    fx_nested_whole_work EC ib events <= fx_nested_run_input_budget EX L mode S SS ib fuel.

(** Each phase consumes the exact result returned by its predecessor. *)
Inductive fx_nested_run_model_relation {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (fuel : positive) :
    option (assignment X A) -> list (fx_nested_whole_event X C A B) -> Prop :=
  | FxNestedRunModel : forall graph ix graph_events prepared prepare_events tokens wto_events
      plan plan_events result machine_events,
      fx_dep_graph_build EX S SS cb = (graph, ix, graph_events) ->
      audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb ix) =
        (prepared, prepare_events) ->
      audit_wto_source_counted prepared (fx_dep_dfs_cb cb) = (tokens, wto_events) ->
      fx_nested_plan_from_tokens EX S tokens = (plan, plan_events) ->
      fx_nested_loop EX L plan mode S fuel (nested_start plan) = (result, machine_events) ->
      fx_nested_run_model_relation EX L mode S SS cb fuel
        (match result with inl _ => None | inr values => Some values end)
        [FnWholeDependency graph_events; FnWholePrepare prepare_events; FnWholeWto wto_events;
         FnWholePlan plan_events; FnWholeMachine machine_events; FnWholeCase 0].

(** Every counted nested run has the corresponding phase derivation. *)
Definition fx_nested_run_model_total_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) mode (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) fuel,
    let '(out, events) := fx_nested_run_counted EX L mode S SS cb fuel in
    fx_nested_run_model_relation EX L mode S SS cb fuel out events.

(** Each such derivation preserves the native result and the independent phase allowance. *)
Definition fx_nested_run_model_correct_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel out events,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_nested_run_model_relation EX L mode S SS cb fuel out events ->
    out = nested_run EX EC L mode S SS fuel /\
    fx_nested_whole_work EC ib events <= fx_nested_run_input_budget EX L mode S SS ib fuel.
```

## Galois.Fixpoint.FixpointAuditNestedCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNestedCallbacks.v`.

```rocq
(** * Nested solver callback source receipts

    The graph callbacks, plan and machine retain actual callback operands and bodies.
    For example, a non-widening update has no widening-body receipt.
    Builds on: FixpointAuditNested and the declared callback source model. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphAuditDfs GraphAuditWto.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditScheduleWrapper FixpointAuditNestedPlan FixpointAuditNestedMachine
  FixpointAuditNested.
Import List.ListNotations.

Definition fx_nested_entries {X}
    (events : list (audit_set_event X (fx_encoder_entry X))) : list (fx_encoder_entry X) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

Definition fx_nested_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

Definition fx_nested_plan_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_nested_plan_event X C) (bodies : list (list B)) : Prop :=
  match event with
  | FnpTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FnpMembersSet x _ code _ _ _ | FnpTargetRead x code _ _ _ |
    FnpTargetWrite x code _ _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FnpHeadsSet _ _ events =>
      Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies
  | _ => bodies = []
  end.

Definition fx_nested_machine_event_source {X C A B}
    (source : fx_declared_callback_source X C A B) (event : fx_nested_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxNestedQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxNestedRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FxNestedTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxNestedLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | FxNestedJoin a b out => exists body, bodies = [body] /\ fx_source_join source a b out body
  | FxNestedWiden a b out => exists body, bodies = [body] /\ fx_source_widen source a b out body
  | FxNestedMapGet x code _ _ _ | FxNestedTargetsGet x code _ _ _ |
    FxNestedValueSet x _ code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxNestedSetMem _ _ _ events | FxNestedSetAdd _ _ _ events |
    FxNestedSetRemove _ _ _ events =>
      Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies
  | _ => bodies = []
  end.

Definition fx_nested_wto_event_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))) : Prop :=
  Forall (fun capture => match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body => fx_dep_body_source source body
    | AuditGraphEncodeCapture _ _ _ _ _ body => fx_dep_body_source source body
    end) (snd event).

Definition fx_nested_whole_event_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_nested_whole_event X C A B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FnWholeDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FnWholePrepare events => Forall (fx_dep_prepare_source index_source) events /\ bodies = []
  | FnWholeWto events => Forall (fx_nested_wto_event_source index_source) events /\ bodies = []
  | FnWholePlan events => exists groups,
      Forall2 (fx_nested_plan_event_source source) events groups /\ bodies = concat groups
  | FnWholeMachine events => exists groups,
      Forall2 (fx_nested_machine_event_source source) events groups /\ bodies = concat groups
  | FnWholeCase _ => bodies = []
  end.

Definition fx_nested_trace_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (events : list (fx_nested_whole_event X C A B))
    (bodies : list (list (list D))) : Prop :=
  Forall2 (fx_nested_whole_event_source index_source source) events bodies.

Definition fx_nested_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry X)) : nat :=
  fold_right (fun entry total => match entry with
    | FxEncodeEntry x _ => fx_budget_encode_x budget x + total
    end) 0 entries.

Definition fx_nested_plan_external_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_nested_plan_event X C) : nat :=
  match event with
  | FnpTarget c _ => fx_budget_target budget c
  | FnpMembersSet x _ _ _ _ _ | FnpTargetRead x _ _ _ _ |
    FnpTargetWrite x _ _ _ _ _ => fx_budget_encode_x budget x
  | FnpHeadsSet _ _ events => fx_nested_entries_budget budget (fx_nested_entries events)
  | _ => 0
  end.

Definition fx_nested_machine_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_nested_event X C A) : nat :=
  match event with
  | FxNestedQuery events => fx_declared_external_trace_budget budget events
  | FxNestedRhs c _ => fx_budget_rhs budget c
  | FxNestedTarget c _ => fx_budget_target budget c
  | FxNestedLeb a b _ => fx_budget_leb budget a b
  | FxNestedJoin a b _ => fx_budget_join budget a b
  | FxNestedWiden a b _ => fx_budget_widen budget a b
  | FxNestedMapGet x _ _ _ _ | FxNestedTargetsGet x _ _ _ _ |
    FxNestedValueSet x _ _ _ _ _ => fx_budget_encode_x budget x
  | FxNestedSetMem _ _ _ events | FxNestedSetAdd _ _ _ events |
    FxNestedSetRemove _ _ _ events => fx_nested_entries_budget budget (fx_nested_entries events)
  | _ => 0
  end.

Definition fx_nested_external_trace_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (events : list (fx_nested_whole_event X C A
  B)) : nat :=
  fold_right (fun event total => total + match event with
    | FnWholePlan plan => fold_right (fun e n => fx_nested_plan_external_budget budget e + n) 0 plan
    | FnWholeMachine machine =>
        fold_right (fun e n => fx_nested_machine_external_budget budget e + n) 0 machine
    | _ => 0
    end) 0 events.

(** The per-call laws cover only source operations reached by plan or machine. *)
Definition fx_nested_machine_source_laws {X C A D} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall a b, exists body, fx_source_widen source a b (widen L a b) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c) /\
  (forall k a out body, fx_source_continuation source k a out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b out body, fx_source_leb source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_leb budget a b) /\
  (forall a b out body, fx_source_join source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_join budget a b) /\
  (forall a b out body, fx_source_widen source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_widen budget a b).

(** The same execution has source receipts and a phase bound plus per-invocation bodies. *)
Definition fx_nested_external_source_statement : Prop :=
  forall X C A B D (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    fuel,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_nested_run_counted EX L mode S SS cb fuel in
    exists bodies, fx_nested_trace_source index_source source events bodies /\
      out = nested_run EX EC L mode S SS fuel /\
      fx_nested_whole_work EC ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_nested_run_input_budget EX L mode S SS ib fuel + fx_nested_external_trace_budget
  budget events.
```

## Galois.Fixpoint.FixpointAuditNestedMachine

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNestedMachine.v`.

```rocq
(** * Counted explicit nested solver machine

    This candidate retains actual traversal frames, maps, dirty-set operations and query runs.
    It assumes a supplied concrete prepared plan; nested_prepare is a separate source phase.
    Builds on FixpointNested and the counted shared collections and query models. *)
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
  let heads := match raw with Some hs => hs | None => [] end in
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
              let targets := match raw with Some cs => cs | None => [] end in
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
      let '(second, later) := match first with
        | inr values => (inr values, [FxNestedCase 16])
        | inl next => let '(out, body) := fx_nested_loop smaller next in
            (out, FxNestedCase 16 :: body)
        end in
      let '(out, last) := fx_nested_tick second in
      (out, FxNestedCase 15 :: events ++ later ++ last)
  end.

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
  | FxNestedMapGet _ code _ _ body | FxNestedTargetsGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FxNestedValueSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FxNestedSetMem _ _ _ body | FxNestedSetAdd _ _ _ body | FxNestedSetRemove _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | _ => 1
  end.
Definition fx_nested_event_budget {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_nested_event X C A) : nat :=
  match event with
  | FxNestedQuery body => audit_work body + fx_declared_primitive_budget EC body
  | FxNestedMapGet _ code _ _ _ | FxNestedTargetsGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FxNestedValueSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | FxNestedSetMem x _ _ _ => 12 + 5 * Pos.size_nat (encode EX x)
  | FxNestedSetAdd x _ _ _ | FxNestedSetRemove x _ _ _ => 12 + 17 * Pos.size_nat (encode EX x)
  | _ => 1
  end.
Definition fx_nested_work {X C A} (EC : encoding C) (events : list (fx_nested_event X C A)) : nat :=
  fold_right (fun event n => fx_nested_event_work EC event + n) 0 events.
Definition fx_nested_budget {X C A} (EX : encoding X) (EC : encoding C)
    (events : list (fx_nested_event X C A)) : nat :=
  fold_right (fun event n => fx_nested_event_budget EX EC event + n) 0 events.
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
      let second := match first with inr values => inr values | inl next => nested_loop step
  smaller next end in
      2 + fx_nested_loop_input_budget EX L plan mode S smaller state +
      (match first with inr _ => 0 | inl next => fx_nested_loop_input_budget EX L plan mode S
  smaller next end) +
      fx_nested_tick_input_budget EX L plan mode S second
  end.
Definition fx_nested_loop_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (plan : NestedPlan.t X C) mode (S : System.t X C A) fuel state,
    let '(out, events) := fx_nested_loop EX L plan mode S fuel state in
    out = nested_loop (nested_step EX L plan mode S) fuel state /\
    fx_nested_work EC events <= fx_nested_loop_input_budget EX L plan mode S fuel state.
```

## Galois.Fixpoint.FixpointAuditNestedPlan

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditNestedPlan.v`.

```rocq
(** * Counted nested-plan syntax phases

    The bounded parser and the head/member traversals preserve component order and stacks.
    For example, an open component parses its body before its following siblings.
    Builds on FixpointNested and the counted collection models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointNested.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditNarrowDiscovery.
Import List.ListNotations.

Inductive fx_nested_plan_event (X C : Type) : Type :=
  | FnpParse (bound : nat) (remaining : wto X)
  | FnpRows (stack : list X) (code : nested_code X)
  | FnpHeads (code : nested_code X)
  | FnpLength (size : nat)
  | FnpAppend (size : nat)
  | FnpTarget (constraint : C) (out : X)
  | FnpMembersSet (x : X) (stack : list X) (code : positive) (before after : Map.t X (list X))
      (body : audit_trace (audit_trie_call (X * list X)))
  | FnpTargetRead (x : X) (code : positive) (before : Map.t X (list C)) (raw : option (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FnpTargetWrite (x : X) (code : positive) (value : list C) (before after : Map.t X (list C))
      (body : audit_trace (audit_trie_call (X * list C)))
  | FnpHeadsSet (heads : list X) (out : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FnpCase (site : nat).
Arguments FnpParse {X C} _ _.
Arguments FnpRows {X C} _ _.
Arguments FnpHeads {X C} _.
Arguments FnpLength {X C} _.
Arguments FnpAppend {X C} _.
Arguments FnpTarget {X C} _ _.
Arguments FnpMembersSet {X C} _ _ _ _ _ _.
Arguments FnpTargetRead {X C} _ _ _ _ _.
Arguments FnpTargetWrite {X C} _ _ _ _ _ _.
Arguments FnpHeadsSet {X C} _ _ _.
Arguments FnpCase {X C} _.

Fixpoint fx_nested_parse {X C} (bound : nat) (tokens : wto X) :
    (nested_code X * wto X) * list (fx_nested_plan_event X C) :=
  let here := [FnpParse bound tokens] in
  match bound with
  | 0 => ((NestedEnd, tokens), here)
  | S smaller =>
      match tokens with
      | [] => ((NestedEnd, []), here ++ [FnpCase 0])
      | WClose :: rest => ((NestedEnd, rest), here ++ [FnpCase 0])
      | WVertex x :: rest =>
          let '(result, events) := @fx_nested_parse X C smaller rest in
          let '(code, after) := result in
          ((NestedVisit x code, after), here ++ FnpCase 0 :: events ++ [FnpCase 1])
      | WOpen h :: rest =>
          let '(first, body_events) := @fx_nested_parse X C smaller rest in
          let '(body, after_body) := first in
          let '(second, tail_events) := @fx_nested_parse X C smaller after_body in
          let '(tail, after) := second in
          ((NestedComponent h body tail, after), here ++ FnpCase 0 :: body_events ++
            tail_events ++ [FnpCase 2])
      end
  end.
Definition fx_nested_tree {X C} (tokens : wto X) :
    nested_code X * list (fx_nested_plan_event X C) :=
  let '(out, events) := @fx_nested_parse X C (S (length tokens)) (tokens ++ [WClose]) in
  (fst out, FnpLength (length tokens) :: FnpAppend (length tokens) :: events).

Fixpoint fx_nested_rows {X C} (stack : list X) (code : nested_code X) :
    list (X * list X) * list (fx_nested_plan_event X C) :=
  match code with
  | NestedEnd => ([], [FnpRows stack code])
  | NestedVisit x rest =>
      let '(tail, events) := @fx_nested_rows X C stack rest in
      ((x, stack) :: tail, FnpRows stack code :: events ++ [FnpCase 3])
  | NestedComponent h body rest =>
      let '(first, body_events) := @fx_nested_rows X C (h :: stack) body in
      let '(second, rest_events) := @fx_nested_rows X C stack rest in
      ((h, h :: stack) :: first ++ second,
       FnpRows stack code :: body_events ++ rest_events ++ [FnpAppend (length first); FnpCase 4])
  end.
Fixpoint fx_nested_heads {X C} (code : nested_code X) :
    list X * list (fx_nested_plan_event X C) :=
  match code with
  | NestedEnd => ([], [FnpHeads code])
  | NestedVisit _ rest =>
      let '(tail, events) := @fx_nested_heads X C rest in (tail, FnpHeads code :: events)
  | NestedComponent h body rest =>
      let '(first, body_events) := @fx_nested_heads X C body in
      let '(second, rest_events) := @fx_nested_heads X C rest in
      (h :: first ++ second, FnpHeads code :: body_events ++ rest_events ++
        [FnpAppend (length first); FnpCase 5])
  end.

Fixpoint fx_nested_member_fold {X C} (EX : encoding X) (rows : list (X * list X)) :
    Map.t X (list X) * list (fx_nested_plan_event X C) :=
  match rows with
  | [] => (Map.empty, [FnpCase 6])
  | (x, stack) :: rest =>
      let '(before, tail) := @fx_nested_member_fold X C EX rest in
      let code := encode EX x in
      let '(after, body) := audit_trie_set code (x, stack) before in
      (after, FnpCase 6 :: tail ++ [FnpMembersSet x stack code before after body])
  end.
Definition fx_nested_members {X C} (EX : encoding X) (code : nested_code X) :
    Map.t X (list X) * list (fx_nested_plan_event X C) :=
  let '(rows, row_events) := @fx_nested_rows X C [] code in
  let '(members, fold_events) := @fx_nested_member_fold X C EX rows in
  (members, row_events ++ fold_events).

Fixpoint fx_nested_target_fold {X C A} (EX : encoding X) (S : System.t X C A) (cs : list C) :
    Map.t X (list C) * list (fx_nested_plan_event X C) :=
  match cs with
  | [] => (Map.empty, [FnpCase 7])
  | c :: rest =>
      let '(before, tail) := fx_nested_target_fold EX S rest in
      let x := System.target S c in
      let read_code := encode EX x in
      let '(raw, read_body) := audit_map_code_get read_code before in
      let old := match raw with Some values => values | None => [] end in
      let value := c :: old in
      let write_code := encode EX x in
      let '(after, write_body) := audit_trie_set write_code (x, value) before in
      (after, FnpCase 7 :: tail ++
        [FnpTarget c x; FnpTargetRead x read_code before raw read_body; FnpCase 8;
         FnpTargetWrite x write_code value before after write_body])
  end.
Definition fx_nested_targets {X C A} (EX : encoding X) (S : System.t X C A) :
    Map.t X (list C) * list (fx_nested_plan_event X C) :=
  fx_nested_target_fold EX S (System.constraints S).
Definition fx_nested_plan_from_tokens {X C A} (EX : encoding X) (S : System.t X C A)
    (tokens : wto X) : NestedPlan.t X C * list (fx_nested_plan_event X C) :=
  let '(code, parse_events) := @fx_nested_tree X C tokens in
  let '(members, member_events) := @fx_nested_members X C EX code in
  let '(targets, target_events) := fx_nested_targets EX S in
  let '(heads, head_events) := @fx_nested_heads X C code in
  let '(head_set, set_events) := audit_finset_of_list (fx_index_encoder EX) heads in
  (NestedPlan.Make code members targets head_set,
    parse_events ++ member_events ++ target_events ++ head_events ++ [FnpHeadsSet heads head_set
  set_events]).

Definition fx_nested_plan_semantic_statement : Prop :=
  (forall X C bound tokens, fst (@fx_nested_parse X C bound tokens) = nested_parse bound tokens) /\
  (forall X C tokens, fst (@fx_nested_tree X C tokens) = nested_tree tokens) /\
  (forall X C stack code, fst (@fx_nested_rows X C stack code) = nested_rows stack code) /\
  (forall X C code, fst (@fx_nested_heads X C code) = nested_heads code) /\
  (forall X C (EX : encoding X) code, fst (@fx_nested_members X C EX code) = nested_members EX
  code) /\
  (forall X C A (EX : encoding X) (S : System.t X C A),
    fst (fx_nested_targets EX S) = nested_targets EX S) /\
  (forall X C A (EX : encoding X) (S : System.t X C A) tokens,
    fst (fx_nested_plan_from_tokens EX S tokens) =
      let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
        (nested_targets EX S) (FinSet.of_list EX (nested_heads code))).

Definition fx_nested_plan_event_work {X C} (event : fx_nested_plan_event X C) : nat :=
  match event with
  | FnpLength n | FnpAppend n => 1 + n
  | FnpMembersSet _ _ code _ _ body | FnpTargetWrite _ code _ _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FnpTargetRead _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | FnpHeadsSet _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | _ => 1
  end.
Definition fx_nested_plan_event_budget {X C} (EX : encoding X) (event : fx_nested_plan_event X
  C) : nat :=
  match event with
  | FnpLength n | FnpAppend n => 1 + n
  | FnpMembersSet _ _ code _ _ _ | FnpTargetWrite _ code _ _ _ _ => 2 + 17 * Pos.size_nat code
  | FnpTargetRead _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | FnpHeadsSet heads _ _ =>
      12 + 12 * length heads + 17 * fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 heads
  | _ => 1
  end.
Definition fx_nested_plan_work {X C} (events : list (fx_nested_plan_event X C)) : nat :=
  fold_right (fun event n => fx_nested_plan_event_work event + n) 0 events.
Definition fx_nested_plan_budget {X C} (EX : encoding X) (events : list (fx_nested_plan_event X
  C)) : nat :=
  fold_right (fun event n => fx_nested_plan_event_budget EX event + n) 0 events.
Definition fx_nested_plan_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (S : System.t X C A) tokens,
    let '(result, events) := fx_nested_plan_from_tokens EX S tokens in
    result = (let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
      (nested_targets EX S) (FinSet.of_list EX (nested_heads code))) /\
    fx_nested_plan_work events <= fx_nested_plan_budget EX events.

(** This bound is computed from the original token list, code-derived rows and actual
    constraint targets, independently of the observer's event list. *)
Definition fx_nested_plan_input_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (tokens : wto X) : nat :=
  let code := nested_tree tokens in
  let rows := nested_rows [] code in
  let heads := nested_heads code in
  let targets := map (System.target S) (System.constraints S) in
  let size := 1 + length tokens + length (System.constraints S) in
  200 * size * size * size +
  40 * (fx_index_input_bits EX (map fst rows) + fx_index_input_bits EX heads +
        fx_index_input_bits EX targets).
Definition fx_nested_plan_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (S : System.t X C A) tokens,
    let '(result, events) := fx_nested_plan_from_tokens EX S tokens in
    result = (let code := nested_tree tokens in NestedPlan.Make code (nested_members EX code)
      (nested_targets EX S) (FinSet.of_list EX (nested_heads code))) /\
    fx_nested_plan_work events <= fx_nested_plan_input_budget EX S tokens.
```

## Galois.Fixpoint.FixpointAuditPartialCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditPartialCallbacks.v`.

```rocq
(** * Rooted partial-checker callback receipts

    The actual explored-set checker uses contributors from a well-formed system index.
    For example, duplicate contributors each retain their own callback invocations.
    Builds on: FixpointAuditLocalPartial and FixpointAuditCheckCallbacks. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointPartial
  FixpointAuditWorklistCallbacks FixpointAuditCheckCallbacks FixpointAuditLocalPartial.
Import List.ListNotations.

Definition fx_local_partial_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_partial_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxPartialQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxPartialRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FxPartialTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxPartialLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | FxPartialMem _ _ _ events =>
      Forall2 (fx_local_x_entry_source source) (fx_local_set_entries events) bodies
  | FxPartialIndexGet x code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | _ => bodies = []
  end.

Definition fx_local_partial_event_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_partial_event X C A) : nat :=
  match event with
  | FxPartialQuery events => fx_declared_external_trace_budget budget events
  | FxPartialRhs c _ => fx_budget_rhs budget c
  | FxPartialTarget c _ => fx_budget_target budget c
  | FxPartialLeb a b _ => fx_budget_leb budget a b
  | FxPartialMem _ _ _ events => fx_local_x_entries_budget budget (fx_local_set_entries events)
  | FxPartialIndexGet x _ _ _ _ => fx_budget_encode_x budget x
  | _ => 0
  end.

Definition fx_partial_rooted_trace_source {X C A B}
    (source : fx_declared_callback_source X C A B) (events : list (fx_partial_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_local_partial_event_source source) events bodies.

Definition fx_partial_rooted_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_partial_event X C A)) : nat :=
  fold_right (fun event n => fx_local_partial_event_budget budget event + n) 0 events.

(** The actual partial checker has rooted receipts for every well-formed contributor. *)
Definition fx_partial_rooted_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B),
    sys_index_laws EX S SS ix -> fx_fullcheck_rooted_laws EX L S source budget ->
    let '(out, events) := check_partial_counted EX L S ix explored m in
    exists bodies, fx_partial_rooted_trace_source source events bodies /\
      out = check_partial EX L S SS ix explored m /\
      fx_partial_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_partial_input_budget EX L S ix explored m + fx_partial_rooted_external_budget budget
  events.
```

## Galois.Fixpoint.FixpointAuditPartialCheck

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditPartialCheck.v`.

```rocq
(** * Partial checker with explicit callback-body subruns

    Every explored-set visit, contributor, query and strict boolean side is retained.
    Higher-order query continuations use the fixed relation from the full checker.
    Builds on FixpointPartial and shared collection/full-check models. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointPartial.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditFullCheck.
Import List.ListNotations.

Inductive fx_partial_nested_event (X C A B : Type) : Type :=
  | FpnCheck (body : list (fx_check_nested_event X C A B))
  | FpnMem (x : X) (set : FinSet.t X) (answer : bool) (body : list (audit_set_event X B))
  | FpnIndex (x : X) (input : Map.t X (list C)) (raw : option (list C))
      (body : list (audit_map_event X (list C) B))
  | FpnElements (set : FinSet.t X) (items : list X) (body : list (audit_set_elements_event X))
  | FpnCase (site : nat).
Arguments FpnCheck {X C A B} _.
Arguments FpnMem {X C A B} _ _ _ _.
Arguments FpnIndex {X C A B} _ _ _ _.
Arguments FpnElements {X C A B} _ _ _.
Arguments FpnCase {X C A B} _.

Section PartialAdapter.
Context {X C A B : Type} (L : lattice A) (S : System.t X C A)
  (ix : sys_index X C) (explored : FinSet.t X) (m : assignment X A)
  (cb : fx_check_external_model X C A B).
Fixpoint fpn_reads (xs : list X) : bool * list (fx_partial_nested_event X C A B) :=
  match xs with
  | [] => (true, [FpnCase 0])
  | x :: rest =>
      let '(head, body) := audit_finset_mem (fx_check_encode_model cb) x explored in
      let '(tail, events) := fpn_reads rest in
      (andb head tail, FpnCase 0 :: FpnMem x explored head body :: events ++ [FpnCase 1])
  end.
Fixpoint fpn_sides (xs : list (X * A)) : bool * list (fx_partial_nested_event X C A B) :=
  match xs with
  | [] => (true, [FpnCase 2])
  | (x, value) :: rest =>
      let '(member, mem_body) := audit_finset_mem (fx_check_encode_model cb) x explored in
      let '(old, lookup_events) := fcn_lookup L m cb x in
      let '(le, leb_body) := fx_check_leb_model cb value old in
      let guard := orb (negb member) le in
      let '(tail, events) := fpn_sides rest in
      (andb guard tail, FpnCase 2 :: FpnMem x explored member mem_body :: FpnCase 3 ::
        FpnCheck lookup_events :: FpnCheck [FcnLeb value old le leb_body] :: FpnCase 4 ::
        events ++ [FpnCase 5])
  end.

Inductive fpn_constraint_run : C -> bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnConstraint : forall c rhs rhs_body value reads sides query_events reads_ok reads_events
      target1 target_body1 member mem_body target2 target_body2 old lookup_events le leb_body
      side_ok side_events,
      fx_check_rhs_model cb c = (rhs, rhs_body) ->
      fcn_query_run L m cb rhs (value, reads, sides) query_events ->
      fpn_reads reads = (reads_ok, reads_events) ->
      fx_check_target_model cb c = (target1, target_body1) ->
      audit_finset_mem (fx_check_encode_model cb) target1 explored = (member, mem_body) ->
      fx_check_target_model cb c = (target2, target_body2) ->
      fcn_lookup L m cb target2 = (old, lookup_events) ->
      fx_check_leb_model cb value old = (le, leb_body) ->
      fpn_sides sides = (side_ok, side_events) ->
      fpn_constraint_run c (andb (andb reads_ok (orb (negb member) le)) side_ok)
        ([FpnCheck [FcnRhs c rhs rhs_body]; FpnCheck query_events] ++ reads_events ++
         [FpnCheck [FcnTarget c target1 target_body1]; FpnMem target1 explored member mem_body;
          FpnCase 6; FpnCheck [FcnTarget c target2 target_body2]; FpnCheck lookup_events;
          FpnCheck [FcnLeb value old le leb_body]; FpnCase 7; FpnCase 8] ++ side_events ++
  [FpnCase 9]).
Inductive fpn_constraints_run : list C -> bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnConstraintsNil : fpn_constraints_run [] true [FpnCase 10]
  | FpnConstraintsCons : forall c rest head first tail later,
      fpn_constraint_run c head first -> fpn_constraints_run rest tail later ->
      fpn_constraints_run (c :: rest) (andb head tail)
        (FpnCase 10 :: first ++ later ++ [FpnCase 11]).
Inductive fpn_unknowns_run : list X -> bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnUnknownsNil : fpn_unknowns_run [] true [FpnCase 12]
  | FpnUnknownsCons : forall x rest raw map_body cs head first tail later,
      audit_map_get (fx_check_encode_model cb) x (contributors ix) = (raw, map_body) ->
      cs = (match raw with Some found => found | None => [] end) ->
      fpn_constraints_run cs head first -> fpn_unknowns_run rest tail later ->
      fpn_unknowns_run (x :: rest) (andb head tail)
        (FpnCase 12 :: FpnIndex x (contributors ix) raw map_body :: first ++ later ++ [FpnCase 13]).
Inductive fx_partial_nested_run : bool -> list (fx_partial_nested_event X C A B) -> Prop :=
  | FpnRun : forall xs elements_body out events,
      audit_finset_elements explored = (xs, elements_body) ->
      fpn_unknowns_run xs out events ->
      fx_partial_nested_run out (FpnElements explored xs elements_body :: events).
End PartialAdapter.
Definition fx_partial_nested_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> forall out events,
    fx_partial_nested_run L ix explored m cb out events ->
    out = check_partial EX L S SS ix explored m.
Definition fx_partial_nested_total_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> exists out events, fx_partial_nested_run L ix explored
  m cb out events.

Definition fpn_event_work {X C A B} (budget : fx_check_external_budget X C A B)
    (event : fx_partial_nested_event X C A B) : nat :=
  match event with
  | FpnCheck body => fx_check_nested_work budget body
  | FpnMem _ _ _ body => 3 + audit_finset_source_work (fx_check_body_work budget) body
  | FpnIndex _ _ _ body => 3 + audit_map_source_work (fx_check_body_work budget) body
  | FpnElements _ _ body => 3 + audit_set_elements_work body
  | FpnCase _ => 3
  end.
Definition fx_partial_nested_work {X C A B} (budget : fx_check_external_budget X C A B)
    (events : list (fx_partial_nested_event X C A B)) : nat :=
  fold_right (fun e n => fpn_event_work budget e + n) 0 events.
Definition fpn_mem_budget {X C A B} (EX : encoding X) (budget : fx_check_external_budget X C A B)
    (x : X) : nat := 9 + fx_check_encode_bound budget x + 5 * Pos.size_nat (encode EX x).
Fixpoint fpn_reads_budget {X C A B} (EX : encoding X) (budget : fx_check_external_budget X C A B)
    (reads : list X) : nat :=
  match reads with [] => 3 | x :: rest => 6 + fpn_mem_budget EX budget x + fpn_reads_budget EX
  budget rest end.
Fixpoint fpn_sides_budget {X C A B} (EX : encoding X) (L : lattice A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 3
  | (x, value) :: rest => 15 + fpn_mem_budget EX budget x + fx_check_nested_lookup_budget EX
  budget x +
      fx_check_leb_bound budget value (lookup EX L m x) + fpn_sides_budget EX L budget m rest
  end.
Definition fpn_constraint_budget {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (c : C) : nat :=
  let rhs := System.rhs S c in let '(value, reads, sides) := Query.run rhs (lookup EX L m) in
  let target := System.target S c in
  24 + fx_check_rhs_bound budget c + 2 * fx_check_target_bound budget c +
    fx_check_nested_query_budget EX L budget m rhs + fpn_reads_budget EX budget reads +
    fpn_mem_budget EX budget target + fx_check_nested_lookup_budget EX budget target +
    fx_check_leb_bound budget value (lookup EX L m target) + fpn_sides_budget EX L budget m sides.
Fixpoint fpn_constraints_budget {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 3
  | c :: rest => 6 + fpn_constraint_budget EX L S budget m c + fpn_constraints_budget EX L S
  budget m rest
  end.
Fixpoint fpn_unknowns_budget {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (budget : fx_check_external_budget X C A B) (ix : sys_index X C) (m : assignment X A)
    (xs : list X) : nat :=
  match xs with
  | [] => 3
  | x :: rest => 14 + fx_check_encode_bound budget x + 5 * Pos.size_nat (encode EX x) +
      fpn_constraints_budget EX L S budget m (contributors_of EX ix x) +
      fpn_unknowns_budget EX L S budget ix m rest
  end.
Definition fx_partial_nested_input_budget {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (budget : fx_check_external_budget X C A B) (ix : sys_index X C)
    (explored : FinSet.t X) (m : assignment X A) : nat :=
  9 + 19 * audit_trie_nodes explored + audit_trie_output_bits explored +
    fpn_unknowns_budget EX L S budget ix m (FinSet.elements explored).
Definition fx_partial_nested_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B)
    (budget : fx_check_external_budget X C A B),
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_partial_nested_run L ix explored m cb out events ->
    out = check_partial EX L S SS ix explored m /\
    fx_partial_nested_work budget events <= fx_partial_nested_input_budget EX L S budget ix
  explored m.

Definition fpn_set_source_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (body : list (audit_set_event X B)) : Prop :=
  Forall (fun e => match e with
    | AuditSetAdd x code _ _ trace _ | AuditSetMem x code _ _ trace _ |
      AuditSetRemove x code _ _ trace _ => fx_check_encode_source source x code trace
    | AuditSetFold _ _ => True end) body.
Definition fpn_map_source_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (body : list (audit_map_event X (list C) B)) : Prop :=
  Forall (fun e => match e with
    | AuditMapGet x code _ _ trace _ | AuditMapSet x _ code _ _ trace _ |
      AuditMapRemove x code _ _ trace _ => fx_check_encode_source source x code trace end) body.
Definition fx_partial_external_trace_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (events : list (fx_partial_nested_event X C A B)) : Prop :=
  Forall (fun e => match e with
    | FpnCheck body => fx_check_external_trace_adequacy source body
    | FpnMem _ _ _ body => fpn_set_source_adequacy source body
    | FpnIndex _ _ _ body => fpn_map_source_adequacy source body
    | _ => True end) events.
Definition fx_partial_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (cb : fx_check_external_model X C A B)
    (budget : fx_check_external_budget X C A B) (source : fx_check_external_source X C A B),
    sys_index_laws EX S SS ix ->
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_partial_nested_run L ix explored m cb out events -> fx_partial_external_trace_adequacy
  source events ->
    out = check_partial EX L S SS ix explored m /\
    fx_partial_nested_work budget events <= fx_partial_nested_input_budget EX L S budget ix
  explored m.
```

## Galois.Fixpoint.FixpointAuditRecorded

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditRecorded.v`.

```rocq
(** * Recorded-reader worklist source model

    This proposal retains the actual duplicate read occurrences and persistent reader maps.
    For example, two reads of the same unknown execute two recorded updates.
    Builds on: FixpointWorklist and the counted queue, trie, set and enumeration models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsHeap CollectionsAuditQueue.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet
  CollectionsAuditQueue CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
Import List.ListNotations.
Definition fx_index_set_nested_work {X} (event : audit_set_event X (fx_encoder_entry X)) : nat :=
  match event with
  | AuditSetAdd _ _ _ _ enc trie | AuditSetRemove _ _ _ _ enc trie =>
      List.length enc + audit_trie_update_trace_source_work trie
  | AuditSetMem _ _ _ _ enc trie => List.length enc + audit_trie_get_trace_source_work trie
  | AuditSetFold _ _ => 0
  end.

(** An event retains the exact persistent reader map and all actual nested primitive subruns. *)
Inductive fx_recorded_event (X C A : Type) : Type :=
  | FxRecordedBase (events : audit_trace (fx_declared_call X C A))
  | FxRecordedRead (unknown : X) (constraint : C) (before : Map.t X (FinSet.t C))
      (lookup_code : positive) (raw : option (FinSet.t C))
      (lookup_events : audit_trace (audit_trie_call (X * FinSet.t C)))
      (old_set new_set : FinSet.t C) (add_events : list (audit_set_event C (fx_encoder_entry C)))
      (set_code : positive) (after : Map.t X (FinSet.t C))
      (set_events : audit_trace (audit_trie_call (X * FinSet.t C)))
  | FxRecordedReaders (unknown : X) (before : Map.t X (FinSet.t C))
      (code : positive) (raw : option (FinSet.t C))
      (lookup_events : audit_trace (audit_trie_call (X * FinSet.t C)))
      (set : FinSet.t C) (readers : list C) (elements_events : list (audit_set_elements_event C))
  | FxRecordedWrite (unknown : X) (code : positive) (value : A)
      (before after : assignment X A) (body : audit_trace (audit_trie_call (X * A)))
  | FxRecordedCompare (value old : A) (unchanged : bool)
  | FxRecordedCase (site : nat).

Arguments FxRecordedBase {X C A} _.
Arguments FxRecordedRead {X C A} _ _ _ _ _ _ _ _ _ _ _ _.
Arguments FxRecordedReaders {X C A} _ _ _ _ _ _ _ _.
Arguments FxRecordedWrite {X C A} _ _ _ _ _ _.
Arguments FxRecordedCompare {X C A} _ _ _.
Arguments FxRecordedCase {X C A} _.

(** One read performs the original map lookup, set insertion and map write once each. *)
Definition fx_recorded_read_one {X C A} (EX : encoding X) (EC : encoding C) (c : C) (x : X)
    (before : Map.t X (FinSet.t C)) : Map.t X (FinSet.t C) * fx_recorded_event X C A :=
  let lookup_code := encode EX x in
  let '(raw, lookup_events) := audit_map_code_get lookup_code before in
  let old_set := match raw with Some set => set | None => FinSet.empty end in
  let '(new_set, add_events) := audit_finset_add (fx_index_encoder EC) c old_set in
  let set_code := encode EX x in
  let '(after, set_events) := audit_trie_set set_code (x, new_set) before in
  (after, FxRecordedRead x c before lookup_code raw lookup_events old_set new_set add_events
    set_code after set_events).

(** The real left fold retains every read occurrence, including duplicate unknowns. *)
Fixpoint fx_record_reads_counted {X C A} (EX : encoding X) (EC : encoding C) (c : C)
    (reads : list X) (before : Map.t X (FinSet.t C)) :
    Map.t X (FinSet.t C) * list (fx_recorded_event X C A) :=
  match reads with
  | [] => (before, [FxRecordedCase 0])
  | x :: rest =>
      let '(next, event) := @fx_recorded_read_one X C A EX EC c x before in
      let '(out, tail) := @fx_record_reads_counted X C A EX EC c rest next in
      (out, FxRecordedCase 0 :: event :: tail)
  end.

(** Reader lookup retains the exact set and its actual enumeration subrun. *)
Definition fx_recorded_readers_counted {X C A} (EX : encoding X)
    (before : Map.t X (FinSet.t C)) (x : X) : list C * fx_recorded_event X C A :=
  let code := encode EX x in
  let '(raw, lookup_events) := audit_map_code_get code before in
  let set := match raw with Some value => value | None => FinSet.empty end in
  let '(readers, elements_events) := audit_finset_elements set in
  (readers, FxRecordedReaders x before code raw lookup_events set readers elements_events).

(** Reader-map updates erase to the actual recorded dependency operation. *)
Definition fx_record_reads_erasure_statement : Prop :=
  forall X C (EX : encoding X) (EC : encoding C) c reads before,
    fst (@fx_record_reads_counted X C unit EX EC c reads before) = record_reads EX EC c reads
  before.

(** Every read occurrence contributes one update, even when values repeat. *)
Definition fx_record_reads_count_statement : Prop :=
  forall X C (EX : encoding X) (EC : encoding C) c reads before,
    List.length (snd (@fx_record_reads_counted X C unit EX EC c reads before)) =
      Datatypes.S (2 * List.length reads).

(** A recorded-reader enumeration returns the original engine reader list. *)
Definition fx_recorded_readers_erasure_statement : Prop :=
  forall X C A (EX : encoding X) (S : System.t X C A) before x,
    fst (@fx_recorded_readers_counted X C A EX before x) =
      engine_readers EX (Recorded : dependencies S) before x.

Section RecordedEngine.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).

(** The original update branches on the actual old value and enumerates recorded readers. *)
Definition fx_recorded_update (r : Map.t X (FinSet.t C)) (xa : X * A)
    (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * list (fx_recorded_event X C A) :=
  let '(values, queue) := mq in
  let '(x, value) := xa in
  let '(old, lookup_events) := @fx_model_lookup X C A EX L values x in
  let unchanged := leb L value old in
  if unchanged then
    ((values, queue), [FxRecordedBase lookup_events; FxRecordedCompare value old unchanged;
      FxRecordedCase 1])
  else
    let '(raised, raise_events) := @fx_model_raise X C A L sch mode x old value in
    let code := encode EX x in
    let '(next_values, write_events) := audit_trie_set code (x, raised) values in
    let '(readers, reader_event) := @fx_recorded_readers_counted X C A EX r x in
    let '(next_queue, enqueue_events) := fx_model_enqueue EC sch S readers queue in
    ((next_values, next_queue),
     [FxRecordedBase lookup_events; FxRecordedCompare value old unchanged; FxRecordedCase 1;
      FxRecordedBase raise_events; FxRecordedWrite x code raised values next_values write_events;
      reader_event; FxRecordedBase enqueue_events]).

(** Updates follow the actual left fold and retain every intermediate assignment and queue. *)
Fixpoint fx_recorded_updates (r : Map.t X (FinSet.t C)) (updates : list (X * A))
    (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * list (fx_recorded_event X C A) :=
  match updates with
  | [] => (mq, [FxRecordedCase 2])
  | update :: rest =>
      let '(next, head) := fx_recorded_update r update mq in
      let '(out, tail) := fx_recorded_updates r rest next in
      (out, FxRecordedCase 2 :: head ++ tail)
  end.

(** Each successful step records exactly the reads returned by that same query run. *)
Definition fx_recorded_step (state : Engine.t X C A) :
    outcome X C A * list (fx_recorded_event X C A) :=
  let '(popped, pop_events) := audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state)
  in
  let prefix := [FxRecordedBase [AuditCall (FxPop (Engine.queue state) popped pop_events)];
                 FxRecordedCase 3] in
  match popped with
  | None => (Done (Engine.current state), prefix)
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(result, query_events) := @fx_model_query X C A EX L rhs (Engine.current state) in
      let '(value, reads, sides) := result in
      let '(recorded, read_events) :=
        @fx_record_reads_counted X C A EX EC c reads (Engine.recorded state) in
      let target := System.target S c in
      let '(next, update_events) :=
        fx_recorded_updates recorded ((target, value) :: sides) (Engine.current state, queue) in
      let '(values, next_queue) := next in
      (Pending (Engine.State values next_queue recorded),
       prefix ++ [FxRecordedBase [AuditCall (FxRhs c rhs)]; FxRecordedBase query_events] ++
       read_events ++ [FxRecordedBase [AuditCall (FxTarget c target)]] ++ update_events ++
       [FxRecordedCase 8])
  end.

(** Binary fuel follows the same continuation branches as the original recorded worklist. *)
Fixpoint fx_recorded_loop (fuel : positive) (state : Engine.t X C A) :
    outcome X C A * list (fx_recorded_event X C A) :=
  match fuel with
  | xH =>
      let '(out, events) := fx_recorded_step state in (out, FxRecordedCase 4 :: events)
  | xO rest =>
      let '(first, first_events) := fx_recorded_loop rest state in
      match first with
      | Done values => (Done values, FxRecordedCase 4 :: first_events ++ [FxRecordedCase 5])
      | Pending next =>
          let '(out, second_events) := fx_recorded_loop rest next in
          (out, FxRecordedCase 4 :: first_events ++ [FxRecordedCase 5] ++ second_events)
      end
  | xI rest =>
      let '(first, first_events) := fx_recorded_loop rest state in
      let '(second, second_events) :=
        match first with
        | Done values => (Done values, [FxRecordedCase 5])
        | Pending next =>
            let '(out, events) := fx_recorded_loop rest next in (out, FxRecordedCase 5 :: events)
        end in
      match second with
      | Done values =>
          (Done values, FxRecordedCase 4 :: first_events ++ second_events ++ [FxRecordedCase 5])
      | Pending next =>
          let '(out, final_events) := fx_recorded_step next in
          (out, FxRecordedCase 4 :: first_events ++ second_events ++ [FxRecordedCase 5] ++
  final_events)
      end
  end.

(** Initialization and fuel exhaustion retain the actual recorded worklist result. *)
Definition run_worklist_recorded_model (fuel : positive) :
    option (assignment X A) * list (fx_recorded_event X C A) :=
  let '(queue, initialization) := fx_model_enqueue EC sch S (System.constraints S) PQueue.empty in
  let '(out, events) := fx_recorded_loop fuel (Engine.State Map.empty queue Map.empty) in
  (match out with Done values => Some values | Pending _ => None end,
   FxRecordedBase initialization :: FxRecordedCase 6 :: events ++ [FxRecordedCase 7]).

(** Each helper and the full fixed-fuel operation erase to the original recorded operations. *)
Definition fx_recorded_model_erasure_statement : Prop :=
  (forall r xa mq, fst (fx_recorded_update r xa mq) =
    engine_update EX EC L sch mode S Recorded r xa mq) /\
  (forall r ups mq, fst (fx_recorded_updates r ups mq) =
    engine_updates EX EC L sch mode S Recorded r ups mq) /\
  (forall state, fst (fx_recorded_step state) = step_outcome EX EC L sch mode S Recorded state) /\
  (forall fuel state, fst (fx_recorded_loop fuel state) =
    loop (step_outcome EX EC L sch mode S Recorded) fuel state) /\
  (forall fuel, fst (run_worklist_recorded_model fuel) =
    run_worklist EX EC L sch mode S Recorded fuel).

(** The fixed charge includes each retained map, set, enumeration and queue source-frame model. *)
Definition fx_recorded_event_work (event : fx_recorded_event X C A) : nat :=
  match event with
  | FxRecordedBase events => fx_declared_model_work EC events
  | FxRecordedRead _ _ _ lookup_code _ lookup_events _ _ add_events set_code _ set_events =>
      1 + audit_encoding_weight (Pos.size_nat lookup_code) +
      audit_trie_get_trace_source_work lookup_events + audit_finset_source_work (@length
  (fx_encoder_entry C)) add_events +
      audit_encoding_weight (Pos.size_nat set_code) + audit_trie_update_trace_source_work set_events
  | FxRecordedReaders _ _ code _ lookup_events _ _ elements_events =>
      1 + audit_encoding_weight (Pos.size_nat code) +
      audit_trie_get_trace_source_work lookup_events + audit_set_elements_work elements_events
  | FxRecordedWrite _ code _ _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FxRecordedCompare _ _ _ => 1
  | FxRecordedCase _ => 1
  end.

(** Work is the fixed fold over this particular recorded execution's events. *)
Definition fx_recorded_work (events : list (fx_recorded_event X C A)) : nat :=
  fold_right (fun event total => fx_recorded_event_work event + total) 0 events.

(** The budget uses actual operand sizes and reader-set states, never a client-provided price. *)
Definition fx_recorded_event_budget (event : fx_recorded_event X C A) : nat :=
  match event with
  | FxRecordedBase events => audit_work events + fx_declared_primitive_budget EC events
  | FxRecordedRead _ c _ lookup_code _ _ _ _ _ set_code _ _ =>
      20 + 6 * Pos.size_nat lookup_code + 17 * Pos.size_nat set_code +
        16 * Pos.size_nat (encode EC c)
  | FxRecordedReaders _ _ code _ _ set _ _ =>
      8 + 6 * Pos.size_nat code + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxRecordedWrite _ code _ _ _ _ => 2 + 17 * Pos.size_nat code
  | FxRecordedCompare _ _ _ => 1
  | FxRecordedCase _ => 1
  end.

Definition fx_recorded_budget (events : list (fx_recorded_event X C A)) : nat :=
  fold_right (fun event total => fx_recorded_event_budget event + total) 0 events.

(** Base worklist events are kept in execution order for concrete pop and RHS counts. *)
Fixpoint fx_recorded_base_calls (events : list (fx_recorded_event X C A)) :
    list (fx_declared_call X C A) :=
  match events with
  | [] => []
  | FxRecordedBase base :: rest => audit_calls base ++ fx_recorded_base_calls rest
  | _ :: rest => fx_recorded_base_calls rest
  end.

(** The actual run meets operand-derived work and fuel bounds on that very execution. *)
Definition fx_recorded_model_cost_statement : Prop :=
  forall fuel,
    let '(result, events) := run_worklist_recorded_model fuel in
    result = run_worklist EX EC L sch mode S Recorded fuel /\
    fx_recorded_work events <= fx_recorded_budget events /\
    List.length (filter (fun call => match call with
      | FxPop _ _ _ => true | _ => false end) (fx_recorded_base_calls events)) <= Pos.to_nat fuel /\
    List.length (filter (fun call => match call with
      | FxRhs _ _ => true | _ => false end) (fx_recorded_base_calls events)) <= Pos.to_nat fuel.

(** A successful query creates exactly one recorded successor engine state. *)
Definition fx_recorded_successor_count_statement : Prop :=
  forall fuel,
    let '(_, events) := run_worklist_recorded_model fuel in
    List.length (filter (fun event => match event with
      | FxRecordedCase 8 => true | _ => false end) events) =
    List.length (filter (fun call => match call with
      | FxRhs _ _ => true | _ => false end) (fx_recorded_base_calls events)).

End RecordedEngine.
```

## Galois.Fixpoint.FixpointAuditRecordedBudget

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditRecordedBudget.v`.

```rocq
(** * Recorded-reader worklist input budget

    The recurrence follows the actual recorded map, intermediate states and duplicate reads;
    its evaluation is a mathematical observation outside the claimed source operation.
    Builds on FixpointRecordedModel and the declared queue/query budgets. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklistBudget FixpointAuditRecorded.
Import List.ListNotations.

Fixpoint fx_record_reads_input_budget {X C} (EX : encoding X) (EC : encoding C) (c : C)
    (reads : list X) : nat :=
  match reads with
  | [] => 1
  | x :: rest => 21 + 23 * Pos.size_nat (encode EX x) + 16 * Pos.size_nat (encode EC c) +
      fx_record_reads_input_budget EX EC c rest
  end.
Definition fx_recorded_update_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (recorded : Map.t X (FinSet.t C)) (update : X * A) (state : assignment X A * PQueue.t C) : nat
  :=
  let '(x, value) := update in let '(m, q) := state in
  let old := lookup EX L m x in
  fx_fullcheck_lookup_input_budget EX x + 2 +
  if leb L value old then 0 else
    let set := recorded_at EX recorded x in
    4 + (2 + 17 * Pos.size_nat (encode EX x)) +
      (8 + 6 * Pos.size_nat (encode EX x) + 19 * audit_trie_nodes set + audit_trie_output_bits set)
  +
      fx_declared_enqueue_input_budget EC sch S (FinSet.elements set) q.
Fixpoint fx_recorded_updates_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (recorded : Map.t X (FinSet.t C)) (updates : list (X * A))
    (state : assignment X A * PQueue.t C) : nat :=
  match updates with
  | [] => 1
  | update :: rest =>
      1 + fx_recorded_update_input_budget EX EC L sch mode S recorded update state +
      fx_recorded_updates_input_budget EX EC L sch mode S recorded rest
        (engine_update EX EC L sch mode S Recorded recorded update state)
  end.
Definition fx_recorded_step_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (state : Engine.t X C A) : nat :=
  fx_declared_pop_input_budget EC (Engine.queue state) + 1 +
  match PQueue.pop EC (Engine.queue state) with
  | None => 0
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(value, reads, sides) := Query.run rhs (lookup EX L (Engine.current state)) in
      let recorded := record_reads EX EC c reads (Engine.recorded state) in
      3 + fx_fullcheck_query_input_budget EX L (Engine.current state) rhs +
        fx_record_reads_input_budget EX EC c reads +
        fx_recorded_updates_input_budget EX EC L sch mode S recorded
          ((System.target S c, value) :: sides) (Engine.current state, queue)
  end.
Fixpoint fx_recorded_loop_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (fuel : positive) (state : Engine.t X C A) : nat :=
  let step := step_outcome EX EC L sch mode S Recorded in
  match fuel with
  | xH => 1 + fx_recorded_step_input_budget EX EC L sch mode S state
  | xO smaller =>
      2 + fx_recorded_loop_input_budget EX EC L sch mode S smaller state +
      match loop step smaller state with
      | Done _ => 0
      | Pending next => fx_recorded_loop_input_budget EX EC L sch mode S smaller next
      end
  | xI smaller =>
      let first := loop step smaller state in
      let second := match first with Done values => Done values | Pending next => loop step smaller
  next end in
      3 + fx_recorded_loop_input_budget EX EC L sch mode S smaller state +
      (match first with Done _ => 0 | Pending next =>
        fx_recorded_loop_input_budget EX EC L sch mode S smaller next end) +
      match second with Done _ => 0 | Pending next => fx_recorded_step_input_budget EX EC L sch mode
  S next end
  end.
Definition fx_recorded_run_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A) (fuel : positive) :
  nat :=
  let queue := enqueue EC sch S (System.constraints S) PQueue.empty in
  fx_declared_enqueue_input_budget EC sch S (System.constraints S) PQueue.empty +
    2 + fx_recorded_loop_input_budget EX EC L sch mode S fuel (Engine.State Map.empty queue
  Map.empty).
Definition fx_recorded_run_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) fuel,
    let '(out, events) := run_worklist_recorded_model EX EC L sch mode S fuel in
    out = run_worklist EX EC L sch mode S Recorded fuel /\
    fx_recorded_work EC events <= fx_recorded_run_input_budget EX EC L sch mode S fuel.
```

## Galois.Fixpoint.FixpointAuditRecordedCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditRecordedCallbacks.v`.

```rocq
(** Recorded-reader source receipts, including duplicate reads and both map encodings.
    Individual callback laws remain external obligations; no whole-work assumption. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditRecorded FixpointAuditRecordedBudget.
Import List.ListNotations.
Definition fx_recorded_set_entries {C} (events : list (audit_set_event C (fx_encoder_entry C))) :
  list (fx_encoder_entry C) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
      AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => [] end) events.
Definition fx_recorded_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_recorded_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxRecordedBase events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxRecordedRead x _ _ code _ _ _ _ add_events set_code _ _ =>
      exists lookup_body add_bodies set_body,
        bodies = [lookup_body] ++ add_bodies ++ [set_body] /\
        fx_source_encode_x source x code lookup_body /\
        Forall2 (fx_queue_encoder_source source) (fx_recorded_set_entries add_events) add_bodies /\
        fx_source_encode_x source x set_code set_body
  | FxRecordedReaders x _ code _ _ _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxRecordedWrite x code _ _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxRecordedCompare value old unchanged =>
      exists body, bodies = [body] /\ fx_source_leb source value old unchanged body
  | FxRecordedCase _ => bodies = []
  end.
Definition fx_recorded_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (events : list (fx_recorded_event X C A)) (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_recorded_event_source source) events bodies.
Definition fx_recorded_event_external_budget {X C A B} (budget : fx_declared_callback_budget X C A
  B)
    (event : fx_recorded_event X C A) : nat :=
  match event with
  | FxRecordedBase events => fx_declared_external_trace_budget budget events
  | FxRecordedRead x _ _ _ _ _ _ _ add_events _ _ _ =>
      2 * fx_budget_encode_x budget x +
      fold_right (fun e n => fx_queue_entry_budget budget e + n) 0 (fx_recorded_set_entries
  add_events)
  | FxRecordedReaders x _ _ _ _ _ _ _ | FxRecordedWrite x _ _ _ _ _ => fx_budget_encode_x budget x
  | FxRecordedCompare value old _ => fx_budget_leb budget value old
  | FxRecordedCase _ => 0
  end.
Definition fx_recorded_external_trace_budget {X C A B} (budget : fx_declared_callback_budget X C A
  B)
    (events : list (fx_recorded_event X C A)) : nat :=
  fold_right (fun event n => fx_recorded_event_external_budget budget event + n) 0 events.
Definition fx_recorded_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) fuel
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_declared_source_laws EX EC L sch S source -> fx_declared_callback_bounded source budget ->
    let '(out, events) := run_worklist_recorded_model EX EC L sch mode S fuel in
    exists bodies,
      fx_recorded_trace_source source events bodies /\
      out = run_worklist EX EC L sch mode S Recorded fuel /\
      fx_recorded_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_recorded_run_input_budget EX EC L sch mode S fuel + fx_recorded_external_trace_budget
  budget events.
```

## Galois.Fixpoint.FixpointAuditSchedule

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditSchedule.v`.

```rocq
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphDfs GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSchedule.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditCompare
  CollectionsAuditEncoding.
Import List.ListNotations.

Inductive audit_rpo_schedule_event (V B : Type) : Type :=
| RpoScheduleCase : nat -> audit_rpo_schedule_event V B
| RpoScheduleNext : positive -> positive -> list audit_nat_encoding_event ->
  audit_rpo_schedule_event V B
| RpoScheduleMap : audit_map_event V positive B -> audit_rpo_schedule_event V B
| RpoScheduleSet : audit_set_event V B -> audit_rpo_schedule_event V B.
Arguments RpoScheduleCase {V B} _.
Arguments RpoScheduleNext {V B} _ _ _.
Arguments RpoScheduleMap {V B} _.
Arguments RpoScheduleSet {V B} _.

Fixpoint audit_rpo_schedule_positions {V B} (enc : V -> positive * list B) (vertices : list V) (next
  : positive)
    : Map.t V positive * list (audit_rpo_schedule_event V B) :=
  match vertices with
  | [] => (Map.empty, [RpoScheduleCase 0])
  | v :: rest => let '(next', successor_events) := audit_positive_succ next in
      let '(middle, events) := audit_rpo_schedule_positions enc rest next' in
      let '(result, writes) := audit_map_set enc v next middle in
      (result, [RpoScheduleCase 1; RpoScheduleNext next next' successor_events] ++ events ++ map
  RpoScheduleMap writes)
  end.

Definition audit_rpo_schedule_priority {V B} (enc : V -> positive * list B) (positions : Map.t V
  positive) (v : V)
    : positive * list (audit_rpo_schedule_event V B) :=
  let '(found, reads) := audit_map_get enc v positions in
  (match found with Some rank => rank | None => 1%positive end, map RpoScheduleMap reads).

Definition audit_rpo_schedule_widening {V B} (enc : V -> positive * list B) (heads : FinSet.t V) (v
  : V)
    : bool * list (audit_rpo_schedule_event V B) :=
  let '(result, events) := audit_finset_mem enc v heads in (result, map RpoScheduleSet events).

Definition audit_rpo_schedule_positions_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) vertices next,
    (forall v, fst (enc v) = encode EV v) ->
    fst (audit_rpo_schedule_positions enc vertices next) = schedule_positions EV vertices next.

Definition audit_rpo_schedule_callbacks_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) positions heads v,
    (forall x, fst (enc x) = encode EV x) ->
    fst (audit_rpo_schedule_priority enc positions v) = schedule_priority EV positions v /\
    fst (audit_rpo_schedule_widening enc heads v) = FinSet.mem EV v heads.

Record audit_rpo_graph_callbacks (V E B : Type) : Type := AuditRpoGraphCallbacks {
  audit_rpo_graph_encode : V -> positive * list B;
  audit_rpo_graph_out : V -> list E * list B;
  audit_rpo_graph_source : E -> V * list B;
  audit_rpo_graph_target : E -> V * list B
}.
Arguments audit_rpo_graph_encode {V E B} _ _.
Arguments audit_rpo_graph_out {V E B} _ _.
Arguments audit_rpo_graph_source {V E B} _ _.
Arguments audit_rpo_graph_target {V E B} _ _.

Inductive audit_rpo_graph_event (V E B : Type) : Type :=
| RpoGraphCase : nat -> audit_rpo_graph_event V E B
| RpoGraphOut : V -> list E -> list B -> audit_rpo_graph_event V E B
| RpoGraphSource : E -> V -> list B -> audit_rpo_graph_event V E B
| RpoGraphTarget : E -> V -> list B -> audit_rpo_graph_event V E B
| RpoGraphRank : audit_map_event V positive B -> audit_rpo_graph_event V E B
| RpoGraphSet : audit_set_event V B -> audit_rpo_graph_event V E B
| RpoGraphCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
  audit_rpo_graph_event V E B.
Arguments RpoGraphCase {V E B} _.
Arguments RpoGraphOut {V E B} _ _ _.
Arguments RpoGraphSource {V E B} _ _ _.
Arguments RpoGraphTarget {V E B} _ _ _.
Arguments RpoGraphRank {V E B} _.
Arguments RpoGraphSet {V E B} _.
Arguments RpoGraphCompare {V E B} _ _ _ _.

Definition audit_rpo_graph_ancestor {V E B} (enc : V -> positive * list B) (r : dfs_result V E) (u v
  : V)
    : bool * list (audit_rpo_graph_event V E B) :=
  let '(a, ea) := audit_map_get enc u (pre_num r) in
  match a with None => (false, map RpoGraphRank ea) | Some av =>
    let '(b, eb) := audit_map_get enc v (pre_num r) in
    match b with None => (false, map RpoGraphRank (ea ++ eb)) | Some bv =>
      let '(c, ec) := audit_map_get enc u (post_num r) in
      match c with None => (false, map RpoGraphRank (ea ++ eb ++ ec)) | Some cv =>
        let '(d, ed) := audit_map_get enc v (post_num r) in
        match d with None => (false, map RpoGraphRank (ea ++ eb ++ ec ++ ed)) | Some dv =>
          let '(first, ef) := audit_positive_leb av bv in let '(second, es) := audit_positive_leb dv
  cv in
          (first && second, map RpoGraphRank (ea ++ eb ++ ec ++ ed) ++
            [RpoGraphCompare av bv first ef; RpoGraphCompare dv cv second es])
        end
      end
    end
  end.

Fixpoint audit_rpo_graph_filter {V E B} (cb : audit_rpo_graph_callbacks V E B) (r : dfs_result V E)
  (edges : list E)
    : list E * list (audit_rpo_graph_event V E B) :=
  match edges with
  | [] => ([], [RpoGraphCase 0])
  | edge :: rest => let '(target, tb) := audit_rpo_graph_target cb edge in
      let '(source, sb) := audit_rpo_graph_source cb edge in
      let '(keep, checks) := audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r target source in
      let '(later, events) := audit_rpo_graph_filter cb r rest in
      (if keep then edge :: later else later,
        [RpoGraphCase 1; RpoGraphTarget edge target tb; RpoGraphSource edge source sb] ++ checks ++
  events)
  end.

Fixpoint audit_rpo_graph_targets {V E B} (cb : audit_rpo_graph_callbacks V E B) (edges : list E)
    : list V * list (audit_rpo_graph_event V E B) :=
  match edges with
  | [] => ([], [RpoGraphCase 2])
  | edge :: rest => let '(target, body) := audit_rpo_graph_target cb edge in
      let '(later, events) := audit_rpo_graph_targets cb rest in
      (target :: later, RpoGraphCase 3 :: RpoGraphTarget edge target body :: events)
  end.

Fixpoint audit_rpo_graph_collect {V E B} (cb : audit_rpo_graph_callbacks V E B) (r : dfs_result V E)
  (vertices : list V)
    : list V * list (audit_rpo_graph_event V E B) :=
  match vertices with
  | [] => ([], [RpoGraphCase 4])
  | v :: rest => let '(outgoing, body) := audit_rpo_graph_out cb v in
      let '(retreats, checks) := audit_rpo_graph_filter cb r outgoing in
      let '(targets, target_events) := audit_rpo_graph_targets cb retreats in
      let '(later, events) := audit_rpo_graph_collect cb r rest in
      (targets ++ later, [RpoGraphCase 5; RpoGraphOut v outgoing body] ++ checks ++ target_events ++
  events)
  end.

Fixpoint audit_rpo_graph_add_all {V E B} (enc : V -> positive * list B) (vertices : list V) (heads :
  FinSet.t V)
    : FinSet.t V * list (audit_rpo_graph_event V E B) :=
  match vertices with
  | [] => (heads, [RpoGraphCase 6])
  | v :: rest => let '(next, events) := audit_finset_add enc v heads in
      let '(result, later) := audit_rpo_graph_add_all enc rest next in
      (result, RpoGraphCase 7 :: map RpoGraphSet events ++ later)
  end.

Definition audit_rpo_schedule_retreats {V E B} (cb : audit_rpo_graph_callbacks V E B)
    (g : Graph.t V E) (r : dfs_result V E) : FinSet.t V * list (audit_rpo_graph_event V E B) :=
  let '(vertices, events) := audit_rpo_graph_collect cb r (Graph.nodes g) in
  let '(result, adds) := audit_rpo_graph_add_all (audit_rpo_graph_encode cb) vertices FinSet.empty
  in
  (result, events ++ adds).

Definition audit_rpo_graph_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) : Prop :=
  (forall v, fst (audit_rpo_graph_encode cb v) = encode EV v) /\
  (forall v, fst (audit_rpo_graph_out cb v) = Graph.out g v) /\
  (forall e, fst (audit_rpo_graph_source cb e) = Graph.source g e) /\
  (forall e, fst (audit_rpo_graph_target cb e) = Graph.target g e).

Definition audit_rpo_schedule_retreats_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (cb :
  audit_rpo_graph_callbacks V E B),
    audit_rpo_graph_callbacks_erase EV g cb -> fst (audit_rpo_schedule_retreats cb g r) =
  schedule_retreats EV g r.

Definition audit_rpo_schedule_event_work {V B} (weight : B -> nat) (event : audit_rpo_schedule_event
  V B) : nat :=
  let body := fun es => fold_right (fun item n => weight item + n) 0 es in
  64 + match event with
  | RpoScheduleMap item => audit_map_source_work body [item]
  | RpoScheduleSet item => audit_finset_source_work body [item]
  | RpoScheduleNext _ _ events => 2 * length events
  | RpoScheduleCase _ => 0
  end.

Definition audit_rpo_graph_event_work {V E B} (weight : B -> nat) (event : audit_rpo_graph_event V E
  B) : nat :=
  let body := fun es => fold_right (fun item n => weight item + n) 0 es in
  64 + match event with
  | RpoGraphOut _ _ es | RpoGraphSource _ _ es | RpoGraphTarget _ _ es => body es
  | RpoGraphRank item => audit_map_source_work body [item]
  | RpoGraphSet item => audit_finset_source_work body [item]
  | RpoGraphCompare _ _ _ events => audit_positive_order_source_work events
  | RpoGraphCase _ => 0
  end.

Definition audit_rpo_schedule_event_body {V B} (weight : B -> nat) (event : audit_rpo_schedule_event
  V B) : nat :=
  match event with
  | RpoScheduleMap (AuditMapGet _ _ _ _ body _) | RpoScheduleMap (AuditMapSet _ _ _ _ _ body _) |
    RpoScheduleMap (AuditMapRemove _ _ _ _ body _) | RpoScheduleSet (AuditSetMem _ _ _ _ body _) |
    RpoScheduleSet (AuditSetAdd _ _ _ _ body _) | RpoScheduleSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | RpoScheduleSet (AuditSetFold _ _) | RpoScheduleNext _ _ _ | RpoScheduleCase _ => 0
  end.

Definition audit_rpo_graph_event_body {V E B} (weight : B -> nat) (event : audit_rpo_graph_event V E
  B) : nat :=
  match event with
  | RpoGraphOut _ _ body | RpoGraphSource _ _ body | RpoGraphTarget _ _ body |
    RpoGraphRank (AuditMapGet _ _ _ _ body _) | RpoGraphRank (AuditMapSet _ _ _ _ _ body _) |
    RpoGraphRank (AuditMapRemove _ _ _ _ body _) | RpoGraphSet (AuditSetMem _ _ _ _ body _) |
    RpoGraphSet (AuditSetAdd _ _ _ _ body _) | RpoGraphSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | RpoGraphSet (AuditSetFold _ _) | RpoGraphCompare _ _ _ _ | RpoGraphCase _ => 0
  end.

Definition audit_rpo_schedule_work {V B} (weight : B -> nat) (events : list
  (audit_rpo_schedule_event V B)) : nat :=
  fold_right (fun event n => audit_rpo_schedule_event_work weight event + n) 0 events.
Definition audit_rpo_schedule_body_work {V B} (weight : B -> nat) (events : list
  (audit_rpo_schedule_event V B)) : nat :=
  fold_right (fun event n => audit_rpo_schedule_event_body weight event + n) 0 events.
Definition audit_rpo_graph_work {V E B} (weight : B -> nat) (events : list (audit_rpo_graph_event V
  E B)) : nat :=
  fold_right (fun event n => audit_rpo_graph_event_work weight event + n) 0 events.
Definition audit_rpo_graph_body_work {V E B} (weight : B -> nat) (events : list
  (audit_rpo_graph_event V E B)) : nat :=
  fold_right (fun event n => audit_rpo_graph_event_body weight event + n) 0 events.

Definition audit_rpo_positions_budget {V} (EV : encoding V) (vertices : list V) (next : positive) :
  nat :=
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  256 * S (length vertices) * (128 + 32 * width + Pos.size_nat next + length vertices).

Definition audit_rpo_graph_budget {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) :
  nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ map (Graph.source g) edges ++ map (Graph.target g) edges ++
    map fst (Map.elements (pre_num r)) ++ map fst (Map.elements (post_num r)) in
  let numbers := map snd (Map.elements (pre_num r)) ++ map snd (Map.elements (post_num r)) in
  let width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map Pos.size_nat numbers)) in
  4096 * S (length (Graph.nodes g) + length edges) * S (length (Graph.nodes g) + length edges) *
  (128 + 32 * width).

Definition audit_rpo_positions_bound_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) vertices next,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_rpo_schedule_positions enc vertices next in
    result = schedule_positions EV vertices next /\
    audit_rpo_schedule_work weight events <= audit_rpo_positions_budget EV vertices next +
      audit_rpo_schedule_body_work weight events.

Definition audit_rpo_retreats_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (cb : audit_rpo_graph_callbacks V E B) (weight : B -> nat),
    audit_rpo_graph_callbacks_erase EV g cb ->
    let '(result, events) := audit_rpo_schedule_retreats cb g r in
    result = schedule_retreats EV g r /\
    audit_rpo_graph_work weight events <= audit_rpo_graph_budget EV g r + audit_rpo_graph_body_work
  weight events.

Definition audit_rpo_schedule_query_bound_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) positions heads v,
    (forall x, fst (enc x) = encode EV x) ->
    let '(priority, priority_events) := audit_rpo_schedule_priority enc positions v in
    let '(widening, widening_events) := audit_rpo_schedule_widening enc heads v in
    priority = schedule_priority EV positions v /\ widening = FinSet.mem EV v heads /\
    audit_rpo_schedule_work weight priority_events + audit_rpo_schedule_work weight widening_events
  <=
      512 + 32 * Pos.size_nat (encode EV v) + audit_rpo_schedule_body_work weight priority_events +
        audit_rpo_schedule_body_work weight widening_events.

(** One generic adapter applies to each genuinely external callback signature. *)
Definition audit_rpo_schedule_event_budget {V B} (budget : V -> nat) (event :
  audit_rpo_schedule_event V B) : nat :=
  match event with
  | RpoScheduleMap (AuditMapGet key _ _ _ _ _) | RpoScheduleMap (AuditMapSet key _ _ _ _ _ _) |
    RpoScheduleMap (AuditMapRemove key _ _ _ _ _) | RpoScheduleSet (AuditSetMem key _ _ _ _ _) |
    RpoScheduleSet (AuditSetAdd key _ _ _ _ _) | RpoScheduleSet (AuditSetRemove key _ _ _ _ _) =>
  budget key
  | RpoScheduleSet (AuditSetFold _ _) | RpoScheduleNext _ _ _ | RpoScheduleCase _ => 0
  end.

Definition audit_rpo_graph_event_budget {V E B} (encode_budget : V -> nat) (out_budget : V -> nat)
    (source_budget target_budget : E -> nat) (event : audit_rpo_graph_event V E B) : nat :=
  match event with
  | RpoGraphOut v _ _ => out_budget v
  | RpoGraphSource e _ _ => source_budget e
  | RpoGraphTarget e _ _ => target_budget e
  | RpoGraphRank (AuditMapGet key _ _ _ _ _) | RpoGraphRank (AuditMapSet key _ _ _ _ _ _) |
    RpoGraphRank (AuditMapRemove key _ _ _ _ _) | RpoGraphSet (AuditSetMem key _ _ _ _ _) |
    RpoGraphSet (AuditSetAdd key _ _ _ _ _) | RpoGraphSet (AuditSetRemove key _ _ _ _ _) =>
  encode_budget key
  | RpoGraphSet (AuditSetFold _ _) | RpoGraphCompare _ _ _ _ | RpoGraphCase _ => 0
  end.

Definition audit_rpo_positions_adapted_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat)
    source budget vertices next,
    (forall v, fst (enc v) = encode EV v) -> audit_graph_external_callback_adapter enc weight source
  budget ->
    let '(result, events) := audit_rpo_schedule_positions enc vertices next in
    result = schedule_positions EV vertices next /\
    audit_rpo_schedule_work weight events <= audit_rpo_positions_budget EV vertices next +
      fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0 events.

Definition audit_rpo_retreats_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (cb : audit_rpo_graph_callbacks V E B) (weight : B -> nat)
    encode_source out_source source_source target_source encode_budget out_budget source_budget
  target_budget,
    audit_rpo_graph_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_rpo_graph_encode cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_rpo_graph_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (audit_rpo_graph_source cb) weight source_source
  source_budget ->
    audit_graph_external_callback_adapter (audit_rpo_graph_target cb) weight target_source
  target_budget ->
    let '(result, events) := audit_rpo_schedule_retreats cb g r in
    result = schedule_retreats EV g r /\
    audit_rpo_graph_work weight events <= audit_rpo_graph_budget EV g r +
      fold_right (fun event n => audit_rpo_graph_event_budget encode_budget out_budget source_budget
  target_budget event + n) 0 events.

Definition audit_rpo_successor_source_obligations : Prop :=
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement.
```

## Galois.Fixpoint.FixpointAuditScheduleWrapper

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditScheduleWrapper.v`.

```rocq
(** RPO scheduler preparation using the actual counted index, dependency out bodies,
    graph preparation, DFS, positions and retreating-edge traversal. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditSchedule.
Import List.ListNotations.
Inductive fx_dep_event (X C B : Type) :=
  | FxDepIndexEvent (event : fx_index_nested_event X C B)
  | FxDepEncode (input : X) (code : positive) (body : list B)
  | FxDepCase (site : nat)
  | FxDepListWork (size : nat).
Arguments FxDepIndexEvent {X C B} _.
Arguments FxDepEncode {X C B} _ _ _.
Arguments FxDepCase {X C B} _.
Arguments FxDepListWork {X C B} _.
Fixpoint fx_dep_unknowns_input {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    list X * list (fx_dep_event X C B) :=
  match cs with
  | [] => ([], [FxDepCase 0])
  | c :: rest =>
      let '(target, tb) := fxi_target cb c in let '(deps, db) := fxi_deps cb c in
      let '(sides, sb) := fxi_sides cb c in
      let '(tail, events) := fx_dep_unknowns_input cb rest in
      (target :: deps ++ sides ++ tail,
       FxDepCase 0 :: FxDepIndexEvent (FxiTarget c target tb) ::
       FxDepIndexEvent (FxiDeps c deps db) :: FxDepIndexEvent (FxiSides c sides sb) ::
       FxDepListWork (length deps) :: events ++ [FxDepListWork (1 + length deps + length sides)])
  end.
Fixpoint fx_dep_outputs_input {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    list X * list (fx_dep_event X C B) :=
  match cs with
  | [] => ([], [FxDepCase 1])
  | c :: rest =>
      let '(target, tb) := fxi_target cb c in let '(sides, sb) := fxi_sides cb c in
      let '(tail, events) := fx_dep_outputs_input cb rest in
      (target :: sides ++ tail, FxDepCase 1 :: FxDepIndexEvent (FxiTarget c target tb) ::
        FxDepIndexEvent (FxiSides c sides sb) :: events ++ [FxDepListWork (1 + length sides)])
  end.
Definition fx_dep_out {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C) (y : X) :
    list (X * X) * list (fx_dep_event X C B) :=
  let '(code, encbody) := fxi_encode cb y in
  let '(raw, triebody) := audit_map_code_get code (readers ix) in
  let constraints := match raw with Some found => found | None => [] end in
  let '(values, bodies) := fx_dep_outputs_input cb constraints in
  let '(distinct, distinct_events) := fxi_distinct_counted cb values in
  (map (fun x => (y, x)) distinct,
    FxDepCase 2 :: FxDepIndexEvent (FxiRead y code (readers ix) raw encbody triebody) ::
      bodies ++ map FxDepIndexEvent distinct_events ++ [FxDepListWork (length distinct); FxDepCase
  3]).
Definition fx_dep_graph_build {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
    Graph.t X (X * X) * sys_index X C * list (fx_dep_event X C B) :=
  let '(input, input_events) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(vertices, distinct_events) := fxi_distinct_counted cb input in
  let '(ix, index_events) := fx_index_nested_counted S cb in
  ({| Graph.entries := vertices; Graph.nodes := vertices;
      Graph.out := fun y => map (fun x => (y, x)) (distinct_unknowns EX
        (flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y)));
      Graph.source := fst; Graph.target := snd |}, ix,
   input_events ++ map FxDepIndexEvent distinct_events ++ map FxDepIndexEvent index_events).
Definition fx_dep_encoder {X C B} (cb : fx_index_external_model X C B) (x : X) :
    positive * list (fx_dep_event X C B) :=
  let '(code, body) := fxi_encode cb x in (code, [FxDepEncode x code body]).
Definition fx_dep_prepare_cb {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C) :
    audit_prepare_callback_model X (X * X) (fx_dep_event X C B) :=
  AuditPrepareCallbackModel X (X * X) (fx_dep_event X C B)
    (fx_dep_out cb ix) (fun e => (snd e, [FxDepCase 4])) (fx_dep_encoder cb).
Definition fx_dep_dfs_cb {X C B} (cb : fx_index_external_model X C B) :
    audit_dfs_callback_model X (X * X) (fx_dep_event X C B) :=
  AuditDfsCallbackModel X (X * X) (fx_dep_event X C B)
    (fun e => (snd e, [FxDepCase 5])) (fx_dep_encoder cb).
Definition fx_dep_rpo_cb {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C) :
    audit_rpo_graph_callbacks X (X * X) (fx_dep_event X C B) :=
  AuditRpoGraphCallbacks X (X * X) (fx_dep_event X C B) (fx_dep_encoder cb)
    (fx_dep_out cb ix) (fun e => (fst e, [FxDepCase 6])) (fun e => (snd e, [FxDepCase 7])).
Definition fx_dep_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_dep_event X C B) : nat :=
  16 + match event with
  | FxDepIndexEvent nested => fxi_event_work ib nested
  | FxDepEncode _ _ body => fxi_body_work ib body
  | FxDepCase _ => 0
  | FxDepListWork size => 1 + size end.
Definition fx_dep_events_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_dep_event X C B)) : nat :=
  fold_right (fun event n => fx_dep_event_work ib event + n) 0 events.
Definition fx_dep_build_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let '(g, ix, _) := fx_dep_graph_build EX S SS cb in
    g = dependency_graph EX S SS /\ ix = index_system EX S SS.
Definition fx_dep_out_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) ix y,
    fx_index_external_erases EX S SS cb ->
    fst (fx_dep_out cb ix y) =
      map (fun x => (y, x)) (distinct_unknowns EX
        (flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y))).

Record fx_rpo_result (X C B : Type) := FxRpoResult {
  fx_rpo_positions : Map.t X positive;
  fx_rpo_heads : FinSet.t X;
  fx_rpo_reverse_input : list X;
  fx_rpo_reverse_output : list X;
  fx_rpo_reverse_work : nat;
  fx_rpo_build_events : list (fx_dep_event X C B);
  fx_rpo_prepare_events : list (audit_prepare_source_event X (X * X) (fx_dep_event X C B));
  fx_rpo_dfs_events : list (audit_dfs_nested_event X (X * X)
    (audit_graph_callback_capture X (X * X) (fx_dep_event X C B)));
  fx_rpo_position_events : list (audit_rpo_schedule_event X (fx_dep_event X C B));
  fx_rpo_retreat_events : list (audit_rpo_graph_event X (X * X) (fx_dep_event X C B))
}.
Arguments FxRpoResult {X C B} _ _ _ _ _ _ _ _ _ _.
Arguments fx_rpo_positions {X C B} _.
Arguments fx_rpo_heads {X C B} _.
Arguments fx_rpo_reverse_input {X C B} _.
Arguments fx_rpo_reverse_output {X C B} _.
Arguments fx_rpo_reverse_work {X C B} _.
Arguments fx_rpo_build_events {X C B} _.
Arguments fx_rpo_prepare_events {X C B} _.
Arguments fx_rpo_dfs_events {X C B} _.
Arguments fx_rpo_position_events {X C B} _.
Arguments fx_rpo_retreat_events {X C B} _.
Definition fx_rpo_scheduler_counted {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) : fx_rpo_result X C B :=
  let '(g, ix, build) := fx_dep_graph_build EX S SS cb in
  let '(p, prepare_events) := audit_prepare_source_counted EX g (fx_dep_prepare_cb cb ix) in
  let '(search, dfs_events) := audit_dfs_source_counted p (fx_dep_dfs_cb cb) FinSet.empty
  (Graph.entries g) in
  let '(order, reverse_work) := audit_graph_reverse_fast_counted (postorder search) [] in
  let '(positions, position_events) := audit_rpo_schedule_positions (fx_dep_encoder cb) order 1 in
  let '(heads, retreat_events) := audit_rpo_schedule_retreats (fx_dep_rpo_cb cb ix) g search in
  FxRpoResult positions heads (postorder search) order reverse_work
    build prepare_events dfs_events position_events retreat_events.
Definition fx_rpo_scheduler_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    forall x,
      fst (audit_rpo_schedule_priority (fx_dep_encoder cb) (fx_rpo_positions result) x) =
        priority (rpo_scheduler EX S SS) x /\
      fst (audit_rpo_schedule_widening (fx_dep_encoder cb) (fx_rpo_heads result) x) =
        widening_point (rpo_scheduler EX S SS) x.
Definition fx_rpo_scheduler_work {X C B} (ib : fx_index_external_budget X C B)
    (result : fx_rpo_result X C B) : nat :=
  fx_dep_events_work ib (fx_rpo_build_events result) + fx_rpo_reverse_work result +
  audit_prepare_source_work (fx_dep_event_work ib) (fx_rpo_prepare_events result) +
  audit_dfs_source_work (fx_dep_event_work ib) (fx_rpo_dfs_events result) +
  audit_rpo_schedule_work (fx_dep_event_work ib) (fx_rpo_position_events result) +
  audit_rpo_graph_work (fx_dep_event_work ib) (fx_rpo_retreat_events result).

(** Source-intermediate budgets use the real operands, not a caller-supplied global bound. *)
Definition fx_dep_unknowns_native {X C A} (S : System.t X C A) (SS : System.static S) : list X :=
  flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c) (System.constraints S).
Definition fx_dep_out_values_native {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (y : X) : list X :=
  flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y).
Definition fx_dep_callback_budget {X C B} (ib : fx_index_external_budget X C B) (cs : list C) : nat
  :=
  fold_right (fun c n => fxi_target_bound ib c + fxi_deps_bound ib c + fxi_sides_bound ib c + n) 0
  cs.
Definition fx_dep_build_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let cs := System.constraints S in let input := fx_dep_unknowns_native S SS in
  1024 * (1 + length cs + length input) + fx_dep_callback_budget ib cs +
    fxi_distinct_input_budget EX ib input + fx_index_nested_input_budget EX S SS ib.
Definition fx_dep_out_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B) (y : X) : nat
  :=
  let cs := readers_of EX ix y in let values := fx_dep_out_values_native EX S SS ix y in
  1024 * (1 + length cs + length values) + fx_dep_callback_budget ib cs +
    32 * Pos.size_nat (encode EX y) + fxi_encode_bound ib y + fxi_distinct_input_budget EX ib
  values.
Definition fx_dep_build_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(_, _, events) := fx_dep_graph_build EX S SS cb in
    fx_dep_events_work ib events <= fx_dep_build_budget EX S SS ib.
Definition fx_dep_out_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B) ix y,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_events_work ib (snd (fx_dep_out cb ix y)) <= fx_dep_out_budget EX S SS ix ib y.
Definition fx_rpo_callback_max {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let g := dependency_graph EX S SS in let ix := index_system EX S SS in
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map fst edges ++ map snd edges in
  64 + fold_right (fun x n => Nat.max n
    (fx_dep_out_budget EX S SS ix ib x + fxi_encode_bound ib x)) 0 vertices.
Definition fx_rpo_receipt_count_limit {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : nat :=
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let search := dfs p FinSet.empty (Graph.entries g) in
  audit_graph_prepare_full_event_bound g + audit_dfs_full_input_event_bound p (Graph.entries g) +
    16 * (1 + length (postorder search)) + audit_rpo_graph_budget EX g search.
Definition fx_rpo_scheduler_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let search := dfs p FinSet.empty (Graph.entries g) in
  let receipt_count := fx_rpo_receipt_count_limit EX S SS in
  fx_dep_build_budget EX S SS ib + audit_prepare_source_budget EX g +
    audit_dfs_source_budget EX g p (Graph.entries g) +
    audit_graph_reverse_fast_work (length (postorder search)) +
    audit_rpo_positions_budget EX (rpo search) 1 +
    audit_rpo_graph_budget EX g search + 64 * (1 + receipt_count) * fx_rpo_callback_max EX S SS ib.
Definition fx_rpo_scheduler_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    fx_rpo_scheduler_work ib result <= fx_rpo_scheduler_budget EX S SS ib.

(** Per-call source rules refer to the actual index client's callback bodies. *)
Definition fx_dep_source_laws {X C B} (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) : Prop :=
  (forall x, let '(out, body) := fxi_encode cb x in fxi_encode_source source x out body) /\
  (forall c, let '(out, body) := fxi_target cb c in fxi_target_source source c out body) /\
  (forall c, let '(out, body) := fxi_sides cb c in fxi_sides_source source c out body) /\
  (forall c, let '(out, body) := fxi_deps cb c in fxi_deps_source source c out body).
Definition fx_dep_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_dep_event X C B) : Prop :=
  match event with
  | FxDepIndexEvent e => fx_index_external_trace_adequacy source [e]
  | FxDepEncode x code body => fxi_encode_source source x code body
  | _ => True
  end.
Definition fx_dep_body_source {X C B} (source : fx_index_external_source X C B)
    (body : list (fx_dep_event X C B)) : Prop := Forall (fx_dep_event_source source) body.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
Definition fx_dep_map_source {X C B A} (source : fx_index_external_source X C B)
    (event : audit_map_event X A (fx_dep_event X C B)) : Prop :=
  match event with
  | AuditMapGet _ _ _ _ body _ | AuditMapSet _ _ _ _ _ body _ |
    AuditMapRemove _ _ _ _ body _ => fx_dep_body_source source body
  end.
Definition fx_dep_set_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_set_event X (fx_dep_event X C B)) : Prop :=
  match event with
  | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
    AuditSetRemove _ _ _ _ body _ => fx_dep_body_source source body
  | AuditSetFold _ _ => True
  end.
Definition fx_dep_prepare_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_prepare_source_event X (X * X) (fx_dep_event X C B)) : Prop :=
  match event with
  | PrepareSourceOut _ _ body | PrepareSourceTarget _ _ body => fx_dep_body_source source body
  | PrepareSourceMap e => fx_dep_map_source source e
  | _ => True
  end.
Definition fx_dep_dfs_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_dfs_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))) : Prop :=
  Forall (fun capture => match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body | AuditGraphEncodeCapture _ _ _ _ _ body =>
        fx_dep_body_source source body end) (snd event).
Definition fx_dep_positions_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_rpo_schedule_event X (fx_dep_event X C B)) : Prop :=
  match event with RpoScheduleMap e => fx_dep_map_source source e
  | RpoScheduleSet e => fx_dep_set_source source e | _ => True end.
Definition fx_dep_retreat_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_rpo_graph_event X (X * X) (fx_dep_event X C B)) : Prop :=
  match event with
  | RpoGraphOut _ _ body | RpoGraphSource _ _ body | RpoGraphTarget _ _ body => fx_dep_body_source
  source body
  | RpoGraphRank e => fx_dep_map_source source e | RpoGraphSet e => fx_dep_set_source source e
  | _ => True end.
Definition fx_rpo_scheduler_source_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (source : fx_index_external_source X C B),
    fx_dep_source_laws cb source ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    fx_dep_body_source source (fx_rpo_build_events result) /\
    Forall (fx_dep_prepare_source source) (fx_rpo_prepare_events result) /\
    Forall (fx_dep_dfs_source source) (fx_rpo_dfs_events result) /\
    Forall (fx_dep_positions_source source) (fx_rpo_position_events result) /\
    Forall (fx_dep_retreat_source source) (fx_rpo_retreat_events result).
Definition fx_rpo_receipt_count_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    length (fx_rpo_prepare_events result) + length (fx_rpo_dfs_events result) +
      length (fx_rpo_position_events result) + length (fx_rpo_retreat_events result) <=
      fx_rpo_receipt_count_limit EX S SS.

(** Prospective source boundary: AUD-GR-DFS implements the equivalent fast `rpo` reverse.
    The unchanged baseline uses `rev`; this model makes no claim that the refactor has landed. *)
Definition fx_rpo_fast_reverse_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    let result := fx_rpo_scheduler_counted EX S SS cb in
    let g := dependency_graph EX S SS in let p := prepare EX g in
    let search := dfs p FinSet.empty (Graph.entries g) in
    fx_rpo_reverse_input result = postorder search /\
    fx_rpo_reverse_output result = rpo search /\
    audit_graph_reverse_fast_run (fx_rpo_reverse_input result) []
      (fx_rpo_reverse_output result) (fx_rpo_reverse_work result) /\
    fx_rpo_reverse_work result = audit_graph_reverse_fast_work (length (postorder search)).
```

## Galois.Fixpoint.FixpointAuditTotal

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditTotal.v`.

```rocq
(** Total solver with the concrete indexed producer and source-witness worklist phases.
    This is a declaration-only candidate. Internal callbacks must be instantiated with
    their actual bodies; no native-runtime or observer-evaluation cost is claimed. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointCycles FixpointWorklist
  FixpointTotal.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Fixpoint Require Import FixpointAuditIndex FixpointAuditWorklist
  FixpointAuditWorklistBudget FixpointAuditWorklistCallbacks.
Import List.ListNotations.
Definition fx_total_weight_bound (n r : nat) : nat :=
  1 + n * Nat.pow (2 + r * n) (S n).
Definition fx_total_queue_bound (n r : nat) : nat :=
  r * (1 + n * fx_total_weight_bound n r).
Definition fx_total_join_step_bound {X C A} {S : System.t X C A}
    (L : lattice A) (H : height L) (SS : System.static S) : nat :=
  let n := length (total_unknowns SS) in
  let r := length (System.constraints S) in
  (1 + n * bound H) * (1 + r).
Definition fx_total_widen_step_bound {X C A} {S : System.t X C A}
    (L : lattice A) (W : widening_rank L) (SS : System.static S) : nat :=
  let n := length (total_unknowns SS) in
  let r := length (System.constraints S) in
  (1 + n * wrank W (bot L)) * (1 + fx_total_queue_bound n r).

Inductive fx_total_callbacks_run {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (cb : fx_index_external_model X C B) : assignment X A -> list (fx_index_nested_event X C B) ->
    audit_trace (fx_declared_call X C A) -> audit_trace (fx_declared_call X C A) -> Prop :=
  | FxTotalCallbacksRun : forall ix index_events queue init_events values engine_events,
      fx_index_nested_counted S cb = (ix, index_events) ->
      fx_model_enqueue EC sch S (System.constraints S) PQueue.empty = (queue, init_events) ->
      fx_declared_total_engine_run EX EC L sch mode S ix
        (Engine.State Map.empty queue Map.empty) values engine_events ->
      fx_total_callbacks_run EX EC L sch mode S cb values index_events init_events engine_events.
Definition fx_total_callbacks_realization_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S)
    (HT : terminates L SS sch mode) (cb : fx_index_external_model X C B),
    fx_index_external_erases EX S SS cb ->
    exists index_events init_events engine_events,
      fx_total_callbacks_run EX EC L sch mode S cb
        (proj1_sig (total_solver_map EX EC L HL sch mode S SS HT)) index_events init_events
  engine_events.
Definition fx_total_callbacks_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S)
    (HT : terminates L SS sch mode) (cb : fx_index_external_model X C B)
    result index_events init_events engine_events,
    fx_index_external_erases EX S SS cb ->
    fx_total_callbacks_run EX EC L sch mode S cb result index_events init_events engine_events ->
    result = proj1_sig (total_solver_map EX EC L HL sch mode S SS HT).

(** The same index, initial queue and engine derivation carry actual per-call source
    receipts. The index receipts refer to the counted producer's exact body observations. *)
Definition fx_total_callbacks_source_statement : Prop :=
  forall X C A BI BW (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C BI) (index_source : fx_index_external_source X C BI)
    (source : fx_declared_callback_source X C A BW)
    result index_events init_events engine_events,
    fx_index_external_erases EX S SS cb ->
    fx_index_external_trace_adequacy index_source index_events ->
    fx_declared_source_laws EX EC L sch S source ->
    fx_total_callbacks_run EX EC L sch mode S cb result index_events init_events engine_events ->
    exists init_bodies engine_bodies,
      fx_declared_trace_source source init_events init_bodies /\
      fx_declared_trace_source source engine_events engine_bodies.
Definition fx_total_callbacks_join_work_statement : Prop :=
  forall X C A BI BW (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (H : height L) (sch : scheduler X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C BI) (index_budget : fx_index_external_budget X C BI)
    (source : fx_declared_callback_source X C A BW) (budget : fx_declared_callback_budget X C A BW)
    result index_events init_events engine_events init_bodies engine_bodies,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb index_budget ->
    fx_declared_callback_bounded source budget ->
    fx_total_callbacks_run EX EC L sch Joining S cb result index_events init_events engine_events ->
    fx_declared_trace_source source init_events init_bodies ->
    fx_declared_trace_source source engine_events engine_bodies ->
    let ix := fst (fx_index_nested_counted S cb) in
    let fuel := Pos.of_succ_nat (fx_total_join_step_bound L H SS) in
    result = proj1_sig (total_solver_map EX EC L HL sch Joining S SS (inhabits H)) /\
    fx_index_adapter_work index_budget index_events + fx_declared_model_work EC init_events +
      fx_declared_model_work EC engine_events + fx_declared_body_work (fx_body_weight budget)
  init_bodies +
      fx_declared_body_work (fx_body_weight budget) engine_bodies <=
      fx_index_nested_input_budget EX S SS index_budget +
      fx_declared_run_input_budget EX EC L sch Joining S SS ix fuel +
      fx_declared_external_trace_budget budget init_events + fx_declared_external_trace_budget
  budget engine_events.
Definition fx_total_callbacks_widen_work_statement : Prop :=
  forall X C A BI BW (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (W : widening_rank L) (sch : scheduler X) (S : System.t X C A) (SS : System.static S)
    (Hcut : cuts_every_cycle SS (widening_point sch))
    (cb : fx_index_external_model X C BI) (index_budget : fx_index_external_budget X C BI)
    (source : fx_declared_callback_source X C A BW) (budget : fx_declared_callback_budget X C A BW)
    result index_events init_events engine_events init_bodies engine_bodies,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb index_budget ->
    fx_declared_callback_bounded source budget ->
    fx_total_callbacks_run EX EC L sch Widening S cb result index_events init_events engine_events
  ->
    fx_declared_trace_source source init_events init_bodies ->
    fx_declared_trace_source source engine_events engine_bodies ->
    let ix := fst (fx_index_nested_counted S cb) in
    let fuel := Pos.of_succ_nat (fx_total_widen_step_bound L W SS) in
    result = proj1_sig (total_solver_map EX EC L HL sch Widening S SS (conj (inhabits W) Hcut)) /\
    fx_index_adapter_work index_budget index_events + fx_declared_model_work EC init_events +
      fx_declared_model_work EC engine_events + fx_declared_body_work (fx_body_weight budget)
  init_bodies +
      fx_declared_body_work (fx_body_weight budget) engine_bodies <=
      fx_index_nested_input_budget EX S SS index_budget +
      fx_declared_run_input_budget EX EC L sch Widening S SS ix fuel +
      fx_declared_external_trace_budget budget init_events + fx_declared_external_trace_budget
  budget engine_events.
```

## Galois.Fixpoint.FixpointAuditWorklist

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditWorklist.v`.

```rocq
(** * Complete declared-worklist atomic model

    This report-local proposal fixes the execution equations for the complete fuel worklist
    operation with declared dependencies. For example, exhausted fuel returns None without
    inventing an additional empty-pop probe. External dictionary bodies have entry charges;
    their recursive implementation costs require their separately certified adapters.
    Builds on: FixpointWorklist, CollectionsAuditQueue and CostVocabulary. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsHeap CollectionsAuditQueue.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointTotal.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.
Inductive fx_encoder_entry (X : Type) := FxEncodeEntry (key : X) (code : positive).
Arguments FxEncodeEntry {X} _ _.
Definition fx_index_encoder {X} (EX : encoding X) (x : X) : positive * list (fx_encoder_entry X) :=
  let code := encode EX x in (code, [FxEncodeEntry x code]).

(** Actual typed operands and results identify every external entry and internal primitive. *)
Inductive fx_declared_call (X C A : Type) : Type :=
  | FxTarget (constraint : C) (result : X)
  | FxPriority (unknown : X) (result : positive)
  | FxWideningPoint (unknown : X) (result : bool)
  | FxRhs (constraint : C) (result : Query.t X A)
  | FxContinuation (unknown : X) (value : A) (continuation : A -> Query.t X A)
      (result : Query.t X A)
  | FxLeb (left right : A) (result : bool)
  | FxJoin (left right result : A)
  | FxWiden (left right result : A)
  | FxGet (unknown : X) (code : positive) (before : assignment X A) (raw : option A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxSet (unknown : X) (code : positive) (value : A) (before after : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxReaders (unknown : X) (code : positive) (before : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxPush (priority : positive) (constraint : C) (before after : PQueue.t C)
      (body : list (audit_queue_nested_event C (positive * list (fx_encoder_entry C))))
  | FxPop (before : PQueue.t C) (result : option (positive * C * PQueue.t C))
      (body : list (audit_queue_nested_event C (positive * list (fx_encoder_entry C)))).

Arguments FxTarget {X C A} _ _.
Arguments FxPriority {X C A} _ _.
Arguments FxWideningPoint {X C A} _ _.
Arguments FxRhs {X C A} _ _.
Arguments FxContinuation {X C A} _ _ _ _.
Arguments FxLeb {X C A} _ _ _.
Arguments FxJoin {X C A} _ _ _.
Arguments FxWiden {X C A} _ _ _.
Arguments FxGet {X C A} _ _ _ _ _.
Arguments FxSet {X C A} _ _ _ _ _ _.
Arguments FxReaders {X C A} _ _ _ _ _.
Arguments FxPush {X C A} _ _ _ _ _.
Arguments FxPop {X C A} _ _ _.

Definition fx_queue_internal_charge {C B} (_ : encoding C)
    (body : list (audit_queue_nested_event C (positive * list B))) : nat :=
  audit_queue_recorded_internal_source_work body.

Section DeclaredModel.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

(** Lookup retains its single actual encoding and the missing-entry branch. *)
Definition fx_model_lookup (values : assignment X A) (x : X) :
    A * audit_trace (fx_declared_call X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code values in
  (match raw with Some a => a | None => bot L end,
   [AuditCall (FxGet x code values raw body); AuditCase 0 []]).

(** The actual query continuation and assignment lookup execute once per Ask occurrence. *)
Fixpoint fx_model_query (q : Query.t X A) (values : assignment X A) :
    (A * list X * list (X * A)) * audit_trace (fx_declared_call X C A) :=
  match q with
  | Query.Ret a =>
      ((a, [], []), [AuditCase 1 []])
  | Query.Ask x k =>
      let '(value, lookup_events) := fx_model_lookup values x in
      let next := k value in
      let '(result, body) := fx_model_query next values in
      let '(a, reads, sides) := result in
      ((a, x :: reads, sides), [AuditCase 1 []] ++ lookup_events ++
        [AuditCall (FxContinuation x value k next)] ++ body ++ [AuditConstruct 0 []])
  | Query.Side x a next =>
      let '(result, body) := fx_model_query next values in
      let '(r, reads, sides) := result in
      ((r, reads, (x, a) :: sides), [AuditCase 1 []] ++ body ++ [AuditConstruct 1 []])
  end.

(** Left-fold enqueue retains each target, priority and actual persistent queue subrun. *)
Fixpoint fx_model_enqueue (constraints : list C) (queue : PQueue.t C) :
    PQueue.t C * audit_trace (fx_declared_call X C A) :=
  match constraints with
  | [] =>
      (queue, [AuditCase 2 []])
  | c :: rest =>
      let x := System.target S c in
      let p := priority sch x in
      let '(next, queue_events) := audit_queue_recorded_push (fx_index_encoder EC) p c queue in
      let '(out, tail) := fx_model_enqueue rest next in
      (out, [AuditCase 2 []; AuditCall (FxTarget c x); AuditCall (FxPriority x p);
        AuditCall (FxPush p c queue next queue_events)] ++ tail)
  end.

(** The selected join/widen branch follows the original mode and scheduler. *)
Definition fx_model_raise (x : X) (old value : A) :
    A * audit_trace (fx_declared_call X C A) :=
  match mode with
  | Joining =>
      let result := join L old value in
      (result, [AuditCase 3 []; AuditCall (FxJoin old value result)])
  | Widening =>
      let point := widening_point sch x in
      if point then
        let result := widen L old value in
        (result, [AuditCase 3 []; AuditCall (FxWideningPoint x point); AuditCase 11 [];
          AuditCall (FxWiden old value result)])
      else
        let result := join L old value in
        (result, [AuditCase 3 []; AuditCall (FxWideningPoint x point); AuditCase 11 [];
          AuditCall (FxJoin old value result)])
  end.

(** Unchanged updates perform one lookup and comparison and no reader lookup or enqueue. *)
Definition fx_model_update (xa : X * A) (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * audit_trace (fx_declared_call X C A) :=
  let '(values, queue) := mq in
  let '(x, value) := xa in
  let '(old, lookup_events) := fx_model_lookup values x in
  let unchanged := leb L value old in
  if unchanged then
    ((values, queue), lookup_events ++ [AuditCall (FxLeb value old unchanged); AuditCase 4 []])
  else
    let '(raised, raise_events) := fx_model_raise x old value in
    let write_code := encode EX x in
    let '(next_values, write_body) := audit_trie_set write_code (x, raised) values in
    let reader_code := encode EX x in
    let '(raw, reader_body) := audit_map_code_get reader_code (readers ix) in
    let constraints := match raw with Some cs => cs | None => [] end in
    let '(next_queue, enqueue_events) := fx_model_enqueue constraints queue in
    ((next_values, next_queue), lookup_events ++
      [AuditCall (FxLeb value old unchanged); AuditCase 4 []] ++ raise_events ++
      [AuditCall (FxSet x write_code raised values next_values write_body);
       AuditCall (FxReaders x reader_code (readers ix) raw reader_body); AuditCase 5 []] ++
      enqueue_events).

(** Target and side updates use the actual left-fold intermediate assignment and queue. *)
Fixpoint fx_model_updates (updates : list (X * A)) (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * audit_trace (fx_declared_call X C A) :=
  match updates with
  | [] =>
      (mq, [AuditCase 6 []])
  | update :: rest =>
      let '(next, head) := fx_model_update update mq in
      let '(out, tail) := fx_model_updates rest next in
      (out, [AuditCase 6 []] ++ head ++ tail)
  end.

(** A successful pop invokes exactly one rhs, one query run and its target-plus-side updates. *)
Definition fx_model_step (state : Engine.t X C A) :
    outcome X C A * audit_trace (fx_declared_call X C A) :=
  let '(popped, pop_events) := audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state)
  in
  let prefix := [AuditCall (FxPop (Engine.queue state) popped pop_events); AuditCase 7 []] in
  match popped with
  | None =>
      (Done (Engine.current state), prefix)
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(result, query_events) := fx_model_query rhs (Engine.current state) in
      let '(value, _, sides) := result in
      let target := System.target S c in
      let '(next, update_events) :=
        fx_model_updates ((target, value) :: sides) (Engine.current state, queue) in
      let '(values, next_queue) := next in
      (Pending (Engine.State values next_queue (Engine.recorded state)), prefix ++
        [AuditCall (FxRhs c rhs)] ++ query_events ++ [AuditCall (FxTarget c target)] ++
        update_events ++ [AuditConstruct 2 []])
  end.

(** Binary fuel uses the original then_run branches and does not charge skipped step bodies. *)
Fixpoint fx_model_loop (fuel : positive) (state : Engine.t X C A) :
    outcome X C A * audit_trace (fx_declared_call X C A) :=
  match fuel with
  | xH =>
      let '(out, events) := fx_model_step state in
      (out, AuditCase 8 [] :: events)
  | xO rest =>
      let '(first, first_events) := fx_model_loop rest state in
      match first with
      | Done values =>
          (Done values, AuditCase 8 [] :: first_events ++ [AuditCase 9 []])
      | Pending next =>
          let '(out, second_events) := fx_model_loop rest next in
          (out, AuditCase 8 [] :: first_events ++ [AuditCase 9 []] ++ second_events)
      end
  | xI rest =>
      let '(first, first_events) := fx_model_loop rest state in
      let '(second, second_events) :=
        match first with
        | Done values =>
            (Done values, [AuditCase 9 []])
        | Pending next =>
            let '(out, events) := fx_model_loop rest next in
            (out, AuditCase 9 [] :: events)
        end in
      match second with
      | Done values =>
          (Done values, AuditCase 8 [] :: first_events ++ second_events ++ [AuditCase 9 []])
      | Pending next =>
          let '(out, final_events) := fx_model_step next in
          (out, AuditCase 8 [] :: first_events ++ second_events ++
            [AuditCase 9 []] ++ final_events)
      end
  end.

(** This fixes the complete run_worklist call, including initial enqueue and final option branch. *)
Definition run_worklist_declared_model (fuel : positive) :
    option (assignment X A) * audit_trace (fx_declared_call X C A) :=
  let '(queue, initialization_events) :=
    fx_model_enqueue (System.constraints S) PQueue.empty in
  let '(result, body) := fx_model_loop fuel (Engine.State Map.empty queue Map.empty) in
  (match result with Done values => Some values | Pending _ => None end,
   initialization_events ++ [AuditConstruct 3 []] ++ body ++ [AuditCase 10 []]).

(** Every core model helper must erase to the same original engine computation. *)
Definition fx_declared_model_erasure_statement : Prop :=
  (forall values x, fst (fx_model_lookup values x) = lookup EX L values x) /\
  (forall q values, fst (fx_model_query q values) = Query.run q (lookup EX L values)) /\
  (forall cs queue, fst (fx_model_enqueue cs queue) = enqueue EC sch S cs queue) /\
  (forall x old value, fst (fx_model_raise x old value) =
    update_value L sch mode x old value) /\
  (forall xa mq, fst (fx_model_update xa mq) =
    engine_update EX EC L sch mode S (Declared SS ix) Map.empty xa mq) /\
  (forall updates mq, fst (fx_model_updates updates mq) =
    engine_updates EX EC L sch mode S (Declared SS ix) Map.empty updates mq) /\
  (forall state, fst (fx_model_step state) =
    step_outcome EX EC L sch mode S (Declared SS ix) state) /\
  (forall fuel state, fst (fx_model_loop fuel state) =
    loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state) /\
  (forall fuel, fst (run_worklist_declared_model fuel) =
    run_worklist EX EC L sch mode S (Declared SS ix) fuel).

(** Charges include the same invocation's fixed queue body and actual encoded map keys. *)
Definition fx_declared_call_charge (call : fx_declared_call X C A) : nat :=
  match call with
  | FxGet _ code _ _ body =>
      audit_encoding_weight (Pos.size_nat code) + audit_get_weight code +
        audit_trie_get_trace_source_work body
  | FxReaders _ code _ _ body =>
      audit_encoding_weight (Pos.size_nat code) + audit_get_weight code +
        audit_trie_get_trace_source_work body
  | FxSet _ code _ _ _ body =>
      audit_encoding_weight (Pos.size_nat code) + audit_set_weight code +
        audit_trie_update_trace_source_work body
  | FxPush _ _ _ _ body | FxPop _ _ body =>
      1 + fx_queue_internal_charge EC body + audit_queue_recorded_body_work (fun _ => 1) body
  | _ =>
      1
  end.

(** The sum is a deterministic measure of the fixed operation trace, with no price argument. *)
Fixpoint fx_declared_model_work (events : audit_trace (fx_declared_call X C A)) : nat :=
  match events with
  | [] =>
      0
  | AuditCall call :: rest =>
      fx_declared_call_charge call + fx_declared_model_work rest
  | _ :: rest =>
      1 + fx_declared_model_work rest
  end.

(** This explicit primitive excess budget gives two or three actual key bits per map access. *)
Fixpoint fx_declared_primitive_budget (events : audit_trace (fx_declared_call X C A)) : nat :=
  match events with
  | [] =>
      0
  | AuditCall (FxGet _ code _ _ body) :: rest =>
      1 + 2 * Pos.size_nat code + audit_trie_get_trace_source_work body +
        fx_declared_primitive_budget rest
  | AuditCall (FxReaders _ code _ _ body) :: rest =>
      1 + 2 * Pos.size_nat code + audit_trie_get_trace_source_work body +
        fx_declared_primitive_budget rest
  | AuditCall (FxSet _ code _ _ _ body) :: rest =>
      1 + 3 * Pos.size_nat code + audit_trie_update_trace_source_work body +
        fx_declared_primitive_budget rest
  | AuditCall (FxPush _ _ _ _ body) :: rest
  | AuditCall (FxPop _ _ body) :: rest =>
      fx_queue_internal_charge EC body + audit_queue_recorded_body_work (fun _ => 1) body +
        fx_declared_primitive_budget rest
  | _ :: rest =>
      fx_declared_primitive_budget rest
  end.

(** This component contract covers the entire declared fuel run, not other solver portfolios. *)
Definition run_worklist_declared_model_cost_statement : Prop :=
  forall fuel,
    let '(out, events) := run_worklist_declared_model fuel in
    out = run_worklist EX EC L sch mode S (Declared SS ix) fuel /\
    fx_declared_model_work events = audit_work events + fx_declared_primitive_budget events /\
    List.length (filter (fun event => match event with
      | AuditCall (FxPop _ _ _) => true | _ => false end) events) <= Pos.to_nat fuel /\
    List.length (filter (fun event => match event with
      | AuditCall (FxRhs _ _) => true | _ => false end) events) <= Pos.to_nat fuel.

(** Total execution stops on the same empty pop or recurses on the same successful-step state. *)
Inductive fx_declared_total_engine_run : Engine.t X C A -> assignment X A ->
    audit_trace (fx_declared_call X C A) -> Prop :=
  | FxTotalEngineStop : forall state values events,
      fx_model_step state = (Done values, events) ->
      fx_declared_total_engine_run state values events
  | FxTotalEngineContinue : forall state next values head tail,
      fx_model_step state = (Pending next, head) ->
      fx_declared_total_engine_run next values tail ->
      fx_declared_total_engine_run state values (head ++ tail).

(** Accessibility supplies an actual finite modeled execution, not a presumed whole-work bound. *)
Definition fx_declared_total_engine_total_statement : Prop :=
  forall start,
    Acc (engine_rel EX EC L sch mode S (Declared SS ix)) start ->
    exists values events, fx_declared_total_engine_run start values events.

(** A total execution retains the original successful steps and its actual final empty pop. *)
Definition fx_declared_total_engine_erases_statement : Prop :=
  forall start values events,
    fx_declared_total_engine_run start values events ->
    exists steps final,
      engine_steps EX EC L sch mode S (Declared SS ix) steps start final /\
      engine_step EX EC L sch mode S (Declared SS ix) final = None /\
      Engine.current final = values /\
      List.length (filter (fun event => match event with
        | AuditCall (FxPop _ _ _) => true | _ => false end) events) = Datatypes.S steps /\
      List.length (filter (fun event => match event with
        | AuditCall (FxRhs _ _) => true | _ => false end) events) = steps /\
      fx_declared_model_work events = audit_work events + fx_declared_primitive_budget events.

End DeclaredModel.

(** The total-solver execution witness uses that call's exact prepared index and returned map. *)
Definition total_solver_map_model_execution_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (HT : terminates L SS sch mode),
    exists events,
      fx_declared_total_engine_run EX EC L sch mode S (index_system EX S SS)
        (initial_state EC sch S) (proj1_sig (total_solver_map EX EC L HL sch mode S SS HT))
        events.
```

## Galois.Fixpoint.FixpointAuditWorklistBudget

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditWorklistBudget.v`.

```rocq
(** * Input/intermediate-state budgets for declared worklist execution

    These mathematical recurrences inspect source intermediate states and do not consume
    returned model event lists. Their evaluation is excluded from the source-work claim.
    Builds on FixpointWorklist, the shared queue bounds and counted declared execution. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditQueue.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
Import List.ListNotations.
Definition fx_fullcheck_lookup_input_budget {X} (EX : encoding X) (x : X) : nat :=
  3 + 7 * Pos.size_nat (encode EX x).
Fixpoint fx_fullcheck_query_input_budget {X A} (EX : encoding X) (L : lattice A)
    (m : assignment X A) (q : Query.t X A) : nat :=
  match q with
  | Query.Ret _ => 1
  | Query.Ask x k =>
      3 + fx_fullcheck_lookup_input_budget EX x +
        fx_fullcheck_query_input_budget EX L m (k (lookup EX L m x))
  | Query.Side _ _ next => 2 + fx_fullcheck_query_input_budget EX L m next
  end.

Definition fx_declared_push_input_budget {C} (EC : encoding C) (priority : positive)
    (c : C) (q : PQueue.t C) : nat :=
  let heap := PQueue.pending q in
  1 + audit_queue_full_input_budget EC 1 heap (PQueue.live q) [c] [priority] +
    2 * audit_queue_input_event_bound 1 heap.
Definition fx_declared_pop_input_budget {C} (EC : encoding C) (q : PQueue.t C) : nat :=
  let heap := PQueue.pending q in
  let fuel := PQueue.pending_count q in
  1 + audit_queue_full_input_budget EC fuel heap (PQueue.live q) [] [] +
    2 * audit_queue_input_event_bound fuel heap.
Fixpoint fx_declared_enqueue_input_budget {X C A} (EC : encoding C) (sch : scheduler X)
    (S : System.t X C A) (cs : list C) (q : PQueue.t C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let priority := priority sch (System.target S c) in
      3 + fx_declared_push_input_budget EC priority c q +
        fx_declared_enqueue_input_budget EC sch S rest (PQueue.push EC priority c q)
  end.
Definition fx_declared_update_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (ix : sys_index X C) (update : X * A) (state : assignment X A * PQueue.t C) : nat :=
  let '(x, value) := update in let '(m, q) := state in
  let old := lookup EX L m x in
  fx_fullcheck_lookup_input_budget EX x + 2 +
  if leb L value old then 0 else
    6 + (2 + 19 * Pos.size_nat (encode EX x)) + (2 + 7 * Pos.size_nat (encode EX x)) +
      fx_declared_enqueue_input_budget EC sch S (readers_of EX ix x) q.
Fixpoint fx_declared_updates_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (updates : list (X * A))
    (state : assignment X A * PQueue.t C) : nat :=
  match updates with
  | [] => 1
  | update :: rest =>
      1 + fx_declared_update_input_budget EX EC L sch mode S ix update state +
      fx_declared_updates_input_budget EX EC L sch mode S SS ix rest
        (engine_update EX EC L sch mode S (Declared SS ix) Map.empty update state)
  end.
Definition fx_declared_step_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (state : Engine.t X C A) : nat :=
  fx_declared_pop_input_budget EC (Engine.queue state) + 1 +
  match PQueue.pop EC (Engine.queue state) with
  | None => 0
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L (Engine.current state)) in
      3 + fx_fullcheck_query_input_budget EX L (Engine.current state) rhs +
      fx_declared_updates_input_budget EX EC L sch mode S SS ix
        ((System.target S c, value) :: sides) (Engine.current state, queue)
  end.
Fixpoint fx_declared_loop_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (fuel : positive) (state : Engine.t X C A) : nat :=
  let step := step_outcome EX EC L sch mode S (Declared SS ix) in
  match fuel with
  | xH => 1 + fx_declared_step_input_budget EX EC L sch mode S SS ix state
  | xO smaller =>
      2 + fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller state +
      match loop step smaller state with
      | Done _ => 0
      | Pending next => fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller next
      end
  | xI smaller =>
      let first := loop step smaller state in
      let second := match first with Done values => Done values | Pending next => loop step smaller
  next end in
      3 + fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller state +
      (match first with Done _ => 0 | Pending next =>
        fx_declared_loop_input_budget EX EC L sch mode S SS ix smaller next end) +
      match second with Done _ => 0 | Pending next => fx_declared_step_input_budget EX EC L sch mode
  S SS ix next end
  end.
Definition fx_declared_run_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (fuel : positive) : nat :=
  let queue := enqueue EC sch S (System.constraints S) PQueue.empty in
  fx_declared_enqueue_input_budget EC sch S (System.constraints S) PQueue.empty +
    2 + fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel (Engine.State Map.empty queue
  Map.empty).
Definition fx_declared_run_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) (SS : System.static S) ix fuel,
    let '(out, events) := run_worklist_declared_model EX EC L sch mode S ix fuel in
    out = run_worklist EX EC L sch mode S (Declared SS ix) fuel /\
    fx_declared_model_work EC events <= fx_declared_run_input_budget EX EC L sch mode S SS ix fuel.
```

## Galois.Fixpoint.FixpointAuditWorklistCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditWorklistCallbacks.v`.

```rocq
(** Source witnesses for the actual callback occurrences in one declared-worklist run.
    Callback relations describe individual source calls and their bodies, not a whole-run
    bound or a client assertion of the desired result. The observer is mathematical and
    its evaluation cost is excluded. Concrete library-owned clients must supply their real
    source rules; source-correspondence and bounds remain future theorem obligations. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditQueue.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

Record fx_declared_callback_source (X C A B : Type) := FxDeclaredCallbackSource {
  fx_source_encode_x : X -> positive -> list B -> Prop;
  fx_source_encode_c : C -> positive -> list B -> Prop;
  fx_source_target : C -> X -> list B -> Prop;
  fx_source_priority : X -> positive -> list B -> Prop;
  fx_source_widening_point : X -> bool -> list B -> Prop;
  fx_source_rhs : C -> Query.t X A -> list B -> Prop;
  fx_source_continuation : (A -> Query.t X A) -> A -> Query.t X A -> list B -> Prop;
  fx_source_leb : A -> A -> bool -> list B -> Prop;
  fx_source_join : A -> A -> A -> list B -> Prop;
  fx_source_widen : A -> A -> A -> list B -> Prop
}.
Arguments fx_source_encode_x {X C A B} _ _ _ _.
Arguments fx_source_encode_c {X C A B} _ _ _ _.
Arguments fx_source_target {X C A B} _ _ _ _.
Arguments fx_source_priority {X C A B} _ _ _ _.
Arguments fx_source_widening_point {X C A B} _ _ _ _.
Arguments fx_source_rhs {X C A B} _ _ _ _.
Arguments fx_source_continuation {X C A B} _ _ _ _ _.
Arguments fx_source_leb {X C A B} _ _ _ _ _.
Arguments fx_source_join {X C A B} _ _ _ _ _.
Arguments fx_source_widen {X C A B} _ _ _ _ _.

Definition fx_queue_encoder_entries {C} (events : list (audit_queue_nested_event C (positive * list
  (fx_encoder_entry C)))) : list (fx_encoder_entry C) :=
  flat_map (fun event => flat_map snd (snd (snd event))) events.
Definition fx_queue_encoder_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry C) (body : list B) : Prop :=
  match entry with FxEncodeEntry c code => fx_source_encode_c source c code body end.
Definition fx_declared_call_source {X C A B} (source : fx_declared_callback_source X C A B)
    (call : fx_declared_call X C A) (bodies : list (list B)) : Prop :=
  match call with
  | FxTarget c result => exists body, bodies = [body] /\ fx_source_target source c result body
  | FxPriority x result => exists body, bodies = [body] /\ fx_source_priority source x result body
  | FxWideningPoint x result => exists body, bodies = [body] /\ fx_source_widening_point source x
  result body
  | FxRhs c result => exists body, bodies = [body] /\ fx_source_rhs source c result body
  | FxContinuation _ value k result => exists body, bodies = [body] /\ fx_source_continuation source
  k value result body
  | FxLeb a b result => exists body, bodies = [body] /\ fx_source_leb source a b result body
  | FxJoin a b result => exists body, bodies = [body] /\ fx_source_join source a b result body
  | FxWiden a b result => exists body, bodies = [body] /\ fx_source_widen source a b result body
  | FxGet x code _ _ _ | FxSet x code _ _ _ _ | FxReaders x code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxPush _ _ _ _ nested | FxPop _ _ nested =>
      Forall2 (fx_queue_encoder_source source) (fx_queue_encoder_entries nested) bodies
  end.
Definition fx_declared_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : audit_event (fx_declared_call X C A)) (bodies : list (list B)) : Prop :=
  match event with
  | AuditCall call => fx_declared_call_source source call bodies
  | _ => bodies = []
  end.
Definition fx_declared_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (events : audit_trace (fx_declared_call X C A)) (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_declared_event_source source) events bodies.
Definition fx_declared_body_work {B} (weight : B -> nat) (bodies : list (list (list B))) : nat :=
  fold_right (fun event n => fold_right (fun body m => fold_right (fun x k => weight x + k) 0 body +
  m) 0 event + n) 0 bodies.

Inductive fx_declared_query_reachable {X C A} (S : System.t X C A) : Query.t X A -> Prop :=
  | FxReachableRhs : forall c, In c (System.constraints S) ->
      fx_declared_query_reachable S (System.rhs S c)
  | FxReachableAsk : forall x k a, fx_declared_query_reachable S (Query.Ask x k) ->
      fx_declared_query_reachable S (k a)
  | FxReachableSide : forall x a next, fx_declared_query_reachable S (Query.Side x a next) ->
      fx_declared_query_reachable S next.

(** Each source relation must describe the corresponding actual external callback body.
    These laws do not assume any result or work bound for the surrounding solver. *)
Definition fx_declared_source_laws {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (S : System.t X C A)
    (source : fx_declared_callback_source X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_encode_c source c (encode EC c) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall x, exists body, fx_source_priority source x (priority sch x) body) /\
  (forall x, exists body, fx_source_widening_point source x (widening_point sch x) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall (k : A -> Query.t X A) a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
  exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall a b, exists body, fx_source_widen source a b (widen L a b) body).

Record fx_declared_callback_budget (X C A B : Type) := FxDeclaredCallbackBudget {
  fx_body_weight : B -> nat;
  fx_budget_encode_x : X -> nat;
  fx_budget_encode_c : C -> nat;
  fx_budget_target : C -> nat;
  fx_budget_priority : X -> nat;
  fx_budget_widening_point : X -> nat;
  fx_budget_rhs : C -> nat;
  fx_budget_continuation : (A -> Query.t X A) -> A -> nat;
  fx_budget_leb : A -> A -> nat;
  fx_budget_join : A -> A -> nat;
  fx_budget_widen : A -> A -> nat
}.
Arguments fx_body_weight {X C A B} _ _.
Arguments fx_budget_encode_x {X C A B} _ _.
Arguments fx_budget_encode_c {X C A B} _ _.
Arguments fx_budget_target {X C A B} _ _.
Arguments fx_budget_priority {X C A B} _ _.
Arguments fx_budget_widening_point {X C A B} _ _.
Arguments fx_budget_rhs {X C A B} _ _.
Arguments fx_budget_continuation {X C A B} _ _ _.
Arguments fx_budget_leb {X C A B} _ _ _.
Arguments fx_budget_join {X C A B} _ _ _.
Arguments fx_budget_widen {X C A B} _ _ _.
Definition fx_one_body_work {B} (weight : B -> nat) (body : list B) : nat :=
  fold_right (fun e n => weight e + n) 0 body.
Definition fx_declared_callback_bounded {X C A B}
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B) :
  Prop :=
  (forall x result body, fx_source_encode_x source x result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_encode_x budget x) /\
  (forall c result body, fx_source_encode_c source c result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_encode_c budget c) /\
  (forall c result body, fx_source_target source c result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_target budget c) /\
  (forall x result body, fx_source_priority source x result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_priority budget x) /\
  (forall x result body, fx_source_widening_point source x result body -> fx_one_body_work
  (fx_body_weight budget) body <= fx_budget_widening_point budget x) /\
  (forall c result body, fx_source_rhs source c result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_rhs budget c) /\
  (forall k a result body, fx_source_continuation source k a result body -> fx_one_body_work
  (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b result body, fx_source_leb source a b result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_leb budget a b) /\
  (forall a b result body, fx_source_join source a b result body -> fx_one_body_work (fx_body_weight
  budget) body <= fx_budget_join budget a b) /\
  (forall a b result body, fx_source_widen source a b result body -> fx_one_body_work
  (fx_body_weight budget) body <= fx_budget_widen budget a b).
Definition fx_queue_entry_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entry : fx_encoder_entry C) : nat :=
  match entry with FxEncodeEntry c _ => fx_budget_encode_c budget c end.
Definition fx_declared_external_call_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (call : fx_declared_call X C A) : nat :=
  match call with
  | FxTarget c _ => fx_budget_target budget c
  | FxPriority x _ => fx_budget_priority budget x
  | FxWideningPoint x _ => fx_budget_widening_point budget x
  | FxRhs c _ => fx_budget_rhs budget c
  | FxContinuation _ a k _ => fx_budget_continuation budget k a
  | FxLeb a b _ => fx_budget_leb budget a b
  | FxJoin a b _ => fx_budget_join budget a b
  | FxWiden a b _ => fx_budget_widen budget a b
  | FxGet x _ _ _ _ | FxSet x _ _ _ _ _ | FxReaders x _ _ _ _ => fx_budget_encode_x budget x
  | FxPush _ _ _ _ nested | FxPop _ _ nested =>
      fold_right (fun entry n => fx_queue_entry_budget budget entry + n) 0 (fx_queue_encoder_entries
  nested)
  end.
Definition fx_declared_external_trace_budget {X C A B} (budget : fx_declared_callback_budget X C A
  B)
    (events : audit_trace (fx_declared_call X C A)) : nat :=
  fold_right (fun event n => match event with
    | AuditCall call => fx_declared_external_call_budget budget call + n
    | _ => n end) 0 events.

(** Future theorem: the very same whole execution has callback-body witnesses in event
    order. Its external allowance is the sum over actual call operands, not a premise
    asserting the solver's result or its desired whole-run bound. *)
Definition fx_declared_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S) ix fuel
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    sys_index_laws EX S SS ix ->
    fx_declared_source_laws EX EC L sch S source ->
    fx_declared_callback_bounded source budget ->
    let '(out, events) := run_worklist_declared_model EX EC L sch mode S ix fuel in
    exists bodies,
      fx_declared_trace_source source events bodies /\
      out = run_worklist EX EC L sch mode S (Declared SS ix) fuel /\
      fx_declared_model_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_declared_run_input_budget EX EC L sch mode S SS ix fuel +
          fx_declared_external_trace_budget budget events.
```

### Future proofs in `FixpointAuditCacheAdequacy`

Card: AUD-FX-CACHE

Source destination: `theories/Fixpoint/FixpointAuditCacheAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditCache.

Theorem cache_callbacks_erasure :
  FixpointAuditCache.cache_callbacks_erasure_statement.
Theorem cache_query_callbacks_source :
  FixpointAuditCache.cache_query_callbacks_source_statement.
Theorem cache_init_callbacks_source :
  FixpointAuditCache.cache_init_callbacks_source_statement.
Theorem cache_query_input_bound :
  FixpointAuditCache.cache_query_input_bound_statement.
```

### Future proofs in `FixpointAuditCacheSemanticAdequacy`

Card: AUD-FX-CACHE

Source destination: `theories/Fixpoint/FixpointAuditCacheSemanticAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditCacheSemantic.

Theorem cache_epoch_initial_valid :
  FixpointAuditCacheSemantic.cache_epoch_initial_valid_statement.
Theorem cache_epoch_miss_rebuild :
  FixpointAuditCacheSemantic.cache_epoch_miss_rebuild_statement.
Theorem cache_epoch_hit :
  FixpointAuditCacheSemantic.cache_epoch_hit_statement.
Theorem cache_epoch_refuel :
  FixpointAuditCacheSemantic.cache_epoch_refuel_statement.
```

### Future proofs in `FixpointAuditCheckCallbacksAdequacy`

Card: AUD-FX-FULLCHECK

Source destination: `theories/Fixpoint/FixpointAuditCheckCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditCheckCallbacks.

Theorem fx_fullcheck_rooted_source :
  FixpointAuditCheckCallbacks.fx_fullcheck_rooted_source_statement.
```

### Future proofs in `FixpointAuditCutAdequacy`

Card: AUD-FX-CUT

Source destination: `theories/Fixpoint/FixpointAuditCutAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditCut.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_cut_model_erasure :
  FixpointAuditContractClosures.fx_cut_model_erasure_contract.
Theorem fx_cut_expand_selected_cost :
  FixpointAuditCut.fx_cut_expand_selected_cost_statement.
Theorem fx_cut_expand_input_bound :
  FixpointAuditCut.fx_cut_expand_input_bound_statement.
```

### Future proofs in `FixpointAuditCutCallbacksAdequacy`

Card: AUD-FX-CUT

Source destination: `theories/Fixpoint/FixpointAuditCutCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditCutCallbacks.

Theorem fx_cut_external_source_holds :
  FixpointAuditCutCallbacks.fx_cut_external_source_statement.
```

### Future proofs in `FixpointAuditFallbackAdequacy`

Card: AUD-FX-FALLBACK

Source destination: `theories/Fixpoint/FixpointAuditFallbackAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditFallback.

Theorem fx_fallback_erasure :
  FixpointAuditFallback.fx_fallback_erasure_statement.
Theorem fx_recorded_fallback_input_bound :
  FixpointAuditFallback.fx_recorded_fallback_input_bound_statement.
Theorem fx_nested_fallback_input_bound :
  FixpointAuditFallback.fx_nested_fallback_input_bound_statement.
Theorem fx_fallback_apply :
  FixpointAuditFallback.fx_fallback_apply_statement.
```

### Future proofs in `FixpointAuditFallbackCallbacksAdequacy`

Card: AUD-FX-FALLBACK

Source destination: `theories/Fixpoint/FixpointAuditFallbackCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditFallbackCallbacks.

Theorem fx_recorded_fallback_external_source :
  FixpointAuditFallbackCallbacks.fx_recorded_fallback_external_source_statement.
Theorem fx_nested_fallback_external_source :
  FixpointAuditFallbackCallbacks.fx_nested_fallback_external_source_statement.
Theorem fx_fallback_apply_external_source :
  FixpointAuditFallbackCallbacks.fx_fallback_apply_external_source_statement.
```

### Future proofs in `FixpointAuditFullCheckAdequacy`

Card: AUD-FX-FULLCHECK

Source destination: `theories/Fixpoint/FixpointAuditFullCheckAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditFullCheck.

Theorem fx_fullcheck_nested_erasure :
  FixpointAuditFullCheck.fx_fullcheck_nested_erasure_statement.
Theorem fx_fullcheck_nested_total :
  FixpointAuditFullCheck.fx_fullcheck_nested_total_statement.
Theorem fx_fullcheck_nested_input_bound :
  FixpointAuditFullCheck.fx_fullcheck_nested_input_bound_statement.
Theorem fx_fullcheck_external_source :
  FixpointAuditFullCheck.fx_fullcheck_external_source_statement.
```

### Future proofs in `FixpointAuditIndexAdequacy`

Card: AUD-FX-INDEX

Source destination: `theories/Fixpoint/FixpointAuditIndexAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditIndex.

Theorem fx_index_nested_erasure :
  FixpointAuditIndex.fx_index_nested_erasure_statement.
Theorem fx_index_nested_input_bound :
  FixpointAuditIndex.fx_index_nested_input_bound_statement.
Theorem fx_index_external_source_holds :
  FixpointAuditIndex.fx_index_external_source_statement.
```

### Future proofs in `FixpointAuditLocalAdequacy`

Card: AUD-FX-LOCAL

Source destination: `theories/Fixpoint/FixpointAuditLocalAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditLocal.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_local_solve_erasure :
  FixpointAuditContractClosures.fx_local_solve_erasure_contract.
Theorem fx_local_checked_erasure :
  FixpointAuditContractClosures.fx_local_checked_erasure_contract.
Theorem fx_local_checked_selected_cost :
  FixpointAuditLocal.fx_local_checked_selected_cost_statement.
Theorem fx_local_checked_input_bound :
  FixpointAuditLocal.fx_local_checked_input_bound_statement.
```

### Future proofs in `FixpointAuditLocalCallbacksAdequacy`

Card: AUD-FX-LOCAL

Source destination: `theories/Fixpoint/FixpointAuditLocalCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditLocalCallbacks.

Theorem fx_local_external_source_holds :
  FixpointAuditLocalCallbacks.fx_local_external_source_statement.
```

### Future proofs in `FixpointAuditLocalClosureAdequacy`

Card: AUD-FX-LOCAL

Source destination: `theories/Fixpoint/FixpointAuditLocalClosureAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditLocalClosure.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_local_step_erasure :
  FixpointAuditContractClosures.fx_local_step_erasure_contract.
Theorem fx_local_walk_erasure :
  FixpointAuditContractClosures.fx_local_walk_erasure_contract.
Theorem fx_local_walk_selected_cost :
  FixpointAuditLocalClosure.fx_local_walk_selected_cost_statement.
Theorem fx_local_walk_input_bound :
  FixpointAuditLocalClosure.fx_local_walk_input_bound_statement.
```

### Future proofs in `FixpointAuditLocalPartialAdequacy`

Card: AUD-FX-PARTIALCHECK

Source destination: `theories/Fixpoint/FixpointAuditLocalPartialAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditLocalPartial.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_partial_model_erasure :
  FixpointAuditContractClosures.fx_partial_model_erasure_contract.
Theorem fx_partial_model_cost :
  FixpointAuditContractClosures.fx_partial_model_cost_contract.
Theorem fx_partial_input_bound :
  FixpointAuditLocalPartial.fx_partial_input_bound_statement.
```

### Future proofs in `FixpointAuditNarrowAdequacy`

Card: AUD-FX-NARROW

Source destination: `theories/Fixpoint/FixpointAuditNarrowAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNarrow.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_narrow_checked_erasure :
  FixpointAuditContractClosures.fx_narrow_checked_erasure_contract.
Theorem fx_narrow_checked_selected_cost :
  FixpointAuditNarrow.fx_narrow_checked_selected_cost_statement.
Theorem fx_narrow_checked_input_bound :
  FixpointAuditNarrow.fx_narrow_checked_input_bound_statement.
Theorem fx_narrow_run_total :
  FixpointAuditNarrow.fx_narrow_run_total_statement.
Theorem fx_narrow_run_correct :
  FixpointAuditNarrow.fx_narrow_run_correct_statement.
```

### Future proofs in `FixpointAuditNarrowCallbacksAdequacy`

Card: AUD-FX-NARROW

Source destination: `theories/Fixpoint/FixpointAuditNarrowCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNarrowCallbacks.

Theorem fx_narrow_external_source :
  FixpointAuditNarrowCallbacks.fx_narrow_external_source_statement.
```

### Future proofs in `FixpointAuditNarrowCheckAdequacy`

Card: AUD-FX-FULLCHECK

Source destination: `theories/Fixpoint/FixpointAuditNarrowCheckAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNarrowCheck.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_fullcheck_erasure :
  FixpointAuditContractClosures.fx_fullcheck_erasure_contract.
Theorem fx_fullcheck_selected_cost :
  FixpointAuditNarrowCheck.fx_fullcheck_selected_cost_statement.
Theorem fx_fullcheck_input_bound :
  FixpointAuditNarrowCheck.fx_fullcheck_input_bound_statement.
```

### Future proofs in `FixpointAuditNestedAdequacy`

Card: AUD-FX-NESTED

Source destination: `theories/Fixpoint/FixpointAuditNestedAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNested.

Theorem fx_nested_run_erasure :
  FixpointAuditNested.fx_nested_run_erasure_statement.
Theorem fx_nested_run_input_bound :
  FixpointAuditNested.fx_nested_run_input_bound_statement.
Theorem fx_nested_run_model_total :
  FixpointAuditNested.fx_nested_run_model_total_statement.
Theorem fx_nested_run_model_correct :
  FixpointAuditNested.fx_nested_run_model_correct_statement.
```

### Future proofs in `FixpointAuditNestedCallbacksAdequacy`

Card: AUD-FX-NESTED

Source destination: `theories/Fixpoint/FixpointAuditNestedCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNestedCallbacks.

Theorem fx_nested_external_source :
  FixpointAuditNestedCallbacks.fx_nested_external_source_statement.
```

### Future proofs in `FixpointAuditNestedMachineAdequacy`

Card: AUD-FX-NESTED

Source destination: `theories/Fixpoint/FixpointAuditNestedMachineAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNestedMachine.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_nested_machine_erasure :
  FixpointAuditContractClosures.fx_nested_machine_erasure_contract.
Theorem fx_nested_loop_selected_cost :
  FixpointAuditNestedMachine.fx_nested_loop_selected_cost_statement.
Theorem fx_nested_loop_input_bound :
  FixpointAuditNestedMachine.fx_nested_loop_input_bound_statement.
```

### Future proofs in `FixpointAuditNestedPlanAdequacy`

Card: AUD-FX-NESTED

Source destination: `theories/Fixpoint/FixpointAuditNestedPlanAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditNestedPlan.

Theorem fx_nested_plan_semantic :
  FixpointAuditNestedPlan.fx_nested_plan_semantic_statement.
Theorem fx_nested_plan_selected_cost :
  FixpointAuditNestedPlan.fx_nested_plan_selected_cost_statement.
Theorem fx_nested_plan_input_bound :
  FixpointAuditNestedPlan.fx_nested_plan_input_bound_statement.
```

### Future proofs in `FixpointAuditPartialCallbacksAdequacy`

Card: AUD-FX-PARTIALCHECK

Source destination: `theories/Fixpoint/FixpointAuditPartialCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditPartialCallbacks.

Theorem fx_partial_rooted_source :
  FixpointAuditPartialCallbacks.fx_partial_rooted_source_statement.
```

### Future proofs in `FixpointAuditPartialCheckAdequacy`

Card: AUD-FX-PARTIALCHECK

Source destination: `theories/Fixpoint/FixpointAuditPartialCheckAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditPartialCheck.

Theorem fx_partial_nested_erasure :
  FixpointAuditPartialCheck.fx_partial_nested_erasure_statement.
Theorem fx_partial_nested_total :
  FixpointAuditPartialCheck.fx_partial_nested_total_statement.
Theorem fx_partial_nested_input_bound :
  FixpointAuditPartialCheck.fx_partial_nested_input_bound_statement.
Theorem fx_partial_external_source :
  FixpointAuditPartialCheck.fx_partial_external_source_statement.
```

### Future proofs in `FixpointAuditRecordedAdequacy`

Card: AUD-FX-RECORDED

Source destination: `theories/Fixpoint/FixpointAuditRecordedAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditRecorded.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_record_reads_erasure :
  FixpointAuditRecorded.fx_record_reads_erasure_statement.
Theorem fx_record_reads_count :
  FixpointAuditRecorded.fx_record_reads_count_statement.
Theorem fx_recorded_readers_erasure :
  FixpointAuditRecorded.fx_recorded_readers_erasure_statement.
Theorem fx_recorded_model_erasure :
  FixpointAuditContractClosures.fx_recorded_model_erasure_contract.
Theorem fx_recorded_model_cost :
  FixpointAuditContractClosures.fx_recorded_model_cost_contract.
Theorem fx_recorded_successor_count :
  FixpointAuditContractClosures.fx_recorded_successor_count_contract.
```

### Future proofs in `FixpointAuditRecordedBudgetAdequacy`

Card: AUD-FX-RECORDED

Source destination: `theories/Fixpoint/FixpointAuditRecordedBudgetAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditRecordedBudget.

Theorem fx_recorded_run_input_bound :
  FixpointAuditRecordedBudget.fx_recorded_run_input_bound_statement.
```

### Future proofs in `FixpointAuditRecordedCallbacksAdequacy`

Card: AUD-FX-RECORDED

Source destination: `theories/Fixpoint/FixpointAuditRecordedCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditRecordedCallbacks.

Theorem fx_recorded_external_source :
  FixpointAuditRecordedCallbacks.fx_recorded_external_source_statement.
```

### Future proofs in `FixpointAuditScheduleAdequacy`

Card: AUD-FX-SCHEDULE

Source destination: `theories/Fixpoint/FixpointAuditScheduleAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditSchedule.

Theorem audit_rpo_schedule_positions_erases :
  FixpointAuditSchedule.audit_rpo_schedule_positions_statement.
Theorem audit_rpo_schedule_callbacks_erases :
  FixpointAuditSchedule.audit_rpo_schedule_callbacks_statement.
Theorem audit_rpo_schedule_retreats_erases :
  FixpointAuditSchedule.audit_rpo_schedule_retreats_statement.
Theorem audit_rpo_positions_bound_correct :
  FixpointAuditSchedule.audit_rpo_positions_bound_statement.
Theorem audit_rpo_retreats_bound_correct :
  FixpointAuditSchedule.audit_rpo_retreats_bound_statement.
Theorem audit_rpo_schedule_query_bound_correct :
  FixpointAuditSchedule.audit_rpo_schedule_query_bound_statement.
Theorem audit_rpo_positions_adapted_correct :
  FixpointAuditSchedule.audit_rpo_positions_adapted_statement.
Theorem audit_rpo_retreats_adapted_correct :
  FixpointAuditSchedule.audit_rpo_retreats_adapted_statement.
```

### Future proofs in `FixpointAuditScheduleWrapperAdequacy`

Card: AUD-FX-SCHEDULE

Source destination: `theories/Fixpoint/FixpointAuditScheduleWrapperAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditScheduleWrapper.

Theorem fx_dep_build_erasure_correct :
  FixpointAuditScheduleWrapper.fx_dep_build_erasure_statement.
Theorem fx_dep_out_erasure_correct :
  FixpointAuditScheduleWrapper.fx_dep_out_erasure_statement.
Theorem fx_rpo_scheduler_erasure_correct :
  FixpointAuditScheduleWrapper.fx_rpo_scheduler_erasure_statement.
Theorem fx_dep_build_bound_correct :
  FixpointAuditScheduleWrapper.fx_dep_build_bound_statement.
Theorem fx_dep_out_bound_correct :
  FixpointAuditScheduleWrapper.fx_dep_out_bound_statement.
Theorem fx_rpo_scheduler_input_bound_correct :
  FixpointAuditScheduleWrapper.fx_rpo_scheduler_input_bound_statement.
Theorem fx_rpo_scheduler_source_correct :
  FixpointAuditScheduleWrapper.fx_rpo_scheduler_source_statement.
Theorem fx_rpo_receipt_count_correct :
  FixpointAuditScheduleWrapper.fx_rpo_receipt_count_statement.
Theorem fx_rpo_fast_reverse_correct :
  FixpointAuditScheduleWrapper.fx_rpo_fast_reverse_statement.
```

### Future proofs in `FixpointAuditTotalAdequacy`

Card: AUD-FX-TOTAL

Source destination: `theories/Fixpoint/FixpointAuditTotalAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditTotal.

Theorem fx_total_callbacks_realization :
  FixpointAuditTotal.fx_total_callbacks_realization_statement.
Theorem fx_total_callbacks_erasure :
  FixpointAuditTotal.fx_total_callbacks_erasure_statement.
Theorem fx_total_callbacks_source :
  FixpointAuditTotal.fx_total_callbacks_source_statement.
Theorem fx_total_callbacks_join_work :
  FixpointAuditTotal.fx_total_callbacks_join_work_statement.
Theorem fx_total_callbacks_widen_work :
  FixpointAuditTotal.fx_total_callbacks_widen_work_statement.
```

### Future proofs in `FixpointAuditWorklistAdequacy`

Card: AUD-FX-WORKLIST

Source destination: `theories/Fixpoint/FixpointAuditWorklistAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditWorklist.
From Galois.Fixpoint Require Import FixpointAuditContractClosures.

Theorem fx_declared_model_erasure :
  FixpointAuditContractClosures.fx_declared_model_erasure_contract.
Theorem run_worklist_declared_model_cost :
  FixpointAuditContractClosures.run_worklist_declared_model_cost_contract.
Theorem fx_declared_total_engine_total :
  FixpointAuditContractClosures.fx_declared_total_engine_total_contract.
Theorem fx_declared_total_engine_erases :
  FixpointAuditContractClosures.fx_declared_total_engine_erases_contract.
Theorem total_solver_map_model_execution :
  FixpointAuditWorklist.total_solver_map_model_execution_statement.
```

### Future proofs in `FixpointAuditWorklistBudgetAdequacy`

Card: AUD-FX-WORKLIST

Source destination: `theories/Fixpoint/FixpointAuditWorklistBudgetAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditWorklistBudget.

Theorem fx_declared_run_input_bound :
  FixpointAuditWorklistBudget.fx_declared_run_input_bound_statement.
```

### Future proofs in `FixpointAuditWorklistCallbacksAdequacy`

Card: AUD-FX-WORKLIST

Source destination: `theories/Fixpoint/FixpointAuditWorklistCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditWorklistCallbacks.

Theorem fx_declared_external_source_holds :
  FixpointAuditWorklistCallbacks.fx_declared_external_source_statement.
```

<!-- AUD-API-FX-END -->

<!-- AUD-API-OBS-BEGIN -->

# Observation source contracts


## Galois.Fixpoint.FixpointAuditObserveCompare

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveCompare.v`.

```rocq
(** * Observation-plan key comparisons

    Both boolean operands and all list tails are evaluated by the source functions.
    For example, a matching early element does not erase later equality calls.
    Builds on: FixpointObserve and FixpointAuditWorklistCallbacks. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditWorklist
  FixpointAuditWorklistCallbacks.
Import List.ListNotations.

Inductive fx_observe_compare_event (X : Type) : Type :=
  | FxObserveCompare (x y : X) (left right : positive) (result : bool)
  | FxObserveCompareCase.
Arguments FxObserveCompare {X} _ _ _ _ _.
Arguments FxObserveCompareCase {X}.

(** A comparison captures both actual encoder inputs, outputs and the equality result. *)
Definition fx_observe_key_compare {X} (EX : encoding X) (x y : X) :
    bool * list (fx_observe_compare_event X) :=
  let left := encode EX x in
  let right := encode EX y in
  let result := Pos.eqb left right in
  (result, [FxObserveCompare x y left right result]).

(** Both the head predicate and the recursive tail contribute, even after a match. *)
Fixpoint fx_observe_exists_key {X} (EX : encoding X) (x : X) (ys : list X) :
    bool * list (fx_observe_compare_event X) :=
  match ys with
  | [] => (false, [FxObserveCompareCase])
  | y :: rest =>
      let '(same, first) := fx_observe_key_compare EX x y in
      let '(later, tail) := fx_observe_exists_key EX x rest in
      (same || later, FxObserveCompareCase :: first ++ tail)
  end.

(** Every outer element invokes the complete inner scan. *)
Fixpoint fx_observe_all_keys {X} (EX : encoding X) (xs ys : list X) :
    bool * list (fx_observe_compare_event X) :=
  match xs with
  | [] => (true, [FxObserveCompareCase])
  | x :: rest =>
      let '(found, first) := fx_observe_exists_key EX x ys in
      let '(later, tail) := fx_observe_all_keys EX rest ys in
      (found && later, FxObserveCompareCase :: first ++ tail)
  end.

(** Set equality evaluates both directed scans. *)
Definition fx_observe_seteq {X} (EX : encoding X) (xs ys : list X) :
    bool * list (fx_observe_compare_event X) :=
  let '(forward, first) := fx_observe_all_keys EX xs ys in
  let '(backward, later) := fx_observe_all_keys EX ys xs in
  (forward && backward, FxObserveCompareCase :: first ++ later).

(** A duplicate check evaluates all later duplicate checks. *)
Fixpoint fx_observe_nodup {X} (EX : encoding X) (xs : list X) :
    bool * list (fx_observe_compare_event X) :=
  match xs with
  | [] => (true, [FxObserveCompareCase])
  | x :: rest =>
      let '(found, first) := fx_observe_exists_key EX x rest in
      let '(later, tail) := fx_observe_nodup EX rest in
      (negb found && later, FxObserveCompareCase :: first ++ tail)
  end.

(** Source frames charge comparison operand widths and the list constructors. *)
Definition fx_observe_compare_event_work {X} (event : fx_observe_compare_event X) : nat :=
  match event with
  | FxObserveCompare _ _ code1 code2 _ => 4 + Pos.size_nat code1 + Pos.size_nat code2
  | FxObserveCompareCase => 1
  end.

(** The frame work folds over the events captured by the same execution. *)
Definition fx_observe_compare_work {X} (events : list (fx_observe_compare_event X)) : nat :=
  fold_right (fun e n => fx_observe_compare_event_work e + n) 0 events.

(** The inner source bound uses all actual input elements and encoded-key lengths. *)
Fixpoint fx_observe_exists_key_budget {X} (EX : encoding X) (x : X) (ys : list X) : nat :=
  match ys with
  | [] => 1
  | y :: rest => 5 + Pos.size_nat (encode EX x) + Pos.size_nat (encode EX y) +
      fx_observe_exists_key_budget EX x rest
  end.

(** The outer source bound charges each complete inner scan. *)
Fixpoint fx_observe_all_keys_budget {X} (EX : encoding X) (xs ys : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 1 + fx_observe_exists_key_budget EX x ys +
      fx_observe_all_keys_budget EX rest ys
  end.

(** The duplicate-check bound charges the suffix scan for every element. *)
Fixpoint fx_observe_nodup_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 1 + fx_observe_exists_key_budget EX x rest + fx_observe_nodup_budget EX rest
  end.

(** The two-sided source bound is independent of the captured events. *)
Definition fx_observe_seteq_budget {X} (EX : encoding X) (xs ys : list X) : nat :=
  1 + fx_observe_all_keys_budget EX xs ys + fx_observe_all_keys_budget EX ys xs.

(** Set equality retains the actual result and an input-derived source-frame bound. *)
Definition fx_observe_seteq_statement : Prop :=
  forall (X : Type) (EX : encoding X) (xs ys : list X),
    let '(out, events) := fx_observe_seteq EX xs ys in
    out = observation_seteq EX xs ys /\
    fx_observe_compare_work events <= fx_observe_seteq_budget EX xs ys.

(** Duplicate checking retains the actual result and an input-derived source-frame bound. *)
Definition fx_observe_nodup_statement : Prop :=
  forall (X : Type) (EX : encoding X) (xs : list X),
    let '(out, events) := fx_observe_nodup EX xs in
    out = observation_nodup_check EX xs /\
    fx_observe_compare_work events <= fx_observe_nodup_budget EX xs.

(** Each comparison carries both encoder bodies from its actual call operands. *)
Definition fx_observe_compare_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_observe_compare_event X) (bodies : list (list B)) : Prop :=
  match event with
  | FxObserveCompare x y code1 code2 _ => exists body1 body2,
      bodies = [body1; body2] /\ fx_source_encode_x source x code1 body1 /\
        fx_source_encode_x source y code2 body2
  | FxObserveCompareCase => bodies = []
  end.

(** Encoder laws are per actual input and body, without a whole-scan premise. *)
Definition fx_observe_compare_source_laws {X C A B} (EX : encoding X)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall x code body, fx_source_encode_x source x code body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x).

(** The callback budget sums the two encoder calls of each captured comparison. *)
Definition fx_observe_compare_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_observe_compare_event X) : nat :=
  match event with
  | FxObserveCompare x y _ _ _ => fx_budget_encode_x budget x + fx_budget_encode_x budget y
  | FxObserveCompareCase => 0
  end.

(** One captured set-equality scan carries all source bodies and both cost components. *)
Definition fx_observe_seteq_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (xs ys : list X),
    fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_seteq EX xs ys in
    exists bodies, Forall2 (fx_observe_compare_source source) events bodies /\
      out = observation_seteq EX xs ys /\
      fx_observe_compare_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_seteq_budget EX xs ys +
        fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events.

(** One captured duplicate scan carries its own encoder bodies and frame bound. *)
Definition fx_observe_nodup_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (xs : list X),
    fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_nodup EX xs in
    exists bodies, Forall2 (fx_observe_compare_source source) events bodies /\
      out = observation_nodup_check EX xs /\
      fx_observe_compare_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_nodup_budget EX xs +
        fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveCompareAdequacy`

Card: AUD-FX-OBS-PRIMS

Source destination: `theories/Fixpoint/FixpointAuditObserveCompareAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveCompare.

Theorem fx_observe_seteq_correct :
  FixpointAuditObserveCompare.fx_observe_seteq_statement.
Theorem fx_observe_nodup_correct :
  FixpointAuditObserveCompare.fx_observe_nodup_statement.
Theorem fx_observe_seteq_source :
  FixpointAuditObserveCompare.fx_observe_seteq_source_statement.
Theorem fx_observe_nodup_source :
  FixpointAuditObserveCompare.fx_observe_nodup_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveCompile

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveCompile.v`.

```rocq
(** * Observation component compilation

    Compilation builds the dependency graph and root set once, then each induced component.
    For example, each local WTO sees its own filtered outgoing-closure bodies.
    Builds on: FixpointAuditObserveInduced and the nested-plan and WTO models. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphWto GraphAuditBase GraphAuditDfs
  GraphAuditWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointNested
  FixpointObserve FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklist
  FixpointAuditNestedPlan FixpointAuditNestedCallbacks FixpointAuditWorklistCallbacks
  FixpointAuditNarrowDiscovery
  FixpointAuditObserveExecute.
From Galois.Fixpoint Require Import FixpointAuditObserveInduced FixpointAuditObserveCompare.
Import List.ListNotations.

Inductive fx_observe_compile_event (X C D B : Type) : Type :=
  | FxCompileDependency (events : list (fx_dep_event X C B))
  | FxCompileSet (events : list (audit_set_event X B))
  | FxCompileInduced (events : list (fx_induced_event X C B))
  | FxCompilePrepare (events : list (audit_prepare_source_event X (X * X) (fx_induced_event X C B)))
  | FxCompileWto (events : list (audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_induced_event X C B))))
  | FxCompilePlan (events : list (fx_nested_plan_event X D))
  | FxCompileHeads (events : list (audit_set_event X (fx_encoder_entry X)))
  | FxCompileTargets (events : list (audit_map_event X (list D) (fx_encoder_entry X)))
  | FxCompileExpiry (events : list (audit_map_event X (list X) (fx_encoder_entry X)))
  | FxCompileCase.
Arguments FxCompileDependency {X C D B} _.
Arguments FxCompileSet {X C D B} _.
Arguments FxCompileInduced {X C D B} _.
Arguments FxCompilePrepare {X C D B} _.
Arguments FxCompileWto {X C D B} _.
Arguments FxCompilePlan {X C D B} _.
Arguments FxCompileHeads {X C D B} _.
Arguments FxCompileTargets {X C D B} _.
Arguments FxCompileExpiry {X C D B} _.
Arguments FxCompileCase {X C D B}.

(** Every requested target key captures both its input lookup and output write. *)
Fixpoint fx_compile_restrict {X C D B} (EX : encoding X) (targets : Map.t X (list D))
    (members : list X) : Map.t X (list D) * list (fx_observe_compile_event X C D B) :=
  match members with
  | [] => (Map.empty, [FxCompileCase])
  | x :: rest =>
      let '(before, later) := @fx_compile_restrict X C D B EX targets rest in
      let '(found, read) := audit_map_get (fx_index_encoder EX) x targets in
      let values := match found with Some values => values | None => [] end in
      let '(after, write) := audit_map_set (fx_index_encoder EX) x values before in
      (after, FxCompileCase :: later ++ [FxCompileTargets read; FxCompileTargets write])
  end.

(** Output filtering checks each component member against the once-built root set. *)
Fixpoint fx_compile_outputs {X C D B} (cb : fx_index_external_model X C B)
    (roots : FinSet.t X) (members : list X) : list X * list (fx_observe_compile_event X C D B) :=
  match members with
  | [] => ([], [FxCompileCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x roots in
      let '(later, events) := @fx_compile_outputs X C D B cb roots rest in
      (if present then x :: later else later, FxCompileCase :: FxCompileSet mem :: events)
  end.

(** One local component captures its induced graph, WTO, nested plan, outputs and expiry. *)
Definition fx_compile_component {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (graph : Graph.t X (X * X))
    (ix : sys_index X C) (targets : Map.t X (list D)) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) :
    ObservationComponent.t X D * list (fx_observe_compile_event X C D B) :=
  let '(keep, keep_events) := audit_finset_of_list (fxi_encode cb) members in
  let '(nodes, node_events) := fx_induced_filter_vertices cb keep (Graph.nodes graph) in
  let local := {| Graph.entries := members; Graph.nodes := nodes;
    Graph.out := Graph.out (induced EX keep graph); Graph.source := fst; Graph.target := snd |} in
  let '(prepared, prepare_events) := audit_prepare_source_counted EX local
    (fx_induced_prepare_cb cb ix keep) in
  let '(tokens, wto_events) := audit_wto_source_counted prepared (fx_induced_dfs_cb cb) in
  let '(code, parse_events) := @fx_nested_tree X D tokens in
  let '(nest_members, member_events) := @fx_nested_members X D EX code in
  let '(restrict, restrict_events) := @fx_compile_restrict X C D B EX targets members in
  let '(heads, head_events) := @fx_nested_heads X D code in
  let '(head_set, set_events) := audit_finset_of_list (fx_index_encoder EX) heads in
  let plan := NestedPlan.Make code nest_members restrict head_set in
  let '(outputs, output_events) := @fx_compile_outputs X C D B cb roots members in
  let '(expires, expire_events) := match members with
    | [] => ([], [])
    | h :: _ =>
        let '(found, events) := audit_map_get (fx_index_encoder EX) h expiration in
        (match found with Some xs => xs | None => [] end, [FxCompileExpiry events])
    end in
  (ObservationComponent.Make members plan outputs expires,
    [FxCompileSet keep_events; FxCompileInduced node_events; FxCompilePrepare prepare_events;
     FxCompileWto wto_events; FxCompilePlan (parse_events ++ member_events)] ++ restrict_events ++
     [FxCompilePlan head_events; FxCompileHeads set_events] ++ output_events ++ expire_events).

(** Each component runs against the same dependency graph and root-set witness. *)
Fixpoint fx_compile_components {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (graph : Graph.t X (X * X))
    (ix : sys_index X C) (targets : Map.t X (list D)) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (order : list (list X)) :
    list (ObservationComponent.t X D) * list (fx_observe_compile_event X C D B) :=
  match order with
  | [] => ([], [FxCompileCase])
  | members :: rest =>
      let '(component, events) := fx_compile_component EX S SS cb graph ix targets roots
    expiration members in
      let '(later, tail) := fx_compile_components EX S SS cb graph ix targets roots expiration
    rest in
      (component :: later, FxCompileCase :: events ++ tail)
  end.

(** Targets compilation builds its graph and selected root set exactly once. *)
Definition fx_observe_compile_targets {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (targets : Map.t X (list D))
    (roots : list X) (p : observation_plan X) :
    list (ObservationComponent.t X D) * list (fx_observe_compile_event X C D B) :=
  let '(graph, ix, graph_events) := fx_dep_graph_build EX S SS cb in
  let '(selected, set_events) := audit_finset_of_list (fxi_encode cb) roots in
  let '(components, events) := fx_compile_components EX S SS cb graph ix targets selected
    (observation_expire p) (observation_components p) in
  (components, FxCompileDependency graph_events :: FxCompileSet set_events :: events).

(** Captured work includes the induced graph closures and every local-plan operation. *)
Definition fx_observe_compile_event_work {X C D B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_compile_event X C D B) : nat :=
  match event with
  | FxCompileDependency events => fx_dep_events_work ib events
  | FxCompileSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxCompileInduced events => fx_induced_work ib events
  | FxCompilePrepare events => audit_prepare_source_work (fx_induced_event_work ib) events
  | FxCompileWto events => audit_wto_source_work (fx_induced_event_work ib) events
  | FxCompilePlan events => fx_nested_plan_work events
  | FxCompileHeads events => audit_finset_source_work (@length (fx_encoder_entry X)) events
  | FxCompileTargets events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxCompileExpiry events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxCompileCase => 1
  end.

(** Compile work is a fold over the one captured component schedule. *)
Definition fx_observe_compile_work {X C D B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_compile_event X C D B)) : nat :=
  fold_right (fun event n => fx_observe_compile_event_work ib event + n) 0 events.

(** Every member incurs a target lookup/write and an output-membership test. *)
Fixpoint fx_compile_members_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (members : list X) : nat :=
  match members with
  | [] => 2
  | x :: rest => 20 + 26 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_compile_members_budget EX ib rest
  end.

(** This finite maximum covers actual graph vertices and all observed edge endpoints. *)
Definition fx_compile_callback_max {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (members : list X) : nat :=
  let graph := dependency_graph EX S SS in
  let ix := index_system EX S SS in
  let vertices := Graph.nodes graph ++ members ++
    flat_map (fun x => map snd (Graph.out graph x)) (Graph.nodes graph) in
  64 + fold_right (fun x n => Nat.max n
    (fx_induced_out_budget EX S SS ix ib x + fxi_encode_bound ib x)) 0 vertices.

(** This code bound covers parsing, nested members, head enumeration and head-set construction. *)
Definition fx_compile_code_budget {X} (EX : encoding X) (tokens : wto X) : nat :=
  let code := nested_tree tokens in
  let rows := nested_rows [] code in
  let heads := nested_heads code in
  let size := S (length tokens) in
  200 * size * size * size +
    40 * (fx_index_input_bits EX (map fst rows) + fx_index_input_bits EX heads).

(** Each component budget uses its actual induced graph, prepared graph and WTO. *)
Definition fx_compile_component_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (members : list X) : nat :=
  let graph := dependency_graph EX S SS in
  let local := observation_graph EX S SS members in
  let prepared := prepare EX local in
  let tokens := wto_total prepared in
  let count := audit_graph_prepare_full_event_bound local + audit_wto_input_event_bound prepared in
  fxi_set_input_budget EX ib members + fx_induced_vertices_budget EX ib (Graph.nodes graph) +
    audit_prepare_source_budget EX local + audit_wto_source_budget EX local prepared +
    64 * (1 + count) * fx_compile_callback_max EX S SS ib members +
    fx_compile_code_budget EX tokens + fx_compile_members_budget EX ib members +
    match members with [] => 0 | h :: _ => 6 + 5 * Pos.size_nat (encode EX h) end.

(** Component budgets sum over the actual plan order. *)
Fixpoint fx_compile_components_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (order : list (list X)) : nat :=
  match order with
  | [] => 1
  | members :: rest => 1 + fx_compile_component_budget EX S SS ib members +
      fx_compile_components_budget EX S SS ib rest
  end.

(** One graph and one root set precede the component budgets. *)
Definition fx_observe_compile_targets_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (roots : list X)
    (p : observation_plan X) : nat :=
  fx_dep_build_budget EX S SS ib + fxi_set_input_budget EX ib roots +
    fx_compile_components_budget EX S SS ib (observation_components p).

(** Graph-preparation calls carry the bodies of the actual induced closures. *)
Definition fx_compile_prepare_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_prepare_source_event X (X * X) (fx_induced_event X C B)) : Prop :=
  match event with
  | PrepareSourceOut _ _ body | PrepareSourceTarget _ _ body =>
      Forall (fx_induced_event_source source) body
  | PrepareSourceMap e =>
      match e with
      | AuditMapGet _ _ _ _ body _ | AuditMapSet _ _ _ _ _ body _ |
        AuditMapRemove _ _ _ _ body _ => Forall (fx_induced_event_source source) body
      end
  | _ => True
  end.

(** WTO graph calls retain the corresponding induced encoder or target body. *)
Definition fx_compile_wto_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_induced_event X C B))) : Prop :=
  Forall (fun capture => match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body | AuditGraphEncodeCapture _ _ _ _ _ body =>
        Forall (fx_induced_event_source source) body
    end) (snd event).

(** Each compile phase carries original callback bodies and actual nested encoder bodies. *)
Definition fx_observe_compile_event_source {X C D A B E}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X D A E) (event : fx_observe_compile_event X C D B)
    (bodies : list (list E)) : Prop :=
  match event with
  | FxCompileDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FxCompileSet events => fxi_set_external_adequacy index_source events /\ bodies = []
  | FxCompileInduced events => Forall (fx_induced_event_source index_source) events /\ bodies = []
  | FxCompilePrepare events => Forall (fx_compile_prepare_source index_source) events /\ bodies = []
  | FxCompileWto events => Forall (fx_compile_wto_source index_source) events /\ bodies = []
  | FxCompilePlan events => exists groups,
      Forall2 (fx_nested_plan_event_source source) events groups /\ bodies = concat groups
  | FxCompileHeads events => Forall2 (fx_nested_entry_source source) (fx_nested_entries events)
    bodies
  | FxCompileTargets events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxCompileExpiry events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxCompileCase => bodies = []
  end.

(** Only actual nested-plan encoder calls contribute declared callback budgets. *)
Definition fx_observe_compile_external_budget {X C D A B E}
    (budget : fx_declared_callback_budget X D A E) (event : fx_observe_compile_event X C D B) :
    nat :=
  match event with
  | FxCompilePlan events =>
      fold_right (fun e n => fx_nested_plan_external_budget budget e + n) 0 events
  | FxCompileHeads events => fx_nested_entries_budget budget (fx_nested_entries events)
  | FxCompileTargets events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries
    events)
  | FxCompileExpiry events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries
    events)
  | _ => 0
  end.

(** One target-compilation witness provides its actual schedule, bodies and input-derived bound. *)
Definition fx_observe_compile_targets_source_statement : Prop :=
  forall (X C D A B E : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X D A E)
    (budget : fx_declared_callback_budget X D A E) (targets : Map.t X (list D))
    (roots : list X) (p : observation_plan X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_compile_targets EX S SS cb targets roots p in
    exists bodies, Forall2 (fx_observe_compile_event_source index_source source) events bodies /\
      out = observation_compile_targets EX S SS targets roots p /\
      fx_observe_compile_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_compile_targets_budget EX S SS ib roots p +
        fold_right (fun e n => fx_observe_compile_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveCompileAdequacy`

Card: AUD-FX-OBS-COMPILE

Source destination: `theories/Fixpoint/FixpointAuditObserveCompileAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveCompile.

Theorem fx_observe_compile_targets_source :
  FixpointAuditObserveCompile.fx_observe_compile_targets_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveCompileWhole

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveCompileWhole.v`.

```rocq
(** * Numbered observation compilation

    Numbering and target indexing feed the same captured table to component compilation.
    For example, repeated constraints remain distinct occurrences in each local target map.
    Builds on: FixpointAuditObserveNumberTargets and FixpointAuditObserveCompile. *)
From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointObserve FixpointAuditIndex
  FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObserveExpiry FixpointAuditObserveNumberTargets
  FixpointAuditObserveNumberMachine FixpointAuditObserveCompile.
Import List.ListNotations.

Inductive fx_observe_compile_whole_event (X C A B : Type) : Type :=
  | FxWholeNumber (events : list (fx_observe_number_target_event X C))
  | FxWholeCompile (events : list (fx_observe_compile_event X C nat B)).
Arguments FxWholeNumber {X C A B} _.
Arguments FxWholeCompile {X C A B} _.

(** The actual numbered target index feeds one component-compilation execution. *)
Definition fx_observe_compile_whole {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (fallback : C)
    (roots : list X) (p : observation_plan X) :
    list (ObservationComponent.t X nat) * list (fx_observe_compile_whole_event X C A B) :=
  let '((_, _, targets), number_events) := fx_observe_numbered_system_targets EX S fallback in
  let '(out, compile_events) := fx_observe_compile_targets EX S SS cb targets roots p in
  (out, [FxWholeNumber number_events; FxWholeCompile compile_events]).

(** The full input budget composes numbered construction and local-component compilation. *)
Definition fx_observe_compile_whole_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (fallback : C)
    (roots : list X) (p : observation_plan X) : nat :=
  fx_observe_numbered_targets_budget EX S fallback +
    fx_observe_compile_targets_budget EX S SS ib roots p.

(** The captured phase work counts numbering, induced closures and local components. *)
Definition fx_observe_compile_whole_event_work {X C A B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_compile_whole_event X C A B) : nat :=
  match event with
  | FxWholeNumber events => fx_number_targets_work events
  | FxWholeCompile events => fx_observe_compile_work ib events
  end.

(** Both phases use their actual original callback bodies. *)
Definition fx_observe_compile_whole_event_source {X C A B D}
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (event : fx_observe_compile_whole_event X C A B) (bodies : list (list D)) : Prop :=
  match event with
  | FxWholeNumber events => exists groups,
      Forall2 (fx_number_target_event_source source) events groups /\ bodies = concat groups
  | FxWholeCompile events => exists groups,
      Forall2 (fx_observe_compile_event_source index_source (fx_number_passthrough_source source))
        events groups /\ bodies = concat groups
  end.

(** External budgets are charged to actual captured numbering and local-plan callbacks. *)
Definition fx_observe_compile_whole_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_compile_whole_event X C
    A B) : nat :=
  match event with
  | FxWholeNumber events => fold_right (fun e n => fx_number_target_external_budget budget e +
    n) 0 events
  | FxWholeCompile events => fold_right
      (fun e n => fx_observe_compile_external_budget (fx_number_passthrough_budget budget) e + n)
      0 events
  end.

(** The same counted compilation has exact schedule output, source bodies and an input bound. *)
Definition fx_observe_compile_whole_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (fallback : C) (roots : list X)
    (p : observation_plan X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_compile_whole EX S SS cb fallback roots p in
    exists bodies, Forall2 (fx_observe_compile_whole_event_source index_source source) events
    bodies /\
      out = observation_compile EX S SS fallback roots p /\
      fold_right (fun e n => fx_observe_compile_whole_event_work ib e + n) 0 events +
        fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_compile_whole_budget EX S SS ib fallback roots p +
        fold_right (fun e n => fx_observe_compile_whole_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveCompileWholeAdequacy`

Card: AUD-FX-OBS-COMPILE

Source destination: `theories/Fixpoint/FixpointAuditObserveCompileWholeAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveCompileWhole.

Theorem fx_observe_compile_whole_source :
  FixpointAuditObserveCompileWhole.fx_observe_compile_whole_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveComponents

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveComponents.v`.

```rocq
(** * Observation component validation

    Component validation compares SCC classes, universe coverage and forward boundaries.
    For example, an earlier failed component match does not stop a strict existsb tail.
    Builds on: FixpointAuditObserveOrder, FixpointAuditObserveForward and comparison models. *)
From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointSchedule FixpointObserve
    FixpointAuditIndex
  FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObserveOrder FixpointAuditObserveForward
    FixpointAuditObserveCompare.
Import List.ListNotations.

Inductive fx_observe_component_event (X C B : Type) : Type :=
  | FxComponentOrder (events : list (fx_observe_order_event X C B))
  | FxComponentDependency (events : list (fx_dep_event X C B))
  | FxComponentIndex (events : list (fx_index_nested_event X C B))
  | FxComponentForward (events : list (fx_observe_forward_event X C B))
  | FxComponentCompare (events : list (fx_observe_compare_event X))
  | FxComponentList (size : nat)
  | FxComponentCase.
Arguments FxComponentOrder {X C B} _.
Arguments FxComponentDependency {X C B} _.
Arguments FxComponentIndex {X C B} _.
Arguments FxComponentForward {X C B} _.
Arguments FxComponentCompare {X C B} _.
Arguments FxComponentList {X C B} _.
Arguments FxComponentCase {X C B}.

(** Every candidate class is examined, including after a successful class match. *)
Fixpoint fx_component_in_classes {X C B} (EX : encoding X) (component : list X)
    (classes : list (list X)) : bool * list (fx_observe_component_event X C B) :=
  match classes with
  | [] => (false, [FxComponentCase])
  | class :: rest =>
      let '(same, events) := fx_observe_seteq EX component class in
      let '(later, tail) := @fx_component_in_classes X C B EX component rest in
      (same || later, FxComponentCase :: FxComponentCompare events :: tail)
  end.

(** Every component receives a full class scan. *)
Fixpoint fx_components_in_classes {X C B} (EX : encoding X) (order classes : list (list X)) :
    bool * list (fx_observe_component_event X C B) :=
  match order with
  | [] => (true, [FxComponentCase])
  | component :: rest =>
      let '(found, events) := @fx_component_in_classes X C B EX component classes in
      let '(later, tail) := @fx_components_in_classes X C B EX rest classes in
      (found && later, FxComponentCase :: events ++ tail)
  end.

(** Nonempty validation evaluates all list tails. *)
Fixpoint fx_components_nonempty {X C B} (order : list (list X)) :
    bool * list (fx_observe_component_event X C B) :=
  match order with
  | [] => (true, [FxComponentCase])
  | component :: rest =>
      let '(later, tail) := @fx_components_nonempty X C B rest in
      ((match component with [] => false | _ => true end) && later, FxComponentCase :: tail)
  end.

(** All strict component checks consume the same computed classes and actual input order. *)
Definition fx_observe_components {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (order : list (list X)) :
    bool * list (fx_observe_component_event X C B) :=
  let '(classes, class_events) := fx_observe_order EX S SS cb in
  let '(nodup, nd_events) := fx_observe_nodup EX (concat order) in
  let '(input, dep_events) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, unknown_events) := fxi_distinct_counted cb input in
  let '(cover, cover_events) := fx_observe_seteq EX (concat order) unknown in
  let '(nonempty, nonempty_events) := @fx_components_nonempty X C B order in
  let '(belongs, belongs_events) := @fx_components_in_classes X C B EX order classes in
  let '(forward, forward_events) := fx_observe_forward_run cb (System.constraints S) order in
  (nodup && cover && nonempty && belongs && forward,
    [FxComponentOrder class_events; FxComponentList (length order + length (concat order));
     FxComponentCompare nd_events; FxComponentDependency dep_events; FxComponentIndex
    unknown_events;
     FxComponentList (length order + length (concat order)); FxComponentCompare cover_events] ++
     nonempty_events ++ belongs_events ++ [FxComponentForward forward_events]).

(** Class scans use input lists and encoded-key widths. *)
Fixpoint fx_component_in_classes_budget {X} (EX : encoding X) (component : list X)
    (classes : list (list X)) : nat :=
  match classes with
  | [] => 1
  | class :: rest => 1 + fx_observe_seteq_budget EX component class +
      fx_component_in_classes_budget EX component rest
  end.

(** The full class-membership budget traverses every component and class. *)
Fixpoint fx_components_in_classes_budget {X} (EX : encoding X) (order classes : list (list X))
    : nat :=
  match order with
  | [] => 1
  | component :: rest => 1 + fx_component_in_classes_budget EX component classes +
      fx_components_in_classes_budget EX rest classes
  end.

(** The component bound includes both concat calls and all five strict checks. *)
Definition fx_observe_components_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (order : list (list X)) : nat :=
  let classes := observation_order EX S SS in
  let unknown := unknowns EX S SS in
  fx_observe_order_budget EX S SS ib + fx_dep_build_budget EX S SS ib +
    8 * (1 + length order + length (concat order)) + fx_observe_nodup_budget EX (concat order) +
    fx_observe_seteq_budget EX (concat order) unknown +
    fx_components_in_classes_budget EX order classes +
    fx_observe_forward_budget EX S SS ib order.

(** Every event is charged for its own actual phase or list traversal. *)
Definition fx_observe_component_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_component_event X C B) : nat :=
  match event with
  | FxComponentOrder events => fx_observe_order_work ib events
  | FxComponentDependency events => fx_dep_events_work ib events
  | FxComponentIndex events => fx_index_adapter_work ib events
  | FxComponentForward events => fx_observe_forward_work ib events
  | FxComponentCompare events => fx_observe_compare_work events
  | FxComponentList n => 2 + n
  | FxComponentCase => 1
  end.

(** Work folds the captured component-check events. *)
Definition fx_observe_components_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_component_event X C B)) : nat :=
  fold_right (fun event n => fx_observe_component_event_work ib event + n) 0 events.

(** Callback sources and comparison bodies are attached to each selected event. *)
Definition fx_observe_component_event_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_component_event X C B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxComponentOrder events => Forall (fx_observe_order_event_source index_source) events /\
    bodies = []
  | FxComponentDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FxComponentIndex events => fx_index_external_trace_adequacy index_source events /\ bodies = []
  | FxComponentForward events =>
      Forall (fx_observe_forward_event_source index_source) events /\ bodies = []
  | FxComponentCompare events => exists groups,
      Forall2 (fx_observe_compare_source source) events groups /\ bodies = concat groups
  | _ => bodies = []
  end.

(** Only actual comparisons contribute encoder-body budgets. *)
Definition fx_observe_component_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_component_event X C B) :
    nat :=
  match event with
  | FxComponentCompare events =>
      fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events
  | _ => 0
  end.

(** One component-check witness provides its result, callbacks and independent frame bound. *)
Definition fx_observe_components_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (order : list (list X)),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_components EX S SS cb order in
    exists bodies, Forall2 (fx_observe_component_event_source index_source source) events bodies /\
      out = observation_components_check EX S SS order /\
      fx_observe_components_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_components_budget EX S SS ib order +
        fold_right (fun e n => fx_observe_component_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveComponentsAdequacy`

Card: AUD-FX-OBS-CHECK

Source destination: `theories/Fixpoint/FixpointAuditObserveComponentsAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveComponents.

Theorem fx_observe_components_source :
  FixpointAuditObserveComponents.fx_observe_components_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveExecute

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveExecute.v`.

```rocq
(** * Observation execution and boundary accounting

    The counted machine retains nested transitions, output writes and optional evictions.
    For example, completing one component records its roots before evicting expired values.
    Builds on: FixpointObserve and FixpointAuditNestedMachine. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointNested
  FixpointObserve
  FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditNestedMachine.
From Galois.Fixpoint Require Import FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks.
Import List.ListNotations.

Inductive fx_observe_event (X C A : Type) : Type :=
  | FxObserveNested (events : list (fx_nested_event X C A))
  | FxObserveQuery (events : audit_trace (fx_declared_call X C A))
  | FxObserveMap (event : audit_map_event X A (fx_encoder_entry X))
  | FxObserveCase (site : nat).
Arguments FxObserveNested {X C A} _.
Arguments FxObserveQuery {X C A} _.
Arguments FxObserveMap {X C A} _.
Arguments FxObserveCase {X C A} _.

Section ObserveExecution.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (mode : strategy) (S : System.t X C A).

Fixpoint fx_observe_record (keys : list X) (values output : assignment X A) :
    assignment X A * list (fx_observe_event X C A) :=
  match keys with
  | [] => (output, [FxObserveCase 0])
  | x :: rest =>
      let '(value, reads) := @fx_model_lookup X C A EX L values x in
      let '(next, writes) := audit_map_set (fx_index_encoder EX) x value output in
      let '(result, later) := fx_observe_record rest values next in
      (result, FxObserveCase 0 :: FxObserveQuery reads :: map FxObserveMap writes ++ later)
  end.

Fixpoint fx_observe_evict (keys : list X) (values : assignment X A) :
    assignment X A * list (fx_observe_event X C A) :=
  match keys with
  | [] => (values, [FxObserveCase 1])
  | x :: rest =>
      let '(next, removed) := audit_map_remove (fx_index_encoder EX) x values in
      let '(result, later) := fx_observe_evict rest next in
      (result, FxObserveCase 1 :: map FxObserveMap removed ++ later)
  end.

Definition fx_observe_tick (evict : bool)
    (input : ObservationState.t X C A + (assignment X A * assignment X A)) :
    (ObservationState.t X C A + (assignment X A * assignment X A)) *
      list (fx_observe_event X C A) :=
  match input with
  | inr finished => (inr finished, [FxObserveCase 2])
  | inl state =>
      let component := ObservationState.active state in
      let '(next, nested_events) :=
        fx_nested_step EX L (ObservationComponent.code component) mode S
          (ObservationState.local state) in
      match next with
      | Some local =>
          (inl (ObservationState.Make component (ObservationState.pending state) local
            (ObservationState.observed state)), [FxObserveCase 2; FxObserveNested nested_events])
      | None =>
          let values := NestedState.current (ObservationState.local state) in
          let '(output, record_events) :=
            fx_observe_record (ObservationComponent.outputs component) values
              (ObservationState.observed state) in
          let '(retained, evict_events) :=
            if evict then fx_observe_evict (ObservationComponent.expire component) values
            else (values, []) in
          let events := FxObserveCase 2 :: FxObserveNested nested_events ::
            record_events ++ evict_events in
          match ObservationState.pending state with
          | [] => (inr (retained, output), events ++ [FxObserveCase 3])
          | next :: rest =>
              (inl (ObservationState.Make next rest (observation_start_local next retained) output),
               events ++ [FxObserveCase 3])
          end
      end
  end.

Fixpoint fx_observe_repeat (evict : bool) (fuel : positive)
    (input : ObservationState.t X C A + (assignment X A * assignment X A)) :
    (ObservationState.t X C A + (assignment X A * assignment X A)) *
      list (fx_observe_event X C A) :=
  match fuel with
  | xH => fx_observe_tick evict input
  | xO smaller =>
      let '(first, events) := fx_observe_repeat evict smaller input in
      let '(out, later) := fx_observe_repeat evict smaller first in
      (out, FxObserveCase 4 :: events ++ later)
  | xI smaller =>
      let '(first, events) := fx_observe_repeat evict smaller input in
      let '(second, later) := fx_observe_repeat evict smaller first in
      let '(out, last) := fx_observe_tick evict second in
      (out, FxObserveCase 4 :: events ++ later ++ last)
  end.

Definition fx_observe_execute (schedule : list (ObservationComponent.t X C))
    (evict : bool) (fuel : positive) :
    option (assignment X A * assignment X A) * list (fx_observe_event X C A) :=
  match schedule with
  | [] => (Some (Map.empty, Map.empty), [FxObserveCase 5])
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty in
      let '(out, events) := fx_observe_repeat evict fuel (inl initial) in
      (match out with inl _ => None | inr result => Some result end, FxObserveCase 5 :: events)
  end.
End ObserveExecution.

(** Every helper and the whole execution erase to the actual observation machine. *)
Definition fx_observe_execute_erasure_statement : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) mode (S : System.t X C A) schedule evict fuel,
    fst (fx_observe_execute EX L mode S schedule evict fuel) =
      observation_execute EX L mode S schedule evict fuel.

Definition fx_observe_event_work {X C A} (EC : encoding C) (event : fx_observe_event X C A) : nat :=
  match event with
  | FxObserveNested events => fx_nested_work EC events
  | FxObserveQuery events => fx_declared_model_work EC events
  | FxObserveMap e => audit_map_source_work (@length (fx_encoder_entry X)) [e]
  | FxObserveCase _ => 1
  end.
Definition fx_observe_work {X C A} (EC : encoding C)
    (events : list (fx_observe_event X C A)) : nat :=
  fold_right (fun e n => fx_observe_event_work EC e + n) 0 events.

(** * Input-derived execution budget *)

(** Each recorded key pays for the lookup and the output-map update. *)
Fixpoint fx_observe_record_input_budget {X} (EX : encoding X) (keys : list X) : nat :=
  match keys with
  | [] => 1
  | x :: rest =>
      1 + fx_fullcheck_lookup_input_budget EX x + 3 + 16 * Pos.size_nat (encode EX x) +
        fx_observe_record_input_budget EX rest
  end.

(** Each expired key pays for a removal from the current assignment. *)
Fixpoint fx_observe_evict_input_budget {X} (EX : encoding X) (keys : list X) : nat :=
  match keys with
  | [] => 1
  | x :: rest => 4 + 16 * Pos.size_nat (encode EX x) + fx_observe_evict_input_budget EX rest
  end.

(** The boundary charge is selected by the actual nested-step outcome. *)
Definition fx_observe_tick_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (evict : bool)
    (state : ObservationState.t X C A + (assignment X A * assignment X A)) : nat :=
  match state with
  | inr _ => 1
  | inl current =>
      let component := ObservationState.active current in
      3 + fx_nested_step_input_budget EX L (ObservationComponent.code component) mode S
        (ObservationState.local current) +
      match nested_step EX L (ObservationComponent.code component) mode S
          (ObservationState.local current) with
      | Some _ => 0
      | None => fx_observe_record_input_budget EX (ObservationComponent.outputs component) +
          (if evict then fx_observe_evict_input_budget EX (ObservationComponent.expire component)
           else 0) + 1
      end
  end.

(** Binary repetition charges every tick, including ticks after an already finished result. *)
Fixpoint fx_observe_repeat_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (evict : bool) (fuel : positive)
    (state : ObservationState.t X C A + (assignment X A * assignment X A)) : nat :=
  match fuel with
  | xH => fx_observe_tick_input_budget EX L mode S evict state
  | xO smaller =>
      let first := observation_repeat (observation_tick EX L mode S evict) smaller state in
      1 + fx_observe_repeat_input_budget EX L mode S evict smaller state +
        fx_observe_repeat_input_budget EX L mode S evict smaller first
  | xI smaller =>
      let first := observation_repeat (observation_tick EX L mode S evict) smaller state in
      let second := observation_repeat (observation_tick EX L mode S evict) smaller first in
      1 + fx_observe_repeat_input_budget EX L mode S evict smaller state +
        fx_observe_repeat_input_budget EX L mode S evict smaller first +
        fx_observe_tick_input_budget EX L mode S evict second
  end.

(** The schedule bound uses only its input and the actual intermediate machine states. *)
Definition fx_observe_execute_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (schedule : list (ObservationComponent.t X C))
    (evict : bool) (fuel : positive) : nat :=
  match schedule with
  | [] => 1
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty in
      1 + fx_observe_repeat_input_budget EX L mode S evict fuel (inl initial)
  end.

(** The same counted execution erases and is bounded by its input-derived source frames. *)
Definition fx_observe_execute_input_bound_statement : Prop :=
  forall (X C A : Type) (EX : encoding X) (EC : encoding C) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (schedule : list (ObservationComponent.t X C))
    (evict : bool) (fuel : positive),
    let '(out, events) := fx_observe_execute EX L mode S schedule evict fuel in
    out = observation_execute EX L mode S schedule evict fuel /\
      fx_observe_work EC events <= fx_observe_execute_input_budget EX L mode S schedule evict fuel.

(** * Callback receipts for the captured execution *)

(** The actual encoder calls inside a map event carry their own source bodies. *)
Definition fx_observe_map_entries {X A}
    (event : audit_map_event X A (fx_encoder_entry X)) : list (fx_encoder_entry X) :=
  match event with
  | AuditMapGet _ _ _ _ entries _ => entries
  | AuditMapSet _ _ _ _ _ entries _ => entries
  | AuditMapRemove _ _ _ _ entries _ => entries
  end.

(** Each event's bodies describe the callbacks in that event, with no replay. *)
Definition fx_observe_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_observe_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxObserveNested events => exists groups,
      Forall2 (fx_nested_machine_event_source source) events groups /\ bodies = concat groups
  | FxObserveQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxObserveMap event =>
      Forall2 (fx_nested_entry_source source) (fx_observe_map_entries event) bodies
  | FxObserveCase _ => bodies = []
  end.

(** The receipt budget sums per-invocation callback budgets over the captured trace. *)
Definition fx_observe_event_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_observe_event X C A) : nat :=
  match event with
  | FxObserveNested events =>
      fold_right (fun e n => fx_nested_machine_external_budget budget e + n) 0 events
  | FxObserveQuery events => fx_declared_external_trace_budget budget events
  | FxObserveMap event => fx_nested_entries_budget budget (fx_observe_map_entries event)
  | FxObserveCase _ => 0
  end.

(** Every constraint enqueued by a component belongs to the original system. *)
Definition fx_observe_schedule_targets_within {X C} (EX : encoding X)
    (constraints : list C) (schedule : list (ObservationComponent.t X C)) : Prop :=
  forall component x c, In component schedule ->
    In c (index_get EX (NestedPlan.targets (ObservationComponent.code component)) x) ->
    In c constraints.

(** One captured execution carries all source bodies and its input-derived frame bound. *)
Definition fx_observe_execute_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (EC : encoding C) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B)
    (schedule : list (ObservationComponent.t X C)) (evict : bool) (fuel : positive),
    fx_nested_machine_source_laws EX L S source budget ->
    fx_observe_schedule_targets_within EX (System.constraints S) schedule ->
    let '(out, events) := fx_observe_execute EX L mode S schedule evict fuel in
    exists bodies, Forall2 (fx_observe_event_source source) events bodies /\
      out = observation_execute EX L mode S schedule evict fuel /\
      fx_observe_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_execute_input_budget EX L mode S schedule evict fuel +
        fold_right (fun e n => fx_observe_event_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveExecuteAdequacy`

Card: AUD-FX-OBS-EXEC

Source destination: `theories/Fixpoint/FixpointAuditObserveExecuteAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveExecute.

Theorem fx_observe_execute_erasure :
  FixpointAuditObserveExecute.fx_observe_execute_erasure_statement.
Theorem fx_observe_execute_input_bound :
  FixpointAuditObserveExecute.fx_observe_execute_input_bound_statement.
Theorem fx_observe_execute_source :
  FixpointAuditObserveExecute.fx_observe_execute_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveExpireCheck

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveExpireCheck.v`.

```rocq
(** * Observation expiration-map validation

    Structural comparison follows the first trie and stops at the first failed subcomparison.
    For example, a failed left child suppresses its parent value and right child.
    Builds on: FixpointAuditObserveCompare and CollectionsTrie. *)
From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditWorklistCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObserveCompare.
Import List.ListNotations.

Inductive fx_expire_check_event (X : Type) : Type :=
  | FxExpireCheckCase
  | FxExpireCheckCompare (events : list (fx_observe_compare_event X)).
Arguments FxExpireCheckCase {X}.
Arguments FxExpireCheckCompare {X} _.

(** The relation compares actual stored lists, using [] for an absent opposite binding. *)
Definition fx_expire_check_value {X} (EX : encoding X) (entry : X * list X)
    (opposite : option (X * list X)) : bool * list (fx_expire_check_event X) :=
  let ys := match opposite with Some (_, found) => found | None => [] end in
  let '(out, events) := fx_observe_seteq EX (snd entry) ys in
  (out, [FxExpireCheckCompare events]).

(** Each trie branch follows the source's selective nested matches. *)
Fixpoint fx_expire_check_ne {X} (EX : encoding X) (first : Trie.ne (X * list X))
    (second : Trie.t (X * list X)) : bool * list (fx_expire_check_event X) :=
  match first with
  | Trie.N001 r =>
      let '(out, events) := fx_expire_check_ne EX r (Trie.right second) in
      (out, FxExpireCheckCase :: events)
  | Trie.N010 v =>
      let '(out, events) := fx_expire_check_value EX v (Trie.value second) in
      (out, FxExpireCheckCase :: events)
  | Trie.N011 v r =>
      let '(test, events) := fx_expire_check_value EX v (Trie.value second) in
      if test then
        let '(out, later) := fx_expire_check_ne EX r (Trie.right second) in
        (out, FxExpireCheckCase :: events ++ later)
      else (false, FxExpireCheckCase :: events)
  | Trie.N100 l =>
      let '(out, events) := fx_expire_check_ne EX l (Trie.left second) in
      (out, FxExpireCheckCase :: events)
  | Trie.N101 l r =>
      let '(test, events) := fx_expire_check_ne EX l (Trie.left second) in
      if test then
        let '(out, later) := fx_expire_check_ne EX r (Trie.right second) in
        (out, FxExpireCheckCase :: events ++ later)
      else (false, FxExpireCheckCase :: events)
  | Trie.N110 l v =>
      let '(test, events) := fx_expire_check_ne EX l (Trie.left second) in
      if test then
        let '(out, later) := fx_expire_check_value EX v (Trie.value second) in
        (out, FxExpireCheckCase :: events ++ later)
      else (false, FxExpireCheckCase :: events)
  | Trie.N111 l v r =>
      let '(test, events) := fx_expire_check_ne EX l (Trie.left second) in
      if test then
        let '(middle, mid_events) := fx_expire_check_value EX v (Trie.value second) in
        if middle then
          let '(out, later) := fx_expire_check_ne EX r (Trie.right second) in
          (out, FxExpireCheckCase :: events ++ mid_events ++ later)
        else (false, FxExpireCheckCase :: events ++ mid_events)
      else (false, FxExpireCheckCase :: events)
  end.

(** A directed map comparison processes its first trie's actual shape. *)
Definition fx_expire_check_directed {X} (EX : encoding X) (first second : Map.t X (list X)) :
    bool * list (fx_expire_check_event X) :=
  match first with
  | Trie.Empty => (true, [FxExpireCheckCase])
  | Trie.Nodes n =>
      let '(out, events) := fx_expire_check_ne EX n second in
      (out, FxExpireCheckCase :: events)
  end.

(** Both directed map comparisons execute because their enclosing andb is strict. *)
Definition fx_expire_check {X} (EX : encoding X) (left_map right_map : Map.t X (list X)) :
    bool * list (fx_expire_check_event X) :=
  let '(a, first) := fx_expire_check_directed EX left_map right_map in
  let '(b, second) := fx_expire_check_directed EX right_map left_map in
  (a && b, FxExpireCheckCase :: first ++ second).

(** The selected trace counts trie frames and every captured set comparison. *)
Definition fx_expire_check_work {X} (events : list (fx_expire_check_event X)) : nat :=
  fold_right (fun e n => n + match e with
    | FxExpireCheckCase => 1
    | FxExpireCheckCompare body => fx_observe_compare_work body
    end) 0 events.

(** This upper bound covers both children and values, including branches skipped on failure. *)
Fixpoint fx_expire_check_ne_budget {X} (EX : encoding X) (first : Trie.ne (X * list X))
    (second : Trie.t (X * list X)) : nat :=
  let vbudget := fun v => fx_observe_seteq_budget EX (snd v)
    (match Trie.value second with Some (_, ys) => ys | None => [] end) in
  match first with
  | Trie.N001 r => 1 + fx_expire_check_ne_budget EX r (Trie.right second)
  | Trie.N010 v => 1 + vbudget v
  | Trie.N011 v r => 1 + vbudget v + fx_expire_check_ne_budget EX r (Trie.right second)
  | Trie.N100 l => 1 + fx_expire_check_ne_budget EX l (Trie.left second)
  | Trie.N101 l r => 1 + fx_expire_check_ne_budget EX l (Trie.left second) +
      fx_expire_check_ne_budget EX r (Trie.right second)
  | Trie.N110 l v => 1 + fx_expire_check_ne_budget EX l (Trie.left second) + vbudget v
  | Trie.N111 l v r => 1 + fx_expire_check_ne_budget EX l (Trie.left second) + vbudget v +
      fx_expire_check_ne_budget EX r (Trie.right second)
  end.

(** The directed bound includes the outer trie match. *)
Definition fx_expire_check_directed_budget {X} (EX : encoding X)
    (first second : Map.t X (list X)) : nat :=
  match first with
  | Trie.Empty => 1
  | Trie.Nodes n => 1 + fx_expire_check_ne_budget EX n second
  end.

(** Both directions contribute independent input-derived upper bounds. *)
Definition fx_expire_check_budget {X} (EX : encoding X) (left_map right_map : Map.t X (list X))
    : nat :=
  1 + fx_expire_check_directed_budget EX left_map right_map +
    fx_expire_check_directed_budget EX right_map left_map.

(** The exact map-check result and source-frame budget follow one captured traversal. *)
Definition fx_expire_check_statement : Prop :=
  forall (X : Type) (EX : encoding X) (left_map right_map : Map.t X (list X)),
    let '(out, events) := fx_expire_check EX left_map right_map in
    out = observation_expire_check EX left_map right_map /\
      fx_expire_check_work events <= fx_expire_check_budget EX left_map right_map.

(** Set-comparison events carry only their own actual encoder callback bodies. *)
Definition fx_expire_check_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_expire_check_event X) (bodies : list (list B)) : Prop :=
  match event with
  | FxExpireCheckCase => bodies = []
  | FxExpireCheckCompare events => exists groups,
      Forall2 (fx_observe_compare_source source) events groups /\ bodies = concat groups
  end.

(** Only selected comparisons contribute external encoder-call budgets. *)
Definition fx_expire_check_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_expire_check_event X) : nat :=
  match event with
  | FxExpireCheckCase => 0
  | FxExpireCheckCompare events =>
      fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events
  end.

(** The same selective traversal provides exact output, bodies and an input-derived bound. *)
Definition fx_expire_check_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (left_map right_map : Map.t X (list X)),
    fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_expire_check EX left_map right_map in
    exists bodies, Forall2 (fx_expire_check_event_source source) events bodies /\
      out = observation_expire_check EX left_map right_map /\
      fx_expire_check_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_expire_check_budget EX left_map right_map +
        fold_right (fun e n => fx_expire_check_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveExpireCheckAdequacy`

Card: AUD-FX-OBS-PRIMS

Source destination: `theories/Fixpoint/FixpointAuditObserveExpireCheckAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveExpireCheck.

Theorem fx_expire_check_correct :
  FixpointAuditObserveExpireCheck.fx_expire_check_statement.
Theorem fx_expire_check_source :
  FixpointAuditObserveExpireCheck.fx_expire_check_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveExpiry

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveExpiry.v`.

```rocq
(** * Observation lifetime searches

    The last-reader search considers later components before an earlier component.
    For example, a found later use avoids constructing the earlier component's set.
    Builds on: FixpointObserve and the counted collection operations. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditMap.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointObserve
  FixpointAuditWorklist.
From Galois.Fixpoint Require Import FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks
  FixpointAuditObserveExecute.
Import List.ListNotations.

Inductive fx_observe_expiry_event (X C : Type) : Type :=
  | FxExpirySet (events : list (audit_set_event X (fx_encoder_entry X)))
  | FxExpiryReaders (events : list (audit_map_event X (list C) (fx_encoder_entry X)))
  | FxExpiryMap (events : list (audit_map_event X (list X) (fx_encoder_entry X)))
  | FxExpiryTarget (constraint : C) (target : X)
  | FxExpiryCase.
Arguments FxExpirySet {X C} _.
Arguments FxExpiryReaders {X C} _.
Arguments FxExpiryMap {X C} _.
Arguments FxExpiryTarget {X C} _ _.
Arguments FxExpiryCase {X C}.

(** Every reader's actual target is checked, even if an earlier target matched. *)
Fixpoint fx_observe_reader_uses {X C A} (EX : encoding X) (S : System.t X C A)
    (members : FinSet.t X) (cs : list C) : bool * list (fx_observe_expiry_event X C) :=
  match cs with
  | [] => (false, [FxExpiryCase])
  | c :: rest =>
      let target := System.target S c in
      let '(present, mem) := audit_finset_mem (fx_index_encoder EX) target members in
      let '(later, tail) := fx_observe_reader_uses EX S members rest in
      (present || later, FxExpiryCase :: FxExpiryTarget c target :: FxExpirySet mem :: tail)
  end.

(** Membership and reader lookup are both evaluated for the current component. *)
Definition fx_observe_component_uses {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (members : FinSet.t X) (x : X) :
    bool * list (fx_observe_expiry_event X C) :=
  let '(self, mem) := audit_finset_mem (fx_index_encoder EX) x members in
  let '(found, read) := audit_map_get (fx_index_encoder EX) x (readers ix) in
  let cs := match found with Some items => items | None => [] end in
  let '(used, calls) := fx_observe_reader_uses EX S members cs in
  (self || used, FxExpiryCase :: FxExpirySet mem :: FxExpiryReaders read :: calls).

(** The tail is searched first, and only a missing result inspects this component. *)
Fixpoint fx_observe_last_reader {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x : X) :
    option X * list (fx_observe_expiry_event X C) :=
  match order with
  | [] => (None, [FxExpiryCase])
  | [] :: rest =>
      let '(out, events) := fx_observe_last_reader EX S ix rest x in
      (out, FxExpiryCase :: events)
  | (h :: body) :: rest =>
      let '(last, later) := fx_observe_last_reader EX S ix rest x in
      match last with
      | Some found => (Some found, FxExpiryCase :: later)
      | None =>
          let '(members, set) := audit_finset_of_list (fx_index_encoder EX) (h :: body) in
          let '(used, calls) := fx_observe_component_uses EX S ix members x in
          (if used then Some h else None, FxExpiryCase :: later ++ FxExpirySet set :: calls)
      end
  end.

(** Expiration writes capture both index lookup and persistent update for each selected key. *)
Fixpoint fx_observe_expiry_fold {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (xs : list X) :
    Map.t X (list X) * list (fx_observe_expiry_event X C) :=
  match xs with
  | [] => (Map.empty, [FxExpiryCase])
  | x :: rest =>
      let '(before, tail) := fx_observe_expiry_fold EX S ix order rest in
      let '(last, calls) := fx_observe_last_reader EX S ix order x in
      match last with
      | None => (before, FxExpiryCase :: tail ++ calls)
      | Some h =>
          let '(old, read) := audit_map_get (fx_index_encoder EX) h before in
          let previous := match old with Some ys => ys | None => [] end in
          let '(after, write) := audit_map_set (fx_index_encoder EX) h (x :: previous) before in
          (after, FxExpiryCase :: tail ++ calls ++ [FxExpiryMap read; FxExpiryMap write])
      end
  end.

(** The fold returns the same map as the source expiration traversal. *)
Definition fx_observe_expiry_fold_statement : Prop :=
  forall (X C A : Type) (EX : encoding X) (S : System.t X C A) (ix : sys_index X C)
    (order : list (list X)) (xs : list X),
    fst (fx_observe_expiry_fold EX S ix order xs) =
      fold_right (fun x expiration =>
        match observation_last_reader EX S ix order x with
        | Some h => index_push EX x h expiration
        | None => expiration
        end) Map.empty xs.

(** The frame fold charges concrete set and map child traces and selected target calls. *)
Definition fx_observe_expiry_event_work {X C} (event : fx_observe_expiry_event X C) : nat :=
  match event with
  | FxExpirySet events => audit_finset_source_work (@length (fx_encoder_entry X)) events
  | FxExpiryReaders events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxExpiryMap events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxExpiryTarget _ _ | FxExpiryCase => 1
  end.

(** The work is computed from the same captured lifetime-search events. *)
Definition fx_observe_expiry_work {X C} (events : list (fx_observe_expiry_event X C)) : nat :=
  fold_right (fun event total => fx_observe_expiry_event_work event + total) 0 events.

(** The set construction bound charges every source list occurrence. *)
Fixpoint fx_observe_expiry_set_budget {X} (EX : encoding X) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest => 4 + 16 * Pos.size_nat (encode EX x) + fx_observe_expiry_set_budget EX rest
  end.

(** Reader checking charges each actual target and finite-set membership. *)
Fixpoint fx_observe_reader_uses_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest => 9 + 5 * Pos.size_nat (encode EX (System.target S c)) +
      fx_observe_reader_uses_budget EX S rest
  end.

(** The use bound includes the reader-index lookup and all its actual readers. *)
Definition fx_observe_component_uses_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (x : X) : nat :=
  16 + 10 * Pos.size_nat (encode EX x) + fx_observe_reader_uses_budget EX S (readers_of EX ix x).

(** The last-reader bound follows the real selective branch after the recursive tail. *)
Fixpoint fx_observe_last_reader_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x : X) : nat :=
  match order with
  | [] => 1
  | [] :: rest => 1 + fx_observe_last_reader_budget EX S ix rest x
  | (h :: body) :: rest =>
      1 + fx_observe_last_reader_budget EX S ix rest x +
      match observation_last_reader EX S ix rest x with
      | Some _ => 0
      | None => fx_observe_expiry_set_budget EX (h :: body) +
          fx_observe_component_uses_budget EX S ix x
      end
  end.

(** The fold bound charges the selected last-reader search and optional map operations. *)
Fixpoint fx_observe_expiry_fold_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (xs : list X) : nat :=
  match xs with
  | [] => 1
  | x :: rest =>
      1 + fx_observe_expiry_fold_budget EX S ix order rest +
      fx_observe_last_reader_budget EX S ix order x +
      match observation_last_reader EX S ix order x with
      | None => 0
      | Some h => 10 + 21 * Pos.size_nat (encode EX h)
      end
  end.

(** The captured expiration fold has an input-derived source-frame bound. *)
Definition fx_observe_expiry_fold_bound_statement : Prop :=
  forall (X C A : Type) (EX : encoding X) (S : System.t X C A) (ix : sys_index X C)
    (order : list (list X)) (xs : list X),
    let '(_, events) := fx_observe_expiry_fold EX S ix order xs in
    fx_observe_expiry_work events <= fx_observe_expiry_fold_budget EX S ix order xs.

(** Source receipts bind every captured encoder and original-system target invocation. *)
Definition fx_observe_expiry_event_source {X C A B}
    (source : fx_declared_callback_source X C A B) (event : fx_observe_expiry_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxExpirySet events => Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies
  | FxExpiryReaders events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxExpiryMap events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | FxExpiryTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxExpiryCase => bodies = []
  end.

(** These laws describe individual encodings and target callbacks on their actual inputs. *)
Definition fx_observe_expiry_source_laws {X C A B} (EX : encoding X) (S : System.t X C A)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c).

(** The callback budget charges every encoder entry and selected original target call. *)
Definition fx_observe_expiry_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_observe_expiry_event X C) : nat :=
  match event with
  | FxExpirySet events => fx_nested_entries_budget budget (fx_nested_entries events)
  | FxExpiryReaders events =>
      fx_nested_entries_budget budget (flat_map fx_observe_map_entries events)
  | FxExpiryMap events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries events)
  | FxExpiryTarget c _ => fx_budget_target budget c
  | FxExpiryCase => 0
  end.

(** A single expiration-fold witness supplies its erasure, frame bound and callback bodies. *)
Definition fx_observe_expiry_fold_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (ix : sys_index X C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (order : list (list X)) (xs : list X),
    fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_expiry_fold EX S ix order xs in
    exists bodies, Forall2 (fx_observe_expiry_event_source source) events bodies /\
      out = fold_right (fun x expiration =>
        match observation_last_reader EX S ix order x with
        | Some h => index_push EX x h expiration
        | None => expiration
        end) Map.empty xs /\
      fx_observe_expiry_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_expiry_fold_budget EX S ix order xs +
        fold_right (fun e n => fx_observe_expiry_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveExpiryAdequacy`

Card: AUD-FX-OBS-CHECK

Source destination: `theories/Fixpoint/FixpointAuditObserveExpiryAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveExpiry.

Theorem fx_observe_expiry_fold_bound :
  FixpointAuditObserveExpiry.fx_observe_expiry_fold_bound_statement.
Theorem fx_observe_expiry_fold_source :
  FixpointAuditObserveExpiry.fx_observe_expiry_fold_source_statement.
Theorem fx_observe_expiry_fold_correct :
  FixpointAuditObserveExpiry.fx_observe_expiry_fold_statement.
```

## Galois.Fixpoint.FixpointAuditObserveForward

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveForward.v`.

```rocq
(** * Observation forward-boundary checking

    Every constraint target is checked against the current component.
    For example, only a target inside the component causes its dependencies to be inspected.
    Builds on: FixpointObserve and the counted finite-set operations. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointObserve FixpointAuditIndex.
Import List.ListNotations.

Inductive fx_observe_forward_event (X C B : Type) : Type :=
  | FxForwardIndex (events : list (fx_index_nested_event X C B))
  | FxForwardSet (events : list (audit_set_event X B))
  | FxForwardConcat (suffix : list (list X))
  | FxForwardBuild (size : nat)
  | FxForwardCase.
Arguments FxForwardIndex {X C B} _.
Arguments FxForwardSet {X C B} _.
Arguments FxForwardConcat {X C B} _.
Arguments FxForwardBuild {X C B} _.
Arguments FxForwardCase {X C B}.

(** A dependency scan evaluates every finite-set lookup, including after a failed test. *)
Fixpoint fx_forward_deps {X C B} (cb : fx_index_external_model X C B)
    (later : FinSet.t X) (deps : list X) : bool * list (fx_observe_forward_event X C B) :=
  match deps with
  | [] => (true, [FxForwardCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x later in
      let '(out, events) := fx_forward_deps cb later rest in
      (negb present && out, FxForwardCase :: FxForwardSet mem :: events)
  end.

(** Target membership selects dependency evaluation, but all constraint tails execute. *)
Fixpoint fx_forward_constraints {X C B} (cb : fx_index_external_model X C B)
    (members later : FinSet.t X) (cs : list C) : bool * list (fx_observe_forward_event X C B) :=
  match cs with
  | [] => (true, [FxForwardCase])
  | c :: rest =>
      let '(target, target_body) := fxi_target cb c in
      let '(present, target_mem) := audit_finset_mem (fxi_encode cb) target members in
      let '(current, here) :=
        if present then
          let '(deps, deps_body) := fxi_deps cb c in
          let '(out, events) := fx_forward_deps cb later deps in
          (out, FxForwardIndex [FxiDeps c deps deps_body] :: events)
        else (true, []) in
      let '(out, tail) := fx_forward_constraints cb members later rest in
      (current && out, FxForwardCase :: FxForwardIndex [FxiTarget c target target_body] ::
        FxForwardSet target_mem :: here ++ tail)
  end.

(** A boundary constructs both sets and the actual concatenation of later components. *)
Definition fx_forward_boundary {X C B} (cb : fx_index_external_model X C B)
    (cs : list C) (component : list X) (suffix : list (list X)) :
    bool * list (fx_observe_forward_event X C B) :=
  let '(members, member_events) := audit_finset_of_list (fxi_encode cb) component in
  let later_list := concat suffix in
  let '(later, later_events) := audit_finset_of_list (fxi_encode cb) later_list in
  let '(out, events) := fx_forward_constraints cb members later cs in
  (out, FxForwardSet member_events :: FxForwardConcat suffix :: FxForwardSet later_events ::
    events).

(** Each boundary receives exactly the unprocessed component suffix. *)
Fixpoint fx_observe_forward {X C B} (cb : fx_index_external_model X C B) (cs : list C)
    (order : list (list X)) : bool * list (fx_observe_forward_event X C B) :=
  match order with
  | [] => (true, [FxForwardCase])
  | component :: rest =>
      let '(here, events) := fx_forward_boundary cb cs component rest in
      let '(later, tail) := fx_observe_forward cb cs rest in
      (here && later, FxForwardCase :: events ++ tail)
  end.

(** Captured frame work includes the actual concatenation lengths and callback bodies. *)
Definition fx_observe_forward_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_forward_event X C B) : nat :=
  match event with
  | FxForwardIndex events => fx_index_adapter_work ib events
  | FxForwardSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxForwardConcat suffix => 2 + length suffix + length (concat suffix)
  | FxForwardBuild size => 2 + 2 * size
  | FxForwardCase => 1
  end.

(** The frame work folds the selected events from one traversal. *)
Definition fx_observe_forward_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_forward_event X C B)) : nat :=
  fold_right (fun e n => fx_observe_forward_event_work ib e + n) 0 events.

(** The dependency bound charges each actual declared read. *)
Fixpoint fx_forward_deps_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (deps : list X) : nat :=
  match deps with
  | [] => 1
  | x :: rest => 8 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_forward_deps_budget EX ib rest
  end.

(** The constraint budget follows target membership and includes only selected deps callbacks. *)
Fixpoint fx_forward_constraints_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B)
    (members : FinSet.t X) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | c :: rest =>
      let target := System.target S c in
      12 + fxi_target_bound ib c + fxi_encode_bound ib target +
        5 * Pos.size_nat (encode EX target) +
        (if FinSet.mem EX target members then
          3 + fxi_deps_bound ib c + fx_forward_deps_budget EX ib (System.deps SS c) else 0) +
        fx_forward_constraints_budget EX S SS ib members rest
  end.

(** The bound pays for both constructed sets and the source concatenation. *)
Definition fx_forward_boundary_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B)
    (component : list X) (suffix : list (list X)) : nat :=
  let later := concat suffix in
  2 + length suffix + length later + fxi_set_input_budget EX ib component +
    fxi_set_input_budget EX ib later +
    fx_forward_constraints_budget EX S SS ib (FinSet.of_list EX component) (System.constraints S).

(** Each source boundary contributes its own input-derived charge. *)
Fixpoint fx_observe_forward_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (order : list (list X)) : nat :=
  match order with
  | [] => 1
  | component :: rest => 1 + fx_forward_boundary_budget EX S SS ib component rest +
      fx_observe_forward_budget EX S SS ib rest
  end.

(** Constructing observation_boundaries contributes its own list frames. *)
Definition fx_observe_forward_run {X C B} (cb : fx_index_external_model X C B) (cs : list C)
    (order : list (list X)) : bool * list (fx_observe_forward_event X C B) :=
  let '(out, events) := fx_observe_forward cb cs order in
  (out, FxForwardBuild (length order) :: events).

(** Index and set events retain actual source bodies at each selected call. *)
Definition fx_observe_forward_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_observe_forward_event X C B) : Prop :=
  match event with
  | FxForwardIndex events => fx_index_external_trace_adequacy source events
  | FxForwardSet events => fxi_set_external_adequacy source events
  | _ => True
  end.

(** The captured boundary check retains its source result, callbacks and input-derived work. *)
Definition fx_observe_forward_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B) (order : list (list X)),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    (forall x, let '(out, body) := fxi_encode cb x in fxi_encode_source source x out body) ->
    (forall c, let '(out, body) := fxi_target cb c in fxi_target_source source c out body) ->
    (forall c, let '(out, body) := fxi_deps cb c in fxi_deps_source source c out body) ->
    let '(out, events) := fx_observe_forward_run cb (System.constraints S) order in
    Forall (fx_observe_forward_event_source source) events /\
      out = observation_forward_check EX S SS order /\
      fx_observe_forward_work ib events <=
        2 + 2 * length order + fx_observe_forward_budget EX S SS ib order.
```

### Future proofs in `FixpointAuditObserveForwardAdequacy`

Card: AUD-FX-OBS-PRIMS

Source destination: `theories/Fixpoint/FixpointAuditObserveForwardAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveForward.

Theorem fx_observe_forward_source :
  FixpointAuditObserveForward.fx_observe_forward_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveInduced

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveInduced.v`.

```rocq
(** * Observation induced-graph callbacks

    Each component graph filters the dependency graph by its concrete member set.
    For example, an outgoing edge is retained only after checking its actual target.
    Builds on: FixpointAuditScheduleWrapper and the counted set model. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphAuditBase GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointAuditIndex
  FixpointAuditScheduleWrapper.
Import List.ListNotations.

Inductive fx_induced_event (X C B : Type) : Type :=
  | FxInducedDependency (events : list (fx_dep_event X C B))
  | FxInducedSet (events : list (audit_set_event X B))
  | FxInducedEncode (x : X) (code : positive) (body : list B)
  | FxInducedCase.
Arguments FxInducedDependency {X C B} _.
Arguments FxInducedSet {X C B} _.
Arguments FxInducedEncode {X C B} _ _ _.
Arguments FxInducedCase {X C B}.

(** Every input vertex is checked, including repeated vertices. *)
Fixpoint fx_induced_filter_vertices {X C B} (cb : fx_index_external_model X C B)
    (keep : FinSet.t X) (vertices : list X) : list X * list (fx_induced_event X C B) :=
  match vertices with
  | [] => ([], [FxInducedCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x keep in
      let '(later, events) := fx_induced_filter_vertices cb keep rest in
      (if present then x :: later else later, FxInducedCase :: FxInducedSet mem :: events)
  end.

(** Every edge checks its actual target and keeps the original pair and order. *)
Fixpoint fx_induced_filter_edges {X C B} (cb : fx_index_external_model X C B)
    (keep : FinSet.t X) (edges : list (X * X)) :
    list (X * X) * list (fx_induced_event X C B) :=
  match edges with
  | [] => ([], [FxInducedCase])
  | edge :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) (snd edge) keep in
      let '(later, events) := fx_induced_filter_edges cb keep rest in
      (if present then edge :: later else later, FxInducedCase :: FxInducedSet mem :: events)
  end.

(** The graph's outgoing closure first invokes the concrete dependency-graph closure. *)
Definition fx_induced_out {X C B} (cb : fx_index_external_model X C B) (ix : sys_index X C)
    (keep : FinSet.t X) (x : X) : list (X * X) * list (fx_induced_event X C B) :=
  let '(edges, dependency) := fx_dep_out cb ix x in
  let '(out, filtered) := fx_induced_filter_edges cb keep edges in
  (out, FxInducedDependency dependency :: filtered).

(** The induced graph's encoder closure records the original actual encoder body. *)
Definition fx_induced_encoder {X C B} (cb : fx_index_external_model X C B) (x : X) :
    positive * list (fx_induced_event X C B) :=
  let '(code, body) := fxi_encode cb x in (code, [FxInducedEncode x code body]).

(** Graph preparation uses the induced out closure and concrete pair projections. *)
Definition fx_induced_prepare_cb {X C B} (cb : fx_index_external_model X C B)
    (ix : sys_index X C) (keep : FinSet.t X) :
    audit_prepare_callback_model X (X * X) (fx_induced_event X C B) :=
  AuditPrepareCallbackModel X (X * X) (fx_induced_event X C B)
    (fx_induced_out cb ix keep) (fun edge => (snd edge, [FxInducedCase])) (fx_induced_encoder cb).

(** WTO graph traversals use the same encoder and concrete target projection. *)
Definition fx_induced_dfs_cb {X C B} (cb : fx_index_external_model X C B) :
    audit_dfs_callback_model X (X * X) (fx_induced_event X C B) :=
  AuditDfsCallbackModel X (X * X) (fx_induced_event X C B)
    (fun edge => (snd edge, [FxInducedCase])) (fx_induced_encoder cb).

(** A captured induced event charges its selected dependency or finite-set child body. *)
Definition fx_induced_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_induced_event X C B) : nat :=
  8 + match event with
  | FxInducedDependency events => fx_dep_events_work ib events
  | FxInducedSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxInducedEncode _ _ body => fxi_body_work ib body
  | FxInducedCase => 0
  end.

(** Work folds a concrete induced-closure body. *)
Definition fx_induced_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_induced_event X C B)) : nat :=
  fold_right (fun event n => fx_induced_event_work ib event + n) 0 events.

(** Filtering budgets use every input endpoint and the original encoder's actual input budget. *)
Fixpoint fx_induced_vertices_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (vertices : list X) : nat :=
  match vertices with
  | [] => 8
  | x :: rest => 32 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_induced_vertices_budget EX ib rest
  end.

(** Outgoing work includes the dependency callback and all filtered edge targets. *)
Definition fx_induced_out_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B) (x : X) :
    nat :=
  fx_dep_out_budget EX S SS ix ib x + 8 +
    fx_induced_vertices_budget EX ib
      (distinct_unknowns EX (fx_dep_out_values_native EX S SS ix x)).

(** Each body is tied to the concrete underlying encoder or dependency callback source. *)
Definition fx_induced_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_induced_event X C B) : Prop :=
  match event with
  | FxInducedDependency events => fx_dep_body_source source events
  | FxInducedSet events => fxi_set_external_adequacy source events
  | FxInducedEncode x code body => fxi_encode_source source x code body
  | FxInducedCase => True
  end.

(** The actual induced out closure preserves selected edges and has an input-derived bound. *)
Definition fx_induced_out_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B) (keep : FinSet.t X) (x : X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb source ->
    let '(out, events) := fx_induced_out cb ix keep x in
    Forall (fx_induced_event_source source) events /\
      out = filter (fun edge => FinSet.mem EX (snd edge) keep)
        (map (fun y => (x, y)) (distinct_unknowns EX
          (flat_map (fun c => System.target S c :: System.side_targets SS c) (readers_of EX ix
    x)))) /\
      fx_induced_work ib events <= fx_induced_out_budget EX S SS ix ib x.
```

### Future proofs in `FixpointAuditObserveInducedAdequacy`

Card: AUD-FX-OBS-COMPILE

Source destination: `theories/Fixpoint/FixpointAuditObserveInducedAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveInduced.

Theorem fx_induced_out_source :
  FixpointAuditObserveInduced.fx_induced_out_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveNumber

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveNumber.v`.

```rocq
(** * Numbered observation-system closures

    The numbered system retains a table of original constraint occurrences.
    For example, two equal constraints at different positions retain separate labels.
    Builds on: FixpointObserve and CollectionsAuditMap. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditEncoding
  CollectionsAuditEncoderBudget.
From Galois.Fixpoint Require Import FixpointObserve.
Import List.ListNotations.

(** Building the numbered table captures each recursive map write in source order. *)
Fixpoint fx_observe_number {C} (next : nat) (cs : list C) :
    Map.t nat C * list (audit_map_event nat C audit_nat_encoding_event) :=
  match cs with
  | [] => (Map.empty, [])
  | c :: rest =>
      let '(table, later) := fx_observe_number (S next) rest in
      let '(result, write) := audit_map_set audit_nat_encode next c table in
      (result, later ++ write)
  end.

(** A label closure captures the lookup and preserves fallback on a missing index. *)
Definition fx_observe_label {C} (fallback : C) (table : Map.t nat C) (i : nat) :
    C * list (audit_map_event nat C audit_nat_encoding_event) :=
  let '(found, events) := audit_map_get audit_nat_encode i table in
  (match found with Some c => c | None => fallback end, events).

(** The table budget counts list traversal, encoded-key length and persistent map writes. *)
Fixpoint fx_observe_number_budget {C} (next : nat) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | _ :: rest =>
      3 + audit_nat_input_budget next + 16 * Pos.size_nat (encode nat_encoding next) +
        fx_observe_number_budget (S next) rest
  end.

(** The label budget includes encoding and persistent-map lookup for this actual index. *)
Definition fx_observe_label_budget (i : nat) : nat :=
  6 + audit_nat_input_budget i + 5 * Pos.size_nat (encode nat_encoding i).

(** Numbering has the same table and an input-derived source-frame bound. *)
Definition fx_observe_number_source_statement : Prop :=
  forall (C : Type) (next : nat) (cs : list C),
    let '(out, events) := fx_observe_number next cs in
    out = observation_number next cs /\
    audit_map_source_work (audit_nat_events_work) events <=
      fx_observe_number_budget next cs.

(** The lookup closure has the same label and an input-derived source-frame bound. *)
Definition fx_observe_label_source_statement : Prop :=
  forall (C : Type) (fallback : C) (table : Map.t nat C) (i : nat),
    let '(out, events) := fx_observe_label fallback table i in
    out = observation_label fallback table i /\
    audit_map_source_work (audit_nat_events_work) events <= fx_observe_label_budget i.
```

### Future proofs in `FixpointAuditObserveNumberAdequacy`

Card: AUD-FX-OBS-EXEC

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveNumber.

Theorem fx_observe_number_source :
  FixpointAuditObserveNumber.fx_observe_number_source_statement.
Theorem fx_observe_label_source :
  FixpointAuditObserveNumber.fx_observe_label_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveNumberCallbacks

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberCallbacks.v`.

```rocq
(** * Numbered observation callback closures

    Target and RHS closures first look up an occurrence label, then invoke the original system.
    For example, an absent index uses the original fallback constraint.
    Builds on: FixpointAuditObserveNumber and FixpointAuditWorklistCallbacks. *)
From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsMap CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointObserve
  FixpointAuditWorklistCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObserveNumber.
Import List.ListNotations.

(** One closure invocation retains its concrete label lookup and original target call. *)
Definition fx_observe_numbered_target {X C A} (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (i : nat) : X * C * list (audit_map_event nat C
    audit_nat_encoding_event) :=
  let '(label, events) := fx_observe_label fallback table i in
  (System.target S label, label, events).

(** One closure invocation retains its concrete label lookup and original RHS call. *)
Definition fx_observe_numbered_rhs {X C A} (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (i : nat) :
    Query.t X A * C * list (audit_map_event nat C audit_nat_encoding_event) :=
  let '(label, events) := fx_observe_label fallback table i in
  (System.rhs S label, label, events).

(** Actual original target and RHS calls have individual body witnesses and bounds. *)
Definition fx_observe_numbered_source_laws {X C A B} (S : System.t X C A)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c).

(** The actual target call retains its original callback body and internal lookup cost. *)
Definition fx_observe_numbered_target_source_statement : Prop :=
  forall (X C A B : Type) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (i : nat),
    fx_observe_numbered_source_laws S source budget ->
    let '(out, label, events) := fx_observe_numbered_target S fallback table i in
    exists body, fx_source_target source label out body /\
      label = observation_label fallback table i /\
      out = System.target S (observation_label fallback table i) /\
      audit_map_source_work audit_nat_events_work events +
        fx_one_body_work (fx_body_weight budget) body <=
        fx_observe_label_budget i + fx_budget_target budget (observation_label fallback table i).

(** The actual RHS call retains its original callback body and internal lookup cost. *)
Definition fx_observe_numbered_rhs_source_statement : Prop :=
  forall (X C A B : Type) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (i : nat),
    fx_observe_numbered_source_laws S source budget ->
    let '(out, label, events) := fx_observe_numbered_rhs S fallback table i in
    exists body, fx_source_rhs source label out body /\
      label = observation_label fallback table i /\
      out = System.rhs S (observation_label fallback table i) /\
      audit_map_source_work audit_nat_events_work events +
        fx_one_body_work (fx_body_weight budget) body <=
        fx_observe_label_budget i + fx_budget_rhs budget (observation_label fallback table i).
```

### Future proofs in `FixpointAuditObserveNumberCallbacksAdequacy`

Card: AUD-FX-OBS-EXEC

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberCallbacksAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveNumberCallbacks.

Theorem fx_observe_numbered_target_source :
  FixpointAuditObserveNumberCallbacks.fx_observe_numbered_target_source_statement.
Theorem fx_observe_numbered_rhs_source :
  FixpointAuditObserveNumberCallbacks.fx_observe_numbered_rhs_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveNumberExecute

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberExecute.v`.

```rocq
(** * Numbered observation execution

    This execution captures each numbered callback in the same machine tick that invokes it.
    For example, boundary output writes retain their own encoder calls before eviction.
    Builds on: FixpointAuditObserveNumberMachine and FixpointAuditObserveExecute. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested FixpointObserve
  FixpointAuditWorklistCallbacks FixpointAuditNestedMachine FixpointAuditNestedCallbacks
  FixpointAuditObserveExecute.
From Galois.Fixpoint Require Import FixpointAuditObserveNumber FixpointAuditObserveNumberMachine.
Import List.ListNotations.

Inductive fx_number_execute_event (X C A : Type) : Type :=
  | FxNumberExecuteMachine (events : list (fx_number_machine_event X C A))
  | FxNumberExecuteBoundary (events : list (fx_observe_event X nat A))
  | FxNumberExecuteCase.
Arguments FxNumberExecuteMachine {X C A} _.
Arguments FxNumberExecuteBoundary {X C A} _.
Arguments FxNumberExecuteCase {X C A}.

(** A tick performs the counted nested step, then the actual boundary operations if finished. *)
Definition fx_number_execute_tick {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (state : ObservationState.t X nat A + (assignment X A * assignment X A)) :
    (ObservationState.t X nat A + (assignment X A * assignment X A)) *
      list (fx_number_execute_event X C A) :=
  match state with
  | inr finished => (inr finished, [FxNumberExecuteCase])
  | inl current =>
      let component := ObservationState.active current in
      let '(next, machine) := fx_number_machine_step EX L (ObservationComponent.code component)
        mode S fallback table (ObservationState.local current) in
      match next with
      | Some local =>
          (inl (ObservationState.Make component (ObservationState.pending current) local
            (ObservationState.observed current)), [FxNumberExecuteCase; FxNumberExecuteMachine
    machine])
      | None =>
          let values := NestedState.current (ObservationState.local current) in
          let '(output, record_events) := @fx_observe_record X nat A EX L
            (ObservationComponent.outputs component) values (ObservationState.observed current) in
          let '(retained, evict_events) := if evict then
            @fx_observe_evict X nat A EX (ObservationComponent.expire component) values
            else (values, []) in
          let events := [FxNumberExecuteCase; FxNumberExecuteMachine machine;
            FxNumberExecuteBoundary (record_events ++ evict_events); FxNumberExecuteCase] in
          match ObservationState.pending current with
          | [] => (inr (retained, output), events)
          | next :: rest =>
              (inl (ObservationState.Make next rest (observation_start_local next retained)
    output), events)
          end
      end
  end.

(** Binary repetition retains every real tick, even after a finished state. *)
Fixpoint fx_number_execute_repeat {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (fuel : positive) (state : ObservationState.t X nat A + (assignment X A * assignment X A)) :
    (ObservationState.t X nat A + (assignment X A * assignment X A)) *
      list (fx_number_execute_event X C A) :=
  match fuel with
  | xH => fx_number_execute_tick EX L mode S fallback table evict state
  | xO smaller =>
      let '(first, events) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    state in
      let '(out, later) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    first in
      (out, FxNumberExecuteCase :: events ++ later)
  | xI smaller =>
      let '(first, events) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    state in
      let '(second, later) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    first in
      let '(out, last) := fx_number_execute_tick EX L mode S fallback table evict second in
      (out, FxNumberExecuteCase :: events ++ later ++ last)
  end.

(** The machine starts from the actual first component and preserves both returned maps. *)
Definition fx_number_execute {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (schedule : list (ObservationComponent.t X nat)) (evict : bool) (fuel : positive) :
    option (assignment X A * assignment X A) * list (fx_number_execute_event X C A) :=
  match schedule with
  | [] => (Some (Map.empty, Map.empty), [FxNumberExecuteCase])
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
    Map.empty in
      let '(out, events) := fx_number_execute_repeat EX L mode S fallback table evict fuel (inl
    initial) in
      (match out with inl _ => None | inr result => Some result end, FxNumberExecuteCase :: events)
  end.

(** Each event charges its actual nested, label or boundary frames. *)
Definition fx_number_execute_event_work {X C A} (event : fx_number_execute_event X C A) : nat :=
  match event with
  | FxNumberExecuteMachine events => fx_number_machine_work events
  | FxNumberExecuteBoundary events => fx_observe_work nat_encoding events
  | FxNumberExecuteCase => 1
  end.

(** Execution work folds exactly the events captured by the run. *)
Definition fx_number_execute_work {X C A} (events : list (fx_number_execute_event X C A)) : nat :=
  fold_right (fun event n => fx_number_execute_event_work event + n) 0 events.

(** The tick bound adds the concrete label costs only when a constraint is ready. *)
Definition fx_number_execute_tick_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (state : ObservationState.t X nat A + (assignment X A * assignment X A)) : nat :=
  fx_observe_tick_input_budget EX L mode (fx_number_system S fallback table) evict state +
  match state with
  | inr _ => 0
  | inl current => match NestedState.ready (ObservationState.local current) with
      | [] => 0
      | i :: _ => 2 * fx_observe_label_budget i
      end
  end.

(** The binary bound follows the real intermediate states, including finished-state ticks. *)
Fixpoint fx_number_execute_repeat_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (fuel : positive) (state : ObservationState.t X nat A + (assignment X A * assignment X A))
    : nat :=
  let tick := observation_tick EX L mode (fx_number_system S fallback table) evict in
  match fuel with
  | xH => fx_number_execute_tick_budget EX L mode S fallback table evict state
  | xO smaller =>
      let first := observation_repeat tick smaller state in
      1 + fx_number_execute_repeat_budget EX L mode S fallback table evict smaller state +
        fx_number_execute_repeat_budget EX L mode S fallback table evict smaller first
  | xI smaller =>
      let first := observation_repeat tick smaller state in
      let second := observation_repeat tick smaller first in
      1 + fx_number_execute_repeat_budget EX L mode S fallback table evict smaller state +
        fx_number_execute_repeat_budget EX L mode S fallback table evict smaller first +
        fx_number_execute_tick_budget EX L mode S fallback table evict second
  end.

(** The schedule budget starts from the real initial state and charges the empty branch. *)
Definition fx_number_execute_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (schedule : list (ObservationComponent.t X nat)) (evict : bool) (fuel : positive) : nat :=
  match schedule with
  | [] => 1
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
    Map.empty in
      1 + fx_number_execute_repeat_budget EX L mode S fallback table evict fuel (inl initial)
  end.

(** Every machine and boundary event carries the bodies belonging to that actual tick. *)
Definition fx_number_execute_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_number_execute_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxNumberExecuteMachine events => exists groups,
      Forall2 (fx_number_machine_event_source source) events groups /\ bodies = concat groups
  | FxNumberExecuteBoundary events => exists groups,
      Forall2 (fx_observe_event_source (fx_number_passthrough_source source)) events groups /\
        bodies = concat groups
  | FxNumberExecuteCase => bodies = []
  end.

(** External budgets follow the callback invocations actually retained in the run. *)
Definition fx_number_execute_external_budget {X C A B} (budget : fx_declared_callback_budget X
    C A B)
    (event : fx_number_execute_event X C A) : nat :=
  match event with
  | FxNumberExecuteMachine events =>
      fold_right (fun e n => fx_number_machine_external_budget budget e + n) 0 events
  | FxNumberExecuteBoundary events =>
      fold_right (fun e n => fx_observe_event_external_budget (fx_number_passthrough_budget
    budget) e + n)
        0 events
  | FxNumberExecuteCase => 0
  end.

(** One execution witness supplies both maps, captured source bodies and its intermediate-state
    bound. *)
Definition fx_number_execute_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (fallback : C) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (schedule : list (ObservationComponent.t X nat))
    (evict : bool) (fuel : positive),
    In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
    let table := observation_number 0 (System.constraints S) in
    let '(out, events) := fx_number_execute EX L mode S fallback table schedule evict fuel in
    exists bodies, Forall2 (fx_number_execute_event_source source) events bodies /\
      out = observation_execute EX L mode (observation_system S fallback) schedule evict fuel /\
      fx_number_execute_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_number_execute_budget EX L mode S fallback table schedule evict fuel +
        fold_right (fun e n => fx_number_execute_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveNumberExecuteAdequacy`

Card: AUD-FX-OBS-EXEC

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberExecuteAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveNumberExecute.

Theorem fx_number_execute_source :
  FixpointAuditObserveNumberExecute.fx_number_execute_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveNumberMachine

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberMachine.v`.

```rocq
(** * Numbered observation-machine callbacks

    Numbered target and RHS closures capture label lookups at their actual machine invocation.
    For example, a ready constraint reads its label once for RHS and once for target.
    Builds on: FixpointAuditObserveNumberCallbacks and FixpointAuditNestedMachine. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointNested
  FixpointObserve FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditWorklistCallbacks
  FixpointAuditNestedMachine FixpointAuditNestedCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObserveNumber FixpointAuditObserveNumberCallbacks.
Import List.ListNotations.

Inductive fx_number_machine_event (X C A : Type) : Type :=
  | FxNumberMachineNested (events : list (fx_nested_event X nat A))
  | FxNumberMachineRhs (i : nat) (label : C) (out : Query.t X A)
      (events : list (audit_map_event nat C audit_nat_encoding_event))
  | FxNumberMachineTarget (i : nat) (label : C) (out : X)
      (events : list (audit_map_event nat C audit_nat_encoding_event)).
Arguments FxNumberMachineNested {X C A} _.
Arguments FxNumberMachineRhs {X C A} _ _ _ _.
Arguments FxNumberMachineTarget {X C A} _ _ _ _.

(** The shared captured table determines the actual numbered system closures. *)
Definition fx_number_system {X C A} (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) : System.t X nat A :=
  System.Make (seq 0 (length (System.constraints S)))
    (fun i => System.target S (observation_label fallback table i))
    (fun i => System.rhs S (observation_label fallback table i)).

(** A ready step captures its two label calls while executing the original query and updates. *)
Definition fx_number_machine_step {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) (mode : strategy) (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (state : NestedState.t X nat A) :
    option (NestedState.t X nat A) * list (fx_number_machine_event X C A) :=
  let numbered := fx_number_system S fallback table in
  match NestedState.ready state with
  | [] =>
      let '(out, events) := fx_nested_step EX L plan mode numbered state in
      (out, [FxNumberMachineNested events])
  | i :: rest =>
      let values := NestedState.current state in
      let '(rhs, rhs_label, rhs_events) := fx_observe_numbered_rhs S fallback table i in
      let '(answer, query_events) := @fx_model_query X nat A EX L rhs values in
      let '(value, _, sides) := answer in
      let '(target, target_label, target_events) := fx_observe_numbered_target S fallback table i in
      let next := NestedState.Make values rest (NestedState.frames state)
        (NestedState.dirty state) (NestedState.changed state) in
      let '(out, update_events) := fx_nested_updates EX L plan mode ((target, value) :: sides)
    next in
      (Some out, [FxNumberMachineNested [FxNestedCase 6];
        FxNumberMachineRhs i rhs_label rhs rhs_events;
        FxNumberMachineNested [FxNestedQuery query_events];
        FxNumberMachineTarget i target_label target target_events;
        FxNumberMachineNested update_events])
  end.

(** The step frame cost counts concrete label maps in addition to nested-machine frames. *)
Definition fx_number_machine_event_work {X C A} (event : fx_number_machine_event X C A) : nat :=
  match event with
  | FxNumberMachineNested events => fx_nested_work nat_encoding events
  | FxNumberMachineRhs _ _ _ events | FxNumberMachineTarget _ _ _ events =>
      1 + audit_map_source_work audit_nat_events_work events
  end.

(** Step work folds its captured nested and label events. *)
Definition fx_number_machine_work {X C A} (events : list (fx_number_machine_event X C A)) : nat :=
  fold_right (fun event n => fx_number_machine_event_work event + n) 0 events.

(** The independent step budget adds two label lookups exactly on ready states. *)
Definition fx_number_machine_step_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) (mode : strategy) (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (state : NestedState.t X nat A) : nat :=
  fx_nested_step_input_budget EX L plan mode (fx_number_system S fallback table) state +
  match NestedState.ready state with
  | [] => 0
  | i :: _ => 2 * fx_observe_label_budget i
  end.

(** Non-numbered events use original encoder, continuation and lattice source relations. *)
Definition fx_number_passthrough_source {X C A B} (source : fx_declared_callback_source X C A B) :
    fx_declared_callback_source X nat A B :=
  FxDeclaredCallbackSource X nat A B (fx_source_encode_x source) (fun _ _ _ => False)
    (fun _ _ _ => False) (fx_source_priority source) (fx_source_widening_point source)
    (fun _ _ _ => False) (fx_source_continuation source) (fx_source_leb source)
    (fx_source_join source) (fx_source_widen source).

(** Unused numbered callback slots cost zero; real label calls are charged separately. *)
Definition fx_number_passthrough_budget {X C A B} (budget : fx_declared_callback_budget X C A B) :
    fx_declared_callback_budget X nat A B :=
  FxDeclaredCallbackBudget X nat A B (fx_body_weight budget) (fx_budget_encode_x budget)
    (fun _ => 0) (fun _ => 0) (fx_budget_priority budget) (fx_budget_widening_point budget)
    (fun _ => 0) (fx_budget_continuation budget) (fx_budget_leb budget)
    (fx_budget_join budget) (fx_budget_widen budget).

(** Captured numbered calls use the actual label and original callback body. *)
Definition fx_number_machine_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_number_machine_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxNumberMachineNested events => exists groups,
      Forall2 (fx_nested_machine_event_source (fx_number_passthrough_source source)) events
    groups /\
        bodies = concat groups
  | FxNumberMachineRhs _ label out _ => exists body,
      bodies = [body] /\ fx_source_rhs source label out body
  | FxNumberMachineTarget _ label out _ => exists body,
      bodies = [body] /\ fx_source_target source label out body
  end.

(** External budgets refer to the exact captured label or nested callback invocation. *)
Definition fx_number_machine_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_number_machine_event X C A) : nat :=
  match event with
  | FxNumberMachineNested events => fold_right
      (fun event n => fx_nested_machine_external_budget (fx_number_passthrough_budget budget)
    event + n)
      0 events
  | FxNumberMachineRhs _ label _ _ => fx_budget_rhs budget label
  | FxNumberMachineTarget _ label _ _ => fx_budget_target budget label
  end.

(** One numbered step captures both label maps and the original callback bodies at invocation. *)
Definition fx_number_machine_step_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X nat)
    (mode : strategy) (S : System.t X C A) (fallback : C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (state : NestedState.t X nat A),
    In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
    let table := observation_number 0 (System.constraints S) in
    let '(out, events) := fx_number_machine_step EX L plan mode S fallback table state in
    exists bodies, Forall2 (fx_number_machine_event_source source) events bodies /\
      out = nested_step EX L plan mode (observation_system S fallback) state /\
      fx_number_machine_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_number_machine_step_budget EX L plan mode S fallback table state +
        fold_right (fun e n => fx_number_machine_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveNumberMachineAdequacy`

Card: AUD-FX-OBS-EXEC

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberMachineAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveNumberMachine.

Theorem fx_number_machine_step_source :
  FixpointAuditObserveNumberMachine.fx_number_machine_step_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveNumberTargets

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberTargets.v`.

```rocq
(** * Numbered observation target index

    The numbered system first constructs its occurrence table and then indexes its targets.
    For example, duplicate constraints have separate numbered target-index entries.
    Builds on: FixpointAuditObserveNumberCallbacks and the counted map model. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointNested FixpointObserve
    FixpointAuditWorklist
  FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks FixpointAuditObserveExecute.
From Galois.Fixpoint Require Import FixpointAuditObserveNumber
    FixpointAuditObserveNumberCallbacks FixpointAuditObserveExpiry.
Import List.ListNotations.

Inductive fx_observe_number_target_event (X C : Type) : Type :=
  | FxNumberTable (events : list (audit_map_event nat C audit_nat_encoding_event))
  | FxNumberTarget (i : nat) (label : C) (out : X)
      (events : list (audit_map_event nat C audit_nat_encoding_event))
  | FxNumberIndex (events : list (audit_map_event X (list nat) (fx_encoder_entry X)))
  | FxNumberSeq (size : nat)
  | FxNumberCase.
Arguments FxNumberTable {X C} _.
Arguments FxNumberTarget {X C} _ _ _ _.
Arguments FxNumberIndex {X C} _.
Arguments FxNumberSeq {X C} _.
Arguments FxNumberCase {X C}.

(** The target fold preserves occurrence order and captures every label lookup. *)
Fixpoint fx_number_targets_fold {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) (table : Map.t nat C) (indices : list nat) :
    Map.t X (list nat) * list (fx_observe_number_target_event X C) :=
  match indices with
  | [] => (Map.empty, [FxNumberCase])
  | i :: rest =>
      let '(before, later) := fx_number_targets_fold EX S fallback table rest in
      let '(target, label, label_events) := fx_observe_numbered_target S fallback table i in
      let '(found, read) := audit_map_get (fx_index_encoder EX) target before in
      let old := match found with Some xs => xs | None => [] end in
      let '(after, write) := audit_map_set (fx_index_encoder EX) target (i :: old) before in
      (after, FxNumberCase :: later ++
        [FxNumberTarget i label target label_events; FxNumberIndex read; FxNumberIndex write])
  end.

(** Building the numbered target map captures its table and the source seq construction. *)
Definition fx_observe_numbered_targets {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) : Map.t X (list nat) * list (fx_observe_number_target_event X C) :=
  let cs := System.constraints S in
  let '(table, table_events) := fx_observe_number 0 cs in
  let indices := seq 0 (length cs) in
  let '(targets, events) := fx_number_targets_fold EX S fallback table indices in
  (targets, FxNumberTable table_events :: FxNumberSeq (length cs) :: events).

(** Nat-key maps charge concrete unary encoder bodies, not a unit-cost callback. *)
Definition fx_number_target_event_work {X C} (event : fx_observe_number_target_event X C) : nat :=
  match event with
  | FxNumberTable events => audit_map_source_work audit_nat_events_work events
  | FxNumberTarget _ _ _ events => 1 + audit_map_source_work audit_nat_events_work events
  | FxNumberIndex events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxNumberSeq n => 4 + 4 * n
  | FxNumberCase => 1
  end.

(** The fold sums actual table, label, index and sequence frames. *)
Definition fx_number_targets_work {X C} (events : list (fx_observe_number_target_event X C)) :
    nat :=
  fold_right (fun event n => fx_number_target_event_work event + n) 0 events.

(** Target-index frames use each actual label and encoded target key. *)
Fixpoint fx_number_targets_fold_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) (table : Map.t nat C) (indices : list nat) : nat :=
  match indices with
  | [] => 1
  | i :: rest =>
      let label := observation_label fallback table i in
      let target := System.target S label in
      12 + fx_observe_label_budget i + 21 * Pos.size_nat (encode EX target) +
        fx_number_targets_fold_budget EX S fallback table rest
  end.

(** The target-index bound depends on the input system and concrete numbered table. *)
Definition fx_observe_numbered_targets_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) : nat :=
  let cs := System.constraints S in
  let table := observation_number 0 cs in
  fx_observe_number_budget 0 cs + 4 + 4 * length cs +
    fx_number_targets_fold_budget EX S fallback table (seq 0 (length cs)).

(** Each original target call and each X encoder call has its own source body. *)
Definition fx_number_target_event_source {X C A B}
    (source : fx_declared_callback_source X C A B) (event : fx_observe_number_target_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxNumberTarget _ label out _ => exists body,
      bodies = [body] /\ fx_source_target source label out body
  | FxNumberIndex events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | _ => bodies = []
  end.

(** Per-invocation target and encoder budgets are summed from the captured trace. *)
Definition fx_number_target_external_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_observe_number_target_event X C) : nat :=
  match event with
  | FxNumberTarget _ label _ _ => fx_budget_target budget label
  | FxNumberIndex events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries events)
  | _ => 0
  end.

(** One numbered-index witness supplies its exact target map and all actual source bodies. *)
Definition fx_observe_numbered_targets_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (fallback : C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_numbered_targets EX S fallback in
    exists bodies, Forall2 (fx_number_target_event_source source) events bodies /\
      out = nested_targets EX (observation_system S fallback) /\
      fx_number_targets_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_numbered_targets_budget EX S fallback +
        fold_right (fun e n => fx_number_target_external_budget budget e + n) 0 events.

(** The system and target map share one captured occurrence table and sequence construction. *)
Definition fx_observe_numbered_system_targets {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) : (Map.t nat C * System.t X nat A * Map.t X (list nat)) *
      list (fx_observe_number_target_event X C) :=
  let cs := System.constraints S in
  let '(table, table_events) := fx_observe_number 0 cs in
  let indices := seq 0 (length cs) in
  let numbered := System.Make indices
    (fun i => System.target S (observation_label fallback table i))
    (fun i => System.rhs S (observation_label fallback table i)) in
  let '(targets, events) := fx_number_targets_fold EX S fallback table indices in
  ((table, numbered, targets), FxNumberTable table_events :: FxNumberSeq (length cs) :: events).

(** The shared system/table witness has the actual source results and callback-body bound. *)
Definition fx_observe_numbered_system_targets_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (fallback : C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_numbered_system_targets EX S fallback in
    let numbered := observation_system S fallback in
    exists bodies, Forall2 (fx_number_target_event_source source) events bodies /\
      out = (observation_number 0 (System.constraints S), numbered, nested_targets EX numbered) /\
      fx_number_targets_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_numbered_targets_budget EX S fallback +
        fold_right (fun e n => fx_number_target_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveNumberTargetsAdequacy`

Card: AUD-FX-OBS-COMPILE

Source destination: `theories/Fixpoint/FixpointAuditObserveNumberTargetsAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveNumberTargets.

Theorem fx_observe_numbered_targets_source :
  FixpointAuditObserveNumberTargets.fx_observe_numbered_targets_source_statement.
Theorem fx_observe_numbered_system_targets_source :
  FixpointAuditObserveNumberTargets.fx_observe_numbered_system_targets_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveOrder

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveOrder.v`.

```rocq
(** * Observation SCC order

    This model retains dependency construction, graph preparation and the actual SCC traversal.
    For example, the outer List.rev keeps its legacy quadratic source cost.
    Builds on: FixpointAuditScheduleWrapper and GraphAuditScc. *)
From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase GraphAuditDfs
  GraphAuditScc.
From Galois.Fixpoint Require Import FixpointSystem FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper.
Import List.ListNotations.

Inductive fx_observe_order_event (X C B : Type) : Type :=
  | FxObserveOrderGraph (events : list (fx_dep_event X C B))
  | FxObserveOrderPrepare (events : list (audit_prepare_source_event X (X * X)
      (fx_dep_event X C B)))
  | FxObserveOrderScc (events : list (audit_tarjan_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))))
  | FxObserveOrderReverse (length : nat).
Arguments FxObserveOrderGraph {X C B} _.
Arguments FxObserveOrderPrepare {X C B} _.
Arguments FxObserveOrderScc {X C B} _.
Arguments FxObserveOrderReverse {X C B} _.

(** The SCC phase assumes AUD-GR-SCC has replaced the two internal reversals. *)
Definition fx_observe_order {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
    list (list X) * list (fx_observe_order_event X C B) :=
  let '(graph, ix, graph_events) := fx_dep_graph_build EX S SS cb in
  let '(prepared, prep_events) := audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb ix) in
  let '(result, scc_events) :=
    audit_scc_source_counted prepared (fx_dep_dfs_cb cb) (Graph.nodes graph) in
  let classes := components result in
  (rev classes, [FxObserveOrderGraph graph_events; FxObserveOrderPrepare prep_events;
    FxObserveOrderScc scc_events; FxObserveOrderReverse (length classes)]).

(** The post-SCC refinement and outer legacy reverse contribute their source work. *)
Definition fx_observe_order_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_order_event X C B) : nat :=
  match event with
  | FxObserveOrderGraph events => fx_dep_events_work ib events
  | FxObserveOrderPrepare events => audit_prepare_source_work (fx_dep_event_work ib) events
  | FxObserveOrderScc events =>
      audit_scc_source_work (fx_dep_event_work ib) events
  | FxObserveOrderReverse n => audit_graph_reverse_work n
  end.

(** The order work folds exactly the events from one captured execution. *)
Definition fx_observe_order_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_order_event X C B)) : nat :=
  fold_right (fun event n => fx_observe_order_event_work ib event + n) 0 events.

(** The order budget uses the actual input graph and native SCC intermediate. *)
Definition fx_observe_order_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let graph := dependency_graph EX S SS in
  let prepared := prepare EX graph in
  let classes := components (scc prepared) in
  let count := audit_graph_prepare_full_event_bound graph +
    audit_tarjan_input_event_bound prepared (Graph.nodes graph) in
  fx_dep_build_budget EX S SS ib + audit_prepare_source_budget EX graph +
    audit_scc_source_budget EX graph prepared (Graph.nodes graph) +
    64 * (1 + count) * fx_rpo_callback_max EX S SS ib +
    audit_graph_reverse_work (length classes).

(** The order phase has the source result and a native-input budget. *)
Definition fx_observe_order_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(out, events) := fx_observe_order EX S SS cb in
    out = observation_order EX S SS /\
      fx_observe_order_work ib events <= fx_observe_order_budget EX S SS ib.

(** Every graph callback retains its original dependency-graph callback body. *)
Definition fx_observe_order_capture_source {X C B} (source : fx_index_external_source X C B)
    (capture : audit_graph_callback_capture X (X * X) (fx_dep_event X C B)) : Prop :=
  match capture with
  | AuditGraphTargetCapture _ _ _ _ _ body => fx_dep_body_source source body
  | AuditGraphEncodeCapture _ _ _ _ _ body => fx_dep_body_source source body
  end.

(** The source relation follows each actual graph, preparation and SCC callback. *)
Definition fx_observe_order_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_observe_order_event X C B) : Prop :=
  match event with
  | FxObserveOrderGraph events => fx_dep_body_source source events
  | FxObserveOrderPrepare events => Forall (fx_dep_prepare_source source) events
  | FxObserveOrderScc events =>
      Forall (fun event => Forall (fx_observe_order_capture_source source) (snd event)) events
  | FxObserveOrderReverse _ => True
  end.

(** The same captured order execution supplies callbacks, result and input-derived work bound. *)
Definition fx_observe_order_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb source ->
    let '(out, events) := fx_observe_order EX S SS cb in
    Forall (fx_observe_order_event_source source) events /\ out = observation_order EX S SS /\
      fx_observe_order_work ib events <= fx_observe_order_budget EX S SS ib.
```

### Future proofs in `FixpointAuditObserveOrderAdequacy`

Card: AUD-FX-OBS-CHECK

Source destination: `theories/Fixpoint/FixpointAuditObserveOrderAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveOrder.

Theorem fx_observe_order_correct :
  FixpointAuditObserveOrder.fx_observe_order_statement.
Theorem fx_observe_order_source :
  FixpointAuditObserveOrder.fx_observe_order_source_statement.
```

## Galois.Fixpoint.FixpointAuditObservePlanCheck

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObservePlanCheck.v`.

```rocq
(** * Observation plan checking

    The checker evaluates all four boolean operands, including after an earlier rejection.
    For example, an invalid root does not suppress component or expiration validation.
    Builds on: the observation preparation, component and expiration comparison models. *)
From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObservePrepare FixpointAuditObserveComponents
    FixpointAuditObserveExpiry
  FixpointAuditObserveExpireCheck.
Import List.ListNotations.

Inductive fx_observe_check_event (X C B : Type) : Type :=
  | FxCheckPrepare (events : list (fx_observe_prepare_event X C B))
  | FxCheckComponents (events : list (fx_observe_component_event X C B))
  | FxCheckExpiry (events : list (fx_observe_expiry_event X C))
  | FxCheckCompare (events : list (fx_expire_check_event X))
  | FxCheckCase.
Arguments FxCheckPrepare {X C B} _.
Arguments FxCheckComponents {X C B} _.
Arguments FxCheckExpiry {X C B} _.
Arguments FxCheckCompare {X C B} _.
Arguments FxCheckCase {X C B}.

(** Every boolean operand and the actual expiration reconstruction runs on every input. *)
Definition fx_observe_plan_check {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (cb : fx_index_external_model X C B)
    (roots : list X) (p : observation_plan X) : bool * list (fx_observe_check_event X C B) :=
  let '(side, side_events) := fx_observe_side_free cb (System.constraints S) in
  let '(root, root_events) := fx_observe_roots_check S cb roots in
  let order := observation_components p in
  let '(components, component_events) := fx_observe_components EX S SS cb order in
  let '(input, dep_events) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, unknown_events) := fxi_distinct_counted cb input in
  let '(expiration, expiry_events) := fx_observe_expiry_fold EX S ix order unknown in
  let '(expires, compare_events) := fx_expire_check EX (observation_expire p) expiration in
  (side && root && components && expires,
    [FxCheckPrepare side_events; FxCheckPrepare root_events; FxCheckComponents component_events;
     FxCheckPrepare [FxPrepareDependency dep_events; FxPrepareIndex unknown_events];
     FxCheckExpiry expiry_events; FxCheckCompare compare_events; FxCheckCase]).

(** The frame budget charges both strict checks and independently rebuilt expirations. *)
Definition fx_observe_plan_check_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B)
    (roots : list X) (p : observation_plan X) : nat :=
  let order := observation_components p in
  let expiration := observation_expirations EX S SS ix order in
  1 + fx_observe_prepare_budget EX S SS ix ib roots + fx_observe_components_budget EX S SS ib
    order +
    fx_dep_build_budget EX S SS ib +
    fx_observe_expiry_fold_budget EX S ix order (unknowns EX S SS) +
    fx_expire_check_budget EX (observation_expire p) expiration.

(** Each event charges its own source frames and captured index callback bodies. *)
Definition fx_observe_check_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_check_event X C B) : nat :=
  match event with
  | FxCheckPrepare events => fx_observe_prepare_work ib events
  | FxCheckComponents events => fx_observe_components_work ib events
  | FxCheckExpiry events => fx_observe_expiry_work events
  | FxCheckCompare events => fx_expire_check_work events
  | FxCheckCase => 1
  end.

(** The work fold uses exactly the captured checker events. *)
Definition fx_observe_check_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_check_event X C B)) : nat :=
  fold_right (fun event n => fx_observe_check_event_work ib event + n) 0 events.

(** Every nested event retains its own source bodies; no callback is replayed for receipts. *)
Definition fx_observe_check_event_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_check_event X C B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxCheckPrepare events => exists groups,
      Forall2 (fx_observe_prepare_event_source index_source source) events groups /\
        bodies = concat groups
  | FxCheckComponents events => exists groups,
      Forall2 (fx_observe_component_event_source index_source source) events groups /\
        bodies = concat groups
  | FxCheckExpiry events => exists groups,
      Forall2 (fx_observe_expiry_event_source source) events groups /\ bodies = concat groups
  | FxCheckCompare events => exists groups,
      Forall2 (fx_expire_check_event_source source) events groups /\ bodies = concat groups
  | FxCheckCase => bodies = []
  end.

(** Each actual expiry and comparison callback contributes its own external budget. *)
Definition fx_observe_check_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_check_event X C B) : nat :=
  match event with
  | FxCheckPrepare events =>
      fold_right (fun e n => fx_observe_prepare_external_budget budget e + n) 0 events
  | FxCheckComponents events =>
      fold_right (fun e n => fx_observe_component_external_budget budget e + n) 0 events
  | FxCheckExpiry events =>
      fold_right (fun e n => fx_observe_expiry_external_budget budget e + n) 0 events
  | FxCheckCompare events =>
      fold_right (fun e n => fx_expire_check_external_budget budget e + n) 0 events
  | FxCheckCase => 0
  end.

(** A single checker witness provides source bodies, exact result and its input-derived bound. *)
Definition fx_observe_plan_check_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_plan_check EX S SS ix cb roots p in
    exists bodies, Forall2 (fx_observe_check_event_source index_source source) events bodies /\
      out = observation_plan_check EX S SS ix roots p /\
      fx_observe_check_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_plan_check_budget EX S SS ix ib roots p +
        fold_right (fun e n => fx_observe_check_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObservePlanCheckAdequacy`

Card: AUD-FX-OBS-CHECK

Source destination: `theories/Fixpoint/FixpointAuditObservePlanCheckAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObservePlanCheck.

Theorem fx_observe_plan_check_source :
  FixpointAuditObservePlanCheck.fx_observe_plan_check_source_statement.
```

## Galois.Fixpoint.FixpointAuditObservePrepare

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObservePrepare.v`.

```rocq
(** * Observation preparation

    Preparation checks side targets and roots before constructing an SCC order and lifetimes.
    For example, both checks run even when the side-target check returns false.
    Builds on: FixpointAuditObserveOrder and FixpointAuditObserveExpiry. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks.
From Galois.Fixpoint Require Import FixpointAuditObserveOrder FixpointAuditObserveExpiry.
Import List.ListNotations.

Inductive fx_observe_prepare_event (X C B : Type) : Type :=
  | FxPrepareDependency (events : list (fx_dep_event X C B))
  | FxPrepareIndex (events : list (fx_index_nested_event X C B))
  | FxPrepareSet (events : list (audit_set_event X B))
  | FxPrepareOrder (events : list (fx_observe_order_event X C B))
  | FxPrepareExpiry (events : list (fx_observe_expiry_event X C))
  | FxPrepareCase.
Arguments FxPrepareDependency {X C B} _.
Arguments FxPrepareIndex {X C B} _.
Arguments FxPrepareSet {X C B} _.
Arguments FxPrepareOrder {X C B} _.
Arguments FxPrepareExpiry {X C B} _.
Arguments FxPrepareCase {X C B}.

(** Side-target checking traverses every listed constraint. *)
Fixpoint fx_observe_side_free {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    bool * list (fx_observe_prepare_event X C B) :=
  match cs with
  | [] => (true, [FxPrepareCase])
  | c :: rest =>
      let '(sides, body) := fxi_sides cb c in
      let '(later, events) := fx_observe_side_free cb rest in
      ((match sides with [] => true | _ => false end) && later,
        FxPrepareCase :: FxPrepareIndex [FxiSides c sides body] :: events)
  end.

(** Root checking tests every root, preserving duplicates and all boolean tails. *)
Fixpoint fx_observe_roots_mem {X C B} (cb : fx_index_external_model X C B)
    (universe : FinSet.t X) (roots : list X) : bool * list (fx_observe_prepare_event X C B) :=
  match roots with
  | [] => (true, [FxPrepareCase])
  | x :: rest =>
      let '(present, mem) := audit_finset_mem (fxi_encode cb) x universe in
      let '(later, events) := fx_observe_roots_mem cb universe rest in
      (present && later, FxPrepareCase :: FxPrepareSet mem :: events)
  end.

(** Root preparation captures unknowns and the rebuilt universe before the root scan. *)
Definition fx_observe_roots_check {X C A B} (S : System.t X C A)
    (cb : fx_index_external_model X C B) (roots : list X) :
    bool * list (fx_observe_prepare_event X C B) :=
  let '(input, calls) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, distinct) := fxi_distinct_counted cb input in
  let '(universe, set) := audit_finset_of_list (fxi_encode cb) unknown in
  let '(result, members) := fx_observe_roots_mem cb universe roots in
  (result, [FxPrepareDependency calls; FxPrepareIndex distinct; FxPrepareSet set] ++ members).

(** One counted preparation retains the actual selected branch and its phase receipts. *)
Definition fx_observe_prepare {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (cb : fx_index_external_model X C B)
    (roots : list X) : option (observation_plan X) * list (fx_observe_prepare_event X C B) :=
  let '(side, side_events) := fx_observe_side_free cb (System.constraints S) in
  let '(root, root_events) := fx_observe_roots_check S cb roots in
  if side && root then
    let '(order, order_events) := fx_observe_order EX S SS cb in
    let '(input, input_events) := fx_dep_unknowns_input cb (System.constraints S) in
    let '(unknown, distinct_events) := fxi_distinct_counted cb input in
    let '(expiration, expiry_events) := fx_observe_expiry_fold EX S ix order unknown in
    (Some (ObservationPlan order expiration),
      side_events ++ root_events ++ [FxPrepareOrder order_events;
        FxPrepareDependency input_events; FxPrepareIndex distinct_events;
        FxPrepareExpiry expiry_events])
  else (None, side_events ++ root_events ++ [FxPrepareCase]).

(** The side and root costs use actual input keys and callback-specific budgets. *)
Fixpoint fx_observe_roots_mem_budget {X C B} (EX : encoding X)
    (ib : fx_index_external_budget X C B) (roots : list X) : nat :=
  match roots with
  | [] => 1
  | x :: rest => 8 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
      fx_observe_roots_mem_budget EX ib rest
  end.

(** The full frame budget follows the real preparation acceptance branch. *)
Definition fx_observe_prepare_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B)
    (roots : list X) : nat :=
  let cs := System.constraints S in
  let input := fx_dep_unknowns_native S SS in
  let unknown := unknowns EX S SS in
  32 * (1 + length cs + length input) + fx_dep_callback_budget ib cs +
    fx_dep_build_budget EX S SS ib + fxi_distinct_input_budget EX ib input +
    fxi_set_input_budget EX ib unknown + fx_observe_roots_mem_budget EX ib roots +
    if observation_side_free S SS && observation_roots_check EX S SS roots then
      let order := observation_order EX S SS in
      fx_observe_order_budget EX S SS ib + fx_dep_build_budget EX S SS ib +
        fx_observe_expiry_fold_budget EX S ix order unknown
    else 1.

(** The preparation frame work includes each captured child phase and collection traversal. *)
Definition fx_observe_prepare_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_prepare_event X C B) : nat :=
  match event with
  | FxPrepareDependency events => fx_dep_events_work ib events
  | FxPrepareIndex events => fx_index_adapter_work ib events
  | FxPrepareSet events => audit_finset_source_work (fxi_body_work ib) events
  | FxPrepareOrder events => fx_observe_order_work ib events
  | FxPrepareExpiry events => fx_observe_expiry_work events
  | FxPrepareCase => 1
  end.

(** The source work folds exactly the events returned by one preparation. *)
Definition fx_observe_prepare_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_prepare_event X C B)) : nat :=
  fold_right (fun e n => fx_observe_prepare_event_work ib e + n) 0 events.

(** A preparation event preserves index callback bodies and selected expiry bodies. *)
Definition fx_observe_prepare_event_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_prepare_event X C B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxPrepareDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FxPrepareIndex events => fx_index_external_trace_adequacy index_source events /\ bodies = []
  | FxPrepareSet events => fxi_set_external_adequacy index_source events /\ bodies = []
  | FxPrepareOrder events => Forall (fx_observe_order_event_source index_source) events /\
    bodies = []
  | FxPrepareExpiry events => exists groups,
      Forall2 (fx_observe_expiry_event_source source) events groups /\ bodies = concat groups
  | FxPrepareCase => bodies = []
  end.

(** External expiry bodies are charged only at actual selected callback invocations. *)
Definition fx_observe_prepare_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_prepare_event X C B) : nat :=
  match event with
  | FxPrepareExpiry events =>
      fold_right (fun e n => fx_observe_expiry_external_budget budget e + n) 0 events
  | _ => 0
  end.

(** One captured preparation supplies its source receipts, result and independent frame bound. *)
Definition fx_observe_prepare_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_prepare EX S SS ix cb roots in
    exists bodies, Forall2 (fx_observe_prepare_event_source index_source source) events bodies /\
      out = observation_prepare EX S SS ix roots /\
      fx_observe_prepare_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_prepare_budget EX S SS ix ib roots +
        fold_right (fun e n => fx_observe_prepare_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObservePrepareAdequacy`

Card: AUD-FX-OBS-CHECK

Source destination: `theories/Fixpoint/FixpointAuditObservePrepareAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObservePrepare.

Theorem fx_observe_prepare_source :
  FixpointAuditObservePrepare.fx_observe_prepare_source_statement.
```

## Galois.Fixpoint.FixpointAuditObserveWhole

Card: AUD-FX-MODELS

Source destination: `theories/Fixpoint/FixpointAuditObserveWhole.v`.

```rocq
(** * Whole observation runners

    A single captured plan check feeds numbered compilation and the selected execution.
    For example, rejection and an empty system return before any numbered callback runs.
    Builds on: the observer checker, numbered compiler and numbered execution models. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditNestedCallbacks FixpointAuditObserveExecute.
From Galois.Fixpoint Require Import FixpointAuditObservePlanCheck FixpointAuditObserveNumberTargets
  FixpointAuditObserveNumberMachine FixpointAuditObserveNumberExecute FixpointAuditObserveCompile
  FixpointAuditObserveExpiry.
Import List.ListNotations.

Inductive fx_observe_whole_event (X C A B : Type) : Type :=
  | FxObserveWholeCheck (events : list (fx_observe_check_event X C B))
  | FxObserveWholeNumber (events : list (fx_observe_number_target_event X C))
  | FxObserveWholeCompile (events : list (fx_observe_compile_event X C nat B))
  | FxObserveWholeExecute (events : list (fx_number_execute_event X C A))
  | FxObserveWholeProject (events : list (fx_observe_event X nat A))
  | FxObserveWholeCase.
Arguments FxObserveWholeCheck {X C A B} _.
Arguments FxObserveWholeNumber {X C A B} _.
Arguments FxObserveWholeCompile {X C A B} _.
Arguments FxObserveWholeExecute {X C A B} _.
Arguments FxObserveWholeProject {X C A B} _.
Arguments FxObserveWholeCase {X C A B}.

(** The shared core preserves rejection, empty-system and both execution-map branches. *)
Definition fx_observe_whole_core {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X)
    (fuel : positive) (evict : bool) : option (assignment X A) * list (fx_observe_whole_event X
    C A B) :=
  let '(accepted, check_events) := fx_observe_plan_check EX S SS ix cb roots p in
  if accepted then
    match System.constraints S with
    | [] => (Some Map.empty, [FxObserveWholeCheck check_events; FxObserveWholeCase])
    | fallback :: _ =>
        let '((table, _, targets), number_events) := fx_observe_numbered_system_targets EX S
    fallback in
        let '(schedule, compile_events) := fx_observe_compile_targets EX S SS cb targets roots p in
        let '(result, execute_events) := fx_number_execute EX L mode S fallback table schedule
    evict fuel in
        (option_map (if evict then @snd (assignment X A) (assignment X A)
                     else @fst (assignment X A) (assignment X A)) result,
          [FxObserveWholeCheck check_events; FxObserveWholeNumber number_events;
           FxObserveWholeCompile compile_events; FxObserveWholeExecute execute_events;
    FxObserveWholeCase])
    end
  else (None, [FxObserveWholeCheck check_events; FxObserveWholeCase]).

(** The full reference uses non-evicting execution and returns the full assignment. *)
Definition fx_observe_full_reference {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X) (fuel :
    positive) :=
  fx_observe_whole_core EX L mode S SS ix cb roots p fuel false.

(** The optimized runner uses eviction and returns the separately retained output map. *)
Definition fx_observe_run {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X) (fuel :
    positive) :=
  fx_observe_whole_core EX L mode S SS ix cb roots p fuel true.

(** Reference projection is a separate traversal only when the full reference succeeds. *)
Definition fx_observe_reference {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X) (fuel :
    positive) :
    option (assignment X A) * list (fx_observe_whole_event X C A B) :=
  let '(full, events) := fx_observe_full_reference EX L mode S SS ix cb roots p fuel in
  match full with
  | None => (None, events ++ [FxObserveWholeCase])
  | Some values =>
      let '(out, project_events) := @fx_observe_record X nat A EX L roots values Map.empty in
      (Some out, events ++ [FxObserveWholeProject project_events; FxObserveWholeCase])
  end.

(** Work uses the actual captured checker, numbered closures, compiler and machine. *)
Definition fx_observe_whole_event_work {X C A B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_whole_event X C A B) : nat :=
  match event with
  | FxObserveWholeCheck events => fx_observe_check_work ib events
  | FxObserveWholeNumber events => fx_number_targets_work events
  | FxObserveWholeCompile events => fx_observe_compile_work ib events
  | FxObserveWholeExecute events => fx_number_execute_work events
  | FxObserveWholeProject events => fx_observe_work nat_encoding events
  | FxObserveWholeCase => 1
  end.

(** The full source-frame work is a fold over one captured runner execution. *)
Definition fx_observe_whole_work {X C A B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_whole_event X C A B)) : nat :=
  fold_right (fun event n => fx_observe_whole_event_work ib event + n) 0 events.

(** The input bound selects exactly the actual rejection, empty or execution branch. *)
Definition fx_observe_whole_core_budget {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (ib : fx_index_external_budget X C B) (roots : list X) (p : observation_plan X)
    (fuel : positive) (evict : bool) : nat :=
  fx_observe_plan_check_budget EX S SS ix ib roots p + 1 +
  if observation_plan_check EX S SS ix roots p then
    match System.constraints S with
    | [] => 0
    | fallback :: _ =>
        let table := observation_number 0 (System.constraints S) in
        let schedule := observation_compile EX S SS fallback roots p in
        fx_observe_numbered_targets_budget EX S fallback +
          fx_observe_compile_targets_budget EX S SS ib roots p +
          fx_number_execute_budget EX L mode S fallback table schedule evict fuel
    end
  else 0.

(** Reference projection is charged only for an actual successful full-reference result. *)
Definition fx_observe_reference_budget {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (ib : fx_index_external_budget X C B) (roots : list X) (p : observation_plan X)
    (fuel : positive) : nat :=
  1 + fx_observe_whole_core_budget EX L mode S SS ix ib roots p fuel false +
  match observation_full_reference EX L mode S SS ix roots p fuel with
  | None => 0
  | Some _ => fx_observe_record_input_budget EX roots
  end.

(** Each nested phase retains the source bodies of the actual callbacks it invoked. *)
Definition fx_observe_whole_event_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_whole_event X C A B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxObserveWholeCheck events => exists groups,
      Forall2 (fx_observe_check_event_source index_source source) events groups /\ bodies =
    concat groups
  | FxObserveWholeNumber events => exists groups,
      Forall2 (fx_number_target_event_source source) events groups /\ bodies = concat groups
  | FxObserveWholeCompile events => exists groups,
      Forall2 (fx_observe_compile_event_source index_source (fx_number_passthrough_source source))
        events groups /\ bodies = concat groups
  | FxObserveWholeExecute events => exists groups,
      Forall2 (fx_number_execute_event_source source) events groups /\ bodies = concat groups
  | FxObserveWholeProject events => exists groups,
      Forall2 (fx_observe_event_source (fx_number_passthrough_source source)) events groups /\
    bodies = concat groups
  | FxObserveWholeCase => bodies = []
  end.

(** Each actual callback body is charged against its corresponding per-call input budget. *)
Definition fx_observe_whole_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_whole_event X C A B) : nat :=
  match event with
  | FxObserveWholeCheck events =>
      fold_right (fun e n => fx_observe_check_external_budget budget e + n) 0 events
  | FxObserveWholeNumber events =>
      fold_right (fun e n => fx_number_target_external_budget budget e + n) 0 events
  | FxObserveWholeCompile events => fold_right
      (fun e n => fx_observe_compile_external_budget (fx_number_passthrough_budget budget) e +
    n) 0 events
  | FxObserveWholeExecute events =>
      fold_right (fun e n => fx_number_execute_external_budget budget e + n) 0 events
  | FxObserveWholeProject events =>
      fold_right (fun e n => fx_observe_event_external_budget (fx_number_passthrough_budget
    budget) e + n) 0 events
  | FxObserveWholeCase => 0
  end.

(** The full-reference witness gives the exact option and the whole source-work allowance. *)
Definition fx_observe_full_reference_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X)
    (fuel : positive),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_observe_full_reference EX L mode S SS ix cb roots p fuel in
    exists bodies, Forall2 (fx_observe_whole_event_source index_source source) events bodies /\
      out = observation_full_reference EX L mode S SS ix roots p fuel /\
      fx_observe_whole_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_whole_core_budget EX L mode S SS ix ib roots p fuel false +
        fold_right (fun e n => fx_observe_whole_external_budget budget e + n) 0 events.

(** The evicting-run witness gives its exact option and whole source-work allowance. *)
Definition fx_observe_run_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X)
    (fuel : positive),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_observe_run EX L mode S SS ix cb roots p fuel in
    exists bodies, Forall2 (fx_observe_whole_event_source index_source source) events bodies /\
      out = observation_run EX L mode S SS ix roots p fuel /\
      fx_observe_whole_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_whole_core_budget EX L mode S SS ix ib roots p fuel true +
        fold_right (fun e n => fx_observe_whole_external_budget budget e + n) 0 events.

(** The reference witness includes its separate root projection and exact failure branch. *)
Definition fx_observe_reference_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X)
    (fuel : positive),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_observe_reference EX L mode S SS ix cb roots p fuel in
    exists bodies, Forall2 (fx_observe_whole_event_source index_source source) events bodies /\
      out = observation_reference EX L mode S SS ix roots p fuel /\
      fx_observe_whole_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_reference_budget EX L mode S SS ix ib roots p fuel +
        fold_right (fun e n => fx_observe_whole_external_budget budget e + n) 0 events.
```

### Future proofs in `FixpointAuditObserveWholeAdequacy`

Card: AUD-FX-OBS-WHOLE

Source destination: `theories/Fixpoint/FixpointAuditObserveWholeAdequacy.v`.

```rocq
From Galois.Fixpoint Require Import FixpointAuditObserveWhole.

Theorem fx_observe_full_reference_source :
  FixpointAuditObserveWhole.fx_observe_full_reference_source_statement.
Theorem fx_observe_run_source :
  FixpointAuditObserveWhole.fx_observe_run_source_statement.
Theorem fx_observe_reference_source :
  FixpointAuditObserveWhole.fx_observe_reference_source_statement.
```

<!-- AUD-API-OBS-END -->

<!-- AUD-API-BRIDGE-Fixpoint-BEGIN -->

## Galois.Fixpoint.FixpointAuditCost

Card: AUD-FX-COST

Source destination: `theories/Fixpoint/FixpointAuditCost.v`.

```rocq
(** * Solver source-family contracts

    These propositions combine the fixed solver phase source contracts.
    For example, the full family retains both reference and observed executions.
    Builds on: the Fixpoint phase and observer source models. *)

From Galois.Fixpoint Require Import
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditRecordedCallbacks FixpointAuditTotal FixpointAuditCheckCallbacks
  FixpointAuditPartialCallbacks FixpointAuditCutCallbacks FixpointAuditLocalCallbacks
  FixpointAuditNarrowCallbacks FixpointAuditNestedCallbacks FixpointAuditCache
  FixpointAuditFallbackCallbacks FixpointAuditObserveExecute FixpointAuditObservePrepare
  FixpointAuditObservePlanCheck FixpointAuditObserveCompile FixpointAuditObserveCompileWhole
  FixpointAuditObserveNumberExecute FixpointAuditObserveWhole.

(** The index and scheduler source obligations cover actual preparation. *)
Definition solver_preparation_cost_statement : Prop :=
  fx_index_external_source_statement /\ fx_rpo_scheduler_source_statement.

(** The dependency family includes the solver and rooted checker source obligations. *)
Definition solver_dependency_cost_statement : Prop :=
  fx_declared_external_source_statement /\ fx_recorded_external_source_statement /\
  fx_total_callbacks_source_statement /\ fx_fullcheck_rooted_source_statement /\
  fx_partial_rooted_source_statement /\ fx_cut_external_source_statement /\
  fx_local_external_source_statement /\ fx_narrow_external_source_statement /\
  fx_nested_external_source_statement.

(** The full family also covers cache, fallback and all observation entrypoints. *)
Definition solver_full_source_family_statement : Prop :=
  solver_preparation_cost_statement /\ solver_dependency_cost_statement /\
  cache_init_callbacks_source_statement /\ cache_query_callbacks_source_statement /\
  fx_recorded_fallback_external_source_statement /\
  fx_nested_fallback_external_source_statement /\ fx_fallback_apply_external_source_statement /\
  fx_observe_prepare_source_statement /\ fx_observe_plan_check_source_statement /\
  fx_observe_compile_targets_source_statement /\ fx_observe_compile_whole_source_statement /\
  fx_observe_execute_source_statement /\ fx_number_execute_source_statement /\
  fx_observe_full_reference_source_statement /\ fx_observe_reference_source_statement /\
  fx_observe_run_source_statement.
```

Future theorems in `FixpointAuditCost`:

```rocq
Theorem solver_preparation_cost : solver_preparation_cost_statement.
Theorem solver_dependency_cost : solver_dependency_cost_statement.
Theorem solver_full_source_family : solver_full_source_family_statement.
```


<!-- AUD-API-BRIDGE-Fixpoint-END -->
