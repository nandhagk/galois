# Galois.Rules

Rules is a Datalog-style front end for dataflow analyses. An analysis is written as inference
rules over facts, as in the 15-411 notes (Pfenning, Platzer and Simmons), and the package compiles
it into the constraint systems of Fixpoint, one static system per stratum, and solves it with the
same engine. Facts are ground atoms whose arguments are the numeric codes of the client's keys. For
example, `live(n,x) :- use(n,x).` and `live(n,x) :- succ(n,m), live(m,x), !def(n,x).` with the facts
`use(2,7)`, `succ(1,2)` and no `def` give `live(2,7)` and `live(1,7)`. The *model* of a program is
defined by derivability, it is stratum-wise least (each stratum is least over the model below), and
the theorem of this package is that the engine computes exactly it.

Conventions of this document. Names are those of the anchors; `finite_set`,
`finite_powerset_lattice`, `finite_powerset_height` and `finite_powerset_laws` come from Order,
`list_encoding` from Collections, and the engine from Fixpoint (`System.t`, `Query.Ret`, `ask_all`,
`solve_total`, `rpo_scheduler`, `reached`, `least_solution`). Sets are `FinSet.t K`, written with
the encoding first. The names of this package are bare: a client writes `program`, `holds`,
`least_model`, `TVar`, and qualifies by the shortest module prefix only when its own names clash.
There is no text parser: a rule is written as a value. Statements sit in `Section`s whose `Context`
and `Variables` declare what they mention. Every `Inductive` and `Record` takes its parameters
implicitly in constructors and projections (`Arguments` declarations are omitted).

## Files

| File | Contents | Card |
|---|---|---|
| `RulesSyntax.v` | `term`, `atom`, `literal`, `rule`, `program`, `ground_atom`, `inst`, `ground`, `program_wf` | RUL-1a |
| `RulesStratify.v` | `stratification`, `stratified`, `stratify` (check and complete) | RUL-1a |
| `RulesCompile.v` | `preds`, `constants`, `in_universe`, `herbrand` (proof-only), `relation`, `restrict`, `fire_rule`, `rconstraint`, `stratum_system`, `stratum_static`; `fire_rule_exact`, `stratum_system_monotone` | RUL-1a |
| `RulesModel.v` | `derives`, `model_below`, `perfect_model`, `least_model`, `holds`; `least_model_closed` | RUL-1b |
| `RulesSolve.v` | `solve_program`, `db_holds`, `represents`; stratum soundness and completeness, `solve_program_exact` | RUL-1b |
| `RulesJoin.v` | selectable indexed and multiway joins with exact firing agreement | RUL-2a |
| `RulesDelta.v` | semi-naive stratified solver and exact model agreement | RUL-2b |

Prerequisites. RUL-1a needs FIX-1 and ORD-2. RUL-1b needs RUL-1a and FIX-2b (it uses
`solve_total`, `solve_total_reached` and `solve_total_least`).
RUL-2a needs RUL-1b; RUL-2b needs RUL-2a. The original solver remains available as a
reference and for existing clients. The semi-naive solver is the primary production path.

## Definitions

### Syntax and well-formedness

Predicates are of any encodable type `P`; variables are numbers; constants are the `positive`
codes of the client's keys (`encode E k`), so a ground atom is a predicate and a list of codes.

```coq
Definition tuple : Type := list positive.
Inductive term : Type := TVar (v : nat) | TConst (c : positive).
Record atom (P : Type) : Type := Atom { pred : P; args : list term }.
Inductive literal (P : Type) : Type := LPos (a : atom P) | LNeg (a : atom P).
Record rule (P : Type) : Type := Rule { head : atom P; body : list (literal P) }.
Record program (P : Type) : Type := Program {
  penc : encoding P;                     (* how predicates are keyed *)
  arity : P -> nat;
  rules : list (rule P)
}.
Definition ground_atom (P : Type) : Type := (P * tuple)%type.     (* a fact: the extensional facts are a list of them *)
Definition inst (sigma : nat -> positive) (t : term) : positive :=
  match t with TVar v => sigma v | TConst c => c end.
Definition ground {P} (sigma : nat -> positive) (a : atom P) : ground_atom P :=
  (pred a, map (inst sigma) (args a)).
Definition lit_atom {P} (l : literal P) : atom P := match l with LPos a | LNeg a => a end.
Definition atom_vars {P} (a : atom P) : list nat :=
  flat_map (fun t => match t with TVar v => [v] | TConst _ => [] end) (args a).
(* range restriction: every variable of the head or of a negative literal occurs in a positive literal *)
Definition safe_rule {P} (r : rule P) : Prop :=
  forall v, (In v (atom_vars (head r)) \/ exists a, In (LNeg a) (body r) /\ In v (atom_vars a)) ->
    exists a, In (LPos a) (body r) /\ In v (atom_vars a).
Definition program_wf {P} (prog : program P) (facts : list (ground_atom P)) : Prop :=
  (forall r, In r (rules prog) -> safe_rule r /\
     length (args (head r)) = arity prog (pred (head r)) /\
     forall l, In l (body r) -> length (args (lit_atom l)) = arity prog (pred (lit_atom l))) /\
  forall f, In f facts -> length (snd f) = arity prog (fst f).
```

### Stratification (`RulesStratify.v`)

A stratification gives each predicate a level. Negation may only read a strictly lower level, so
extensional predicates (level 0, no rules) can be negated freely.

```coq
Record stratification (P : Type) : Type := Stratification { level : P -> nat; count : nat }.
Definition stratified {P} (prog : program P) (st : stratification P) : Prop :=
  (forall p, level st p < count st) /\
  forall r l, In r (rules prog) -> In l (body r) ->
    match l with
    | LPos a => level st (pred a) <= level st (pred (head r))
    | LNeg a => level st (pred a) < level st (pred (head r))
    end.
Definition stratify {P} (prog : program P) : option (stratification P).
(* n := the number of distinct predicates that occur in rules. Raise levels to a fixpoint: all 0; each
   round is one pass over the rules, with a Map from predicate code to level, raising the level of the
   head to the maximum of itself, the level of each positive body predicate and one more than the
   level of each negative one. Fuel n*n+1 rounds: None if a level reaches n, or if the fuel runs out;
   otherwise level 0 for predicates outside the rules and count one more than the largest level *)
```

### The model (`RulesModel.v`)

Derivability is an inductive definition, so the model is the least set closed under its rules. At
level `k` it is taken over a given model `lower` of the levels below; a positive literal of level
`k` is derived recursively, a lower one and a negative one are read from `lower`. The perfect model
is built stratum by stratum, each stratum least over the one below.

```coq
Inductive derives {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
    (k : nat) (lower : ground_atom P -> Prop) : ground_atom P -> Prop :=
  | derive_fact : forall f, In f facts -> level st (fst f) = k -> derives prog facts st k lower f
  | derive_rule : forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
      (forall a, In (LPos a) (body r) -> level st (pred a) < k -> lower (ground sigma a)) ->
      (forall a, In (LPos a) (body r) -> level st (pred a) = k ->
         derives prog facts st k lower (ground sigma a)) ->
      (forall a, In (LNeg a) (body r) -> ~ lower (ground sigma a)) ->
      derives prog facts st k lower (ground sigma (head r)).
(* the atoms of levels below n *)
Fixpoint model_below {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
    (n : nat) : ground_atom P -> Prop :=
  match n with
  | O => fun _ => False
  | S k => fun f => model_below prog facts st k f \/
                    derives prog facts st k (model_below prog facts st k) f
  end.
Definition perfect_model {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P) :
  ground_atom P -> Prop := model_below prog facts st (count st).
Definition least_model {P} (prog : program P) (facts : list (ground_atom P)) : ground_atom P -> Prop :=
  match stratify prog with Some st => perfect_model prog facts st | None => fun _ => False end.
Definition holds {P} (M : ground_atom P -> Prop) (p : P) (args : tuple) : Prop := M (p, args).
```

### Compilation to constraint systems (`RulesCompile.v`)

Negation makes the whole program non-monotone (`p :- !q.` with no rule for `q` has no least
post-solution), so each level compiles to its own static system in which every lower level is a
constant relation, and the levels are solved in order. Values are finite sets of tuples inside the
Herbrand universe, which gives a finite height.

The universe is described, never enumerated. `preds` and `constants` are finite sets computed in one
pass over the rules and facts (the predicates that occur, and every `TConst` and every component of
a fact). A tuple is inside the universe of a predicate when `in_universe` says so, a test that costs
its length. `herbrand` lists all such tuples and exists only as the `U` argument of Order's
finite-set lattice, in types and proofs: it is never evaluated. The `extraction/` directory (not
`theories/`) declares `Extraction Implicit` for the `U` argument of `finite_powerset_lattice` and
`finite_powerset_top`, and TOOL-2 checks that the extracted `solve_program` never mentions
`herbrand`.

```coq
Definition tuple_encoding : encoding tuple := list_encoding positive_encoding.
Definition preds {P} (prog : program P) (facts : list (ground_atom P)) : FinSet.t P.
(* FinSet.of_list (penc prog) of the head and body predicates of the rules and the predicates of the facts *)
Definition constants {P} (prog : program P) (facts : list (ground_atom P)) : FinSet.t positive.
(* FinSet.of_list positive_encoding of every TConst of the rules and every component of every fact *)
Definition in_universe {P} (prog : program P) (facts : list (ground_atom P)) (p : P) (ts : tuple) : bool :=
  FinSet.mem (penc prog) p (preds prog facts) && Nat.eqb (length ts) (arity prog p) &&
  forallb (fun c => FinSet.mem positive_encoding c (constants prog facts)) ts.
Definition herbrand {P} (prog : program P) (facts : list (ground_atom P)) : list tuple.
(* PROOF-ONLY: the distinct tuples over the constants whose length is the arity of a predicate that
   occurs, with herbrand_spec and herbrand_nodup below; never evaluated *)
Definition relation {P} (prog : program P) (facts : list (ground_atom P)) : Type :=
  finite_set tuple_encoding (herbrand prog facts).
Definition relation_lattice {P} (prog : program P) (facts : list (ground_atom P)) : lattice (relation prog facts) :=
  finite_powerset_lattice tuple_encoding (herbrand prog facts).
(* the tuples of s that are inside the universe of p, normalised through FinSet.of_list; membership in
   herbrand is proved from in_universe by herbrand_spec. This is the identity on the filtered
   output of fire_rule at the head predicate (restrict_spec). *)
Definition restrict {P} (prog : program P) (facts : list (ground_atom P)) (p : P) (s : FinSet.t tuple) :
  relation prog facts.
(* every tuple of env p has the arity of p, and env p is well formed *)
Definition env_wf {P} (prog : program P) (env : P -> FinSet.t tuple) : Prop :=
  forall p, FinSet.wf tuple_encoding (env p) /\
    forall ts, FinSet.mem tuple_encoding ts (env p) = true -> length ts = arity prog p.
(* head tuples of valuations satisfying the body, filtered to the head predicate's universe *)
Definition fire_rule {P} (prog : program P) (facts : list (ground_atom P)) (r : rule P)
  (env : P -> FinSet.t tuple) : FinSet.t tuple.
(* an index nested-loop join of the positive literals in order, each probed through a Table on its
   already-bound argument positions, built once per firing from the relation with FinSet.elements; a
   tuple whose length differs from the literal's matches nothing; a negative literal is a membership
   test; filter each head tuple with in_universe prog facts (pred (head r)), then build the result
   with FinSet.of_list, so it is well formed *)
Inductive rconstraint (P : Type) : Type := FromRule (i : nat) (h : P) | FromFact (p : P).
Definition rconstraint_encoding {P} (EP : encoding P) : encoding (rconstraint P).
Definition stratum_system {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
  (lower : P -> FinSet.t tuple) (k : nat) : System.t P (rconstraint P) (relation prog facts).
(* constraints: FromRule i (pred (head r_i)) for each rule r_i whose head has level k (i its position
   in rules prog), and FromFact p for each distinct predicate p of level k that has facts.
   target (FromRule _ h) = h and target (FromFact p) = p.
   rhs (FromRule i h) = ask_all the distinct level-k predicates of the positive literals of r_i
     (fun rels => Query.Ret (restrict prog facts h (fire_rule prog facts r_i env))), where env p is the
     asked relation (its underlying set) if level p = k, and lower p otherwise; an index i out of
     range gives Query.Ret of the empty relation;
   rhs (FromFact p) = Query.Ret (restrict prog facts p (the set of the facts of p)) *)
Definition stratum_static {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
  (lower : P -> FinSet.t tuple) (k : nat) : System.static (stratum_system prog facts st lower k).
(* deps (FromRule i _) = those level-k predicates; deps (FromFact _) = []; side_targets _ = [];
   reads_within and sides_within hold by ask_all_spec: the evidence is built with the system *)
```

### Solving (`RulesSolve.v`)

```coq
Definition database (P : Type) : Type := Map.t P (FinSet.t tuple).
Definition rel_of {P} (prog : program P) (db : database P) (p : P) : FinSet.t tuple :=
  match Map.get (penc prog) p db with Some s => s | None => FinSet.empty end.
Definition db_holds {P} (prog : program P) (db : database P) (p : P) (ts : tuple) : bool :=
  FinSet.mem tuple_encoding ts (rel_of prog db p).
Definition solve_program {P} (prog : program P) (facts : list (ground_atom P)) : option (database P).
(* stratify prog; for k = 0 .. count - 1: solve_total (penc prog) (rconstraint_encoding (penc prog))
   over stratum_system with lower = rel_of of the database so far, strategy Joining, scheduler
   rpo_scheduler, evidence inhabits (base_height (finite_powerset_height tuple_encoding
   (herbrand prog facts) herbrand_nodup)), a proof-only term that extraction erases. For the solver
   result s, add proj1_sig ((proj1_sig s) p) for each distinct target p of the stratum; None if not
   stratifiable *)
(* db represents a model M: every relation is well formed and holds exactly the atoms of M *)
Definition represents {P} (db : P -> FinSet.t tuple) (M : ground_atom P -> Prop) : Prop :=
  (forall p, FinSet.wf tuple_encoding (db p)) /\
  forall p ts, FinSet.mem tuple_encoding ts (db p) = true <-> M (p, ts).
```

### Selectable joins and semi-naive solving

```coq
Inductive join_strategy : Type := IndexedNested | IndexedMultiway.

Definition fire_rule_join {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
    FinSet.t tuple.

Definition solve_program_delta {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) : option (database P).

Theorem fire_rule_join_exact {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
  program_wf prog facts -> In r (rules prog) -> env_wf prog env ->
  forall ts, FinSet.mem tuple_encoding ts (fire_rule_join strategy prog facts r env) = true <->
    FinSet.mem tuple_encoding ts (fire_rule prog facts r env) = true.

Theorem fire_rule_join_wf {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  FinSet.wf tuple_encoding (fire_rule_join strategy prog facts r env).

Theorem solve_program_delta_exact {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) :
  program_wf prog facts -> (exists st, stratified prog st) ->
  exists db, solve_program_delta strategy prog facts = Some db /\
    represents (rel_of prog db) (least_model prog facts).

Theorem solve_program_delta_none {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) :
  (forall st, ~ stratified prog st) -> solve_program_delta strategy prog facts = None.

Theorem solve_program_delta_agrees {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (db delta : database P) :
  program_wf prog facts -> solve_program prog facts = Some db ->
  solve_program_delta strategy prog facts = Some delta ->
  forall p ts, db_holds prog db p ts = db_holds prog delta p ts.
```

`IndexedNested` probes indexes for bound arguments; `IndexedMultiway` intersects indexed
variable bindings. Prepare indexes once per input relation and maintain them when tuples are
added. Both respect constants, repeated variables and arity; lower-stratum negation is tested
only after that stratum is complete. Prove index lookup and join agreement independently of
the implementation. Card: RUL-2a.

For each stratum, retain accumulated and delta tuples. Fire recursive rule variants with at
least one current delta, deduplicate candidates against accumulated tuples, and advance until
all deltas are empty. Include facts and nonrecursive rules in initialization. Process strata in
order; never evaluate negation against an unfinished lower relation. Prove each produced tuple
derivable, every newly derivable tuple eventually produced, finite termination, and quiescent
closure, then derive exact model correspondence and pointwise agreement. Each tuple is inserted
once, but can participate in many joins; no linear running-time claim follows. Card: RUL-2b.

## Theorems

```coq
Section Rules.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : stratification P).
Variables (k : nat) (lower : P -> FinSet.t tuple) (env : P -> FinSet.t tuple) (r : rule P)
  (p : P) (ts : tuple) (s0 : FinSet.t tuple).

(** The proof-only universe is exactly the tuples inside it, without repetition. *)
Theorem herbrand_spec : In ts (herbrand prog facts) <-> exists p', FinSet.mem (penc prog) p' (preds prog facts) = true /\
  length ts = arity prog p' /\ forall c, In c ts -> FinSet.mem positive_encoding c (constants prog facts) = true.
Theorem herbrand_nodup : NoDup (herbrand prog facts).
(* Proof idea: the tuples of each arity over the elements of the constants set, deduplicated; FinSet.elements_spec and FinSet.elements_nodup. Card: RUL-1a. *)
(** `restrict` keeps exactly the members of a well-formed set that lie in the universe of the predicate. *)
Theorem restrict_spec : FinSet.wf tuple_encoding s0 ->
  FinSet.mem tuple_encoding ts (proj1_sig (restrict prog facts p s0)) = true <->
  FinSet.mem tuple_encoding ts s0 = true /\ in_universe prog facts p ts = true.
(* Proof idea: FinSet.of_list_spec and the membership of FinSet.elements. Card: RUL-1a. *)

(** `stratify` returns a stratification, and returns one whenever one exists. *)
Theorem stratify_sound : stratify prog = Some st -> stratified prog st.
Theorem stratify_complete : (exists st', stratified prog st') -> exists st'', stratify prog = Some st''.
(* Proof idea: soundness: the loop stops at a fixpoint of the raising rules. Completeness: if some level reaches n, the number of occurring predicates, a chain of raises through at least n negative edges visits a predicate twice, so a cycle through a negative literal exists and no stratification does; hence a stratifiable program keeps every level below n, each round that changes something raises the sum of the levels by at least one, the sum stays below n*n, and n*n+1 rounds reach a fixpoint. Card: RUL-1a. *)

(** A tuple is fired exactly when it lies in the universe and a valuation instantiates the head
    to it while satisfying the body on the relations. *)
Theorem fire_rule_exact : program_wf prog facts -> In r (rules prog) -> env_wf prog env -> forall ts',
  FinSet.mem tuple_encoding ts' (fire_rule prog facts r env) = true <->
  in_universe prog facts (pred (head r)) ts' = true /\
  exists sigma, ts' = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
       FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
    (forall a, In (LNeg a) (body r) ->
       FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false).
Theorem fire_rule_wf : (forall q, FinSet.wf tuple_encoding (env q)) ->
  FinSet.wf tuple_encoding (fire_rule prog facts r env).
(* Proof idea: induction on the positive literals in join order: the partial bindings are exactly
   those of the satisfied prefix; safety binds every head and negative variable; a variable outside
   the rule is free in sigma; the arity premise makes every stored tuple the instance of its own
   literal; the filter enforces in_universe and the result is FinSet.of_list. Card: RUL-1a. *)
(** The converse needs no environment arity: an in-universe head satisfying the body is fired. *)
Theorem fire_rule_complete : program_wf prog facts -> In r (rules prog) ->
  (forall q, FinSet.wf tuple_encoding (env q)) -> forall sigma,
  in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
  (forall a, In (LPos a) (body r) ->
     FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) ->
  (forall a, In (LNeg a) (body r) ->
     FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false) ->
  FinSet.mem tuple_encoding (map (inst sigma) (args (head r))) (fire_rule prog facts r env) = true.
(* Proof idea: as fire_rule_exact, one direction; a tuple of the wrong length is ignored by the
   index and never needed, and the in_universe premise passes the output filter. Card: RUL-1a. *)

(** Each level compiles to a monotone system: lower levels and negated predicates are constants. *)
Theorem stratum_system_monotone : program_wf prog facts -> env_wf prog lower -> stratified prog st ->
  monotone_system (relation_lattice prog facts) (stratum_system prog facts st lower k).
(* Proof idea: a positive level-k literal grows with its relation (monotone_query of ask_all and a join whose probes only gain matches); restrict is monotone (restrict_spec); every other literal reads the constant `lower`. Card: RUL-1a. *)

(** The model contains the facts and is closed under every rule: a satisfied body gives its head. *)
Theorem least_model_closed : stratify prog = Some st ->
  (forall f, In f facts -> least_model prog facts f) /\
  forall sigma, In r (rules prog) ->
    (forall a, In (LPos a) (body r) -> least_model prog facts (ground sigma a)) ->
    (forall a, In (LNeg a) (body r) -> ~ least_model prog facts (ground sigma a)) ->
    least_model prog facts (ground sigma (head r)).
(* Proof idea: an atom of level j is in model_below n exactly when it is derived at stage j, for every n above j, since a stage derives only atoms of its own level; then derive_fact and derive_rule. Card: RUL-1b. *)
(** Every atom of the model lies in the universe of its predicate: right arity, constants of the program. *)
Theorem model_constants : program_wf prog facts -> stratified prog st ->
  forall n a, model_below prog facts st n a -> in_universe prog facts (fst a) (snd a) = true.
(* Proof idea: induction on n and on the derivation: facts use their constants; a derived head has the arity of its predicate (program_wf) and each component is a rule constant or, by safety, a component of a positive body atom, which lies in the universe. Card: RUL-1b. *)

(** On a database that represents the levels below, every post-solution of the level's system contains what is derived there. *)
Theorem stratum_post_solution_contains : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, post_solution (relation_lattice prog facts) (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k -> derives prog facts st k (model_below prog facts st k) (p', ts') ->
  FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true.
(* Proof idea: induction on the derivation: a fact is its FromFact constraint. For a rule instance,
   model_constants supplies the in_universe premise of fire_rule_complete; positive level-k atoms
   are in the contained relations by the induction hypothesis, and lower atoms and the absence of
   negated ones follow from represents. restrict_spec keeps the result, and the post-solution
   inequality puts it in s. Card: RUL-1b. *)
(** What a run of the engine reaches from bottom is derived: member implies derived. *)
Theorem stratum_reached_derives : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, reached (penc prog) (relation_lattice prog facts) (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k -> FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true ->
  derives prog facts st k (model_below prog facts st k) (p', ts').
(* Proof idea: induction on reached: bottom has no members; a run adds only tuples of fire_rule_exact on the current relations, whose own members are derived by the induction hypothesis (and are arity-respecting, since restrict keeps in_universe), so each added tuple is a derive_rule or derive_fact instance. Card: RUL-1b. *)
(** A least solution of the level's system holds exactly what is derived there. *)
Theorem stratum_least_is_derives : program_wf prog facts -> stratified prog st -> (k < count st)%nat ->
  represents lower (model_below prog facts st k) ->
  forall s, least_solution (relation_lattice prog facts) (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k ->
    (FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true <->
     derives prog facts st k (model_below prog facts st k) (p', ts')).
(* Proof idea: derived implies member is stratum_post_solution_contains. Member implies derived: the engine's result s' is reached (solve_total_reached, with the evidence from finite_powerset_height) and a post-solution, hence least (reached_least, with finite_powerset_laws, finite_powerset_lub and stratum_system_monotone); least_solution_unique makes s and s' equivalent, so they have the same members, and stratum_reached_derives applies to s'. Card: RUL-1b. *)

(** The solver fails exactly on unstratifiable programs and otherwise computes the least model; since each level is solved to its least solution, the result of the engine with `Joining` is the model, stratum by stratum. *)
Theorem solve_program_exact : program_wf prog facts -> (exists st', stratified prog st') ->
  exists db, solve_program prog facts = Some db /\ represents (rel_of prog db) (least_model prog facts).
Theorem solve_program_none : (forall st', ~ stratified prog st') -> solve_program prog facts = None.
(* Proof idea: induction on the level k: the database before level k represents model_below k; solve_total_least (lub_laws and the height of the finite powerset, monotone by stratum_system_monotone) makes the level's values a least solution, which stratum_least_is_derives identifies with the derivations, so the database represents model_below (k + 1). The second is stratify_complete. Card: RUL-1b. *)
End Rules.
```

## Algorithms and references

- **Analyses as inference rules:** the 15-411 lecture notes of Pfenning, Platzer and Simmons give
  liveness, neededness (`N1` to `N3`) and reaching definitions as rules over `use`, `def`, `succ`
  and `nec`; ANA-11 writes them as `program` values. Datalog for program analysis: Whaley, Avots,
  Carbin and Lam (APLAS 2005); Soufflé (Jordan, Scholz and Subotic, CAV 2016).
- **Stratified negation and the perfect model:** Apt, Blair and Walker, "Towards a theory of
  declarative knowledge" (1988); Przymusinski (1988). `derives` is the textbook inductive
  definition of derivability, taken one level at a time over the model below.
- **Evaluation:** naive bottom-up evaluation through the Fixpoint engine, one level at a time.
  Semi-naive evaluation (Bancilhon and Ramakrishnan, 1986) would fire only on the new tuples and
  changes `fire_rule` and not the theorems.
- **Joins:** index nested loops over the positive literals in order, as in a Datalog interpreter.

## Performance notes

- Each positive literal is probed through an index on its already-bound argument positions: a
  `Table` keyed by the list of bound codes, built once per firing from the relation in
  O(size of the relation), then one probe per partial binding. No list of tuples is scanned inside
  the join; a negative literal is one `FinSet.mem`. The agreement lemma of these indexes (a probe
  returns exactly the tuples that match the bound positions) is internal to `fire_rule_exact`.
- The compiled system is static, so the engine reads dependencies from its prepared `sys_index`
  (`index_system_laws`). A rule fires again whenever a level-`k` relation in its body changes, so
  evaluation is naive: polynomial in the number of constants, quadratic in the worst case.
- `stratify` makes at most `n*n+1` rounds, each a pass over the rules with a `Map` from predicate
  code to level.
- `preds` and `constants` are built once per `solve_program` call, linear in the program and facts;
  `fire_rule` filters each firing's output with `in_universe`, linear in the output. `herbrand`
  appears only in types and proofs and is erased: the `U` argument of `finite_powerset_lattice` and
  `finite_powerset_top` is `Extraction Implicit`, and the evidence passed to `solve_total` is
  `inhabited`, which extraction erases.

## Open questions

1. **Interface assumed by ANA-11.** `program P`, `ground_atom P`, `least_model prog facts`,
   `holds` and arguments as lists of codes are as ANA-11 writes them. A program here also carries
   `penc` and `arity`, so ANA-11's `liveness_program` supplies them. The three programs of ANA-11
   are written as values; a printer or notation is not part of this card.
2. **One system per level.** A single system for the whole program is non-monotone under negation
   and has no least post-solution (`p :- !q.` has post-solutions with `q` empty and `p` full, and
   with `q` full and `p` empty), so the compile is per level and the engine runs level by level.
3. **Facts for derived predicates** are allowed (`FromFact`); a fact of level `k` feeds level `k`.
4. **Safety is required** so that every derived tuple lies inside the universe; `program_wf`
   rejects an unsafe rule, and `least_model` is only claimed to match the engine under it.
5. **Unstratifiable programs** have the empty `least_model` and `solve_program = None`; a client
   checks `stratify` first.
6. **Constants are codes.** There is no constant type parameter; a client encodes its keys with
   `encode`, and `holds` takes the codes, as ANA-11 does, so no decoding is needed.

## Cross-document contracts

Analyses uses the bare Rules names. Where a constructor conflicts, it uses its defining module.
`program_wf` takes the program and facts. The solvers return functions with post-solution proofs.
Order provides the finite powerset laws and height. Collections provides well-formed finite sets
and a `Table` keyed by `list positive`.

<!-- AUD-API-MAT-BEGIN -->

# MAT source contracts

Definitions specify source work; future theorem types are proof obligations.

## Galois.Rules.RulesAuditMaterializeDeltaTotal

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeDeltaTotal.v`.

```rocq
(** * Finite total execution, strata composition and whole source bound types
    The well-founded engine erases to repeated prepared steps and retains the final empty batch.
    Builds on: MatRounds and MatStratify. *)
From Stdlib Require Import List NArith PArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesModel RulesDelta.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Rules Require Import RulesAuditMaterializePlans.
From Galois.Rules Require Import RulesAuditMaterializeDifference.
From Galois.Rules Require Import RulesAuditMaterializeJobs.
From Galois.Rules Require Import RulesAuditMaterializeRounds.
From Galois.Rules Require Import RulesAuditMaterializeStratify.
Import ListNotations.
Section TotalRun.
Context {P:Type}(prog:program P) (facts:list(ground_atom P)) (st:mat_level_context P) (k:nat)
  (lower:database P)
 (cached:FinSet.t P*FinSet.t positive).
Inductive mat_total_run : delta_state P->delta_state P->list mat_frame->nat->Prop :=
 | MatTotalStop : forall state events,
 mat_prepared_step prog facts st k(mat_rel prog lower)cached state=(None, events)->
 mat_total_run state state events 0
 | MatTotalNext : forall state next final first rest rounds,
 mat_prepared_step prog facts st k(mat_rel prog lower)cached state=(Some next, first)->
 mat_total_run next final rest rounds->mat_total_run state final(first++rest) (S rounds).
End TotalRun.
Inductive mat_stratum_run {P} strategy(prog:program P)facts(st:mat_level_context P)k(lower:database
  P)
 : delta_state P->list mat_frame->nat->Prop :=
 | MatStratumRun : forall initial setup cached prepared final rounds events,
 mat_initial strategy prog facts st k(mat_rel prog lower)=(initial, setup)->
 mat_setup_cached prog facts=(cached, prepared)->
 mat_total_run prog facts st k lower cached initial final events rounds->
 mat_stratum_run strategy prog facts st k lower final(setup++prepared++events)rounds.
Inductive mat_levels_run {P} strategy(prog:program P)facts(st:mat_level_context P)
 : nat->database P->list mat_frame->nat->Prop :=
 | MatLevelsZero : mat_levels_run strategy prog facts st 0 Map.empty[MatBlock 90]0
 | MatLevelsNext : forall k lower before n1 state body n2 atoms enumeration final output,
 mat_levels_run strategy prog facts st k lower before n1->
 mat_stratum_run strategy prog facts st k lower state body n2->
 mat_elements(delta_accumulated state)=(atoms, enumeration)->mat_atom_fold prog atoms lower=(final,
   output)->
 mat_levels_run strategy prog facts st(S k)final(before++body++enumeration++output++[MatBlock 91])
   (n1+n2).
Definition mat_bounded_program {P} strategy(prog:program P)facts fuel :=
 stratification<-mat_stratify prog;; match stratification with None=> mat_return None
 | Some st=> mat_bounded_levels strategy prog facts st fuel(count(mat_native_levels st)) end.
Inductive mat_program_run {P} strategy(prog:program P)facts : option(database P)->list
  mat_frame->nat->Prop :=
 | MatProgramRejected : forall events, mat_stratify prog=(None, events)->mat_program_run strategy
   prog facts None events 0
 | MatProgramAccepted : forall st setup output events rounds,
 mat_stratify prog=(Some st, setup)->mat_levels_run strategy prog facts st(count(mat_native_levels
   st))output events rounds->
 mat_program_run strategy prog facts(Some output) (setup++events)rounds.
Fixpoint mat_terms_dimension(ts:list term) : nat := match ts with []=> 1
 | TVar v::rest=> (1+v+mat_terms_dimension rest)%nat
 | TConst c::rest=> (1+Pos.size_nat c+mat_terms_dimension rest)%nat end.
Definition mat_atom_dimension {P}(a:atom P) := mat_terms_dimension(args a).
Definition mat_rule_dimension {P}(r:rule P) :=
 (1+mat_atom_dimension(head r)+fold_right(fun lit n=> (mat_atom_dimension(lit_atom
   lit)+n)%nat)0%nat(body r))%nat.
Definition mat_input_dimension {P}(prog:program P) (facts:list(ground_atom P)) :=
 (1+fold_right(fun r n=> (mat_rule_dimension r+n)%nat)0%nat(rules prog)+
 fold_right(fun fact n=> (mat_tuple_size(snd fact)+n)%nat)0%nat facts)%nat.
Definition mat_whole_budget input loop_count operand_width :=
 (1000000000000*(S input)*(S loop_count)*Nat.pow(S operand_width)16)%nat.
Definition mat_total_realization_statement : Prop := forall P(prog:program P)facts st k lower
  cached state,
 delta_valid prog facts state->exists final events rounds, mat_total_run prog facts st k lower
   cached state final events rounds.
Definition mat_total_erases_statement : Prop := forall P(prog:program P)facts st k lower
  state(Hvalid:delta_valid prog facts state)final events rounds,
 let cached:=fst(mat_setup_cached prog facts) in
 mat_total_run prog facts st k lower cached state final events rounds->
 final=proj1_sig(delta_execute prog facts(mat_native_levels st)k(rel_of prog lower)state Hvalid).
Definition mat_total_unique_statement : Prop := forall P(prog:program P)facts st k lower cached
  state f1 e1 n1 f2 e2 n2,
 mat_total_run prog facts st k lower cached state f1 e1 n1->mat_total_run prog facts st k lower
   cached state f2 e2 n2->
 f1=f2 /\ e1=e2 /\ n1=n2.
Definition mat_stratum_realization_statement : Prop := forall P strategy(prog:program P)facts st k
  lower,
 exists final events rounds, mat_stratum_run strategy prog facts st k lower final events rounds.
Definition mat_stratum_erases_statement : Prop := forall P strategy(prog:program P)facts st k lower
  final events rounds,
 mat_stratum_run strategy prog facts st k lower final events rounds->
 final=delta_solve_stratum strategy prog facts(mat_native_levels st)k(rel_of prog lower).
Definition mat_levels_realization_statement : Prop := forall P strategy(prog:program P)facts st n,
 exists db events rounds, mat_levels_run strategy prog facts st n db events rounds.
Definition mat_levels_erases_statement : Prop := forall P strategy(prog:program P)facts st n db
  events rounds,
 mat_levels_run strategy prog facts st n db events rounds->db=delta_solve_levels strategy prog
   facts(mat_native_levels st)n.
Definition mat_program_realization_statement : Prop := forall P strategy(prog:program P)facts,
 exists output events rounds, mat_program_run strategy prog facts output events rounds.
Definition mat_program_erases_statement : Prop := forall P strategy(prog:program P)facts output
  events rounds,
 mat_program_run strategy prog facts output events rounds->output=solve_program_delta strategy prog
   facts.
Definition mat_program_unique_statement : Prop := forall P strategy(prog:program P)facts o1 e1 n1
  o2 e2 n2,
 mat_program_run strategy prog facts o1 e1 n1->mat_program_run strategy prog facts o2 e2 n2->o1=o2
   /\ e1=e2 /\ n1=n2.
Definition mat_program_whole_bound_statement : Prop := forall P strategy(prog:program P)facts
  output events rounds,
 mat_program_run strategy prog facts output events rounds->
 (mat_work events<=mat_whole_budget(mat_input_dimension prog facts) (rounds+length(rules prog))
   (mat_width events))%nat.
Definition mat_bounded_program_erases_statement : Prop := forall P strategy(prog:program P)facts
  fuel,
 fst(mat_bounded_program strategy prog facts fuel)=delta_bounded_program strategy prog facts fuel.
Definition mat_bounded_program_bound_statement : Prop := forall P strategy(prog:program P)facts
  fuel,
 let '(_, events):=mat_bounded_program strategy prog facts fuel in
 (mat_work events<=mat_whole_budget(mat_input_dimension prog facts) (Pos.to_nat fuel+1) (mat_width
   events))%nat.
Definition mat_materialization_consumer_statement : Prop := forall P strategy(prog:program P)facts
  output events rounds,
 program_wf prog facts->mat_program_run strategy prog facts output events rounds->
 forall db, output=Some db->represents(rel_of prog db) (least_model prog facts).

(** This carrier is a mathematical input budget, not an executed enumeration. *)
Definition mat_program_loop_budget {P}(prog:program P)facts :=
 ((1+length(rule_nodes prog))*(1+length(delta_support prog facts)))%nat.
Definition mat_total_rounds_input_bound_statement : Prop := forall P(prog:program P)facts st k
  lower state final events rounds,
 delta_valid prog facts state->
 mat_total_run prog facts st k lower(fst(mat_setup_cached prog facts))state final events rounds->
 (rounds<=delta_remaining prog facts state)%nat.
Definition mat_program_rounds_input_bound_statement : Prop := forall P strategy(prog:program
  P)facts output events rounds,
 mat_program_run strategy prog facts output events rounds->(rounds<=mat_program_loop_budget prog
   facts)%nat.
Definition mat_program_input_loop_bound_statement : Prop := forall P strategy(prog:program P)facts
  output events rounds,
 mat_program_run strategy prog facts output events rounds->
 (mat_work events<=mat_whole_budget(mat_input_dimension prog facts) (mat_program_loop_budget prog
   facts) (mat_width events))%nat.
Definition rules_materialization_cost_statement := mat_program_input_loop_bound_statement.
Definition rules_materialization_source_correspondence_statement := mat_program_erases_statement.
Definition rules_materialization_consumer_statement := mat_materialization_consumer_statement.

(** The permitted maximum is measured on this same execution, independently of work. *)
Definition rules_materialization_same_execution_bound_statement :=
  mat_program_input_loop_bound_statement.

(** Only the genuinely supplied predicate encoder and arity callbacks have these interfaces.
    The client supplies its literal body judgment, not a value paired with an arbitrary price.
    A receipt preserves the actual input, output, source derivation and positive body frames. *)
Record mat_predicate_callback_source {P}(prog:program P) (B:Type) : Type :=
  MatPredicateCallbackSource {
 mat_predicate_encoder_body : P->positive->list B->Prop;
 mat_predicate_arity_body : P->nat->list B->Prop;
 mat_predicate_body_frame_weight : B->nat
}.
Definition mat_predicate_callback_receipts_statement {P}(prog:program P)B
 (source:mat_predicate_callback_source prog B) : Prop :=
 (forall frame, (1<=mat_predicate_body_frame_weight _ _ source frame)%nat) /\
 (forall p, exists body, mat_predicate_encoder_body _ _ source p(encode(penc prog)p)body) /\
 (forall p, exists body, mat_predicate_arity_body _ _ source p(arity prog p)body) /\
 (forall p code body, mat_predicate_encoder_body _ _ source p code body->code=encode(penc prog)p) /\
 (forall p value body, mat_predicate_arity_body _ _ source p value body->value=arity prog p).
Definition mat_predicate_callback_input_bounds_statement {P}(prog:program P)B
 (source:mat_predicate_callback_source prog B) (encode_budget arity_budget:P->nat) : Prop :=
 (forall p code body, mat_predicate_encoder_body _ _ source p code body->
 (1+fold_right(fun frame n=> mat_predicate_body_frame_weight _ _ source frame+n)0
   body<=encode_budget p)%nat) /\
 (forall p value body, mat_predicate_arity_body _ _ source p value body->
 (1+fold_right(fun frame n=> mat_predicate_body_frame_weight _ _ source frame+n)0
   body<=arity_budget p)%nat).
(** An external stratification may supply a level function. Internally captured level maps
    always use mat_level's concrete MatCapturedLevels branch and never this adapter. *)
Record mat_external_level_source {P}(st:stratification P) (B:Type) : Type := MatExternalLevelSource
  {
 mat_external_level_body : P->nat->list B->Prop;
 mat_external_level_frame_weight : B->nat
}.
Definition mat_external_level_receipts_statement {P}(st:stratification P)B
 (source:mat_external_level_source st B) (input_budget:P->nat) : Prop :=
 (forall frame, (1<=mat_external_level_frame_weight _ _ source frame)%nat) /\
 (forall p, exists body, mat_external_level_body _ _ source p(level st p)body) /\
 (forall p value body, mat_external_level_body _ _ source p value body->value=level st p /\
 (1+fold_right(fun frame n=> mat_external_level_frame_weight _ _ source frame+n)0
   body<=input_budget p)%nat).
```

## Galois.Rules.RulesAuditMaterializeDifference

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeDifference.v`.

```rocq
(** * Literal FinSet difference trie combine
    Both one-sided filters traverse every stored node; empty output does not skip their work.
    Builds on: MatPrelude and the seven native nonempty trie constructors. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Collections Require Import CollectionsAuditElements.
Definition mat_node {A} (l:Trie.t A) o r := mat_mark 40 (mat_return(Trie.node l o r)).
Fixpoint mat_filter_ne {A B} (f:A->mat_run(option B)) (n:Trie.ne A) : mat_run(Trie.t B) := mat_mark
  41 (
 match n with
 | Trie.N001 r=> right<-mat_filter_ne f r;;  mat_node Trie.Empty None right
 | Trie.N010 v=> value<-f v;;  mat_node Trie.Empty value Trie.Empty
 | Trie.N011 v r=> value<-f v;;  right<-mat_filter_ne f r;;  mat_node Trie.Empty value right
 | Trie.N100 l=> left<-mat_filter_ne f l;;  mat_node left None Trie.Empty
 | Trie.N101 l r=> left<-mat_filter_ne f l;;  right<-mat_filter_ne f r;;  mat_node left None right
 | Trie.N110 l v=> left<-mat_filter_ne f l;;  value<-f v;;  mat_node left value Trie.Empty
 | Trie.N111 l v r=> left<-mat_filter_ne f l;; value<-f v;;  right<-mat_filter_ne f r;;  mat_node
   left value right end).
Definition mat_filter_trie {A B} (f:A->mat_run(option B)) (input:Trie.t A) := mat_mark 42 (
 match input with Trie.Empty=> mat_return Trie.Empty | Trie.Nodes n=> mat_filter_ne f n end).
Definition mat_diff_value {K} (a b:option(K*unit)) := mat_mark 43 (mat_return(
 match a, b with Some(k, _), None=> Some(k, tt) | _, _=> None end)).
Definition mat_diff_left {K} := @mat_filter_trie (K*unit) (K*unit) (fun a=> mat_diff_value(Some
  a)None).
Definition mat_diff_right {K} := @mat_filter_trie (K*unit) (K*unit) (fun b=> mat_diff_value
  None(Some b)).
Fixpoint mat_diff_ne {K} (n:Trie.ne(K*unit)) (b:Trie.t(K*unit)) : mat_run(Trie.t(K*unit)) :=
  mat_mark 44 (
 match b with Trie.Empty=> mat_diff_left(Trie.Nodes n) | Trie.Nodes _=>
 match n with
 | Trie.N001 r=> left<-mat_diff_right(Trie.left b);;  value<-mat_diff_value None(Trie.value b);;
 right<-mat_diff_ne r(Trie.right b);;  mat_node left value right
 | Trie.N010 v=> left<-mat_diff_right(Trie.left b);;  value<-mat_diff_value(Some v) (Trie.value b);;
 right<-mat_diff_right(Trie.right b);;  mat_node left value right
 | Trie.N011 v r=> left<-mat_diff_right(Trie.left b);; value<-mat_diff_value(Some v) (Trie.value
   b);;
 right<-mat_diff_ne r(Trie.right b);;  mat_node left value right
 | Trie.N100 l=> left<-mat_diff_ne l(Trie.left b);;  value<-mat_diff_value None(Trie.value b);;
 right<-mat_diff_right(Trie.right b);;  mat_node left value right
 | Trie.N101 l r=> left<-mat_diff_ne l(Trie.left b);;  value<-mat_diff_value None(Trie.value b);;
 right<-mat_diff_ne r(Trie.right b);;  mat_node left value right
 | Trie.N110 l v=> left<-mat_diff_ne l(Trie.left b);;  value<-mat_diff_value(Some v) (Trie.value
   b);;
 right<-mat_diff_right(Trie.right b);;  mat_node left value right
 | Trie.N111 l v r=> left<-mat_diff_ne l(Trie.left b);;  value<-mat_diff_value(Some v) (Trie.value
   b);;
 right<-mat_diff_ne r(Trie.right b);;  mat_node left value right end end).
Definition mat_diff {K} (a b:FinSet.t K) := mat_mark 45 (
 match a with Trie.Empty=> mat_diff_right b | Trie.Nodes n=> mat_diff_ne n b end).
Definition mat_diff_erases_statement : Prop := forall K E (a b:FinSet.t K), fst(mat_diff a
  b)=FinSet.diff E a b.
Definition mat_diff_bound_statement : Prop := forall K (a b:FinSet.t K),
 (mat_work(snd(mat_diff a b)) <= 10000*(1+audit_trie_nodes a+audit_trie_nodes b))%nat.
```

## Galois.Rules.RulesAuditMaterializeFullSource

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeFullSource.v`.

```rocq
(** * Complete naive and semi-naive source boundaries

    Both fixed public solvers include real predicate callback bodies at their actual occurrences.
    For example, a cached arity read has one source receipt for the supplied arity implementation.
    Builds on: the concrete Delta and naive total runs and per-call predicate receipts. *)

From Stdlib Require Import List.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta
  RulesAuditMaterializePrelude RulesAuditMaterializeDeltaTotal RulesAuditMaterializeReceipts
  RulesAuditMaterializeNaiveTotal.

(** Every real external occurrence in a completed Delta run has its literal body receipt. *)
Definition mat_delta_program_callback_receipts_statement : Prop :=
  forall P strategy (prog : program P) facts B (source : mat_predicate_callback_source prog B)
    encode_budget arity_budget output events rounds,
  mat_predicate_callback_receipts_statement prog B source ->
  mat_program_run strategy prog facts output events rounds ->
  exists receipts,
    mat_external_trace_receipts prog B source encode_budget arity_budget events receipts.

(** The full Delta bound uses input rounds, actual operands and only per-call external allowances.
  *)
Definition rules_delta_materialization_full_source_statement : Prop :=
  forall P strategy (prog : program P) facts B (source : mat_predicate_callback_source prog B)
    encode_budget arity_budget,
  mat_predicate_callback_receipts_statement prog B source ->
  mat_predicate_callback_input_bounds_statement prog B source encode_budget arity_budget ->
  exists output events rounds receipts,
    mat_program_run strategy prog facts output events rounds /\
    output = solve_program_delta strategy prog facts /\
    mat_external_trace_receipts prog B source encode_budget arity_budget events receipts /\
    mat_work events + mat_external_body_work prog B source receipts <=
      mat_whole_budget (mat_input_dimension prog facts) (mat_program_loop_budget prog facts)
        (mat_width events) + mat_external_trace_allowance B receipts.

(** This family root includes both fixed algorithms and no generic operation placeholder. *)
Definition rules_materialization_full_source_statement : Prop :=
  rules_delta_materialization_full_source_statement /\
  rules_naive_materialization_full_source_statement.
```

## Galois.Rules.RulesAuditMaterializeJobs

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeJobs.v`.

```rocq
(** * Exact delta tagging, rule variants and prepared jobs
    Universe closures distinguish legacy partial preparation from the cached two-argument body.
    Builds on: MatPlans and the native source callback captures. *)
From Stdlib Require Import List NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditFinSet.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Collections Require Import CollectionsAuditPrimitive.
From Galois.Rules Require Import RulesAuditRelations.
From Galois.Rules Require Import RulesAuditUniverse.
From Galois.Rules Require Import RulesAuditNestedPrepare.
From Galois.Rules Require Import RulesAuditNestedProbe.
From Galois.Rules Require Import RulesAuditMultiwayPrepare.
From Galois.Rules Require Import RulesAuditMultiwayProbe.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Rules Require Import RulesAuditMaterializePlans.
Import ListNotations.
Definition mat_pos_equal a b := mat_lift 50 (fun _=> 1+Pos.size_nat a+Pos.size_nat b)
  audit_positive_eqb_source_work(audit_positive_eqb a b).
Definition mat_term_equal a b := mat_mark 51(match a, b with
 | TVar x, TVar y=> mat_nat_test 0 Nat.eqb x y | TConst x, TConst y=> mat_pos_equal x y | _, _=>
   mat_return false end).
Fixpoint mat_terms_equal xs ys : mat_run bool := mat_mark 52(match xs, ys with
 | [], []=> mat_return true | x::xs, y::ys=> first<-mat_term_equal x y;;  later<-mat_terms_equal xs
   ys;;  mat_return(first&&later)
 | _, _=> mat_return false end).
Definition mat_atom_equal {P} E (a b:atom P) :=
 first<-mat_encode E(pred a);;  second<-mat_encode E(pred b);;  same<-mat_pos_equal first second;;
 terms<-mat_terms_equal(args a) (args b);;  mat_return(same&&terms).
Definition mat_tag_atom {P} E (pivot a:atom P) := same<-mat_atom_equal E a pivot;;
  mat_return(Atom(pred a, same) (args a)).
Definition mat_tag_rule {P} E (r:rule P) pivot :=
 ps<-mat_positive_atoms(body r);;  literals<-mat_map(fun a=> tagged<-mat_tag_atom E pivot a;;
   mat_return(LPos tagged))ps;;
 mat_return(Rule(Atom(pred(head r), false) (args(head r)))literals).
Definition mat_recursive {P} (st:mat_level_context P) k (r:rule P) := ps<-mat_positive_atoms(body
  r);;
 mat_filter(fun a=> lev<-mat_level st(pred a);;  mat_nat_test 1 Nat.eqb lev k)ps.
Definition mat_specs {P} (prog:program P) st k :=
 rs<-mat_filter(fun r=> lev<-mat_level st(pred(head r));;  mat_nat_test 2 Nat.eqb lev k) (rules
   prog);;
 mat_flatmap(fun r=> atoms<-mat_recursive st k r;;  mat_map(fun a=> mat_return(r, a))atoms)rs.
Definition mat_current {P} (prog:program P) st k (lower:P->mat_run(FinSet.t tuple)) db p :=
 lev<-mat_level st p;;  current<-mat_nat_test 3 Nat.eqb lev k;;
 if current then mat_rel prog db p else lower p.
Definition mat_tag_env {P} (prog:program P) st k lower acc front (q:P*bool) := mat_mark 53 (
 if snd q then mat_rel prog front(fst q) else mat_current prog st k lower acc(fst q)).
(** Predicate encoders inside imported set operations remain actual typed callback occurrences. *)
Definition mat_predicate_set_calls {P} (prog : program P)
    (events : list (audit_set_event P (rules_encode_entry P))) : list mat_frame :=
  flat_map (fun event =>
    let encoded := match event with
      | AuditSetAdd _ _ _ _ encoded _ | AuditSetMem _ _ _ _ encoded _ =>  encoded
      | _ =>  []
      end in
    map (fun entry =>  match entry with
      | RulesEncodeEntry p code =>  MatEncode P (penc prog) p code
      end) encoded) events.

(** Imported universe preparation exposes its real encoder and arity calls. *)
Definition mat_universe_calls {P} (prog : program P)
    (events : list (rules_universe_event P)) : list mat_frame :=
  flat_map (fun event =>  match event with
    | RuPredicatesSet _ _ inner | RuPredicateMem _ _ _ inner =>  mat_predicate_set_calls prog inner
    | RuArity p n =>  [MatArity P prog p n]
    | _ =>  []
    end) events.

Definition mat_universe_prepare_source {P} (prog : program P) facts p :=
  let '(state, events) := rules_universe_prepare_counted prog facts p in
  (state, MatImported _ 60 (state, events) (rules_universe_work events) 1 ::
    mat_universe_calls prog events).


Definition mat_setup_cached {P} (prog:program P) facts :=
 rule_ps<-mat_lift 54 (@length P) rules_universe_work(ru_rule_predicates(rules prog));;
 fact_ps<-mat_lift 55 (@length P) rules_universe_work(ru_fact_predicates facts);;
 ps<-mat_append rule_ps fact_ps;;  predicates<-mat_predicate_set_encoded(mat_encode(penc prog))ps;;
 rule_cs<-mat_lift 56 (@length positive) rules_universe_work(ru_rule_constants(rules prog));;
 fact_cs<-mat_lift 57 (@length positive) rules_universe_work(ru_fact_constants facts);;
 cs<-mat_append rule_cs fact_cs;;  constants<-mat_of_list audit_positive_encode
   audit_basic_encoding_work cs;;
 mat_return(predicates, constants).
Definition mat_accept_cached {P} (prog:program P) (state:FinSet.t P*FinSet.t positive) p row :=
 found<-mat_get(penc prog)p(fst state);;
 present<-mat_return(match found with Some _=> true | None=> false end);;
 length<-mat_nat 4 (fun _ _=> List.length row) (List.length row)0;;  arity<-mat_arity prog p;;
 proper<-mat_nat_test 5 Nat.eqb length arity;;
 constants<-mat_all(fun c=> mat_lift 59 (fun _=> 1+Pos.size_nat c+audit_trie_nodes(snd state))
 (audit_finset_source_work audit_basic_encoding_work) (audit_finset_mem audit_positive_encode c(snd
   state)))row;;
 mat_return(present&&proper&&constants).
Definition mat_variant {P} (prog:program P) (facts:list(ground_atom P)) lower (r:rule P) pivot env
  plan
 (accept:P->tuple->mat_run bool) : mat_run(list tuple) :=
 tagged<-mat_tag_rule(penc prog)r pivot;;  ps<-mat_positive_atoms(body tagged);;
 bindings<-mat_plan_bindings ps env plan;;  good<-mat_filter(mat_negative r lower)bindings;;
 rows<-mat_map(fun b=> mat_instantiate b(args(head r)))good;;  mat_filter(accept(pred(head r)))rows.
Definition mat_variant_legacy {P} (prog:program P) facts lower r pivot env plan :=
 state<-mat_universe_prepare_source prog facts(pred(head r));;
 @mat_variant P prog facts lower r pivot env plan (fun _ row=> mat_lift 61 (fun _=>
   1+mat_tuple_size row)
 rules_universe_work(@rules_universe_check_counted P state row)).
Definition mat_prepare_jobs {P} strategy (prog:program P) st k lower acc front :=
 specs<-mat_specs prog st k;;
 atoms<-mat_flatmap(fun spec=> tagged<-mat_tag_rule(penc prog) (fst spec) (snd spec);;
   mat_positive_atoms(body tagged))specs;;
 snapshot<-mat_snapshot_encoded(mat_tagged_encoder prog)atoms(mat_tag_env prog st k lower acc
   front);;
 mat_map(fun spec=> let '(r, pivot):=spec in tagged<-mat_tag_rule(penc prog)r pivot;;
 ps<-mat_positive_atoms(body tagged);; plan<-mat_plan_rows strategy
   ps(mat_snapshot_rows_encoded(mat_tagged_encoder prog)snapshot);;
 mat_return(spec, plan))specs.
Definition mat_update_jobs {P} (prog:program P) (rows:P->mat_run(list tuple)) (jobs:list(delta_job
  P)) :=
 mat_map(fun job=> updated<-mat_plan_update(fun q=> mat_return(snd q)) (fun q=> rows(fst q)) (snd
   job);;
 mat_return(fst job, updated))jobs.
Definition mat_candidates {P} (prog:program P) facts st k lower acc front (jobs:list(delta_job P))
  :=
 atoms<-mat_flatmap(fun job=> let '((r, pivot), plan):=job in
 rows<-mat_variant_legacy prog facts lower r pivot(mat_tag_env prog st k lower acc front)plan;;
 mat_map(fun row=> mat_return(pred(head r), row))rows)jobs;;  mat_ground_set prog atoms.
Definition mat_candidates_prepared {P} (prog:program P) facts st k lower acc front jobs cached :=
 atoms<-mat_flatmap(fun job=> let '((r, pivot), plan):=job in
 rows<-mat_variant prog facts lower r pivot(mat_tag_env prog st k lower acc
   front)plan(mat_accept_cached prog cached);;
 mat_map(fun row=> mat_return(pred(head r), row))rows)jobs;;  mat_ground_set prog atoms.
Definition mat_tag_rule_erases_statement : Prop := forall P E (r:rule P) pivot,
 fst(mat_tag_rule E r pivot)=delta_tag_rule E r pivot.
Definition mat_prepare_jobs_erases_statement : Prop := forall P strategy (prog:program P) st k
  lower acc front,
 fst(mat_prepare_jobs strategy prog (MatExternalLevels st) k(fun p=> mat_return(lower p))acc
   front)=delta_prepare_jobs strategy prog st k lower acc front.
Definition mat_candidates_erases_statement : Prop := forall P(prog:program P)facts st k lower acc
  front jobs,
 fst(mat_candidates prog facts (MatExternalLevels st) k(fun p=> mat_return(lower p))acc front
   jobs)=delta_candidates prog facts st k lower acc front jobs.
```

## Galois.Rules.RulesAuditMaterializeNaiveBodies

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveBodies.v`.

```rocq
(** * Fixed generated naive-solver callback data bodies
    The remaining FX/RPO execution adapter must compose these concrete bodies at actual calls.
    Builds on: MatTotal and the prepared RulesSolve source. *)
From Stdlib Require Import List NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Rules Require Import RulesAuditNestedProbe.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Rules Require Import RulesAuditIndex.
From Galois.Rules Require Import RulesAuditMaterializePlans.
From Galois.Rules Require Import RulesAuditMaterializeJobs.
From Galois.Rules Require Import RulesAuditMaterializeRounds.
From Galois.Rules Require Import RulesAuditMaterializeStratify.
Import ListNotations.
Definition mat_nat_encoder n := mat_lift 120 Pos.size_nat audit_nat_events_work(audit_nat_encode n).
Fixpoint mat_numbered_rules {P} n(rs:list(rule P)) : mat_run(list(nat*rule P)) := mat_mark
  121(match rs with
 | []=> mat_return [] | r::rest=> next<-mat_nat 30 Nat.add n 1;; tail<-mat_numbered_rules next
   rest;; mat_return((n, r)::tail) end).
Fixpoint mat_rule_index {P} n(rs:list(rule P)) : mat_run(Map.t nat(rule P)) := mat_mark 122(match
  rs with
 | []=> mat_return Map.empty | r::rest=> next<-mat_nat 31 Nat.add n 1;; tail<-mat_rule_index next
   rest;; mat_set_encoded mat_nat_encoder n r tail end).
Definition mat_dependencies {P}(prog:program P)st k(r:rule P) :=
 ps<-mat_positive_atoms(body r);; selected<-mat_filter(fun a=> lev<-mat_level st(pred a);;
   mat_nat_test 32 Nat.eqb lev k)ps;;
 keys<-mat_map(fun a=> mat_return(pred a))selected;; set<-mat_predicate_set_encoded(mat_encode(penc
   prog))keys;; mat_elements set.
Fixpoint mat_fill_values {P A}(E:encoding P) (ps:list P) (values:list A) : mat_run(Map.t P A) :=
  mat_mark 123(match ps, values with
 | p::rest, v::tail=> before<-mat_fill_values E rest tail;; mat_set E p v before | _, _=>
   mat_return Map.empty end).
Definition mat_generated_env {P}(prog:program P)facts st lower k(reads:Map.t P(relation prog
  facts))p :=
 lev<-mat_level st p;; same<-mat_nat_test 33 Nat.eqb lev k;; if same then
 found<-mat_get(penc prog)p reads;; mat_return(match found with Some value=> proj1_sig value |
   None=> FinSet.empty end)else lower p.
Fixpoint mat_classic_join {P}(ps:list(atom P))bound(env:P->mat_run(FinSet.t tuple))bindings :
  mat_run(list binding) := mat_mark 124(match ps with
 | []=> mat_return bindings | a::rest=> next_bound<-mat_bound_add bound a;;
 set<-env(pred a);; rows<-mat_elements set;; index<-mat_build_index_full bound(args a)rows;;
 joined<-mat_lift 125 (@length binding)rules_nested_probe_work(rules_probe_bindings(NestedSearch
   bound(args a)index)bindings);;
 mat_classic_join rest next_bound env joined end).
Definition mat_naive_firing {P}(prog:program P)cached(r:rule P)env :=
 ps<-mat_positive_atoms(body r);; bindings<-mat_classic_join ps FinSet.empty env[Map.empty];;
 accepted<-mat_filter(mat_negative r env)bindings;; rows<-mat_map(fun b=> mat_instantiate
   b(args(head r)))accepted;;
 valid<-mat_filter(mat_accept_cached prog cached(pred(head r)))rows;;
 mat_of_list(audit_list_encode audit_positive_encode) (audit_list_events_work
   audit_basic_encoding_work)valid.
Definition mat_clamp {P}(prog:program P)cached p(set:FinSet.t tuple) :=
 rows<-mat_elements set;; accepted<-mat_filter(mat_accept_cached prog cached p)rows;;
 mat_of_list(audit_list_encode audit_positive_encode) (audit_list_events_work
   audit_basic_encoding_work)accepted.
Definition mat_constraints {P}(prog:program P) (facts:list(ground_atom P))st k :=
 indexed<-mat_numbered_rules 0(rules prog);;
 first<-mat_flatmap(fun ir=> lev<-mat_level st(pred(head(snd ir)));; same<-mat_nat_test 34 Nat.eqb
   lev k;;
 mat_return(if same then[FromRule(fst ir) (pred(head(snd ir)))]else[]))indexed;;
 predicates<-mat_map(fun fact=> mat_return(fst fact))facts;;
   distinct<-mat_predicate_set_encoded(mat_encode(penc prog))predicates;;
 keys<-mat_elements distinct;; selected<-mat_filter(fun p=> lev<-mat_level st p;; mat_nat_test 35
   Nat.eqb lev k)keys;;
 second<-mat_map(fun p=> mat_return(FromFact p))selected;; mat_append first second.
Definition mat_generated_deps {P}(prog:program P)st k(ri:Map.t nat(rule P)) (c:rconstraint P) :=
 match c with FromFact _=> mat_return [] | FromRule i _=> found<-mat_get_encoded mat_nat_encoder i
   ri;;
 match found with None=> mat_return [] | Some r=> mat_dependencies prog st k r end end.
Definition mat_generated_targets {P}(prog:program P)facts st k :=
 constraints<-mat_constraints prog facts st k;; keys<-mat_map(fun c=> mat_return(match c with
   FromRule _ h=> h | FromFact p=> p end))constraints;;
 set<-mat_predicate_set_encoded(mat_encode(penc prog))keys;; mat_elements set.
Definition mat_store_relations {P}(prog:program P)facts ps(s:P->relation prog facts)db :=
 mat_foldr(fun p before=> value<-mat_return(proj1_sig(s p));; mat_set(penc prog)p value before)ps
   db.
Definition mat_rule_index_erases_statement : Prop := forall P n(rs:list(rule P)),
  fst(mat_rule_index n rs)=index_rules_from n rs.
Definition mat_dependencies_erases_statement : Prop := forall P(prog:program P)st k r,
 fst(mat_dependencies prog(MatExternalLevels st)k r)=level_dependencies prog st k r.
Definition mat_constraints_erases_statement : Prop := forall P(prog:program P)facts st k,
 fst(mat_constraints prog facts(MatExternalLevels st)k)=stratum_constraints prog facts st k.
Definition mat_classic_join_erases_statement : Prop := forall P ps bound env bindings,
 fst(@mat_classic_join P ps bound(fun p=> mat_return(env p))bindings)=join_positive ps bound env
   bindings.

(** Real environment traces change cost, while the selected values feed the native join. *)
Definition mat_classic_join_source_erases_statement : Prop := forall P ps bound
    (env : P -> mat_run (FinSet.t tuple)) bindings,
  fst (mat_classic_join ps bound env bindings) =
    join_positive ps bound (fun p =>  fst (env p)) bindings.

(** The cached firing body has the native output for the fixed prepared universe sets. *)
Definition mat_naive_firing_erases_statement : Prop := forall P (prog : program P) facts r env,
  fst (mat_naive_firing prog (fst (mat_setup_cached prog facts)) r env) =
    fire_rule prog facts r (fun p =>  fst (env p)).

(** The cached clamp uses the same admissibility test and output representation as restrict. *)
Definition mat_clamp_erases_statement : Prop := forall P (prog : program P) facts p input,
  fst (mat_clamp prog (fst (mat_setup_cached prog facts)) p input) =
    proj1_sig (restrict prog facts p input).

(** The generated environment retains its actual level and map lookup branches. *)
Definition mat_generated_env_erases_statement : Prop :=
  forall P (prog : program P) facts st lower k reads p,
  fst (mat_generated_env prog facts st (mat_rel prog lower) k reads p) =
    stratum_env prog facts (mat_native_levels st) (rel_of prog lower) k reads p.
```

## Galois.Rules.RulesAuditMaterializeNaiveCallbacks

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCallbacks.v`.

```rocq
(** * Literal callback bodies for the naive total solver

    Generated queries, continuations and lattice calls have fixed source instances.
    For example, continuation receipts retain their actual ask-all capture and input value.
    Builds on: the materialization system, query and finite-powerset models. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditEncoding CollectionsAuditFinSet
  CollectionsAuditElements.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklistCallbacks FixpointAuditSchedule
  FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesAuditRelations
  RulesAuditMaterializePrelude RulesAuditMaterializeJobs RulesAuditMaterializeNaiveBodies
  RulesAuditMaterializeNaiveQuery RulesAuditMaterializePowerset RulesAuditMaterializeSystem.
Import List.ListNotations.

(** The internal constraint encoder expands the actual nat/predicate pair encoding. *)
Definition mat_constraint_encoder {P} (prog : program P) (c : rconstraint P) : mat_run positive :=
  mat_mark 160 (match c with
  | FromFact p =>  code <- mat_encode (penc prog) p;;  mat_return (xI code)
  | FromRule i h =>
    let '(code, events) := audit_pair_encode audit_nat_encode (rules_encoder (penc prog)) (i, h) in
    (xO code, MatImported _ 161 (code, events)
      (audit_pair_events_work audit_nat_events_work (@length (rules_encode_entry P)) events)
      (1 + i + Pos.size_nat code) ::
      flat_map (fun event =>  match event with
        | AuditPairSecond p encoded _ =>  [MatEncode P (penc prog) p encoded]
        | _ =>  []
        end) events)
  end).

Definition mat_positive_body_work (events : list mat_frame) : nat :=
  fold_right (fun frame n =>  S (mat_frame_work frame) + n) 0 events.

Definition mat_index_source_event_work {P}
    (event : fx_index_nested_event P (rconstraint P) mat_frame) : nat :=
  match event with
  | FxiTarget _ _ body | FxiSides _ _ body | FxiDeps _ _ body =>  3 + mat_positive_body_work body
  | FxiDistinctBuild _ _ body =>  3 + audit_finset_source_work mat_positive_body_work body
  | FxiDistinctElements _ _ body =>  3 + audit_set_elements_work body
  | FxiRead _ _ _ _ enc trie =>
    8 + mat_positive_body_work enc + audit_trie_get_trace_source_work trie
  | FxiWrite _ _ _ _ _ enc trie =>
    8 + mat_positive_body_work enc + audit_trie_update_trace_source_work trie
  | FxiCase _ =>  3
  end.

Definition mat_dep_source_weight {P} (event : fx_dep_event P (rconstraint P) mat_frame) : nat :=
  16 + match event with
  | FxDepIndexEvent nested =>  mat_index_source_event_work nested
  | FxDepEncode _ _ body =>  mat_positive_body_work body
  | FxDepCase _ =>  0
  | FxDepListWork size =>  1 + size
  end.

Inductive mat_naive_body_event (P : Type) : Type :=
  | MatNaiveLocal (event : mat_frame)
  | MatNaiveScheduleQuery
      (event : audit_rpo_schedule_event P (fx_dep_event P (rconstraint P) mat_frame)).

Arguments MatNaiveLocal {P} _.
Arguments MatNaiveScheduleQuery {P} _.

Definition mat_naive_body_weight {P} (event : mat_naive_body_event P) : nat :=
  match event with
  | MatNaiveLocal local =>  S (mat_frame_work local)
  | MatNaiveScheduleQuery nested =>  S (audit_rpo_schedule_event_work mat_dep_source_weight nested)
  end.

Definition mat_local_receipt {P A} (run : mat_run A) (result : A)
    (body : list (mat_naive_body_event P)) : Prop :=
  exists local, run = (result, local) /\ body = map MatNaiveLocal local.

Section GeneratedBackend.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : mat_level_context P) (lower : database P) (k : nat)
  (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
  (schedule : fx_rpo_result P (rconstraint P) mat_frame).

(** Every library-owned callback is the fixed generated body at this captured source invocation. *)
Definition mat_naive_declared_source :
    fx_declared_callback_source P (rconstraint P) (relation prog facts) (mat_naive_body_event P) :=
  {| fx_source_encode_x := fun x result body =>
       mat_local_receipt (mat_encode (penc prog) x) result body;
     fx_source_encode_c := fun c result body =>
       mat_local_receipt (mat_constraint_encoder prog c) result body;
     fx_source_target := fun c result body =>  mat_local_receipt (mat_target_source c) result body;
     fx_source_priority := fun x result body =>  exists local,
       audit_rpo_schedule_priority (fx_dep_encoder (mat_index_callbacks prog st k ri))
         (fx_rpo_positions schedule) x = (result, local) /\
       body = map MatNaiveScheduleQuery local;
     fx_source_widening_point := fun x result body =>  exists local,
       audit_rpo_schedule_widening (fx_dep_encoder (mat_index_callbacks prog st k ri))
         (fx_rpo_heads schedule) x = (result, local) /\ body = map MatNaiveScheduleQuery local;
     fx_source_rhs := fun c result body =>
       mat_local_receipt (mat_rhs_source prog facts st lower k cached ri fi c) result body;
     fx_source_continuation := fun native value result body =>  exists local,
       mat_generated_continuation_source prog facts st lower k cached ri native value result local
  /\
       body = map MatNaiveLocal local;
     fx_source_leb := fun a b result body =>
       mat_local_receipt (mat_relation_leb prog facts a b) result body;
     fx_source_join := fun a b result body =>
       mat_local_receipt (mat_relation_join prog facts a b) result body;
     fx_source_widen := fun a b result body =>
       mat_local_receipt (mat_relation_widen prog facts a b) result body |}.

(** The concrete instance satisfies the FX source laws without assuming its own whole bound. *)
Definition mat_naive_declared_source_laws_statement : Prop :=
  cached = fst (mat_setup_cached prog facts) -> ri = index_rules_from 0 (rules prog) ->
  fi = facts_by_pred prog facts -> schedule = mat_rpo_source prog facts st lower k ri ->
  fx_declared_source_laws (penc prog) (rconstraint_encoding (penc prog))
    (relation_lattice prog facts)
    (rpo_scheduler (penc prog) (mat_compiled_system prog facts st lower k)
      (mat_compiled_static prog facts st lower k))
    (mat_compiled_system prog facts st lower k) mat_naive_declared_source.

End GeneratedBackend.

(** All callback-frame weights include a positive local allowance. *)
Definition mat_naive_body_positive_statement : Prop := forall P (event : mat_naive_body_event P),
  1 <= mat_naive_body_weight event.

(** The literal index weights are the fixed FX instance, not a separately chosen price. *)
Definition mat_index_weight_instance_statement : Prop := forall P (prog : program P) st k ri event,
  mat_index_source_event_work event = fxi_event_work (mat_index_callback_budget prog st k ri) event.
```

## Galois.Rules.RulesAuditMaterializeNaiveDimensions

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveDimensions.v`.

```rocq
(** * Same-execution operands and input loop budget

    Dimensions inspect actual data operands, never returned work or event counts.
    For example, queue dimensions include its real entries and encoded priorities.
    Builds on: the source captures and the finite-powerset termination height. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap CollectionsAuditCost CollectionsAuditElements CollectionsAuditQueue.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditWorklist FixpointAuditTotal FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeDeltaTotal RulesAuditMaterializeTrace.
Import List.ListNotations.

Definition mat_relation_dimension {P} (prog : program P) facts (a : relation prog facts) : nat :=
  1 + audit_trie_nodes (proj1_sig a) +
    fold_right (fun row n =>  mat_tuple_size row + n) 0 (FinSet.elements (proj1_sig a)).

Definition mat_assignment_dimension {P} (prog : program P) facts
    (values : assignment P (relation prog facts)) : nat :=
  1 + audit_trie_nodes values +
    fold_right (fun entry n =>  mat_relation_dimension prog facts (snd entry) + n)
      0 (Map.elements values).

Definition mat_constraint_dimension {P} (prog : program P) (c : rconstraint P) : nat :=
  match c with
  | FromRule i p =>  1 + i + Pos.size_nat (encode (penc prog) p)
  | FromFact p =>  1 + Pos.size_nat (encode (penc prog) p)
  end.

Definition mat_queue_dimension {P} (prog : program P) (queue : PQueue.t (rconstraint P)) : nat :=
  let heap := PQueue.pending queue in
  1 + PQueue.pending_count queue + PQueue.live_count queue +
    length heap + length (PQueue.entries heap) + audit_trie_nodes (PQueue.live queue) +
    audit_queue_input_width (rconstraint_encoding (penc prog)) heap (PQueue.live queue) [] [].

Definition mat_engine_call_dimension {P} (prog : program P) facts
    (call : fx_declared_call P (rconstraint P) (relation prog facts)) : nat :=
  match call with
  | FxTarget c _ | FxRhs c _ =>  mat_constraint_dimension prog c
  | FxPriority _ priority =>  1 + Pos.size_nat priority
  | FxWideningPoint _ _ =>  1
  | FxContinuation _ value _ _ =>  mat_relation_dimension prog facts value
  | FxLeb a b _ =>  1 + mat_relation_dimension prog facts a + mat_relation_dimension prog facts b
  | FxJoin a b out | FxWiden a b out =>
    1 + mat_relation_dimension prog facts a + mat_relation_dimension prog facts b +
      mat_relation_dimension prog facts out
  | FxGet _ code before raw _ =>
    1 + Pos.size_nat code + mat_assignment_dimension prog facts before +
      match raw with None =>  0 | Some a =>  mat_relation_dimension prog facts a end
  | FxSet _ code value before after _ =>
    1 + Pos.size_nat code + mat_relation_dimension prog facts value +
      mat_assignment_dimension prog facts before + mat_assignment_dimension prog facts after
  | FxReaders _ code before raw _ =>
    1 + Pos.size_nat code + audit_trie_nodes before +
      match raw with None =>  0 | Some cs =>  length cs end
  | FxPush priority c before after _ =>
    1 + Pos.size_nat priority + mat_constraint_dimension prog c +
      mat_queue_dimension prog before + mat_queue_dimension prog after
  | FxPop before result _ =>  mat_queue_dimension prog before +
      match result with None =>  1 | Some (_, c, after) =>
        1 + mat_constraint_dimension prog c + mat_queue_dimension prog after end
  end.

Definition mat_engine_trace_dimension {P} (prog : program P) facts
    (events : audit_trace (fx_declared_call P (rconstraint P) (relation prog facts))) : nat :=
  fold_right (fun event n =>  Nat.max n (match event with
    | AuditCall call =>  mat_engine_call_dimension prog facts call
    | AuditArithmetic _ operands =>  fold_right (fun value m =>  Nat.max (N.size_nat value) m) 1
      operands
    | _ =>  1
    end)) 1 events.

Definition mat_rpo_dimension {P} (run : fx_rpo_result P (rconstraint P) mat_frame) : nat :=
  1 + length (fx_rpo_reverse_input run) + length (fx_rpo_reverse_output run) +
    audit_trie_nodes (fx_rpo_positions run) + audit_trie_nodes (fx_rpo_heads run) +
    fold_right (fun entry n =>  Nat.max (Pos.size_nat (snd entry)) n) 1
      (Map.elements (fx_rpo_positions run)) + mat_width (mat_rpo_callback_frames run).

(** This mathematical input budget uses the actual finite-powerset height, without executing it. *)
Definition mat_naive_level_input_steps {P} (prog : program P) facts (st : stratification P) k
    : nat :=
  fx_total_join_step_bound (relation_lattice prog facts)
    (base_height (finite_powerset_height tuple_encoding (herbrand prog facts)
      (herbrand_nodup prog facts)))
    (stratum_static prog facts st (fun _ =>  FinSet.empty) k).

Fixpoint mat_naive_levels_input_steps {P} (prog : program P) facts (st : stratification P)
    (n : nat) : nat :=
  match n with
  | O =>  1
  | S k =>  1 + mat_naive_levels_input_steps prog facts st k +
      mat_naive_level_input_steps prog facts st k
  end.

Definition mat_naive_program_input_steps {P} (prog : program P) facts : nat :=
  match stratify prog with
  | None =>  1
  | Some st =>  mat_naive_levels_input_steps prog facts st (count st)
  end.

(** The whole budget uses input syntax, an input loop bound and actual operand dimensions. *)
Definition mat_naive_whole_budget {P} (prog : program P) facts (operand_max : nat) : nat :=
  1000000000000000 * S (mat_input_dimension prog facts) *
    S (mat_naive_program_input_steps prog facts) * Nat.pow (S operand_max) 32.
```

## Galois.Rules.RulesAuditMaterializeNaiveQuery

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveQuery.v`.

```rocq
(** * Literal generated RHS and ask_all continuation bodies
    Capture witnesses describe only the generated finite closure family, without function
      extensionality.
    Builds on: MatNaiveCallbacks and the native proof-carrying relation/query types. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Rules Require Import RulesAuditMaterializeNaiveBodies.
Import ListNotations.
Section GeneratedQueries.
Context {P:Type}(prog:program P) (facts:list(ground_atom P)) (st:mat_level_context P)
 (lower:database P) (k:nat) (cached:FinSet.t P*FinSet.t positive).
Local Notation A := (relation prog facts).
Record mat_rule_finish_context : Type := MatRuleFinishContext {
 mat_finish_rule : rule P;
 mat_finish_head : P;
 mat_finish_dependencies : list P
}.
Definition mat_native_finish(ctx:mat_rule_finish_context) (values:list A) : Query.t P A :=
 Query.Ret(restrict prog facts(mat_finish_head ctx)
 (fire_rule prog facts(mat_finish_rule ctx)
 (stratum_env prog facts(mat_native_levels st) (rel_of prog lower)k
 (fill_values(penc prog) (mat_finish_dependencies ctx)values)))).
Definition mat_rule_finish_source(ctx:mat_rule_finish_context) (values:list A) : mat_run(Query.t P
  A) :=
 reads<-mat_fill_values(penc prog) (mat_finish_dependencies ctx)values;;
 fired<-mat_naive_firing prog cached(mat_finish_rule ctx)
 (mat_generated_env prog facts st(mat_rel prog lower)k reads);;
 clamped<-mat_clamp prog cached(mat_finish_head ctx)fired;;
 mat_return(mat_native_finish ctx values).

(** Each constructor is one literal captured closure body from ask_all. *)
Inductive mat_finish_capture : (list A->Query.t P A)->Type :=
 | MatFinishBase : forall ctx, mat_finish_capture(mat_native_finish ctx)
 | MatFinishCons : forall f, mat_finish_capture f->forall value:A,
   mat_finish_capture(fun values=> f(value::values)).
Arguments MatFinishCons {f} _ _.
Fixpoint mat_finish_apply {f}(capture:mat_finish_capture f) (values:list A) : mat_run(Query.t P A)
  :=
 match capture with
 | MatFinishBase ctx=> mat_rule_finish_source ctx values
 | MatFinishCons previous value=> mat_mark 130(mat_finish_apply previous(value::values))
 end.
Definition mat_ask_all_source {f}(capture:mat_finish_capture f) (pending:list P) : mat_run(Query.t
  P A) :=
 mat_mark 131(match pending with []=> mat_finish_apply capture [] | _=> mat_return(ask_all pending
   f) end).
Fixpoint mat_finish_depth {f}(capture:mat_finish_capture f) : nat :=match capture with
 | MatFinishBase _=> 0 | MatFinishCons previous _=> S(mat_finish_depth previous) end.
Fixpoint mat_finish_origin {f}(capture:mat_finish_capture f) : mat_rule_finish_context :=match
  capture with
 | MatFinishBase ctx=> ctx | MatFinishCons previous _=> mat_finish_origin previous end.
Definition mat_finish_origin_valid (ri:Map.t nat(rule P)){f}(capture:mat_finish_capture f) : Prop :=
 let origin:=mat_finish_origin capture in
 (exists i, Map.get nat_encoding i ri=Some(mat_finish_rule origin)) /\
 mat_finish_dependencies origin=fst(mat_dependencies prog st k(mat_finish_rule origin)).
Inductive mat_generated_continuation_source (ri:Map.t nat(rule P)) : (A->Query.t P A)->A->Query.t P
  A->list mat_frame->Prop :=
 | MatGeneratedContinuation : forall f(capture:mat_finish_capture f)pending value output events,
   mat_finish_origin_valid ri capture->
   (mat_finish_depth capture+S(length pending)=length(mat_finish_dependencies(mat_finish_origin
     capture)))%nat->
   mat_ask_all_source(MatFinishCons capture value)pending=(output, events)->
   mat_generated_continuation_source ri(fun a=> ask_all pending(fun values=> f(a::values)))value
     output events.
Definition mat_rhs_source(ri:Map.t nat(rule P)) (fi:database P) (c:rconstraint P) : mat_run(Query.t
  P A) :=
 mat_mark 132(match c with
 | FromRule i head=> found<-mat_get_encoded mat_nat_encoder i ri;;
   match found with None=> mat_return(Query.Ret(bot(relation_lattice prog facts)))
   | Some r=> dependencies<-mat_dependencies prog st k r;;
     let ctx:=MatRuleFinishContext r head dependencies in mat_ask_all_source(MatFinishBase
       ctx)dependencies end
 | FromFact p=> set<-mat_rel prog fi p;; clamped<-mat_clamp prog cached p set;;
   mat_return(Query.Ret(restrict prog facts p set)) end).
Definition mat_rhs_source_erases_statement : Prop := forall ri fi c,
 fst(mat_rhs_source ri fi c)=stratum_rhs prog facts(mat_native_levels st) (rel_of prog lower)k ri
   fi c.
Definition mat_finish_apply_erases_statement : Prop := forall f(capture:mat_finish_capture f)values,
 fst(mat_finish_apply capture values)=f values.
Definition mat_generated_continuation_erases_statement : Prop := forall ri native value result
  events,
 mat_generated_continuation_source ri native value result events->result=native value.
Definition mat_generated_continuation_total_statement : Prop := forall ri
  f(capture:mat_finish_capture f)pending value,
 mat_finish_origin_valid ri capture->
 (mat_finish_depth capture+S(length pending)=length(mat_finish_dependencies(mat_finish_origin
   capture)))%nat->
 exists output events, mat_generated_continuation_source ri(fun a=> ask_all pending(fun values=>
   f(a::values)))value output events.
End GeneratedQueries.
```

## Galois.Rules.RulesAuditMaterializeNaiveTotal

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveTotal.v`.

```rocq
(** * Whole naive materialization source execution

    Prepared caches feed the canonical RPO scheduler and the distinct total-solver index build.
    For example, storing a stratum result performs the actual assignment lookup for each target.
    Builds on: concrete materialization callbacks, query provenance and canonical FX total runs. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditTotal
  FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesSolve RulesModel
  RulesAuditMaterializePrelude RulesAuditMaterializeAdapters RulesAuditMaterializeJobs
  RulesAuditMaterializeStratify RulesAuditMaterializeDeltaTotal RulesAuditMaterializeNaiveBodies
  RulesAuditMaterializeSystem RulesAuditMaterializeNaiveCallbacks RulesAuditMaterializeTrace
  RulesAuditMaterializeQueryTrace RulesAuditMaterializeNaiveDimensions
  RulesAuditMaterializeReceipts.
Import List.ListNotations.

(** Facts are indexed by the native tail-first atom fold once per prepared-program invocation. *)
Definition mat_facts_by_pred_source {P} (prog : program P) facts :=
  mat_atom_fold prog facts Map.empty.

(** Store each real lookup result from the final assignment, including absent-key bottom. *)
Definition mat_store_total_values {P} (prog : program P) facts (targets : list P)
    (values : assignment P (relation prog facts)) (db : database P) : mat_run (database P) :=
  mat_foldr (fun p before =>
    found <- mat_get (penc prog) p values;;
    let value := match found with Some a =>  proj1_sig a | None =>  FinSet.empty end in
    mat_set (penc prog) p value before) targets db.

(** The source storage body includes the same missing-key behavior as solve_total's lookup. *)
Definition mat_store_total_values_erases_statement : Prop := forall P (prog : program P)
    facts targets values db,
  fst (mat_store_total_values prog facts targets values db) =
    store_relations prog facts targets (lookup (penc prog) (relation_lattice prog facts) values) db.

(** Prepared facts use exactly the native facts_by_pred map. *)
Definition mat_facts_by_pred_source_erases_statement : Prop := forall P (prog : program P) facts,
  fst (mat_facts_by_pred_source prog facts) = facts_by_pred prog facts.

(** Cached universe sets are the fixed program/fact sets, without a client law. *)
Definition mat_setup_cached_erases_statement : Prop := forall P (prog : program P) facts,
  fst (mat_setup_cached prog facts) = (preds prog facts, constants prog facts).

Inductive mat_naive_event {P} (prog : program P) (facts : list (ground_atom P)) : Type :=
  | MatNaiveFrame (frame : mat_frame)
  | MatNaiveScheduler (st : mat_level_context P) (lower : database P) (k : nat)
      (ri : Map.t nat (rule P)) (run : fx_rpo_result P (rconstraint P) mat_frame)
  | MatNaiveEngine (st : mat_level_context P) (lower : database P) (k : nat)
      (ri : Map.t nat (rule P))
      (index_events : list (fx_index_nested_event P (rconstraint P) mat_frame))
      (init_events engine_events : audit_trace (fx_declared_call P (rconstraint P)
        (relation prog facts)))
      (init_bodies engine_bodies : list (list (list (mat_naive_body_event P)))).

Arguments MatNaiveFrame {P prog facts} _.
Arguments MatNaiveScheduler {P prog facts} _ _ _ _ _.
Arguments MatNaiveEngine {P prog facts} _ _ _ _ _ _ _ _ _.

Definition mat_naive_event_work {P prog facts} (event : @mat_naive_event P prog facts) : nat :=
  match event with
  | MatNaiveFrame frame =>  mat_frame_work frame
  | MatNaiveScheduler st _ k ri run =>
    fx_rpo_scheduler_work (mat_index_callback_budget prog st k ri) run
  | MatNaiveEngine st _ k ri index_events init_events engine_events init_bodies engine_bodies =>
    fx_index_adapter_work (mat_index_callback_budget prog st k ri) index_events +
      fx_declared_model_work (rconstraint_encoding (penc prog)) init_events +
      fx_declared_model_work (rconstraint_encoding (penc prog)) engine_events +
      fx_declared_body_work mat_naive_body_weight init_bodies +
      fx_declared_body_work mat_naive_body_weight engine_bodies
  end.

Definition mat_naive_event_frames {P prog facts} (event : @mat_naive_event P prog facts)
    : list mat_frame :=
  match event with
  | MatNaiveFrame frame =>  [frame]
  | MatNaiveScheduler _ _ _ _ run =>  mat_rpo_callback_frames run
  | MatNaiveEngine _ _ _ _ index_events _ _ init_bodies engine_bodies =>
    flat_map mat_index_callback_frames index_events ++
      mat_naive_bodies_callback_frames init_bodies ++ mat_naive_bodies_callback_frames engine_bodies
  end.

Definition mat_naive_event_dimension {P prog facts} (event : @mat_naive_event P prog facts)
    : nat :=
  match event with
  | MatNaiveFrame frame =>  mat_width [frame]
  | MatNaiveScheduler st lower k ri run =>
    1 + mat_db_size lower + mat_index_capture_dimension prog st k ri + mat_rpo_dimension run
  | MatNaiveEngine st lower k ri _ init_events engine_events init_bodies engine_bodies =>
    1 + mat_db_size lower + mat_index_capture_dimension prog st k ri +
      mat_engine_trace_dimension prog facts init_events +
      mat_engine_trace_dimension prog facts engine_events +
      mat_width (mat_naive_bodies_callback_frames init_bodies) +
      mat_width (mat_naive_bodies_callback_frames engine_bodies)
  end.

Definition mat_naive_work {P prog facts} (events : list (@mat_naive_event P prog facts)) : nat :=
  fold_right (fun event n =>  mat_naive_event_work event + n) 0 events.

Definition mat_naive_operand_max {P prog facts} (events : list (@mat_naive_event P prog facts))
    : nat := fold_right (fun event n =>  Nat.max (mat_naive_event_dimension event) n) 1 events.

Definition mat_naive_callback_frames {P prog facts} (events : list (@mat_naive_event P prog facts))
    : list mat_frame := flat_map mat_naive_event_frames events.

Inductive mat_naive_level_run {P} (prog : program P) facts (st : mat_level_context P)
    (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
    (lower : database P) (k : nat) : database P -> list (@mat_naive_event P prog facts) -> Prop :=
  | MatNaiveLevelRun : forall constraints preparation schedule values index_events init_events
      engine_events init_bodies engine_bodies targets target_events final store_events,
      mat_constraints prog facts st k = (constraints, preparation) ->
      schedule = mat_rpo_source prog facts st lower k ri ->
      fx_total_callbacks_run (penc prog) (rconstraint_encoding (penc prog))
        (relation_lattice prog facts)
        (rpo_scheduler (penc prog) (mat_compiled_system prog facts st lower k)
          (mat_compiled_static prog facts st lower k)) Joining
        (mat_compiled_system prog facts st lower k) (mat_index_callbacks prog st k ri)
        values index_events init_events engine_events ->
      mat_naive_trace_source prog facts st lower k cached ri fi schedule
        None init_events init_bodies None ->
      mat_naive_trace_source prog facts st lower k cached ri fi schedule
        None engine_events engine_bodies None ->
      mat_generated_targets prog facts st k = (targets, target_events) ->
      mat_store_total_values prog facts targets values lower = (final, store_events) ->
      mat_naive_level_run prog facts st cached ri fi lower k final
        (map MatNaiveFrame preparation ++ [MatNaiveScheduler st lower k ri schedule;
          MatNaiveEngine st lower k ri index_events init_events engine_events init_bodies
            engine_bodies] ++ map MatNaiveFrame (target_events ++ store_events)).

Inductive mat_naive_levels_run {P} (prog : program P) facts (st : mat_level_context P)
    (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
    : nat -> database P -> list (@mat_naive_event P prog facts) -> Prop :=
  | MatNaiveLevelsZero :
      mat_naive_levels_run prog facts st cached ri fi 0 Map.empty [MatNaiveFrame (MatBlock 171)]
  | MatNaiveLevelsNext : forall k lower before final events,
      mat_naive_levels_run prog facts st cached ri fi k lower before ->
      mat_naive_level_run prog facts st cached ri fi lower k final events ->
      mat_naive_levels_run prog facts st cached ri fi (S k) final
        (MatNaiveFrame (MatBlock 172) :: before ++ events).

(** Program preparation constructs each cached set, rule index and fact index exactly once. *)
Inductive mat_naive_program_run {P} (prog : program P) facts :
    option (database P) -> list (@mat_naive_event P prog facts) -> Prop :=
  | MatNaiveProgramRejected : forall setup,
      mat_stratify prog = (None, setup) ->
      mat_naive_program_run prog facts None (map MatNaiveFrame setup)
  | MatNaiveProgramAccepted : forall st setup cached cached_events ri rule_events fi fact_events
      output events,
      mat_stratify prog = (Some st, setup) ->
      mat_setup_cached prog facts = (cached, cached_events) ->
      mat_rule_index 0 (rules prog) = (ri, rule_events) ->
      mat_facts_by_pred_source prog facts = (fi, fact_events) ->
      mat_naive_levels_run prog facts st cached ri fi (count (mat_native_levels st)) output events
 ->
      mat_naive_program_run prog facts (Some output)
        (map MatNaiveFrame (setup ++ cached_events ++ [MatBlock 170] ++ rule_events ++ fact_events)
          ++ events).

(** Every program has a complete execution of these fixed source equations. *)
Definition mat_naive_program_realization_statement : Prop := forall P (prog : program P) facts,
  exists output events, mat_naive_program_run prog facts output events.

(** Whole erasure preserves the existing public naive solver result on all inputs. *)
Definition mat_naive_program_erases_statement : Prop := forall P (prog : program P) facts output
  events,
  mat_naive_program_run prog facts output events -> output = solve_program prog facts.

(** The fixed source trace has the input-loop and actual-operand bound without a width premise. *)
Definition mat_naive_program_source_bound_statement : Prop :=
  forall P (prog : program P) facts output events,
  mat_naive_program_run prog facts output events ->
  mat_naive_work events <= mat_naive_whole_budget prog facts (mat_naive_operand_max events).

(** Real predicate callback bodies are attached to the actual nested calls in the same run. *)
Definition mat_naive_program_callback_receipts_statement : Prop :=
  forall P (prog : program P) facts B (source : mat_predicate_callback_source prog B)
    encode_budget arity_budget output events,
  mat_predicate_callback_receipts_statement prog B source ->
  mat_naive_program_run prog facts output events ->
  exists receipts, mat_external_trace_receipts prog B source encode_budget arity_budget
    (mat_naive_callback_frames events) receipts.

(** Full source work adds actual callback bodies and only their per-input allowances. *)
Definition rules_naive_materialization_full_source_statement : Prop :=
  forall P (prog : program P) facts B (source : mat_predicate_callback_source prog B)
    encode_budget arity_budget,
  mat_predicate_callback_receipts_statement prog B source ->
  mat_predicate_callback_input_bounds_statement prog B source encode_budget arity_budget ->
  exists output events receipts,
    mat_naive_program_run prog facts output events /\ output = solve_program prog facts /\
    mat_external_trace_receipts prog B source encode_budget arity_budget
      (mat_naive_callback_frames events) receipts /\
    mat_naive_work events + mat_external_body_work prog B source receipts <=
      mat_naive_whole_budget prog facts (mat_naive_operand_max events) +
        mat_external_trace_allowance B receipts.

(** The same concrete model retains the existing least-model consumer conclusion. *)
Definition rules_naive_materialization_consumer_statement : Prop :=
  forall P (prog : program P) facts db events,
  program_wf prog facts -> mat_naive_program_run prog facts (Some db) events ->
  represents (rel_of prog db) (least_model prog facts).
```

## Galois.Rules.RulesAuditMaterializePlans

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializePlans.v`.

```rocq
(** * Literal retained-plan initialization, reset and extension
    All generic callback parameters are source-level arguments; whole callers supply fixed captured
      bodies.
    Builds on: MatPrelude and the actual delta cache types. *)
From Stdlib Require Import List NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTable.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditFinSet.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Rules Require Import RulesAuditRelations.
From Galois.Rules Require Import RulesAuditNestedPrepare.
From Galois.Rules Require Import RulesAuditNestedProbe.
From Galois.Rules Require Import RulesAuditMultiwayPrepare.
From Galois.Rules Require Import RulesAuditMultiwayProbe.
From Galois.Rules Require Import RulesAuditTerminal.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Rules Require Import RulesAuditIndex.
Import ListNotations.
Fixpoint mat_nested_rows {Q} (ps:list(atom Q)) bound (rows:Q->mat_run(list tuple)) :
  mat_run(delta_nested_cache Q) := mat_mark 30 (
 match ps with []=> mat_return [] | a::rest=> rs<-rows(pred a);;  index<-mat_build_index_full
   bound(args a)rs;;
 search<-mat_return(NestedSearch bound(args a)index);;  node<-mat_return(a, search);;
 next<-mat_bound_add bound a;;  tail<-mat_nested_rows rest next rows;;  mat_return(node::tail) end).
Definition mat_nested_prepare {Q} ps bound (env:Q->mat_run(FinSet.t tuple)) :=
 @mat_nested_rows Q ps bound (fun p=> s<-env p;;  mat_elements s).
Definition mat_nested_rebuild {Q} (env:Q->mat_run(FinSet.t tuple)) (cache:delta_nested_cache Q) :=
 mat_map(fun node=> let '(a, search):=node in s<-env(pred a);;  rows<-mat_elements s;;
 index<-mat_build_index_full(nested_bound search) (nested_terms search)rows;;
 mat_return(NestedSearch(nested_bound search) (nested_terms search)index)) cache.
Definition mat_nested_update {Q} (reset:Q->mat_run bool) (rows:Q->mat_run(list tuple))
  (cache:delta_nested_cache Q) :=
 mat_map(fun node=> let '(a, search):=node in clear<-reset(pred a);;
 initial<-mat_return(if clear then Map.empty else nested_index search);;  batch<-rows(pred a);;
 index<-mat_foldr(mat_index_add_full(nested_bound search) (nested_terms search)) batch initial;;
 mat_return(a, NestedSearch(nested_bound search) (nested_terms search)index)) cache.
Definition mat_variable_domains {Q} v bound (ps:list(atom Q)) (rows:Q->mat_run(list tuple)) :=
 selected<-mat_atoms_with v ps;;  mat_map(fun a=> batch<-rows(pred a);;
 index<-mat_build_variable_full bound(args a)v batch;; mat_return(a, VariableSearch(args a)index))
   selected.
Fixpoint mat_multiway_rows {Q} (vs:list nat) bound (ps:list(atom Q)) (rows:Q->mat_run(list tuple))
  : mat_run(list(delta_variable_cache Q)) := mat_mark 31 (
 match vs with []=> mat_return [] | v::rest=> domains<-mat_variable_domains v bound ps rows;;
 layer<-mat_return(DeltaVariableCache v bound domains);;  next<-mat_nat_add v bound;;
 tail<-mat_multiway_rows rest next ps rows;;  mat_return(layer::tail) end).
Definition mat_multiway_prepare {Q} vs bound ps (env:Q->mat_run(FinSet.t tuple)) :=
 @mat_multiway_rows Q vs bound ps (fun p=> s<-env p;;  mat_elements s).
Definition mat_variable_erase {Q} (layer:delta_variable_cache Q) :=
 domains<-mat_map(fun node=> mat_return(snd node)) (delta_domains layer);;
 mat_return(MultiwaySearch(delta_variable layer) (delta_bound layer)domains).
Definition mat_variable_rebuild {Q} (env:Q->mat_run(FinSet.t tuple)) (layer:delta_variable_cache Q)
  :=
 domains<-mat_map(fun node=> let '(a, search):=node in s<-env(pred a);;  rows<-mat_elements s;;
 index<-mat_build_variable_full(delta_bound layer) (variable_terms search) (delta_variable
   layer)rows;;
 mat_return(VariableSearch(variable_terms search)index)) (delta_domains layer);;
 mat_return(MultiwaySearch(delta_variable layer) (delta_bound layer)domains).
Definition mat_variable_update {Q} (reset:Q->mat_run bool) (rows:Q->mat_run(list tuple))
  (layer:delta_variable_cache Q) :=
 domains<-mat_map(fun node=> let '(a, search):=node in clear<-reset(pred a);;
 initial<-mat_return(if clear then Table.empty else variable_table search);;  batch<-rows(pred a);;
 index<-mat_foldr(mat_variable_add_full(delta_bound layer) (variable_terms search) (delta_variable
   layer))batch initial;;
 mat_return(a, VariableSearch(variable_terms search)index)) (delta_domains layer);;
 mat_return(DeltaVariableCache(delta_variable layer) (delta_bound layer)domains).
Definition mat_plan_rows {Q} strategy (ps:list(atom Q)) rows : mat_run(delta_join_plan Q) :=
  mat_mark 32 (
 match strategy with
 | IndexedNested=> cache<-mat_nested_rows ps FinSet.empty rows;;  mat_return(DeltaNested cache)
 | IndexedMultiway=> vs<-mat_join_variables ps;;  cache<-mat_multiway_rows vs FinSet.empty ps
   rows;;  mat_return(DeltaMultiway cache) end).
Definition mat_plan_prepare {Q} strategy ps (env:Q->mat_run(FinSet.t tuple)) :=
 @mat_plan_rows Q strategy ps(fun p=> s<-env p;;  mat_elements s).
Definition mat_plan_update {Q} reset rows (plan:delta_join_plan Q) := mat_mark 33 (
 match plan with DeltaNested cache=> out<-mat_nested_update reset rows cache;;
   mat_return(DeltaNested out)
 | DeltaMultiway cache=> out<-mat_map(mat_variable_update reset rows)cache;;
   mat_return(DeltaMultiway out) end).
Definition mat_terminal_atom {Q} (env:Q->mat_run(FinSet.t tuple)) b (a:atom Q) :=
 row<-mat_instantiate b(args a);;  s<-env(pred a);;  mat_tuple_mem row s.
Definition mat_positive {Q} atoms (env:Q->mat_run(FinSet.t tuple)) b := mat_all(mat_terminal_atom
  env b)atoms.
Definition mat_negative {Q} (r:rule Q) (env:Q->mat_run(FinSet.t tuple)) b :=
 mat_all(fun lit=> match lit with LPos _=> mat_return true | LNeg a=> found<-mat_terminal_atom env
   b a;;  mat_return(negb found) end) (body r).
Definition mat_plan_bindings {Q} (ps:list(atom Q)) (env:Q->mat_run(FinSet.t tuple))
  (plan:delta_join_plan Q) := mat_mark 34 (
 match plan with
 | DeltaNested cache=> searches<-mat_map(fun node=> mat_return(snd node))cache;;
 mat_lift 35 (@length binding) rules_nested_probe_work(rules_run_nested_counted searches[Map.empty])
 | DeltaMultiway cache=> searches<-mat_map mat_variable_erase cache;;
 bindings<-mat_lift 36 (@length binding) rules_multi_probe_work(rules_run_multiway_counted
   searches[Map.empty]);;
 mat_filter(mat_positive ps env)bindings end).
Fixpoint mat_fill_snapshot {Q}(enc:Q->mat_run positive) (keys:list Q) (values:list(list tuple)) :
  mat_run(Map.t Q(list tuple)) := mat_mark 37(
 match keys, values with p::ps, rows::rest=> before<-mat_fill_snapshot enc ps rest;;
   mat_set_encoded enc p rows before
 | _, _=> mat_return Map.empty end).
Definition mat_snapshot_encoded {Q} (enc:Q->mat_run positive) (atoms:list(atom Q))
  (env:Q->mat_run(FinSet.t tuple)) :=
 predicates<-mat_map(fun a=> mat_return(pred a))atoms;;
 distinct<-mat_predicate_set_encoded enc predicates;;  keys<-mat_elements distinct;;
 sets<-mat_map(fun p=> s<-env p;;  mat_elements s)keys;;
 mat_fill_snapshot enc keys sets.
Definition mat_snapshot {Q}(E:encoding Q) := @mat_snapshot_encoded Q(mat_encode E).
Definition mat_snapshot_rows {Q} (E:encoding Q) (snapshot:Map.t Q(list tuple)) q :=
 found<-mat_get E q snapshot;;  mat_return(match found with Some rows=> rows | None=> [] end).
Definition mat_snapshot_rows_encoded {Q}(enc:Q->mat_run positive) (snapshot:Map.t Q(list tuple))q :=
 found<-mat_get_encoded enc q snapshot;; mat_return(match found with Some rows=> rows | None=> []
   end).
Definition mat_plan_rows_erases_statement : Prop := forall Q strategy (ps:list(atom Q)) rows,
 fst(mat_plan_rows strategy ps (fun q=> mat_return(rows q)))=delta_plan_rows strategy ps rows.
Definition mat_plan_update_erases_statement : Prop := forall Q reset rows (plan:delta_join_plan Q),
 fst(mat_plan_update(fun q=> mat_return(reset q)) (fun q=> mat_return(rows
   q))plan)=delta_update_plan reset rows plan.
Definition mat_plan_bindings_erases_statement : Prop := forall Q ps env (plan:delta_join_plan Q),
 fst(mat_plan_bindings ps(fun q=> mat_return(env q))plan)=delta_plan_bindings ps env plan.
```

## Galois.Rules.RulesAuditMaterializePowerset

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializePowerset.v`.

```rocq
(** * Literal finite-powerset callback bodies
    Inclusion follows only left paths and preserves every native conditional short circuit.
    Builds on: the native finite relation lattice and MatPrelude's complete union model. *)
From Stdlib Require Import List Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Rules Require Import RulesSyntax RulesCompile.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Collections Require Import CollectionsAuditElements.
Definition mat_subset_root {K}(right:Trie.t(K*unit)) := mat_mark 140(mat_return(match Trie.value
  right with Some _=> true | None=> false end)).
Fixpoint mat_subset_ne {K}(left:Trie.ne(K*unit)) (right:Trie.t(K*unit)) : mat_run bool := mat_mark
  141(match left with
 | Trie.N001 r=> mat_subset_ne r(Trie.right right)
 | Trie.N010 _=> mat_subset_root right
 | Trie.N011 _ r=> root<-mat_subset_root right;; if root then mat_subset_ne r(Trie.right right)else
   mat_return false
 | Trie.N100 l=> mat_subset_ne l(Trie.left right)
 | Trie.N101 l r=> first<-mat_subset_ne l(Trie.left right);; if first then mat_subset_ne
   r(Trie.right right)else mat_return false
 | Trie.N110 l _=> first<-mat_subset_ne l(Trie.left right);; if first then mat_subset_root right
   else mat_return false
 | Trie.N111 l _ r=> first<-mat_subset_ne l(Trie.left right);; if first then root<-mat_subset_root
   right;;
   if root then mat_subset_ne r(Trie.right right)else mat_return false else mat_return false end).
Definition mat_subset {K}(a b:FinSet.t K) := mat_mark 142(match a with Trie.Empty=> mat_return true
  | Trie.Nodes n=> mat_subset_ne n b end).
Definition mat_subset_erases_statement : Prop := forall K E(a b:FinSet.t K), fst(mat_subset a
  b)=FinSet.subset E a b.
Definition mat_subset_bound_statement : Prop := forall K(a b:FinSet.t K),
 (mat_work(snd(mat_subset a b))<=10000*(1+audit_trie_nodes a))%nat.
Definition mat_relation_leb {P}(prog:program P)facts(a b:relation prog facts) :=
 ignored<-mat_emit(MatOperand(1+audit_trie_nodes(proj1_sig a)+audit_trie_nodes(proj1_sig b)));;
 mat_subset(proj1_sig a) (proj1_sig b).
Definition mat_relation_bot {P}(prog:program P)facts :=mat_return(bot(relation_lattice prog facts)).
Definition mat_relation_join {P}(prog:program P)facts(a b:relation prog facts) :=
 source<-mat_union(proj1_sig a) (proj1_sig b);; mat_return(join(relation_lattice prog facts)a b).
Definition mat_relation_widen {P}(prog:program P)facts(a b:relation prog facts) :=
 source<-mat_union(proj1_sig a) (proj1_sig b);; mat_return(widen(relation_lattice prog facts)a b).
Definition mat_relation_narrow {P}(prog:program P)facts(a b:relation prog facts) :=mat_return a.
Definition mat_relation_callbacks_erases_statement : Prop := forall P(prog:program P)facts,
 (forall a b, fst(mat_relation_leb prog facts a b)=leb(relation_lattice prog facts)a b) /\
 (forall a b, fst(mat_relation_join prog facts a b)=join(relation_lattice prog facts)a b) /\
 (forall a b, fst(mat_relation_widen prog facts a b)=widen(relation_lattice prog facts)a b).
Definition mat_relation_callbacks_bound_statement : Prop := forall P(prog:program P)facts(a
  b:relation prog facts),
 let nodes:=(1+audit_trie_nodes(proj1_sig a)+audit_trie_nodes(proj1_sig b))%nat in
 (mat_work(snd(mat_relation_leb prog facts a b))<=10000*nodes /\
 mat_work(snd(mat_relation_join prog facts a b))<=10000*nodes /\
 mat_work(snd(mat_relation_widen prog facts a b))<=10000*nodes)%nat.
```

## Galois.Rules.RulesAuditMaterializeQueryTrace

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeQueryTrace.v`.

```rocq
(** * Provenance of generated ask-all continuation calls

    A cursor starts at the actual indexed RHS and advances with that execution's read values.
    For example, a continuation cannot borrow the body of another extensionally equal closure.
    Builds on: RulesAuditMaterializeNaiveQuery and the canonical FX callback trace. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Fixpoint Require Import FixpointQuery FixpointAuditWorklist
  FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeNaiveBodies RulesAuditMaterializeNaiveQuery
  RulesAuditMaterializeNaiveCallbacks.
Import List.ListNotations.

Section QueryProvenance.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : mat_level_context P) (lower : database P) (k : nat)
  (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
  (schedule : fx_rpo_result P (rconstraint P) mat_frame).
Local Notation A := (relation prog facts).

(** Only the generated base and cons captures inhabit this cursor. *)
Inductive mat_query_cursor : Type :=
  | MatQueryCursor : forall f,
      mat_finish_capture prog facts st lower k f -> list P -> mat_query_cursor.

Definition mat_cursor_start (c : rconstraint P) : option mat_query_cursor :=
  match c with
  | FromFact _ =>  None
  | FromRule i head =>
    match fst (mat_get_encoded mat_nat_encoder i ri) with
    | None =>  None
    | Some r =>
      let dependencies := fst (mat_dependencies prog st k r) in
      let origin := MatRuleFinishContext r head dependencies in
      match dependencies with
      | [] =>  None
      | _ :: _ =>  Some (MatQueryCursor _ (MatFinishBase prog facts st lower k origin) dependencies)
      end
    end
  end.

Definition mat_cursor_next {f} (capture : mat_finish_capture prog facts st lower k f)
    (value : A) (pending : list P) : option mat_query_cursor :=
  match pending with
  | [] =>  None
  | _ :: _ =>  Some (MatQueryCursor _ (MatFinishCons prog facts st lower k _ capture value) pending)
  end.

Definition mat_event_changes_cursor
    (event : audit_event (fx_declared_call P (rconstraint P) A)) : bool :=
  match event with
  | AuditCall (FxRhs _ _) | AuditCall (FxContinuation _ _ _ _) =>  true
  | _ =>  false
  end.

(** A receipt sequence follows the same RHS identity and exact successive captured values. *)
Inductive mat_naive_trace_source : option mat_query_cursor ->
    audit_trace (fx_declared_call P (rconstraint P) A) ->
    list (list (list (mat_naive_body_event P))) -> option mat_query_cursor -> Prop :=
  | MatNaiveTraceNil : forall cursor, mat_naive_trace_source cursor [] [] cursor
  | MatNaiveTraceOther : forall cursor event body rest bodies final,
      mat_event_changes_cursor event = false ->
      fx_declared_event_source
        (mat_naive_declared_source prog facts st lower k cached ri fi schedule) event body ->
      mat_naive_trace_source cursor rest bodies final ->
      mat_naive_trace_source cursor (event :: rest) (body :: bodies) final
  | MatNaiveTraceRhs : forall c q body rest bodies final,
      fx_declared_event_source
        (mat_naive_declared_source prog facts st lower k cached ri fi schedule)
        (AuditCall (FxRhs c q)) body ->
      mat_naive_trace_source (mat_cursor_start c) rest bodies final ->
      mat_naive_trace_source None (AuditCall (FxRhs c q) :: rest) (body :: bodies) final
  | MatNaiveTraceContinuation : forall f
      (capture : mat_finish_capture prog facts st lower k f) x pending value native output
      local rest bodies final,
      native = (fun a =>  ask_all pending (fun values =>  f (a :: values))) ->
      mat_ask_all_source prog facts st lower k cached (MatFinishCons prog facts st lower k _
 capture value) pending = (output, local) ->
      fx_declared_event_source
        (mat_naive_declared_source prog facts st lower k cached ri fi schedule)
        (AuditCall (FxContinuation x value native output)) [map MatNaiveLocal local] ->
      mat_naive_trace_source (mat_cursor_next capture value pending) rest bodies final ->
      mat_naive_trace_source (Some (MatQueryCursor _ capture (x :: pending)))
        (AuditCall (FxContinuation x value native output) :: rest)
        ([map MatNaiveLocal local] :: bodies) final.

(** The stronger provenance receipts retain the exact ordinary FX callback-source clauses. *)
Definition mat_naive_trace_source_forgets_statement : Prop := forall initial events bodies final,
  mat_naive_trace_source initial events bodies final ->
  fx_declared_trace_source
    (mat_naive_declared_source prog facts st lower k cached ri fi schedule) events bodies.

End QueryProvenance.
```

## Galois.Rules.RulesAuditMaterializeReceipts

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeReceipts.v`.

```rocq
(** * Genuine predicate callback body receipts

    Only the supplied predicate encoder and arity implementation need external body evidence.
    For example, an encoder receipt retains the actual predicate and returned positive code.
    Builds on: the concrete materialization frames and predicate source interface. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Rules Require Import RulesSyntax RulesAuditMaterializePrelude
  RulesAuditMaterializeDeltaTotal.
Import List.ListNotations.

Definition mat_frame_needs_callback (frame : mat_frame) : bool :=
  match frame with
  | MatEncode _ _ _ _ | MatArity _ _ _ _ | MatLevel _ _ _ _ =>  true
  | _ =>  false
  end.

Section PredicateBodies.
Context {P : Type} (prog : program P) (B : Type) (source : mat_predicate_callback_source prog B)
  (encode_budget arity_budget : P -> nat).

(** A receipt records one actual external body and its per-input allowance. *)
Inductive mat_external_frame_receipt : mat_frame -> list B * nat -> Prop :=
  | MatInternalFrameReceipt : forall frame,
      mat_frame_needs_callback frame = false -> mat_external_frame_receipt frame ([], 0)
  | MatPredicateEncodeReceipt : forall p code body,
      mat_predicate_encoder_body prog B source p code body ->
      mat_external_frame_receipt (MatEncode P (penc prog) p code) (body, encode_budget p)
  | MatPredicateArityReceipt : forall p n body,
      mat_predicate_arity_body prog B source p n body ->
      mat_external_frame_receipt (MatArity P prog p n) (body, arity_budget p).

(** Every receipt belongs to the corresponding occurrence in this same frame sequence. *)
Definition mat_external_trace_receipts (frames : list mat_frame) (receipts : list (list B * nat))
    : Prop := Forall2 mat_external_frame_receipt frames receipts.

Definition mat_external_body_work (receipts : list (list B * nat)) : nat :=
  fold_right (fun receipt n =>
    fold_right (fun frame m =>  mat_predicate_body_frame_weight prog B source frame + m)
      0 (fst receipt) + n) 0 receipts.

Definition mat_external_trace_allowance (receipts : list (list B * nat)) : nat :=
  fold_right (fun receipt n =>  snd receipt + n) 0 receipts.

(** Local source-body bounds compose at the actual calls without an assumed whole-family bound. *)
Definition mat_external_trace_bound_statement : Prop :=
  mat_predicate_callback_input_bounds_statement prog B source encode_budget arity_budget ->
  forall frames receipts, mat_external_trace_receipts frames receipts ->
  mat_external_body_work receipts <= mat_external_trace_allowance receipts.

End PredicateBodies.
```

## Galois.Rules.RulesAuditMaterializeRounds

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeRounds.v`.

```rocq
(** * Complete seed, candidate, advancing and bounded-round bodies
    Prepared closures capture their cached universe once; bounded legacy rounds rebuild each
      variant's universe.
    Builds on: MatJobs, MatDifference and actual delta state fields. *)
From Stdlib Require Import List NArith PArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditDeltaRows.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
From Galois.Rules Require Import RulesAuditMaterializePlans.
From Galois.Rules Require Import RulesAuditMaterializeDifference.
From Galois.Rules Require Import RulesAuditMaterializeJobs.
Import ListNotations.
Definition mat_selected {P} strategy(prog:program P) (r:rule P)env :=
 ps<-mat_positive_atoms(body r);;  snapshot<-mat_snapshot(penc prog)ps env;;
 plan<-mat_plan_rows strategy ps(mat_snapshot_rows(penc prog)snapshot);;  mat_plan_bindings ps env
   plan.
Definition mat_seed_atoms {P} strategy(prog:program P)facts st k lower :=
 cached<-mat_setup_cached prog facts;;
 initial_facts<-mat_filter(fun f=> lev<-mat_level st(fst f);;  same<-mat_nat_test 10 Nat.eqb lev k;;
 allowed<-mat_accept_cached prog cached(fst f) (snd f);;  mat_return(same&&allowed))facts;;
 rs<-mat_filter(fun r=> lev<-mat_level st(pred(head r));;  same<-mat_nat_test 11 Nat.eqb lev k;;
 recursive<-mat_recursive st k r;;  no_recursive<-mat_return(match recursive with []=> true | _=>
   false end);;
 mat_return(same&&no_recursive)) (rules prog);;
 derived<-mat_flatmap(fun r=>
 bindings<-mat_selected strategy prog r(mat_current prog st k lower Map.empty);;
 good<-mat_filter(mat_negative r(mat_current prog st k lower Map.empty))bindings;;
 rows<-mat_map(fun b=> mat_instantiate b(args(head r)))good;;
 valid<-mat_filter(mat_accept_cached prog cached(pred(head r)))rows;;
 set<-mat_of_list(audit_list_encode audit_positive_encode) (audit_list_events_work
   audit_basic_encoding_work)valid;;
 elements<-mat_elements set;;  mat_map(fun row=> mat_return(pred(head r), row))elements)rs;;
 mat_append initial_facts derived.
Definition mat_initial {P} strategy(prog:program P)facts st k lower :=
 atoms<-mat_seed_atoms strategy prog facts st k lower;;  seeds<-mat_ground_set prog atoms;;
 index<-mat_index prog seeds;;  jobs<-mat_prepare_jobs strategy prog st k lower index index;;
 mat_return(DeltaState seeds seeds index index jobs).
Definition mat_advance {P}(prog:program P) (s:delta_state P)batch :=
 index<-mat_index prog batch;;
 snapshot<-mat_lift 70 (fun m=> audit_trie_nodes m)
   rules_delta_rows_snapshot_work(rules_delta_rows_snapshot_counted index);;
 accumulated<-mat_union(delta_accumulated s)batch;;
 atoms<-mat_elements batch;;  accumulated_index<-mat_atom_fold prog atoms(delta_accumulated_index
   s);;
 jobs<-mat_update_jobs prog(mat_snapshot_rows(penc prog)snapshot) (delta_jobs s);;
 mat_return(DeltaState accumulated batch accumulated_index index jobs).
Definition mat_step {P}(prog:program P)facts st k lower(s:delta_state P) :=
 candidates<-mat_candidates prog facts st k lower(delta_accumulated_index s) (delta_frontier_index
   s) (delta_jobs s);;
 batch<-mat_diff candidates(delta_accumulated s);;
 mat_mark 71(if FinSet.is_empty batch then mat_return None else next<-mat_advance prog s batch;;
   mat_return(Some next)).
Definition mat_prepared_step {P}(prog:program P)facts st k lower cached(s:delta_state P) :=
 candidates<-mat_candidates_prepared prog facts st k lower(delta_accumulated_index s)
   (delta_frontier_index s) (delta_jobs s)cached;;
 batch<-mat_diff candidates(delta_accumulated s);;
 mat_mark 72(if FinSet.is_empty batch then mat_return None else next<-mat_advance prog s batch;;
   mat_return(Some next)).
Definition mat_one {P}(prog:program P)facts st k lower(s:delta_state P) :=
 next<-mat_step prog facts st k lower s;;  mat_return(match next with Some out=> out | None=> s
   end).
Fixpoint mat_observe {P}(prog:program P)facts st k lower(fuel:positive) (s:delta_state P) :
  mat_run(delta_state P) := mat_mark 73(
 match fuel with xH=> mat_one prog facts st k lower s
 | xO p=> mid<-mat_observe prog facts st k lower p s;;  mat_observe prog facts st k lower p mid
 | xI p=> mid1<-mat_observe prog facts st k lower p s;;  mid2<-mat_observe prog facts st k lower p
   mid1;;  mat_one prog facts st k lower mid2 end).
Definition mat_bounded_stratum {P} strategy(prog:program P)facts st k lower fuel :=
 initial<-mat_initial strategy prog facts st k lower;; result<-mat_observe prog facts st k lower
   fuel initial;;
 final<-mat_step prog facts st k lower result;;  mat_return(match final with Some _=> None | None=>
   Some result end).
Fixpoint mat_bounded_levels {P} strategy(prog:program P)facts st fuel(n:nat) :
  mat_run(option(database P)) := mat_mark 74(
 match n with O=> mat_return(Some Map.empty) | S k=> previous<-mat_bounded_levels strategy prog
   facts st fuel k;;
 match previous with None=> mat_return None | Some lower=>
 result<-mat_bounded_stratum strategy prog facts st k(mat_rel prog lower)fuel;;
 match result with None=> mat_return None | Some final=> atoms<-mat_elements(delta_accumulated
   final);;
 db<-mat_atom_fold prog atoms lower;;  mat_return(Some db) end end end).
Definition mat_initial_erases_statement : Prop := forall P strategy(prog:program P)facts st k lower,
 fst(mat_initial strategy prog facts (MatExternalLevels st) k(fun p=> mat_return(lower
   p)))=delta_initial strategy prog facts st k lower.
Definition mat_step_erases_statement : Prop := forall P(prog:program P)facts st k lower s,
 fst(mat_step prog facts (MatExternalLevels st) k(fun p=> mat_return(lower p))s)=delta_step prog
   facts st k lower s.
Definition mat_prepared_step_erases_statement : Prop := forall P(prog:program P)facts st k lower s,
 let cached:=fst(mat_setup_cached prog facts) in
 fst(mat_prepared_step prog facts (MatExternalLevels st) k(fun p=> mat_return(lower p))cached
   s)=delta_prepared_step prog facts st k lower s.
Definition mat_bounded_levels_erases_statement : Prop := forall P strategy(prog:program P)facts st
  fuel n,
 fst(mat_bounded_levels strategy prog facts (MatExternalLevels st) fuel n)=delta_bounded_levels
   strategy prog facts st fuel n.
```

## Galois.Rules.RulesAuditMaterializeStratify

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeStratify.v`.

```rocq
(** * Whole stratification source equations
    Done states still execute every remaining binary-fuel call; returned levels retain their actual
      map.
    Builds on: MatPrelude and RulesStratify. *)
From Stdlib Require Import List NArith ZArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditRelations.
From Galois.Rules Require Import RulesAuditMaterializePrelude.
From Galois.Rules Require Import RulesAuditMaterializeAdapters.
From Galois.Rules Require Import RulesAuditJoinSyntax.
Import ListNotations.
Definition mat_rule_edges {P}(r:rule P) := mat_map(fun lit=> mat_return(pred(head r),
  (pred(lit_atom lit), match lit with LPos _=> 0%nat | LNeg _=> 1%nat end))) (body r).
Definition mat_program_edges {P}(prog:program P) := mat_flatmap mat_rule_edges(rules prog).
Definition mat_rule_predicates {P}(r:rule P) := tail<-mat_map(fun lit=> mat_return(pred(lit_atom
  lit))) (body r);; mat_return(pred(head r)::tail).
Definition mat_rule_nodes {P}(prog:program P) := all<-mat_flatmap mat_rule_predicates(rules prog);;
 set<-mat_predicate_set_encoded(mat_encode(penc prog))all;; mat_elements set.
Definition mat_level_at {P} E(m:Map.t P nat)p := found<-mat_get E p m;; mat_return(match found with
  Some n=> n | None=> 0%nat end).
Definition mat_edge_ok {P} E m(e:P*(P*nat)) :=
 source<-mat_level_at E m(fst(snd e));; required<-mat_nat 20 Nat.add source(snd(snd e));;
 target<-mat_level_at E m(fst e);; mat_nat_test 21 Nat.leb required target.
Definition mat_raise_edge {P} E m(e:P*(P*nat)) :=
 target<-mat_level_at E m(fst e);; source<-mat_level_at E m(fst(snd e));;
 required<-mat_nat 22 Nat.add source(snd(snd e));; maximum<-mat_nat 23 Nat.max target required;;
   mat_set E(fst e)maximum m.
Definition mat_stratify_tick {P}(prog:program P) (state:Map.t P nat*bool) := mat_mark 80(
 let '(levels, done):=state in if done then mat_return state else
 edges<-mat_program_edges prog;; ready<-mat_all(mat_edge_ok(penc prog)levels)edges;;
 if ready then mat_return(levels, true) else
 raising<-mat_program_edges prog;; next<-mat_foldl(mat_raise_edge(penc prog))raising levels;;
   mat_return(next, false)).
Fixpoint mat_piter {A}(fuel:positive) (body:A->mat_run A) (state:A) : mat_run A := mat_mark 81(
 match fuel with xH=> body state | xO p=> mid<-mat_piter p body state;; mat_piter p body mid
 | xI p=> mid1<-mat_piter p body state;; mid2<-mat_piter p body mid1;; body mid2 end).
Definition mat_niter {A}(fuel:N) (body:A->mat_run A) (state:A) := mat_mark 82(
 match fuel with N0=> mat_return state | Npos p=> mat_piter p body state end).
Definition mat_stratify {P}(prog:program P) : mat_run(option(mat_level_context P)) :=
 nodes<-mat_rule_nodes prog;; let count:=length nodes in
 ignored<-mat_emit(MatNat 24 count 0);;
 let n:=N.of_nat count in
 ignored<-mat_emit(MatChild 83 (audit_unary_conversion_weight count) (S count));;
 let square:=(n*n)%N in
 ignored<-mat_emit(MatChild 84 (audit_multiply_weight(Z.of_N n) (Z.of_N n)) (S count));;
 let fuel:=N.succ square in
 ignored<-mat_emit(MatChild 85 (audit_binary_weight(Z.of_N square)0) (S count));;
 state<-mat_niter fuel(mat_stratify_tick prog) (Map.empty, false);;
 mat_mark 86(let '(levels, done):=state in if done then
 nodes_again<-mat_rule_nodes prog;; values<-mat_map(mat_level_at(penc prog)levels)nodes_again;;
 maximum<-mat_foldr(fun n m=> mat_nat 25 Nat.max n m)values 0%nat;;
 bound<-mat_nat 26 Nat.add maximum 1%nat;; mat_return(Some(MatCapturedLevels(penc prog)levels
   bound))
 else mat_return None).
Definition mat_stratify_erases_statement : Prop := forall P(prog:program P),
 match fst(mat_stratify prog), stratify prog with
 | None, None=> True | Some context, Some native=> count(mat_native_levels context)=count native /\
 forall p, level(mat_native_levels context)p=level native p | _, _=> False end.
Definition mat_stratify_bound_statement : Prop := forall P(prog:program P),
 let '(_, events):=mat_stratify prog in let width:=S(mat_width events) in
 (mat_work events<=100000000*Nat.pow width 12)%nat.
Definition mat_stratify_total_statement : Prop := forall P(prog:program P), exists out trace,
  mat_stratify prog=(out, trace).
Definition mat_stratify_unique_statement : Prop := forall P(prog:program P)r1 t1 r2 t2,
 mat_stratify prog=(r1, t1)->mat_stratify prog=(r2, t2)->r1=r2 /\ t1=t2.
```

## Galois.Rules.RulesAuditMaterializeSystem

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeSystem.v`.

```rocq
(** * Concrete compiled-system callback instances

    The naive solver supplies fixed bodies to the canonical Fixpoint scheduler owner.
    For example, a missing rule index produces an empty static dependency list.
    Builds on: RulesAuditMaterializeNaiveBodies and FixpointAuditScheduleWrapper. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditSchedule FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeNaiveBodies.
Import List.ListNotations.

Section GeneratedSystem.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : mat_level_context P) (lower : database P) (k : nat) (ri : Map.t nat (rule P)).

Definition mat_compiled_system :=
  stratum_system prog facts (mat_native_levels st) (rel_of prog lower) k.

Definition mat_compiled_static :=
  stratum_static prog facts (mat_native_levels st) (rel_of prog lower) k.

Definition mat_target_source (c : rconstraint P) : mat_run P :=
  mat_return (match c with FromRule _ h =>  h | FromFact p =>  p end).

(** Generated dependencies and encoders use their concrete bodies at each occurrence. *)
Definition mat_index_callbacks : fx_index_external_model P (rconstraint P) mat_frame :=
  FxIndexExternalModel P (rconstraint P) mat_frame (mat_encode (penc prog))
    mat_target_source (fun _ =>  mat_return []) (mat_generated_deps prog st k ri).

(** Each source clause records the actual typed callback result and literal body. *)
Definition mat_naive_index_source : fx_index_external_source P (rconstraint P) mat_frame :=
  {| fxi_encode_source := fun p result body =>  mat_encode (penc prog) p = (result, body);
     fxi_target_source := fun c result body =>  mat_target_source c = (result, body);
     fxi_sides_source := fun _ result body =>  mat_return [] = (result, body);
     fxi_deps_source := fun c result body =>  mat_generated_deps prog st k ri c = (result, body) |}.

(** Captured rule lookup agrees with the compiler's static callbacks. *)
Definition mat_index_callbacks_erases_statement : Prop :=
  ri = index_rules_from 0 (rules prog) ->
  fx_index_external_erases (penc prog) mat_compiled_system mat_compiled_static mat_index_callbacks.

(** Literal callback source equations require no assumed whole-graph or whole-solver law. *)
Definition mat_index_callbacks_source_statement : Prop :=
  fx_dep_source_laws mat_index_callbacks mat_naive_index_source.

End GeneratedSystem.

Definition mat_level_capture_dimension {P} (st : mat_level_context P) : nat :=
  match st with
  | MatExternalLevels _ =>  1
  | MatCapturedLevels _ levels bound =>
    1 + bound + audit_trie_nodes levels +
      fold_right (fun entry n =>  snd entry + n) 0 (Map.elements levels)
  end.

Definition mat_dependency_rule_dimension {P} (prog : program P) st k (r : rule P) : nat :=
  1 + length (body r) + fold_right (fun lit n =>
    let a := lit_atom lit in
    1 + Pos.size_nat (encode (penc prog) (pred a)) +
      level (mat_native_levels st) (pred a) + k + n) 0 (body r).

Definition mat_index_capture_dimension {P} (prog : program P) st k
    (ri : Map.t nat (rule P)) : nat :=
  1 + mat_level_capture_dimension st + audit_trie_nodes ri +
    fold_right (fun entry n =>
      fst entry + mat_dependency_rule_dimension prog st k (snd entry) + n) 0 (Map.elements ri).

(** Per-call bounds use actual callback inputs and captured source data. *)
Definition mat_index_callback_budget {P} (prog : program P) st k (ri : Map.t nat (rule P))
    : fx_index_external_budget P (rconstraint P) mat_frame :=
  {| fxi_body_weight := fun frame =>  S (mat_frame_work frame);
     fxi_encode_bound := fun _ =>  2;
     fxi_target_bound := fun _ =>  101;
     fxi_sides_bound := fun _ =>  101;
     fxi_deps_bound := fun c =>
       let index := match c with FromRule i _ =>  i | FromFact _ =>  0 end in
       1000000 * Nat.pow (1 + index + mat_index_capture_dimension prog st k ri) 12 |}.

(** Bounds for generated callbacks are library obligations, never assumed solver bounds. *)
Definition mat_index_callback_bounded_statement : Prop := forall P (prog : program P) st k ri,
  fx_index_external_bounded (mat_index_callbacks prog st k ri)
    (mat_index_callback_budget prog st k ri).

(** The source instance invokes the sole production scheduler owner. *)
Definition mat_rpo_source {P} (prog : program P) facts st lower k ri :=
  fx_rpo_scheduler_counted (penc prog) (mat_compiled_system prog facts st lower k)
    (mat_compiled_static prog facts st lower k) (mat_index_callbacks prog st k ri).

(** Scheduling retains native observations after the approved GR-DFS reverse refactor. *)
Definition mat_rpo_source_erases_statement : Prop := forall P (prog : program P)
    facts st lower k ri,
  ri = index_rules_from 0 (rules prog) ->
  let result := mat_rpo_source prog facts st lower k ri in
  let native := rpo_scheduler (penc prog) (mat_compiled_system prog facts st lower k)
    (mat_compiled_static prog facts st lower k) in
  forall x,
    fst (audit_rpo_schedule_priority (fx_dep_encoder (mat_index_callbacks prog st k ri))
      (fx_rpo_positions result) x) = priority native x /\
    fst (audit_rpo_schedule_widening (fx_dep_encoder (mat_index_callbacks prog st k ri))
      (fx_rpo_heads result) x) = widening_point native x.
```

## Galois.Rules.RulesAuditMaterializeTrace

Card: AUD-RU-MAT-BASE

Source destination: `theories/Rules/RulesAuditMaterializeTrace.v`.

```rocq
(** * Actual callback occurrences in canonical solver subruns

    These observers select callback bodies from the same index, scheduler and engine captures.
    For example, a scheduler map lookup retains the encoder body for that exact lookup key.
    Builds on: canonical Collections, Graph and Fixpoint source models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointAuditIndex FixpointAuditSchedule
  FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesCompile RulesAuditMaterializePrelude
  RulesAuditMaterializeNaiveCallbacks.
Import List.ListNotations.

Definition mat_set_callback_frames {P} (event : audit_set_event P mat_frame) : list mat_frame :=
  match event with
  | AuditSetAdd _ _ _ _ encoded _ | AuditSetMem _ _ _ _ encoded _ |
    AuditSetRemove _ _ _ _ encoded _ =>  encoded
  | AuditSetFold _ _ =>  []
  end.

Definition mat_index_callback_frames {P}
    (event : fx_index_nested_event P (rconstraint P) mat_frame) : list mat_frame :=
  match event with
  | FxiTarget _ _ body | FxiSides _ _ body | FxiDeps _ _ body =>  body
  | FxiDistinctBuild _ _ body =>  flat_map mat_set_callback_frames body
  | FxiRead _ _ _ _ encoded _ | FxiWrite _ _ _ _ _ encoded _ =>  encoded
  | _ =>  []
  end.

Definition mat_dep_callback_frames {P}
    (event : fx_dep_event P (rconstraint P) mat_frame) : list mat_frame :=
  match event with
  | FxDepIndexEvent nested =>  mat_index_callback_frames nested
  | FxDepEncode _ _ body =>  body
  | _ =>  []
  end.

Definition mat_dep_map_frames {P A}
    (event : audit_map_event P A (fx_dep_event P (rconstraint P) mat_frame)) : list mat_frame :=
  match event with
  | AuditMapGet _ _ _ _ body _ | AuditMapSet _ _ _ _ _ body _ |
    AuditMapRemove _ _ _ _ body _ =>  flat_map mat_dep_callback_frames body
  end.

Definition mat_dep_set_frames {P}
    (event : audit_set_event P (fx_dep_event P (rconstraint P) mat_frame)) : list mat_frame :=
  match event with
  | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
    AuditSetRemove _ _ _ _ body _ =>  flat_map mat_dep_callback_frames body
  | AuditSetFold _ _ =>  []
  end.

Definition mat_prepare_callback_frames {P}
    (event : audit_prepare_source_event P (P * P) (fx_dep_event P (rconstraint P) mat_frame))
    : list mat_frame :=
  match event with
  | PrepareSourceOut _ _ body | PrepareSourceTarget _ _ body =>
    flat_map mat_dep_callback_frames body
  | PrepareSourceMap nested =>  mat_dep_map_frames nested
  | _ =>  []
  end.

Definition mat_dfs_callback_frames {P}
    (event : audit_dfs_nested_event P (P * P)
      (audit_graph_callback_capture P (P * P) (fx_dep_event P (rconstraint P) mat_frame)))
    : list mat_frame :=
  flat_map (fun capture =>  match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body | AuditGraphEncodeCapture _ _ _ _ _ body =>
      flat_map mat_dep_callback_frames body
    end) (snd event).

Definition mat_positions_callback_frames {P}
    (event : audit_rpo_schedule_event P (fx_dep_event P (rconstraint P) mat_frame))
    : list mat_frame :=
  match event with
  | RpoScheduleMap nested =>  mat_dep_map_frames nested
  | RpoScheduleSet nested =>  mat_dep_set_frames nested
  | _ =>  []
  end.

Definition mat_retreat_callback_frames {P}
    (event : audit_rpo_graph_event P (P * P) (fx_dep_event P (rconstraint P) mat_frame))
    : list mat_frame :=
  match event with
  | RpoGraphOut _ _ body | RpoGraphSource _ _ body | RpoGraphTarget _ _ body =>
    flat_map mat_dep_callback_frames body
  | RpoGraphRank nested =>  mat_dep_map_frames nested
  | RpoGraphSet nested =>  mat_dep_set_frames nested
  | _ =>  []
  end.

(** Every selected frame belongs to the one canonical scheduler capture supplied here. *)
Definition mat_rpo_callback_frames {P} (run : fx_rpo_result P (rconstraint P) mat_frame)
    : list mat_frame :=
  flat_map mat_dep_callback_frames (fx_rpo_build_events run) ++
  flat_map mat_prepare_callback_frames (fx_rpo_prepare_events run) ++
  flat_map mat_dfs_callback_frames (fx_rpo_dfs_events run) ++
  flat_map mat_positions_callback_frames (fx_rpo_position_events run) ++
  flat_map mat_retreat_callback_frames (fx_rpo_retreat_events run).

Definition mat_naive_body_callback_frames {P} (event : mat_naive_body_event P) : list mat_frame :=
  match event with
  | MatNaiveLocal local =>  [local]
  | MatNaiveScheduleQuery nested =>  mat_positions_callback_frames nested
  end.

Definition mat_naive_bodies_callback_frames {P}
    (bodies : list (list (list (mat_naive_body_event P)))) : list mat_frame :=
  flat_map mat_naive_body_callback_frames (concat (concat bodies)).
```

### `RulesAuditMaterializeDeltaCorrectness.mat_bounded_levels_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_bounded_levels_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (st : RulesStratify.stratification P)
  (fuel : positive) (n : nat),
@fst (option (RulesSolve.database P)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_bounded_levels P strategy prog facts
     (@RulesAuditMaterializePrelude.MatExternalLevels P st) fuel n) =
@RulesDelta.delta_bounded_levels P strategy prog facts st fuel n.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_bounded_program_bound`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_bounded_program_bound :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (fuel : positive),
let
'(_, events) := @mat_bounded_program P strategy prog facts fuel in
 RulesAuditMaterializePrelude.mat_work events <=
 mat_whole_budget (@mat_input_dimension P prog facts) (Pos.to_nat fuel + 1)
   (RulesAuditMaterializePrelude.mat_width events).
```

### `RulesAuditMaterializeDeltaCorrectness.mat_bounded_program_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_bounded_program_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (fuel : positive),
@fst (option (RulesSolve.database P)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_bounded_program P strategy prog facts fuel) =
@RulesDelta.delta_bounded_program P strategy prog facts fuel.
```

### `RulesAuditMaterializePlansCorrectness.mat_candidates_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_candidates_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesStratify.stratification P) (k : nat)
  (lower : P -> CollectionsFinSet.FinSet.t RulesSyntax.tuple)
  (acc front : RulesSolve.database P) (jobs : list (RulesDelta.delta_job P)),
@fst (CollectionsFinSet.FinSet.t (P * list positive))
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_candidates P prog facts (@RulesAuditMaterializePrelude.MatExternalLevels P st) k
     (fun p : P =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (lower p))
     acc front jobs) =
@RulesDelta.delta_candidates P prog facts st k lower acc front jobs.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_clamp_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_clamp_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (p : P) (input : CollectionsFinSet.FinSet.t RulesSyntax.tuple),
@fst (CollectionsTrie.Trie.t (list positive * unit))
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_clamp P prog
     (@fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
        (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts))
     p input) =
@proj1_sig (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
  (fun s : CollectionsFinSet.FinSet.t RulesSyntax.tuple =>
   @OrderPowerset.within_set RulesSyntax.tuple RulesCompile.tuple_encoding
     (@RulesCompile.herbrand P prog facts) s)
  (@RulesCompile.restrict P prog facts p input).
```

### `RulesAuditMaterializeBodiesCorrectness.mat_classic_join_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_classic_join_erases :
forall (P : Type) (ps : list (RulesSyntax.atom P)) (bound : CollectionsFinSet.FinSet.t nat)
  (env : P -> CollectionsFinSet.FinSet.t RulesSyntax.tuple)
  (bindings : list RulesCompile.binding),
@fst (list RulesCompile.binding) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_classic_join P ps bound
     (fun p : P =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (env p))
     bindings) =
@RulesCompile.join_positive P ps bound env bindings.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_classic_join_source_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_classic_join_source_erases :
forall (P : Type) (ps : list (RulesSyntax.atom P)) (bound : CollectionsFinSet.FinSet.t nat)
  (env : P ->
         RulesAuditMaterializePrelude.mat_run (CollectionsFinSet.FinSet.t RulesSyntax.tuple))
  (bindings : list RulesCompile.binding),
@fst (list RulesCompile.binding) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_classic_join P ps bound env bindings) =
@RulesCompile.join_positive P ps bound
  (fun p : P =>
   @fst (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
     (list RulesAuditMaterializePrelude.mat_frame) (env p))
  bindings.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_constraints_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_constraints_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesStratify.stratification P) (k : nat),
@fst (list (RulesCompile.rconstraint P)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_constraints P prog facts (@RulesAuditMaterializePrelude.MatExternalLevels P st) k) =
@RulesCompile.stratum_constraints P prog facts st k.
```

### `RulesAuditMaterializeFullSourceCorrectness.mat_delta_program_callback_receipts`

Card: AUD-RU-MAT

Source destination: `theories/Rules/RulesAuditMaterializeFullSourceCorrectness.v`.

```rocq
Theorem mat_delta_program_callback_receipts :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (B : Type)
  (source : @mat_predicate_callback_source P prog B) (encode_budget arity_budget : P -> nat)
  (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_predicate_callback_receipts_statement P prog B source ->
@mat_program_run P strategy prog facts output events rounds ->
exists receipts : list (list B * nat),
  @mat_external_trace_receipts P prog B source encode_budget arity_budget events receipts.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_dependencies_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_dependencies_erases :
forall (P : Type) (prog : RulesSyntax.program P) (st : RulesStratify.stratification P)
  (k : nat) (r : RulesSyntax.rule P),
@fst (list P) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_dependencies P prog (@RulesAuditMaterializePrelude.MatExternalLevels P st) k r) =
@RulesCompile.level_dependencies P prog st k r.
```

### `RulesAuditMaterializePlansCorrectness.mat_diff_bound`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_diff_bound :
forall (K : Type) (a b : CollectionsFinSet.FinSet.t K),
RulesAuditMaterializePrelude.mat_work
  (@snd (CollectionsTrie.Trie.t (K * unit)) (list RulesAuditMaterializePrelude.mat_frame)
     (@mat_diff K a b)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))) *
(1 + @CollectionsAuditElements.audit_trie_nodes (K * unit) a +
 @CollectionsAuditElements.audit_trie_nodes (K * unit) b).
```

### `RulesAuditMaterializePlansCorrectness.mat_diff_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_diff_erases :
forall (K : Type) (E : CollectionsEncoding.encoding K) (a b : CollectionsFinSet.FinSet.t K),
@fst (CollectionsTrie.Trie.t (K * unit)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_diff K a b) =
@CollectionsFinSet.FinSet.diff K E a b.
```

### `RulesAuditMaterializeReceiptsCorrectness.mat_external_trace_bound`

Card: AUD-RU-MAT-RECEIPTS

Source destination: `theories/Rules/RulesAuditMaterializeReceiptsCorrectness.v`.

```rocq
Theorem mat_external_trace_bound :
forall (P : Type) (prog : RulesSyntax.program P) (B : Type)
  (source : @mat_predicate_callback_source P prog B) (encode_budget arity_budget : P -> nat),
@mat_predicate_callback_input_bounds_statement P prog B source encode_budget arity_budget ->
forall (frames : list RulesAuditMaterializePrelude.mat_frame) (receipts : list (list B * nat)),
@mat_external_trace_receipts P prog B source encode_budget arity_budget frames receipts ->
@mat_external_body_work P prog B source receipts <= mat_external_trace_allowance B receipts.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_facts_by_pred_source_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_facts_by_pred_source_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P)),
@fst (RulesSolve.database P) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_facts_by_pred_source P prog facts) =
@RulesCompile.facts_by_pred P prog facts.
```

### `RulesAuditMaterializeFxCorrectness.mat_finish_apply_erases`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_finish_apply_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive),
forall
  (f : list (@RulesCompile.relation P prog facts) ->
       FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
  (capture : @mat_finish_capture P prog facts st lower k f)
  (values : list (@RulesCompile.relation P prog facts)),
@fst (FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_finish_apply P prog facts st lower k cached f capture values) =
f values.
```

### `RulesAuditMaterializeFxCorrectness.mat_generated_continuation_erases`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_generated_continuation_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive),
forall (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P))
  (native : @RulesCompile.relation P prog facts ->
            FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
  (value : @RulesCompile.relation P prog facts)
  (result : FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
  (events : list RulesAuditMaterializePrelude.mat_frame),
@mat_generated_continuation_source P prog facts st lower k cached ri native value result events ->
result = native value.
```

### `RulesAuditMaterializeFxCorrectness.mat_generated_continuation_total`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_generated_continuation_total :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive),
forall (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P))
  (f : list (@RulesCompile.relation P prog facts) ->
       FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
  (capture : @mat_finish_capture P prog facts st lower k f) (pending : list P)
  (value : @RulesCompile.relation P prog facts),
@mat_finish_origin_valid P prog facts st lower k ri f capture ->
@mat_finish_depth P prog facts st lower k f capture + S (@length P pending) =
@length P (@mat_finish_dependencies P (@mat_finish_origin P prog facts st lower k f capture)) ->
exists
  (output : FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
(events : list RulesAuditMaterializePrelude.mat_frame),
  @mat_generated_continuation_source P prog facts st lower k cached ri
    (fun a : @RulesCompile.relation P prog facts =>
     @FixpointQuery.ask_all P (@RulesCompile.relation P prog facts) pending
       (fun values : list (@RulesCompile.relation P prog facts) => f (a :: values)))
    value output events.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_generated_env_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_generated_env_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (reads : CollectionsMap.Map.t P (@RulesCompile.relation P prog facts))
  (p : P),
@fst (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_generated_env P prog facts st (@RulesAuditMaterializePrelude.mat_rel P prog lower) k
     reads p) =
@RulesCompile.stratum_env P prog facts (@RulesAuditMaterializePrelude.mat_native_levels P st)
  (@RulesSolve.rel_of P prog lower) k reads p.
```

### `RulesAuditMaterializeFxCorrectness.mat_index_callback_bounded`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_index_callback_bounded :
forall (P : Type) (prog : RulesSyntax.program P)
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)),
@FixpointAuditIndex.fx_index_external_bounded P (RulesCompile.rconstraint P)
  RulesAuditMaterializePrelude.mat_frame (@mat_index_callbacks P prog st k ri)
  (@mat_index_callback_budget P prog st k ri).
```

### `RulesAuditMaterializeFxCorrectness.mat_index_callbacks_erases`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_index_callbacks_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)),
ri = @RulesCompile.index_rules_from P 0 (@RulesSyntax.rules P prog) ->
@FixpointAuditIndex.fx_index_external_erases P (RulesCompile.rconstraint P)
  (@RulesCompile.relation P prog facts) RulesAuditMaterializePrelude.mat_frame
  (@RulesSyntax.penc P prog) (@mat_compiled_system P prog facts st lower k)
  (@mat_compiled_static P prog facts st lower k) (@mat_index_callbacks P prog st k ri).
```

### `RulesAuditMaterializeFxCorrectness.mat_index_callbacks_source`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_index_callbacks_source :
forall (P : Type) (prog : RulesSyntax.program P)
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)),
@FixpointAuditScheduleWrapper.fx_dep_source_laws P (RulesCompile.rconstraint P)
  RulesAuditMaterializePrelude.mat_frame (@mat_index_callbacks P prog st k ri)
  (@mat_naive_index_source P prog st k ri).
```

### `RulesAuditMaterializeFxCorrectness.mat_index_weight_instance`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_index_weight_instance :
forall (P : Type) (prog : RulesSyntax.program P)
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P))
  (event : FixpointAuditIndex.fx_index_nested_event P (RulesCompile.rconstraint P)
             RulesAuditMaterializePrelude.mat_frame),
@mat_index_source_event_work P event =
@FixpointAuditIndex.fxi_event_work P (RulesCompile.rconstraint P)
  RulesAuditMaterializePrelude.mat_frame (@mat_index_callback_budget P prog st k ri) event.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_initial_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_initial_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (st : RulesStratify.stratification P)
  (k : nat) (lower : P -> CollectionsFinSet.FinSet.t RulesSyntax.tuple),
@fst (RulesDelta.delta_state P) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_initial P strategy prog facts (@RulesAuditMaterializePrelude.MatExternalLevels P st) k
     (fun p : P =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (lower p))) =
@RulesDelta.delta_initial P strategy prog facts st k lower.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_levels_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_levels_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (n : nat)
  (db : RulesSolve.database P) (events : list RulesAuditMaterializePrelude.mat_frame)
  (rounds : nat),
@mat_levels_run P strategy prog facts st n db events rounds ->
db =
@RulesDelta.delta_solve_levels P strategy prog facts
  (@RulesAuditMaterializePrelude.mat_native_levels P st) n.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_levels_realization`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_levels_realization :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (n : nat),
exists
  (db : RulesSolve.database P) (events : list RulesAuditMaterializePrelude.mat_frame)
(rounds : nat), @mat_levels_run P strategy prog facts st n db events rounds.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_materialization_consumer`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_materialization_consumer :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@RulesSyntax.program_wf P prog facts ->
@mat_program_run P strategy prog facts output events rounds ->
forall db : RulesSolve.database P,
output = @Some (RulesSolve.database P) db ->
@RulesSolve.represents P (@RulesSolve.rel_of P prog db) (@RulesModel.least_model P prog facts).
```

### `RulesAuditMaterializeFxCorrectness.mat_naive_body_positive`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_naive_body_positive :
forall (P : Type) (event : mat_naive_body_event P), 1 <= @mat_naive_body_weight P event.
```

### `RulesAuditMaterializeFxCorrectness.mat_naive_declared_source_laws`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_naive_declared_source_laws :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive)
  (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)) (fi : RulesSolve.database P)
  (schedule : FixpointAuditScheduleWrapper.fx_rpo_result P (RulesCompile.rconstraint P)
                RulesAuditMaterializePrelude.mat_frame),
cached =
@fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
  (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts) ->
ri = @RulesCompile.index_rules_from P 0 (@RulesSyntax.rules P prog) ->
fi = @RulesCompile.facts_by_pred P prog facts ->
schedule = @mat_rpo_source P prog facts st lower k ri ->
@FixpointAuditWorklistCallbacks.fx_declared_source_laws P (RulesCompile.rconstraint P)
  (@RulesCompile.relation P prog facts) (mat_naive_body_event P) (@RulesSyntax.penc P prog)
  (@RulesCompile.rconstraint_encoding P (@RulesSyntax.penc P prog))
  (@RulesCompile.relation_lattice P prog facts)
  (@FixpointSchedule.rpo_scheduler P (RulesCompile.rconstraint P)
     (@RulesCompile.relation P prog facts) (@RulesSyntax.penc P prog)
     (@mat_compiled_system P prog facts st lower k)
     (@mat_compiled_static P prog facts st lower k))
  (@mat_compiled_system P prog facts st lower k)
  (@mat_naive_declared_source P prog facts st lower k cached ri fi schedule).
```

### `RulesAuditMaterializeBodiesCorrectness.mat_naive_firing_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_naive_firing_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (r : RulesSyntax.rule P)
  (env : P ->
         RulesAuditMaterializePrelude.mat_run (CollectionsFinSet.FinSet.t RulesSyntax.tuple)),
@fst (CollectionsTrie.Trie.t (list positive * unit))
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_naive_firing P prog
     (@fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
        (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts))
     r env) =
@RulesCompile.fire_rule P prog facts r
  (fun p : P =>
   @fst (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
     (list RulesAuditMaterializePrelude.mat_frame) (env p)).
```

### `RulesAuditMaterializeNaiveCorrectness.mat_naive_program_callback_receipts`

Card: AUD-RU-MAT-NAIVE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCorrectness.v`.

```rocq
Theorem mat_naive_program_callback_receipts :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (B : Type) (source : @mat_predicate_callback_source P prog B)
  (encode_budget arity_budget : P -> nat) (output : option (RulesSolve.database P))
  (events : list (@mat_naive_event P prog facts)),
@mat_predicate_callback_receipts_statement P prog B source ->
@mat_naive_program_run P prog facts output events ->
exists receipts : list (list B * nat),
  @mat_external_trace_receipts P prog B source encode_budget arity_budget
    (@mat_naive_callback_frames P prog facts events) receipts.
```

### `RulesAuditMaterializeNaiveCorrectness.mat_naive_program_erases`

Card: AUD-RU-MAT-NAIVE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCorrectness.v`.

```rocq
Theorem mat_naive_program_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (output : option (RulesSolve.database P)) (events : list (@mat_naive_event P prog facts)),
@mat_naive_program_run P prog facts output events ->
output = @RulesSolve.solve_program P prog facts.
```

### `RulesAuditMaterializeNaiveCorrectness.mat_naive_program_realization`

Card: AUD-RU-MAT-NAIVE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCorrectness.v`.

```rocq
Theorem mat_naive_program_realization :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P)),
exists
  (output : option (RulesSolve.database P)) (events : list (@mat_naive_event P prog facts)),
  @mat_naive_program_run P prog facts output events.
```

### `RulesAuditMaterializeNaiveCorrectness.mat_naive_program_source_bound`

Card: AUD-RU-MAT-NAIVE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCorrectness.v`.

```rocq
Theorem mat_naive_program_source_bound :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (output : option (RulesSolve.database P)) (events : list (@mat_naive_event P prog facts)),
@mat_naive_program_run P prog facts output events ->
@mat_naive_work P prog facts events <=
@RulesAuditMaterializeNaiveDimensions.mat_naive_whole_budget P prog facts
  (@mat_naive_operand_max P prog facts events).
```

### `RulesAuditMaterializeFxCorrectness.mat_naive_trace_source_forgets`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_naive_trace_source_forgets :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive)
  (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)) (fi : RulesSolve.database P)
  (schedule : FixpointAuditScheduleWrapper.fx_rpo_result P (RulesCompile.rconstraint P)
                RulesAuditMaterializePrelude.mat_frame),
forall (initial : option (@mat_query_cursor P prog facts st lower k))
  (events : CollectionsAuditCost.audit_trace
              (FixpointAuditWorklist.fx_declared_call P (RulesCompile.rconstraint P)
                 (@RulesCompile.relation P prog facts)))
  (bodies : list (list (list (mat_naive_body_event P))))
  (final : option (@mat_query_cursor P prog facts st lower k)),
@mat_naive_trace_source P prog facts st lower k cached ri fi schedule initial events bodies
  final ->
@FixpointAuditWorklistCallbacks.fx_declared_trace_source P (RulesCompile.rconstraint P)
  (@RulesCompile.relation P prog facts) (mat_naive_body_event P)
  (@mat_naive_declared_source P prog facts st lower k cached ri fi schedule) events bodies.
```

### `RulesAuditMaterializePlansCorrectness.mat_plan_bindings_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_plan_bindings_erases :
forall (Q : Type) (ps : list (RulesSyntax.atom Q))
  (env : Q -> CollectionsFinSet.FinSet.t RulesSyntax.tuple)
  (plan : RulesDelta.delta_join_plan Q),
@fst (list RulesCompile.binding) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_plan_bindings Q ps
     (fun q : Q =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (env q))
     plan) =
@RulesDelta.delta_plan_bindings Q ps env plan.
```

### `RulesAuditMaterializePlansCorrectness.mat_plan_rows_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_plan_rows_erases :
forall (Q : Type) (strategy : RulesJoin.join_strategy) (ps : list (RulesSyntax.atom Q))
  (rows : Q -> list RulesSyntax.tuple),
@fst (RulesDelta.delta_join_plan Q) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_plan_rows Q strategy ps
     (fun q : Q => @RulesAuditMaterializePrelude.mat_return (list RulesSyntax.tuple) (rows q))) =
@RulesDelta.delta_plan_rows Q strategy ps rows.
```

### `RulesAuditMaterializePlansCorrectness.mat_plan_update_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_plan_update_erases :
forall (Q : Type) (reset : Q -> bool) (rows : Q -> list RulesSyntax.tuple)
  (plan : RulesDelta.delta_join_plan Q),
@fst (RulesDelta.delta_join_plan Q) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_plan_update Q (fun q : Q => @RulesAuditMaterializePrelude.mat_return bool (reset q))
     (fun q : Q => @RulesAuditMaterializePrelude.mat_return (list RulesSyntax.tuple) (rows q))
     plan) =
@RulesDelta.delta_update_plan Q reset rows plan.
```

### `RulesAuditMaterializePlansCorrectness.mat_prepare_jobs_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_prepare_jobs_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (st : RulesStratify.stratification P) (k : nat)
  (lower : P -> CollectionsFinSet.FinSet.t RulesSyntax.tuple)
  (acc front : RulesSolve.database P),
@fst (list (RulesSyntax.rule P * RulesSyntax.atom P * RulesDelta.delta_join_plan (P * bool)))
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_prepare_jobs P strategy prog (@RulesAuditMaterializePrelude.MatExternalLevels P st) k
     (fun p : P =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (lower p))
     acc front) =
@RulesDelta.delta_prepare_jobs P strategy prog st k lower acc front.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_prepared_step_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_prepared_step_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesStratify.stratification P) (k : nat)
  (lower : P -> CollectionsFinSet.FinSet.t RulesSyntax.tuple) (s : RulesDelta.delta_state P),
let cached :=
  @fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
    (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts)
  in
@fst (option (RulesDelta.delta_state P)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_prepared_step P prog facts (@RulesAuditMaterializePrelude.MatExternalLevels P st) k
     (fun p : P =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (lower p))
     cached s) =
@RulesDelta.delta_prepared_step P prog facts st k lower s.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_program_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_program_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
output = @RulesDelta.solve_program_delta P strategy prog facts.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_program_input_loop_bound`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_program_input_loop_bound :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
RulesAuditMaterializePrelude.mat_work events <=
mat_whole_budget (@mat_input_dimension P prog facts) (@mat_program_loop_budget P prog facts)
  (RulesAuditMaterializePrelude.mat_width events).
```

### `RulesAuditMaterializeDeltaCorrectness.mat_program_realization`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_program_realization :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)),
exists
  (output : option (RulesSolve.database P)) (events : list
                                                        RulesAuditMaterializePrelude.mat_frame)
(rounds : nat), @mat_program_run P strategy prog facts output events rounds.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_program_rounds_input_bound`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_program_rounds_input_bound :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
rounds <= @mat_program_loop_budget P prog facts.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_program_unique`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_program_unique :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (o1 : option (RulesSolve.database P))
  (e1 : list RulesAuditMaterializePrelude.mat_frame) (n1 : nat)
  (o2 : option (RulesSolve.database P)) (e2 : list RulesAuditMaterializePrelude.mat_frame)
  (n2 : nat),
@mat_program_run P strategy prog facts o1 e1 n1 ->
@mat_program_run P strategy prog facts o2 e2 n2 -> o1 = o2 /\ e1 = e2 /\ n1 = n2.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_program_whole_bound`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_program_whole_bound :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
RulesAuditMaterializePrelude.mat_work events <=
mat_whole_budget (@mat_input_dimension P prog facts)
  (rounds + @length (RulesSyntax.rule P) (@RulesSyntax.rules P prog))
  (RulesAuditMaterializePrelude.mat_width events).
```

### `RulesAuditMaterializeBodiesCorrectness.mat_relation_callbacks_bound`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_relation_callbacks_bound :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (a b : @RulesCompile.relation P prog facts),
let nodes :=
  1 +
  @CollectionsAuditElements.audit_trie_nodes (RulesSyntax.tuple * unit)
    (@proj1_sig (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
       (fun s : CollectionsFinSet.FinSet.t RulesSyntax.tuple =>
        @OrderPowerset.within_set RulesSyntax.tuple RulesCompile.tuple_encoding
          (@RulesCompile.herbrand P prog facts) s)
       a) +
  @CollectionsAuditElements.audit_trie_nodes (RulesSyntax.tuple * unit)
    (@proj1_sig (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
       (fun s : CollectionsFinSet.FinSet.t RulesSyntax.tuple =>
        @OrderPowerset.within_set RulesSyntax.tuple RulesCompile.tuple_encoding
          (@RulesCompile.herbrand P prog facts) s)
       b)
  in
RulesAuditMaterializePrelude.mat_work
  (@snd bool (list RulesAuditMaterializePrelude.mat_frame) (@mat_relation_leb P prog facts a b)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))) *
nodes /\
RulesAuditMaterializePrelude.mat_work
  (@snd (@RulesCompile.relation P prog facts) (list RulesAuditMaterializePrelude.mat_frame)
     (@mat_relation_join P prog facts a b)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))) *
nodes /\
RulesAuditMaterializePrelude.mat_work
  (@snd (@RulesCompile.relation P prog facts) (list RulesAuditMaterializePrelude.mat_frame)
     (@mat_relation_widen P prog facts a b)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))) *
nodes.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_relation_callbacks_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_relation_callbacks_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P)),
(forall a b : @RulesCompile.relation P prog facts,
 @fst bool (list RulesAuditMaterializePrelude.mat_frame) (@mat_relation_leb P prog facts a b) =
 @OrderLattice.leb (@RulesCompile.relation P prog facts)
   (@RulesCompile.relation_lattice P prog facts) a b) /\
(forall a b : @RulesCompile.relation P prog facts,
 @fst (@RulesCompile.relation P prog facts) (list RulesAuditMaterializePrelude.mat_frame)
   (@mat_relation_join P prog facts a b) =
 @OrderLattice.join (@RulesCompile.relation P prog facts)
   (@RulesCompile.relation_lattice P prog facts) a b) /\
(forall a b : @RulesCompile.relation P prog facts,
 @fst (@RulesCompile.relation P prog facts) (list RulesAuditMaterializePrelude.mat_frame)
   (@mat_relation_widen P prog facts a b) =
 @OrderLattice.widen (@RulesCompile.relation P prog facts)
   (@RulesCompile.relation_lattice P prog facts) a b).
```

### `RulesAuditMaterializeFxCorrectness.mat_rhs_source_erases`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_rhs_source_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive),
forall (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)) (fi : RulesSolve.database P)
  (c : RulesCompile.rconstraint P),
@fst (FixpointQuery.Query.t P (@RulesCompile.relation P prog facts))
  (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_rhs_source P prog facts st lower k cached ri fi c) =
@RulesCompile.stratum_rhs P prog facts (@RulesAuditMaterializePrelude.mat_native_levels P st)
  (@RulesSolve.rel_of P prog lower) k ri fi c.
```

### `RulesAuditMaterializeFxCorrectness.mat_rpo_source_erases`

Card: AUD-RU-MAT-FX

Source destination: `theories/Rules/RulesAuditMaterializeFxCorrectness.v`.

```rocq
Theorem mat_rpo_source_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (lower : RulesSolve.database P)
  (k : nat) (ri : CollectionsMap.Map.t nat (RulesSyntax.rule P)),
ri = @RulesCompile.index_rules_from P 0 (@RulesSyntax.rules P prog) ->
let result := @mat_rpo_source P prog facts st lower k ri in
let native :=
  @FixpointSchedule.rpo_scheduler P (RulesCompile.rconstraint P)
    (@RulesCompile.relation P prog facts) (@RulesSyntax.penc P prog)
    (@mat_compiled_system P prog facts st lower k)
    (@mat_compiled_static P prog facts st lower k)
  in
forall x : P,
@fst positive
  (list
     (FixpointAuditSchedule.audit_rpo_schedule_event P
        (FixpointAuditScheduleWrapper.fx_dep_event P (RulesCompile.rconstraint P)
           RulesAuditMaterializePrelude.mat_frame)))
  (@FixpointAuditSchedule.audit_rpo_schedule_priority P
     (FixpointAuditScheduleWrapper.fx_dep_event P (RulesCompile.rconstraint P)
        RulesAuditMaterializePrelude.mat_frame)
     (@FixpointAuditScheduleWrapper.fx_dep_encoder P (RulesCompile.rconstraint P)
        RulesAuditMaterializePrelude.mat_frame (@mat_index_callbacks P prog st k ri))
     (@FixpointAuditScheduleWrapper.fx_rpo_positions P (RulesCompile.rconstraint P)
        RulesAuditMaterializePrelude.mat_frame result)
     x) =
@FixpointWorklist.priority P native x /\
@fst bool
  (list
     (FixpointAuditSchedule.audit_rpo_schedule_event P
        (FixpointAuditScheduleWrapper.fx_dep_event P (RulesCompile.rconstraint P)
           RulesAuditMaterializePrelude.mat_frame)))
  (@FixpointAuditSchedule.audit_rpo_schedule_widening P
     (FixpointAuditScheduleWrapper.fx_dep_event P (RulesCompile.rconstraint P)
        RulesAuditMaterializePrelude.mat_frame)
     (@FixpointAuditScheduleWrapper.fx_dep_encoder P (RulesCompile.rconstraint P)
        RulesAuditMaterializePrelude.mat_frame (@mat_index_callbacks P prog st k ri))
     (@FixpointAuditScheduleWrapper.fx_rpo_heads P (RulesCompile.rconstraint P)
        RulesAuditMaterializePrelude.mat_frame result)
     x) =
@FixpointWorklist.widening_point P native x.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_rule_index_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_rule_index_erases :
forall (P : Type) (n : nat) (rs : list (RulesSyntax.rule P)),
@fst (CollectionsMap.Map.t nat (RulesSyntax.rule P))
  (list RulesAuditMaterializePrelude.mat_frame) (@mat_rule_index P n rs) =
@RulesCompile.index_rules_from P n rs.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_setup_cached_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_setup_cached_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P)),
@fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
  (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts) =
(@RulesCompile.preds P prog facts, @RulesCompile.constants P prog facts).
```

### `RulesAuditMaterializeDeltaCorrectness.mat_step_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_step_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesStratify.stratification P) (k : nat)
  (lower : P -> CollectionsFinSet.FinSet.t RulesSyntax.tuple) (s : RulesDelta.delta_state P),
@fst (option (RulesDelta.delta_state P)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_step P prog facts (@RulesAuditMaterializePrelude.MatExternalLevels P st) k
     (fun p : P =>
      @RulesAuditMaterializePrelude.mat_return (CollectionsFinSet.FinSet.t RulesSyntax.tuple)
        (lower p))
     s) =
@RulesDelta.delta_step P prog facts st k lower s.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_store_total_values_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_store_total_values_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (targets : list P)
  (values : FixpointSystem.assignment P (@RulesCompile.relation P prog facts))
  (db : RulesSolve.database P),
@fst (RulesSolve.database P) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_store_total_values P prog facts targets values db) =
@RulesSolve.store_relations P prog facts targets
  (@FixpointSystem.lookup P (@RulesCompile.relation P prog facts) (@RulesSyntax.penc P prog)
     (@RulesCompile.relation_lattice P prog facts) values)
  db.
```

### `RulesAuditMaterializeStratifyCorrectness.mat_stratify_bound`

Card: AUD-RU-MAT-STRATIFY

Source destination: `theories/Rules/RulesAuditMaterializeStratifyCorrectness.v`.

```rocq
Theorem mat_stratify_bound :
forall (P : Type) (prog : RulesSyntax.program P),
let
'(_, events) := @mat_stratify P prog in
 let width := S (RulesAuditMaterializePrelude.mat_width events) in
 RulesAuditMaterializePrelude.mat_work events <=
 Init.Nat.of_num_uint
   (Number.UIntDecimal
      (Decimal.D1
         (Decimal.D0
            (Decimal.D0
               (Decimal.D0
    (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))))
      *
 width ^ 12.
```

### `RulesAuditMaterializeStratifyCorrectness.mat_stratify_erases`

Card: AUD-RU-MAT-STRATIFY

Source destination: `theories/Rules/RulesAuditMaterializeStratifyCorrectness.v`.

```rocq
Theorem mat_stratify_erases :
forall (P : Type) (prog : RulesSyntax.program P),
match
  @fst (option (RulesAuditMaterializePrelude.mat_level_context P))
    (list RulesAuditMaterializePrelude.mat_frame) (@mat_stratify P prog)
with
| @Some _ context =>
    match @RulesStratify.stratify P prog with
    | @Some _ native =>
        @RulesStratify.count P (@RulesAuditMaterializePrelude.mat_native_levels P context) =
        @RulesStratify.count P native /\
        (forall p : P,
         @RulesStratify.level P (@RulesAuditMaterializePrelude.mat_native_levels P context) p =
         @RulesStratify.level P native p)
    | @None _ => False
    end
| @None _ =>
    match @RulesStratify.stratify P prog with
    | @Some _ _ => False
    | @None _ => True
    end
end.
```

### `RulesAuditMaterializeStratifyCorrectness.mat_stratify_total`

Card: AUD-RU-MAT-STRATIFY

Source destination: `theories/Rules/RulesAuditMaterializeStratifyCorrectness.v`.

```rocq
Theorem mat_stratify_total :
forall (P : Type) (prog : RulesSyntax.program P),
exists
  (out : option (RulesAuditMaterializePrelude.mat_level_context P))
(trace : list RulesAuditMaterializePrelude.mat_frame), @mat_stratify P prog = (out, trace).
```

### `RulesAuditMaterializeStratifyCorrectness.mat_stratify_unique`

Card: AUD-RU-MAT-STRATIFY

Source destination: `theories/Rules/RulesAuditMaterializeStratifyCorrectness.v`.

```rocq
Theorem mat_stratify_unique :
forall (P : Type) (prog : RulesSyntax.program P)
  (r1 : option (RulesAuditMaterializePrelude.mat_level_context P))
  (t1 : list RulesAuditMaterializePrelude.mat_frame)
  (r2 : option (RulesAuditMaterializePrelude.mat_level_context P))
  (t2 : list RulesAuditMaterializePrelude.mat_frame),
@mat_stratify P prog = (r1, t1) -> @mat_stratify P prog = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_stratum_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_stratum_erases :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (lower : RulesSolve.database P) (final : RulesDelta.delta_state P)
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_stratum_run P strategy prog facts st k lower final events rounds ->
final =
@RulesDelta.delta_solve_stratum P strategy prog facts
  (@RulesAuditMaterializePrelude.mat_native_levels P st) k (@RulesSolve.rel_of P prog lower).
```

### `RulesAuditMaterializeDeltaCorrectness.mat_stratum_realization`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_stratum_realization :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (lower : RulesSolve.database P),
exists
  (final : RulesDelta.delta_state P) (events : list RulesAuditMaterializePrelude.mat_frame)
(rounds : nat), @mat_stratum_run P strategy prog facts st k lower final events rounds.
```

### `RulesAuditMaterializeBodiesCorrectness.mat_subset_bound`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_subset_bound :
forall (K : Type) (a b : CollectionsFinSet.FinSet.t K),
RulesAuditMaterializePrelude.mat_work
  (@snd bool (list RulesAuditMaterializePrelude.mat_frame) (@mat_subset K a b)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))) *
(1 + @CollectionsAuditElements.audit_trie_nodes (K * unit) a).
```

### `RulesAuditMaterializeBodiesCorrectness.mat_subset_erases`

Card: AUD-RU-MAT-BODIES

Source destination: `theories/Rules/RulesAuditMaterializeBodiesCorrectness.v`.

```rocq
Theorem mat_subset_erases :
forall (K : Type) (E : CollectionsEncoding.encoding K) (a b : CollectionsFinSet.FinSet.t K),
@fst bool (list RulesAuditMaterializePrelude.mat_frame) (@mat_subset K a b) =
@CollectionsFinSet.FinSet.subset K E a b.
```

### `RulesAuditMaterializePlansCorrectness.mat_tag_rule_erases`

Card: AUD-RU-MAT-PLANS

Source destination: `theories/Rules/RulesAuditMaterializePlansCorrectness.v`.

```rocq
Theorem mat_tag_rule_erases :
forall (P : Type) (E : CollectionsEncoding.encoding P) (r : RulesSyntax.rule P)
  (pivot : RulesSyntax.atom P),
@fst (RulesSyntax.rule (P * bool)) (list RulesAuditMaterializePrelude.mat_frame)
  (@mat_tag_rule P E r pivot) =
@RulesDelta.delta_tag_rule P E r pivot.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_total_erases`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_total_erases :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (lower : RulesSolve.database P) (state : RulesDelta.delta_state P)
  (Hvalid : @RulesDelta.delta_valid P prog facts state) (final : RulesDelta.delta_state P)
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
let cached :=
  @fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
    (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts)
  in
@mat_total_run P prog facts st k lower cached state final events rounds ->
final =
@proj1_sig (RulesDelta.delta_state P)
  (fun t : RulesDelta.delta_state P =>
   @RulesDelta.delta_step P prog facts (@RulesAuditMaterializePrelude.mat_native_levels P st) k
     (@RulesSolve.rel_of P prog lower) t =
   @None (RulesDelta.delta_state P) /\
   Relation_Operators.clos_refl_trans (RulesDelta.delta_state P)
     (fun x y : RulesDelta.delta_state P =>
      @RulesDelta.delta_step P prog facts
        (@RulesAuditMaterializePrelude.mat_native_levels P st) k
        (@RulesSolve.rel_of P prog lower) x =
      @Some (RulesDelta.delta_state P) y)
     state t)
  (@RulesDelta.delta_execute P prog facts
     (@RulesAuditMaterializePrelude.mat_native_levels P st) k (@RulesSolve.rel_of P prog lower)
     state Hvalid).
```

### `RulesAuditMaterializeDeltaCorrectness.mat_total_realization`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_total_realization :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (lower : RulesSolve.database P)
  (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive)
  (state : RulesDelta.delta_state P),
@RulesDelta.delta_valid P prog facts state ->
exists
  (final : RulesDelta.delta_state P) (events : list RulesAuditMaterializePrelude.mat_frame)
(rounds : nat), @mat_total_run P prog facts st k lower cached state final events rounds.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_total_rounds_input_bound`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_total_rounds_input_bound :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (lower : RulesSolve.database P) (state final : RulesDelta.delta_state P)
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@RulesDelta.delta_valid P prog facts state ->
@mat_total_run P prog facts st k lower
  (@fst (CollectionsMap.Map.t P unit * CollectionsTrie.Trie.t (positive * unit))
     (list RulesAuditMaterializePrelude.mat_frame) (@mat_setup_cached P prog facts))
  state final events rounds ->
rounds <= @RulesDelta.delta_remaining P prog facts state.
```

### `RulesAuditMaterializeDeltaCorrectness.mat_total_unique`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem mat_total_unique :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (st : RulesAuditMaterializePrelude.mat_level_context P) (k : nat)
  (lower : RulesSolve.database P)
  (cached : CollectionsFinSet.FinSet.t P * CollectionsFinSet.FinSet.t positive)
  (state f1 : RulesDelta.delta_state P) (e1 : list RulesAuditMaterializePrelude.mat_frame)
  (n1 : nat) (f2 : RulesDelta.delta_state P) (e2 : list RulesAuditMaterializePrelude.mat_frame)
  (n2 : nat),
@mat_total_run P prog facts st k lower cached state f1 e1 n1 ->
@mat_total_run P prog facts st k lower cached state f2 e2 n2 -> f1 = f2 /\ e1 = e2 /\ n1 = n2.
```

### `RulesAuditMaterializeFullSourceCorrectness.rules_delta_materialization_full_source`

Card: AUD-RU-MAT

Source destination: `theories/Rules/RulesAuditMaterializeFullSourceCorrectness.v`.

```rocq
Theorem rules_delta_materialization_full_source :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (B : Type)
  (source : @mat_predicate_callback_source P prog B) (encode_budget arity_budget : P -> nat),
@mat_predicate_callback_receipts_statement P prog B source ->
@mat_predicate_callback_input_bounds_statement P prog B source encode_budget arity_budget ->
exists
  (output : option (RulesSolve.database P)) (events : list
                                                        RulesAuditMaterializePrelude.mat_frame)
(rounds : nat) (receipts : list (list B * nat)),
  @mat_program_run P strategy prog facts output events rounds /\
  output = @RulesDelta.solve_program_delta P strategy prog facts /\
  @mat_external_trace_receipts P prog B source encode_budget arity_budget events receipts /\
  RulesAuditMaterializePrelude.mat_work events +
  @mat_external_body_work P prog B source receipts <=
  mat_whole_budget (@mat_input_dimension P prog facts) (@mat_program_loop_budget P prog facts)
    (RulesAuditMaterializePrelude.mat_width events) +
  mat_external_trace_allowance B receipts.
```

### `RulesAuditMaterializeDeltaCorrectness.rules_materialization_consumer`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem rules_materialization_consumer :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@RulesSyntax.program_wf P prog facts ->
@mat_program_run P strategy prog facts output events rounds ->
forall db : RulesSolve.database P,
output = @Some (RulesSolve.database P) db ->
@RulesSolve.represents P (@RulesSolve.rel_of P prog db) (@RulesModel.least_model P prog facts).
```

### `RulesAuditMaterializeDeltaCorrectness.rules_materialization_cost`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem rules_materialization_cost :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
RulesAuditMaterializePrelude.mat_work events <=
mat_whole_budget (@mat_input_dimension P prog facts) (@mat_program_loop_budget P prog facts)
  (RulesAuditMaterializePrelude.mat_width events).
```

### `RulesAuditMaterializeFullSourceCorrectness.rules_materialization_full_source`

Card: AUD-RU-MAT

Source destination: `theories/Rules/RulesAuditMaterializeFullSourceCorrectness.v`.

```rocq
Theorem rules_materialization_full_source :
rules_delta_materialization_full_source_statement /\
rules_naive_materialization_full_source_statement.
```

### `RulesAuditMaterializeDeltaCorrectness.rules_materialization_same_execution_bound`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem rules_materialization_same_execution_bound :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
RulesAuditMaterializePrelude.mat_work events <=
mat_whole_budget (@mat_input_dimension P prog facts) (@mat_program_loop_budget P prog facts)
  (RulesAuditMaterializePrelude.mat_width events).
```

### `RulesAuditMaterializeDeltaCorrectness.rules_materialization_source_correspondence`

Card: AUD-RU-MAT-DELTA

Source destination: `theories/Rules/RulesAuditMaterializeDeltaCorrectness.v`.

```rocq
Theorem rules_materialization_source_correspondence :
forall (P : Type) (strategy : RulesJoin.join_strategy) (prog : RulesSyntax.program P)
  (facts : list (RulesSyntax.ground_atom P)) (output : option (RulesSolve.database P))
  (events : list RulesAuditMaterializePrelude.mat_frame) (rounds : nat),
@mat_program_run P strategy prog facts output events rounds ->
output = @RulesDelta.solve_program_delta P strategy prog facts.
```

### `RulesAuditMaterializeNaiveCorrectness.rules_naive_materialization_consumer`

Card: AUD-RU-MAT-NAIVE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCorrectness.v`.

```rocq
Theorem rules_naive_materialization_consumer :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (db : RulesSolve.database P) (events : list (@mat_naive_event P prog facts)),
@RulesSyntax.program_wf P prog facts ->
@mat_naive_program_run P prog facts (@Some (RulesSolve.database P) db) events ->
@RulesSolve.represents P (@RulesSolve.rel_of P prog db) (@RulesModel.least_model P prog facts).
```

### `RulesAuditMaterializeNaiveCorrectness.rules_naive_materialization_full_source`

Card: AUD-RU-MAT-NAIVE

Source destination: `theories/Rules/RulesAuditMaterializeNaiveCorrectness.v`.

```rocq
Theorem rules_naive_materialization_full_source :
forall (P : Type) (prog : RulesSyntax.program P) (facts : list (RulesSyntax.ground_atom P))
  (B : Type) (source : @mat_predicate_callback_source P prog B)
  (encode_budget arity_budget : P -> nat),
@mat_predicate_callback_receipts_statement P prog B source ->
@mat_predicate_callback_input_bounds_statement P prog B source encode_budget arity_budget ->
exists
  (output : option (RulesSolve.database P)) (events : list (@mat_naive_event P prog facts))
(receipts : list (list B * nat)),
  @mat_naive_program_run P prog facts output events /\
  output = @RulesSolve.solve_program P prog facts /\
  @mat_external_trace_receipts P prog B source encode_budget arity_budget
    (@mat_naive_callback_frames P prog facts events) receipts /\
  @mat_naive_work P prog facts events + @mat_external_body_work P prog B source receipts <=
  @RulesAuditMaterializeNaiveDimensions.mat_naive_whole_budget P prog facts
    (@mat_naive_operand_max P prog facts events) +
  mat_external_trace_allowance B receipts.
```

<!-- AUD-API-MAT-END -->

<!-- AUD-API-RU-BEGIN -->

# Rules source contracts

Definitions specify source work; future theorem types are proof obligations.

## Galois.Rules.RulesAuditAtomFold

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditAtomFold.v`.

```rocq
(** * Full nested atom-fold library model

    This preserves all three encoder calls and each actual trie subrun of delta_add_atoms.
    Duplicate atoms remain separate fold iterations. Builds on RulesDelta and shared models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditElements.
From Galois.Rules Require Import RulesAuditRelations.
Import List.ListNotations.

Inductive rules_atom_full_event (P : Type) : Type :=
  | RafRelationGet (predicate : P) (code : positive) (before : database P)
      (raw : option (FinSet.t tuple)) (body : audit_trace (audit_trie_call (P * FinSet.t tuple)))
  | RafTupleAdd (row : tuple) (before after : FinSet.t tuple)
      (body : list (audit_set_event tuple (audit_list_event positive (audit_basic_encoding_event
  positive))))
  | RafRelationSet (predicate : P) (value : FinSet.t tuple) (code : positive)
      (before after : database P) (body : audit_trace (audit_trie_call (P * FinSet.t tuple)))
  | RafElements (input : FinSet.t (ground_atom P)) (output : list (ground_atom P))
      (body : list (audit_set_elements_event (ground_atom P)))
  | RafCase (site : nat).
Arguments RafRelationGet {P} _ _ _ _ _.
Arguments RafTupleAdd {P} _ _ _ _.
Arguments RafRelationSet {P} _ _ _ _ _ _.
Arguments RafElements {P} _ _ _.
Arguments RafCase {P} _.

Fixpoint rules_atom_fold_counted {P} (prog : program P) (atoms : list (ground_atom P))
    (initial : database P) : database P * list (rules_atom_full_event P) :=
  match atoms with
  | [] => (initial, [RafCase 0])
  | (p, row) :: rest =>
      let '(before, tail) := rules_atom_fold_counted prog rest initial in
      let lookup_code := encode (penc prog) p in
      let '(raw, get_body) := audit_map_code_get lookup_code before in
      let relation := match raw with Some r => r | None => FinSet.empty end in
      let '(next, add_body) := audit_finset_add (audit_list_encode audit_positive_encode) row
  relation in
      let write_code := encode (penc prog) p in
      let '(after, set_body) := audit_trie_set write_code (p, next) before in
      (after, RafCase 0 :: tail ++ [RafRelationGet p lookup_code before raw get_body; RafCase 1;
        RafTupleAdd row relation next add_body; RafRelationSet p next write_code before after
  set_body])
  end.

Definition rules_delta_index_counted {P} (prog : program P) (input : FinSet.t (ground_atom P)) :
    database P * list (rules_atom_full_event P) :=
  let '(atoms, element_body) := audit_finset_elements input in
  let '(out, events) := rules_atom_fold_counted prog atoms Map.empty in
  (out, RafElements input atoms element_body :: events).

Definition rules_atom_fold_erasure_statement : Prop :=
  (forall P (prog : program P) atoms initial,
    fst (rules_atom_fold_counted prog atoms initial) = delta_add_atoms prog atoms initial) /\
  (forall P (prog : program P) input,
    fst (rules_delta_index_counted prog input) = delta_index prog input).

Definition rules_atom_full_event_work {P} (event : rules_atom_full_event P) : nat :=
  match event with
  | RafRelationGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | RafTupleAdd _ _ _ body =>
      audit_finset_source_work (audit_list_events_work audit_basic_encoding_work) body
  | RafRelationSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | RafElements _ _ body => audit_set_elements_work body
  | RafCase _ => 1
  end.
Definition rules_atom_full_event_budget {P} (event : rules_atom_full_event P) : nat :=
  match event with
  | RafRelationGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | RafTupleAdd row _ _ _ =>
      10 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
        16 * Pos.size_nat (encode tuple_encoding row)
  | RafRelationSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | RafElements input _ _ => 6 + 19 * audit_trie_nodes input + audit_trie_output_bits input
  | RafCase _ => 1
  end.
Definition rules_atom_full_work {P} (events : list (rules_atom_full_event P)) : nat :=
  fold_right (fun event n => rules_atom_full_event_work event + n) 0 events.
Definition rules_atom_full_budget {P} (events : list (rules_atom_full_event P)) : nat :=
  fold_right (fun event n => rules_atom_full_event_budget event + n) 0 events.
Definition rules_atom_fold_selected_cost_statement : Prop :=
  forall P (prog : program P) atoms initial,
    let '(result, events) := rules_atom_fold_counted prog atoms initial in
    result = delta_add_atoms prog atoms initial /\
    rules_atom_full_work events <= rules_atom_full_budget events.

(** This selected bound depends only on the original atom list and encoded operands. It
    excludes execution of the mathematical observer and external predicate encoder bodies. *)
Fixpoint rules_atom_fold_input_budget {P} (prog : program P) (atoms : list (ground_atom P)) : nat :=
  match atoms with
  | [] => 1
  | (p, row) :: rest =>
      1 + rules_atom_fold_input_budget prog rest +
      (2 + 6 * Pos.size_nat (encode (penc prog) p)) + 1 +
      (10 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
       16 * Pos.size_nat (encode tuple_encoding row)) +
      (2 + 17 * Pos.size_nat (encode (penc prog) p))
  end.
Definition rules_atom_fold_input_bound_statement : Prop :=
  forall P (prog : program P) atoms initial,
    let '(result, events) := rules_atom_fold_counted prog atoms initial in
    result = delta_add_atoms prog atoms initial /\
    rules_atom_full_work events <= rules_atom_fold_input_budget prog atoms.
Definition rules_delta_index_input_budget {P} (prog : program P) (input : FinSet.t (ground_atom
  P)) : nat :=
  6 + 19 * audit_trie_nodes input + audit_trie_output_bits input +
    rules_atom_fold_input_budget prog (FinSet.elements input).
Definition rules_delta_index_input_bound_statement : Prop :=
  forall P (prog : program P) input,
    let '(result, events) := rules_delta_index_counted prog input in
    result = delta_index prog input /\
    rules_atom_full_work events <= rules_delta_index_input_budget prog input.

(** Source-shaped fold derivation. Each cons contains the same recursively produced
    database, actual get, actual tuple-encoder/add subrun and actual database write. *)
Inductive rules_atom_fold_run {P} (prog : program P) :
    list (ground_atom P) -> database P -> database P -> list (rules_atom_full_event P) -> Prop :=
  | RulesAtomFoldNil : forall initial,
      rules_atom_fold_run prog [] initial initial [RafCase 0]
  | RulesAtomFoldCons : forall p row rest initial before tail raw get_body relation next add_body
      after set_body,
      rules_atom_fold_run prog rest initial before tail ->
      audit_map_code_get (encode (penc prog) p) before = (raw, get_body) ->
      relation = (match raw with Some value => value | None => FinSet.empty end) ->
      audit_finset_add (audit_list_encode audit_positive_encode) row relation = (next, add_body) ->
      audit_trie_set (encode (penc prog) p) (p, next) before = (after, set_body) ->
      rules_atom_fold_run prog ((p, row) :: rest) initial after
        (RafCase 0 :: tail ++ [RafRelationGet p (encode (penc prog) p) before raw get_body;
          RafCase 1; RafTupleAdd row relation next add_body;
          RafRelationSet p next (encode (penc prog) p) before after set_body]).

Definition rules_atom_fold_run_total_statement : Prop :=
  forall P (prog : program P) atoms initial,
    let '(result, events) := rules_atom_fold_counted prog atoms initial in
    rules_atom_fold_run prog atoms initial result events.
Definition rules_atom_fold_run_unique_statement : Prop :=
  forall P (prog : program P) atoms initial result events,
    rules_atom_fold_run prog atoms initial result events ->
    rules_atom_fold_counted prog atoms initial = (result, events).
Definition rules_atom_fold_run_erasure_statement : Prop :=
  forall P (prog : program P) atoms initial result events,
    rules_atom_fold_run prog atoms initial result events ->
    result = delta_add_atoms prog atoms initial /\
    rules_atom_full_work events <= rules_atom_fold_input_budget prog atoms.
```

## Galois.Rules.RulesAuditCost

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditCost.v`.

```rocq
(** * Rules join cost contract

    This proposition combines the fixed phase contracts without asserting their proofs.
    For example, its firing component retains each strategy's own intermediate bindings.
    Builds on: the Rules audit index, selection, callback and firing modules. *)
From Galois.Rules Require Import RulesAuditIndex RulesAuditIndexCounts RulesAuditJoinSyntax
  RulesAuditRelations RulesAuditRelationCallbacks RulesAuditNestedPrepare RulesAuditMultiwayPrepare
  RulesAuditPrepareCallbacks RulesAuditNestedProbe RulesAuditMultiwayProbe RulesAuditTerminal
  RulesAuditTerminalCallbacks RulesAuditUniverse RulesAuditNestedSelection
  RulesAuditMultiwaySelection
  RulesAuditFiring RulesAuditFiringCallbacks RulesAuditJoin.

(** Both indexed strategies use actual source phases, callback receipts and quantitative bounds. *)
Definition rules_index_cost : Prop :=
  mat_index_full_erases_statement /\
  mat_index_full_input_bound_statement /\
  mat_variable_full_input_bound_statement /\
  mat_index_full_source_statement /\
  mat_index_row_counts_statement /\
  mat_index_fold_counts_statement /\
  mat_index_add_run_total_statement /\
  mat_join_syntax_erasure_statement /\
  rules_join_relations_erasure_statement /\
  rules_join_relations_row_count_statement /\
  rules_join_relations_selected_cost_statement /\
  rules_join_relations_input_bound_statement /\
  rules_relations_external_source_statement /\
  rules_prepare_nested_full_erases_statement /\
  rules_prepare_nested_full_input_bound_statement /\
  rules_prepare_multiway_full_erases_statement /\
  rules_nested_prepare_source_statement /\
  rules_multiway_prepare_source_statement /\
  rules_nested_probe_erasure_statement /\
  rules_run_nested_selected_cost_statement /\
  rules_multiway_probe_erasure_statement /\
  rules_run_multiway_selected_cost_statement /\
  rules_terminal_erasure_statement /\
  rules_terminal_selected_cost_statement /\
  rules_positive_filter_erasure_statement /\
  rules_universe_erasure_statement /\
  rules_universe_selected_cost_statement /\
  rules_nested_selection_input_bound_statement /\
  rules_nested_selection_source_statement /\
  rules_multiway_selection_count_statement /\
  rules_multiway_selection_input_bound_statement /\
  rules_multiway_selection_source_statement /\
  rules_firing_tail_input_bound_statement /\
  rules_firing_tail_source_statement /\
  rules_join_firing_input_bound_statement /\
  rules_join_firing_source_statement.
```

## Galois.Rules.RulesAuditDeltaRows

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditDeltaRows.v`.

```rocq
(** * Counted materialization row snapshot

    The source maps every stored relation once before exposing its lookup closure.
    Nested relation traversals are retained inside their actual map callbacks.
    Builds on RulesDelta and the shared map and set-enumeration models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditElements CollectionsAuditMapTraverse.
Import List.ListNotations.

Definition rules_delta_rows_snapshot_counted {P} (db : database P) :
    Map.t P (list tuple) *
      list (audit_map_transform_event P (FinSet.t tuple) (list tuple) (audit_set_elements_event
  tuple)) :=
  audit_map_transform audit_finset_elements db.

Definition rules_delta_rows_lookup_counted {P} (prog : program P) (snapshot : Map.t P (list tuple))
    (p : P) : list tuple * (positive * option (list tuple) * audit_trace (audit_trie_call (P *
  list tuple))) :=
  let code := encode (penc prog) p in
  let '(raw, body) := audit_map_code_get code snapshot in
  (match raw with Some rows => rows | None => [] end, (code, raw, body)).

Definition rules_delta_rows_erasure_statement : Prop :=
  forall P (prog : program P) db p,
    let '(snapshot, _) := rules_delta_rows_snapshot_counted db in
    fst (rules_delta_rows_lookup_counted prog snapshot p) = delta_rows prog db p.

Definition rules_delta_rows_snapshot_work {P}
    (events : list (audit_map_transform_event P (FinSet.t tuple) (list tuple)
      (audit_set_elements_event tuple))) : nat :=
  audit_map_transform_source_work audit_set_elements_work events.
Definition rules_delta_rows_snapshot_budget {P} (db : database P)
    (events : list (audit_map_transform_event P (FinSet.t tuple) (list tuple)
      (audit_set_elements_event tuple))) : nat :=
  20 * audit_trie_nodes db + audit_map_transform_child_work audit_set_elements_work events.
Definition rules_delta_rows_snapshot_cost_statement : Prop :=
  forall P (db : database P),
    let '(snapshot, events) := rules_delta_rows_snapshot_counted db in
    snapshot = Map.map FinSet.elements db /\
    rules_delta_rows_snapshot_work events <= rules_delta_rows_snapshot_budget db events.

(** Input-only budget accounts for every relation stored in the original database. *)
Definition rules_delta_rows_input_budget {P} (db : database P) : nat :=
  20 * audit_trie_nodes db +
  fold_right (fun pair n =>
    let relation := snd pair in
    6 + 19 * audit_trie_nodes relation + audit_trie_output_bits relation + n)
    0 (Map.elements db).
Definition rules_delta_rows_input_bound_statement : Prop :=
  forall P (db : database P),
    let '(snapshot, events) := rules_delta_rows_snapshot_counted db in
    snapshot = Map.map FinSet.elements db /\
    rules_delta_rows_snapshot_work events <= rules_delta_rows_input_budget db.
```

## Galois.Rules.RulesAuditFiring

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditFiring.v`.

```rocq
(** * Rule firing after indexed selection

    The same selected bindings pass through negative checks, head instantiation, the universe
    closure and final tuple-set construction. For example, rejected negatives do not produce rows.
    Builds on: RulesAuditTerminal, RulesAuditUniverse and the shared collection audits. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditNestedProbe RulesAuditTerminal RulesAuditUniverse.
Import List.ListNotations.

Fixpoint rules_negative_filter_capture {P} (r : rule P) (env : P -> FinSet.t tuple)
    (bindings : list binding) : list binding * list (list (rules_terminal_event P)) :=
  match bindings with
  | [] => ([], [])
  | b :: rest =>
      let '(keep, first) := rules_negative_literals_counted (body r) env b in
      let '(tail, later) := rules_negative_filter_capture r env rest in
      (if keep then b :: tail else tail, first :: later)
  end.

Fixpoint rules_head_rows_capture (terms : list term) (bindings : list binding) :
    list tuple * list (list rules_nested_probe_event) :=
  match bindings with
  | [] => ([], [])
  | b :: rest =>
      let '(row, first) := rules_probe_instantiate b terms in
      let '(tail, later) := rules_head_rows_capture terms rest in
      (row :: tail, first :: later)
  end.

Fixpoint rules_universe_filter_capture {P} (state : bool * nat * FinSet.t positive)
    (rows : list tuple) : list tuple * list (list (rules_universe_event P)) :=
  match rows with
  | [] => ([], [])
  | row :: rest =>
      let '(keep, first) := @rules_universe_check_counted P state row in
      let '(tail, later) := @rules_universe_filter_capture P state rest in
      (if keep then row :: tail else tail, first :: later)
  end.

Record rules_firing_tail_run (P : Type) := RulesFiringTailRun {
  rules_firing_tail_result : FinSet.t tuple;
  rules_firing_tail_negative_events : list (list (rules_terminal_event P));
  rules_firing_tail_head_events : list (list rules_nested_probe_event);
  rules_firing_tail_universe_events : list (rules_universe_event P);
  rules_firing_tail_filter_events : list (list (rules_universe_event P));
  rules_firing_tail_output_events : list (audit_set_event tuple
    (audit_list_event positive (audit_basic_encoding_event positive)))
}.
Arguments rules_firing_tail_result {P} _.
Arguments rules_firing_tail_negative_events {P} _.
Arguments rules_firing_tail_head_events {P} _.
Arguments rules_firing_tail_universe_events {P} _.
Arguments rules_firing_tail_filter_events {P} _.
Arguments rules_firing_tail_output_events {P} _.

Definition rules_firing_tail_capture {P} (prog : program P) (facts : list (ground_atom P))
    (r : rule P) (env : P -> FinSet.t tuple) (bindings : list binding) : rules_firing_tail_run P :=
  let '(negative, negative_events) := rules_negative_filter_capture r env bindings in
  let '(rows, head_events) := rules_head_rows_capture (args (head r)) negative in
  let '(universe, universe_events) := rules_universe_prepare_counted prog facts (pred (head r)) in
  let '(accepted, filter_events) := rules_universe_filter_capture universe rows in
  let '(output, output_events) :=
    audit_finset_of_list (audit_list_encode audit_positive_encode) accepted in
  RulesFiringTailRun P output negative_events head_events universe_events filter_events
  output_events.

Definition rules_firing_tail_work {P} (run : rules_firing_tail_run P) : nat :=
  4 + 2 * length (rules_firing_tail_negative_events run) +
    fold_right (fun events n => rules_terminal_work events + n) 0
  (rules_firing_tail_negative_events run) +
    2 * length (rules_firing_tail_head_events run) +
    fold_right (fun events n => rules_nested_probe_work events + n) 0
  (rules_firing_tail_head_events run) +
    rules_universe_work (rules_firing_tail_universe_events run) +
    2 * length (rules_firing_tail_filter_events run) +
    fold_right (fun events n => rules_universe_work events + n) 0
  (rules_firing_tail_filter_events run) +
    audit_finset_source_work (audit_list_events_work audit_basic_encoding_work)
      (rules_firing_tail_output_events run).

Definition rules_firing_binding_size (b : binding) : nat :=
  fold_right (fun entry n => 1 + fst entry + Pos.size_nat (snd entry) + n) 0 (Map.elements b).

Definition rules_firing_atom_size {P} (E : encoding P) (a : atom P) : nat :=
  1 + Pos.size_nat (encode E (pred a)) + mat_index_terms_input (args a).

Definition rules_firing_rule_size {P} (E : encoding P) (r : rule P) : nat :=
  rules_firing_atom_size E (head r) +
    fold_right (fun literal n => rules_firing_atom_size E (lit_atom literal) + n) 0 (body r).

Definition rules_firing_tail_input_size {P} (prog : program P) (facts : list (ground_atom P))
    (r : rule P) (bindings : list binding) : nat :=
  2 + arity prog (pred (head r)) + rules_firing_rule_size (penc prog) r +
    fold_right (fun rule n => rules_firing_rule_size (penc prog) rule + n) 0 (rules prog) +
    fold_right (fun fact n => 1 + Pos.size_nat (encode (penc prog) (fst fact)) +
      mat_tuple_size (snd fact) + n) 0 facts +
    fold_right (fun b n => 1 + rules_firing_binding_size b + n) 0 bindings.

Definition rules_firing_tail_input_budget {P} (prog : program P) (facts : list (ground_atom P))
    (r : rule P) (bindings : list binding) : nat :=
  1000000000 * Nat.pow (rules_firing_tail_input_size prog facts r bindings) 12.

(** Tail construction agrees with the original rule firing pipeline for any selected bindings. *)
Definition rules_firing_tail_input_bound_statement : Prop :=
  forall P (prog : program P) facts (r : rule P) env bindings,
    let run := rules_firing_tail_capture prog facts r env bindings in
    rules_firing_tail_result run = FinSet.of_list tuple_encoding
      (filter (in_universe prog facts (pred (head r)))
        (map (fun b => map (inst (binding_value b)) (args (head r)))
          (filter (negative_ok r env) bindings))) /\
    rules_firing_tail_work run <= rules_firing_tail_input_budget prog facts r bindings.
```

## Galois.Rules.RulesAuditFiringCallbacks

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditFiringCallbacks.v`.

```rocq
(** * Rule firing callback receipts

    Negative tests and universe preparation retain environment, encoding and arity bodies.
    For example, each negative literal calls its environment even after a previous failure.
    Builds on: RulesAuditFiring and the relation and terminal callback sources. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin
  RulesAuditRelations
  RulesAuditRelationCallbacks RulesAuditPrepareCallbacks RulesAuditTerminal
  RulesAuditTerminalCallbacks
  RulesAuditUniverse RulesAuditFiring.
Import List.ListNotations.

Definition rules_arity_source_laws {P B} (prog : program P)
    (source : P -> nat -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) : Prop :=
  (forall p, exists body, source p (arity prog p) body) /\
  (forall p out body, source p out body ->
    fold_right (fun item n => weight item + n) 0 body <= bound p).

Definition rules_universe_event_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (event : rules_universe_event P)
    (bodies : list (list B)) : Prop :=
  match event with
  | RuPredicatesSet _ _ events | RuPredicateMem _ _ _ events =>
      Forall2 (rules_relation_entry_source pred_source) (rules_relation_entries events) bodies
  | RuArity p out => exists body, bodies = [body] /\ arity_source p out body
  | _ => bodies = []
  end.

Definition rules_universe_trace_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (events : list (rules_universe_event P))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_universe_event_source pred_source arity_source) events bodies.

Definition rules_negative_filter_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (groups : list (list (rules_terminal_event P))) (bodies : list (list (list (list B)))) : Prop :=
  Forall2 (rules_terminal_trace_source source) groups bodies.

Definition rules_negative_input_budget {P} (bound : P -> nat) (r : rule P) : nat :=
  fold_right (fun literal n => match literal with
    | LPos _ => n
    | LNeg a => bound (pred a) + n
    end) 0 (body r).

Definition rules_universe_external_input_budget {P} (prog : program P) (facts : list
  (ground_atom P))
    (p : P) (pred_bound arity_bound : P -> nat) : nat :=
  let predicates := flat_map rule_predicates (rules prog) ++ map fst facts in
  fold_right (fun key n => pred_bound key + n) 0 predicates + pred_bound p + arity_bound p.

(** The actual tail has same-invocation callback receipts and an input-derived allowance. *)
Definition rules_firing_tail_source_statement : Prop :=
  forall P B (prog : program P) facts (r : rule P) (env : P -> FinSet.t tuple) bindings
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound arity_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    rules_arity_source_laws prog arity_source weight arity_bound ->
    let run := rules_firing_tail_capture prog facts r env bindings in
    exists negative_bodies universe_bodies,
      rules_negative_filter_source env_source (rules_firing_tail_negative_events run)
  negative_bodies /\
      rules_universe_trace_source pred_source arity_source
        (rules_firing_tail_universe_events run) universe_bodies /\
      rules_firing_tail_result run = FinSet.of_list tuple_encoding
        (filter (in_universe prog facts (pred (head r)))
          (map (fun b => map (inst (binding_value b)) (args (head r)))
            (filter (negative_ok r env) bindings))) /\
      rules_firing_tail_work run + rules_terminal_bodies_work weight negative_bodies +
        rules_predicate_bodies_work weight universe_bodies <=
        rules_firing_tail_input_budget prog facts r bindings +
          length bindings * rules_negative_input_budget env_bound r +
          rules_universe_external_input_budget prog facts (pred (head r)) pred_bound arity_bound.
```

## Galois.Rules.RulesAuditIndex

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditIndex.v`.

```rocq
(** * Counted row and variable indexes

    The model retains tuple encoding, trie updates and the actual binding probe subruns.
    For example, a malformed row leaves the current index unchanged.
    Builds on: RulesAuditMaterializePrelude and RulesAuditNestedProbe. *)
From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsTable CollectionsAuditCost CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditNestedProbe
  RulesAuditMaterializePrelude.
Import List.ListNotations.

Definition mat_tuple_encoder (row : tuple) :=
  mat_lift 100 Pos.size_nat (audit_list_events_work audit_basic_encoding_work)
    (audit_list_encode audit_positive_encode row).

Definition mat_bound_term (bound : FinSet.t nat) (t : term) :=
  mat_mark 101 (match t with
    | TConst _ => mat_return true
    | TVar v => mat_lift 102 (fun _ => 1 + v + audit_trie_nodes bound)
        (audit_finset_source_work audit_nat_events_work) (audit_finset_mem audit_nat_encode v bound)
    end).

Fixpoint mat_tuple_key (bound : FinSet.t nat) (ts : list term) (row : tuple) :
    mat_run (option tuple) :=
  mat_mark 103 (match ts, row with
    | [], [] => mat_return (Some [])
    | t :: tail_terms, c :: tail_row =>
        tail <- mat_tuple_key bound tail_terms tail_row;;
        match tail with
        | None => mat_return None
        | Some key => kept <- mat_bound_term bound t;;
            mat_return (Some (if kept then c :: key else key))
        end
    | _, _ => mat_return None
    end).

Definition mat_index_add_full bound terms row before :=
  key <- mat_tuple_key bound terms row;;
  match key with
  | None => mat_return before
  | Some key =>
      raw <- mat_get_encoded mat_tuple_encoder key before;;
      let old := match raw with Some rows => rows | None => [] end in
      value <- mat_return (row :: old);;
      mat_set_encoded mat_tuple_encoder key value before
  end.

Definition mat_build_index_full bound terms rows :=
  mat_foldr (mat_index_add_full bound terms) rows Map.empty.

Definition mat_variable_add_full bound terms v row before :=
  key <- mat_tuple_key bound terms row;;
  match key with
  | None => mat_return before
  | Some key =>
      found <- mat_lift 104 (fun _ => 1 + length terms + mat_tuple_size row)
        rules_nested_probe_work (rules_bind_terms_counted terms row Map.empty);;
      match found with
      | None => mat_return before
      | Some binding =>
          value <- mat_lift 105 Pos.size_nat rules_nested_probe_work (rules_probe_value binding v);;
          raw <- mat_get_encoded mat_tuple_encoder key before;;
          let set := match raw with Some s => s | None => FinSet.empty end in
          next <- mat_lift 106 (fun s => 1 + Pos.size_nat value + audit_trie_nodes s)
            (audit_finset_source_work audit_basic_encoding_work)
            (audit_finset_add audit_positive_encode value set);;
          mat_set_encoded mat_tuple_encoder key next before
      end
  end.

Definition mat_build_variable_full bound terms v rows :=
  mat_foldr (mat_variable_add_full bound terms v) rows Table.empty.

(** Each counted row and variable index erases to the corresponding source operation. *)
Definition mat_index_full_erases_statement : Prop :=
  (forall bound terms row before,
    fst (mat_index_add_full bound terms row before) = index_add bound terms row before) /\
  (forall bound terms rows,
    fst (mat_build_index_full bound terms rows) = build_index bound terms rows) /\
  (forall bound terms v row before,
    fst (mat_variable_add_full bound terms v row before) =
      variable_index_add bound terms v row before) /\
  (forall bound terms v rows,
    fst (mat_build_variable_full bound terms v rows) = build_variable_index bound terms v rows).

Definition mat_index_terms_input (terms : list term) : nat :=
  fold_right (fun t n => 1 + n + match t with
    | TVar v => v
    | TConst c => Pos.size_nat c
    end) 1 terms.

Definition mat_index_rows_input (rows : list tuple) : nat :=
  fold_right (fun row n => mat_tuple_size row + n) 1 rows.

Definition mat_index_input_budget {A} (bound : FinSet.t nat) terms rows (before : Trie.t A) :=
  1000000 * Nat.pow
    (1 + audit_trie_nodes bound + mat_index_terms_input terms + mat_index_rows_input rows +
      audit_trie_nodes before) 6.

(** The row-index budget is derived from the input and current trie, not returned work. *)
Definition mat_index_full_input_bound_statement : Prop :=
  (forall bound terms row before,
    mat_work (snd (mat_index_add_full bound terms row before)) <=
      mat_index_input_budget bound terms [row] before) /\
  (forall bound terms rows,
    mat_work (snd (mat_build_index_full bound terms rows)) <=
      mat_index_input_budget bound terms rows (Map.empty : tuple_index)).

(** The variable-index budget additionally accounts for the queried variable. *)
Definition mat_variable_full_input_bound_statement : Prop :=
  (forall bound terms v row before,
    mat_work (snd (mat_variable_add_full bound terms v row before)) <=
      S v * mat_index_input_budget bound terms [row] before) /\
  (forall bound terms v rows,
    mat_work (snd (mat_build_variable_full bound terms v rows)) <=
      S v * mat_index_input_budget bound terms rows (Table.empty : variable_index)).

(** The combined claim retains both erasure and the separate phase bounds. *)
Definition mat_index_full_source_statement : Prop :=
  mat_index_full_erases_statement /\ mat_index_full_input_bound_statement /\
    mat_variable_full_input_bound_statement.
```

## Galois.Rules.RulesAuditIndexCounts

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditIndexCounts.v`.

```rocq
(** * Row-index call counts

    A fold derivation preserves the actual events of each individual source row.
    For example, a wrong-arity row has one add call and no map get or set.
    Builds on: RulesAuditIndex. *)
From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesAuditMaterializePrelude
  RulesAuditIndex.
Import List.ListNotations.

Definition mat_block_count (site : nat) (events : list mat_frame) : nat :=
  length (filter (fun event => match event with
    | MatBlock actual => Nat.eqb actual site
    | _ => false
    end) events).

Definition mat_import_count (site : nat) (events : list mat_frame) : nat :=
  length (filter (fun event => match event with
    | MatImported _ actual _ _ _ => Nat.eqb actual site
    | _ => false
    end) events).

Definition mat_index_success (bound : FinSet.t nat) (terms : list term) (row : tuple) : bool :=
  match tuple_key bound terms row with
  | Some _ => true
  | None => false
  end.

(** Chunks align with input rows; emitted events retain the actual tail-first fold order. *)
Inductive mat_index_fold_run (bound : FinSet.t nat) (terms : list term) :
    list tuple -> tuple_index -> list mat_frame -> list (list mat_frame) -> Prop :=
  | MatIndexFoldNil :
      mat_index_fold_run bound terms [] Map.empty [MatBlock 5; MatBlock 0] []
  | MatIndexFoldCons : forall row rows before out later here chunks,
      mat_index_fold_run bound terms rows before later chunks ->
      mat_index_add_full bound terms row before = (out, here) ->
      mat_index_fold_run bound terms (row :: rows) out (MatBlock 5 :: later ++ here)
        (here :: chunks).

(** Each row performs one key computation; successful keys perform one get, one set and two
  encodings. *)
Definition mat_index_row_counts_statement : Prop :=
  forall bound terms row before,
    let '(_, events) := mat_index_add_full bound terms row before in
    mat_import_count 10 events = (if mat_index_success bound terms row then 1 else 0) /\
    mat_import_count 11 events = (if mat_index_success bound terms row then 1 else 0) /\
    mat_import_count 100 events = (if mat_index_success bound terms row then 2 else 0).

(** The whole fold has m+1 entries and m actual row calls, including duplicates and failures. *)
Definition mat_index_fold_counts_statement : Prop :=
  forall bound terms rows,
    let '(out, events) := mat_build_index_full bound terms rows in
    exists chunks, mat_index_fold_run bound terms rows out events chunks /\
      length chunks = length rows /\ mat_block_count 5 events = S (length rows) /\
      mat_import_count 10 events = length (filter (mat_index_success bound terms) rows) /\
      mat_import_count 11 events = length (filter (mat_index_success bound terms) rows) /\
      mat_import_count 100 events = 2 * length (filter (mat_index_success bound terms) rows).

(** A row derivation retains exactly its one key computation and its selected map branch. *)
Inductive mat_index_add_run (bound : FinSet.t nat) (terms : list term) (row : tuple)
    (before : tuple_index) : tuple_index -> list mat_frame -> Prop :=
  | MatIndexAddNoKey : forall key_events,
      mat_tuple_key bound terms row = (None, key_events) ->
      mat_index_add_run bound terms row before before (key_events ++ [MatBlock 0])
  | MatIndexAddKey : forall key key_events raw get_events old out set_events,
      mat_tuple_key bound terms row = (Some key, key_events) ->
      mat_get_encoded mat_tuple_encoder key before = (raw, get_events) ->
      old = (match raw with Some rows => rows | None => [] end) ->
      mat_set_encoded mat_tuple_encoder key (row :: old) before = (out, set_events) ->
      mat_index_add_run bound terms row before out
        (key_events ++ get_events ++ [MatBlock 0] ++ set_events).

(** Every actual row subrun has the corresponding single-key derivation. *)
Definition mat_index_add_run_total_statement : Prop :=
  forall bound terms row before,
    let '(out, events) := mat_index_add_full bound terms row before in
    mat_index_add_run bound terms row before out events.
```

## Galois.Rules.RulesAuditJoin

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditJoin.v`.

```rocq
(** * Complete indexed rule firing account

    The selected strategy's actual bindings feed one negative, universe and output pipeline.
    For example, both strategies retain their own preparation while sharing the same tail model.
    Builds on: RulesAuditNestedSelection, RulesAuditMultiwaySelection and
  RulesAuditFiringCallbacks. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin
  RulesAuditPrepareCallbacks RulesAuditRelationCallbacks RulesAuditTerminalCallbacks
  RulesAuditNestedSelection RulesAuditMultiwaySelection RulesAuditFiring RulesAuditFiringCallbacks.
Import List.ListNotations.

Inductive rules_selection_capture (P : Type) :=
  | RulesNestedCapture (run : rules_nested_selection_run P)
  | RulesMultiwayCapture (run : rules_multiway_selection_run P).
Arguments RulesNestedCapture {P} _.
Arguments RulesMultiwayCapture {P} _.

Definition rules_select_capture {P} (strategy : join_strategy) (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : rules_selection_capture P :=
  match strategy with
  | IndexedNested => RulesNestedCapture (rules_selected_nested_capture prog r env)
  | IndexedMultiway => RulesMultiwayCapture (rules_selected_multiway_capture prog r env)
  end.

Definition rules_selection_result {P} (run : rules_selection_capture P) : list binding :=
  match run with
  | RulesNestedCapture nested => rules_nested_selection_result nested
  | RulesMultiwayCapture multiway => rules_multiway_selection_result multiway
  end.

Definition rules_selection_work {P} (run : rules_selection_capture P) : nat :=
  match run with
  | RulesNestedCapture nested => rules_nested_selection_work nested
  | RulesMultiwayCapture multiway => rules_multiway_selection_work multiway
  end.

Definition rules_selection_input_budget {P} (strategy : join_strategy) (prog : program P)
    (r : rule P) (env : P -> FinSet.t tuple) : nat :=
  match strategy with
  | IndexedNested => rules_nested_selection_input_budget prog r env
  | IndexedMultiway => rules_multiway_selection_input_budget prog r env
  end.

Record rules_join_firing_run (P : Type) := RulesJoinFiringRun {
  rules_join_firing_selection : rules_selection_capture P;
  rules_join_firing_tail : rules_firing_tail_run P
}.
Arguments rules_join_firing_selection {P} _.
Arguments rules_join_firing_tail {P} _.

Definition rules_join_firing_capture {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
    rules_join_firing_run P :=
  let selection := rules_select_capture strategy prog r env in
  let tail := rules_firing_tail_capture prog facts r env (rules_selection_result selection) in
  RulesJoinFiringRun P selection tail.

Definition rules_join_firing_work {P} (run : rules_join_firing_run P) : nat :=
  1 + rules_selection_work (rules_join_firing_selection run) +
    rules_firing_tail_work (rules_join_firing_tail run).

Definition rules_join_firing_input_budget {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple)
    (selected : list binding) : nat :=
  1 + rules_selection_input_budget strategy prog r env +
    rules_firing_tail_input_budget prog facts r selected.

(** The selected run returns the original firing output with a same-intermediate allowance. *)
Definition rules_join_firing_input_bound_statement : Prop :=
  forall P strategy (prog : program P) facts r env,
    let run := rules_join_firing_capture strategy prog facts r env in
    rules_firing_tail_result (rules_join_firing_tail run) = fire_rule_join strategy prog facts r
  env /\
    rules_join_firing_work run <= rules_join_firing_input_budget strategy prog facts r env
      (rules_selection_result (rules_join_firing_selection run)).

Definition rules_flat_body_work {B} (weight : B -> nat) (bodies : list (list B)) : nat :=
  fold_right (fun body n => fold_right (fun item total => weight item + total) 0 body + n) 0 bodies.

Definition rules_selection_receipt_source {P B} (E : encoding P)
    (pred_source : P -> positive -> list B -> Prop) (env_source : P -> FinSet.t tuple -> list B
  -> Prop)
    (run : rules_selection_capture P) (bodies : list (list B)) : Prop :=
  match run with
  | RulesNestedCapture nested => exists relation_bodies prepare_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_nested_selection_relation_events nested) relation_bodies /\
      rules_predicate_trace_source E pred_source
        (rules_nested_selection_prepare_events nested) prepare_bodies /\
      bodies = concat relation_bodies ++ concat prepare_bodies
  | RulesMultiwayCapture multiway => exists relation_bodies prepare_bodies terminal_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_multiway_selection_relation_events multiway) relation_bodies /\
      rules_predicate_trace_source E pred_source
        (rules_multiway_selection_prepare_events multiway) prepare_bodies /\
      rules_positive_filter_source env_source
        (rules_multiway_selection_terminal_events multiway) terminal_bodies /\
      bodies = concat relation_bodies ++ concat prepare_bodies ++ concat (concat terminal_bodies)
  end.

Definition rules_tail_receipt_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (arity_source : P -> nat -> list B -> Prop)
    (run : rules_firing_tail_run P) (bodies : list (list B)) : Prop :=
  exists negative_bodies universe_bodies,
    rules_negative_filter_source env_source (rules_firing_tail_negative_events run)
  negative_bodies /\
    rules_universe_trace_source pred_source arity_source
      (rules_firing_tail_universe_events run) universe_bodies /\
    bodies = concat (concat negative_bodies) ++ concat universe_bodies.

Definition rules_selection_external_budget {P} (prog : program P) (r : rule P)
    (pred_bound env_bound : P -> nat) (run : rules_selection_capture P) : nat :=
  let atoms := positive_atoms (body r) in
  rules_relation_external_input_budget (penc prog) atoms pred_bound env_bound +
  match run with
  | RulesNestedCapture _ => rules_predicate_input_budget pred_bound atoms
  | RulesMultiwayCapture multiway =>
      length (join_variables atoms) * rules_predicate_input_budget pred_bound atoms +
        length (rules_multiway_selection_candidates multiway) *
          rules_predicate_input_budget env_bound atoms
  end.

(** The complete firing run retains the exact external body of every invocation. *)
Definition rules_join_firing_source_statement : Prop :=
  forall P B strategy (prog : program P) facts (r : rule P) (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop)
    (arity_source : P -> nat -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound arity_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    rules_arity_source_laws prog arity_source weight arity_bound ->
    let run := rules_join_firing_capture strategy prog facts r env in
    let selected := rules_join_firing_selection run in
    let tail := rules_join_firing_tail run in
    exists selection_bodies tail_bodies,
      rules_selection_receipt_source (penc prog) pred_source env_source selected selection_bodies /\
      rules_tail_receipt_source pred_source env_source arity_source tail tail_bodies /\
      rules_firing_tail_result tail = fire_rule_join strategy prog facts r env /\
      rules_join_firing_work run + rules_flat_body_work weight selection_bodies +
        rules_flat_body_work weight tail_bodies <=
        rules_join_firing_input_budget strategy prog facts r env (rules_selection_result selected) +
          rules_selection_external_budget prog r pred_bound env_bound selected +
          length (rules_selection_result selected) * rules_negative_input_budget env_bound r +
          rules_universe_external_input_budget prog facts (pred (head r)) pred_bound arity_bound.

(** Both existing strategies agree on final tuple membership under the original premises. *)
Definition rules_join_agrees : Prop :=
  forall P (prog : program P) (facts : list (ground_atom P)) (r : rule P)
    (env : P -> FinSet.t tuple),
    program_wf prog facts -> List.In r (rules prog) -> env_wf prog env ->
    forall ts,
      FinSet.mem tuple_encoding ts (fire_rule_join IndexedNested prog facts r env) = true <->
      FinSet.mem tuple_encoding ts (fire_rule_join IndexedMultiway prog facts r env) = true.
```

## Galois.Rules.RulesAuditJoinSyntax

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditJoinSyntax.v`.

```rocq
(** * Join syntax and variable preparation

    These source mirrors retain list, set and union work before index preparation.
    For example, repeated variables cause repeated insertion before set enumeration.
    Builds on: RulesAuditMaterializePrelude and RulesCompile. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditEncoding
  CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude.
Import List.ListNotations.

Definition mat_term_vars (t : term) : mat_run (list nat) :=
  mat_mark 41 (match t with
    | TVar v => mat_return [v]
    | TConst _ => mat_return []
    end).

Definition mat_atom_vars {P} (a : atom P) : mat_run (list nat) :=
  mat_flatmap mat_term_vars (args a).

Definition mat_bound_add {P} (bound : FinSet.t nat) (a : atom P) : mat_run (FinSet.t nat) :=
  variables <- mat_atom_vars a;;
  vars <- mat_of_list audit_nat_encode audit_nat_events_work variables;;
  mat_union bound vars.

Definition mat_positive_literal {P} (item : literal P) : mat_run (list (atom P)) :=
  mat_mark 42 (match item with
    | LPos a => mat_return [a]
    | LNeg _ => mat_return []
    end).

Definition mat_positive_atoms {P} (items : list (literal P)) : mat_run (list (atom P)) :=
  mat_flatmap mat_positive_literal items.

Definition mat_join_variables {P} (atoms : list (atom P)) : mat_run (list nat) :=
  variables <- mat_flatmap mat_atom_vars atoms;;
  vars <- mat_of_list audit_nat_encode audit_nat_events_work variables;;
  mat_elements vars.

Definition mat_has_variable {P} (v : nat) (a : atom P) : mat_run bool :=
  variables <- mat_atom_vars a;;
  vars <- mat_of_list audit_nat_encode audit_nat_events_work variables;;
  mat_lift 43 (fun _ => 1 + v + mat_set_size vars)
    (audit_finset_source_work audit_nat_events_work) (audit_finset_mem audit_nat_encode v vars).

Definition mat_atoms_with {P} (v : nat) (atoms : list (atom P)) : mat_run (list (atom P)) :=
  mat_filter (mat_has_variable v) atoms.

(** Each syntax helper returns the value of the corresponding original source operation. *)
Definition mat_join_syntax_erasure_statement : Prop :=
  (forall P (a : atom P), fst (mat_atom_vars a) = atom_vars a) /\
  (forall P bound (a : atom P), fst (mat_bound_add bound a) = bound_add bound a) /\
  (forall P (items : list (literal P)), fst (mat_positive_atoms items) = positive_atoms items) /\
  (forall P (atoms : list (atom P)), fst (mat_join_variables atoms) = join_variables atoms) /\
  (forall P v (atoms : list (atom P)), fst (mat_atoms_with v atoms) = atoms_with_variable v atoms).
```

## Galois.Rules.RulesAuditMaterializeAdapters

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditMaterializeAdapters.v`.

```rocq
(** * Shared Rules materialization adapters

    The adapters retain actual predicate encoder calls and imported atom-fold subruns.
    For example, inserting a ground atom emits separate read and write encoder receipts.
    Builds on: RulesAuditMaterializePrelude, RulesAuditRelations and RulesAuditAtomFold. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta
  RulesAuditMaterializePrelude RulesAuditRelations RulesAuditAtomFold RulesAuditNestedProbe.
Import List.ListNotations.

Definition mat_ground_encoder {P} (prog : program P) :=
  audit_pair_encode (rules_encoder (penc prog)) (audit_list_encode audit_positive_encode).

Definition mat_ground_encoding_work {P}
    (events : list (audit_pair_event P tuple (rules_encode_entry P)
      (audit_list_event positive (audit_basic_encoding_event positive)))) :=
  audit_pair_events_work (@length (rules_encode_entry P))
    (audit_list_events_work audit_basic_encoding_work) events.

Definition mat_ground_calls {P} (prog : program P)
    (events : list (audit_set_event (ground_atom P) (audit_pair_event P tuple
      (rules_encode_entry P) (audit_list_event positive (audit_basic_encoding_event positive))))) :
    list mat_frame :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ encoded _ => flat_map (fun pair => match pair with
        | AuditPairFirst p code _ => [MatEncode P (penc prog) p code]
        | _ => []
        end) encoded
    | _ => []
    end) events.

Definition mat_ground_set {P} (prog : program P) (xs : list (ground_atom P)) :=
  let '(out, events) := audit_finset_of_list (mat_ground_encoder prog) xs in
  (out, MatImported _ 13 (out, events)
    (audit_finset_source_work (@mat_ground_encoding_work P) events)
    (1 + length xs + audit_trie_nodes out) :: mat_ground_calls prog events).

Definition mat_atom_calls {P} (prog : program P) (events : list (rules_atom_full_event P)) :
    list mat_frame :=
  flat_map (fun event => match event with
    | RafRelationGet p code _ _ _ | RafRelationSet p _ code _ _ _ =>
        [MatEncode P (penc prog) p code]
    | _ => []
    end) events.

Definition mat_atom_fold {P} (prog : program P) atoms db :=
  let '(out, events) := rules_atom_fold_counted prog atoms db in
  (out, MatImported _ 17 (out, events) (rules_atom_full_work events) (mat_db_size out) ::
    mat_atom_calls prog events).

Definition mat_index {P} (prog : program P) set :=
  let '(out, events) := rules_delta_index_counted prog set in
  (out, MatImported _ 18 (out, events) (rules_atom_full_work events) (mat_db_size out) ::
    mat_atom_calls prog events).

Definition mat_instantiate (b : binding) (ts : list term) :=
  mat_lift 27 mat_tuple_size rules_nested_probe_work (rules_probe_instantiate b ts).

Definition mat_tagged_encoder {P} (prog : program P) (q : P * bool) :=
  let '(out, events) := audit_pair_encode (rules_encoder (penc prog)) audit_bool_encode q in
  (out, MatImported _ 28 (out, events)
    (audit_pair_events_work (@length (rules_encode_entry P)) audit_basic_encoding_work events)
    (Pos.size_nat out) ::
    flat_map (fun event => match event with
      | AuditPairFirst p code _ => [MatEncode P (penc prog) p code]
      | _ => []
      end) events).
```

## Galois.Rules.RulesAuditMaterializePrelude

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditMaterializePrelude.v`.

```rocq
(** * Materialization source-accounting foundation

    These mathematical writers retain fixed source frames and actual collection subruns.
    For example, a counted map lookup retains its key, encoded key and trie trace.
    Builds on: RulesSyntax, RulesStratify and the shared collection audit models. *)
From Stdlib Require Import List NArith PArith ZArith Bool Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsTable CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditUnion.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
Import List.ListNotations.

Inductive mat_frame : Type :=
  | MatBlock (site : nat)
  | MatNat (site lhs rhs : nat)
  | MatEncode : forall Q, encoding Q -> Q -> positive -> mat_frame
  | MatLevel : forall P, stratification P -> P -> nat -> mat_frame
  | MatArity : forall P, program P -> P -> nat -> mat_frame
  | MatOperand (size : nat)
  | MatChild (site work operand_size : nat)
  | MatImported : forall T, nat -> T -> nat -> nat -> mat_frame.

Definition mat_frame_work (e : mat_frame) : nat :=
  match e with
  | MatBlock _ => 100
  | MatNat _ a b => 1 + a + b
  | MatEncode _ _ _ _ | MatLevel _ _ _ _ | MatArity _ _ _ _ => 1
  | MatOperand _ => 0
  | MatChild _ work _ | MatImported _ _ _ work _ => work
  end.

Definition mat_work (trace : list mat_frame) : nat :=
  fold_right (fun e n => mat_frame_work e + n) 0 trace.

Definition mat_width (trace : list mat_frame) : nat :=
  fold_right (fun e n => Nat.max n (match e with
    | MatNat _ a b => 1 + a + b
    | MatEncode _ _ _ code => Pos.size_nat code
    | MatLevel _ _ _ value | MatArity _ _ _ value => S value
    | MatOperand size | MatChild _ _ size | MatImported _ _ _ _ size => size
    | _ => 1
    end)) 1 trace.

Definition mat_run (A : Type) : Type := A * list mat_frame.

Definition mat_return {A} (a : A) : mat_run A := (a, [MatBlock 0]).

Definition mat_bind {A B} (r : mat_run A) (f : A -> mat_run B) : mat_run B :=
  let '(a, first) := r in
  let '(b, second) := f a in
  (b, first ++ second).

Notation "x <- r ;; body" := (mat_bind r (fun x => body))
  (at level 100, r at next level, right associativity).

Definition mat_mark {A} (site : nat) (r : mat_run A) : mat_run A :=
  (fst r, MatBlock site :: snd r).

Definition mat_lift {A E} (site : nat) (size : A -> nat) (work : list E -> nat)
    (r : A * list E) : mat_run A :=
  let '(a, events) := r in
  (a, [MatImported (A * list E) site (a, events) (work events) (size a)]).

Definition mat_emit (e : mat_frame) : mat_run unit := (tt, [e]).

Fixpoint mat_map {A B} (f : A -> mat_run B) (xs : list A) : mat_run (list B) :=
  mat_mark 1 (match xs with
    | [] => mat_return []
    | x :: rest => y <- f x;; ys <- mat_map f rest;; mat_return (y :: ys)
    end).

Fixpoint mat_append {A} (xs ys : list A) : mat_run (list A) :=
  mat_mark 2 (match xs with
    | [] => mat_return ys
    | x :: rest => tail <- mat_append rest ys;; mat_return (x :: tail)
    end).

Fixpoint mat_flatmap {A B} (f : A -> mat_run (list B)) (xs : list A) : mat_run (list B) :=
  mat_mark 3 (match xs with
    | [] => mat_return []
    | x :: rest => first <- f x;; later <- mat_flatmap f rest;; mat_append first later
    end).

Fixpoint mat_filter {A} (f : A -> mat_run bool) (xs : list A) : mat_run (list A) :=
  mat_mark 4 (match xs with
    | [] => mat_return []
    | x :: rest => keep <- f x;; tail <- mat_filter f rest;;
        mat_return (if keep then x :: tail else tail)
    end).

Fixpoint mat_foldr {A B} (f : A -> B -> mat_run B) (xs : list A) (initial : B) : mat_run B :=
  mat_mark 5 (match xs with
    | [] => mat_return initial
    | x :: rest => before <- mat_foldr f rest initial;; f x before
    end).

Fixpoint mat_foldl {A B} (f : B -> A -> mat_run B) (xs : list A) (initial : B) : mat_run B :=
  mat_mark 6 (match xs with
    | [] => mat_return initial
    | x :: rest => next <- f initial x;; mat_foldl f rest next
    end).

Fixpoint mat_all {A} (f : A -> mat_run bool) (xs : list A) : mat_run bool :=
  mat_mark 7 (match xs with
    | [] => mat_return true
    | x :: rest => first <- f x;; later <- mat_all f rest;; mat_return (first && later)
    end).

Definition mat_encode {Q} (E : encoding Q) (q : Q) : mat_run positive :=
  let code := encode E q in (code, [MatEncode Q E q code]).

Inductive mat_level_context (P : Type) : Type :=
  | MatExternalLevels (st : stratification P)
  | MatCapturedLevels (E : encoding P) (levels : Map.t P nat) (bound : nat).
Arguments MatExternalLevels {P} _.
Arguments MatCapturedLevels {P} _ _ _.

Definition mat_native_levels {P} (st : mat_level_context P) : stratification P :=
  match st with
  | MatExternalLevels native => native
  | MatCapturedLevels E levels bound => Stratification (level_at E levels) bound
  end.

Definition mat_arity {P} (prog : program P) (p : P) : mat_run nat :=
  let n := arity prog p in (n, [MatArity P prog p n]).

Definition mat_nat (site : nat) (f : nat -> nat -> nat) (a b : nat) : mat_run nat :=
  (f a b, [MatNat site a b]).

Definition mat_nat_test (site : nat) (f : nat -> nat -> bool) (a b : nat) : mat_run bool :=
  (f a b, [MatNat site a b]).

Definition mat_tuple_size (row : tuple) : nat :=
  fold_right (fun p n => 1 + Pos.size_nat p + n) 1 row.

Definition mat_set_size {Q} (s : FinSet.t Q) : nat := audit_trie_nodes s.

Definition mat_db_size {P} (db : database P) : nat :=
  1 + audit_trie_nodes db +
  fold_right (fun entry n => audit_trie_nodes (snd entry) + n) 0 (Map.elements db).

Definition mat_get {Q A} (E : encoding Q) (key : Q) (input : Map.t Q A) : mat_run (option A) :=
  code <- mat_encode E key;;
  let '(out, events) := audit_map_code_get code input in
  (out, [MatImported _ 10 (key, code, input, out, events)
    (audit_trie_get_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes input)]).

Definition mat_level {P} (st : mat_level_context P) (p : P) : mat_run nat :=
  match st with
  | MatExternalLevels native => let n := level native p in (n, [MatLevel P native p n])
  | MatCapturedLevels E levels _ =>
      found <- mat_get E p levels;;
      mat_return (match found with Some n => n | None => 0 end)
  end.

Definition mat_set {Q A} (E : encoding Q) (key : Q) (value : A) (input : Map.t Q A) :
    mat_run (Map.t Q A) :=
  code <- mat_encode E key;;
  let '(out, events) := audit_trie_set code (key, value) input in
  (out, [MatImported _ 11 (key, code, value, input, out, events)
    (audit_trie_update_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes out)]).

Definition mat_rel {P} (prog : program P) (db : database P) (p : P) : mat_run (FinSet.t tuple) :=
  found <- mat_get (penc prog) p db;;
  mat_return (match found with Some s => s | None => FinSet.empty end).

Definition mat_elements {Q} (s : FinSet.t Q) : mat_run (list Q) :=
  mat_lift 12 (fun xs => 1 + length xs + audit_trie_nodes s)
    audit_set_elements_work (audit_finset_elements s).

Definition mat_of_list {Q E} (enc : Q -> positive * list E) (ew : list E -> nat) (xs : list Q) :=
  mat_lift 13 (fun s => 1 + length xs + audit_trie_nodes s)
    (audit_finset_source_work ew) (audit_finset_of_list enc xs).

Definition mat_tuple_mem (row : tuple) (s : FinSet.t tuple) :=
  mat_lift 14 (fun _ => 1 + mat_tuple_size row + audit_trie_nodes s)
    (audit_finset_source_work (audit_list_events_work audit_basic_encoding_work))
    (audit_finset_mem (audit_list_encode audit_positive_encode) row s).

Definition mat_union {Q} (a b : FinSet.t Q) :=
  mat_lift 15 (fun s => 1 + audit_trie_nodes a + audit_trie_nodes b + audit_trie_nodes s)
    audit_finset_union_source_work (audit_finset_union a b).

Definition mat_nat_add (v : nat) (s : FinSet.t nat) :=
  mat_lift 16 (fun out => 1 + v + audit_trie_nodes s + audit_trie_nodes out)
    (audit_finset_source_work audit_nat_events_work) (audit_finset_add audit_nat_encode v s).

Definition mat_get_encoded {Q A} (enc : Q -> mat_run positive) (key : Q) (input : Map.t Q A) :=
  code <- enc key;;
  let '(out, events) := audit_map_code_get code input in
  (out, [MatImported _ 10 (key, code, input, out, events)
    (audit_trie_get_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes input)]).

Definition mat_set_encoded {Q A} (enc : Q -> mat_run positive) (key : Q) (value : A)
    (input : Map.t Q A) :=
  code <- enc key;;
  let '(out, events) := audit_trie_set code (key, value) input in
  (out, [MatImported _ 11 (key, code, value, input, out, events)
    (audit_trie_update_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes out)]).

Definition mat_predicate_set_encoded {Q} (enc : Q -> mat_run positive) (keys : list Q) :=
  mat_foldl (fun set key => mat_set_encoded enc key tt set) keys Map.empty.
```

## Galois.Rules.RulesAuditMultiwayPrepare

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditMultiwayPrepare.v`.

```rocq
(** Multiway preparation using actual variable-index primitive subruns.
    Predicate encoder execution is a separate external source adapter. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Rules Require Import RulesAuditMaterializePrelude RulesAuditIndex RulesAuditJoinSyntax.
Import List.ListNotations.
Fixpoint rules_variable_map_full {P} (E : encoding P) (relations : Map.t P (list tuple))
    (bound : FinSet.t nat) (v : nat) (atoms : list (atom P)) : mat_run (list variable_search) :=
  mat_mark 221 (match atoms with
  | [] => mat_return []
  | a :: rest =>
      raw <- mat_get E (pred a) relations;;
      let rows := match raw with Some found => found | None => [] end in
      index <- mat_build_variable_full bound (args a) v rows;;
      tail <- rules_variable_map_full E relations bound v rest;;
      mat_return (VariableSearch (args a) index :: tail)
  end).
Definition rules_prepare_variable_full {P} (E : encoding P) (relations : Map.t P (list tuple))
    (bound : FinSet.t nat) (v : nat) (atoms : list (atom P)) : mat_run (list variable_search) :=
  selected <- mat_atoms_with v atoms;;
  rules_variable_map_full E relations bound v selected.
Fixpoint rules_prepare_multiway_full {P} (E : encoding P) (relations : Map.t P (list tuple))
    (vars : list nat) (bound : FinSet.t nat) (atoms : list (atom P)) : mat_run (list
  multiway_search) :=
  mat_mark 222 (match vars with
  | [] => mat_return []
  | v :: rest =>
      domains <- rules_prepare_variable_full E relations bound v atoms;;
      next <- mat_nat_add v bound;;
      tail <- rules_prepare_multiway_full E relations rest next atoms;;
      mat_return (MultiwaySearch v bound domains :: tail)
  end).
Definition rules_prepare_multiway_full_erases_statement : Prop :=
  forall P (E : encoding P) relations vars bound atoms,
    fst (rules_prepare_multiway_full E relations vars bound atoms) =
      prepare_multiway vars bound atoms (join_relation_rows E relations).
```

## Galois.Rules.RulesAuditMultiwayProbe

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditMultiwayProbe.v`.

```rocq
(** * Counted multiway candidate intersection and enumeration

    The model retains each table lookup, concrete shared set intersection and each value
    binding in the original order. Empty intersections still execute the remaining probes.
    Builds on RulesJoin and the frozen collection intersection model. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditElements CollectionsAuditInter.
From Galois.Rules Require Import RulesAuditNestedProbe.
Import List.ListNotations.

Inductive rules_multi_probe_event : Type :=
  | RmProbeKey (events : list rules_nested_probe_event)
  | RmTableGet (key : tuple) (code : positive) (input : variable_index)
      (raw : option (FinSet.t positive))
      (encoding_body : list (audit_list_event positive (audit_basic_encoding_event positive)))
      (body : audit_trace (audit_trie_call (tuple * FinSet.t positive)))
  | RmIntersect (lhs rhs out : FinSet.t positive) (body : list (audit_inter_event positive))
  | RmElements (input : FinSet.t positive) (values : list positive)
      (body : list (audit_set_elements_event positive))
  | RmBind (events : list rules_nested_probe_event)
  | RmAppend (size : nat)
  | RmCase (site : nat).

Definition rules_variable_probe_counted (bound : FinSet.t nat) (b : binding)
    (search : variable_search) : FinSet.t positive * list rules_multi_probe_event :=
  let '(key, key_events) := rules_bound_key_counted bound b (variable_terms search) in
  let '(code, encoding_body) := audit_list_encode audit_positive_encode key in
  let '(raw, get_events) := audit_map_code_get code (variable_table search) in
  (match raw with Some result => result | None => FinSet.empty end,
   [RmProbeKey key_events; RmTableGet key code (variable_table search) raw encoding_body get_events;
    RmCase 0]).

Fixpoint rules_intersect_domains_counted (bound : FinSet.t nat) (b : binding)
    (first : FinSet.t positive) (searches : list variable_search) :
    FinSet.t positive * list rules_multi_probe_event :=
  match searches with
  | [] => (first, [RmCase 1])
  | search :: rest =>
      let '(next, probe_events) := rules_variable_probe_counted bound b search in
      let '(intersection, inter_events) := audit_finset_inter first next in
      let '(out, tail) := rules_intersect_domains_counted bound b intersection rest in
      (out, RmCase 1 :: probe_events ++ RmIntersect first next intersection inter_events :: tail)
  end.

Definition rules_variable_candidates_counted (bound : FinSet.t nat) (b : binding)
    (searches : list variable_search) : FinSet.t positive * list rules_multi_probe_event :=
  match searches with
  | [] => (FinSet.empty, [RmCase 2])
  | search :: rest =>
      let '(first, probe_events) := rules_variable_probe_counted bound b search in
      let '(out, later) := rules_intersect_domains_counted bound b first rest in
      (out, RmCase 2 :: probe_events ++ later)
  end.

Fixpoint rules_multiway_values_counted (v : nat) (b : binding) (values : list positive) :
    list binding * list rules_multi_probe_event :=
  match values with
  | [] => ([], [RmCase 3])
  | value :: rest =>
      let '(candidate, bind_events) := rules_bind_term_counted b (TVar v) value in
      let head := match candidate with Some result => [result] | None => [] end in
      let '(tail, events) := rules_multiway_values_counted v b rest in
      (head ++ tail, RmCase 3 :: RmBind bind_events :: RmCase 4 :: events ++ [RmAppend (length
  head)])
  end.

Fixpoint rules_multiway_bindings_counted (search : multiway_search) (bindings : list binding) :
    list binding * list rules_multi_probe_event :=
  match bindings with
  | [] => ([], [RmCase 5])
  | b :: rest =>
      let '(set, candidate_events) := rules_variable_candidates_counted
        (multiway_bound search) b (multiway_domains search) in
      let '(values, element_events) := audit_finset_elements set in
      let '(head, value_events) := rules_multiway_values_counted (multiway_variable search) b
  values in
      let '(tail, tail_events) := rules_multiway_bindings_counted search rest in
      (head ++ tail, RmCase 5 :: candidate_events ++ RmElements set values element_events ::
        value_events ++ tail_events ++ [RmAppend (length head)])
  end.

Fixpoint rules_run_multiway_counted (searches : list multiway_search) (bindings : list binding) :
    list binding * list rules_multi_probe_event :=
  match searches with
  | [] => (bindings, [RmCase 6])
  | search :: rest =>
      let '(next, first) := rules_multiway_bindings_counted search bindings in
      let '(out, tail) := rules_run_multiway_counted rest next in
      (out, RmCase 6 :: first ++ tail)
  end.

Definition rules_multiway_probe_erasure_statement : Prop :=
  (forall bound b search, fst (rules_variable_probe_counted bound b search) = variable_probe
  bound b search) /\
  (forall bound b first searches, fst (rules_intersect_domains_counted bound b first searches) =
    intersect_variable_domains bound b first searches) /\
  (forall bound b searches, fst (rules_variable_candidates_counted bound b searches) =
    variable_candidates bound b searches) /\
  (forall search bindings, fst (rules_multiway_bindings_counted search bindings) =
    multiway_step search bindings) /\
  (forall searches bindings, fst (rules_run_multiway_counted searches bindings) =
    run_multiway searches bindings).

Definition rules_multi_probe_event_work (event : rules_multi_probe_event) : nat :=
  match event with
  | RmProbeKey events | RmBind events => rules_nested_probe_work events
  | RmTableGet _ _ _ _ encoding_body body =>
      1 + audit_list_events_work audit_basic_encoding_work encoding_body +
        audit_trie_get_trace_source_work body
  | RmIntersect _ _ _ body => audit_finset_inter_source_work body
  | RmElements _ _ body => audit_set_elements_work body
  | RmAppend size => 1 + size
  | RmCase _ => 1
  end.
Definition rules_multi_probe_event_budget (event : rules_multi_probe_event) : nat :=
  match event with
  | RmProbeKey events | RmBind events => rules_nested_probe_budget events
  | RmTableGet key code _ _ _ _ =>
      10 + 10 * length key + 20 * audit_encoded_bits audit_positive_encode key + 5 *
  Pos.size_nat code
  | RmIntersect lhs rhs _ _ => 2 + 30 * (audit_trie_nodes lhs + audit_trie_nodes rhs)
  | RmElements set _ _ => 6 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | RmAppend size => 1 + size
  | RmCase _ => 1
  end.
Definition rules_multi_probe_work (events : list rules_multi_probe_event) : nat :=
  fold_right (fun event n => rules_multi_probe_event_work event + n) 0 events.
Definition rules_multi_probe_budget (events : list rules_multi_probe_event) : nat :=
  fold_right (fun event n => rules_multi_probe_event_budget event + n) 0 events.
Definition rules_run_multiway_selected_cost_statement : Prop :=
  forall searches bindings,
    let '(out, events) := rules_run_multiway_counted searches bindings in
    out = run_multiway searches bindings /\
    rules_multi_probe_work events <= rules_multi_probe_budget events.
```

## Galois.Rules.RulesAuditMultiwaySelection

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditMultiwaySelection.v`.

```rocq
(** * Whole indexed-multiway binding selection

    One relation snapshot feeds variable indexes, intersections and strict positive filtering.
    For example, each candidate binding invokes every positive environment test.
    Builds on: RulesAuditMultiwayPrepare, RulesAuditMultiwayProbe and terminal callbacks. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditJoinSyntax RulesAuditRelations RulesAuditRelationCallbacks RulesAuditMultiwayPrepare
  RulesAuditMultiwayProbe RulesAuditTerminal RulesAuditTerminalCallbacks RulesAuditPrepareCallbacks
  RulesAuditNestedSelection.
Import List.ListNotations.

Record rules_multiway_selection_run (P : Type) := RulesMultiwaySelectionRun {
  rules_multiway_selection_result : list binding;
  rules_multiway_selection_candidates : list binding;
  rules_multiway_selection_atoms : list (atom P);
  rules_multiway_selection_atom_events : list mat_frame;
  rules_multiway_selection_relation_events : list (rules_relation_event P);
  rules_multiway_selection_variable_events : list mat_frame;
  rules_multiway_selection_prepare_events : list mat_frame;
  rules_multiway_selection_probe_events : list rules_multi_probe_event;
  rules_multiway_selection_terminal_events : list (list (rules_terminal_event P))
}.
Arguments rules_multiway_selection_result {P} _.
Arguments rules_multiway_selection_candidates {P} _.
Arguments rules_multiway_selection_atoms {P} _.
Arguments rules_multiway_selection_atom_events {P} _.
Arguments rules_multiway_selection_relation_events {P} _.
Arguments rules_multiway_selection_variable_events {P} _.
Arguments rules_multiway_selection_prepare_events {P} _.
Arguments rules_multiway_selection_probe_events {P} _.
Arguments rules_multiway_selection_terminal_events {P} _.

Definition rules_selected_multiway_capture {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : rules_multiway_selection_run P :=
  let '(atoms, atom_events) := mat_positive_atoms (body r) in
  let '(relations, relation_events) := rules_join_relations_counted (penc prog) atoms env in
  let '(vars, var_events) := mat_join_variables atoms in
  let '(searches, prepare_events) :=
    rules_prepare_multiway_full (penc prog) relations vars FinSet.empty atoms in
  let '(candidates, probe_events) := rules_run_multiway_counted searches [Map.empty] in
  let '(result, terminal_events) := rules_positive_filter_capture atoms env candidates in
  RulesMultiwaySelectionRun P result candidates atoms atom_events relation_events var_events
    prepare_events probe_events terminal_events.

Definition rules_multiway_selection_work {P} (run : rules_multiway_selection_run P) : nat :=
  mat_work (rules_multiway_selection_atom_events run) +
    rules_relation_work (rules_multiway_selection_relation_events run) +
    mat_work (rules_multiway_selection_variable_events run) +
    mat_work (rules_multiway_selection_prepare_events run) +
    rules_multi_probe_work (rules_multiway_selection_probe_events run) +
    rules_positive_filter_work (rules_multiway_selection_terminal_events run) + 1.

Definition rules_multiway_selection_input_budget {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : nat :=
  let atoms := positive_atoms (body r) in
  1000000000 * Nat.pow (rules_nested_selection_input_size prog r env)
    (32 + 4 * length atoms + 4 * length (join_variables atoms)).

(** Same-run terminal groups correspond exactly to the actual candidate bindings. *)
Definition rules_multiway_selection_count_statement : Prop :=
  forall P (prog : program P) r env,
    let run := rules_selected_multiway_capture prog r env in
    length (rules_multiway_selection_terminal_events run) =
      length (rules_multiway_selection_candidates run).

(** The captured multiway selection returns the native result within the input allowance. *)
Definition rules_multiway_selection_input_bound_statement : Prop :=
  forall P (prog : program P) r env,
    let run := rules_selected_multiway_capture prog r env in
    rules_multiway_selection_result run = selected_bindings IndexedMultiway prog r env /\
    rules_multiway_selection_work run <= rules_multiway_selection_input_budget prog r env.

(** The relation, variable preparation and terminal filter retain every external callback body. *)
Definition rules_multiway_selection_source_statement : Prop :=
  forall P B (prog : program P) r (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    let run := rules_selected_multiway_capture prog r env in
    exists relation_bodies prepare_bodies terminal_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_multiway_selection_relation_events run) relation_bodies /\
      rules_predicate_trace_source (penc prog) pred_source
        (rules_multiway_selection_prepare_events run) prepare_bodies /\
      rules_positive_filter_source env_source
        (rules_multiway_selection_terminal_events run) terminal_bodies /\
      rules_multiway_selection_result run = selected_bindings IndexedMultiway prog r env /\
      rules_multiway_selection_work run + rules_predicate_bodies_work weight relation_bodies +
        rules_predicate_bodies_work weight prepare_bodies +
        rules_terminal_bodies_work weight terminal_bodies <=
        rules_multiway_selection_input_budget prog r env +
          rules_relation_external_input_budget (penc prog) (positive_atoms (body r)) pred_bound
  env_bound +
          length (join_variables (positive_atoms (body r))) *
            rules_predicate_input_budget pred_bound (positive_atoms (body r)) +
          length (rules_multiway_selection_candidates run) *
            rules_predicate_input_budget env_bound (positive_atoms (body r)).
```

## Galois.Rules.RulesAuditNestedPrepare

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditNestedPrepare.v`.

```rocq
(** Nested-join preparation using the actual row-index primitive subruns.
    Partial integration candidate: external predicate-encoding adequacy and a whole-input
    budget are not supplied by this declaration. No implementation proofs are claimed. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Rules Require Import RulesAuditMaterializePrelude RulesAuditIndex RulesAuditJoinSyntax.
Import ListNotations.

Fixpoint rules_prepare_nested_full {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (atoms : list (atom P))
    (bound : FinSet.t nat) : mat_run (list nested_search) :=
  mat_mark 201 (
    match atoms with
    | [] => mat_return []
    | a :: rest =>
        raw <- mat_get E (pred a) relations;;
        let rows := match raw with Some found => found | None => [] end in
        index <- mat_build_index_full bound (args a) rows;;
        let search := NestedSearch bound (args a) index in
        next_bound <- mat_bound_add bound a;;
        tail <- rules_prepare_nested_full E relations rest next_bound;;
        mat_return (search :: tail)
    end).

Definition rules_prepare_nested_full_erases_statement : Prop :=
  forall P (E : encoding P) relations atoms bound,
    fst (rules_prepare_nested_full E relations atoms bound) =
      prepare_nested atoms bound (join_relation_rows E relations).

(** A candidate input-only allowance for this preparation phase. The model charges each
    predicate encoder as one external call; its real body needs a separate adapter. *)
From Galois.Collections Require Import CollectionsAuditElements.
Definition rules_nested_prepare_input_size {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (atoms : list (atom P))
    (bound : FinSet.t nat) : nat :=
  1 + audit_trie_nodes relations + audit_trie_nodes bound +
  fold_right (fun entry n => mat_index_rows_input (snd entry) + n) 0 (Map.elements relations) +
  fold_right (fun a n => 1 + Pos.size_nat (encode E (pred a)) +
    mat_index_terms_input (args a) + n) 0 atoms.
Definition rules_nested_prepare_input_budget {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (atoms : list (atom P))
    (bound : FinSet.t nat) : nat :=
  1000000000 * Nat.pow (rules_nested_prepare_input_size E relations atoms bound) 16.
Definition rules_prepare_nested_full_input_bound_statement : Prop :=
  forall P (E : encoding P) relations atoms bound,
    mat_work (snd (rules_prepare_nested_full E relations atoms bound)) <=
      rules_nested_prepare_input_budget E relations atoms bound.
```

## Galois.Rules.RulesAuditNestedProbe

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditNestedProbe.v`.

```rocq
(** * Counted nested-join probing

    This candidate fixes the actual bound-key, trie lookup, repeated-variable binding and
    flat-map source branches, preserving the selected rows and their original order.
    Builds on RulesJoin and the shared finite-set, trie and encoding models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditPrimitive.
Import List.ListNotations.

Inductive rules_nested_probe_event : Type :=
  | RprobeBoundMem (variable : nat) (bound : FinSet.t nat) (result : bool)
      (body : list (audit_set_event nat audit_nat_encoding_event))
  | RprobeBindingGet (variable : nat) (code : positive) (binding : binding)
      (raw : option positive) (encoding_body : list audit_nat_encoding_event)
      (body : audit_trace (audit_trie_call (nat * positive)))
  | RprobeBindingSet (variable : nat) (value : positive) (code : positive)
      (before after : binding) (encoding_body : list audit_nat_encoding_event)
      (body : audit_trace (audit_trie_call (nat * positive)))
  | RprobeIndexGet (key : tuple) (code : positive) (index : tuple_index) (raw : option (list tuple))
      (encoding_body : list (audit_list_event positive (audit_basic_encoding_event positive)))
      (body : audit_trace (audit_trie_call (tuple * list tuple)))
  | RprobeEqual (left right : positive) (result : bool) (body : list audit_positive_eqb_event)
  | RprobeAppend (left_length : nat)
  | RprobeCase (site : nat).

Definition rules_probe_bound_term (bound : FinSet.t nat) (t : term) :
    bool * list rules_nested_probe_event :=
  match t with
  | TConst _ => (true, [RprobeCase 0])
  | TVar v =>
      let '(result, body) := audit_finset_mem audit_nat_encode v bound in
      (result, [RprobeCase 0; RprobeBoundMem v bound result body])
  end.

Fixpoint rules_probe_filter (bound : FinSet.t nat) (terms : list term) :
    list term * list rules_nested_probe_event :=
  match terms with
  | [] => ([], [RprobeCase 1])
  | t :: ts =>
      let '(keep, head) := rules_probe_bound_term bound t in
      let '(tail, events) := rules_probe_filter bound ts in
      (if keep then t :: tail else tail, RprobeCase 1 :: head ++ [RprobeCase 2] ++ events ++
        if keep then [RprobeCase 3] else [])
  end.

Definition rules_probe_value (b : binding) (v : nat) : positive * list rules_nested_probe_event :=
  let '(code, encoding_body) := audit_nat_encode v in
  let '(raw, body) := audit_map_code_get code b in
  (match raw with Some value => value | None => 1%positive end,
   [RprobeBindingGet v code b raw encoding_body body; RprobeCase 4]).

Fixpoint rules_probe_instantiate (b : binding) (terms : list term) :
    tuple * list rules_nested_probe_event :=
  match terms with
  | [] => ([], [RprobeCase 5])
  | t :: ts =>
      let '(value, first) := match t with
        | TConst c => (c, [RprobeCase 6])
        | TVar v => let '(value, body) := rules_probe_value b v in
            (value, RprobeCase 6 :: body)
        end in
      let '(tail, events) := rules_probe_instantiate b ts in
      (value :: tail, RprobeCase 5 :: first ++ events ++ [RprobeCase 7])
  end.

Definition rules_bound_key_counted (bound : FinSet.t nat) (b : binding) (terms : list term) :
    tuple * list rules_nested_probe_event :=
  let '(selected, filtering) := rules_probe_filter bound terms in
  let '(key, instantiation) := rules_probe_instantiate b selected in
  (key, filtering ++ instantiation).

Definition rules_bind_term_counted (b : binding) (t : term) (value : positive) :
    option binding * list rules_nested_probe_event :=
  match t with
  | TConst expected =>
      let '(equal, body) := audit_positive_eqb value expected in
      (if equal then Some b else None,
       [RprobeCase 8; RprobeEqual value expected equal body; RprobeCase 9])
  | TVar v =>
      let '(code, encoding_body) := audit_nat_encode v in
      let '(raw, body) := audit_map_code_get code b in
      let prefix := [RprobeCase 8; RprobeBindingGet v code b raw encoding_body body; RprobeCase
  10] in
      match raw with
      | Some old =>
          let '(equal, equal_body) := audit_positive_eqb value old in
          (if equal then Some b else None,
           prefix ++ [RprobeEqual value old equal equal_body; RprobeCase 11])
      | None =>
          let '(write_code, write_encoding) := audit_nat_encode v in
          let '(after, set_body) := audit_trie_set write_code (v, value) b in
          (Some after, prefix ++ [RprobeBindingSet v value write_code b after write_encoding
  set_body])
      end
  end.

Fixpoint rules_bind_terms_counted (terms : list term) (row : tuple) (b : binding) :
    option binding * list rules_nested_probe_event :=
  match terms, row with
  | [], [] => (Some b, [RprobeCase 12])
  | t :: ts, value :: rest =>
      let '(next, first) := rules_bind_term_counted b t value in
      match next with
      | None => (None, RprobeCase 12 :: first ++ [RprobeCase 13])
      | Some updated =>
          let '(out, events) := rules_bind_terms_counted ts rest updated in
          (out, RprobeCase 12 :: first ++ RprobeCase 13 :: events)
      end
  | _, _ => (None, [RprobeCase 12])
  end.

Fixpoint rules_probe_rows (terms : list term) (b : binding) (rows : list tuple) :
    list binding * list rules_nested_probe_event :=
  match rows with
  | [] => ([], [RprobeCase 14])
  | row :: rest =>
      let '(candidate, first) := rules_bind_terms_counted terms row b in
      let prefix := match candidate with Some result => [result] | None => [] end in
      let '(tail, events) := rules_probe_rows terms b rest in
      (prefix ++ tail, RprobeCase 14 :: first ++ RprobeCase 15 :: events ++
        [RprobeAppend (length prefix)])
  end.

Fixpoint rules_probe_bindings (search : nested_search) (bindings : list binding) :
    list binding * list rules_nested_probe_event :=
  match bindings with
  | [] => ([], [RprobeCase 16])
  | b :: rest =>
      let '(key, key_events) := rules_bound_key_counted (nested_bound search) b (nested_terms
  search) in
      let '(code, encoding_body) := audit_list_encode audit_positive_encode key in
      let '(raw, get_body) := audit_map_code_get code (nested_index search) in
      let rows := match raw with Some found => found | None => [] end in
      let '(head, row_events) := rules_probe_rows (nested_terms search) b rows in
      let '(tail, tail_events) := rules_probe_bindings search rest in
      (head ++ tail, RprobeCase 16 :: key_events ++
        [RprobeIndexGet key code (nested_index search) raw encoding_body get_body; RprobeCase 17] ++
        row_events ++ tail_events ++ [RprobeAppend (length head)])
  end.

Fixpoint rules_run_nested_counted (searches : list nested_search) (bindings : list binding) :
    list binding * list rules_nested_probe_event :=
  match searches with
  | [] => (bindings, [RprobeCase 18])
  | search :: rest =>
      let '(next, first) := rules_probe_bindings search bindings in
      let '(result, events) := rules_run_nested_counted rest next in
      (result, RprobeCase 18 :: first ++ events)
  end.

Definition rules_nested_probe_erasure_statement : Prop :=
  (forall bound b terms, fst (rules_bound_key_counted bound b terms) = bound_key bound b terms) /\
  (forall b term value, fst (rules_bind_term_counted b term value) = bind_term b term value) /\
  (forall terms row b, fst (rules_bind_terms_counted terms row b) = bind_terms terms row b) /\
  (forall search bindings, fst (rules_probe_bindings search bindings) = nested_probe search
  bindings) /\
  (forall searches bindings, fst (rules_run_nested_counted searches bindings) =
    run_nested searches bindings).

(** Each nonconstant library body is the actual nested frozen collection derivation. *)
Definition rules_nested_probe_event_work (event : rules_nested_probe_event) : nat :=
  match event with
  | RprobeBoundMem _ _ _ body => audit_finset_source_work audit_nat_events_work body
  | RprobeBindingGet _ _ _ _ encoding_body body =>
      1 + audit_nat_events_work encoding_body + audit_trie_get_trace_source_work body
  | RprobeBindingSet _ _ _ _ _ encoding_body body =>
      1 + audit_nat_events_work encoding_body + audit_trie_update_trace_source_work body
  | RprobeIndexGet _ _ _ _ encoding_body body =>
      1 + audit_list_events_work audit_basic_encoding_work encoding_body +
        audit_trie_get_trace_source_work body
  | RprobeEqual _ _ _ body => audit_positive_eqb_source_work body
  | RprobeAppend size => 1 + size
  | RprobeCase _ => 1
  end.
Definition rules_nat_encoder_budget (v : nat) : nat :=
  2 * S v * S (Pos.size_nat (encode nat_encoding v)).
Definition rules_nested_probe_event_budget (event : rules_nested_probe_event) : nat :=
  match event with
  | RprobeBoundMem v _ _ _ => 7 + rules_nat_encoder_budget v + 5 * Pos.size_nat (encode
  nat_encoding v)
  | RprobeBindingGet v code _ _ _ _ => 2 + rules_nat_encoder_budget v + 5 * Pos.size_nat code
  | RprobeBindingSet v _ code _ _ _ _ => 2 + rules_nat_encoder_budget v + 16 * Pos.size_nat code
  | RprobeIndexGet key code _ _ _ _ =>
      10 + 10 * length key + 20 * audit_encoded_bits audit_positive_encode key + 5 *
  Pos.size_nat code
  | RprobeEqual lhs rhs _ _ => 2 * Nat.min (Pos.size_nat lhs) (Pos.size_nat rhs)
  | RprobeAppend size => 1 + size
  | RprobeCase _ => 1
  end.
Definition rules_nested_probe_work (events : list rules_nested_probe_event) : nat :=
  fold_right (fun event n => rules_nested_probe_event_work event + n) 0 events.
Definition rules_nested_probe_budget (events : list rules_nested_probe_event) : nat :=
  fold_right (fun event n => rules_nested_probe_event_budget event + n) 0 events.
Definition rules_run_nested_selected_cost_statement : Prop :=
  forall searches bindings,
    let '(result, events) := rules_run_nested_counted searches bindings in
    result = run_nested searches bindings /\
    rules_nested_probe_work events <= rules_nested_probe_budget events.
```

## Galois.Rules.RulesAuditNestedSelection

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditNestedSelection.v`.

```rocq
(** * Whole indexed-nested binding selection

    One relation snapshot feeds the actual index preparation and binding probes.
    For example, repeated predicates share the snapshot while each atom builds its own index.
    Builds on: RulesAuditRelationCallbacks, RulesAuditNestedPrepare and RulesAuditNestedProbe. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditElements.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditJoinSyntax RulesAuditRelations RulesAuditNestedPrepare
  RulesAuditNestedProbe RulesAuditPrepareCallbacks RulesAuditRelationCallbacks.
Import List.ListNotations.

Record rules_nested_selection_run (P : Type) := RulesNestedSelectionRun {
  rules_nested_selection_result : list binding;
  rules_nested_selection_atoms : list (atom P);
  rules_nested_selection_atom_events : list mat_frame;
  rules_nested_selection_relation_events : list (rules_relation_event P);
  rules_nested_selection_prepare_events : list mat_frame;
  rules_nested_selection_probe_events : list rules_nested_probe_event
}.
Arguments rules_nested_selection_result {P} _.
Arguments rules_nested_selection_atoms {P} _.
Arguments rules_nested_selection_atom_events {P} _.
Arguments rules_nested_selection_relation_events {P} _.
Arguments rules_nested_selection_prepare_events {P} _.
Arguments rules_nested_selection_probe_events {P} _.

Definition rules_selected_nested_capture {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : rules_nested_selection_run P :=
  let '(atoms, atom_events) := mat_positive_atoms (body r) in
  let '(relations, relation_events) := rules_join_relations_counted (penc prog) atoms env in
  let '(searches, prepare_events) :=
    rules_prepare_nested_full (penc prog) relations atoms FinSet.empty in
  let '(result, probe_events) := rules_run_nested_counted searches [Map.empty] in
  RulesNestedSelectionRun P result atoms atom_events relation_events prepare_events probe_events.

Definition rules_nested_selection_work {P} (run : rules_nested_selection_run P) : nat :=
  mat_work (rules_nested_selection_atom_events run) +
    rules_relation_work (rules_nested_selection_relation_events run) +
    mat_work (rules_nested_selection_prepare_events run) +
    rules_nested_probe_work (rules_nested_selection_probe_events run) + 1.

Definition rules_nested_selection_input_size {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : nat :=
  2 + length (body r) +
    fold_right (fun a n =>
      1 + Pos.size_nat (encode (penc prog) (pred a)) + mat_index_terms_input (args a) +
      audit_trie_nodes (env (pred a)) + mat_index_rows_input (FinSet.elements (env (pred a))) + n)
      0 (positive_atoms (body r)).

Definition rules_nested_selection_input_budget {P} (prog : program P) (r : rule P)
    (env : P -> FinSet.t tuple) : nat :=
  1000000000 * Nat.pow (rules_nested_selection_input_size prog r env)
    (20 + 2 * length (positive_atoms (body r))).

(** The captured selection has the exact native result and input-derived internal allowance. *)
Definition rules_nested_selection_input_bound_statement : Prop :=
  forall P (prog : program P) r env,
    let run := rules_selected_nested_capture prog r env in
    rules_nested_selection_result run = selected_bindings IndexedNested prog r env /\
    rules_nested_selection_work run <= rules_nested_selection_input_budget prog r env.

(** Both external callbacks are related to the exact relation snapshot and preparation run. *)
Definition rules_nested_selection_source_statement : Prop :=
  forall P B (prog : program P) r (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound : P -> nat),
    rules_predicate_source_laws (penc prog) pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    let run := rules_selected_nested_capture prog r env in
    exists relation_bodies prepare_bodies,
      rules_relation_trace_source pred_source env_source
        (rules_nested_selection_relation_events run) relation_bodies /\
      rules_predicate_trace_source (penc prog) pred_source
        (rules_nested_selection_prepare_events run) prepare_bodies /\
      rules_nested_selection_result run = selected_bindings IndexedNested prog r env /\
      rules_nested_selection_work run + rules_predicate_bodies_work weight relation_bodies +
        rules_predicate_bodies_work weight prepare_bodies <=
        rules_nested_selection_input_budget prog r env +
          rules_relation_external_input_budget (penc prog) (positive_atoms (body r)) pred_bound
  env_bound +
          rules_predicate_input_budget pred_bound (positive_atoms (body r)).
```

## Galois.Rules.RulesAuditPrepareCallbacks

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditPrepareCallbacks.v`.

```rocq
(** * Join preparation callback receipts

    Each actual predicate encoding is related to its own external source body.
    For example, a repeated predicate in two atoms retains two separate invocations.
    Builds on: RulesAuditNestedPrepare and RulesAuditMultiwayPrepare. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditJoinSyntax RulesAuditNestedPrepare RulesAuditMultiwayPrepare.
Import List.ListNotations.

Definition rules_predicate_frame_source {P B} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (frame : mat_frame) (bodies : list (list B)) :
  Prop :=
  match frame with
  | MatEncode _ _ _ _ => exists p code body,
      frame = MatEncode P E p code /\ bodies = [body] /\ source p code body
  | _ => bodies = []
  end.

Definition rules_predicate_trace_source {P B} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (events : list mat_frame)
    (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_predicate_frame_source E source) events bodies.

Definition rules_predicate_bodies_work {B} (weight : B -> nat) (bodies : list (list (list B))) :
  nat :=
  fold_right (fun group n => fold_right (fun body m =>
    fold_right (fun item total => weight item + total) 0 body + m) 0 group + n) 0 bodies.

Definition rules_predicate_input_budget {P} (bound : P -> nat) (atoms : list (atom P)) : nat :=
  fold_right (fun a n => bound (pred a) + n) 0 atoms.

Definition rules_predicate_source_laws {P B} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) : Prop :=
  (forall p, exists body, source p (encode E p) body) /\
  (forall p code body, source p code body ->
    fold_right (fun item n => weight item + n) 0 body <= bound p).

(** Each nested preparation call has its own predicate-body receipt. *)
Definition rules_nested_prepare_source_statement : Prop :=
  forall P B (E : encoding P) relations atoms bound
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (price : P -> nat),
    rules_predicate_source_laws E source weight price ->
    let '(out, events) := rules_prepare_nested_full E relations atoms bound in
    exists bodies, rules_predicate_trace_source E source events bodies /\
      out = prepare_nested atoms bound (join_relation_rows E relations) /\
      mat_work events + rules_predicate_bodies_work weight bodies <=
        rules_nested_prepare_input_budget E relations atoms bound +
          rules_predicate_input_budget price atoms.

Definition rules_multiway_prepare_input_size {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (vars : list nat) (bound : FinSet.t nat)
    (atoms : list (atom P)) : nat :=
  rules_nested_prepare_input_size E relations atoms bound +
    fold_right (fun v n => 1 + v + n) 0 vars.

Definition rules_multiway_prepare_input_budget {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (vars : list nat) (bound : FinSet.t nat)
    (atoms : list (atom P)) : nat :=
  1000000000 * Nat.pow (rules_multiway_prepare_input_size E relations vars bound atoms)
    (18 + 2 * length vars).

(** The multiway allowance includes repeated per-variable predicate lookup occurrences. *)
Definition rules_multiway_prepare_source_statement : Prop :=
  forall P B (E : encoding P) relations vars bound atoms
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (price : P -> nat),
    rules_predicate_source_laws E source weight price ->
    let '(out, events) := rules_prepare_multiway_full E relations vars bound atoms in
    exists bodies, rules_predicate_trace_source E source events bodies /\
      out = prepare_multiway vars bound atoms (join_relation_rows E relations) /\
      mat_work events + rules_predicate_bodies_work weight bodies <=
        rules_multiway_prepare_input_budget E relations vars bound atoms +
          length vars * rules_predicate_input_budget price atoms.
```

## Galois.Rules.RulesAuditRelationCallbacks

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditRelationCallbacks.v`.

```rocq
(** * Relation snapshot callback source receipts

    Distinct predicate encodings, table writes and environment calls retain their own bodies.
    For example, duplicate atoms re-encode their predicate but share one environment lookup.
    Builds on: RulesAuditRelations and the predicate source model. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesJoin RulesAuditRelations
  RulesAuditPrepareCallbacks.
Import List.ListNotations.

Definition rules_relation_entries {P}
    (events : list (audit_set_event P (rules_encode_entry P))) : list (rules_encode_entry P) :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

Definition rules_relation_entry_source {P B} (source : P -> positive -> list B -> Prop)
    (entry : rules_encode_entry P) (body : list B) : Prop :=
  match entry with
  | RulesEncodeEntry p code => source p code body
  end.

Definition rules_relation_event_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (event : rules_relation_event P)
    (bodies : list (list B)) : Prop :=
  match event with
  | RulesRelationDistinct _ _ events =>
      Forall2 (rules_relation_entry_source pred_source) (rules_relation_entries events) bodies
  | RulesRelationEnv p result => exists body, bodies = [body] /\ env_source p result body
  | RulesRelationSet p _ code _ _ _ => exists body, bodies = [body] /\ pred_source p code body
  | _ => bodies = []
  end.

Definition rules_relation_trace_source {P B} (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (events : list (rules_relation_event P))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_relation_event_source pred_source env_source) events bodies.

Definition rules_environment_source_laws {P B} (env : P -> FinSet.t tuple)
    (source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) :
  Prop :=
  (forall p, exists body, source p (env p) body) /\
  (forall p out body, source p out body ->
    fold_right (fun item n => weight item + n) 0 body <= bound p).

Definition rules_relation_external_input_budget {P} (E : encoding P) (atoms : list (atom P))
    (pred_bound env_bound : P -> nat) : nat :=
  let predicates := map pred atoms in
  let keys := FinSet.elements (FinSet.of_list E predicates) in
  fold_right (fun p n => pred_bound p + n) 0 predicates +
    fold_right (fun p n => pred_bound p + env_bound p + n) 0 keys.

(** One same-run relation snapshot preserves distinct and repeated callback calls. *)
Definition rules_relations_external_source_statement : Prop :=
  forall P B (E : encoding P) atoms (env : P -> FinSet.t tuple)
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) (weight : B -> nat)
    (pred_bound env_bound : P -> nat),
    rules_predicate_source_laws E pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    let '(out, events) := rules_join_relations_counted E atoms env in
    exists bodies, rules_relation_trace_source pred_source env_source events bodies /\
      out = prepare_join_relations E atoms env /\
      rules_relation_work events + rules_predicate_bodies_work weight bodies <=
        rules_join_relations_input_budget E atoms env +
          rules_relation_external_input_budget E atoms pred_bound env_bound.
```

## Galois.Rules.RulesAuditRelations

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditRelations.v`.

```rocq
(** * Strict shared join-relation snapshot

    This report-only model retains each predicate, set construction, row enumeration and
    tail-first table update. Duplicate predicates trigger repeated insertion, but rows are
    enumerated once per resulting distinct key. Builds on RulesJoin and collection models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditElements.
Import List.ListNotations.

Inductive rules_encode_entry (P : Type) : Type :=
  | RulesEncodeEntry (key : P) (code : positive).
Arguments RulesEncodeEntry {P} _ _.
Definition rules_encoder {P} (E : encoding P) (p : P) : positive * list (rules_encode_entry P) :=
  let code := encode E p in (code, [RulesEncodeEntry p code]).

Inductive rules_relation_event (P : Type) : Type :=
  | RulesRelationPredicate (atom : atom P) (predicate : P)
  | RulesRelationDistinct (keys : list P) (set : FinSet.t P)
      (body : list (audit_set_event P (rules_encode_entry P)))
  | RulesRelationKeys (set : FinSet.t P) (keys : list P)
      (body : list (audit_set_elements_event P))
  | RulesRelationEnv (predicate : P) (result : FinSet.t tuple)
  | RulesRelationRows (predicate : P) (input : FinSet.t tuple) (rows : list tuple)
      (body : list (audit_set_elements_event tuple))
  | RulesRelationSet (predicate : P) (rows : list tuple) (code : positive)
      (before after : Map.t P (list tuple)) (body : audit_trace (audit_trie_call (P * list tuple)))
  | RulesRelationCase (site : nat).
Arguments RulesRelationPredicate {P} _ _.
Arguments RulesRelationDistinct {P} _ _ _.
Arguments RulesRelationKeys {P} _ _ _.
Arguments RulesRelationEnv {P} _ _.
Arguments RulesRelationRows {P} _ _ _ _.
Arguments RulesRelationSet {P} _ _ _ _ _ _.
Arguments RulesRelationCase {P} _.

Fixpoint rules_relation_predicates {P} (atoms : list (atom P)) :
    list P * list (rules_relation_event P) :=
  match atoms with
  | [] => ([], [RulesRelationCase 0])
  | a :: rest =>
      let p := pred a in
      let '(tail, events) := rules_relation_predicates rest in
      (p :: tail, RulesRelationCase 0 :: RulesRelationPredicate a p :: events ++
        [RulesRelationCase 1])
  end.

Fixpoint rules_relation_rows_counted {P} (env : P -> FinSet.t tuple) (keys : list P) :
    list (list tuple) * list (rules_relation_event P) :=
  match keys with
  | [] => ([], [RulesRelationCase 2])
  | p :: rest =>
      let input := env p in
      let '(rows, body) := audit_finset_elements input in
      let '(tail, events) := rules_relation_rows_counted env rest in
      (rows :: tail, RulesRelationCase 2 :: RulesRelationEnv p input ::
        RulesRelationRows p input rows body :: events ++ [RulesRelationCase 3])
  end.

Fixpoint rules_relation_fill_counted {P} (E : encoding P) (keys : list P)
    (values : list (list tuple)) : Map.t P (list tuple) * list (rules_relation_event P) :=
  match keys, values with
  | p :: ps, rows :: vs =>
      let '(before, events) := rules_relation_fill_counted E ps vs in
      let code := encode E p in
      let '(after, body) := audit_trie_set code (p, rows) before in
      (after, RulesRelationCase 4 :: events ++ [RulesRelationSet p rows code before after body])
  | _, _ => (Map.empty, [RulesRelationCase 4])
  end.

Definition rules_join_relations_counted {P} (E : encoding P) (atoms : list (atom P))
    (env : P -> FinSet.t tuple) : Map.t P (list tuple) * list (rules_relation_event P) :=
  let '(predicates, pred_events) := rules_relation_predicates atoms in
  let '(distinct, set_events) := audit_finset_of_list (rules_encoder E) predicates in
  let '(keys, key_events) := audit_finset_elements distinct in
  let '(rows, row_events) := rules_relation_rows_counted env keys in
  let '(result, fill_events) := rules_relation_fill_counted E keys rows in
  (result, pred_events ++ [RulesRelationDistinct predicates distinct set_events;
    RulesRelationKeys distinct keys key_events] ++ row_events ++ fill_events).

Definition rules_join_relations_erasure_statement : Prop :=
  forall P (E : encoding P) atoms env,
    fst (rules_join_relations_counted E atoms env) = prepare_join_relations E atoms env.
Definition rules_join_relations_row_count_statement : Prop :=
  forall P (E : encoding P) atoms env,
    let '(result, events) := rules_join_relations_counted E atoms env in
    length (filter (fun e => match e with RulesRelationEnv _ _ => true | _ => false end) events) =
      length (join_relation_keys E atoms).

(** The fixed set source fold counts the actual predicate encoder entry and trie body. *)
Definition rules_relation_set_event_work {P} (event : audit_set_event P (rules_encode_entry P))
  : nat :=
  match event with
  | AuditSetAdd _ _ _ _ enc body => length enc + audit_trie_update_trace_source_work body
  | AuditSetMem _ _ _ _ enc body => length enc + audit_trie_get_trace_source_work body
  | AuditSetRemove _ _ _ _ enc body => length enc + audit_trie_update_trace_source_work body
  | AuditSetFold _ _ => 1
  end.
Definition rules_relation_event_work {P} (event : rules_relation_event P) : nat :=
  match event with
  | RulesRelationDistinct _ _ body =>
      1 + audit_finset_source_work (@length (rules_encode_entry P)) body
  | RulesRelationKeys _ _ body => 1 + audit_set_elements_work body
  | RulesRelationRows _ _ _ body => 1 + audit_set_elements_work body
  | RulesRelationSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | _ => 1
  end.
Definition rules_relation_event_budget {P} (E : encoding P) (event : rules_relation_event P) :
  nat :=
  match event with
  | RulesRelationDistinct keys _ _ =>
      12 + 12 * length keys + 17 * fold_right (fun p n => Pos.size_nat (encode E p) + n) 0 keys
  | RulesRelationKeys set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | RulesRelationRows _ set _ _ => 7 + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | RulesRelationSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | _ => 1
  end.
Definition rules_relation_work {P} (events : list (rules_relation_event P)) : nat :=
  fold_right (fun event n => rules_relation_event_work event + n) 0 events.
Definition rules_relation_budget {P} (E : encoding P) (events : list (rules_relation_event P)) :
  nat :=
  fold_right (fun event n => rules_relation_event_budget E event + n) 0 events.
Definition rules_join_relations_selected_cost_statement : Prop :=
  forall P (E : encoding P) atoms env,
    let '(result, events) := rules_join_relations_counted E atoms env in
    result = prepare_join_relations E atoms env /\
    rules_relation_work events <= rules_relation_budget E events.

(** A semantic-input recurrence bounds source blocks without consulting the emitted trace.
    External predicate-encoder and environment bodies require separate concrete adapters. *)
Fixpoint rules_relation_predicate_bits {P} (E : encoding P) (keys : list P) : nat :=
  match keys with
  | [] => 0
  | p :: tail => Pos.size_nat (encode E p) + rules_relation_predicate_bits E tail
  end.
Fixpoint rules_relation_input_rows_budget {P} (E : encoding P) (env : P -> FinSet.t tuple)
    (keys : list P) : nat :=
  match keys with
  | [] => 2
  | p :: tail =>
      let rows := env p in
      4 + (7 + 19 * audit_trie_nodes rows + audit_trie_output_bits rows) +
      (2 + 17 * Pos.size_nat (encode E p)) + rules_relation_input_rows_budget E env tail
  end.
Definition rules_join_relations_input_budget {P} (E : encoding P) (atoms : list (atom P))
    (env : P -> FinSet.t tuple) : nat :=
  let predicates := map pred atoms in
  let distinct := FinSet.of_list E predicates in
  let keys := FinSet.elements distinct in
  1 + 3 * length atoms +
    (12 + 12 * length predicates + 17 * rules_relation_predicate_bits E predicates) +
    (7 + 19 * audit_trie_nodes distinct + audit_trie_output_bits distinct) +
    rules_relation_input_rows_budget E env keys.
Definition rules_join_relations_input_bound_statement : Prop :=
  forall P (E : encoding P) atoms env,
    let '(out, events) := rules_join_relations_counted E atoms env in
    out = prepare_join_relations E atoms env /\
    rules_relation_work events <= rules_join_relations_input_budget E atoms env.
```

## Galois.Rules.RulesAuditTerminal

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditTerminal.v`.

```rocq
(** * Strict positive and negative terminal filters

    All literal occurrences and environment snapshots are retained, even after a prior false
    result under strict evaluation. Builds on RulesJoin and the nested binding model. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditNestedProbe.
Import List.ListNotations.

Inductive rules_terminal_event (P : Type) : Type :=
  | RtInstantiate (terms : list term) (input : binding) (output : tuple)
      (events : list rules_nested_probe_event)
  | RtEnv (predicate : P) (result : FinSet.t tuple)
  | RtMember (row : tuple) (input : FinSet.t tuple) (answer : bool)
      (events : list (audit_set_event tuple (audit_list_event positive
  (audit_basic_encoding_event positive))))
  | RtNot (input output : bool)
  | RtAnd (lhs rhs output : bool)
  | RtCase (site : nat).
Arguments RtInstantiate {P} _ _ _ _.
Arguments RtEnv {P} _ _.
Arguments RtMember {P} _ _ _ _.
Arguments RtNot {P} _ _.
Arguments RtAnd {P} _ _ _.
Arguments RtCase {P} _.

Definition rules_terminal_atom_counted {P} (env : P -> FinSet.t tuple) (b : binding)
    (a : atom P) : bool * list (rules_terminal_event P) :=
  let '(row, inst_events) := rules_probe_instantiate b (args a) in
  let p := pred a in
  let set := env p in
  let '(found, mem_events) := audit_finset_mem (audit_list_encode audit_positive_encode) row set in
  (found, [RtInstantiate (args a) b row inst_events; RtEnv p set; RtMember row set found
  mem_events]).

Fixpoint rules_positive_check_counted {P} (atoms : list (atom P)) (env : P -> FinSet.t tuple)
    (b : binding) : bool * list (rules_terminal_event P) :=
  match atoms with
  | [] => (true, [RtCase 0])
  | a :: rest =>
      let '(head, first) := rules_terminal_atom_counted env b a in
      let '(tail, later) := rules_positive_check_counted rest env b in
      (andb head tail, RtCase 0 :: first ++ later ++ [RtAnd head tail (andb head tail)])
  end.

Fixpoint rules_negative_literals_counted {P} (literals : list (literal P))
    (env : P -> FinSet.t tuple) (b : binding) : bool * list (rules_terminal_event P) :=
  match literals with
  | [] => (true, [RtCase 1])
  | literal :: rest =>
      let '(head, first) := match literal with
        | LPos _ => (true, [RtCase 2])
        | LNeg a =>
            let '(found, events) := rules_terminal_atom_counted env b a in
            (negb found, RtCase 2 :: events ++ [RtNot found (negb found)])
        end in
      let '(tail, later) := rules_negative_literals_counted rest env b in
      (andb head tail, RtCase 1 :: first ++ later ++ [RtAnd head tail (andb head tail)])
  end.

Definition rules_terminal_erasure_statement : Prop :=
  (forall P (atoms : list (atom P)) env b,
    fst (rules_positive_check_counted atoms env b) = positive_ok atoms env b) /\
  (forall P (r : rule P) env b,
    fst (rules_negative_literals_counted (body r) env b) = negative_ok r env b).

Definition rules_terminal_event_work {P} (event : rules_terminal_event P) : nat :=
  match event with
  | RtInstantiate _ _ _ events => rules_nested_probe_work events
  | RtMember _ _ _ events =>
      audit_finset_source_work (audit_list_events_work audit_basic_encoding_work) events
  | _ => 1
  end.
Definition rules_terminal_event_budget {P} (event : rules_terminal_event P) : nat :=
  match event with
  | RtInstantiate _ _ _ events => rules_nested_probe_budget events
  | RtMember row _ _ _ =>
      20 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
        5 * Pos.size_nat (encode tuple_encoding row)
  | _ => 1
  end.
Definition rules_terminal_work {P} (events : list (rules_terminal_event P)) : nat :=
  fold_right (fun event n => rules_terminal_event_work event + n) 0 events.
Definition rules_terminal_budget {P} (events : list (rules_terminal_event P)) : nat :=
  fold_right (fun event n => rules_terminal_event_budget event + n) 0 events.
Definition rules_terminal_selected_cost_statement : Prop :=
  (forall P (atoms : list (atom P)) env b,
    let '(out, events) := rules_positive_check_counted atoms env b in
    out = positive_ok atoms env b /\ rules_terminal_work events <= rules_terminal_budget events) /\
  (forall P (r : rule P) env b,
    let '(out, events) := rules_negative_literals_counted (body r) env b in
    out = negative_ok r env b /\ rules_terminal_work events <= rules_terminal_budget events).
```

## Galois.Rules.RulesAuditTerminalCallbacks

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditTerminalCallbacks.v`.

```rocq
(** * Join terminal callback receipts

    Positive and negative checks retain each actual environment invocation.
    For example, strict conjunction still checks later atoms after an earlier failure.
    Builds on: RulesAuditTerminal and the environment source model. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditTerminal
  RulesAuditRelationCallbacks RulesAuditPrepareCallbacks.
Import List.ListNotations.

Definition rules_terminal_event_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (event : rules_terminal_event P) (bodies : list (list B)) : Prop :=
  match event with
  | RtEnv p out => exists body, bodies = [body] /\ source p out body
  | _ => bodies = []
  end.

Definition rules_terminal_trace_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (events : list (rules_terminal_event P)) (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_terminal_event_source source) events bodies.

Fixpoint rules_positive_filter_capture {P} (atoms : list (atom P)) (env : P -> FinSet.t tuple)
    (bindings : list binding) : list binding * list (list (rules_terminal_event P)) :=
  match bindings with
  | [] => ([], [])
  | b :: rest =>
      let '(keep, first) := rules_positive_check_counted atoms env b in
      let '(tail, later) := rules_positive_filter_capture atoms env rest in
      (if keep then b :: tail else tail, first :: later)
  end.

Definition rules_positive_filter_work {P} (groups : list (list (rules_terminal_event P))) : nat :=
  1 + 2 * length groups + fold_right (fun events n => rules_terminal_work events + n) 0 groups.

Definition rules_positive_filter_source {P B} (source : P -> FinSet.t tuple -> list B -> Prop)
    (groups : list (list (rules_terminal_event P))) (bodies : list (list (list (list B)))) : Prop :=
  Forall2 (rules_terminal_trace_source source) groups bodies.

Definition rules_terminal_bodies_work {B} (weight : B -> nat)
    (groups : list (list (list (list B)))) : nat :=
  fold_right (fun bodies n => rules_predicate_bodies_work weight bodies + n) 0 groups.

(** Filtering runs the actual strict checks once per candidate binding. *)
Definition rules_positive_filter_erasure_statement : Prop :=
  forall P (atoms : list (atom P)) env bindings,
    fst (rules_positive_filter_capture atoms env bindings) = filter (positive_ok atoms env)
  bindings.
```

## Galois.Rules.RulesAuditUniverse

Card: AUD-RU-MODELS

Source destination: `theories/Rules/RulesAuditUniverse.v`.

```rocq
(** * Counted finite-universe preparation and membership

    Every rule literal and fact contributes its actual predicates and constants. The
    predicate set and constant set are prepared once before filtering all head tuples.
    Builds on RulesCompile and the shared finite-set models. *)
From Stdlib Require Import List Bool PeanoNat PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditRelations.
Import List.ListNotations.

Inductive rules_universe_event (P : Type) : Type :=
  | RuCase (site : nat)
  | RuAppend (size : nat)
  | RuPredicatesSet (input : list P) (output : FinSet.t P)
      (events : list (audit_set_event P (rules_encode_entry P)))
  | RuConstantsSet (input : list positive) (output : FinSet.t positive)
      (events : list (audit_set_event positive (audit_basic_encoding_event positive)))
  | RuPredicateMem (p : P) (input : FinSet.t P) (output : bool)
      (events : list (audit_set_event P (rules_encode_entry P)))
  | RuConstantMem (c : positive) (input : FinSet.t positive) (output : bool)
      (events : list (audit_set_event positive (audit_basic_encoding_event positive)))
  | RuArity (p : P) (value : nat)
  | RuLength (row : tuple)
  | RuNatEq (lhs rhs : nat) (result : bool)
  | RuAnd (lhs rhs output : bool).
Arguments RuCase {P} _.
Arguments RuAppend {P} _.
Arguments RuPredicatesSet {P} _ _ _.
Arguments RuConstantsSet {P} _ _ _.
Arguments RuPredicateMem {P} _ _ _ _.
Arguments RuConstantMem {P} _ _ _ _.
Arguments RuArity {P} _ _.
Arguments RuLength {P} _.
Arguments RuNatEq {P} _ _ _.
Arguments RuAnd {P} _ _ _.

Fixpoint ru_literal_predicates {P} (items : list (literal P)) :
    list P * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 0])
  | item :: rest =>
      let p := pred (lit_atom item) in
      let '(tail, events) := ru_literal_predicates rest in
      (p :: tail, RuCase 0 :: RuCase 1 :: events ++ [RuCase 2])
  end.
Fixpoint ru_rule_predicates {P} (items : list (rule P)) :
    list P * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 3])
  | r :: rest =>
      let '(body_preds, first) := ru_literal_predicates (body r) in
      let head_preds := pred (head r) :: body_preds in
      let '(tail, events) := ru_rule_predicates rest in
      (head_preds ++ tail, RuCase 3 :: first ++ RuCase 4 :: events ++ [RuAppend (length
  head_preds)])
  end.
Fixpoint ru_fact_predicates {P} (facts : list (ground_atom P)) :
    list P * list (rules_universe_event P) :=
  match facts with
  | [] => ([], [RuCase 5])
  | (p, _) :: rest =>
      let '(tail, events) := ru_fact_predicates rest in
      (p :: tail, RuCase 5 :: events ++ [RuCase 6])
  end.
Fixpoint ru_term_constants {P} (terms : list term) :
    list positive * list (rules_universe_event P) :=
  match terms with
  | [] => ([], [RuCase 7])
  | t :: rest =>
      let current := match t with TVar _ => [] | TConst c => [c] end in
      let '(tail, events) := @ru_term_constants P rest in
      (current ++ tail, RuCase 7 :: RuCase 8 :: events ++ [RuAppend (length current)])
  end.
Fixpoint ru_literal_constants {P} (items : list (literal P)) :
    list positive * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 9])
  | item :: rest =>
      let '(head, first) := ru_term_constants (args (lit_atom item)) in
      let '(tail, events) := ru_literal_constants rest in
      (head ++ tail, RuCase 9 :: first ++ events ++ [RuAppend (length head)])
  end.
Fixpoint ru_rule_constants {P} (items : list (rule P)) :
    list positive * list (rules_universe_event P) :=
  match items with
  | [] => ([], [RuCase 10])
  | r :: rest =>
      let '(head, head_events) := ru_term_constants (args (head r)) in
      let '(body, body_events) := ru_literal_constants (body r) in
      let rule_constants := head ++ body in
      let '(tail, tail_events) := ru_rule_constants rest in
      (rule_constants ++ tail, RuCase 10 :: head_events ++ body_events ++
        [RuAppend (length head)] ++ tail_events ++ [RuAppend (length rule_constants)])
  end.
Fixpoint ru_fact_constants {P} (facts : list (ground_atom P)) :
    list positive * list (rules_universe_event P) :=
  match facts with
  | [] => ([], [RuCase 11])
  | (_, row) :: rest =>
      let '(tail, events) := ru_fact_constants rest in
      (row ++ tail, RuCase 11 :: events ++ [RuAppend (length row)])
  end.

(** All three let bindings are evaluated once before the returned tuple predicate. *)
Definition rules_universe_prepare_counted {P} (prog : program P) (facts : list (ground_atom P))
  (p : P) :
    (bool * nat * FinSet.t positive) * list (rules_universe_event P) :=
  let '(rule_ps, rp_events) := ru_rule_predicates (rules prog) in
  let '(fact_ps, fp_events) := ru_fact_predicates facts in
  let ps := rule_ps ++ fact_ps in
  let '(pset, pset_events) := audit_finset_of_list (rules_encoder (penc prog)) ps in
  let '(present, present_events) := audit_finset_mem (rules_encoder (penc prog)) p pset in
  let n := arity prog p in
  let '(rule_cs, rc_events) := ru_rule_constants (rules prog) in
  let '(fact_cs, fc_events) := ru_fact_constants facts in
  let cs := rule_cs ++ fact_cs in
  let '(cset, cset_events) := audit_finset_of_list audit_positive_encode cs in
  ((present, n, cset), rp_events ++ fp_events ++ [RuAppend (length rule_ps);
    RuPredicatesSet ps pset pset_events; RuPredicateMem p pset present present_events;
    RuArity p n] ++ rc_events ++ fc_events ++ [RuAppend (length rule_cs);
    RuConstantsSet cs cset cset_events]).

Fixpoint ru_constants_check {P} (set : FinSet.t positive) (row : tuple) :
    bool * list (rules_universe_event P) :=
  match row with
  | [] => (true, [RuCase 12])
  | c :: rest =>
      let '(present, mem_events) := audit_finset_mem audit_positive_encode c set in
      let '(tail, events) := @ru_constants_check P set rest in
      (andb present tail, RuCase 12 :: RuConstantMem c set present mem_events :: events ++
        [RuAnd present tail (andb present tail)])
  end.

(** Nat.eqb recurses on the actual unary operands; each pair of constructors is an event. *)
Fixpoint ru_nat_eqb {P} (lhs rhs : nat) : bool * list (rules_universe_event P) :=
  match lhs, rhs with
  | O, O => (true, [RuNatEq O O true])
  | S a, S b =>
      let '(answer, events) := @ru_nat_eqb P a b in (answer, RuNatEq lhs rhs answer :: events)
  | _, _ => (false, [RuNatEq lhs rhs false])
  end.

Definition rules_universe_check_counted {P} (state : bool * nat * FinSet.t positive) (row : tuple) :
    bool * list (rules_universe_event P) :=
  let '(present, n, constants) := state in
  let '(arity_ok, arity_events) := @ru_nat_eqb P (length row) n in
  let first := andb present arity_ok in
  let '(constant_ok, constants_events) := @ru_constants_check P constants row in
  (andb first constant_ok, [RuCase 13; RuLength row] ++ arity_events ++ [RuAnd present arity_ok
  first] ++
    constants_events ++ [RuAnd first constant_ok (andb first constant_ok)]).

Definition rules_universe_erasure_statement : Prop :=
  forall P (prog : program P) facts p row,
    let '(state, _) := rules_universe_prepare_counted prog facts p in
    fst (@rules_universe_check_counted P state row) = in_universe prog facts p row.

Definition rules_universe_event_work {P} (event : rules_universe_event P) : nat :=
  match event with
  | RuPredicatesSet _ _ body | RuPredicateMem _ _ _ body =>
      1 + audit_finset_source_work (@length (rules_encode_entry P)) body
  | RuConstantsSet _ _ body | RuConstantMem _ _ _ body =>
      audit_finset_source_work audit_basic_encoding_work body
  | RuAppend size => 1 + size
  | RuLength row => 1 + length row
  | _ => 1
  end.
Definition rules_universe_event_budget {P} (E : encoding P) (event : rules_universe_event P) :
  nat :=
  match event with
  | RuPredicatesSet input _ _ =>
      12 + 12 * length input + 17 * fold_right (fun p n => Pos.size_nat (encode E p) + n) 0 input
  | RuPredicateMem p _ _ _ => 12 + 17 * Pos.size_nat (encode E p)
  | RuConstantsSet input _ _ =>
      audit_finset_of_list_budget audit_positive_encode audit_basic_encoding_work input
  | RuConstantMem c _ _ _ => 12 + 5 * Pos.size_nat c
  | RuAppend size => 1 + size
  | RuLength row => 1 + length row
  | _ => 1
  end.
Definition rules_universe_work {P} (events : list (rules_universe_event P)) : nat :=
  fold_right (fun event n => rules_universe_event_work event + n) 0 events.
Definition rules_universe_budget {P} (E : encoding P) (events : list (rules_universe_event P)) :
  nat :=
  fold_right (fun event n => rules_universe_event_budget E event + n) 0 events.
Definition rules_universe_selected_cost_statement : Prop :=
  forall P (prog : program P) facts p row,
    let '(state, prep_events) := rules_universe_prepare_counted prog facts p in
    let '(result, check_events) := @rules_universe_check_counted P state row in
    result = in_universe prog facts p row /\
    rules_universe_work (prep_events ++ check_events) <=
      rules_universe_budget (penc prog) (prep_events ++ check_events).
```

### Future proofs in `RulesAuditAtomFoldAdequacy`

Card: AUD-RU-DATA

Source destination: `theories/Rules/RulesAuditAtomFoldAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditAtomFold.

Theorem rules_atom_fold_erasure :
  RulesAuditAtomFold.rules_atom_fold_erasure_statement.
Theorem rules_atom_fold_selected_cost :
  RulesAuditAtomFold.rules_atom_fold_selected_cost_statement.
Theorem rules_atom_fold_input_bound :
  RulesAuditAtomFold.rules_atom_fold_input_bound_statement.
Theorem rules_delta_index_input_bound :
  RulesAuditAtomFold.rules_delta_index_input_bound_statement.
Theorem rules_atom_fold_run_total :
  RulesAuditAtomFold.rules_atom_fold_run_total_statement.
Theorem rules_atom_fold_run_unique :
  RulesAuditAtomFold.rules_atom_fold_run_unique_statement.
Theorem rules_atom_fold_run_erasure :
  RulesAuditAtomFold.rules_atom_fold_run_erasure_statement.
```

### Future proofs in `RulesAuditCostAdequacy`

Card: AUD-RU-JOIN

Source destination: `theories/Rules/RulesAuditCostAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditCost.

Theorem rules_index_cost_holds :
  RulesAuditCost.rules_index_cost.
```

### Future proofs in `RulesAuditDeltaRowsAdequacy`

Card: AUD-RU-DATA

Source destination: `theories/Rules/RulesAuditDeltaRowsAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditDeltaRows.

Theorem rules_delta_rows_erasure :
  RulesAuditDeltaRows.rules_delta_rows_erasure_statement.
Theorem rules_delta_rows_snapshot_cost :
  RulesAuditDeltaRows.rules_delta_rows_snapshot_cost_statement.
Theorem rules_delta_rows_input_bound :
  RulesAuditDeltaRows.rules_delta_rows_input_bound_statement.
```

### Future proofs in `RulesAuditFiringAdequacy`

Card: AUD-RU-JOIN

Source destination: `theories/Rules/RulesAuditFiringAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditFiring.

Theorem rules_firing_tail_input_bound :
  RulesAuditFiring.rules_firing_tail_input_bound_statement.
```

### Future proofs in `RulesAuditFiringCallbacksAdequacy`

Card: AUD-RU-JOIN

Source destination: `theories/Rules/RulesAuditFiringCallbacksAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditFiringCallbacks.

Theorem rules_firing_tail_source :
  RulesAuditFiringCallbacks.rules_firing_tail_source_statement.
```

### Future proofs in `RulesAuditIndexAdequacy`

Card: AUD-RU-INDEX

Source destination: `theories/Rules/RulesAuditIndexAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditIndex.

Theorem mat_index_full_erases :
  RulesAuditIndex.mat_index_full_erases_statement.
Theorem mat_index_full_input_bound :
  RulesAuditIndex.mat_index_full_input_bound_statement.
Theorem mat_variable_full_input_bound :
  RulesAuditIndex.mat_variable_full_input_bound_statement.
Theorem mat_index_full_source :
  RulesAuditIndex.mat_index_full_source_statement.
```

### Future proofs in `RulesAuditIndexCountsAdequacy`

Card: AUD-RU-INDEX

Source destination: `theories/Rules/RulesAuditIndexCountsAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditIndexCounts.

Theorem mat_index_row_counts :
  RulesAuditIndexCounts.mat_index_row_counts_statement.
Theorem mat_index_fold_counts :
  RulesAuditIndexCounts.mat_index_fold_counts_statement.
Theorem mat_index_add_run_total :
  RulesAuditIndexCounts.mat_index_add_run_total_statement.
```

### Future proofs in `RulesAuditJoinAdequacy`

Card: AUD-RU-JOIN

Source destination: `theories/Rules/RulesAuditJoinAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditJoin.

Theorem rules_join_firing_input_bound :
  RulesAuditJoin.rules_join_firing_input_bound_statement.
Theorem rules_join_firing_source :
  RulesAuditJoin.rules_join_firing_source_statement.
Theorem rules_join_agrees_holds :
  RulesAuditJoin.rules_join_agrees.
```

### Future proofs in `RulesAuditJoinSyntaxAdequacy`

Card: AUD-RU-PREP

Source destination: `theories/Rules/RulesAuditJoinSyntaxAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditJoinSyntax.

Theorem mat_join_syntax_erasure :
  RulesAuditJoinSyntax.mat_join_syntax_erasure_statement.
```

### Future proofs in `RulesAuditMultiwayPrepareAdequacy`

Card: AUD-RU-MULTIWAY

Source destination: `theories/Rules/RulesAuditMultiwayPrepareAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditMultiwayPrepare.

Theorem rules_prepare_multiway_full_erases :
  RulesAuditMultiwayPrepare.rules_prepare_multiway_full_erases_statement.
```

### Future proofs in `RulesAuditMultiwayProbeAdequacy`

Card: AUD-RU-MULTIWAY

Source destination: `theories/Rules/RulesAuditMultiwayProbeAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditMultiwayProbe.

Theorem rules_multiway_probe_erasure :
  RulesAuditMultiwayProbe.rules_multiway_probe_erasure_statement.
Theorem rules_run_multiway_selected_cost :
  RulesAuditMultiwayProbe.rules_run_multiway_selected_cost_statement.
```

### Future proofs in `RulesAuditMultiwaySelectionAdequacy`

Card: AUD-RU-MULTIWAY

Source destination: `theories/Rules/RulesAuditMultiwaySelectionAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditMultiwaySelection.

Theorem rules_multiway_selection_count :
  RulesAuditMultiwaySelection.rules_multiway_selection_count_statement.
Theorem rules_multiway_selection_input_bound :
  RulesAuditMultiwaySelection.rules_multiway_selection_input_bound_statement.
Theorem rules_multiway_selection_source :
  RulesAuditMultiwaySelection.rules_multiway_selection_source_statement.
```

### Future proofs in `RulesAuditNestedPrepareAdequacy`

Card: AUD-RU-NESTED

Source destination: `theories/Rules/RulesAuditNestedPrepareAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditNestedPrepare.

Theorem rules_prepare_nested_full_erases :
  RulesAuditNestedPrepare.rules_prepare_nested_full_erases_statement.
Theorem rules_prepare_nested_full_input_bound :
  RulesAuditNestedPrepare.rules_prepare_nested_full_input_bound_statement.
```

### Future proofs in `RulesAuditNestedProbeAdequacy`

Card: AUD-RU-INDEX

Source destination: `theories/Rules/RulesAuditNestedProbeAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditNestedProbe.

Theorem rules_nested_probe_erasure :
  RulesAuditNestedProbe.rules_nested_probe_erasure_statement.
Theorem rules_run_nested_selected_cost :
  RulesAuditNestedProbe.rules_run_nested_selected_cost_statement.
```

### Future proofs in `RulesAuditNestedSelectionAdequacy`

Card: AUD-RU-NESTED

Source destination: `theories/Rules/RulesAuditNestedSelectionAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditNestedSelection.

Theorem rules_nested_selection_input_bound :
  RulesAuditNestedSelection.rules_nested_selection_input_bound_statement.
Theorem rules_nested_selection_source :
  RulesAuditNestedSelection.rules_nested_selection_source_statement.
```

### Future proofs in `RulesAuditPrepareCallbacksAdequacy`

Card: AUD-RU-PREP

Source destination: `theories/Rules/RulesAuditPrepareCallbacksAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditPrepareCallbacks.

Theorem rules_nested_prepare_source :
  RulesAuditPrepareCallbacks.rules_nested_prepare_source_statement.
Theorem rules_multiway_prepare_source :
  RulesAuditPrepareCallbacks.rules_multiway_prepare_source_statement.
```

### Future proofs in `RulesAuditRelationCallbacksAdequacy`

Card: AUD-RU-DATA

Source destination: `theories/Rules/RulesAuditRelationCallbacksAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditRelationCallbacks.

Theorem rules_relations_external_source :
  RulesAuditRelationCallbacks.rules_relations_external_source_statement.
```

### Future proofs in `RulesAuditRelationsAdequacy`

Card: AUD-RU-DATA

Source destination: `theories/Rules/RulesAuditRelationsAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditRelations.

Theorem rules_join_relations_erasure :
  RulesAuditRelations.rules_join_relations_erasure_statement.
Theorem rules_join_relations_row_count :
  RulesAuditRelations.rules_join_relations_row_count_statement.
Theorem rules_join_relations_selected_cost :
  RulesAuditRelations.rules_join_relations_selected_cost_statement.
Theorem rules_join_relations_input_bound :
  RulesAuditRelations.rules_join_relations_input_bound_statement.
```

### Future proofs in `RulesAuditTerminalAdequacy`

Card: AUD-RU-JOIN

Source destination: `theories/Rules/RulesAuditTerminalAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditTerminal.

Theorem rules_terminal_erasure :
  RulesAuditTerminal.rules_terminal_erasure_statement.
Theorem rules_terminal_selected_cost :
  RulesAuditTerminal.rules_terminal_selected_cost_statement.
```

### Future proofs in `RulesAuditTerminalCallbacksAdequacy`

Card: AUD-RU-JOIN

Source destination: `theories/Rules/RulesAuditTerminalCallbacksAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditTerminalCallbacks.

Theorem rules_positive_filter_erasure :
  RulesAuditTerminalCallbacks.rules_positive_filter_erasure_statement.
```

### Future proofs in `RulesAuditUniverseAdequacy`

Card: AUD-RU-DATA

Source destination: `theories/Rules/RulesAuditUniverseAdequacy.v`.

```rocq
From Galois.Rules Require Import RulesAuditUniverse.

Theorem rules_universe_erasure :
  RulesAuditUniverse.rules_universe_erasure_statement.
Theorem rules_universe_selected_cost :
  RulesAuditUniverse.rules_universe_selected_cost_statement.
```

<!-- AUD-API-RU-END -->

### Materialization model examples

Card: AUD-RU-MAT-BASE

Test destination: `tests/Rules/RulesAuditMaterializeModelsExamples.v`.
The future closed examples compute a nonempty materialized result and a finite difference
observation. Universal theorems remain with their named proof cards.
