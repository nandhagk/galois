Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Extensible equality saturation and proved rewriting

Research snapshot and cutoff: 2026-10-28. This report proposes a generic Gaulois framework; it
does not change a public contract, card, source file, decision or ledger. No implementation was
built or benchmarked. External papers, artifacts and source inspection provide design evidence,
not Gaulois correctness evidence. The implementer remains paused pending owner approval.

The recommended direction is a reusable, language-parametric equality kernel and directly proved,
bounded equality-saturation engine. Clients supply operators, typing, semantic interpretations,
rules and rule proofs, optional analyses, and costs. Keep a small independent explanation checker
for external producers and preserve ANA-6's contracted checked pipeline until an approved
replacement and compatibility proof exist. Requiring every internal result to traverse an
untrusted-producer interface would discard the benefit of a direct proof; removing current
validation without an owner ruling would violate C7 and C12.

The proposed design is an inference from the sources and Gaulois constraints, not a claim that
egg, egglog or an external formalization already implements these exact interfaces.

## Scope and primary-source audit

The search covered the original egg and egglog papers; relational e-matching; proof explanations;
2023–2026 work on context, guided saturation, semantic foundations, extraction, extensibility and
cyclic-program analysis; official egg 0.11.0 APIs/source; and current official egglog documentation,
release notes and tutorial. It is a scoped survey, not an assertion that every publication was
found. A source dated after the cutoff is not treated as an established publication at the cutoff.

Classical foundations are congruence closure, term rewriting and equality saturation as developed
by Nelson, Nieuwenhuis and Oliveras, and Tate et al. The relevant modern developments are:

- **2021, egg:** rebuilding defers restoration of congruence and canonicalization across batches;
  e-class analyses integrate domain reasoning with rewriting. Its reusable-library architecture,
  rather than any particular arithmetic rule set, is the main model for this proposal. The paper's
  workload measurements do not predict extracted Gaulois performance. [egg paper][egg]
- **2022, relational e-matching:** compile patterns into conjunctive queries, exploiting repeated
  variables and joins instead of committing to top-down structural traversal. Worst-case optimal
  join bounds concern a fixed query and a specified relational cost model; they do not make
  arbitrary-size matching easy or include all index construction for free. The ACM record lists
  a March 2022 corrigendum; an implementation card must consult it before adopting a precise
  complexity theorem. [Paper][rem], [publication record][rem-record]
- **2022, explanations:** proof generation and proof minimization are separate from finding
  equalities. Flatt et al. describe practical small-proof generation and a different, relaxed
  proof-tree optimality metric. A short certificate is useful but does not verify the producer.
  [Small Proofs from Congruence Closure][small-proofs]
- **2023, egglog:** equality-aware functional tables, relational rules and merge operations unify
  Datalog and EqSat, supporting cooperating analyses and incremental execution. This motivates
  sharing Gaulois query machinery; it does not establish equality with Gaulois's present
  stratified-Datalog perfect model. [Original PLDI paper][egglog-paper]
- **2023, colored e-graphs:** share structure between congruence relations under different
  assumptions while tracking which equalities are conditional. Treat this as an optional context
  backend, not permission to put branch-local equalities in a global union-find. The inspected
  source is the authors' preprint. [Colored E-Graph][colored]
- **2024, guided equality saturation:** sketches and staged exploration can control search and
  extraction without making all rewrite combinations affordable. Guidance changes explored
  candidates, not the semantic justification for a merge. [Guided Equality Saturation][guided]
- **2024, extraction:** exact shared/DAG extraction has substantially different complexity from
  local tree extraction. Low-treewidth parameterization offers a conditional exact approach;
  general hardness and approximation results rule out a universal cheap optimum promise.
  [Fast and Optimal Extraction for Sparse Equality Graphs][sparse-extract]
- **2025, semantic foundations:** tree-automata/fixpoint semantics and a connection to the chase
  separate saturation's mathematical closure from a finite execution. Termination is studied
  explicitly, with a syntactic sufficient criterion; arbitrary rule registration cannot carry
  an unconditional saturation-termination promise. [ICDT paper][foundations]
- **2025, contextual relational reasoning:** the inspected preprint was uploaded in July 2025 and
  says it appeared at EGRAPHS 2024. It describes ongoing work and challenges, not a completed
  verified contextual egglog. [Towards Relational Contextual Equality Saturation][contextual]
- **2025–2026, official egglog evolution:** version 1.0 introduced the database-first parallel
  backend in October 2025; 2.0 added proof preparation and term encoding in February 2026; 3.0
  was released in August 2026. Main-branch APIs continue changing. The old blanket statement
  that egglog has no proof support is stale; proof-mode command support and primitive validators
  must be checked for the selected version. Runtime proof generation is not a Rocq theorem.
  [Official changelog][egglog-changelog], [current API][egglog-api]
- **2026, customizable saturation:** composable strategies, deferred commands and generalized
  metadata are a useful design precedent for extensibility without editing the core. The CC
  paper and artifact evaluate a Scala implementation; their speedups are workload-specific,
  and parallelism is not a prerequisite for Gaulois's first proved engine. [Paper][foresight],
  [artifact][foresight-artifact]
- **2026, optimism:** ordinary optimistic abstract interpretation applied to cyclic program
  e-graphs can be unsound. Arbore et al. give a specific sound algorithm and SSA semantics.
  This is a strong reason to keep finite expression-grammar cycles distinct from recursive
  program/control cycles. [Optimism in Equality Saturation][optimism]
- **July 2026, an Isabelle checker:** the AFP development checks chronological merges and flat
  egg explanations and proves minimum additive extraction for a topologically ordered e-class
  DAG. Its acyclic extraction scope must not be silently generalized to cyclic graphs, nor
  its Isabelle assumptions transferred into the Stdlib-only Gaulois core. [AFP entry][afp]
- **Available at cutoff, forthcoming 2027:** the authors' page for a conditionally accepted
  POPL'27 paper claims an object-language-generic, verified Rocq EqSat procedure following
  egglog. The page says the paper is coming soon; no detailed paper or artifact was exposed
  there during this audit. This is a relevant feasibility lead, not an inspected proof result
  or a justification for claiming that the proposed Gaulois engine is already routine.
  [Author announcement][verified-rocq]

The recent work supports a generic core with explicit extension points. It does not establish one
uniformly fastest matcher, scheduler, analysis or extractor. Correctness proofs and meaningful
examples are required. A new benchmark suite or a mandatory benchmark gate is not recommended.

## What the actual ANA-6 contract already supports

The source of truth is `historical API contracts`, ANA-6 definitions at lines 663–722 and theorems at
1654–1681, together with `historical card ANA-6.md`. It is inaccurate to describe this as a fixed
Bits-only rewriter:

- `term K` has arbitrary operator keys `K`, arbitrary argument lists and variable indices.
  An injective `encoding K` supplies decidable structural equality.
- `denote` uses any client `ev : K -> list C -> option C`; `ok` restricts environments.
  There is no required Bits interpretation or fixed word width.
- A `rewrite_rule K` contains left/right terms and a Boolean condition on term substitutions.
  A client must prove `rule_sound ev ok` for every accepted substitution.
- Positional explanation steps name a rule, direction and explicit substitution. Replay verifies
  the source instance, condition and replacement. The checker lifts local equality through term
  contexts and checks the final term.
- `optimise_sound` promises equivalence and nonincreasing additive operator cost **when** the
  pipeline returns `Some`. It does not prove that saturation or extraction is correct, finds
  a result, saturates, terminates without fuel, or obtains an optimum.
- The nontrivial `egraph_optimise_accepts` example prevents satisfying the API only with an
  always-failing producer. It is still example evidence, not producer completeness.

Thus a new encoded operator, a fixed-arity or variadic application, a syntactic sort guard,
constant folding or an arbitrary sound first-order equation is already expressible without
changing this syntax. A rule schema can also be instantiated by client Gallina code. The existing
API's limitations concern supplied abstractions and proved algorithms, not operator openness.

The precise missing reusable capabilities are:

| Area | Existing ANA-6 | Proposed addition |
| --- | --- | --- |
| Typing | Environments constrained by `ok` | Checked signatures, terms and substitutions |
| Variables | `TVar nat` used in terms and patterns | Separate object variables and pattern holes |
| Rule conditions | Boolean on term substitution | E-class facts and explicit context evidence |
| Rule families | Client-generated lists | Reusable typed schemas and registration helpers |
| Congruence | Abstract untrusted e-graph | Proved add, union, canonicalization and rebuild |
| Search | Unspecified saturation | Indexed sound matching and a bounded proved runner |
| Analysis | No public hook interface | Lawful semantic analyses and justified actions |
| Cost | Sum of `K -> nat` weights | Compositional tree models; separate DAG interfaces |
| Proof path | Full positional term replay | Shared equality kernel plus optional compact proofs |
| Optimality | Cost no worse on acceptance | Separate exactness within a represented grammar |

DOM-7 is also not this framework: its equality partition intersects facts at joins, while its
symbolic expression keys are Bits-specific and sort arguments only for proved commutative Bits
operators. Reuse Collections' union-find and encoded tables; do not reuse that normalization for
arbitrary client operators without laws. A persistent monotone e-graph union is not the same
analysis as a mutable-variable must-equality partition with forget and intersection.

Two contract details need explicit owner attention during the next API review, rather than a
silent redesign. First, `equiv_term` equates equal `option` results and therefore allows
`None = None`; its introductory prose says both sides are defined. The theorem's actual scope
is equality of the partial evaluator's outcomes. Second, the replay contract must specify how a
finite `step_subst` supplies every referenced variable, or reject missing entries. Neither issue
authorizes changing the existing statements during research. A minimal implementation repair,
if necessary, follows C14 and is recorded exactly; a meaning change requires an owner ruling.

## One extensible public architecture

Use a first-order, many-sorted expression core. All names below are proposed interface roles,
not approved public declarations. Parameterize records by their types; put laws in separate
`Prop` records. Never add a carrier `Type` field, global instances or axioms. Executable data
uses Stdlib and Collections' injective encodings and canonical tries. The engine does not depend
on Bits, Domains, Views, Rules, Float or a particular compiler; adapters can depend on it.

The framework needs seven separable interfaces:

1. **Language and terms.** A `signature O S` supplies a decidable application-typing function
   from an operator and argument sorts to an optional result sort. Separate encoded object
   variable keys `Q`, encoded pattern keys `P`, sorts `S` and operators `O`. Terms contain free
   object variables and applications; patterns additionally contain holes. Operator data includes
   every semantic parameter: literal payload, width, type, rounding, overflow flags and address
   space where relevant. Typing laws establish deterministic result sorts and well-formed nodes.
   A fixed-arity helper takes an input-sort list and output sort; a variadic helper checks a
   finite argument-sort list. For example, a tuple constructor and a homogeneous variadic sum
   need no engine change. Typechecking, key encoding and traversing large arities still cost work.
2. **Interpretation and equality.** A client supplies an interpretation into observations `V`,
   an admissible environment/context predicate, and the congruence laws of its chosen semantic
   equality. A standard adapter interprets strict deterministic partial operations with
   `option C`, matching ANA-6. A richer client can choose outcomes that retain traps or events,
   but must prove contextual congruence for the represented language. The generic equality
   derivation contains reflexivity, symmetry, transitivity, operator congruence and registered
   rule instances. Its soundness theorem is the small reusable proof boundary.
3. **Patterns, schemas and rules.** Finite sorted substitutions map holes to e-class IDs during
   matching, and to term witnesses for semantic statements. Repeated holes require the same
   canonical class. RHS holes and condition dependencies must be bound by the LHS/multipattern,
   or introduced by an explicitly specified witness-producing schema. A rule contains patterns,
   direction, a condition descriptor and a stable encoded identity. Its separate law proves
   equal observations for every well-typed substitution satisfying that condition. The same
   rule instantiation operation is shared by every matcher and runner.
4. **Conditions.** A condition checks a read-only clean e-graph, substitution, validated analysis
   facts and explicit context. Its separate law converts success into the premise needed by
   the rule. A class-fact condition establishes that premise for every represented term witness;
   a syntactic condition may instead select explicit finite term witnesses, validate the premise
   for those witnesses, and justify that exact instance before transporting equality through the
   class relation. This preserves ANA-6's arbitrary substitution guards without assuming that
   syntax tests are invariant under equality. Conditions can check sorts, constants, nonzero
   ranges, no-overflow evidence or domination. A heuristic score is not semantic evidence.
   External condition witnesses must pass a proved validator or carry a reconstructed Rocq proof.
5. **E-graph operations.** Hide class storage behind add/find/merge/rebuild and representation
   predicates. A semantic merge always requires a justified equality; no unrestricted client
   `union` may authorize an optimizer result. Internal Gallina laws can discharge justification
   directly, while external commands supply certificates. Clean graphs expose matching and
   validated facts; dirty graphs expose only operations whose weaker invariant is proved.
6. **Analysis and strategies.** An explicit `analysis O S A` supplies initial unknown facts,
   node transfer, fact combination, change detection and a read-only hook producing proposed
   add/merge actions. Laws are separate. A strategy selects rules, matches and safe commands,
   then sequences bounded search/apply/rebuild phases. It cannot bypass typing or justification.
   Trivial unit analysis and a simple all-rules schedule are useful defaults.
7. **Extraction and results.** A tree cost model takes an operator, sort and child costs to a
   cost in a client type with an explicit lawful comparison, with a separate cost for free
   variable leaves. Extraction returns a finite term
   with a representation witness, cost and optional explanation. A result records why the run
   stopped. Semantic preservation, cost improvement and minimum cost are separate claims.

This separation allows a new operator or theory to contribute a signature extension, encoding,
interpretation, rules, rule proofs and optional analysis/cost extensions. The congruence engine,
matcher and runner are unchanged. A sum-signature helper must prove that injection preserves
typing, encoding and denotation; a module's rule proof is reused through this embedding. Mixed
theory rules, such as integer/float conversion identities, need new proofs about the combination.
Independent sound theories do not establish an arbitrary mixed identity automatically.

For infinitely parameterized families, such as all widths or literal payloads, a client can
register a proved rule schema parameterized by width/value and a finite instance enumerator
indexed by operators or sorts currently present. Prove each generated instance sound uniformly;
completeness is only for the enumerator's declared coverage. Do not enumerate all integers, add
operator metavariables without binding laws, or promise every sound schema instance is found.

### Registration ergonomics and the binding boundary

The initial user interface should be ordinary typed Gallina constructors with compact helpers:
operator declarations, checked pattern builders, named rules, composable rule bundles and a
`proved_rule` helper pairing executable data with its `Prop` theorem. A rule needs a name,
patterns, guard and proof once; applying it to many inputs should not require client manipulation
of union-find or proof derivations. Use explicit dictionaries even in convenience APIs.

A small notation layer may elaborate `add_zero`, `mul_one` or guarded `div_self` declarations to
those constructors. A parser or generated DSL is optional and must elaborate to checked data;
string parsing is not part of the semantic trust boundary. Do not require a Rust plugin, code
generator or new theory module for an ordinary rule. Dynamic constant folding can be a proved
action producer instead of materializing a separate static rule for every literal combination.

Arbitrary operators and sorts do not by themselves solve binders. Treat lambda, let and quantified
forms as opaque client nodes until a binding-aware adapter proves alpha-equivalence, weakening,
capture-avoiding substitution, and congruence under extended environments. A de Bruijn encoding
alone does not establish beta reduction soundness. The first-order core may manipulate an encoded
binder only under rules whose client proofs cover scope; it must not confuse pattern holes,
object-language variables and bound indices. Binding-aware patterns are a separate extension.

## Semantic boundaries that rule registration must preserve

ANA-6's `ev` is a pure deterministic mathematical function of its argument values. It cannot,
without a different adapter and laws, model mutable reads, nondeterminism, event ordering,
allocation identity or repeated evaluations with effects. An SSA adapter should initially build
expression regions from proved pure operations and available operand values. It must prove the
region interpretation and replacement theorem, including dominance/availability of operands.
Equality between expression trees alone is not a program transformation theorem.

Partiality is also observable. A sort test proves the type of `x`; it does not prove that computing
`x` returns. In a strict partial language, `(x * 0)` may fail when `x` fails, while `0` returns.
Thus `x * 0 = 0` needs total defined integer operands, or a condition proving the discarded
computation defined and effect-free. Even an integer type is insufficient by itself. `x * 1 = x`
preserves partiality for a compatible strict multiplication but still needs its operator theorem.

The one-way Bits bridge states that a successful client operation has the specified Bits result;
it says nothing when the client traps. It therefore does not justify changing a trapping client
division to a total Bits expression. Use a two-way outcome equivalence for rewrites, or prove
the required no-trap premise. SSA variables read from an admissible environment are already
values; a nested partial expression is not automatically an already-computed SSA value.

Other explicit boundaries are:

- Modular words, mathematical integers, saturating arithmetic and no-overflow arithmetic have
  different equations. Encode flags and width, and prove each rule for its actual operation.
- Float rules must retain NaN, signed zero, rounding and any observable exceptions under the
  client's equality. Real-number algebra does not establish IEEE equivalence. Keep Flocq and
  exactly C13's permitted assumptions in the optional Float adapter; the equality core remains
  axiom-free. A weaker float equivalence needs an explicit observation contract.
- Undefined behavior or poison requires the client's specified equality/refinement relation.
  A directional refinement cannot be inserted as a symmetric e-class equality. Keep refinement
  edges in a separate proved layer unless bidirectional observational equivalence is established.
- Evaluation count and order, memory versions, effects, traps, divergence and resource stops
  matter when moving from expressions to programs. Use Views' appropriate behavior theorem;
  retaining traps and dropping unread traps have different guarantees in the existing contracts.
- A branch fact is valid only under its path/context. Either freeze a context predicate for the
  whole run or keep per-context equivalences. Never merge a branch-local `x = 0` globally.
  Do not export a context-specialized replacement outside the region where its premises hold.

These are proof obligations arising from the proposed semantic interface, not a request to add
a general effectful-program EqSat system to the first delivery.

## Congruence, canonicalization and rebuilding

An application e-node is an operator plus a finite list of child classes and its validated result
sort. Free-variable leaves have a distinct key tag and encoded variable identity. Application keys
contain the encoded operator and canonical child IDs; distinct semantic flags cannot collide.
Use Collections' `Table`, which is a canonical trie map on encoded lists, rather than claim a
machine hash table's expected constant-time lookup. Hash-consing here means unique-node interning.

The implementation maintains class-to-node membership, node-to-class interning, operator/arity/sort
search indexes, and child-to-parent incidence indexes. Store parent incidence sets keyed by node
identity so repeated references can be processed deliberately. A merge finds representatives,
checks sorts and equality evidence, unions classes and enqueues affected parents. Batch rebuild
canonicalizes those parents, repairs table/index entries and merges duplicate canonical nodes.
Deduplicate work; do not rescan every e-class after each merge.

The central invariants should be stated separately:

1. **Storage:** every referenced ID is allocated; roots and memberships agree with union-find;
   maps, sets and tables are well formed; child and result sorts agree with the signature.
2. **Representation:** an inductive finite derivation says which finite terms each class
   represents. Cyclic graphs can represent infinitely many finite trees; no coinductive infinite
   term is silently treated as an executable output.
3. **Equality:** any represented terms in equivalent classes have a derivable equality and hence
   equal client observations under the context. Every semantic union has a rule/congruence reason.
4. **Clean congruence:** canonical equal e-nodes have equivalent owners, and interning/search
   indexes correspond to canonical storage. This is a stronger phase-boundary invariant.
5. **Pending work:** every parent/index/analysis entry invalidated by a union is either repaired
   or covered by queued work. A dirty graph preserves soundness and represented input terms;
   it may temporarily miss congruences or matches.
6. **Facts:** every condition-visible analysis fact has the declared semantic validity, including
   after unions and partial rebuilding. Otherwise it is marked unavailable for guards.

Prove `find` preserves equivalence, add represents its input and adds only reflexive/congruent
facts, justified merge preserves semantic equality, and repair collision implies congruence.
Then prove bounded rebuilding preserves soundness at every step; if pending repair is empty,
the graph is clean. A full closure/termination theorem is distinct: for a fixed finite graph,
union strictly reduces the class count and a work measure must account for all enqueued repairs.
Analysis hooks that add nodes are excluded from that finite-closure argument unless separately
bounded. A fuel stop cannot be reported as restored congruence merely because the outer iteration
ended. Return a resumable dirty state or the last clean snapshot and its reason.

Rebuilding is the selected default for batched saturation. An eager operation can be exposed as
merge followed by complete rebuild for consumers needing a clean graph after every update; it
does not require a second complete engine. Persistent union-find/trie costs must include encoding
lengths and map traversals. Do not import mutable union-find's inverse-Ackermann amortized bound
into this persistent implementation without its own proof and usage assumptions.

## Matching and sharing the rule engine

The matcher should specify a set of substitutions, modulo canonical class IDs. Soundness says
every returned substitution has finite witnesses satisfying the pattern and sort constraints.
Completeness, where claimed, says every such represented match occurs in the result on a clean
graph. Neither property says the rewrite is semantically sound; that comes from rule laws and
condition evidence. Incomplete search can remain sound and must be labelled accordingly.

Offer two consumer-selectable implementations behind that specification where useful:

- An indexed conventional matcher uses the root operator/arity/sort to choose candidates, then
  traverses the pattern, checking repeated holes as soon as bound. It is a sensible first backend
  for small patterns and small graphs, with low setup overhead. Structural recursion terminates
  on finite patterns even when the represented e-graph is cyclic; repeated subqueries can still
  be expensive. Match limits return a sound prefix, not a complete result.
- A relational matcher stores operator relations of the form `(owner, child1, ..., childN)` and
  compiles a pattern to a conjunctive query. For example, `f(?x, g(?x, ?y))` joins an `f` row with
  a `g` row and constrains the two `?x` columns equal. Multipatterns are ordinary shared-variable
  joins. Indexed binary joins suit selective/tree-like patterns; a verified generic multiway join
  can avoid poor intermediate results on cyclic query shapes. Include index preparation, quotient
  repair, result enumeration and query size in the cost model. A fixed-pattern worst-case bound
  is not a universal total EqSat complexity bound. [Relational e-matching][rem]

Both backends call the same checked or directly proved substitution/instantiation operation and
can prove set equality of matches when unbounded. Do not build a second matcher solely for a
benchmark comparison. Reuse the Rules track's verified positive-query representation and joins
if their actual semantics fit; equality-changing keys still need their own repair lemmas.

Official egg separates `Searcher`, `Applier` and `Condition`, with substitutions mapping variables
to class IDs. Its `MultiPattern` API explicitly says explanations are unsupported. That is a
concrete reason not to assume every useful external search result can be sent through the current
flat explanation route. For external multipatterns, require supported per-merge certificates or
use the directly proved matcher and action engine. [Pattern APIs][egg-multi], [conditions][egg-cond]

### Optional equality-aware relations and egglog-style composition

Add an explicit relational module over the same core when consumers need multiple cooperating
analyses or multipattern rules. Distinguish unionable term sorts from base-value sorts. Constructor
tables map canonical child classes to a result class; relation tables contain tuples; analysis
tables map class keys to validated facts. Conflicting constructor outputs require justified
congruence unions. Conflicting analysis values use a separately lawful combination operation.
Each primitive operation has a declared interpretation and proof or a proved validator.

The key new invariant is quotient agreement: after a class union, all affected table keys,
columns, functional dependencies, indexes and pending deltas must denote the same relations
modulo the new equivalence. An old tuple may acquire a new join partner solely because IDs
became equal. Therefore a semi-naive engine must treat equality-induced canonicalization as
new query work, including old rows that have become joinable; looking only at newly inserted
raw tuples is incomplete. The original egglog paper motivates precisely this interaction between
functional tables, equality and rebuilding. [PLDI paper][egglog-paper]

For a first module, support positive premises and monotone information-producing actions with
bounded execution. Prove every derived semantic fact and equality sound by induction over rule
firings, then prove a fixed-point/leastness result only for its declared semantic order, merge
laws, finite-closure and fair scheduling hypotheses. Recursive term construction can create an
unbounded carrier; current Rules' finite-universe proof does not establish termination here.

Keep Gaulois Rules' stratified-negation perfect-model API intact. Negation over unfinished
relations is unsafe, and even completed rows can change meaning when the relevant equality
quotient changes. A negation extension needs frozen lower-stratum facts and relevant equivalence,
or a proved invalidation/recomputation scheme. Retraction, deletion, subsumption and nonmonotone
overwrite likewise need support tracking or recomputation; `push/pop` storage behavior alone is
not an incremental semantic theorem. Context-labelled relations require their own leakage laws.

Modular theories may share positive facts and equality through explicit embeddings and action
laws. Their union preserves soundness when every rule law is valid in the combined interpretation.
It does not guarantee termination, complete theory combination, common-model consistency of
arbitrary assumptions, or a perfect model for every merge policy. Reuse verified query/index
components from R-RULE/R-DELTA, without adding an unproved egglog semantics to those existing
contracts. This optional module is justified by its consumers, not required by a basic term client.

## Lawful e-class analyses and safe extension hooks

The official egg analysis API separates node fact construction, fact merging and an e-graph
modification hook; change flags determine propagation. It also warns against reinserting a node
inside its construction hook and allows matching-cycle restrictions that can miss equalities.
Gaulois should preserve extensibility while making the laws explicit. [Analysis API][egg-analysis]

Use two distinct extension categories:

- **Semantic facts** have a concretization or validity predicate relative to a context and class.
  Examples are a known constant, a nonzero result, totality, a type fact or a safe numeric bound.
  A node-transfer theorem builds valid facts from valid child facts. Fact combination preserves
  validity for equal class denotations. Change detection must not miss a change requiring parent
  propagation. All guard reads use the canonical class and a validated fact.
- **Heuristic metadata** may include rewrite counts, preferred representatives, source locations,
  estimated cost and scheduling priority. It has storage/update laws if needed but cannot prove
  a semantic premise or authorize a union. It may propose a candidate for independent validation.

For a semantic fact meaning `P a v`, a safe combine law can require that if both input facts hold
of the common value `v`, then the combined fact holds of `v`. This supports an intersection-like
combination of independent information about equal terms. A conventional overapproximate join is
also sound but may lose precision. Do not require all existing weak Gaulois domains to become
least-upper-bound semilattices. Stronger algebraic or convergence laws should be optional records
for backends that need schedule independence, exact fixed points or an unbounded terminating pass.

Bottom requires care. A fact with empty concretization is not an unknown fact for a nonempty
class. Initialize conservatively, track uninitialized entries separately, and make the class fact
sound before a guard can use it. A newly added node may temporarily weaken available facts until
its sound transfer is integrated. Transporting a useful fact from one equivalent term to all
class members requires the equality invariant and a predicate stable under the chosen semantic
equality. Facts about successful results alone do not prove that a partial term is defined.

Make hooks pure action producers. Each proposed constant-folding node or merge has either a
uniform Gallina theorem or an explicit certificate checked by the kernel. Separate analysis
propagation from action application and charge both against fuel. A hook can add infinitely many
nodes; monotonicity does not imply convergence. Finite-height facts plus monotone propagation on
a fixed finite graph support a termination proof. Widening or explicit fuel supports sound bounded
results under weaker conditions. Refined facts from a context are invalid outside that context.

Keep two kinds of cycles separate. Expression-grammar cycles introduced by proved equalities can
be handled with induction on finite represented terms and incrementally sound facts. SSA phi and
recursive program cycles encode execution itself and need a different semantic invariant. Do not
initialize such cycles optimistically and accept any equation solution as a sound analysis. The
2026 optimism paper demonstrates the failure of that shortcut. Supporting its stronger analysis
is a separate card after a compatible SSA-cycle semantics is proved. [Optimism paper][optimism]

## Scheduling, budgets and the meaning of saturation

The official egg runner exposes iteration, node and time limits, custom scheduling, hooks and
stop reasons. Its limits are practical controls rather than proofs that all equational search
terminates. Egglog also makes rulesets and scheduling explicit. [Runner API][egg-runner],
[egglog scheduling][egglog-schedule]

Use a finite strategy description or an explicit bounded transition function. Useful combinators
are sequence, choose a rule bundle, bounded repeat, search/apply batch, rebuild and stop on a
specified goal. Backoff and match quotas control explosive rules; staged normalization and
expansion can be supplied by clients. All strategies preserve the same semantic invariant.

Use binary fuel for actual primitive work, not only outer iterations. Matching a large query,
analysis callbacks and rebuild must themselves be structurally terminating, bounded or
well-founded; otherwise an outer iteration counter does not make the whole run bounded. Track
node/class limits before allocation, and a command budget before a large batch. An extracted
wrapper may use a wall-clock timeout to interrupt only at safe boundaries; no real-time theorem
is implied by the pure Rocq fuel proof.

Return a result with roots, graph state or last clean snapshot, counts and a precise stop reason:
fuel exhausted, node limit, match limit, explicit client stop, goal found or a proved no-change
round. Arbitrary strategies can starve a rule. Therefore call the last case `Saturated` only when
complete matching of every declared active rule/condition/action and complete rebuilding establish
the specified fixed point. A scheduler that temporarily bans rules cannot infer saturation from
one empty batch without a separate coverage theorem.

The default bounded engine promises termination and preservation at every return. Optional
fairness/finite-closure hypotheses support stronger theorems. No API should claim complete
equational reasoning, full search termination, or discovery of the globally best equivalent
program for arbitrary client rules. Guidance, budgets and scheduling may change which sound
equalities are discovered and therefore the quality of extraction.

## Extraction, cycles and the exact cost guarantee

There are three distinct results to specify:

1. The returned finite term is represented in the requested class and has the stated sort.
   The equality invariant then gives semantic preservation. No optimality premise is required.
2. The selected term costs no more than the input under the client's declared comparison, checked
   or proved using a retained original representative. This is an improvement guarantee only.
3. The selected term minimizes a specified cost among **finite terms represented in the current
   e-graph**. This is independent of whether saturation discovered every derivable equality.

For the first delivery choose nonnegative additive natural-number tree cost, preserving the
simple ANA-6 model while permitting operator/sort/parameter-dependent weights. AST depth is a
separate useful compositional model. Use mathematical natural costs; any extracted bounded
machine-integer optimization needs an overflow-preservation argument or a documented saturation
semantics. An unlawful comparison or NaN cost cannot be accepted as an ordering law. The official
egg cost API itself requires a monotone cost discipline and warns about overflow and NaN.
[Cost API][egg-cost], [pinned implementation][egg-extract-src]

Acyclic class graphs admit straightforward bottom-up dynamic programming. For finite cyclic
expression e-graphs, a credible direct exactness proof for additive nonnegative tree costs is:

- Define finite representation derivations with a height bound; compute the cheapest witness
  of height at most `h` by dynamic programming, retaining the previous round's candidates.
- Induct on `h` for bounded-height completeness and cost optimality.
- Show cycle elimination: if a class repeats along a witness path, replace the outer occurrence
  by the inner occurrence of the same class. The result remains represented. Nonnegative node
  costs and monotone parent aggregation ensure cost cannot increase; term size strictly falls.
- Repeated elimination yields an equal-or-cheaper witness with no repeated class on a path,
  hence height at most the number of canonical classes, with the leaf-height convention fixed.
  This gives a finite iteration bound for exact minimum tree cost when a finite witness exists.
- Break equal-cost ties by smaller size and a deterministic structural order. Never construct
  a cyclic output pointer from zero-cost ties. A class without a finite derivation returns `None`.

This is a proposed Gaulois proof roadmap, not a theorem imported from the acyclic AFP result.
Zero-cost nodes are allowed because eliminating a repeated class need not strictly lower cost;
the size tie-break and finite-height witnesses handle them. For a more general model, state and
prove the analogous monotonicity and cycle-elimination/extensiveness laws before promising this
exactness. Negative or nonextensive cyclic costs can lack a finite minimum. A bounded extractor
still returns a sound represented candidate but cannot claim optimality when its bound is too low.

Store witness choices in an acyclic height-indexed DAG during computation; materializing the
tree may be exponential in compact representation size. Charge output size. A shared `RecExpr`
representation does not change a tree-cost objective into a DAG-cost objective automatically.

Code size with common subexpressions counted once, register pressure, cross-root sharing,
dominance-constrained placement and target scheduling are global/shared extraction objectives.
Expose a different extraction backend and specification. ILP, bounded search or low-treewidth
algorithms can be consumer options; certify representation and objective facts for external
solutions. A feasible candidate alone does not prove optimum: a checked lower bound or complete
search proof is also needed. The low-treewidth paper offers a conditional exact algorithm, not
a reason to impose that machinery on every client. [Sparse extraction paper][sparse-extract]

## Explanations and the trust boundary

Direct verification and proof production are complementary:

- A directly proved engine preserves a relational soundness invariant through every operation.
  Its consumer applies the preservation theorem; it need not generate or replay a concrete
  explanation for each internal merge. Erased `Prop` evidence is not a runtime log requirement.
- An external egg/egglog producer, cached result or heuristic applier needs a certificate checked
  by the small kernel. The checker validates rule identity, substitution, typing, conditions,
  congruence, symmetry/transitivity and chronological references. Unknown rule names, unchecked
  external facts and arbitrary asserted unions must fail.
- A shared proof DAG avoids repeating subproofs. Its references must be acyclic or strictly
  chronological; bound parsing and validation work. Flattening to ANA-6 positional term steps
  can cause large proof and term expansion, so prove a compatibility translation when feasible
  and keep a compact certificate interface separate. Proof minimization affects size, not trust.

ANA-6's replay already constitutes a small sound boundary for its supported first-order term
certificates. Extend or embed it; do not discard that work or pretend its acceptance theorem is a
direct proof of saturation. External equality proofs establish the accepted equality only, not
the external searcher's completeness, scheduler fairness, cost model accuracy or extraction
optimality. A caller still needs the language adapter's program-replacement theorem.

The compatibility theorem should be concrete: embed existing `term K` using one permissive sort,
operator type `K`, free-variable keys `nat` and the original strict partial evaluator. Interpret
the existing rule terms as patterns through a separate hole translation. Prove preservation of
substitution, positional contexts, denotation, guard success and rule soundness. Instantiate the
new tree cost with the existing operator weights and zero free-variable cost, so it agrees with
ANA-6's sum-over-operators objective. Legacy arbitrary term-substitution guards remain supported
through a term-witness adapter or the old replay validator; do not assume they are invariant on
e-classes. This is a semantic facade over the shared engine/kernel, not a second producer.

The logical core is Rocq's kernel plus the project's ordinary toolchain/extraction assumptions;
all new core claims must be closed under the global context. Do not import proof irrelevance,
functional extensionality, classical choice or axioms merely to identify dictionaries, maps or
semantic environments. Use pointwise equivalence and the provided canonical representations.
External formalizations are proof-design references, never source to copy or assumptions to add.

## Concrete extension example

Consider a toy pure word language with sorts `Word w` and `Bool`; free variables have known
sorts and successful values under an admissible environment. The encoded operator family contains
`Lit w n`, `Add w`, `Mul w`, `UDiv w` and `Shl w`. Each constructor records width and interprets
through total Bits word operations. Typed recursive terms therefore evaluate successfully.
An SSA adapter additionally proves that substituted free values are available at the replacement
point. This example deliberately avoids assuming totality for an arbitrary partial client.

A client registers these ordinary rule values and uniform proofs:

- `add_zero w`: `Add w ?x (Lit w 0) = ?x`, with a checked width match.
- `mul_one w`: `Mul w ?x (Lit w 1) = ?x`, using the same typed substitution interface.
- `div_self w`: `UDiv w ?x ?x = Lit w 1`, guarded by a validated nonzero fact for `?x`.
  The proof uses the word division theorem under a nonzero divisor and fixed width. Repeated
  holes ensure both operands have the same class, and semantic equality transfers the premise.

For `div_self`, add an analysis that records a conservative successful-value range plus a
definedness fact. Initially unknown ranges contain every word of the sort. Literal transfer
produces a singleton; arithmetic transfers use proved Domains/Bits operations. Combine range
facts only under the chosen validity law. A simple independently proved sign/nonzero analysis
can also suffice. The guard succeeds when zero is excluded and definedness is known. A fact
derived only from an environment context carries that context into the result theorem.

For example, suppose the environment proves `x` is a defined 32-bit nonzero value. Rewriting
`Add 32 (UDiv 32 x x) (Lit 32 0)` yields `Lit 32 1`. With add weight 1, divide weight 8, literal
weight 1 and variable weight 1, additive tree cost decreases. Without the nonzero premise, the
division rewrite is unavailable; with a possibly trapping nested operand, its totality premise
must also be supplied. A failed guard changes precision/search, not the equality invariant.

Now add `RotateLeft w`, a new encoding constructor and its client interpretation. Extend the
signature table and register `rotate_zero w` with the appropriate word law. Extend the same
analysis with a sound conservative transfer and set the operator's target cost. No core edit is
required. A custom depth/latency cost can use `weight(op) + max(child costs)` when its lawful
comparison, monotonicity and cycle conditions are proved. A cost estimate is an objective chosen
by the client, not a theorem about hardware time.

The actual extension touchpoints are deliberately small:

| Extension | Client additions | Core modifications |
| --- | --- | --- |
| New operator | Constructor/encoding, typing case, interpretation case/laws | None |
| New equation | Rule data, optional guard, one uniform soundness theorem | None |
| New analysis | Fact type/validity, transfer/combine laws, proved action hook | None |
| New cost | Leaf/node aggregation and ordering/cycle laws for its claims | None |
| New theory bundle | Signature embedding, rules and proofs, adapter laws | None |

An analysis extension can conservatively return unknown for a new operator until a better
transfer is proved. A cost extension can assign a conservative user-chosen default weight.
Neither requires implementing special semantic reasoning in the generic congruence engine.

Finally, a trapping unsigned-division client can reuse the pattern syntax but must prove its own
`div_self` result equality from nonzero and definedness. Its one-way Bits bridge is insufficient
alone. Adding floats, loads or binders requires the corresponding semantic adapter and rule proofs;
registration cannot turn an unproved algebraic guess into a theorem.

## Proposed cards, dependency sequence and realistic scope

Do not replace ANA-6 by one large seven-hour card. The current card's checker claims are much
smaller than a reusable directly proved EqSat framework. The existing plan's combined
`A-PRE, A-EGRAPH` range of 24–45 hours should not be presented as a credible total estimate for
the full proposal below. These ranges are rough engineer-hours for design, proofs, targeted
examples and review preparation, not promises; difficult representation invariants can exceed
them and require a split rather than an axiom.

| Proposed card | Hours | Main dependencies and exit evidence |
| --- | ---: | --- |
| A-EG-LANG | 16–30 | Encodings; sorted syntax, schemas, substitution and context lemmas |
| A-EG-CORE | 32–64 | COL-2, LANG; justified union, interning, indexes, rebuild preservation |
| A-EG-MATCH | 20–40 | CORE; indexed matcher and shared instantiation correctness |
| A-EG-ANALYSIS | 20–40 | CORE, Order; valid facts, propagation and justified hook actions |
| A-EG-RUN | 12–24 | MATCH, ANALYSIS; bounded strategy, stop reasons, preservation |
| A-EG-EXTRACT | 20–40 | CORE; finite witnesses, improvement, conditional tree optimality |
| A-EG-CLIENT | 16–30 | All core cards, Bits/Views; toy rules and ANA-6 compatibility |
| A-EG-REL, optional | 30–60 | MATCH, R-RULE/R-DELTA; exact quotient-aware joins |
| A-EG-CONTEXT, optional | 30–60 | CLIENT, VIEW-5; context-labelled equalities and guarded export |

The core track totals approximately 136–268 hours before optional relational/context/binding or
global extraction extensions. Its generic equality/sorted term layer does not need strict SSA,
dominators or ANA-5; only the SSA client adapter needs those prerequisites.

For owner review, select a standalone **`Gaulois.Rewrite`** theory under `theories/Rewrite/`,
depending only on Stdlib and Collections. Its abstract fact/analysis records need no imported
lattice implementation; the client supplies validity and combination laws. An adapter over
Gaulois Order/Domains proves those laws from the chosen domain, outside the core. This keeps
Bits, Float, SSA, Views and all of Analyses out of the reusable package's dependencies.

Suggested file ownership, all still proposals, is:

- LANG owns `RewriteSyntax.v`, `RewriteRules.v` and `RewriteEquality.v` in the new theory,
  including the small equality kernel and its semantic theorem.
- CORE owns `RewriteEgraph.v`, `RewriteIndex.v` and `RewriteRebuild.v`; MATCH owns
  `RewriteMatch.v`; ANALYSIS owns `RewriteAnalysis.v`; RUN owns `RewriteRun.v`;
  EXTRACT owns `RewriteExtract.v`.
- CLIENT owns only the explicitly listed compatibility declarations in the existing
  `AnalysesEgraph.v`, an optional `AnalysesSsaRewrite.v` pure-region adapter and an
  `AnalysesRewriteDomains.v` numeric-analysis adapter. The latter two may import Rewrite,
  Bits/Domains and Views as appropriate; Rewrite imports none of them. Preserve the current
  generic ANA-6 interface as a facade, rather than describing it as intrinsically SSA-only.
- Tests follow the existing `tests/Rewrite/Rewrite*Test.v` computational Example convention;
  the word/SSA extension examples remain in the assigned example modules. LANG also owns the
  new theory/build declarations, and CLIENT owns extraction-client wiring after approval.
  Their implementers must load the relevant Rocq/OCaml skills and check the actual Dune
  dependency graph before editing.

Every basename starts with its package as required. This is one direct engine plus compatibility
and semantic adapters, not two competing saturation implementations. Preserve the external
certificate/replay route because its trust boundary serves a different consumer. Creating a
package, moving declarations or changing dependencies needs an owner ruling and documentation
checkpoint; no such production edit is made here.

Suggested delivery phases are:

1. Approve scope and public semantic claims. Preserve current ANA-6 and its accepted example.
   Prove sorted syntax, substitution, contexts and the small equality calculus. Demonstrate a
   client adding a new operator and guarded rule without editing the kernel.
2. Build directly verified interning, justified union and batched rebuilding with clean/dirty
   invariants. Implement the useful indexed matcher and bounded runner; retain only sound facts
   at guard reads. Initially allow no-op analysis, then add the proved analysis interface.
3. Prove extraction membership and improvement first; prove exact additive tree extraction over
   the declared finite graph model separately. Connect the typed word toy and pure SSA region,
   and establish compatibility with ANA-6's observable result guarantee.
4. Add relational multipatterns when a consumer needs them, reusing verified query infrastructure.
   Add contextual/colored reasoning, binders, cyclic SSA analysis or shared extraction only on
   concrete client demand and with their distinct public theorem statements.

The owner/card rewrite should add explicit public claims for sorted substitution, representation,
equality preservation, index agreement, rebuild completion under fixed-graph hypotheses, match
soundness/completeness scope, fact validity, bounded termination, output membership and objective
scope. Preserve every still-required ANA-6 name/theorem through an adapter or an approved contract
revision. Record the C7 direct-internal-path ruling explicitly; neither this report nor C14 is
that ruling. No old binding name is silently assigned a stronger or different meaning.

Use the existing test conventions: computational Examples for typed rule application, repeated
holes, false guards, malformed substitutions, operator flags/widths, sort-mismatched unions,
congruence after child unions, stale parents, analysis changes, zero-cost cycles, a class without
a finite witness, exhausted budgets and the toy client extension. Check partial/trapping and
floating-point counterexamples in the adapters that claim those semantics. These are meaningful
regressions complementing proofs; do not add a duplicate implementation or custom benchmark
project. Targeted optional measurement through the existing harness is useful only for a named
unresolved consumer choice and must include preparation, output, encoding and allocation costs.

Risks are the clean/dirty index proof, analysis validity while equality changes, finite-witness
extraction with zero-cost cycles, certificate expansion, client context leakage and overly broad
program-equivalence claims. Reduce scope by delivering one proved extension path and conditional
guarantees, not by leaving proof holes or claiming bounded search complete. Consumer-selectable
conventional/relational matching, schedules and extraction objectives remain explicit where neither
approach dominates; same-result backends share a spec, while budget/precision choices expose
their differences.

## Crosswalk for the main research plan

These are subcapabilities of ANA-EGRAPH and proposed extensions, not additional already contracted
analyses or changes to the stable 106-item inventory:

- EGR-LANG: arbitrary encoded operators, sorted/variadic application and safe schemas.
- EGR-RULE: patterns, repeated holes, typed substitution, guard evidence and per-rule soundness.
- EGR-CONG: interning, equality kernel, canonicalization, parent indexes and batched rebuild.
- EGR-MATCH: conventional and optional relational/multipattern matching with declared coverage.
- EGR-ANALYSIS: semantic fact laws, context transport, convergence and safe dynamic actions.
- EGR-RUN: composable scheduling, binary work fuel, budgets and honest fixed-point status.
- EGR-EXTRACT: finite membership, improvement and distinct tree/shared optimality claims.
- EGR-PROOF: direct internal preservation, compact optional explanations and external checking.
- EGR-CLIENT: reusable language/theory registration and behavior-preserving client adapters.
- EGR-REL/CONTEXT/BIND: optional equality-aware relations, contextual classes and binders.

Current ANA-6 directly contracts EGR-PROOF's positional-checker route and the conditional
improvement wrapper, with generic term/rule data supporting parts of EGR-LANG/RULE. The remaining
direct core and ergonomic interfaces are proposals. Keep the distinction visible in PLAN and
coverage; a report heading saying “e-graphs” alone hides most of the required design work.

## Primary references and inspected artifacts

[egg]: https://arxiv.org/abs/2004.03082
[rem]: https://effect.systems/doc/popl-2022-gj/paper.pdf
[rem-record]: https://doi.org/10.1145/3498696
[small-proofs]: https://arxiv.org/abs/2209.03398
[egglog-paper]: https://effect.systems/doc/pldi-2023-egglog/paper.pdf
[colored]: https://arxiv.org/abs/2305.19203
[guided]: https://steuwer.info/files/publications/2024/POPL-2024-2.pdf
[sparse-extract]: https://cse.hkust.edu.hk/~parreaux/publication/oopsla24a/
[foundations]: https://doi.org/10.4230/LIPIcs.ICDT.2025.11
[contextual]: https://arxiv.org/abs/2507.11897
[egglog-changelog]: https://github.com/egraphs-good/egglog/blob/main/CHANGELOG.md
[egglog-api]: https://egraphs-good.github.io/egglog/docs/egglog/
[foresight]: https://jonathanvdc.github.io/files/2026-cc-foresight.pdf
[foresight-artifact]: https://zenodo.org/records/17955956
[optimism]: https://arxiv.org/abs/2511.20782
[afp]: https://isa-afp.org/entries/Equality_Saturation_Checker.html
[verified-rocq]: https://adam.chlipala.net/papers/EgraphsPOPL27/
[egg-multi]: https://docs.rs/egg/0.11.0/egg/struct.MultiPattern.html
[egg-cond]: https://docs.rs/egg/0.11.0/egg/trait.Condition.html
[egg-analysis]: https://docs.rs/egg/0.11.0/egg/trait.Analysis.html
[egg-runner]: https://docs.rs/egg/0.11.0/egg/struct.Runner.html
[egg-cost]: https://docs.rs/egg/0.11.0/egg/trait.CostFunction.html
[egg-extract-src]: https://github.com/egraphs-good/egg/blob/v0.11.0/src/extract.rs
[egglog-schedule]: https://egraphs-good.github.io/egglog-tutorial/04-scheduling.html

Skill completion: no authored code was edited and no gated-code skill was applied. This report
is research prose only. No production changes, commits, builds or proof-completion claims were made.
