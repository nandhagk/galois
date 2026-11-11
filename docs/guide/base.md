# Base

Base provides key encodings, canonical containers, reflected equality, labelled paths and
certification. Its computational dictionaries contain data and functions. Separate `Prop`
records state injectivity, decoder round trips and numeric cost assumptions. A client can
compute keys without supplying any of these proofs.

## Encodings and codecs

An [`encoding K`](../../theories/Base/BaseEncoding.v#L12) supplies
`encode_c : K -> Cost.t positive`. The pure accessor `encode E x` returns its `Cost.value`.
`key_bits E x` counts every binary digit, including the leading digit. The record
`encoding_laws E` supplies `encode_injective`. It says that equal codes imply equal keys.

A [`codec K`](../../theories/Base/BaseEncoding.v#L52) adds
`decode : positive -> option K`. Its separate `codec_laws` record supplies `decode_encode`.
The theorem `codec_laws_injective` derives the encoding law from that round trip.
A decoder may accept additional codes. The law requires it to recover every encoded value.

The scalar codecs are `positive_codec`, `N_codec`, `nat_codec`, `Z_codec`, `bool_codec` and
`unit_codec`. Each has a `_laws` theorem and an encoding alias such as `nat_encoding`.
Each alias has separate `_laws` and `_cost_laws` theorems.
Positive numbers encode as themselves, naturals as their
positive successor, and signed numbers use low-bit sign tags. Booleans use one for false and
two for true. Unit uses one. Boolean and unit decoders reject other codes.

`of_pure f` lifts a pure word-RAM primitive at one tick per call. Use it when that primitive
cost convention is appropriate. Use a costed encoding directly for a traversal or callback
whose work depends on its input.

## Derive a client codec

The universal [`code`](../../theories/Base/BaseCode.v#L15) has `Atom positive` and
`Node (list code)` constructors. A client supplies a costed conversion
`to_code : T -> Cost.t code`, a partial conversion `of_code : code -> option T`, and a proof
`rt : forall x, of_code (Cost.value (to_code x)) = Some x`.
Then `derive to_code of_code rt` constructs a codec, and `derive_laws` proves its round trip.
The costed callback prevents the client conversion from hiding recursive work.

The [binary-tree client](../../tests/Base/BaseCodeTest.v#L15) is a complete checked example.
Leaves become atoms and branches become nodes holding two child codes.
Its conversion charges each recursion step.
The client proves its round trip with `solve_roundtrip` and passes that proof to `derive`.
Its tests include a recursive tree and a rejected node of the wrong arity.

The built-in `pair_codec`, `list_codec`, `option_codec` and `sum_codec` compute without
component laws. Their `_laws` theorems take the component codec laws.
Pairs and lists use nodes of component atoms. Options use an empty node for absence and a
single atom for presence. Sums use a single atom on the left and an extra nested node on the
right. Arbitrary component tick counts flow through these compositions.

## Serialization and costs

The serializer uses delimited positive symbols and a tree grammar.
An atom begins with false and then emits its positive code. A node begins with true and then
emits its child list. A child list uses false for nil and true followed by a tree and the
rest of the list for cons. Positive symbols use false,false for a zero digit, true,true for a
one digit, and false,true for the final leading one. Bits run from least significant to most
significant. A final one converts the whole stream into a positive number.

`code_decode` parses with fuel equal to the stream length and rejects unused suffix bits.
`read_emit_tree` proves that the emitted structural weight supplies enough fuel.
`code_decode_encode` proves the decoder round trip constructively.
`code_encode_bits` gives the exact bit count as `1 + N.of_nat (code_weight c)`.
The weight counts tree tags, child-list tags and twice the atom digit counts.

Every emission and stream-construction recursion step charges a tick.
The serializer also runs `Cost.tick_bits` on its result.
The named constant [`encode_k`](../../theories/Base/BaseEncoding.v#L83) is `8`.
<!-- Source for constants and formulas: BaseEncoding.v and BaseCode.v cost theorems. -->
`code_encode_cost` bounds serialization by `encode_k` times the result bit count.
The constant is an overhead bound. It does not bound arbitrary component calls.

The separate record `encoding_cost_laws E k` states
`forall x, Cost.ticks (encode_c E x) <= k * key_bits E x`.
The generic composite `_cost` theorems expose component calls and serialization separately.
The `_encode_cost_le` theorems substitute explicit component numeric laws.
For component constants `ka`, `kb` and `k`, the resulting multipliers are as follows.

| Codec | Numeric multiplier on its result bits |
| --- | --- |
| Pair | `ka + kb + encode_k + 3` |
| List | `k + encode_k + 2` |
| Option | `k + encode_k + 2` |
| Sum | `ka + kb + encode_k + 2` |

The bit-size theorems justify these substitutions.
Pair output bits equal `7 + 2 * a + 2 * b` for component bit counts `a` and `b`.
List output bits equal `3 + 2 * length + 2 * total_component_bits`.
The option and sum size theorems give the corresponding branch-specific formulas.
`derive_encode_cost_le` additionally requires a bound on the client conversion.
`encoding_comap` likewise takes a costed conversion and exposes its cost independently.
Its injectivity theorem takes the conversion's injectivity as a separate premise.

## Equality and tactics

[`eqb`](../../theories/Base/BaseEq.v#L50) compares encoded keys.
`eqb_spec`, `eqb_true_iff` and `eqb_false_iff` connect its boolean result to equality under
`encoding_laws E`. Reflexivity and symmetry hold even for an unlawful dictionary.
`eqb_dec` supplies constructive decidable equality.
`eqb_c` charges both encoding callbacks and a synchronized traversal of the shorter code.
The digit traversal computes equality itself, so it does not hide a separate minimum or
comparison traversal.

Import `BaseKeyTactics` to use `case_key` and `solve_roundtrip`.
`case_key` finds `HE : encoding_laws E` and splits an `eqb E a b` or
`Pos.eqb (encode E a) (encode E b)` test in the goal or context.
Each branch keeps `a = b` or `a <> b` and rewrites matching tests.
It leaves substitutions to the caller.
`solve_roundtrip` inducts on the round-trip input, reduces constructor matches, and rewrites
induction hypotheses and component codec laws. Unsupported residue stays visible.
The [tactic clients](../../tests/Base/BaseKeyTacticsTest.v#L16) show both raw and wrapped tests.

## Paths and certification

[`Rel.lpath`](../../theories/Base/BaseRel.v#L13) records a path's labels in order.
Its lemmas support concatenation, induction from the final step, relation inclusion,
state and label mapping, and step-closed invariants.
`Rel.star` allows an empty traversal and `Rel.plus` requires at least one step.
`star_iff_lpath` connects closure to paths carrying unit labels.

[`certify`](../../theories/Base/BaseCertify.v#L12) takes a predicate, a boolean checker,
its soundness proof and a candidate. It returns a proof-carrying candidate when the checker
accepts and `None` when the checker rejects.
`certify_some_iff` characterizes successful certification.
`certify_or` returns a supplied certified fallback on rejection.
`certify_or_sound` proves that the returned candidate satisfies the predicate.
The checker needs soundness. Completeness is a separate client obligation when required.

## Writing against the interface

Use public operations, equations and specification theorems in proofs.
Keep `wf` hypotheses and `encoding_laws E` available when a theorem requires them.
`Map.ext` and `FinSet.ext` turn observational agreement into equality of well-formed values.
The computational values contain no law proofs.

Do not unfold container representations, list scans, heap selection or cost-monad definitions.
Use `Cost.value_bind`, `Cost.value_map` and the public callback-projection equations when
reasoning about a costed client. Replaceable operations carry `Arguments ... : simpl never`.
Fixtures may use `vm_compute` to observe their executable results.

The reference containers charge their list traversals and encoding callbacks.
They do not satisfy the future trie or binomial-heap bounds.
`Map.cost_laws` states separate assumptions on code lookup, insertion and removal.
Each assumption bounds ticks by `N.pos (Pos.size p)` for every code and computational map.
The reference implementation does not supply `Map.cost_laws_hold`.
Consumers that need numeric trie bounds must take the law record as a premise.

Value, order and functional-spec fixtures stay unchanged when a fast backend replaces a reference.
Exact tick fixtures record the current backend's cost observations.
The owner coordinates cost-only expectation updates alongside each replacement and its proved bounds.
These reference counts are not a frozen resource interface.

Costed callback forms retain the callback's full charge and add a call-overhead tick.
Pure wrappers lift their callbacks as one-tick primitives.
For example, use `Index.group_by_c` with a costed key conversion when computing a key requires
a traversal. Use `Memo.get_or_c` when the reference computation has a nonconstant cost.
Neither wrapper proves that an arbitrary client callback takes constant time.

## Maps

[`Map.t`](../../theories/Base/BaseMap.v#L84) stores code, key and value in a sorted list.
`Map.wf E m` requires every stored code to equal its key's encoding and the codes to be
strictly ascending under `Map.code_compare`.
The order is the canonical trie's traversal order.
Zero branches precede their root, and one branches follow it.
Thus codes two, one and three enumerate in that order.
<!-- Source: BaseMapTest.v, map_trie_order. -->

`empty`, `get_code`, `get`, `mem` and `find_or` provide construction and lookup.
`get_c` calls `encode_c` once before `get_code_c`.
`set`, `remove` and `update` change a single encoded position.
An update callback receives the previous `option V`.
It returns `None` to delete or `Some v` to store a value.
`get_set`, `get_remove` and `get_update` expose these observations through reflected key tests.
The `_same` and `_other` theorems specialize equality and disequality.

`map` changes values while retaining keys.
`combine f m n` computes optional values pointwise when `f None None = None`.
Its result takes an existing key from one of the input maps.
`union_with` retains one-sided values and combines shared values.
`inter_with` retains shared values, and `diff` retains left-only values.
Dedicated intersection and difference names let the trie implementation skip one-sided subtrees.
The reference combination uses repeated sorted insertion and removal and may be quadratic.
Its costed implementation retains all of those scans.

`elements_spec` relates enumeration to successful lookup, and `elements_sorted` fixes its order.
`fold_elements` states that `fold` is a left fold over that enumeration.
`size_elements` relates the count to enumeration length.
`of_list_get` gives last-occurrence replacement for construction in input order.
`forall2_spec` specifies a short-circuit relation on every left binding and its optional right value.
`beq` tests value agreement in both directions and ignores stored keys.
`Map.ext` proves canonical equality under `wf` and encoding injectivity.

The [map fixtures](../../tests/Base/BaseMapTest.v#L12) cover replacement, absence,
an absent-key update, deletion of the last binding, empty enumeration and list lookup ticks.

## Finite sets

[`FinSet.t`](../../theories/Base/BaseSet.v#L15) is `Map.t K unit`.
Its `wf` predicate is the underlying map invariant.
Every published set operation has a `_c` form and a pure `Cost.value` wrapper.
`add`, `remove`, `union`, `inter` and `diff` implement the corresponding membership formulas.
In particular, `inter_c` delegates to `Map.inter_with_c` and `diff_c` to `Map.diff_c`.

`subset_spec` specifies pointwise membership implication.
`equal_spec` identifies equal well-formed sets, and `ext` turns equal memberships into equality.
`elements_spec` connects enumeration to membership, and `elements_sorted` retains map code order.
`of_list` removes duplicate input keys.
`mem_of_list` tests the input with encoded equality.
The [set fixtures](../../tests/Base/BaseSetTest.v#L12) exercise duplicates, shared keys,
left-only keys, absence, empty equality and membership ticks.

## Group-by indexes

[`Index.t`](../../theories/Base/BaseIndex.v#L15) maps keys to lists.
`find` returns a stored bucket or `[]` for an absent key.
`group_by_c E key_c xs` charges every input visit and the costed key callback.
It uses `Map.update_c` to cons each item onto its bucket.
It then reverses every bucket once through `Map.map_c`.
Bucket construction therefore avoids repeatedly appending to a growing list.

`find_group_by` proves that a bucket equals the matching input filter in input order.
`wf_group_by` proves the underlying map invariant.
`group_by_c_value` lets a client apply these laws to any costed key callback's returned values.
The [index fixtures](../../tests/Base/BaseIndexTest.v#L12) include interleaved buckets,
an absent bucket, empty input and the charge of a singleton group.

## Priority queues

[`Heap.t`](../../theories/Base/BaseHeap.v#L15) uses the live priority map as its reference state.
`priority` returns an optional positive priority.
`push` inserts an absent key or strictly decreases an existing priority.
A larger or equal supplied priority leaves the queue unchanged.
`size` counts live keys.
`wf` is the live map invariant.

`pop E q` returns `None` on an empty queue.
A successful result is `Some (p, k, q')`.
`pop_priority` proves that `k` had live priority `p`.
`pop_min` proves that every other live `(r, a)` satisfies
`p < r \/ (p = r /\ encode E k <= encode E a)`.
The tie order uses numeric positive codes.
It differs from the trie's enumeration order.
`pop_removes` specifies the selected key's absence and every other key's unchanged priority.
`size_pop` proves that a successful pop removes one live key.
`wf_push` and `wf_pop` maintain the invariant.

The reference pop charges map enumeration, a scan for the minimum and map removal.
Tied comparisons retain both encoding callback costs and charge both code traversals.
It makes no logarithmic or amortized cost claim.
The [heap fixtures](../../tests/Base/BaseHeapTest.v#L12) distinguish numeric tie order from
enumeration order and check decreases, ignored increases, empty pop and insertion ticks.

## Union-find forests

[`UnionFind.t`](../../theories/Base/BaseUnionFind.v#L16) stores parent and rank maps and a
global maximum rank.
`wf E uf` requires both maps to satisfy `Map.wf E`.
It also bounds every key's rank by `max_rank uf` and requires every parent link to increase rank
strictly.
Missing rank entries have rank zero.
`find E x uf` returns a representative and the compressed forest.
Its budget is `S (max_rank uf)`, which suffices under `wf`.
<!-- Source: BaseUnionFind.v, rank_of_equation, wf and find_equation. -->

`find_correct` connects find to parent paths and proves that compression keeps those paths'
root observations.
`find_root` proves that the returned representative has no parent in either forest.
`find_equiv` proves representative membership and preservation of every equivalence class.
`union E x y uf` compresses both argument paths and links their roots by rank.
`union_equiv` specifies exactly the old classes and the two directions of the newly joined class.
`wf_find` and `wf_union` require explicit encoding injectivity and maintain the forest invariant.
`equivb` returns a boolean and the resulting compressed forest.

Unknown keys are singleton classes.
Finding an unknown key returns that key and the unchanged forest.
Self-union registers a singleton.
`keys` enumerates registered support in canonical map order.
`keys_spec`, `keys_union` and `find_support` describe registration and support preservation.
`of_unions` consumes pairs in input order, and `of_unions_equiv` identifies its classes with
the reflexive symmetric transitive closure of those input pairs.

The lower-level `find_fuel` returns its current key on exhaustion and compresses the traversed
prefix to that key.
An insufficient budget can therefore return a non-root.
Use public `find` with `wf` for the root guarantee.
The [forest fixtures](../../tests/Base/BaseUnionFindTest.v#L17) cover unknown keys,
self-union, both rank directions, path compression, support order, exhaustion and exact reference costs.
Reference accounting helpers are private.
Public `find_cost` and `union_cost` are reserved for the later ranked implementation's bounds.

## Interning

[`Intern.t`](../../theories/Base/BaseIntern.v#L15) stores a forward `Map K positive`,
an inverse `Map positive K` and the next unused positive ID.
The inverse map uses the encoding of `positive_codec`, exposed as `positive_encoding`.
`empty` starts allocating at one.
`intern` returns an ID and the resulting table.
`intern_found` returns an existing ID without changing the table.
`intern_new` allocates the old frontier and advances it by one.
<!-- Source: BaseIntern.v, empty_c and intern_new. -->

`wf E s` requires both maps to be well formed.
It also requires forward and inverse lookup to agree, each allocated ID to be below `next s`,
and every positive ID below `next s` to belong to some key.
`intern_wf` maintains these conditions.
`find_intern`, `key_of_intern` and `key_of_find` connect forward lookup and reverse lookup.
`find_intern_old` retains old allocations, and `ids_dense` characterizes the allocated interval.
The reference `size_c` counts the forward map through `Map.size_c`.

`of_list` allocates in first-occurrence order.
`intern_list_spec` states that the resulting table contains exactly the input keys.
The [interning fixtures](../../tests/Base/BaseInternTest.v#L12) check repeated keys,
consecutive allocation, inverse lookup, absence, an empty inverse map and allocation ticks.

## Interval sets

[`IntervalSet.t`](../../theories/Base/BaseIntervalSet.v#L19) is a list of half-open integer ranges.
A pair `(lo, hi)` contains exactly the integers `lo <= b < hi`.
Its separate `wf` predicate requires every range to be nonempty and every earlier range's upper
endpoint to be strictly below every later range's lower endpoint.
Adjacent ranges must coalesce.
Separated ranges have at least one absent integer.
Equal or reversed singleton endpoints denote the empty set.

`mem set b` tests an integer.
`add range set` and `remove range set` insert or subtract a range.
`union left right`, `inter left right` and `diff left right` have pointwise boolean membership laws
under the two input invariants.
Their `wf_*` laws maintain canonical ranges.
`ext` constructively identifies canonical lists with the same integer membership.
`elements` returns ranges in canonical order without enumerating each integer.

`subset left right` decides integer-set inclusion.
`covers set range` tests universal membership over the queried half-open range.
`intersects set range` tests whether at least one queried integer is present.
Every empty query range is covered and has no intersection, including reversed endpoints.
The query specifications require the set's `wf`.

All operations have `_c` forms.
Membership charges each examined range until its first match.
Union merges the sorted streams and coalesces adjacent or overlapping ranges.
Difference retains charged work through its cut continuation.
Intersection composes two differences.
Numeric cost bounds are deferred to `BASE-INTERN`.
The [interval fixtures](../../tests/Base/BaseIntervalSetTest.v#L1) include negative endpoints,
adjacent union, gap coverage, split subtraction, reversed ranges and endpoint-only intersections.

## Memo tables

[`Memo.t`](../../theories/Base/BaseMemo.v#L15) is an ordinary map.
`valid E f m` says that every stored lookup result equals the reference result at its key.
It is separate from `Map.wf E m`.
Both predicates are premises of `get_or_agrees`.
The agreement theorem proves the returned result equals `f k` and the returned cache stays valid.
`wf_get_or` separately proves representation-invariant preservation.

`get_or_c E f_c k m` returns a cached result without calling `f_c` on a hit.
A miss charges the callback and stores its result.
`get_or_c_value` connects that costed callback to the pure agreement theorem.
`map_memo_c` threads one cache through an input list.
`map_memo_agrees` proves equality with `List.map f` and validity and well-formedness of the final cache.
`map_memo_c_value` retains that semantic interface for arbitrary callback charges.
The [memo fixtures](../../tests/Base/BaseMemoTest.v#L12) cover a miss, a hit, an unrelated absent key,
empty and repeated-key lists, and retention of an explicitly expensive callback's charge.

## Container and option tactics

Import `BaseTactics` for `simpl_map`, `simpl_set`, `set_solver` and `inv_option`.
It reexports the `Map` and `FinSet` hints without importing their unqualified operation names.
The named `galois_map` database contains lookup and membership rewrite laws.
`simpl_map` rewrites observations and calls `case_key` when a matching encoding law is present.
`simpl_set` also reduces the boolean membership connectives.
`set_solver` reflects true-membership formulas to `In` propositions and runs bounded `firstorder`
with `auto 4` for its propositional residue.
`inv_option` repeatedly splits option-producing matches, inverts constructor equalities,
substitutes option variables and discharges impossible constructor branches.
It leaves an observation unchanged when its result payload contains the same observation.
This prevents a self-referential lookup equation from expanding its own result repeatedly.

The [tactic contracts](../../tests/Base/BaseTacticsTest.v#L10) have three symbolic goals each
for map rewriting, set rewriting and set solving, and six for option inversion.
An additional unsupported list goal checks that `set_solver` returns control with the residue.
The option tests retain noncyclic lookup rewriting and leave a self-referential lookup for
an explicit witness proof.
A computed constant-function model checks that the self-reference premise is inhabited.
<!-- Source: the named Example declarations in BaseTacticsTest.v. -->
