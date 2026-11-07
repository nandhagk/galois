# Value and state domains

`Galois.Domains` separates runnable dictionaries from semantic laws.
[`ValueAbs.t`](../../theories/Domains/DomainsValue.v#L15) describes abstract values for an
operator carrier `K` and a guard carrier `G`.
Its lattice has the weak laws of `Galois.Lattice`.
Forward, backward and guard callbacks run in `Cost.t`.
The accessors `ValueAbs.op`, `ValueAbs.back` and `ValueAbs.guard` observe their results.
`ValueSem.t` supplies a partial concrete evaluator and a predicate on guarded operand lists.

`value_laws D M gam` connects the two dictionaries.
Every defined concrete result belongs to the forward result.
Backward transfer retains every operand list producing a result in the supplied result fact.
Guard transfer retains every operand list satisfying the guard.
Both refinement operations keep operand count, including on inputs without concrete witnesses.
`value_refines` separately requires their results to be below their inputs.
The record does not carry a meet.
Clients supply a costed meet when they need intersection.

## Terms and assumptions

[`term K X`](../../theories/Domains/DomainsTerm.v#L16) has variable leaves and operator nodes.
`term_ind'` supplies a hypothesis for every child in a node's operand list.
`eval_term` propagates undefined children.
`abs_eval_c` charges syntax visits, operand-list visits and dictionary calls.
`abs_eval_sound` connects its pure accessor to successful concrete evaluation.

`abs_assume_c` takes costed variable equality, a costed meet and a costed environment.
It refines node operands from left to right.
Each recursive call receives all earlier updates.
The returned environment retains charged lookups, so deferred variable updates keep their costs.
`abs_assume_sound` requires equality soundness and a meaning-preserving meet.
`abs_assume_refines` requires weak lattice laws and that meet is below its left input.
The refinement theorem needs no precision property of the backward callback.

## Supplying a transfer table

[`Transfer.table`](../../theories/Domains/DomainsTransfer.v#L17) has two costed lookup fields.
Each lookup receives an operator and an operand count.
A present forward entry receives result context and the ordered operand list.
A present backward entry additionally receives a result fact.
The list-entry representation supports unary, binary, ternary and variadic operators through
one contract.

`Transfer.shape` supplies concrete evaluation, point detection, an empty test, singleton
injection, result bottom and top, and the default backward embedding.
`Transfer.forward` uses the following priority.

- An empty operand returns result bottom before point collection or table lookup.
- An all-point list evaluates concretely and injects the result.
- Failed concrete evaluation returns bottom because it has no defined result.
- Other lists use the entry for their operand count.
- A missing entry returns result top.

`Transfer.backward` uses its arity entry or maps the default embedding.
`transfer_sem` states the shape's semantic promises.
`table_laws` requires soundness of each supplied entry and unconditional backward length.
`forward_sound` and `backward_sound` prove the dispatch once.
`table_refines` states default and per-entry structural refinement.
`backward_refines` lifts those facts through the shared dispatch.

`word_of_table` supplies the payload dictionary from a table, shape, payload lattices, top,
constant and meet callbacks.
`word_of_table_laws` adds the independent lattice, constant and meet obligations.
Its context requires the result width to agree with the successful result.
Its output meaning uses each concrete word's own width.
Backward operands can therefore have widths different from the result, as comparisons and
resizing require.
[`point_word_domain`](../../theories/Domains/DomainsPoint.v#L93) is the reference client.
It uses an empty table and gets concrete singleton evaluation from the shared point path.

## Width tags and open client values

[`word_domain`](../../theories/Domains/DomainsNumeric.v#L67) describes integer payloads at explicit
widths.
`tagged P` adds `TBot`, `TVal w p` and `TAny`.
[`tagged_domain`](../../theories/Domains/DomainsTagged.v#L242) turns a lawful payload dictionary
into a numeric dictionary through `tagged_numeric_laws`.
The numeric interface retains the legacy field meanings.
Its charged callbacks have `_c` names and its result accessors retain the legacy names.
`num_eval` and `num_assume` operate on `Expr.t op`.
Their implementation charges translation into generic terms and uses the shared term traversal.

[`op_bridge`](../../theories/Domains/DomainsBitsValue.v#L15) supplies costed expression lookup and
partial word conversion.
`bits_values` interprets mapped operators with `num_eval_c`.
An unmapped operator returns the caller's global top.
`numeric_conc` interprets a converted value through the numeric meaning.
A nonword value belongs to a fact exactly when that fact is not below bottom.
`bits_values_laws` requires the numeric laws, bridge laws, a top covering every normalized
word and a top comparison that rejects bottom.

Guards have the following meanings and capability checks.

- `Truth b` tests a single concrete value's truth.
  Numeric refinement requires the `truth_words` capability and its conversion-totality law.
- `Equal d` tests concrete equality on one operand.
  A convertible `d` permits meeting the operand with its numeric constant.
- `Differ d` tests concrete disequality on one operand.
  Its costed per-constant capability requires total conversion, width agreement with `d` and
  injectivity against `d`.
  Those premises justify a successful numeric inequality test.
- `Test e b` tests a successful word-expression evaluation over explicitly convertible operands.
  Its semantic premises supply the conversions and successful evaluation.

Disabled capabilities and malformed unary guard arities keep operands unchanged.
Truth needs no injectivity or uniform-width premise.
For example, a mixed-width word language can enable truth and disable disequality.
Refinement first intersects the evaluated result with the requested result fact.
An empty intersection rejects every operand.
Otherwise the numeric assumption engine propagates the fact and reads back the original support.

## Composition and state contracts

[`ValueAbs.product`](../../theories/Domains/DomainsValue.v#L66) computes both components and
applies a costed reducer after forward, backward and guard transfer.
`product_laws` needs the reducer to retain the intersection of component meanings.
`ValueAbs.rename` takes costed operator and guard conversions.
It retains conversion charges and separate overhead for the conversion and delegated domain call.
`rename_laws` states evaluator and guard agreement through the conversion callbacks' values.

`ValueAbs.disjunctive k L compact D` takes an explicit weak lattice on lists and a costed
compaction policy.
Forward transfer enumerates the Cartesian product of operand alternatives.
Backward and guard transfer first join each operand's alternatives and return singleton results.
Alternative joining uses the first element as the seed and folds left in input order.
An empty alternative list uses bottom.
This retains singleton precision under weak laws, which do not require bottom-neutral joins.
`disjunctive_laws` requires monotone existential list meaning, empty list bottom and
meaning-preserving compaction.
It needs no least-join or selective-join premise.
Cap bounds belong to the supplied compaction policy.
`disjunctive_forward_bound` lifts that policy's bound to the forward transfer.
In particular, the legacy zero-cap policy can return a singleton on nonempty input.
Costs depend on actual alternative counts and callback charges.

[`StateAbs.t`](../../theories/Domains/DomainsState.v#L15) supplies assignment, havoc, guard and
projection callbacks over variable maps.
`StateSem.t` supplies concrete update and separate update laws.
`state_laws` describes defined assignments, arbitrary havoc replacements and guards whose
terms all evaluate successfully.
Its arguments are the state dictionary, value semantics, concrete update, value meaning and state
meaning.
It has no unused value-dictionary argument.
The one-live-state fixture in `DomainsStateTest.v` has a separate unreachable bottom.
A carrier containing one element alone could not have both empty bottom and full top over
an inhabited concrete state space.
The two-variable fixture proves that updates preserve a distinct variable and that havoc permits
both Boolean replacements.

[`gamma_solver`](../../theories/Domains/DomainsTactics.v#L13) searches the exported `galois_gamma`
database at fixed depth, then tries order and arithmetic side conditions.
Domains register soundness facts where they prove them.
Unsupported obligations stay visible for the caller.
The test files contain semantic clients, computed boundary cases, charged observations and
legacy differential fixtures.
Deferred leaf lookups charge equality, environment lookup and meet separately.
The differential observations distinguish every global tag, payload tag, width and integer.
