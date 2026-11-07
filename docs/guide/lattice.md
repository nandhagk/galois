# Lattices and domain combinators

A [lattice dictionary](../../theories/Lattice/LatticeCore.v#L12) holds a bottom
value and costed comparison, join, widening and narrowing callbacks. The pure
accessors `leb`, `join`, `widen` and `narrow` observe their results.
`of_pure` wraps pure callbacks and charges one tick per call.
`simple` uses join for widening and keeps the left input for narrowing.

The [weak laws](../../theories/Lattice/LatticeCore.v#L152) require a preorder,
a least bottom, upper bounds for join and widening, and conditional narrowing
bounds. Narrowing needs its second input below its first input.
Leastness of join is a separate `lub_laws` record. In particular, weak laws
permit a join that always returns top. The
[weak-join test](../../tests/Lattice/LatticeCoreTest.v#L96) proves that this
choice can fail leastness. Preorder equivalence uses comparison in both
directions and does not imply carrier equality.

## Choosing meaning and termination evidence

A [domain](../../theories/Lattice/LatticeDomain.v#L10) groups a lattice, a top
value and a concretisation. `domain_of_simple L T G` builds the bundle.
`domain_laws` separately states the weak laws, least joins, greatest top,
monotone concretisation, empty bottom and full top. Agreement is a separate
interpretation for demand domains. Its laws require reflexivity and
antitonicity in the abstract need.

A [height](../../theories/Lattice/LatticeHeight.v#L11) is relative to a
value invariant. Its rank is bounded and monotone on invariant values and
grows at strict joins of invariant inputs. `closed_on` states that operations
keep the invariant. A widening rank instead counts decreasing credits when
the new input escapes the old input. The plain `height` and `widening_rank`
aliases use the total invariant.

`with_widen` and `with_narrow` replace one pure operator. Their `_c` variants
accept costed callbacks. Separate law theorems state the bounds required of
the replacement. Heights survive either replacement through
`with_widen_height` or `with_narrow_height`. A widening rank requires fresh
stable and progress proofs through `with_widen_wrank`. `height_wrank`
complements a height when widening equals join.

## Reusing the proof kit

A [two-slot observation](../../theories/Lattice/LatticeKit.v#L11) reflects
order as the conjunction of component orders and commutes with every
operation. Its projected bottoms equal the component bottoms. These exact
equations let the kit transport arbitrary component invariants and empty
meanings.

A combinator proves its `slots2` fact once. It then applies `slots2_laws`,
`slots2_lub`, `slots2_top`, `slots2_closed`, `slots2_height` and `slots2_wrank`.
The height constructor takes component weak laws, closure and heights.
The widening constructor takes component widening ranks. Both sum the
component measures and bounds. Meaning and agreement intersect through
`slots2_gamma` and `slots2_agree`.
The [costed pair pilot](../../tests/Lattice/LatticeKitTest.v#L13) demonstrates
the constructor and the one-line derivations.

An [indexed family](../../theories/Lattice/LatticeKitFamily.v#L11) uses the
same equations for an arbitrary index type. Its finite measures use a list
`U` and `family_inv`, which requires invariant components everywhere and
default-equivalent components outside `U`. `family_height` additionally
needs component least joins to locate strict growth inside `U`.
`family_wrank` uses component widening credits. Neither requires decidable
index equality or a duplicate-free list. Duplicate indices contribute
repeated summands.

`family_closed` transports pointwise invariants. `family_support_closed`
also transports finite support when bottom matches the default and widening
and ordered narrowing keep default equivalence. Weak laws alone do not give
those default-stability facts.

## Subtypes, fresh bottoms and costs

The [subtype lattice](../../theories/Lattice/LatticeSub.v#L24) uses
`Cost.refine` to attach closure proofs without changing component results.
It checks narrowing's order premise through the costed comparison.
Ordered inputs use the component narrowing. Unordered inputs keep the left
value because closure does not constrain the component's unordered result.
`sub_height` and `sub_wrank` turn invariant-relative measures into total
subtype measures.

The [bottom lift](../../theories/Lattice/LatticeAdjoin.v#L13) uses `None` for
unreachable and `Some a` for a reached component value. `None` has empty
meaning and requires no agreement. Reached heights add one above its zero
rank. Its widening credit is one above the component bound.
`bool_lattice` provides reachability meaning and liveness agreement.
`unit_lattice` supplies a trivial slot whose meaning is always full.

Pure kit facts do not bound costs. `cost_bounded_on` bounds all callbacks on
invariant inputs. `of_pure_cost`, `sub_cost` and `lift_bot_cost` provide
composable bounds. Each other combinator supplies its own cost theorem.
The tests compute both short-circuit comparison costs and result values.
`order_solver` closes order goals from explicit weak, least-join and meet
law records using bounded hint search. It fails when that search cannot
close the goal.
