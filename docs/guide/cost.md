# Cost

A core algorithm returns its result and an abstract step count in `Cost.t A`.
The record has primitive projections `Cost.value : Cost.t A -> A` and
`Cost.ticks : Cost.t A -> N`. It contains computational data alone.
Correctness and cost bounds are separate theorems.

Import `Galois.Cost.CostMonad` and `Cost.Notations` to write costed code.
`Cost.ret a` returns `a` at zero cost. `let* x := m in k` runs `m`, passes its
result to `k` and adds both counts. `m ;; k` discards the first result.
`Cost.tick k` charges `k` ticks and returns `tt`. `Cost.step` charges one tick.

## Write the algorithm once

Name the costed function `f_c` and define its plain interface by
`f := Cost.value (f_c …)`. Prove an `f_equation` theorem that restates the plain
recursion through the public projection lemmas. Consumers use this equation
without unfolding the costed implementation.

For example, the list counter in
[`CostMonadTest.v`](../../tests/Cost/CostMonadTest.v) uses this definition.

```coq
Fixpoint length_c {A : Type} (xs : list A) : Cost.t nat :=
  match xs with
  | [] => Cost.ret 0
  | _ :: rest =>
    Cost.step ;;
    let* n := length_c rest in
    Cost.ret (S n)
  end.
```

The examples check that the result and tick count both equal the list length
on empty, singleton and longer inputs.

Every recursion step and loop iteration must charge a tick. Every callback call
charges one tick plus the callback's own count. Every nonconstant operation uses
a costed function or `Cost.tick_bits`. Tick amounts in algorithm bodies are
literals. Constant-size straight-line code may be free.

## Map, lift and refine

`Cost.map f m` applies a pure function to the result and keeps the count.
`Cost.lift w f a` wraps a pure function and charges the weight `w a`.
The caller must justify the weight when using `lift` in a cost contract.
`Cost.tick_bits p` traverses the binary digits of a positive number and charges
`N.pos (Pos.size p)` ticks, including the leading digit.

`Cost.refine m H` pairs the result of `m` with a proof `H : P (Cost.value m)`.
Its type is `Cost.t {a | P a}`. The result contains the supplied proof, and the
tick count does not change. The cost record itself has no proof fields.

## Prove results and costs separately

`Cost.value_bind` rewrites a sequenced result to the continuation's result.
`Cost.ticks_bind` rewrites its count to a sum.
The corresponding `value_*` and `ticks_*` theorems cover the other operations.
`autorewrite with galois_cost` applies these equations, including refinement.
The monad laws `Cost.bind_ret_l`, `Cost.bind_ret_r` and `Cost.bind_assoc` state
equalities of whole costed computations.

Costs follow a word-RAM model. Operations on counters and dense IDs cost constant
time under the assumption that these values occupy O(log n) bits. Trie descent
charges per key bit. A cost theorem bounds `Cost.ticks (f_c …)` using
named size measures and constants. The theorem describes the Rocq definition.
It does not measure native runtime.

Computational code must not read `Cost.ticks` or inspect the cost record to
choose a result. Such code would prevent cost erasure during extraction.

## List combinators

[`CostList.v`](../../theories/Cost/CostList.v) provides `length_c`, `app_c`,
`rev_c`, `map_c`, `filter_c`, `forallb_c`, `existsb_c`, `fold_left_c`,
`fold_right_c`, `filter_map_c` and `find_c`. Every visited element costs one tick
plus its callback's own count. Empty traversals cost zero. `app_c` visits its
first list alone, and `rev_c` uses a linear left fold.

`map_c`, `filter_c` and `filter_map_c` use a right fold, so their callbacks run
from right to left. Output order follows input order. `filter_map_c` discards
`None` and keeps the payloads of `Some`. The pure `filter_map` function states
this order explicitly. `forallb_c`, `existsb_c` and `find_c` search from left
to right and stop as soon as their result is known.

Every combinator has a `value_*` agreement theorem, an exact `ticks_*` equation,
a `ticks_*_le` uniform bound and a `ticks_*_potential` credit bound.
The fold bounds allow an invariant `I` on the accumulator. For example,
`ticks_fold_left_c_potential` requires each reached callback to preserve `I` and
to satisfy the following inequality for a potential `Phi` and a charge `k`.

```text
ticks (f b x) + Phi (value (f b x)) <= k + Phi b
```

The conclusion refunds the final accumulator potential.

```text
ticks (fold_left_c f l b) + Phi (value (fold_left_c f l b))
  <= N.of_nat (length l) * (k + 1) + Phi b
```

The simple combinators specialize the fold rule to their output accumulators.
Search uses a potential on suffixes. `find_remainder` identifies the unvisited
suffix after success and returns the empty list after exhaustion. Its potential
is refunded in `ticks_find_c_potential`. Universal and existential tests use the
same suffix rule. This accounts for skipped callbacks without charging the
unvisited suffix.

## Binary-fuel loops

[`CostLoop.v`](../../theories/Cost/CostLoop.v) defines
`iterate step fuel s : Cost.t (S + R)` for positive binary fuel.
The callback returns `inl s'` to continue or `inr r` to stop.
The driver's `inl` result means that all `Pos.to_nat fuel` callback steps were
used. An `inr` result propagates the callback's stopping value.
`iterate_value` proves the `runs` relation, and `iterate_inl_runs_out` and
`iterate_inr_stops` give witnesses for exhaustion and stopping.

Fuel one charges one driver tick and one callback call's own count.
An even block charges one descent tick and runs two half blocks.
An odd block charges one descent tick, one callback-invocation tick and its
callback, then runs two half blocks if the callback continues.
Stopped results bypass every later callback and block.
Recursion follows the bits of the fuel.

`iterate_cost step I Phi k fuel s` assumes `I s` and the following callback rule.

```text
forall s, I s ->
  ticks (step s) <= k /\
  match value (step s) with
  | inl s' => I s' /\ Phi s' < Phi s
  | inr _ => True
  end
```

The resulting bound includes the stopping callback and binary descent.

```text
ticks (iterate step fuel s)
  <= (k + 2) * (Phi s + 1) + 2 * N.pos (Pos.size fuel)
```

`iterate_credit` gives a stronger result for composition. An exhausted result
`inl s'` preserves `I` and satisfies
`ticks (iterate step fuel s) + (k + 2) * Phi s' + 1 <= (k + 2) * Phi s`.
A stopped result satisfies the public bound with one copy of the bit count.

Amortisation alone does not imply termination. A callback that always continues
at a positive cost satisfies an amortised rule with `Phi = 0`, yet its cost
grows with the fuel. `iterate_cost_amortised` therefore retains a fuel term.
It defines `result_potential Phi (inl s') = Phi s'` and
`result_potential Phi (inr r) = 0`. Its step premise is the following.

```text
forall s, I s ->
  (match value (step s) with inl s' => I s' | inr _ => True end) /\
  ticks (step s) + result_potential Phi (value (step s)) <= k + Phi s
```

In particular, the stopping callback must satisfy `ticks (step s) <= k + Phi s`.
The theorem preserves the invariant on continuation results and proves this bound.

```text
ticks (iterate step fuel s)
  + result_potential Phi (value (iterate step fuel s)) + 1
  <= (k + 2) * N.pos fuel + Phi s
```

`fix_wf measure F` wraps `Wf.Fix` for terminating recursion.
Recursive calls receive proofs that their measure decreases strictly.
`fix_wf_unfold` requires pointwise extensionality of the functional `F`.
`fix_wf_cost` lifts a local bound on `F` under bounds on all smaller recursive
calls. The wrapper does not add ticks for termination proofs. The functional
must charge its own work.

## Asymptotic bounds

[`CostBound.v`](../../theories/Cost/CostBound.v) defines
`bigO f g := exists c, forall x, g x <= c * (1 + f x)` for `N`-valued sizes
and costs. The size comes first. The additive unit makes constant costs and
zero-sized inputs explicit.

`bigO_refl`, `bigO_trans`, `bigO_le` and `bigO_mono` handle basic comparisons.
`bigO_add` adds sizes and costs, and `bigO_scale` multiplies a cost by a constant.
`bigO_mul` bounds a product cost by `f1 + f2 + f1 * f2`, so the theorem also
covers inputs where either size is zero. `bigO_comp` precomposes a bound with an
input map. `bigO_through` uses a monotone outer size and a pointwise
overapproximation of the mapped size.

`bigO_sum` sums a uniformly bounded family over an input-dependent list.
Its size sums `1 + f y` for each occurrence, which pays for the list length even
when every `f y` is zero. `bigO_bind` adds bounds for a computation and the
continuation reached on its actual value.

## Cost tactics

[`CostTactics.v`](../../theories/Cost/CostTactics.v) exports these tactics.

- `cost_simpl` repeatedly rewrites with `galois_cost` and reduces projection
  redexes. It leaves plain arithmetic for tactics such as `lia`.
- `bigO_solver` searches six composition layers using the bound lemmas and
  `galois_bigO`. It then tries `lia` on residual goals.
- `iterate_invariant I Phi k` applies `iterate_cost` and leaves the callback
  contract and the initial invariant.

The value equations and exact tick equations are exported rewrite hints.
The tactic fixtures include symbolic arithmetic that normalization leaves open.

## Extraction and lint

[`ExtractCost.v`](../../extraction/new/common/ExtractCost.v) realizes `Cost.t A`
as `A`. The runtime in
[`galois_cost.ml`](../../extraction/new/common/galois_cost.ml) passes values
directly through `ret`, `bind`, `value` and `refine`. Mapping applies the function,
lifting ignores the weight, and charging returns unit.

Rocq 9.3 represents primitive projections separately from ordinary constants.
An `Extract Constant` mapping alone does not cover these projection nodes.
The prelude therefore erases the constructor's count argument and supplies a
one-field matcher for the value. `Extraction SafeImplicits` stays enabled.
A primitive `Cost.ticks` observation then fails extraction because it reads the
erased field. The ordinary constant mapping and runtime trap use
`failwith "GALOIS_COST_TICKS"`. The artifact checker independently rejects this
exact sentinel anywhere in generated `.ml` or `.mli` text.

Source lint applies to `theories/` and `examples/` outside `theories/Cost/`.
It rejects cost construction, count observations and syntactically recognized
whole-record matches in computational declarations. Proofs, theorem statements
and `Prop` definitions may inspect costs. The lexer excludes comments and strings.
The lint also rejects plain twins in `_c` bodies and qualified nonconstant
`List` operations there. This lexical check supplements the extraction boundary.
It does not replace type checking or a proof that every operation is charged.
The legacy hygiene, layout, assumption and extraction rules still apply.

## VM gate procedure

[`CostGateTest.v`](../../tests/Cost/CostGateTest.v) defines independent pure and
costed binary tries, proves their value agreement and checks exact key-bit costs.
Its workload inserts successive positive keys and reads every inserted key.
Key generation uses binary successor, so it avoids repeated unary conversion.
Both workload examples compare the entire ordered lookup list against the same
expected list.

Build the tests first with `just test-new`. Create two scratch Rocq clients that
import the compiled gate test. Give each client one of its workload examples,
using the shared `gate_size`. Compile each client three times through a temporary
Just recipe under the same `galois.slice` cap. Alternate pure and costed runs,
use one compiler process at a time and retain the raw wall times. Compare the
two medians. Compiler startup, imports, `vm_compute` and ordinary kernel checking
are included in both measurements. Nix shell startup is excluded.

The recorded run used Rocq 9.3.0, OCaml 5.5.0, Just 1.58.0 and an Intel
Core i5-11300H host. Dependencies were already built and warm. Both targets used
40,000 insertions and 40,000 lookups. The aggregate cap was 10 GB without swap,
and other Galois work could share the host and slice.

<!-- Source: tests/Cost/CostGateTest.v gate_size and the repeated COST-LIBS compiler log. -->
| Round | Pure wall seconds | Costed wall seconds |
| --- | --- | --- |
| 1 | 5.542 | 6.004 |
| 2 | 6.625 | 5.991 |
| 3 | 5.498 | 7.268 |

The pure median was 5.542 seconds and the costed median was 6.004 seconds.
The costed target took ~1.08× the pure target's median time, below the 1.5× gate.
No pure fast path was needed. This measurement covers this workload and toolchain.
It is separate from native runtime performance.
