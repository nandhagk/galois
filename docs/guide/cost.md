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

Costs follow a word-RAM model. Counter operations cost constant time, and trie
descent charges per key bit. A cost theorem bounds `Cost.ticks (f_c …)` using
named size measures and constants. The theorem describes the Rocq definition.
It does not measure native runtime.

Computational code must not read `Cost.ticks` or inspect the cost record to
choose a result. Such code would prevent cost erasure during extraction.
The extraction realization and list and loop combinators belong to the next
Cost library card.
