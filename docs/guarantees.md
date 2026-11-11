# Guarantees

## Claims

A proved claim names a theorem and its premises. A tested claim names the suite and the cases
it covers. A measured claim names the benchmark and its setup. A planned claim describes work
that is not yet done.

## Proof policy

Source contains no `Axiom`, `Parameter`, `Admitted`, `admit`, `give_up` or `Abort`. Every
`Theorem` is closed under the global context, subject to the Float rule below.
`just lint` rejects the forbidden tactics and commands in source, and `just audit` checks the assumptions of every compiled theorem.

## Float axioms

A theorem in any file that imports `Galois.Float` may depend on exactly the following four
axioms. No other theorem may depend on an axiom. This rule applies wherever the file lives.

```text
Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec
Stdlib.Reals.ClassicalDedekindReals.sig_not_dec
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep
Stdlib.Logic.Classical_Prop.classic
```

Flocq is imported only by Float packages and files that import them.

## Cost model

The target cost model is a word-RAM model. Ticks count unit operations, and each costed
algorithm bounds its ticks. Operations on counters, ranks, dense IDs, fuel and similar numbers
cost O(1) when those numbers have O(log n) bits. Trie descent and encoded key comparison charge
one tick per key bit. After interning, a key has O(log n) bits. Bounds concern Rocq definitions.
A tick count is not a time measurement.

## Checks

`just check` checks formatting, the build, the tests, source style and frozen files. `just audit` checks theorem assumptions.
The target cost checks forbid direct inspection of cost records outside their implementation
except in proofs and propositions. They also forbid calls to a plain function from its costed
counterpart. The target includes a `vm_compute` slowdown gate and extraction and nested query
checks. These cost-specific checks are planned until their implementation lands.

## Trust

Rocq's kernel, Stdlib and Flocq under the Float rule form the trusted base. Client laws are
premises of the theorems that use them. Examples are finite observations. Extraction is not
proved.
