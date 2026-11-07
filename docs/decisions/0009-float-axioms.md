# Float axioms

Status: in force

A theorem in a file that imports `Galois.Float` may depend on exactly the four axioms listed
in [guarantees](../guarantees.md) (formerly rulings C13 and C56). No other theorem may depend
on an axiom. The permitted names are listed below.

```text
Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec
Stdlib.Reals.ClassicalDedekindReals.sig_not_dec
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep
Stdlib.Logic.Classical_Prop.classic
```

## Why

The import boundary confines the assumptions required by floating-point proofs.
