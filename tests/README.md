Computed Rocq examples live in `tests/<Package>/` under `Galois.Tests.<Package>`, mirroring
the library packages and retaining each package's basename prefix. Each module's tests cover
positive, rejected and boundary cases through `vm_compute`. Differential tests that import both
libraries live in `tests/legacy/<Package>/` under `Galois.Tests.Legacy.<Package>`. The old test
suite stays in `legacy/tests/` during the migration.
