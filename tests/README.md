Computed Rocq examples live in `tests/<Package>/` under `Galois.Tests.<Package>`, mirroring
the library packages and retaining each package's basename prefix. Memory-domain tests use
`Domains/Memory/`, and client tests use `Examples/<Client>/` for each supported example directory.
Each module's tests cover positive, rejected and boundary cases through `vm_compute`.
