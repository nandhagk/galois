# Performance

Performance is a design requirement. The contracts specify prepared
indexes with agreement lemmas, canonical tries for keys and no list scans in inner loops. Worklist
updates schedule readers of changed unknowns; schedulers can use RPO, WTO nesting or SCC order.
Static dependencies enable these strategies and termination arguments. Query evaluation records
reads and side contributions in one traversal.

Binary fuel avoids unary fuel traversal, while the total solver uses well-founded recursion. A
cut-point certificate stores facts at selected points and recomputes the rest; replay lets observers
consume facts without a second stored map. Structured sequences are balanced when built from lists.
The dominator exactness checker runs a reachability search per node; its cost is not claimed
to be linear. The directly verified LT and Semi-NCA producers establish exactness under their
readiness premises.

The landed e-graph rebuild uses prepared incidence indexes. Its report notes that its congruence
pair universe can be quadratic within an operator bucket; source inspection is not a complexity
proof or benchmark. The interval threshold tree can have linear height for sorted or duplicate
inputs, so its lookup is not claimed to be logarithmic. Consult the individual contracts and
reports for the costs and evidence of each component.

SSA liveness queries account for preparation, trie paths, use scans and returned data. Sparse
evaluation graphs charge construction and solver work separately from prefix and suffix
reconstruction at a query. PRE charges family and graph setup, translation callbacks, indexed
phi operands, reset phases and materialized output; its conservative bounds are not a tight
complexity theorem or an optimality claim. Structured liveness also charges universe filtering
and materialized table rows. These descriptions are source-level accounting, not benchmarks.

The extraction check scans the selected generated artifacts for `Obj.magic` and the Rules solver
closure for proof-only finite-universe enumeration. Clients select extraction realisations outside
theories. The benchmark measures extracted trie, graph, solver and Rules workloads over generated
inputs. A small TOOL-2 experiment measured sizes 8, 16 and 32 with construction and validation
included; it does not establish scaling or a performance guarantee. Report input sizes, commands,
toolchain, machine and timing or memory measurements; label results as experiments. Near-linear
scaling is an objective to investigate, not an established fact.

## Legacy baseline

The following measured timings record the legacy library workflows on this machine after `just clean`.
The build, test, check and benchmark rows reused available shared-cache artifacts after their
required preceding commands. <!-- src: source revision 85c7f30; local measurement record -->

| Command | Real | User | System | Exit |
| --- | ---: | ---: | ---: | ---: |
| `just build` | 0.7 s | 0.4 s | 0.1 s | 0 |
| `just test` | 1.1 s | 0.5 s | 0.2 s | 0 |
| `just check` | 374.3 s | 658.9 s | 59.3 s | 0 |
| `just bench` (defaults) | 0.6 s | 0.3 s | 0.1 s | 0 |

The measured environment had the following values.

- Source revision: `85c7f30`, measured on 2026-11-07.
- CPU: 8 logical CPUs, model `11th Gen Intel(R) Core(TM) i5-11300H @ 3.10GHz`.
- Memory: 15 GiB total, 7.5 GiB used, 2.0 GiB free, 1.1 GiB shared, 7.6 GiB buff/cache,
  and 7.9 GiB available.
- Kernel: `Linux 6.18.60`.
- Toolchain: Just `1.58.0`, OCaml `5.5.0`, Rocq `9.3.0` compiled with OCaml `5.5.0`, and
  Dune `3.23.1`.
- Dune cache: `DUNE_CACHE=enabled`.
- Resource limit: `galois.slice` had `MemoryMax=10000000000` and `MemorySwapMax=0`.

<!-- src: source revision 85c7f30; captured local environment record -->

The Dune cache was present before the run. `just clean` removed this checkout's build outputs.
Subsequent workflows could restore shared cached artifacts. Other isolated worktrees ran
concurrently, so their load may have affected these measurements. No command was interrupted.
