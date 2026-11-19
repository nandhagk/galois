# Ownership of the P2 cards

This table lists the 14 cards of batch P2 with the paths that each card owns, the base it starts
from, the STUB lemmas of the groundwork that it closes, and its size. A card owns no signature and
no file of `just/frozen.sha256`. Every card names its base with the placeholder `{P2_BASE}`, which
the dispatch fills with a commit of `main`.

## Result

- The groundwork holds the signature changes of rulings F8 and IN-3 (`RULINGS.md`, ruling
  P2-ANALYSES sections 1.5 and 4.2). It adds 7 STUB lemmas and 1 STUB-CODE placeholder, 5 and 1
  in `theories/Ssa/Live.v` and 2 in `theories/Fixpoint/Indexed.v`. Every one of them belongs to
  exactly one card.
- P2-BENCH1, P2-LIVE1 and P2-INC start from the groundwork itself and own disjoint paths.
- The other run-first cards follow their chains. Each starts from the commit of `main` that
  integrates the card before it, so the dispatch fills its `{P2_BASE}` with that commit.
  `theories/Ssa/Live.v` passes along P2-LIVE1, P2-LIVE1B, P2-LIVE2 and P2-LIVE3, and
  `tests/Ssa/LiveTest.v` joins the chain at P2-LIVE1B. `bench/` passes from P2-BENCH1 to
  P2-BENCH1B and P2-BENCH2, which own disjoint parts of it.
- The six speculative cards wait for decisions of the owner (`RULINGS.md`, P2 decisions).
  P2-PEDGE has no signature change. P2-CAPRUN adds no signature field. The signature text of
  P2-CAPJOIN, P2-CAPJOINB, P2-RANGE and P2-RANGEX (ruling P2-STRUCTURES, sections 1.6 and 3.4) is
  not on the groundwork. The reviewer lands it, compiles it and refreshes the frozen hashes on the
  base of those cards when the owner accepts their gate. Their STUB counts below are those of that
  later base.
- No card of P1 stage 2 or of the EG batch owns a path of a run-first P2 card. P1-EGG2 owns
  `theories/Egglog/Join.v` from `09655375`, and the `Run.v` chain of P1 stage 2 owns
  `theories/Egglog/Run.v`, which is why the capped join waits for P1 stage 2 and step R8 of the
  readability plan.

## Table

| Card | Owned paths | Starts from | STUBs | Hours |
| --- | --- | --- | --- | --- |
| P2-BENCH1 | `bench/` with placeholder workload libraries in `bench/egglog/`, `bench/ssa/` and `bench/ai/`, the recipes `bench-build`, `bench-check`, `bench`, `bench-promote`, `bench-compare` and `bench-profile` of `justfile`, one line of `.gitignore` | the groundwork | 0 | ~5.5 |
| P2-BENCH1B | the workload files of `bench/egglog/` (`gen_egglog.ml`, `workload_egglog.ml`, their `.mli` files, the placeholders they replace and the `gb_egglog` stanza of `bench/egglog/dune`), `bench/ssa/`, two lines of `bench/runner/bin/registry.ml` | P2-BENCH1 integrated | 0 | ~4 |
| P2-BENCH2 | `bench/ai/`, one line of `bench/runner/bin/registry.ml`, the C8 profile and baseline sections of `bench/README.md` | P2-BENCH1B integrated | 0 | ~4 |
| P2-LIVE1 | `theories/Ssa/Live.v` | the groundwork | 0 | ~6 |
| P2-LIVE1B | `theories/Ssa/Live.v`, `tests/Ssa/LiveTest.v` | P2-LIVE1 integrated | 0 | ~4 |
| P2-LIVE2 | `theories/Ssa/Live.v`, `tests/Ssa/LiveTest.v` | P2-LIVE1B integrated | 3 and the STUB-CODE `live_head_region` | ~4 |
| P2-LIVE3 | `theories/Ssa/Live.v`, `tests/Ssa/LiveTest.v` | P2-LIVE2 integrated | 2 | ~5.5 |
| P2-INC | `theories/Incremental/Incremental.v`, `theories/Incremental/Restrict.v`, `theories/Fixpoint/Indexed.v`, `tests/Incremental/IncrementalTest.v`, `tests/Incremental/RestrictTest.v`, `tests/Fixpoint/IndexedTest.v` | the groundwork | 2 | ~5.5 |
| P2-PEDGE | `theories/Ssa/Present.v`, `tests/Ssa/PresentTest.v`, `tests/Ssa/BuildTest.v`, `tests/Ssa/LiveTest.v` | P2-LIVE3 integrated, the owner accepts the profile of the edge keys | 0 | ~6.5 |
| P2-CAPJOIN | `theories/Egglog/Join.v`, `tests/Egglog/JoinTest.v` | P1 stage 2 and step R8 integrated, the owner accepts the gate of the capped join | 1 and the STUB-CODE `run_upto` | ~3.5 |
| P2-CAPJOINB | `theories/Egglog/Join.v` | P2-CAPJOIN integrated | 6 | ~3.5 |
| P2-CAPRUN | `theories/Egglog/Run.v`, `tests/Egglog/RunTest.v` | P2-CAPJOINB, the `Run.v` chain of P1 stage 2 and step R8 integrated | 0 | ~6 |
| P2-RANGE | `theories/Relational/Karr.v`, `tests/Relational/KarrTest.v` | P1 stage 2 integrated, the owner accepts the profiles | 6 and the STUB-CODE `range_many` | ~6 |
| P2-RANGEX | `theories/Relational/Poly.v`, `Zone.v`, `Octagon.v`, `tests/Relational/PolyTest.v`, `ZoneTest.v`, `OctagonTest.v` | as P2-RANGE, beside it | 12 and 3 STUB-CODE `range_many` | ~3 |

## STUB lemmas of the groundwork

`just admits` counts 146 STUB lemmas and 5 STUB-CODE placeholders on the groundwork. Of these, 139
and 4 were on `main` at `09655375` and belong to the EG batch and P1 stage 2. The other 7 and 1
are the items below.

| File | Name | Kind | Card |
| --- | --- | --- | --- |
| `theories/Ssa/Live.v` | `live_head_region` | STUB-CODE, the empty list | P2-LIVE2 |
| `theories/Ssa/Live.v` | `live_head_region_nodup` | region law | P2-LIVE2 |
| `theories/Ssa/Live.v` | `live_head_region_spec` | region law | P2-LIVE2 |
| `theories/Ssa/Live.v` | `live_head_size_le` | region law | P2-LIVE2 |
| `theories/Ssa/Live.v` | `T_live_in_head_le` | time | P2-LIVE3 |
| `theories/Ssa/Live.v` | `live_in_head_complexity` | time | P2-LIVE3 |
| `theories/Fixpoint/Indexed.v` | `row_code_bits_le` | time law of `LOCAL_TIME` | P2-INC |
| `theories/Fixpoint/Indexed.v` | `rows_of_nodup` | time law of `LOCAL_TIME` | P2-INC |

The cards carry the line of each item in their appendix "STUB items on the base".

## Order

1. P2-BENCH1, P2-LIVE1 and P2-INC, from the groundwork.
2. P2-BENCH1B and P2-LIVE1B, each after the card before it is integrated.
3. P2-BENCH2 and P2-LIVE2.
4. P2-LIVE3. P2-INC may run beside any of the cards above.
5. The speculative cards, when the owner accepts their gates. P2-PEDGE after P2-LIVE3. P2-RANGE
   and P2-RANGEX side by side. P2-CAPJOIN, P2-CAPJOINB and P2-CAPRUN in that order.
