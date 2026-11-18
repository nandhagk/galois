# Ownership of the P1 cards

This table lists the 33 cards of batch P1 and the `theories/` files each one owns. Every owned
file also brings its test file, and a card owns no signature and no frozen file. The check ran over
the 127 non-signature `.v` files of `theories/` at `07f190c6`, and the nine frozen implementation
files of `just/frozen.sha256` (`Egglog/Model.v`, `Egglog/Syntax.v`, `Egraph/Syntax.v`,
`Graph/Data.v`, `Graph/Spec.v`, `Lattice/Gamma.v`, `Relational/Keys.v`, `Relational/LinForm.v`,
`Ssa/Lang.v`).

## Result

- No file is owned by two cards at the same time. `Egglog/Database.v` appears under P1-DB, P1-DBW,
  P1-DBW2 and P1-DBW3, which run one after the other, each from a `p1b/base` that contains the
  previous one. `Egglog/Run.v` appears under P1-RUN and the stage-2 cards P1-PLAN, P1-PLAN2,
  P1-BACKOFF, P1-BACKOFF3, P1-BACKOFF2 and P1-FUSE, in that order, one at a time. `Egglog/Join.v`
  appears under P1-JOIN in stage 1 and under P1-EGG2 in stage 2, which
  starts from `p1b/base` and runs beside the stage-2 cards of `Database.v` and `Run.v`. These are
  the only repeats, and they need no fix.
- No card owns a `*Sig.v` file or a file listed in `just/frozen.sha256`.
- Every non-signature, non-frozen `.v` file under `theories/` has an owner. The list of unowned
  files is empty.
- Nothing needed moving. The splits of this round (P1-SCALAR into P1-SCALAR and P1-INTERVAL,
  P1-KBITS into P1-KBITS and P1-WRAPPED) assign each file to one card. `BRIEF.md` still lists
  `Zone.v` and `Octagon.v` under P1-POLY, and the cards give them to P1-DBM. The cards are the
  authority.
- Five test files under `tests/Domains/` belong to no card and stay unchanged. They are
  `BitsLawTest.v`, `Review12Test.v`, `ValueLawTest.v`, `ValueOpenTest.v` and `ValueReachLawTest.v`.

## Table

| Card | Owned files in `theories/` | Depends on other cards | STUBs at `b9889589` |
| --- | --- | --- | --- |
| P1-TRIE | `Base/*.v` except the seven signatures | none. Adds `root_of` (T5) that P1-DB uses | 25 |
| P1-WORD | `Bits/*.v` | none. Every `Domains` card reads its statements | 0 |
| P1-DB | `Egglog/Database.v` | P1-TRIE (`root_of`, item T5, in `p1/base`), P1-INDEX (public clocks) | 12 |
| P1-DBW | `Egglog/Database.v` (stage 2, state change, 1 of 3) | P1-DB integrated in `p1b/base` | 0 |
| P1-DBW2 | `Egglog/Database.v` (stage 2, 2 of 3, after P1-DBW) | P1-DBW integrated | 0 |
| P1-DBW3 | `Egglog/Database.v` (stage 2, 3 of 3, after P1-DBW2) | P1-DBW2 integrated | 0 |
| P1-INDEX | `Egglog/Index.v` | none. P1-DB compiles against it | 5 |
| P1-RUN | `Egglog/Run.v` | P1-JOIN (`JoinSig.v` statements), P1-DB (public statements) | 9 |
| P1-JOIN | `Egglog/Join.v`, `Sorts.v`, `ModelFacts.v` | none. P1-RUN and P1-DB use its statements | 1 |
| P1-EGRAPH | `Egglog/Extract.v`, `Egraph/Compile.v`, `Egraph/Saturate.v`, `Clients/Andersen.v`, `Clients/Steensgaard.v` | P1-DB, P1-RUN (public statements) | 17 |
| P1-PLAN | `Egglog/Run.v` (stage 2, after P1-RUN) | P1-RUN integrated in `p1b/base` | 0 |
| P1-PLAN2 | `Egglog/Run.v` (stage 2, after P1-PLAN) | P1-PLAN integrated, ruling R1 in place | 0 |
| P1-BACKOFF | `Egglog/Run.v` (stage 2, after P1-PLAN2) | P1-PLAN2 integrated, so P1-RUN is too | 0 |
| P1-BACKOFF3 | `Egglog/Run.v` (stage 2, after P1-BACKOFF) | P1-BACKOFF integrated | 0 |
| P1-BACKOFF2 | `Egglog/Run.v`, `Egraph/Saturate.v` (stage 2, after P1-BACKOFF3) | P1-BACKOFF3 and P1-EGRAPH integrated | 0 |
| P1-FUSE | `Egglog/Run.v` (stage 2, last of the `Run.v` sequence, after P1-BACKOFF2) | P1-BACKOFF2 integrated | 0 |
| P1-EGG2 | `Egglog/Join.v` only (stage 2, parallel with the stage-2 cards of `Database.v` and `Run.v`) | P1-JOIN integrated | 0 |
| P1-KARR | `Relational/Karr.v`, `LinCert.v`, `Linearize.v`, `RelEnv.v` | none. The `RelEnv` fields of ruling D8 are its own | 24 |
| P1-POLY | `Relational/Poly.v` | P1-KARR (15 `LinCert` names used by `SignedCert`) | 11 |
| P1-DBM | `Relational/Zone.v` | P1-TRIE (public map statements) | 10 |
| P1-OCT | `Relational/Octagon.v` (split from P1-DBM by review R3) | P1-TRIE (public map statements) | 10 |
| P1-SCALAR | `Domains/BitsLang.v`, `Const.v`, `CutInterval.v`, `Harness.v`, `Product.v`, `Reduced.v`, `Sign.v`, `Tagged.v`, `Thresholds.v`, `Translate.v`, `ZLang.v` | P1-WORD. Keeps `ConstWordFast` for P1-INTERVAL | 12 |
| P1-INTERVAL | `Domains/Congruence.v`, `Interval.v`, `IntervalBack.v`, `IntervalOps.v` | P1-WORD, P1-SCALAR (`ConstWordFast` of `Const.v`) | 28 |
| P1-KBITS | `Domains/KnownBits.v`, `KnownBitsBack.v`, `KnownBitsOps.v` | P1-WORD | 10 |
| P1-WRAPPED | `Domains/Wrapped.v`, `WrappedOps.v`, `Reducers.v` | P1-WORD | 9 |
| P1-STATE | `Lattice/` (`Bounded`, `Disjunction`, `Dual`, `Flat`, `JoinWidening`, `MapLattice`, `Product`, `Reduced`, `Sets`, `Simple`, `WithBot`, `WithTop`), `States/` (`Disjunction`, `Env`, `EnvBudget`, `EnvIntBudget`, `Partition`), `Widening/Mining.v`, `Alarms/` (`Alarms`, `BitsChecks`, `Checks`) | none. Others read its statements | 38 |
| P1-FIX | `Fixpoint/` (`Certified`, `Check`, `Indexed`, `Narrow`, `Policy`, `Query`, `Schedule`, `SystemKey`, `Worklist`, `WorklistLeast`) | P1-GRAPH (`Prepared` input of `W.build` and `W.check`) | 12 |
| P1-INC | `Incremental/Incremental.v`, `Restrict.v` | none | 4 |
| P1-GRAPH | `Graph/Digraph.v`, `Search.v`, `Scc.v`, `Wto.v`, `Loops.v`, `Frontier.v` | P1-DOM (`DomOrder.v`, `DomProducer.v` names used by `Frontier.v` and `Loops.v`) | 3 |
| P1-DOM | `Graph/Dom.v`, `DomProducer.v`, `DomOrder.v` | P1-GRAPH (`scc_graph`, `prepared_search_trace`, `search_budget` and their lemmas), P1-TRIE | 1 |
| P1-SSA | `Ssa/Build.v`, `Validate.v`, `Destroy.v`, `ParMove.v` | P1-PROG (`LiveT` lemmas), P1-DOM (through `DOM`) | 3 |
| P1-PROG | `Ssa/Live.v`, `Present.v`, `Program/Calls.v`, `Cfg.v`, `Icfg.v`, `Memory.v`, `Semantics.v`, `Ssa.v`, `Vars.v` | P1-SSA (keeps the `LiveT` names it uses) | 37 |
| P1-FRAME | `Framework/Dense.v`, `GenKill.v`, `Ide.v`, `Ifds.v`, `Interp.v`, `Sparse.v`, `Summary.v` | P1-FIX (`WorklistCode` instantiated by `tests/Framework/`) | 30 |

The dependencies are public statements and kept names. No card edits a file that another card
edits at the same time. The stage-2 cards edit `Database.v`, `Run.v` and `Saturate.v` only after
the stage-1 card that owns the file is integrated. The `Run.v` cards run one at a time.

## STUB lemmas on `p1/base`

The count covers `Admitted. (* STUB *)` in `theories` and `tests` at `b9889589` (`git grep -c` over
those two directories). It gives 311 STUBs in 65 files, and no test file holds one. Each card
carries the list of its own STUBs, with file, line and lemma, in the appendix "STUB lemmas on the
base".

- Every STUB belongs to exactly one card. The sum of the per-card totals in the table is 311, and
  no STUB is left without an owner.
- The three shared files give their STUBs to the first card that edits them. `Egglog/Run.v` has 9
  STUBs (the four lemmas of ruling R1 and five `bigO` fields), and they belong to P1-RUN.
  `Egraph/Saturate.v` has 3, and they belong to P1-EGRAPH. `Egglog/Database.v` has 12, and they
  belong to P1-DB. P1-PLAN, P1-PLAN2, P1-BACKOFF, P1-BACKOFF3, P1-BACKOFF2, P1-FUSE, P1-DBW, P1-DBW2,
  P1-DBW3 and P1-EGG2 start from `p1b/base`.
  Their own STUBs come from rulings G1-C and G2X, which are not on `p1/base`, so each of them owns
  0 STUBs at `b9889589`.
- P1-WORD owns 0 STUBs, because ruling A5 landed fully proved.
- P1-SCALAR and P1-INTERVAL split the former scalar card by file, and the 12 and 28 STUBs follow
  that split (`Domains/Interval.v` 21 and `Congruence.v` 7 belong to P1-INTERVAL).

## Order of stage 2

No stage-2 card has an optional item. Every item of every card is required, and a cut line only
says where to stop when time runs out. The cards are sized for a session of about 6 hours, and the
estimates are in the cards.

1. `Egglog/Run.v` (and `Saturate.v` for the fifth card), one card at a time. P1-PLAN (~7 hours),
   P1-PLAN2 (~6), P1-BACKOFF (~6), P1-BACKOFF3 (~3), P1-BACKOFF2 (~6.5, after P1-EGRAPH), P1-FUSE (~6).
2. `Egglog/Database.v`, one card at a time, beside the first sequence. P1-DBW (~6.5 hours),
   P1-DBW2 (~6), P1-DBW3 (~4).
3. `Egglog/Join.v`, beside both sequences. P1-EGG2 (~4 hours).

The three sequences use each other's files through the signatures only, and every card keeps the
statements of its signature fields.
